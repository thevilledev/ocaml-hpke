(** RFC 9180 Hybrid Public Key Encryption.

    This module deliberately exposes only versioned protocol behavior. Secret
    keys and mutable sender/receiver contexts are abstract. *)

module Error : sig
  (** Errors returned by the public API. Error strings describe classes of
      invalid input and never contain key material. *)
  type t =
    | Unsupported_algorithm of int
    | Invalid_public_key of string
    | Invalid_private_key of string
    | Invalid_encapsulation of string
    | Key_mismatch
    | Derive_key_pair_failure
    | Invalid_psk of string
    | Invalid_length of string
    | Message_limit_reached
    | Plaintext_too_long
    | Export_length_out_of_range
    | Concurrent_use
    | Open_error
    | Internal_error of string

  val pp : Format.formatter -> t -> unit
end

module Kem : sig
  (** The closed registry of supported RFC 9180 KEM identifiers. *)
  type id = P256 | P384 | P521 | X25519 | X448

  val to_int : id -> int
  val of_int : int -> (id, Error.t) result
  val pp : Format.formatter -> id -> unit
  val public_key_size : id -> int
  val private_key_size : id -> int
  val encapsulated_key_size : id -> int

  val secret_size : id -> int
  (** [Nsecret], the length in bytes of the KEM shared secret. *)
end

module Kdf : sig
  (** The closed registry of supported RFC 9180 KDF identifiers. *)
  type id = Hkdf_sha256 | Hkdf_sha384 | Hkdf_sha512

  val to_int : id -> int
  val of_int : int -> (id, Error.t) result
  val pp : Format.formatter -> id -> unit

  val hash_size : id -> int
  (** [Nh], the output length in bytes of the underlying hash function. *)

  val extract : id -> salt:string -> string -> string
  (** [extract id ~salt ikm] is the unlabeled RFC 5869 [HKDF-Extract(salt, ikm)]
      of this KDF. HPKE's own key schedule uses labeled derivations internally;
      this function exists for protocols layered on HPKE that derive further
      keys with the suite's KDF, such as the response keys of RFC 9458. *)

  val expand :
    id -> prk:string -> info:string -> int -> (string, Error.t) result
  (** [expand id ~prk ~info length] is the unlabeled RFC 5869
      [HKDF-Expand(prk, info, length)] of this KDF. Returns
      {!Error.Invalid_length} when [prk] is shorter than [hash_size id], or when
      [length] is negative or exceeds [255 * hash_size id]. *)
end

module Aead : sig
  (** The closed registry of supported encryption AEAD identifiers. Export-only
      operation is represented separately by [Suite.export_only]. *)
  type id = Aes_128_gcm | Aes_256_gcm | Chacha20_poly1305

  val to_int : id -> int
  val of_int : int -> (id, Error.t) result
  val pp : Format.formatter -> id -> unit

  val key_size : id -> int
  (** [Nk], the key length in bytes. *)

  val nonce_size : id -> int
  (** [Nn], the nonce length in bytes. *)

  val tag_size : id -> int
  (** [Nt], the authentication tag length in bytes. *)

  type key
  (** A key prepared for repeated use with one AEAD. Preparing an AES-GCM key
      derives its GHASH tables, which without hardware support costs more than
      sealing several kilobytes, so a protocol that seals many messages under
      one key should prepare it once. Values are abstract and cannot be reliably
      zeroized by the OCaml garbage collector. *)

  val key : id -> string -> (key, Error.t) result
  (** [key id secret] prepares [secret] for use with [id]. Returns
      {!Error.Invalid_length} unless [secret] is [key_size id] bytes long. *)

  val seal :
    key ->
    nonce:string ->
    aad:string ->
    plaintext:string ->
    (string, Error.t) result
  (** Single-shot AEAD encryption under an explicit key and nonce, returning the
      ciphertext followed by its tag. Unlike {!Rfc9180.Sender.seal}, nothing
      here prevents nonce reuse: the caller must never seal twice under the same
      key and nonce. This exists for protocols layered on HPKE that encrypt with
      the suite's AEAD under exported keys, such as RFC 9458 responses. Returns
      {!Error.Invalid_length} for a nonce of the wrong size and
      {!Error.Plaintext_too_long} beyond the AEAD's limit. *)

  val open_ :
    key ->
    nonce:string ->
    aad:string ->
    ciphertext:string ->
    (string, Error.t) result
  (** Single-shot AEAD decryption under an explicit key and nonce. Returns
      {!Error.Invalid_length} for a nonce of the wrong size. Authentication
      failure and malformed ciphertexts are both reported as
      {!Error.Open_error}. *)
end

module Public_key : sig
  type t
  (** A validated public key tagged with its KEM. *)

  val of_bytes : kem:Kem.id -> string -> (t, Error.t) result
  (** Parse an exact-length canonical encoding. NIST keys must use uncompressed
      SEC1 form. X25519 and X448 low-order rejection occurs when the key is
      used. *)

  val to_bytes : t -> string
  val kem : t -> Kem.id
end

module Private_key : sig
  type t
  (** A validated private key tagged with its KEM. Values are abstract but
      cannot be reliably zeroized by the OCaml garbage collector. *)

  val of_bytes : kem:Kem.id -> string -> (t, Error.t) result
  (** Parse and validate an exact-length key. X25519 and X448 input is clamped.
  *)

  val to_bytes : t -> string
  (** Serialize the key. X25519 and X448 output is clamped as required by RFC
      9180. *)

  val kem : t -> Kem.id
  val public_key : t -> Public_key.t
end

val generate_key_pair :
  rng:Mirage_crypto_rng.g ->
  Kem.id ->
  (Private_key.t * Public_key.t, Error.t) result
(** Generate a key pair using the explicitly supplied random generator. *)

val derive_key_pair :
  Kem.id -> ikm:string -> (Private_key.t * Public_key.t, Error.t) result
(** Deterministically derive a key pair as specified by RFC 9180. *)

module Psk : sig
  type t
  (** A high-entropy pre-shared secret and its application identifier. *)

  val create : secret:string -> id:string -> (t, Error.t) result
  (** [create ~secret ~id] rejects secrets shorter than 32 bytes and empty
      identifiers. The length check cannot establish entropy. *)

  val id : t -> string
end

module Suite : sig
  type encryption
  (** Runtime-selected, closed ciphersuites. The capability parameter prevents
      export-only suites from being passed to encryption operations. *)

  type export_only
  type _ t

  val create : kem:Kem.id -> kdf:Kdf.id -> aead:Aead.id -> encryption t
  val export_only : kem:Kem.id -> kdf:Kdf.id -> export_only t
  val kem : _ t -> Kem.id
  val kdf : _ t -> Kdf.id
  val aead : encryption t -> Aead.id
end

module Rfc9180 : sig
  (** Stateful RFC 9180 operations. This module's wire semantics will not be
      changed by a future HPKE standard. *)

  module Sender : sig
    type 'capability t
    (** Abstract, role-specific sender contexts. Aliases refer to the same
        mutable sequence state; do not treat assignment as cloning. *)

    val seal :
      Suite.encryption t ->
      aad:string ->
      plaintext:string ->
      (string, Error.t) result
    (** Authenticate and encrypt using the next context nonce. Successful calls
        advance exactly once. Concurrent calls return {!Error.Concurrent_use}
        from one participant before it performs cryptography. *)

    val export : _ t -> context:string -> length:int -> (string, Error.t) result
    (** Export [length] bytes without changing message sequence state. *)
  end

  module Receiver : sig
    type 'capability t
    (** Abstract, role-specific receiver contexts. *)

    val open_ :
      Suite.encryption t ->
      aad:string ->
      ciphertext:string ->
      (string, Error.t) result
    (** Authenticate and decrypt using the next context nonce. Successful calls
        advance exactly once. Authentication failure does not advance sequence
        state. Concurrent calls return {!Error.Concurrent_use} from one
        participant before it performs cryptography. *)

    val export : _ t -> context:string -> length:int -> (string, Error.t) result
    (** Export [length] bytes without changing message sequence state. *)
  end

  type 'capability sender_setup = {
    encapsulated_key : string;
    context : 'capability Sender.t;
  }

  type ciphertext = { encapsulated_key : string; ciphertext : string }
  (** A single-shot result. This record is not a wire encoding; applications
      must frame its fields and bind their protocol context separately. *)

  val setup_base_sender :
    rng:Mirage_crypto_rng.g ->
    'capability Suite.t ->
    recipient:Public_key.t ->
    info:string ->
    ('capability sender_setup, Error.t) result
  (** Establish a Base-mode sender context using fresh randomness. *)

  val setup_base_receiver :
    'capability Suite.t ->
    recipient:Private_key.t ->
    encapsulated_key:string ->
    info:string ->
    ('capability Receiver.t, Error.t) result
  (** Establish a Base-mode receiver context. Invalid encapsulations are
      reported structurally at this context-level API. *)

  val setup_psk_sender :
    rng:Mirage_crypto_rng.g ->
    'capability Suite.t ->
    recipient:Public_key.t ->
    psk:Psk.t ->
    info:string ->
    ('capability sender_setup, Error.t) result
  (** Establish a PSK-mode sender context. *)

  val setup_psk_receiver :
    'capability Suite.t ->
    recipient:Private_key.t ->
    psk:Psk.t ->
    encapsulated_key:string ->
    info:string ->
    ('capability Receiver.t, Error.t) result
  (** Establish a PSK-mode receiver context. *)

  val setup_auth_sender :
    rng:Mirage_crypto_rng.g ->
    'capability Suite.t ->
    recipient:Public_key.t ->
    sender:Private_key.t ->
    info:string ->
    ('capability sender_setup, Error.t) result
  (** Establish an Auth-mode sender context. [sender] is the sender's static
      key, and a receiver set up with its public key opens only what the holder
      of [sender] sealed. That is not a signature. Whoever holds the recipient's
      private key can seal as any sender (key-compromise impersonation, RFC
      9180, Section 9.1.1), so the recipient cannot prove to anyone else who
      sealed a message. Where either matters, also sign the encapsulated key and
      the ciphertexts. Returns {!Error.Key_mismatch} unless the suite and both
      keys share one KEM. *)

  val setup_auth_receiver :
    'capability Suite.t ->
    recipient:Private_key.t ->
    sender:Public_key.t ->
    encapsulated_key:string ->
    info:string ->
    ('capability Receiver.t, Error.t) result
  (** Establish an Auth-mode receiver context for messages sealed by the holder
      of the private key of [sender]. An invalid encapsulation is reported as
      {!Error.Invalid_encapsulation}, and a [sender] key that fails validation,
      such as a low-order X25519 or X448 value, as {!Error.Invalid_public_key}.
      See {!setup_auth_sender} for what the authentication does not provide. *)

  val setup_auth_psk_sender :
    rng:Mirage_crypto_rng.g ->
    'capability Suite.t ->
    recipient:Public_key.t ->
    sender:Private_key.t ->
    psk:Psk.t ->
    info:string ->
    ('capability sender_setup, Error.t) result
  (** Establish an AuthPSK-mode sender context, which authenticates the sender
      as {!setup_auth_sender} does and also mixes in a PSK. Impersonating the
      sender then takes the PSK as well as the recipient's private key. *)

  val setup_auth_psk_receiver :
    'capability Suite.t ->
    recipient:Private_key.t ->
    sender:Public_key.t ->
    psk:Psk.t ->
    encapsulated_key:string ->
    info:string ->
    ('capability Receiver.t, Error.t) result
  (** Establish an AuthPSK-mode receiver context. Errors are reported as by
      {!setup_auth_receiver}. *)

  val seal_base :
    rng:Mirage_crypto_rng.g ->
    Suite.encryption Suite.t ->
    recipient:Public_key.t ->
    info:string ->
    aad:string ->
    plaintext:string ->
    (ciphertext, Error.t) result
  (** Establish, seal one message, and return [enc] and ciphertext separately.
  *)

  val open_base :
    Suite.encryption Suite.t ->
    recipient:Private_key.t ->
    info:string ->
    aad:string ->
    ciphertext:ciphertext ->
    (string, Error.t) result
  (** Open one Base-mode message. Peer-controlled decapsulation and AEAD
      failures are normalized to {!Error.Open_error}. *)

  val seal_psk :
    rng:Mirage_crypto_rng.g ->
    Suite.encryption Suite.t ->
    recipient:Public_key.t ->
    psk:Psk.t ->
    info:string ->
    aad:string ->
    plaintext:string ->
    (ciphertext, Error.t) result
  (** Establish and seal one PSK-mode message. *)

  val open_psk :
    Suite.encryption Suite.t ->
    recipient:Private_key.t ->
    psk:Psk.t ->
    info:string ->
    aad:string ->
    ciphertext:ciphertext ->
    (string, Error.t) result
  (** Open one PSK-mode message with normalized peer failure. *)

  val seal_auth :
    rng:Mirage_crypto_rng.g ->
    Suite.encryption Suite.t ->
    recipient:Public_key.t ->
    sender:Private_key.t ->
    info:string ->
    aad:string ->
    plaintext:string ->
    (ciphertext, Error.t) result
  (** Establish and seal one Auth-mode message. *)

  val open_auth :
    Suite.encryption Suite.t ->
    recipient:Private_key.t ->
    sender:Public_key.t ->
    info:string ->
    aad:string ->
    ciphertext:ciphertext ->
    (string, Error.t) result
  (** Open one Auth-mode message sealed by the holder of the private key of
      [sender]. Every failure other than {!Error.Key_mismatch} is reported as
      {!Error.Open_error}, a message from any other sender included. *)

  val seal_auth_psk :
    rng:Mirage_crypto_rng.g ->
    Suite.encryption Suite.t ->
    recipient:Public_key.t ->
    sender:Private_key.t ->
    psk:Psk.t ->
    info:string ->
    aad:string ->
    plaintext:string ->
    (ciphertext, Error.t) result
  (** Establish and seal one AuthPSK-mode message. *)

  val open_auth_psk :
    Suite.encryption Suite.t ->
    recipient:Private_key.t ->
    sender:Public_key.t ->
    psk:Psk.t ->
    info:string ->
    aad:string ->
    ciphertext:ciphertext ->
    (string, Error.t) result
  (** Open one AuthPSK-mode message. Failures are reported as by {!open_auth}.
  *)
end

(**/**)

module Private : sig
  (* Not part of the public API and excluded from its stability guarantees.
     These functions let the caller choose the sender's ephemeral key, which
     breaks HPKE's security if that key is ever reused or disclosed. They back
     the [hpke.for_testing] library, which is the only supported way to reach
     them. *)

  val setup_base_sender_with_ephemeral :
    'capability Suite.t ->
    ephemeral:Private_key.t ->
    recipient:Public_key.t ->
    info:string ->
    ('capability Rfc9180.sender_setup, Error.t) result

  val setup_psk_sender_with_ephemeral :
    'capability Suite.t ->
    ephemeral:Private_key.t ->
    recipient:Public_key.t ->
    psk:Psk.t ->
    info:string ->
    ('capability Rfc9180.sender_setup, Error.t) result

  val setup_auth_sender_with_ephemeral :
    'capability Suite.t ->
    ephemeral:Private_key.t ->
    recipient:Public_key.t ->
    sender:Private_key.t ->
    info:string ->
    ('capability Rfc9180.sender_setup, Error.t) result

  val setup_auth_psk_sender_with_ephemeral :
    'capability Suite.t ->
    ephemeral:Private_key.t ->
    recipient:Public_key.t ->
    sender:Private_key.t ->
    psk:Psk.t ->
    info:string ->
    ('capability Rfc9180.sender_setup, Error.t) result
end

(**/**)
