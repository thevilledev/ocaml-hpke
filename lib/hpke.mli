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
  type id = P256 | P384 | P521 | X25519

  val to_int : id -> int
  val of_int : int -> (id, Error.t) result
  val pp : Format.formatter -> id -> unit
  val public_key_size : id -> int
  val private_key_size : id -> int
  val encapsulated_key_size : id -> int
end

module Kdf : sig
  (** The closed registry of supported RFC 9180 KDF identifiers. *)
  type id = Hkdf_sha256 | Hkdf_sha384 | Hkdf_sha512

  val to_int : id -> int
  val of_int : int -> (id, Error.t) result
  val pp : Format.formatter -> id -> unit
end

module Aead : sig
  (** The closed registry of supported encryption AEAD identifiers. Export-only
      operation is represented separately by [Suite.export_only]. *)
  type id = Aes_128_gcm | Aes_256_gcm | Chacha20_poly1305

  val to_int : id -> int
  val of_int : int -> (id, Error.t) result
  val pp : Format.formatter -> id -> unit
end

module Public_key : sig
  type t
  (** A validated public key tagged with its KEM. *)

  val of_bytes : kem:Kem.id -> string -> (t, Error.t) result
  (** Parse an exact-length canonical encoding. NIST keys must use uncompressed
      SEC1 form. X25519 low-order rejection occurs when the key is used. *)

  val to_bytes : t -> string
  val kem : t -> Kem.id
end

module Private_key : sig
  type t
  (** A validated private key tagged with its KEM. Values are abstract but
      cannot be reliably zeroized by the OCaml garbage collector. *)

  val of_bytes : kem:Kem.id -> string -> (t, Error.t) result
  (** Parse and validate an exact-length key. X25519 input is clamped. *)

  val to_bytes : t -> string
  (** Serialize the key. X25519 output is clamped as required by RFC 9180. *)

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
    (** Authenticate and decrypt using the next context nonce. Authentication
        failure does not advance sequence state. *)

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
end
