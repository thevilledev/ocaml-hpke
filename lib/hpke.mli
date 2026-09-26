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
    | Unsupported_mode
        (** The suite's KEM does not provide the requested mode. ML-KEM and the
            PQ/T hybrid KEMs have no Auth or AuthPSK mode: see
            {!Kem.supports_auth}. *)
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
  (** The closed registry of supported HPKE KEM identifiers.

      [P256] to [X448] are the Diffie-Hellman KEMs of RFC 9180. [Mlkem512],
      [Mlkem768], and [Mlkem1024] are the post-quantum ML-KEM (FIPS 203) KEMs,
      identifiers [0x0040] to [0x0042], as [draft-ietf-hpke-pq-05] specifies
      them. They work in the Base and PSK modes. That draft is not yet an RFC:
      the encodings below are those of FIPS 203 and are not expected to move,
      but {!derive_key_pair} follows the draft and changes if the draft does.
      The draft prefers [Mlkem768] and [Mlkem1024] to [Mlkem512], as a hedge
      against cryptanalysis that weakens ML-KEM without breaking it.

      [Mlkem768_p256] (MLKEM768-P256, [0x0050]), [Mlkem768_x25519]
      (MLKEM768-X25519, [0x647a]), and [Mlkem1024_p384] (MLKEM1024-P384,
      [0x0051]) are the post-quantum/traditional hybrid KEMs of the same draft,
      as [draft-irtf-cfrg-concrete-hybrid-kems] defines them: ML-KEM combined
      with an elliptic-curve group, secure as long as either half is.
      [Mlkem768_x25519] is X-Wing. They work in the Base and PSK modes. A public
      key is the ML-KEM key followed by the group element, an encapsulated key
      the ML-KEM ciphertext followed by an ephemeral element, and a private key
      the 32-byte seed that both halves are derived from. *)
  type id =
    | P256
    | P384
    | P521
    | X25519
    | X448
    | Mlkem512
    | Mlkem768
    | Mlkem1024
    | Mlkem768_p256
    | Mlkem768_x25519
    | Mlkem1024_p384

  val to_int : id -> int
  val of_int : int -> (id, Error.t) result
  val pp : Format.formatter -> id -> unit

  val public_key_size : id -> int
  (** [Npk]. An ML-KEM public key is a FIPS 203 encapsulation key. A hybrid one
      appends an uncompressed SEC1 point, or an X25519 public value, to it. *)

  val private_key_size : id -> int
  (** [Nsk]. An ML-KEM private key is the 64-byte seed [d || z] of FIPS 203, and
      not the expanded decapsulation key. A hybrid private key is a 32-byte
      seed. *)

  val encapsulated_key_size : id -> int
  (** [Nenc]. A Diffie-Hellman KEM encapsulates to a public key, so this is
      {!public_key_size}; ML-KEM encapsulates to a ciphertext, whose size
      differs from that of a key, and a hybrid KEM to that ciphertext and an
      ephemeral group element. *)

  val secret_size : id -> int
  (** [Nsecret], the length in bytes of the KEM shared secret. *)

  val supports_auth : id -> bool
  (** Whether the KEM provides the Auth and AuthPSK modes: the "Auth" column of
      the IANA HPKE KEM registry. It is [true] for the Diffie-Hellman KEMs and
      [false] for ML-KEM and the hybrid KEMs, which have no authenticated
      encapsulation. With such a KEM the [auth] functions of {!Rfc9180} return
      {!Error.Unsupported_mode}. *)
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
      used. An ML-KEM encapsulation key must pass the modulus check of FIPS 203,
      Section 7.2: every coefficient reduced. Parsing one expands its public
      matrix, so parse a key once for everything sealed to it. A hybrid key must
      pass that check for its ML-KEM half, and its element is validated as a key
      of its group: an uncompressed point on P-256 or P-384, or for X25519 when
      it is used. *)

  val to_bytes : t -> string
  val kem : t -> Kem.id
end

module Private_key : sig
  type t
  (** A validated private key tagged with its KEM. Values are abstract but
      cannot be reliably zeroized by the OCaml garbage collector. *)

  val of_bytes : kem:Kem.id -> string -> (t, Error.t) result
  (** Parse and validate an exact-length key. X25519 and X448 input is clamped.
      Every 64-byte string is an ML-KEM seed; parsing one runs the whole of
      ML-KEM key generation, so parse a key once and keep it. A hybrid seed is
      expanded with SHAKE256 into an ML-KEM seed and a scalar, and so costs as
      much. P-256 and P-384 draw the scalar by rejection sampling, which fails
      with negligible probability and is then reported as
      {!Error.Invalid_private_key}. *)

  val to_bytes : t -> string
  (** Serialize the key. X25519 and X448 output is clamped as required by RFC
      9180. An ML-KEM or hybrid key is serialized as its seed. *)

  val kem : t -> Kem.id
  val public_key : t -> Public_key.t
end

val generate_key_pair :
  rng:Mirage_crypto_rng.g ->
  Kem.id ->
  (Private_key.t * Public_key.t, Error.t) result
(** Generate a key pair using the explicitly supplied random generator. An
    ML-KEM key pair is that of [ML-KEM.KeyGen] (FIPS 203) with 64 bytes of the
    generator's output as its seed, and a hybrid one that of 32 bytes. *)

val derive_key_pair :
  Kem.id -> ikm:string -> (Private_key.t * Public_key.t, Error.t) result
(** Deterministically derive a key pair: as specified by RFC 9180 for its
    Diffie-Hellman KEMs, and for ML-KEM and the hybrid KEMs by
    [draft-ietf-hpke-pq-05], which derives the seed from [ikm] with SHAKE256.
    [ikm] should hold at least {!Kem.private_key_size} bytes of entropy. *)

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
      changed by a future HPKE standard.

      With an ML-KEM suite the Base and PSK modes run the RFC 9180 key schedule
      unchanged, and the encapsulated key is an ML-KEM ciphertext. Two things
      differ from a Diffie-Hellman KEM. The [auth] functions return
      {!Error.Unsupported_mode}. And an encapsulated key of the right length
      never fails to decapsulate: for one that was tampered with or made for
      another key, ML-KEM yields a secret unrelated to the sender's (implicit
      rejection, FIPS 203), so a receiver is set up without an error and the
      failure surfaces as {!Error.Open_error} on its first {!Receiver.open_}, or
      as exports that differ from the sender's.

      A hybrid suite behaves as an ML-KEM one, except that the ephemeral element
      in its encapsulated key is validated: one that is not a point on the
      curve, or an X25519 value of low order, is reported as
      {!Error.Invalid_encapsulation}. [draft-irtf-cfrg-concrete-hybrid-kems]
      does not check the X25519 value, and an honest sender never produces one
      that fails, so this refuses only input that could not come from one. *)

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
      reported structurally at this context-level API. For ML-KEM that is a
      wrong length only, and for a hybrid KEM a wrong length or an invalid
      element: see {!Rfc9180}. *)

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
      the ciphertexts. Returns {!Error.Unsupported_mode} if the suite's KEM has
      no Auth mode, as ML-KEM and the hybrid KEMs do not, and otherwise
      {!Error.Key_mismatch} unless the suite and both keys share one KEM. *)

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
      [sender]. Every failure other than {!Error.Key_mismatch} and
      {!Error.Unsupported_mode}, which only the caller can cause, is reported as
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

module Draft_hpke_04 : sig
  (** The successor of RFC 9180 as [draft-ietf-hpke-hpke-04] specifies it, with
      the one-stage SHA-3 KDFs of [draft-ietf-hpke-pq-05], Section 5.

      This is a separate, versioned module, so that {!Rfc9180} keeps its wire
      behavior: nothing here changes what an {!Rfc9180} function does. The draft
      is not yet an RFC, and this module follows revision 04 of it; a later
      revision that changes the wire gets a module of its own.

      The draft is RFC 9180 without the Auth and AuthPSK modes, and with a
      second kind of KDF. With an HKDF a suite runs the RFC 9180 Base and PSK
      modes unchanged, so its keys, encapsulations, ciphertexts and exports are
      those of {!Rfc9180}. With a one-stage KDF, SHAKE128 or SHAKE256, the key
      schedule derives the key, base nonce and exporter secret in one call of
      [LabeledDerive], and so does {!Sender.export}. Every KEM works with every
      KDF, those of the draft included. TurboSHAKE128 and TurboSHAKE256
      ([0x0012] and [0x0013]) are not provided yet.

      Keys, KEMs, AEADs, PSKs, errors and contexts are those of the rest of the
      library. {!Private_key.to_bytes} clamps X25519 and X448 keys, where the
      draft serializes them unclamped; both describe the same key pair.

      With a one-stage KDF, [info], a PSK and its identifier may each hold at
      most 65535 bytes (Section 7.2.1), and a longer one is
      {!Error.Invalid_length}. An export may be up to 65535 bytes long. *)

  module Kdf : sig
    (** The KDF registry of [draft-ietf-hpke-hpke-04] and
        [draft-ietf-hpke-pq-05]: the HKDFs of RFC 9180, which are two-stage, and
        the one-stage SHAKE128 ([0x0010]) and SHAKE256 ([0x0011]). *)
    type id = Hkdf_sha256 | Hkdf_sha384 | Hkdf_sha512 | Shake128 | Shake256

    val to_int : id -> int
    val of_int : int -> (id, Error.t) result
    val pp : Format.formatter -> id -> unit

    val hash_size : id -> int
    (** [Nh]: the output length of [Extract] for an HKDF, and the security
        strength in bytes for a one-stage KDF, 32 for SHAKE128 and 64 for
        SHAKE256. *)

    val two_stage : id -> Kdf.id option
    (** The RFC 9180 KDF of a two-stage KDF, whose {!Hpke.Kdf.extract} and
        {!Hpke.Kdf.expand} are its [Extract] and [Expand]; [None] for a
        one-stage KDF. *)

    val derive : id -> string -> int -> (string, Error.t) result
    (** [derive id ikm length] is the unlabeled [Derive(ikm, L)] of a one-stage
        KDF, for protocols layered on HPKE: SHAKE128 or SHAKE256 of [ikm], cut
        to [length] bytes. Returns {!Error.Unsupported_algorithm} for a
        two-stage KDF, and {!Error.Invalid_length} for a negative [length]. *)
  end

  module Suite : sig
    type encryption = Suite.encryption
    type export_only = Suite.export_only

    type _ t
    (** A ciphersuite of this module. Its capabilities are those of
        {!Hpke.Suite}, so that its contexts are those of {!Rfc9180}. *)

    val create : kem:Kem.id -> kdf:Kdf.id -> aead:Aead.id -> encryption t
    val export_only : kem:Kem.id -> kdf:Kdf.id -> export_only t
    val kem : _ t -> Kem.id
    val kdf : _ t -> Kdf.id
    val aead : encryption t -> Aead.id
  end

  module Sender = Rfc9180.Sender
  module Receiver = Rfc9180.Receiver

  type 'capability sender_setup = 'capability Rfc9180.sender_setup = {
    encapsulated_key : string;
    context : 'capability Sender.t;
  }

  type ciphertext = Rfc9180.ciphertext = {
    encapsulated_key : string;
    ciphertext : string;
  }

  val setup_base_sender :
    rng:Mirage_crypto_rng.g ->
    'capability Suite.t ->
    recipient:Public_key.t ->
    info:string ->
    ('capability sender_setup, Error.t) result
  (** As {!Rfc9180.setup_base_sender}. Returns {!Error.Key_mismatch} unless the
      suite and the key share one KEM. *)

  val setup_base_receiver :
    'capability Suite.t ->
    recipient:Private_key.t ->
    encapsulated_key:string ->
    info:string ->
    ('capability Receiver.t, Error.t) result
  (** As {!Rfc9180.setup_base_receiver}. *)

  val setup_psk_sender :
    rng:Mirage_crypto_rng.g ->
    'capability Suite.t ->
    recipient:Public_key.t ->
    psk:Psk.t ->
    info:string ->
    ('capability sender_setup, Error.t) result
  (** As {!Rfc9180.setup_psk_sender}. *)

  val setup_psk_receiver :
    'capability Suite.t ->
    recipient:Private_key.t ->
    psk:Psk.t ->
    encapsulated_key:string ->
    info:string ->
    ('capability Receiver.t, Error.t) result
  (** As {!Rfc9180.setup_psk_receiver}. *)

  val seal_base :
    rng:Mirage_crypto_rng.g ->
    Suite.encryption Suite.t ->
    recipient:Public_key.t ->
    info:string ->
    aad:string ->
    plaintext:string ->
    (ciphertext, Error.t) result
  (** As {!Rfc9180.seal_base}. *)

  val open_base :
    Suite.encryption Suite.t ->
    recipient:Private_key.t ->
    info:string ->
    aad:string ->
    ciphertext:ciphertext ->
    (string, Error.t) result
  (** As {!Rfc9180.open_base}: every failure other than {!Error.Key_mismatch} is
      {!Error.Open_error}. *)

  val seal_psk :
    rng:Mirage_crypto_rng.g ->
    Suite.encryption Suite.t ->
    recipient:Public_key.t ->
    psk:Psk.t ->
    info:string ->
    aad:string ->
    plaintext:string ->
    (ciphertext, Error.t) result
  (** As {!Rfc9180.seal_psk}. *)

  val open_psk :
    Suite.encryption Suite.t ->
    recipient:Private_key.t ->
    psk:Psk.t ->
    info:string ->
    aad:string ->
    ciphertext:ciphertext ->
    (string, Error.t) result
  (** As {!Rfc9180.open_psk}. *)
end

(**/**)

module Private : sig
  (* Not part of the public API and excluded from its stability guarantees.
     These functions let the caller choose the sender's ephemeral key, which
     breaks HPKE's security if that key is ever reused or disclosed. They back
     the [hpke.for_testing] library, which is the only supported way to reach
     them. ML-KEM and the hybrid KEMs encapsulate without an ephemeral key, so
     with such a suite the Base and PSK ones return [Invalid_private_key]. The
     Auth and AuthPSK ones return [Unsupported_mode] there, as those KEMs have
     neither mode. *)

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
