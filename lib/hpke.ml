module Error = struct
  type t =
    | Unsupported_algorithm of int
    | Invalid_public_key of string
    | Invalid_private_key of string
    | Invalid_encapsulation of string
    | Key_mismatch
    | Unsupported_mode
    | Derive_key_pair_failure
    | Invalid_psk of string
    | Invalid_length of string
    | Message_limit_reached
    | Plaintext_too_long
    | Export_length_out_of_range
    | Concurrent_use
    | Open_error
    | Internal_error of string

  let pp ppf = function
    | Unsupported_algorithm id ->
        Format.fprintf ppf "unsupported algorithm identifier 0x%04x" id
    | Invalid_public_key reason ->
        Format.fprintf ppf "invalid public key: %s" reason
    | Invalid_private_key reason ->
        Format.fprintf ppf "invalid private key: %s" reason
    | Invalid_encapsulation reason ->
        Format.fprintf ppf "invalid encapsulated key: %s" reason
    | Key_mismatch -> Format.pp_print_string ppf "key and suite KEM differ"
    | Unsupported_mode ->
        Format.pp_print_string ppf
          "the KEM does not support the Auth and AuthPSK modes"
    | Derive_key_pair_failure ->
        Format.pp_print_string ppf "could not derive a valid key pair"
    | Invalid_psk reason -> Format.fprintf ppf "invalid PSK: %s" reason
    | Invalid_length reason -> Format.fprintf ppf "invalid length: %s" reason
    | Message_limit_reached ->
        Format.pp_print_string ppf "HPKE context message limit reached"
    | Plaintext_too_long -> Format.pp_print_string ppf "plaintext is too long"
    | Export_length_out_of_range ->
        Format.pp_print_string ppf "export length is out of range"
    | Concurrent_use ->
        Format.pp_print_string ppf "concurrent use of an HPKE context"
    | Open_error -> Format.pp_print_string ppf "HPKE open failed"
    | Internal_error reason -> Format.fprintf ppf "internal error: %s" reason
end

module Kem = struct
  type id =
    | P256
    | P384
    | P521
    | X25519
    | X448
    | Mlkem512
    | Mlkem768
    | Mlkem1024

  let to_int = function
    | P256 -> 0x0010
    | P384 -> 0x0011
    | P521 -> 0x0012
    | X25519 -> 0x0020
    | X448 -> 0x0021
    | Mlkem512 -> 0x0040
    | Mlkem768 -> 0x0041
    | Mlkem1024 -> 0x0042

  let of_int = function
    | 0x0010 -> Ok P256
    | 0x0011 -> Ok P384
    | 0x0012 -> Ok P521
    | 0x0020 -> Ok X25519
    | 0x0021 -> Ok X448
    | 0x0040 -> Ok Mlkem512
    | 0x0041 -> Ok Mlkem768
    | 0x0042 -> Ok Mlkem1024
    | id -> Error (Error.Unsupported_algorithm id)

  let pp ppf = function
    | P256 -> Format.pp_print_string ppf "DHKEM(P-256, HKDF-SHA256)"
    | P384 -> Format.pp_print_string ppf "DHKEM(P-384, HKDF-SHA384)"
    | P521 -> Format.pp_print_string ppf "DHKEM(P-521, HKDF-SHA512)"
    | X25519 -> Format.pp_print_string ppf "DHKEM(X25519, HKDF-SHA256)"
    | X448 -> Format.pp_print_string ppf "DHKEM(X448, HKDF-SHA512)"
    | Mlkem512 -> Format.pp_print_string ppf "ML-KEM-512"
    | Mlkem768 -> Format.pp_print_string ppf "ML-KEM-768"
    | Mlkem1024 -> Format.pp_print_string ppf "ML-KEM-1024"

  let public_key_size = function
    | P256 -> 65
    | P384 -> 97
    | P521 -> 133
    | X25519 -> 32
    | X448 -> 56
    | Mlkem512 -> 800
    | Mlkem768 -> 1184
    | Mlkem1024 -> 1568

  (* An ML-KEM private key is the 64-byte seed d || z of FIPS 203. *)
  let private_key_size = function
    | P256 -> 32
    | P384 -> 48
    | P521 -> 66
    | X25519 -> 32
    | X448 -> 56
    | Mlkem512 | Mlkem768 | Mlkem1024 -> 64

  (* A DHKEM encapsulation is an ephemeral public key. An ML-KEM one is a
     ciphertext, whose size is not that of a key. *)
  let encapsulated_key_size = function
    | (P256 | P384 | P521 | X25519 | X448) as kem -> public_key_size kem
    | Mlkem512 -> 768
    | Mlkem768 -> 1088
    | Mlkem1024 -> 1568

  let secret_size = function
    | P256 -> 32
    | P384 -> 48
    | P521 -> 64
    | X25519 -> 32
    | X448 -> 64
    | Mlkem512 | Mlkem768 | Mlkem1024 -> 32

  let supports_auth = function
    | P256 | P384 | P521 | X25519 | X448 -> true
    | Mlkem512 | Mlkem768 | Mlkem1024 -> false
end

module Kdf = struct
  type id = Hkdf_sha256 | Hkdf_sha384 | Hkdf_sha512

  let to_int = function
    | Hkdf_sha256 -> 0x0001
    | Hkdf_sha384 -> 0x0002
    | Hkdf_sha512 -> 0x0003

  let of_int = function
    | 0x0001 -> Ok Hkdf_sha256
    | 0x0002 -> Ok Hkdf_sha384
    | 0x0003 -> Ok Hkdf_sha512
    | id -> Error (Error.Unsupported_algorithm id)

  let pp ppf = function
    | Hkdf_sha256 -> Format.pp_print_string ppf "HKDF-SHA256"
    | Hkdf_sha384 -> Format.pp_print_string ppf "HKDF-SHA384"
    | Hkdf_sha512 -> Format.pp_print_string ppf "HKDF-SHA512"

  let hash = function
    | Hkdf_sha256 -> `SHA256
    | Hkdf_sha384 -> `SHA384
    | Hkdf_sha512 -> `SHA512

  let hash_size = function
    | Hkdf_sha256 -> 32
    | Hkdf_sha384 -> 48
    | Hkdf_sha512 -> 64

  let extract id ~salt ikm = Hkdf.extract ~hash:(hash id) ~salt ikm

  (* Callers inside this module pass lengths that are already in range. *)
  let expand_unchecked id ~prk ~info length =
    Hkdf.expand ~hash:(hash id) ~prk ~info length

  let expand id ~prk ~info length =
    if String.length prk < hash_size id then
      Error
        (Error.Invalid_length
           "the pseudorandom key is shorter than the hash output")
    else if length < 0 || length > 255 * hash_size id then
      Error (Error.Invalid_length "the output length is out of range")
    else Ok (expand_unchecked id ~prk ~info length)
end

module Aead = struct
  type id = Aes_128_gcm | Aes_256_gcm | Chacha20_poly1305

  let to_int = function
    | Aes_128_gcm -> 0x0001
    | Aes_256_gcm -> 0x0002
    | Chacha20_poly1305 -> 0x0003

  let of_int = function
    | 0x0001 -> Ok Aes_128_gcm
    | 0x0002 -> Ok Aes_256_gcm
    | 0x0003 -> Ok Chacha20_poly1305
    | id -> Error (Error.Unsupported_algorithm id)

  let pp ppf = function
    | Aes_128_gcm -> Format.pp_print_string ppf "AES-128-GCM"
    | Aes_256_gcm -> Format.pp_print_string ppf "AES-256-GCM"
    | Chacha20_poly1305 -> Format.pp_print_string ppf "ChaCha20-Poly1305"

  let key_size = function
    | Aes_128_gcm -> 16
    | Aes_256_gcm | Chacha20_poly1305 -> 32

  let nonce_size _ = 12
  let tag_size _ = 16

  let plaintext_fits id length =
    let length = Int64.of_int length in
    let maximum =
      match id with
      | Aes_128_gcm | Aes_256_gcm -> Int64.sub (Int64.shift_left 1L 36) 31L
      | Chacha20_poly1305 -> Int64.sub (Int64.shift_left 1L 38) 64L
    in
    Int64.compare length maximum <= 0

  (* Expanding an AES-GCM key derives its GHASH tables, which without hardware
     support costs more than sealing several kilobytes. A key is therefore
     expanded once and kept. *)
  type expanded =
    | Aes_gcm of Mirage_crypto.AES.GCM.key
    | Chacha20 of Mirage_crypto.Chacha20.key

  type key = { id : id; expanded : expanded }

  let expand id secret =
    match id with
    | Aes_128_gcm | Aes_256_gcm ->
        Aes_gcm (Mirage_crypto.AES.GCM.of_secret secret)
    | Chacha20_poly1305 -> Chacha20 (Mirage_crypto.Chacha20.of_secret secret)

  let key id secret =
    if String.length secret <> key_size id then
      Error (Error.Invalid_length "wrong AEAD key length")
    else
      try Ok { id; expanded = expand id secret }
      with Invalid_argument reason -> Error (Error.Internal_error reason)

  let encrypt key ~nonce ~aad plaintext =
    try
      match key.expanded with
      | Aes_gcm key ->
          Ok
            (Mirage_crypto.AES.GCM.authenticate_encrypt ~key ~nonce ~adata:aad
               plaintext)
      | Chacha20 key ->
          Ok
            (Mirage_crypto.Chacha20.authenticate_encrypt ~key ~nonce ~adata:aad
               plaintext)
    with Invalid_argument reason -> Error (Error.Internal_error reason)

  let decrypt key ~nonce ~aad ciphertext =
    try
      let plaintext =
        match key.expanded with
        | Aes_gcm key ->
            Mirage_crypto.AES.GCM.authenticate_decrypt ~key ~nonce ~adata:aad
              ciphertext
        | Chacha20 key ->
            Mirage_crypto.Chacha20.authenticate_decrypt ~key ~nonce ~adata:aad
              ciphertext
      in
      match plaintext with
      | Some plaintext -> Ok plaintext
      | None -> Error Error.Open_error
    with Invalid_argument _ -> Error Error.Open_error

  let check_nonce key nonce =
    if String.length nonce <> nonce_size key.id then
      Error (Error.Invalid_length "wrong AEAD nonce length")
    else Ok ()

  let seal key ~nonce ~aad ~plaintext =
    match check_nonce key nonce with
    | Error _ as error -> error
    | Ok () ->
        if not (plaintext_fits key.id (String.length plaintext)) then
          Error Error.Plaintext_too_long
        else encrypt key ~nonce ~aad plaintext

  let open_ key ~nonce ~aad ~ciphertext =
    match check_nonce key nonce with
    | Error _ as error -> error
    | Ok () ->
        let length = String.length ciphertext in
        if
          length < tag_size key.id
          || not (plaintext_fits key.id (length - tag_size key.id))
        then Error Error.Open_error
        else decrypt key ~nonce ~aad ciphertext
end

module Util = struct
  let ( let* ) value f =
    match value with Ok value -> f value | Error _ as error -> error

  let i2osp2 value =
    if value < 0 || value > 0xffff then invalid_arg "I2OSP(2)";
    String.init 2 (function
      | 0 -> Char.chr ((value lsr 8) land 0xff)
      | _ -> Char.chr (value land 0xff))

  let byte value = String.make 1 (Char.chr value)

  let hex_value = function
    | '0' .. '9' as c -> Char.code c - Char.code '0'
    | 'a' .. 'f' as c -> Char.code c - Char.code 'a' + 10
    | 'A' .. 'F' as c -> Char.code c - Char.code 'A' + 10
    | _ -> invalid_arg "invalid hexadecimal digit"

  let of_hex_exn hex =
    if String.length hex mod 2 <> 0 then invalid_arg "odd hexadecimal string";
    String.init
      (String.length hex / 2)
      (fun i ->
        Char.chr ((hex_value hex.[i * 2] lsl 4) lor hex_value hex.[(i * 2) + 1]))

  let all_zero value =
    let accumulator = ref 0 in
    String.iter
      (fun byte -> accumulator := !accumulator lor Char.code byte)
      value;
    !accumulator = 0

  let normalize_x25519 bytes =
    let bytes = Bytes.of_string bytes in
    Bytes.set_uint8 bytes 0 (Bytes.get_uint8 bytes 0 land 248);
    Bytes.set_uint8 bytes 31 (Bytes.get_uint8 bytes 31 land 127 lor 64);
    Bytes.unsafe_to_string bytes

  let normalize_x448 bytes =
    let bytes = Bytes.of_string bytes in
    Bytes.set_uint8 bytes 0 (Bytes.get_uint8 bytes 0 land 252);
    Bytes.set_uint8 bytes 55 (Bytes.get_uint8 bytes 55 lor 128);
    Bytes.unsafe_to_string bytes

  let ec_error error = Format.asprintf "%a" Mirage_crypto_ec.pp_error error
end

open Util

let curve_order = function
  | Kem.P256 ->
      Util.of_hex_exn
        "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"
  | Kem.P384 ->
      Util.of_hex_exn
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973"
  | Kem.P521 ->
      Util.of_hex_exn
        "01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409"
  | Kem.X25519 -> invalid_arg "X25519 has no rejection-sampling order"
  | Kem.X448 -> invalid_arg "X448 has no rejection-sampling order"
  | Kem.Mlkem512 | Kem.Mlkem768 | Kem.Mlkem1024 ->
      invalid_arg "ML-KEM has no rejection-sampling order"

let valid_nist_scalar kem bytes =
  String.length bytes = Kem.private_key_size kem
  && (not (Util.all_zero bytes))
  && Eqaf.compare_be bytes (curve_order kem) < 0

(* The ML-KEM parameter sets share this interface over distinct key types. *)
module type MLKEM = sig
  type error

  val pp_error : Format.formatter -> error -> unit

  type encapsulation_key
  type decapsulation_key
  type ciphertext
  type shared_secret

  val decapsulation_key_of_seed : string -> (decapsulation_key, error) result

  val encapsulation_key_of_decapsulation_key :
    decapsulation_key -> encapsulation_key

  val encapsulation_key_of_octets : string -> (encapsulation_key, error) result
  val encapsulation_key_to_octets : encapsulation_key -> string
  val ciphertext_of_octets : string -> (ciphertext, error) result
  val ciphertext_to_octets : ciphertext -> string
  val shared_secret_to_octets : shared_secret -> string

  val encapsulate :
    random:(int -> string) -> encapsulation_key -> ciphertext * shared_secret

  val decapsulate : decapsulation_key -> ciphertext -> shared_secret
end

(* The HPKE KEM of draft-ietf-hpke-pq, Section 3, over one parameter set. Keys
   and encapsulations are serialized as FIPS 203 does, a private key as its
   seed, and the shared secret is that of ML-KEM unchanged. *)
module Mlkem_kem (M : MLKEM) = struct
  (* These name a length or a class of encoding, never key material. *)
  let reason error = Format.asprintf "%a" M.pp_error error

  let public_key bytes =
    Result.map_error
      (fun error -> Error.Invalid_public_key (reason error))
      (M.encapsulation_key_of_octets bytes)

  let private_key seed =
    match M.decapsulation_key_of_seed seed with
    | Error error -> Error (Error.Invalid_private_key (reason error))
    | Ok secret ->
        let public = M.encapsulation_key_of_decapsulation_key secret in
        Ok (secret, public, M.encapsulation_key_to_octets public)

  let encap ~random public =
    let ciphertext, shared_secret = M.encapsulate ~random public in
    (M.shared_secret_to_octets shared_secret, M.ciphertext_to_octets ciphertext)

  (* An encapsulation of the right length always decapsulates: for one that was
     not made for this key, FIPS 203 returns a secret unrelated to the sender's
     and no error (implicit rejection). *)
  let decap secret encapsulated_key =
    match M.ciphertext_of_octets encapsulated_key with
    | Error error -> Error (Error.Invalid_encapsulation (reason error))
    | Ok ciphertext ->
        Ok (M.shared_secret_to_octets (M.decapsulate secret ciphertext))
end

module Mlkem512_kem = Mlkem_kem (Mlkem.Mlkem512)
module Mlkem768_kem = Mlkem_kem (Mlkem.Mlkem768)
module Mlkem1024_kem = Mlkem_kem (Mlkem.Mlkem1024)

(* A DHKEM public key is validated when it is parsed and then used as bytes.
   Parsing an ML-KEM encapsulation key expands its public matrix, which every
   encapsulation would otherwise repeat, so that key is parsed once and kept. *)
type public_material =
  | Dh_public
  | Mlkem512_public of Mlkem.Mlkem512.encapsulation_key
  | Mlkem768_public of Mlkem.Mlkem768.encapsulation_key
  | Mlkem1024_public of Mlkem.Mlkem1024.encapsulation_key

let parse_public_bytes kem bytes =
  if String.length bytes <> Kem.public_key_size kem then
    Error (Error.Invalid_public_key "wrong encoded length")
  else
    match kem with
    | Kem.X25519 | Kem.X448 -> Ok Dh_public
    | Kem.P256 ->
        if bytes.[0] <> '\004' then
          Error
            (Error.Invalid_public_key
               "only canonical uncompressed SEC1 encodings are accepted")
        else
          Result.map_error
            (fun error -> Error.Invalid_public_key (Util.ec_error error))
            (Result.map
               (fun _ -> Dh_public)
               (Mirage_crypto_ec.P256.Dsa.pub_of_octets bytes))
    | Kem.P384 ->
        if bytes.[0] <> '\004' then
          Error
            (Error.Invalid_public_key
               "only canonical uncompressed SEC1 encodings are accepted")
        else
          Result.map_error
            (fun error -> Error.Invalid_public_key (Util.ec_error error))
            (Result.map
               (fun _ -> Dh_public)
               (Mirage_crypto_ec.P384.Dsa.pub_of_octets bytes))
    | Kem.P521 ->
        if bytes.[0] <> '\004' then
          Error
            (Error.Invalid_public_key
               "only canonical uncompressed SEC1 encodings are accepted")
        else
          Result.map_error
            (fun error -> Error.Invalid_public_key (Util.ec_error error))
            (Result.map
               (fun _ -> Dh_public)
               (Mirage_crypto_ec.P521.Dsa.pub_of_octets bytes))
    (* The modulus check of FIPS 203, Section 7.2. *)
    | Kem.Mlkem512 ->
        Result.map
          (fun key -> Mlkem512_public key)
          (Mlkem512_kem.public_key bytes)
    | Kem.Mlkem768 ->
        Result.map
          (fun key -> Mlkem768_public key)
          (Mlkem768_kem.public_key bytes)
    | Kem.Mlkem1024 ->
        Result.map
          (fun key -> Mlkem1024_public key)
          (Mlkem1024_kem.public_key bytes)

module Public_key = struct
  type t = { kem : Kem.id; bytes : string; material : public_material }

  let of_bytes ~kem bytes =
    let* material = parse_public_bytes kem bytes in
    Ok { kem; bytes; material }

  let to_bytes key = key.bytes
  let kem key = key.kem
end

(* Parsing a secret derives its public key, a scalar multiplication that for
   X25519 and X448 costs as much as the exchange itself, and for ML-KEM the
   whole of key generation. A secret is therefore parsed once, with its key, and
   kept. *)
type kem_secret =
  | P256_secret of Mirage_crypto_ec.P256.Dh.secret
  | P384_secret of Mirage_crypto_ec.P384.Dh.secret
  | P521_secret of Mirage_crypto_ec.P521.Dh.secret
  | X25519_secret of Mirage_crypto_ec.X25519.secret
  | X448_secret of Curve448.X448.secret
  | Mlkem512_secret of Mlkem.Mlkem512.decapsulation_key
  | Mlkem768_secret of Mlkem.Mlkem768.decapsulation_key
  | Mlkem1024_secret of Mlkem.Mlkem1024.decapsulation_key

let secret_and_public kem bytes =
  (* A Diffie-Hellman secret yields the encoding of its public key, which is
     validated as any other. *)
  let dh wrap parsed =
    match parsed with
    | Error error -> Error (Error.Invalid_private_key (Util.ec_error error))
    | Ok (secret, public) ->
        let* public_key = Public_key.of_bytes ~kem public in
        Ok (wrap secret, public_key)
  in
  (* An ML-KEM secret yields the encapsulation key itself, already parsed. *)
  let mlkem wrap_secret wrap_public parsed =
    let* secret, public, bytes = parsed in
    Ok
      ( wrap_secret secret,
        { Public_key.kem; bytes; material = wrap_public public } )
  in
  match kem with
  | Kem.P256 ->
      dh
        (fun secret -> P256_secret secret)
        (Mirage_crypto_ec.P256.Dh.secret_of_octets ~compress:false bytes)
  | Kem.P384 ->
      dh
        (fun secret -> P384_secret secret)
        (Mirage_crypto_ec.P384.Dh.secret_of_octets ~compress:false bytes)
  | Kem.P521 ->
      dh
        (fun secret -> P521_secret secret)
        (Mirage_crypto_ec.P521.Dh.secret_of_octets ~compress:false bytes)
  | Kem.X25519 ->
      dh
        (fun secret -> X25519_secret secret)
        (Mirage_crypto_ec.X25519.secret_of_octets bytes)
  | Kem.X448 ->
      dh
        (fun secret -> X448_secret secret)
        (Curve448.X448.secret_of_octets bytes)
  | Kem.Mlkem512 ->
      mlkem
        (fun secret -> Mlkem512_secret secret)
        (fun public -> Mlkem512_public public)
        (Mlkem512_kem.private_key bytes)
  | Kem.Mlkem768 ->
      mlkem
        (fun secret -> Mlkem768_secret secret)
        (fun public -> Mlkem768_public public)
        (Mlkem768_kem.private_key bytes)
  | Kem.Mlkem1024 ->
      mlkem
        (fun secret -> Mlkem1024_secret secret)
        (fun public -> Mlkem1024_public public)
        (Mlkem1024_kem.private_key bytes)

module Private_key = struct
  type t = {
    kem : Kem.id;
    bytes : string;
    secret : kem_secret;
    public_key : Public_key.t;
  }

  let of_bytes ~kem bytes =
    if String.length bytes <> Kem.private_key_size kem then
      Error (Error.Invalid_private_key "wrong encoded length")
    else
      let* bytes =
        match kem with
        | Kem.X25519 -> Ok (Util.normalize_x25519 bytes)
        | Kem.X448 -> Ok (Util.normalize_x448 bytes)
        | Kem.P256 | Kem.P384 | Kem.P521 ->
            if valid_nist_scalar kem bytes then Ok bytes
            else
              Error
                (Error.Invalid_private_key "scalar is outside the valid range")
        (* Every string of the right length is an ML-KEM seed. *)
        | Kem.Mlkem512 | Kem.Mlkem768 | Kem.Mlkem1024 -> Ok bytes
      in
      let* secret, public_key = secret_and_public kem bytes in
      Ok { kem; bytes; secret; public_key }

  let to_bytes key = key.bytes
  let kem key = key.kem
  let public_key key = key.public_key
end

module Psk = struct
  type t = { secret : string; id : string }

  let create ~secret ~id =
    if String.length secret < 32 then
      Error (Error.Invalid_psk "the secret must contain at least 32 bytes")
    else if String.length id = 0 then
      Error (Error.Invalid_psk "the identifier must not be empty")
    else Ok { secret; id }

  let id psk = psk.id
end

module Suite = struct
  type encryption
  type export_only

  type _ t =
    | Encryption : {
        kem : Kem.id;
        kdf : Kdf.id;
        aead : Aead.id;
      }
        -> encryption t
    | Export_only : { kem : Kem.id; kdf : Kdf.id } -> export_only t

  let create ~kem ~kdf ~aead = Encryption { kem; kdf; aead }
  let export_only ~kem ~kdf = Export_only { kem; kdf }

  let kem : type capability. capability t -> Kem.id = function
    | Encryption suite -> suite.kem
    | Export_only suite -> suite.kem

  let kdf : type capability. capability t -> Kdf.id = function
    | Encryption suite -> suite.kdf
    | Export_only suite -> suite.kdf

  let[@warning "-8"] aead (Encryption suite) = suite.aead

  let aead_id : type capability. capability t -> int = function
    | Encryption suite -> Aead.to_int suite.aead
    | Export_only _ -> 0xffff
end

module Labeled_kdf = struct
  let version_label = "HPKE-v1"

  let suite_id suite =
    "HPKE"
    ^ Util.i2osp2 (Kem.to_int (Suite.kem suite))
    ^ Util.i2osp2 (Kdf.to_int (Suite.kdf suite))
    ^ Util.i2osp2 (Suite.aead_id suite)

  let kem_suite_id kem = "KEM" ^ Util.i2osp2 (Kem.to_int kem)

  let extract ~kdf ~suite_id ~salt ~label ikm =
    Kdf.extract kdf ~salt (version_label ^ suite_id ^ label ^ ikm)

  let expand ~kdf ~suite_id ~prk ~label ~info length =
    Kdf.expand_unchecked kdf ~prk
      ~info:(Util.i2osp2 length ^ version_label ^ suite_id ^ label ^ info)
      length

  (* The KDF of a DHKEM. ML-KEM has none: what it derives, it derives with
     [kem_derive_shake256]. *)
  let kem_kdf = function
    | Kem.P256 | Kem.X25519 -> Kdf.Hkdf_sha256
    | Kem.P384 -> Kdf.Hkdf_sha384
    | Kem.P521 | Kem.X448 -> Kdf.Hkdf_sha512
    | Kem.Mlkem512 | Kem.Mlkem768 | Kem.Mlkem1024 ->
        invalid_arg "ML-KEM has no KEM KDF"

  let kem_extract kem ~salt ~label ikm =
    extract ~kdf:(kem_kdf kem) ~suite_id:(kem_suite_id kem) ~salt ~label ikm

  let kem_expand kem ~prk ~label ~info length =
    expand ~kdf:(kem_kdf kem) ~suite_id:(kem_suite_id kem) ~prk ~label ~info
      length

  (* LabeledDerive of draft-ietf-hpke-hpke, Section 4.4, over the one-stage
     SHAKE256 KDF of draft-ietf-hpke-pq, Section 5. Unlike the two-stage
     functions above it puts the input first and frames the label with its
     length. SHAKE256 is the one ML-KEM itself runs on. *)
  let kem_derive_shake256 kem ~label ~context ikm length =
    Mlkem.Fips202.shake256 ~output_length:length
      (ikm ^ version_label ^ kem_suite_id kem
      ^ Util.i2osp2 (String.length label)
      ^ label ^ Util.i2osp2 length ^ context)
end

let derive_key_pair_inner kem ~ikm =
  (* Only a DHKEM extracts it. *)
  let dkp_prk =
    lazy (Labeled_kdf.kem_extract kem ~salt:"" ~label:"dkp_prk" ikm)
  in
  let candidate counter =
    Labeled_kdf.kem_expand kem ~prk:(Lazy.force dkp_prk) ~label:"candidate"
      ~info:(Util.byte counter) (Kem.private_key_size kem)
  in
  let secret () =
    Labeled_kdf.kem_expand kem ~prk:(Lazy.force dkp_prk) ~label:"sk" ~info:""
      (Kem.private_key_size kem)
  in
  let secret_result =
    match kem with
    | Kem.X25519 -> Ok (Util.normalize_x25519 (secret ()))
    | Kem.X448 -> Ok (Util.normalize_x448 (secret ()))
    (* draft-ietf-hpke-pq, Section 3: the seed is derived in one step. *)
    | Kem.Mlkem512 | Kem.Mlkem768 | Kem.Mlkem1024 ->
        Ok
          (Labeled_kdf.kem_derive_shake256 kem ~label:"DeriveKeyPair"
             ~context:"" ikm (Kem.private_key_size kem))
    | Kem.P256 | Kem.P384 | Kem.P521 ->
        let rec sample counter =
          if counter > 255 then Error Error.Derive_key_pair_failure
          else
            let candidate = Bytes.of_string (candidate counter) in
            if kem = Kem.P521 then
              Bytes.set_uint8 candidate 0 (Bytes.get_uint8 candidate 0 land 0x01);
            let candidate = Bytes.unsafe_to_string candidate in
            if valid_nist_scalar kem candidate then Ok candidate
            else sample (counter + 1)
        in
        sample 0
  in
  let* secret = secret_result in
  let* private_key = Private_key.of_bytes ~kem secret in
  Ok (private_key, Private_key.public_key private_key)

let derive_key_pair kem ~ikm =
  try derive_key_pair_inner kem ~ikm
  with Invalid_argument reason -> Error (Error.Invalid_length reason)

let generate_key_pair ~rng kem =
  let rec generate attempts =
    if attempts = 0 then Error Error.Derive_key_pair_failure
    else
      let ikm = Mirage_crypto_rng.generate ~g:rng (Kem.private_key_size kem) in
      match derive_key_pair kem ~ikm with
      | Ok _ as pair -> pair
      | Error Error.Derive_key_pair_failure -> generate (attempts - 1)
      | Error _ as error -> error
  in
  match kem with
  | Kem.P256 | Kem.P384 | Kem.P521 | Kem.X25519 | Kem.X448 -> generate 8
  (* GenerateKeyPair of draft-ietf-hpke-pq, Section 3: the randomness is the
     seed itself, which makes this ML-KEM.KeyGen of FIPS 203. *)
  | Kem.Mlkem512 | Kem.Mlkem768 | Kem.Mlkem1024 ->
      let seed = Mirage_crypto_rng.generate ~g:rng (Kem.private_key_size kem) in
      let* private_key = Private_key.of_bytes ~kem seed in
      Ok (private_key, Private_key.public_key private_key)

let dh private_key public_key =
  if Private_key.kem private_key <> Public_key.kem public_key then
    Error Error.Key_mismatch
  else
    let public = Public_key.to_bytes public_key in
    let of_exchange =
      Result.map_error (fun error ->
          Error.Invalid_public_key (Util.ec_error error))
    in
    match private_key.Private_key.secret with
    | P256_secret secret ->
        of_exchange (Mirage_crypto_ec.P256.Dh.key_exchange secret public)
    | P384_secret secret ->
        of_exchange (Mirage_crypto_ec.P384.Dh.key_exchange secret public)
    | P521_secret secret ->
        of_exchange (Mirage_crypto_ec.P521.Dh.key_exchange secret public)
    | X25519_secret secret ->
        of_exchange (Mirage_crypto_ec.X25519.key_exchange secret public)
    | X448_secret secret ->
        of_exchange (Curve448.X448.key_exchange secret public)
    (* Only a caller-chosen ephemeral key gets here: ML-KEM encapsulates without
       one, and its authenticated modes are rejected earlier. *)
    | Mlkem512_secret _ | Mlkem768_secret _ | Mlkem1024_secret _ ->
        Error
          (Error.Invalid_private_key
             "ML-KEM keys cannot perform a Diffie-Hellman exchange")

let extract_and_expand kem ~dh ~kem_context =
  let eae_prk = Labeled_kdf.kem_extract kem ~salt:"" ~label:"eae_prk" dh in
  Labeled_kdf.kem_expand kem ~prk:eae_prk ~label:"shared_secret"
    ~info:kem_context (Kem.secret_size kem)

(* [sender] is the sender's static key in the authenticated modes. AuthEncap and
   AuthDecap (RFC 9180, Section 4.1) append an exchange with it to the ephemeral
   exchange, and its public key to the KEM context. Without it both are empty,
   which leaves Encap and Decap. *)
let encap_with ~ephemeral ~sender recipient =
  let kem = Public_key.kem recipient in
  let* ephemeral_dh = dh ephemeral recipient in
  let* static_dh, sender_public =
    match sender with
    | None -> Ok ("", "")
    | Some sender ->
        let* static_dh = dh sender recipient in
        Ok (static_dh, Public_key.to_bytes (Private_key.public_key sender))
  in
  let encapsulated_key =
    Public_key.to_bytes (Private_key.public_key ephemeral)
  in
  let kem_context =
    encapsulated_key ^ Public_key.to_bytes recipient ^ sender_public
  in
  Ok
    ( extract_and_expand kem ~dh:(ephemeral_dh ^ static_dh) ~kem_context,
      encapsulated_key )

(* ML-KEM has no AuthEncap or AuthDecap (draft-ietf-hpke-pq, Section 7.2).
   [Rfc9180] rejects its authenticated modes before it gets here. Were that
   check ever lost, this one keeps a sender key from being silently dropped,
   which would turn an authenticated mode into an unauthenticated one. *)
let mlkem_without_sender = function
  | None -> Ok ()
  | Some _ -> Error Error.Unsupported_mode

let encap ~rng ~sender recipient =
  let random length = Mirage_crypto_rng.generate ~g:rng length in
  match recipient.Public_key.material with
  | Dh_public ->
      let* ephemeral, _ = generate_key_pair ~rng (Public_key.kem recipient) in
      encap_with ~ephemeral ~sender recipient
  | Mlkem512_public public ->
      let* () = mlkem_without_sender sender in
      Ok (Mlkem512_kem.encap ~random public)
  | Mlkem768_public public ->
      let* () = mlkem_without_sender sender in
      Ok (Mlkem768_kem.encap ~random public)
  | Mlkem1024_public public ->
      let* () = mlkem_without_sender sender in
      Ok (Mlkem1024_kem.encap ~random public)

let dh_decap recipient ~sender ~encapsulated_key =
  let kem = Private_key.kem recipient in
  let encapsulated =
    match Public_key.of_bytes ~kem encapsulated_key with
    | Ok key -> Ok key
    | Error (Error.Invalid_public_key reason) ->
        Error (Error.Invalid_encapsulation reason)
    | Error error -> Error error
  in
  let* encapsulated = encapsulated in
  let ephemeral_dh =
    match dh recipient encapsulated with
    | Error (Error.Invalid_public_key reason) ->
        Error (Error.Invalid_encapsulation reason)
    | result -> result
  in
  let* ephemeral_dh = ephemeral_dh in
  (* A sender key that fails validation is not part of the encapsulation, so it
     stays an invalid public key. *)
  let* static_dh, sender_public =
    match sender with
    | None -> Ok ("", "")
    | Some sender ->
        let* static_dh = dh recipient sender in
        Ok (static_dh, Public_key.to_bytes sender)
  in
  let kem_context =
    encapsulated_key
    ^ Public_key.to_bytes (Private_key.public_key recipient)
    ^ sender_public
  in
  Ok (extract_and_expand kem ~dh:(ephemeral_dh ^ static_dh) ~kem_context)

let decap recipient ~sender ~encapsulated_key =
  match recipient.Private_key.secret with
  | P256_secret _ | P384_secret _ | P521_secret _ | X25519_secret _
  | X448_secret _ ->
      dh_decap recipient ~sender ~encapsulated_key
  | Mlkem512_secret secret ->
      let* () = mlkem_without_sender sender in
      Mlkem512_kem.decap secret encapsulated_key
  | Mlkem768_secret secret ->
      let* () = mlkem_without_sender sender in
      Mlkem768_kem.decap secret encapsulated_key
  | Mlkem1024_secret secret ->
      let* () = mlkem_without_sender sender in
      Mlkem1024_kem.decap secret encapsulated_key

module Rfc9180 = struct
  type encryption_state = {
    aead : Aead.id;
    key : Aead.key;
    base_nonce : string;
    exporter_secret : string;
    kdf : Kdf.id;
    suite_id : string;
    sequence : bytes;
    busy : bool Atomic.t;
  }

  type export_state = {
    exporter_secret : string;
    kdf : Kdf.id;
    suite_id : string;
  }

  type _ context =
    | Encryption_context : encryption_state -> Suite.encryption context
    | Export_context : export_state -> Suite.export_only context

  let exporter_data : type capability. capability context -> export_state =
    function
    | Encryption_context state ->
        {
          exporter_secret = state.exporter_secret;
          kdf = state.kdf;
          suite_id = state.suite_id;
        }
    | Export_context state -> state

  let export context ~context:exporter_context ~length =
    let state = exporter_data context in
    if length < 0 || length > 255 * Kdf.hash_size state.kdf then
      Error Error.Export_length_out_of_range
    else
      try
        Ok
          (Labeled_kdf.expand ~kdf:state.kdf ~suite_id:state.suite_id
             ~prk:state.exporter_secret ~label:"sec" ~info:exporter_context
             length)
      with Invalid_argument reason -> Error (Error.Internal_error reason)

  let sequence_exhausted sequence =
    let exhausted = ref true in
    for index = 0 to Bytes.length sequence - 1 do
      exhausted := !exhausted && Bytes.get_uint8 sequence index = 0xff
    done;
    !exhausted

  (* A signal handler may raise at any poll point, and a recursive function
     polls on every call. Storing the bytes from the last one, as a carry
     propagates, an exception could stop the increment after a byte had become
     zero and before the next one was incremented, leaving a number already
     used. The byte that takes the carry is therefore stored first and the 0xff
     bytes after it cleared last. However the increment is interrupted, the
     sequence then holds its old number, whose ciphertext is not returned, or
     one above the new number: numbers can be skipped but never reused. *)
  let increment_sequence sequence =
    let rec carry index =
      if index = 0 || Bytes.get_uint8 sequence index < 0xff then index
      else carry (index - 1)
    in
    let index = carry (Bytes.length sequence - 1) in
    Bytes.set_uint8 sequence index
      ((Bytes.get_uint8 sequence index + 1) land 0xff);
    Bytes.fill sequence (index + 1) (Bytes.length sequence - index - 1) '\000'

  let nonce state =
    String.init (String.length state.base_nonce) (fun index ->
        Char.chr
          (Char.code state.base_nonce.[index]
          lxor Bytes.get_uint8 state.sequence index))

  let with_busy state operation =
    if not (Atomic.compare_and_set state.busy false true) then
      Error Error.Concurrent_use
    else Fun.protect ~finally:(fun () -> Atomic.set state.busy false) operation

  let seal state ~aad ~plaintext =
    with_busy state (fun () ->
        if sequence_exhausted state.sequence then
          Error Error.Message_limit_reached
        else if not (Aead.plaintext_fits state.aead (String.length plaintext))
        then Error Error.Plaintext_too_long
        else
          let* ciphertext =
            Aead.encrypt state.key ~nonce:(nonce state) ~aad plaintext
          in
          increment_sequence state.sequence;
          Ok ciphertext)

  let open_ciphertext state ~aad ~ciphertext =
    with_busy state (fun () ->
        if sequence_exhausted state.sequence then
          Error Error.Message_limit_reached
        else if String.length ciphertext < Aead.tag_size state.aead then
          Error Error.Open_error
        else
          let plaintext_length =
            String.length ciphertext - Aead.tag_size state.aead
          in
          if not (Aead.plaintext_fits state.aead plaintext_length) then
            Error Error.Open_error
          else
            let* plaintext =
              Aead.decrypt state.key ~nonce:(nonce state) ~aad ciphertext
            in
            increment_sequence state.sequence;
            Ok plaintext)

  module Sender = struct
    type 'capability t = Sender of 'capability context

    let seal :
        Suite.encryption t ->
        aad:string ->
        plaintext:string ->
        (string, Error.t) result =
     fun (Sender context) ~aad ~plaintext ->
      match context with
      | Encryption_context state -> seal state ~aad ~plaintext
      | Export_context _ ->
          Error (Error.Internal_error "export-only context cannot seal")

    let export (Sender context) = export context
  end

  module Receiver = struct
    type 'capability t = Receiver of 'capability context

    let open_ :
        Suite.encryption t ->
        aad:string ->
        ciphertext:string ->
        (string, Error.t) result =
     fun (Receiver context) ~aad ~ciphertext ->
      match context with
      | Encryption_context state -> open_ciphertext state ~aad ~ciphertext
      | Export_context _ ->
          Error (Error.Internal_error "export-only context cannot open")

    let export (Receiver context) = export context
  end

  type 'capability sender_setup = {
    encapsulated_key : string;
    context : 'capability Sender.t;
  }

  type ciphertext = { encapsulated_key : string; ciphertext : string }

  (* ['key] is the half of the sender's static key that a role holds: private
     when sending and public when receiving. A mode that needs a PSK or a sender
     key carries it, so the inconsistent inputs that VerifyPSKInputs rejects
     (RFC 9180, Section 5.1) cannot be expressed. *)
  type 'key mode =
    | Base
    | Psk_mode of Psk.t
    | Auth of 'key
    | Auth_psk of 'key * Psk.t

  let sender_key = function
    | Base | Psk_mode _ -> None
    | Auth key | Auth_psk (key, _) -> Some key

  let key_schedule : type capability key.
      capability Suite.t ->
      key mode ->
      shared_secret:string ->
      info:string ->
      capability context =
   fun suite mode ~shared_secret ~info ->
    let kdf = Suite.kdf suite in
    let suite_id = Labeled_kdf.suite_id suite in
    let mode_byte, psk, psk_id =
      match mode with
      | Base -> (Util.byte 0, "", "")
      | Psk_mode psk -> (Util.byte 1, psk.Psk.secret, psk.Psk.id)
      | Auth _ -> (Util.byte 2, "", "")
      | Auth_psk (_, psk) -> (Util.byte 3, psk.Psk.secret, psk.Psk.id)
    in
    let psk_id_hash =
      Labeled_kdf.extract ~kdf ~suite_id ~salt:"" ~label:"psk_id_hash" psk_id
    in
    let info_hash =
      Labeled_kdf.extract ~kdf ~suite_id ~salt:"" ~label:"info_hash" info
    in
    let key_schedule_context = mode_byte ^ psk_id_hash ^ info_hash in
    let secret =
      Labeled_kdf.extract ~kdf ~suite_id ~salt:shared_secret ~label:"secret" psk
    in
    let exporter_secret =
      Labeled_kdf.expand ~kdf ~suite_id ~prk:secret ~label:"exp"
        ~info:key_schedule_context (Kdf.hash_size kdf)
    in
    match suite with
    | Suite.Export_only _ -> Export_context { exporter_secret; kdf; suite_id }
    | Suite.Encryption suite_details ->
        let key =
          Labeled_kdf.expand ~kdf ~suite_id ~prk:secret ~label:"key"
            ~info:key_schedule_context
            (Aead.key_size suite_details.aead)
        in
        (* Expanded here, once, and not on every seal or open. *)
        let key =
          {
            Aead.id = suite_details.aead;
            expanded = Aead.expand suite_details.aead key;
          }
        in
        let base_nonce =
          Labeled_kdf.expand ~kdf ~suite_id ~prk:secret ~label:"base_nonce"
            ~info:key_schedule_context
            (Aead.nonce_size suite_details.aead)
        in
        Encryption_context
          {
            aead = suite_details.aead;
            key;
            base_nonce;
            exporter_secret;
            kdf;
            suite_id;
            sequence = Bytes.make 12 '\000';
            busy = Atomic.make false;
          }

  let check_public_key suite key =
    if Suite.kem suite = Public_key.kem key then Ok ()
    else Error Error.Key_mismatch

  let check_private_key suite key =
    if Suite.kem suite = Private_key.kem key then Ok ()
    else Error Error.Key_mismatch

  let check_sender_key check suite mode =
    match sender_key mode with None -> Ok () | Some key -> check suite key

  (* Decided by the suite and the mode alone, so it is reported before any key
     is looked at. *)
  let check_mode suite mode =
    match sender_key mode with
    | Some _ when not (Kem.supports_auth (Suite.kem suite)) ->
        Error Error.Unsupported_mode
    | Some _ | None -> Ok ()

  let setup_sender_inner ~encap suite ~recipient ~mode ~info =
    let* () = check_mode suite mode in
    let* () = check_public_key suite recipient in
    let* () = check_sender_key check_private_key suite mode in
    let* shared_secret, encapsulated_key =
      encap ~sender:(sender_key mode) recipient
    in
    let context = key_schedule suite mode ~shared_secret ~info in
    Ok { encapsulated_key; context = Sender.Sender context }

  let setup_sender_encap ~encap suite ~recipient ~mode ~info =
    try setup_sender_inner ~encap suite ~recipient ~mode ~info
    with Invalid_argument reason -> Error (Error.Invalid_length reason)

  let setup_sender ~rng = setup_sender_encap ~encap:(encap ~rng)

  let setup_sender_with_ephemeral ~ephemeral =
    setup_sender_encap ~encap:(encap_with ~ephemeral)

  let setup_receiver_inner suite ~recipient ~encapsulated_key ~mode ~info =
    let* () = check_mode suite mode in
    let* () = check_private_key suite recipient in
    let* () = check_sender_key check_public_key suite mode in
    let* shared_secret =
      decap recipient ~sender:(sender_key mode) ~encapsulated_key
    in
    let context = key_schedule suite mode ~shared_secret ~info in
    Ok (Receiver.Receiver context)

  let setup_receiver suite ~recipient ~encapsulated_key ~mode ~info =
    try setup_receiver_inner suite ~recipient ~encapsulated_key ~mode ~info
    with Invalid_argument reason -> Error (Error.Invalid_length reason)

  let setup_base_sender ~rng suite ~recipient ~info =
    setup_sender ~rng suite ~recipient ~mode:Base ~info

  let setup_base_receiver suite ~recipient ~encapsulated_key ~info =
    setup_receiver suite ~recipient ~encapsulated_key ~mode:Base ~info

  let setup_psk_sender ~rng suite ~recipient ~psk ~info =
    setup_sender ~rng suite ~recipient ~mode:(Psk_mode psk) ~info

  let setup_psk_receiver suite ~recipient ~psk ~encapsulated_key ~info =
    setup_receiver suite ~recipient ~encapsulated_key ~mode:(Psk_mode psk) ~info

  let setup_auth_sender ~rng suite ~recipient ~sender ~info =
    setup_sender ~rng suite ~recipient ~mode:(Auth sender) ~info

  let setup_auth_receiver suite ~recipient ~sender ~encapsulated_key ~info =
    setup_receiver suite ~recipient ~encapsulated_key ~mode:(Auth sender) ~info

  let setup_auth_psk_sender ~rng suite ~recipient ~sender ~psk ~info =
    setup_sender ~rng suite ~recipient ~mode:(Auth_psk (sender, psk)) ~info

  let setup_auth_psk_receiver suite ~recipient ~sender ~psk ~encapsulated_key
      ~info =
    setup_receiver suite ~recipient ~encapsulated_key
      ~mode:(Auth_psk (sender, psk))
      ~info

  let seal_once setup ~aad ~plaintext =
    let* setup = setup in
    let* ciphertext = Sender.seal setup.context ~aad ~plaintext in
    Ok { encapsulated_key = setup.encapsulated_key; ciphertext }

  let seal_base ~rng suite ~recipient ~info ~aad ~plaintext =
    seal_once (setup_base_sender ~rng suite ~recipient ~info) ~aad ~plaintext

  (* A mismatched key and an unsupported mode are the caller's mistakes, and no
     peer can cause them, so they stay distinguishable. *)
  let normalized_open setup ~aad ~ciphertext =
    match setup with
    | Error ((Error.Key_mismatch | Error.Unsupported_mode) as error) ->
        Error error
    | Error _ -> Error Error.Open_error
    | Ok context -> (
        match Receiver.open_ context ~aad ~ciphertext with
        | Ok plaintext -> Ok plaintext
        | Error _ -> Error Error.Open_error)

  let open_base suite ~recipient ~info ~aad ~ciphertext =
    normalized_open
      (setup_base_receiver suite ~recipient
         ~encapsulated_key:ciphertext.encapsulated_key ~info)
      ~aad ~ciphertext:ciphertext.ciphertext

  let seal_psk ~rng suite ~recipient ~psk ~info ~aad ~plaintext =
    seal_once
      (setup_psk_sender ~rng suite ~recipient ~psk ~info)
      ~aad ~plaintext

  let open_psk suite ~recipient ~psk ~info ~aad ~ciphertext =
    normalized_open
      (setup_psk_receiver suite ~recipient ~psk
         ~encapsulated_key:ciphertext.encapsulated_key ~info)
      ~aad ~ciphertext:ciphertext.ciphertext

  let seal_auth ~rng suite ~recipient ~sender ~info ~aad ~plaintext =
    seal_once
      (setup_auth_sender ~rng suite ~recipient ~sender ~info)
      ~aad ~plaintext

  let open_auth suite ~recipient ~sender ~info ~aad ~ciphertext =
    normalized_open
      (setup_auth_receiver suite ~recipient ~sender
         ~encapsulated_key:ciphertext.encapsulated_key ~info)
      ~aad ~ciphertext:ciphertext.ciphertext

  let seal_auth_psk ~rng suite ~recipient ~sender ~psk ~info ~aad ~plaintext =
    seal_once
      (setup_auth_psk_sender ~rng suite ~recipient ~sender ~psk ~info)
      ~aad ~plaintext

  let open_auth_psk suite ~recipient ~sender ~psk ~info ~aad ~ciphertext =
    normalized_open
      (setup_auth_psk_receiver suite ~recipient ~sender ~psk
         ~encapsulated_key:ciphertext.encapsulated_key ~info)
      ~aad ~ciphertext:ciphertext.ciphertext
end

module Private = struct
  let setup_base_sender_with_ephemeral suite ~ephemeral ~recipient ~info =
    Rfc9180.setup_sender_with_ephemeral ~ephemeral suite ~recipient
      ~mode:Rfc9180.Base ~info

  let setup_psk_sender_with_ephemeral suite ~ephemeral ~recipient ~psk ~info =
    Rfc9180.setup_sender_with_ephemeral ~ephemeral suite ~recipient
      ~mode:(Rfc9180.Psk_mode psk) ~info

  let setup_auth_sender_with_ephemeral suite ~ephemeral ~recipient ~sender ~info
      =
    Rfc9180.setup_sender_with_ephemeral ~ephemeral suite ~recipient
      ~mode:(Rfc9180.Auth sender) ~info

  let setup_auth_psk_sender_with_ephemeral suite ~ephemeral ~recipient ~sender
      ~psk ~info =
    Rfc9180.setup_sender_with_ephemeral ~ephemeral suite ~recipient
      ~mode:(Rfc9180.Auth_psk (sender, psk))
      ~info
end
