module Error = struct
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
  type id = P256 | P384 | P521 | X25519

  let to_int = function
    | P256 -> 0x0010
    | P384 -> 0x0011
    | P521 -> 0x0012
    | X25519 -> 0x0020

  let of_int = function
    | 0x0010 -> Ok P256
    | 0x0011 -> Ok P384
    | 0x0012 -> Ok P521
    | 0x0020 -> Ok X25519
    | id -> Error (Error.Unsupported_algorithm id)

  let pp ppf = function
    | P256 -> Format.pp_print_string ppf "DHKEM(P-256, HKDF-SHA256)"
    | P384 -> Format.pp_print_string ppf "DHKEM(P-384, HKDF-SHA384)"
    | P521 -> Format.pp_print_string ppf "DHKEM(P-521, HKDF-SHA512)"
    | X25519 -> Format.pp_print_string ppf "DHKEM(X25519, HKDF-SHA256)"

  let public_key_size = function
    | P256 -> 65
    | P384 -> 97
    | P521 -> 133
    | X25519 -> 32

  let private_key_size = function
    | P256 -> 32
    | P384 -> 48
    | P521 -> 66
    | X25519 -> 32

  let encapsulated_key_size = public_key_size

  let secret_size = function
    | P256 -> 32
    | P384 -> 48
    | P521 -> 64
    | X25519 -> 32
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

  let encrypt id ~key ~nonce ~aad plaintext =
    try
      match id with
      | Aes_128_gcm | Aes_256_gcm ->
          let key = Mirage_crypto.AES.GCM.of_secret key in
          Ok
            (Mirage_crypto.AES.GCM.authenticate_encrypt ~key ~nonce ~adata:aad
               plaintext)
      | Chacha20_poly1305 ->
          let key = Mirage_crypto.Chacha20.of_secret key in
          Ok
            (Mirage_crypto.Chacha20.authenticate_encrypt ~key ~nonce ~adata:aad
               plaintext)
    with Invalid_argument reason -> Error (Error.Internal_error reason)

  let decrypt id ~key ~nonce ~aad ciphertext =
    try
      let plaintext =
        match id with
        | Aes_128_gcm | Aes_256_gcm ->
            let key = Mirage_crypto.AES.GCM.of_secret key in
            Mirage_crypto.AES.GCM.authenticate_decrypt ~key ~nonce ~adata:aad
              ciphertext
        | Chacha20_poly1305 ->
            let key = Mirage_crypto.Chacha20.of_secret key in
            Mirage_crypto.Chacha20.authenticate_decrypt ~key ~nonce ~adata:aad
              ciphertext
      in
      match plaintext with
      | Some plaintext -> Ok plaintext
      | None -> Error Error.Open_error
    with Invalid_argument _ -> Error Error.Open_error

  let check_parameters id ~key ~nonce =
    if String.length key <> key_size id then
      Error (Error.Invalid_length "wrong AEAD key length")
    else if String.length nonce <> nonce_size id then
      Error (Error.Invalid_length "wrong AEAD nonce length")
    else Ok ()

  let seal id ~key ~nonce ~aad ~plaintext =
    match check_parameters id ~key ~nonce with
    | Error _ as error -> error
    | Ok () ->
        if not (plaintext_fits id (String.length plaintext)) then
          Error Error.Plaintext_too_long
        else encrypt id ~key ~nonce ~aad plaintext

  let open_ id ~key ~nonce ~aad ~ciphertext =
    match check_parameters id ~key ~nonce with
    | Error _ as error -> error
    | Ok () ->
        let length = String.length ciphertext in
        if
          length < tag_size id || not (plaintext_fits id (length - tag_size id))
        then Error Error.Open_error
        else decrypt id ~key ~nonce ~aad ciphertext
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

let valid_nist_scalar kem bytes =
  String.length bytes = Kem.private_key_size kem
  && (not (Util.all_zero bytes))
  && Eqaf.compare_be bytes (curve_order kem) < 0

let validate_public_bytes kem bytes =
  if String.length bytes <> Kem.public_key_size kem then
    Error (Error.Invalid_public_key "wrong encoded length")
  else
    match kem with
    | Kem.X25519 -> Ok ()
    | Kem.P256 ->
        if bytes.[0] <> '\004' then
          Error
            (Error.Invalid_public_key
               "only canonical uncompressed SEC1 encodings are accepted")
        else
          Result.map_error
            (fun error -> Error.Invalid_public_key (Util.ec_error error))
            (Result.map
               (fun _ -> ())
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
               (fun _ -> ())
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
               (fun _ -> ())
               (Mirage_crypto_ec.P521.Dsa.pub_of_octets bytes))

module Public_key = struct
  type t = { kem : Kem.id; bytes : string }

  let of_bytes ~kem bytes =
    let* () = validate_public_bytes kem bytes in
    Ok { kem; bytes }

  let to_bytes key = key.bytes
  let kem key = key.kem
end

let dh_secret_and_public kem bytes =
  let parsed =
    match kem with
    | Kem.P256 ->
        Result.map snd
          (Mirage_crypto_ec.P256.Dh.secret_of_octets ~compress:false bytes)
    | Kem.P384 ->
        Result.map snd
          (Mirage_crypto_ec.P384.Dh.secret_of_octets ~compress:false bytes)
    | Kem.P521 ->
        Result.map snd
          (Mirage_crypto_ec.P521.Dh.secret_of_octets ~compress:false bytes)
    | Kem.X25519 ->
        Result.map snd (Mirage_crypto_ec.X25519.secret_of_octets bytes)
  in
  Result.map_error
    (fun error -> Error.Invalid_private_key (Util.ec_error error))
    parsed

module Private_key = struct
  type t = { kem : Kem.id; bytes : string; public_key : Public_key.t }

  let of_bytes ~kem bytes =
    if String.length bytes <> Kem.private_key_size kem then
      Error (Error.Invalid_private_key "wrong encoded length")
    else
      let bytes =
        match kem with Kem.X25519 -> Util.normalize_x25519 bytes | _ -> bytes
      in
      if kem <> Kem.X25519 && not (valid_nist_scalar kem bytes) then
        Error (Error.Invalid_private_key "scalar is outside the valid range")
      else
        let* public_bytes = dh_secret_and_public kem bytes in
        let* public_key = Public_key.of_bytes ~kem public_bytes in
        Ok { kem; bytes; public_key }

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

  let kem_kdf = function
    | Kem.P256 | Kem.X25519 -> Kdf.Hkdf_sha256
    | Kem.P384 -> Kdf.Hkdf_sha384
    | Kem.P521 -> Kdf.Hkdf_sha512

  let kem_extract kem ~salt ~label ikm =
    extract ~kdf:(kem_kdf kem) ~suite_id:(kem_suite_id kem) ~salt ~label ikm

  let kem_expand kem ~prk ~label ~info length =
    expand ~kdf:(kem_kdf kem) ~suite_id:(kem_suite_id kem) ~prk ~label ~info
      length
end

let derive_key_pair_inner kem ~ikm =
  let dkp_prk = Labeled_kdf.kem_extract kem ~salt:"" ~label:"dkp_prk" ikm in
  let candidate counter =
    Labeled_kdf.kem_expand kem ~prk:dkp_prk ~label:"candidate"
      ~info:(Util.byte counter) (Kem.private_key_size kem)
  in
  let secret_result =
    match kem with
    | Kem.X25519 ->
        Ok
          (Util.normalize_x25519
             (Labeled_kdf.kem_expand kem ~prk:dkp_prk ~label:"sk" ~info:""
                (Kem.private_key_size kem)))
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
  generate 8

let dh private_key public_key =
  if Private_key.kem private_key <> Public_key.kem public_key then
    Error Error.Key_mismatch
  else
    let secret = Private_key.to_bytes private_key in
    let public = Public_key.to_bytes public_key in
    let result =
      match Private_key.kem private_key with
      | Kem.P256 ->
          let* secret, _ =
            Result.map_error
              (fun error -> Error.Internal_error (Util.ec_error error))
              (Mirage_crypto_ec.P256.Dh.secret_of_octets secret)
          in
          Result.map_error
            (fun error -> Error.Invalid_public_key (Util.ec_error error))
            (Mirage_crypto_ec.P256.Dh.key_exchange secret public)
      | Kem.P384 ->
          let* secret, _ =
            Result.map_error
              (fun error -> Error.Internal_error (Util.ec_error error))
              (Mirage_crypto_ec.P384.Dh.secret_of_octets secret)
          in
          Result.map_error
            (fun error -> Error.Invalid_public_key (Util.ec_error error))
            (Mirage_crypto_ec.P384.Dh.key_exchange secret public)
      | Kem.P521 ->
          let* secret, _ =
            Result.map_error
              (fun error -> Error.Internal_error (Util.ec_error error))
              (Mirage_crypto_ec.P521.Dh.secret_of_octets secret)
          in
          Result.map_error
            (fun error -> Error.Invalid_public_key (Util.ec_error error))
            (Mirage_crypto_ec.P521.Dh.key_exchange secret public)
      | Kem.X25519 ->
          let* secret, _ =
            Result.map_error
              (fun error -> Error.Internal_error (Util.ec_error error))
              (Mirage_crypto_ec.X25519.secret_of_octets secret)
          in
          Result.map_error
            (fun error -> Error.Invalid_public_key (Util.ec_error error))
            (Mirage_crypto_ec.X25519.key_exchange secret public)
    in
    result

let extract_and_expand kem ~dh ~kem_context =
  let eae_prk = Labeled_kdf.kem_extract kem ~salt:"" ~label:"eae_prk" dh in
  Labeled_kdf.kem_expand kem ~prk:eae_prk ~label:"shared_secret"
    ~info:kem_context (Kem.secret_size kem)

let encap_with ~ephemeral recipient =
  let kem = Public_key.kem recipient in
  let* dh_value = dh ephemeral recipient in
  let encapsulated_key =
    Public_key.to_bytes (Private_key.public_key ephemeral)
  in
  let kem_context = encapsulated_key ^ Public_key.to_bytes recipient in
  Ok (extract_and_expand kem ~dh:dh_value ~kem_context, encapsulated_key)

let encap ~rng recipient =
  let* ephemeral, _ = generate_key_pair ~rng (Public_key.kem recipient) in
  encap_with ~ephemeral recipient

let decap recipient ~encapsulated_key =
  let kem = Private_key.kem recipient in
  let encapsulated =
    match Public_key.of_bytes ~kem encapsulated_key with
    | Ok key -> Ok key
    | Error (Error.Invalid_public_key reason) ->
        Error (Error.Invalid_encapsulation reason)
    | Error error -> Error error
  in
  let* encapsulated = encapsulated in
  let dh_value =
    match dh recipient encapsulated with
    | Error (Error.Invalid_public_key reason) ->
        Error (Error.Invalid_encapsulation reason)
    | result -> result
  in
  let* dh_value = dh_value in
  let kem_context =
    encapsulated_key ^ Public_key.to_bytes (Private_key.public_key recipient)
  in
  Ok (extract_and_expand kem ~dh:dh_value ~kem_context)

module Rfc9180 = struct
  type encryption_state = {
    aead : Aead.id;
    key : string;
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

  let increment_sequence sequence =
    let rec increment index =
      let value = Bytes.get_uint8 sequence index in
      Bytes.set_uint8 sequence index ((value + 1) land 0xff);
      if value = 0xff && index > 0 then increment (index - 1)
    in
    increment (Bytes.length sequence - 1)

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
            Aead.encrypt state.aead ~key:state.key ~nonce:(nonce state) ~aad
              plaintext
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
              Aead.decrypt state.aead ~key:state.key ~nonce:(nonce state) ~aad
                ciphertext
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
  type mode = Base | Psk_mode of Psk.t

  let key_schedule : type capability.
      capability Suite.t ->
      mode ->
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

  let check_public_key suite recipient =
    if Suite.kem suite = Public_key.kem recipient then Ok ()
    else Error Error.Key_mismatch

  let check_private_key suite recipient =
    if Suite.kem suite = Private_key.kem recipient then Ok ()
    else Error Error.Key_mismatch

  let setup_sender_inner ~encap suite ~recipient ~mode ~info =
    let* () = check_public_key suite recipient in
    let* shared_secret, encapsulated_key = encap recipient in
    let context = key_schedule suite mode ~shared_secret ~info in
    Ok { encapsulated_key; context = Sender.Sender context }

  let setup_sender_encap ~encap suite ~recipient ~mode ~info =
    try setup_sender_inner ~encap suite ~recipient ~mode ~info
    with Invalid_argument reason -> Error (Error.Invalid_length reason)

  let setup_sender ~rng = setup_sender_encap ~encap:(encap ~rng)

  let setup_sender_with_ephemeral ~ephemeral =
    setup_sender_encap ~encap:(encap_with ~ephemeral)

  let setup_receiver_inner suite ~recipient ~encapsulated_key ~mode ~info =
    let* () = check_private_key suite recipient in
    let* shared_secret = decap recipient ~encapsulated_key in
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

  let seal_base ~rng suite ~recipient ~info ~aad ~plaintext =
    let* setup = setup_base_sender ~rng suite ~recipient ~info in
    let* ciphertext = Sender.seal setup.context ~aad ~plaintext in
    Ok { encapsulated_key = setup.encapsulated_key; ciphertext }

  let normalized_open setup ~aad ~ciphertext =
    match setup with
    | Error Error.Key_mismatch -> Error Error.Key_mismatch
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
    let* setup = setup_psk_sender ~rng suite ~recipient ~psk ~info in
    let* ciphertext = Sender.seal setup.context ~aad ~plaintext in
    Ok { encapsulated_key = setup.encapsulated_key; ciphertext }

  let open_psk suite ~recipient ~psk ~info ~aad ~ciphertext =
    normalized_open
      (setup_psk_receiver suite ~recipient ~psk
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
end
