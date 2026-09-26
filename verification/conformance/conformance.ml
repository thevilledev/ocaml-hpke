(* Checks lib/hpke.ml against the outputs of its Lean mirrors. Each line of the
   vector file names an internal function, its inputs, and the result the mirror
   computes. A mismatch means the mirror, and so every theorem about it, does
   not describe the code. *)

module H = Hpke_impl

let failures = ref 0
let checked = ref 0
let of_hex = function "-" -> "" | hex -> H.Util.of_hex_exn hex

let to_hex value =
  if value = "" then "-"
  else
    String.concat ""
      (List.init (String.length value) (fun i ->
           Printf.sprintf "%02x" (Char.code value.[i])))

let bool = function true -> "1" | false -> "0"

let kem_name = function
  | H.Kem.P256 -> "p256"
  | P384 -> "p384"
  | P521 -> "p521"
  | X25519 -> "x25519"
  | X448 -> "x448"
  | Mlkem512 -> "mlkem512"
  | Mlkem768 -> "mlkem768"
  | Mlkem1024 -> "mlkem1024"
  (* The Lean mirrors do not model the hybrid KEMs, so no vector names them. *)
  | Mlkem768_p256 -> "mlkem768p256"
  | Mlkem768_x25519 -> "mlkem768x25519"
  | Mlkem1024_p384 -> "mlkem1024p384"

let kdf_name = function
  | H.Kdf.Hkdf_sha256 -> "sha256"
  | Hkdf_sha384 -> "sha384"
  | Hkdf_sha512 -> "sha512"

let aead_name = function
  | H.Aead.Aes_128_gcm -> "aes128gcm"
  | Aes_256_gcm -> "aes256gcm"
  | Chacha20_poly1305 -> "chacha20poly1305"

let all_kems =
  H.Kem.[ P256; P384; P521; X25519; X448; Mlkem512; Mlkem768; Mlkem1024 ]

let all_kdfs = H.Kdf.[ Hkdf_sha256; Hkdf_sha384; Hkdf_sha512 ]
let all_aeads = H.Aead.[ Aes_128_gcm; Aes_256_gcm; Chacha20_poly1305 ]
let find name to_name all = List.find (fun x -> to_name x = name) all
let kem name = find name kem_name all_kems
let kdf name = find name kdf_name all_kdfs
let aead name = find name aead_name all_aeads

let error_name = function
  | H.Error.Unsupported_algorithm _ -> "unsupported_algorithm"
  | Invalid_public_key _ -> "invalid_public_key"
  | Invalid_private_key _ -> "invalid_private_key"
  | Invalid_encapsulation _ -> "invalid_encapsulation"
  | Key_mismatch -> "key_mismatch"
  | Unsupported_mode -> "unsupported_mode"
  | Derive_key_pair_failure -> "derive_key_pair_failure"
  | Invalid_psk _ -> "invalid_psk"
  | Invalid_length _ -> "invalid_length"
  | Message_limit_reached -> "message_limit_reached"
  | Plaintext_too_long -> "plaintext_too_long"
  | Export_length_out_of_range -> "export_length_out_of_range"
  | Concurrent_use -> "concurrent_use"
  | Open_error -> "open_error"
  | Internal_error _ -> "internal_error"

let result render = function
  | Ok value -> "ok " ^ render value
  | Error error -> "error " ^ error_name error

(* The hexadecimal result, or "raises" for [Invalid_argument]. *)
let raises f = try to_hex (f ()) with Invalid_argument _ -> "raises"

let expect line ~expected ~actual =
  incr checked;
  if not (String.equal expected actual) then begin
    incr failures;
    Printf.printf "MISMATCH %s\n  mirror: %s\n  ocaml:  %s\n" line expected
      actual
  end

(* A context whose only relevant fields are the nonce and the sequence. *)
let state ~base_nonce ~sequence =
  let key =
    match H.Aead.key H.Aead.Aes_128_gcm (String.make 16 '\000') with
    | Ok key -> key
    | Error _ -> assert false
  in
  {
    H.Rfc9180.aead = H.Aead.Aes_128_gcm;
    key;
    base_nonce;
    exporter_secret = "";
    kdf = H.Kdf.Hkdf_sha256;
    suite_id = "";
    sequence;
    busy = Atomic.make false;
  }

(* Real keys of every KEM, and an encapsulation to each recipient. *)
let rng =
  Mirage_crypto_rng.create ~seed:(String.make 64 '\x42')
    (module Mirage_crypto_rng.Fortuna)

let ok = function
  | Ok value -> value
  | Error error -> failwith ("conformance setup: " ^ error_name error)

let keys =
  List.map
    (fun k -> (k, ok (H.derive_key_pair k ~ikm:(String.make 64 '\x6b'))))
    all_kems

let private_key k = fst (List.assoc k keys)
let public_key k = snd (List.assoc k keys)
let psk = ok (H.Psk.create ~secret:(String.make 32 '\x70') ~id:"conformance")

let suite k =
  H.Suite.create ~kem:k ~kdf:H.Kdf.Hkdf_sha256 ~aead:H.Aead.Aes_128_gcm

let encapsulations =
  List.map
    (fun k ->
      let setup =
        ok
          (H.Rfc9180.setup_base_sender ~rng (suite k) ~recipient:(public_key k)
             ~info:"")
      in
      (k, setup.H.Rfc9180.encapsulated_key))
    all_kems

let class_of = function
  | Ok _ -> "Ok"
  | Error H.Error.Key_mismatch -> "Key_mismatch"
  | Error H.Error.Unsupported_mode -> "Unsupported_mode"
  | Error error -> error_name error

let setup_sender s r sender mode =
  let suite = suite s and recipient = public_key r and info = "" in
  let sender () = private_key (Option.get sender) in
  class_of
    (match mode with
    | 0 -> H.Rfc9180.setup_base_sender ~rng suite ~recipient ~info
    | 1 -> H.Rfc9180.setup_psk_sender ~rng suite ~recipient ~psk ~info
    | 2 ->
        H.Rfc9180.setup_auth_sender ~rng suite ~recipient ~sender:(sender ())
          ~info
    | _ ->
        H.Rfc9180.setup_auth_psk_sender ~rng suite ~recipient
          ~sender:(sender ()) ~psk ~info)

let setup_receiver s r sender mode =
  let suite = suite s and recipient = private_key r and info = "" in
  let encapsulated_key = List.assoc r encapsulations in
  let sender () = public_key (Option.get sender) in
  class_of
    (match mode with
    | 0 ->
        H.Rfc9180.setup_base_receiver suite ~recipient ~encapsulated_key ~info
    | 1 ->
        H.Rfc9180.setup_psk_receiver suite ~recipient ~psk ~encapsulated_key
          ~info
    | 2 ->
        H.Rfc9180.setup_auth_receiver suite ~recipient ~sender:(sender ())
          ~encapsulated_key ~info
    | _ ->
        H.Rfc9180.setup_auth_psk_receiver suite ~recipient ~sender:(sender ())
          ~psk ~encapsulated_key ~info)

let check line =
  match String.split_on_char ' ' line with
  | [ "kem_of_int"; n; "ok"; name ] | [ "kem_of_int"; n; "error"; name ] ->
      let expected =
        String.concat " " (List.tl (List.tl (String.split_on_char ' ' line)))
      in
      ignore name;
      expect line ~expected
        ~actual:(result kem_name (H.Kem.of_int (int_of_string n)))
  | [ "kdf_of_int"; n; _; _ ] ->
      let expected =
        String.concat " " (List.tl (List.tl (String.split_on_char ' ' line)))
      in
      expect line ~expected
        ~actual:(result kdf_name (H.Kdf.of_int (int_of_string n)))
  | [ "aead_of_int"; n; _; _ ] ->
      let expected =
        String.concat " " (List.tl (List.tl (String.split_on_char ' ' line)))
      in
      expect line ~expected
        ~actual:(result aead_name (H.Aead.of_int (int_of_string n)))
  | [ "kem_sizes"; name; id; npk; nsk; nenc; nsecret; auth ] ->
      let k = kem name in
      expect line
        ~expected:(String.concat " " [ id; npk; nsk; nenc; nsecret; auth ])
        ~actual:
          (Printf.sprintf "%d %d %d %d %d %s" (H.Kem.to_int k)
             (H.Kem.public_key_size k) (H.Kem.private_key_size k)
             (H.Kem.encapsulated_key_size k)
             (H.Kem.secret_size k)
             (bool (H.Kem.supports_auth k)))
  | [ "kdf_sizes"; name; id; nh ] ->
      let k = kdf name in
      expect line
        ~expected:(id ^ " " ^ nh)
        ~actual:(Printf.sprintf "%d %d" (H.Kdf.to_int k) (H.Kdf.hash_size k))
  | [ "aead_sizes"; name; id; nk; nn; nt ] ->
      let a = aead name in
      expect line
        ~expected:(String.concat " " [ id; nk; nn; nt ])
        ~actual:
          (Printf.sprintf "%d %d %d %d" (H.Aead.to_int a) (H.Aead.key_size a)
             (H.Aead.nonce_size a) (H.Aead.tag_size a))
  | [ "increment"; input; output ] ->
      let sequence = Bytes.of_string (of_hex input) in
      H.Rfc9180.increment_sequence sequence;
      expect line ~expected:output ~actual:(to_hex (Bytes.to_string sequence))
  | [ "exhausted"; input; output ] ->
      expect line ~expected:output
        ~actual:
          (bool (H.Rfc9180.sequence_exhausted (Bytes.of_string (of_hex input))))
  | [ "nonce"; base; sequence; output ] ->
      let state =
        state ~base_nonce:(of_hex base)
          ~sequence:(Bytes.of_string (of_hex sequence))
      in
      expect line ~expected:output ~actual:(to_hex (H.Rfc9180.nonce state))
  | [ "plaintext_fits"; name; length; output ] ->
      expect line ~expected:output
        ~actual:
          (bool (H.Aead.plaintext_fits (aead name) (int_of_string length)))
  | [ "i2osp2"; n; output ] ->
      expect line ~expected:output
        ~actual:(raises (fun () -> H.Util.i2osp2 (int_of_string n)))
  | [ "byte"; n; output ] ->
      expect line ~expected:output
        ~actual:(raises (fun () -> H.Util.byte (int_of_string n)))
  | [ "kem_suite_id"; name; output ] ->
      expect line ~expected:output
        ~actual:(to_hex (H.Labeled_kdf.kem_suite_id (kem name)))
  | [ "suite_id"; k; f; "export"; output ] ->
      expect line ~expected:output
        ~actual:
          (to_hex
             (H.Labeled_kdf.suite_id
                (H.Suite.export_only ~kem:(kem k) ~kdf:(kdf f))))
  | [ "suite_id"; k; f; a; output ] ->
      expect line ~expected:output
        ~actual:
          (to_hex
             (H.Labeled_kdf.suite_id
                (H.Suite.create ~kem:(kem k) ~kdf:(kdf f) ~aead:(aead a))))
  (* HKDF over the mirror's framing must equal the labeled function's output. *)
  | [ "labeled_extract"; f; suite_id; salt; label; ikm; labeled_ikm ] ->
      let kdf = kdf f and salt = of_hex salt in
      expect line
        ~expected:(to_hex (H.Kdf.extract kdf ~salt (of_hex labeled_ikm)))
        ~actual:
          (to_hex
             (H.Labeled_kdf.extract ~kdf ~suite_id:(of_hex suite_id) ~salt
                ~label:(of_hex label) (of_hex ikm)))
  | [ "labeled_expand"; f; suite_id; prk; label; info; length; labeled_info ] ->
      let kdf = kdf f and prk = of_hex prk and length = int_of_string length in
      let expected =
        match labeled_info with
        | "raises" -> "raises"
        | info ->
            to_hex (H.Kdf.expand_unchecked kdf ~prk ~info:(of_hex info) length)
      in
      expect line ~expected
        ~actual:
          (raises (fun () ->
               H.Labeled_kdf.expand ~kdf ~suite_id:(of_hex suite_id) ~prk
                 ~label:(of_hex label) ~info:(of_hex info) length))
  | [ "labeled_derive"; k; label; context; ikm; length; input ] ->
      let length = int_of_string length in
      let expected =
        match input with
        | "raises" -> "raises"
        | input ->
            to_hex (Mlkem.Fips202.shake256 ~output_length:length (of_hex input))
      in
      expect line ~expected
        ~actual:
          (raises (fun () ->
               H.Labeled_kdf.kem_derive_shake256 (kem k) ~label:(of_hex label)
                 ~context:(of_hex context) (of_hex ikm) length))
  | [ "curve_order"; k; output ] ->
      expect line ~expected:output
        ~actual:(raises (fun () -> H.curve_order (kem k)))
  | [ "valid_nist_scalar"; k; scalar; output ] ->
      expect line ~expected:output
        ~actual:
          (try bool (H.valid_nist_scalar (kem k) (of_hex scalar))
           with Invalid_argument _ -> "raises")
  | "private_key" :: k :: bytes :: expected ->
      expect line
        ~expected:(String.concat " " expected)
        ~actual:
          (result
             (fun key -> to_hex (H.Private_key.to_bytes key))
             (H.Private_key.of_bytes ~kem:(kem k) (of_hex bytes)))
  | [ "normalize_x25519"; bytes; output ] ->
      expect line ~expected:output
        ~actual:(raises (fun () -> H.Util.normalize_x25519 (of_hex bytes)))
  | [ "normalize_x448"; bytes; output ] ->
      expect line ~expected:output
        ~actual:(raises (fun () -> H.Util.normalize_x448 (of_hex bytes)))
  | [ "all_zero"; bytes; output ] ->
      expect line ~expected:output
        ~actual:(bool (H.Util.all_zero (of_hex bytes)))
  (* Both roles of every row of the setup table. *)
  | [ "setup"; s; r; sender; mode; output ] ->
      let sender = if sender = "-" then None else Some (kem sender) in
      let mode = int_of_string mode in
      expect (line ^ " (sender)") ~expected:output
        ~actual:(setup_sender (kem s) (kem r) sender mode);
      expect (line ^ " (receiver)") ~expected:output
        ~actual:(setup_receiver (kem s) (kem r) sender mode)
  | tag :: _ ->
      incr failures;
      Printf.printf "UNKNOWN TAG %s\n" tag
  | [] -> ()

let () =
  let path = Sys.argv.(1) in
  let channel = open_in path in
  (try
     while true do
       match input_line channel with "" -> () | line -> check line
     done
   with End_of_file -> ());
  close_in channel;
  Printf.printf "%d conformance vectors checked, %d mismatches\n" !checked
    !failures;
  if !failures > 0 || !checked = 0 then exit 1
