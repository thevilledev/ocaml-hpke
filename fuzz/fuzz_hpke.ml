open Hpke

let ok = function
  | Ok value -> value
  | Error error ->
      failwith (Format.asprintf "unexpected setup error: %a" Error.pp error)

let rng () =
  Mirage_crypto_rng.create ~seed:(String.make 64 '\x71')
    (module Mirage_crypto_rng.Fortuna)

let all_kems = [ Kem.P256; Kem.P384; Kem.P521; Kem.X25519; Kem.X448 ]
let all_aeads = [ Aead.Aes_128_gcm; Aead.Aes_256_gcm; Aead.Chacha20_poly1305 ]

let kdf_for_kem = function
  | Kem.P256 | Kem.X25519 -> Kdf.Hkdf_sha256
  | Kem.P384 -> Kdf.Hkdf_sha384
  | Kem.P521 | Kem.X448 -> Kdf.Hkdf_sha512

let kem_name = function
  | Kem.P256 -> "P-256"
  | Kem.P384 -> "P-384"
  | Kem.P521 -> "P-521"
  | Kem.X25519 -> "X25519"
  | Kem.X448 -> "X448"

let aead_name = function
  | Aead.Aes_128_gcm -> "AES-128-GCM"
  | Aead.Aes_256_gcm -> "AES-256-GCM"
  | Aead.Chacha20_poly1305 -> "ChaCha20-Poly1305"

type suite_case = {
  name : string;
  suite : Suite.encryption Suite.t;
  recipient : Private_key.t;
  sender : Public_key.t;
  encapsulated_key : string;
}

let suite_cases =
  let generator = rng () in
  List.concat
    (List.map
       (fun kem ->
         let recipient, public = ok (generate_key_pair ~rng:generator kem) in
         let _, sender = ok (generate_key_pair ~rng:generator kem) in
         List.map
           (fun aead ->
             let suite = Suite.create ~kem ~kdf:(kdf_for_kem kem) ~aead in
             let setup =
               ok
                 (Rfc9180.setup_base_sender ~rng:generator suite
                    ~recipient:public ~info:"encapsulation")
             in
             {
               name = kem_name kem ^ "/" ^ aead_name aead;
               suite;
               recipient;
               sender;
               encapsulated_key = setup.encapsulated_key;
             })
           all_aeads)
       all_kems)

type mode = Base | Psk | Auth | Auth_psk

let mode_cases =
  List.concat
    (List.map
       (fun suite_case ->
         [
           (suite_case, Base);
           (suite_case, Psk);
           (suite_case, Auth);
           (suite_case, Auth_psk);
         ])
       suite_cases)

let fuzz_psk secret id =
  ok (Psk.create ~secret:(String.make 32 '\000' ^ secret) ~id:("\000" ^ id))

let setup_receiver suite_case mode ~encapsulated_key ~info ~psk =
  let { suite; recipient; sender; _ } = suite_case in
  match mode with
  | Base -> Rfc9180.setup_base_receiver suite ~recipient ~encapsulated_key ~info
  | Psk ->
      Rfc9180.setup_psk_receiver suite ~recipient ~psk ~encapsulated_key ~info
  | Auth ->
      Rfc9180.setup_auth_receiver suite ~recipient ~sender ~encapsulated_key
        ~info
  | Auth_psk ->
      Rfc9180.setup_auth_psk_receiver suite ~recipient ~sender ~psk
        ~encapsulated_key ~info

(* Pads or truncates to [size], so that X25519 and X448 inputs reach the
   key-exchange validation instead of failing the length check. Padded NIST
   encodings rarely parse either way. *)
let fit size bytes =
  if String.length bytes >= size then String.sub bytes 0 size
  else bytes ^ String.make (size - String.length bytes) '\000'

let () =
  Crowbar.add_test ~name:"key encodings"
    [ Crowbar.range (List.length all_kems); Crowbar.bytes ]
    (fun selector bytes ->
      let kem = List.nth all_kems selector in
      ignore (Public_key.of_bytes ~kem bytes);
      ignore (Private_key.of_bytes ~kem bytes));
  Crowbar.add_test ~name:"derive_key_pair inputs"
    [ Crowbar.range (List.length all_kems); Crowbar.bytes ]
    (fun selector ikm ->
      ignore (derive_key_pair (List.nth all_kems selector) ~ikm));
  Crowbar.add_test ~name:"PSK inputs" [ Crowbar.bytes; Crowbar.bytes ]
    (fun secret id -> ignore (Psk.create ~secret ~id));
  Crowbar.add_test ~name:"receiver paths"
    [
      Crowbar.range (List.length mode_cases);
      Crowbar.bytes;
      Crowbar.bytes;
      Crowbar.bytes;
      Crowbar.bytes;
      Crowbar.bytes;
      Crowbar.int;
      Crowbar.bytes;
      Crowbar.bytes;
    ]
    (fun selector
         encapsulated_key
         ciphertext
         aad
         info
         exporter_context
         length
         psk_secret
         psk_id
       ->
      let suite_case, mode = List.nth mode_cases selector in
      let psk = fuzz_psk psk_secret psk_id in
      (* Every key but the encapsulation is valid, so that is all that can be
         reported. *)
      (match setup_receiver suite_case mode ~encapsulated_key ~info ~psk with
      | Ok _ | Error (Error.Invalid_encapsulation _) -> ()
      | Error error ->
          Crowbar.failf "%s receiver setup: %a" suite_case.name Error.pp error);
      match
        setup_receiver suite_case mode
          ~encapsulated_key:suite_case.encapsulated_key ~info ~psk
      with
      | Error _ ->
          Crowbar.failf "valid %s receiver setup failed" suite_case.name
      | Ok receiver ->
          ignore (Rfc9180.Receiver.open_ receiver ~aad ~ciphertext);
          ignore
            (Rfc9180.Receiver.export receiver ~context:exporter_context ~length));
  Crowbar.add_test ~name:"sender keys"
    [ Crowbar.range (List.length suite_cases); Crowbar.bytes; Crowbar.bytes ]
    (fun selector encoding ciphertext ->
      let suite_case = List.nth suite_cases selector in
      let { suite; recipient; encapsulated_key; _ } = suite_case in
      let kem = Suite.kem suite in
      match
        Public_key.of_bytes ~kem (fit (Kem.public_key_size kem) encoding)
      with
      | Error _ -> ()
      | Ok sender -> (
          ignore
            (Rfc9180.open_auth suite ~recipient ~sender ~info:"" ~aad:""
               ~ciphertext:{ Rfc9180.encapsulated_key; ciphertext });
          (* The encapsulation is valid, so a failure can only be the sender
             key's. *)
          match
            Rfc9180.setup_auth_receiver suite ~recipient ~sender
              ~encapsulated_key ~info:""
          with
          | Ok _ | Error (Error.Invalid_public_key _) -> ()
          | Error error ->
              Crowbar.failf "%s sender key: %a" suite_case.name Error.pp error))
