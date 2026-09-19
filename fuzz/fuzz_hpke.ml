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
  encapsulated_key : string;
}

let suite_cases =
  let generator = rng () in
  List.concat
    (List.map
       (fun kem ->
         let recipient, public = ok (generate_key_pair ~rng:generator kem) in
         List.map
           (fun aead ->
             let suite = Suite.create ~kem ~kdf:(kdf_for_kem kem) ~aead in
             let sender =
               ok
                 (Rfc9180.setup_base_sender ~rng:generator suite
                    ~recipient:public ~info:"encapsulation")
             in
             {
               name = kem_name kem ^ "/" ^ aead_name aead;
               suite;
               recipient;
               encapsulated_key = sender.encapsulated_key;
             })
           all_aeads)
       all_kems)

type mode = Base | Psk

let mode_cases =
  List.concat
    (List.map
       (fun suite_case -> [ (suite_case, Base); (suite_case, Psk) ])
       suite_cases)

let fuzz_psk secret id =
  ok (Psk.create ~secret:(String.make 32 '\000' ^ secret) ~id:("\000" ^ id))

let setup_receiver suite_case mode ~encapsulated_key ~info ~psk =
  match mode with
  | Base ->
      Rfc9180.setup_base_receiver suite_case.suite
        ~recipient:suite_case.recipient ~encapsulated_key ~info
  | Psk ->
      Rfc9180.setup_psk_receiver suite_case.suite
        ~recipient:suite_case.recipient ~psk ~encapsulated_key ~info

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
      ignore (setup_receiver suite_case mode ~encapsulated_key ~info ~psk);
      match
        setup_receiver suite_case mode
          ~encapsulated_key:suite_case.encapsulated_key ~info ~psk
      with
      | Error _ ->
          Crowbar.failf "valid %s receiver setup failed" suite_case.name
      | Ok receiver ->
          ignore (Rfc9180.Receiver.open_ receiver ~aad ~ciphertext);
          ignore
            (Rfc9180.Receiver.export receiver ~context:exporter_context ~length))
