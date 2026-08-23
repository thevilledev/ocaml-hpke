open Hpke

let suite =
  Suite.create ~kem:Kem.X25519 ~kdf:Kdf.Hkdf_sha256 ~aead:Aead.Aes_128_gcm

let recipient =
  match derive_key_pair Kem.X25519 ~ikm:(String.make 32 '\x42') with
  | Ok (private_key, _) -> private_key
  | Error error ->
      failwith
        (Format.asprintf "fixed key derivation failed: %a" Error.pp error)

let valid_encapsulation =
  (* RFC 9180 Appendix A.1.1. *)
  let hex =
    "37fda3567bdbd628e88668c3c8d7e97d1d1253b6d4ea6d44c150f741f1bf4431"
  in
  let digit = function
    | '0' .. '9' as c -> Char.code c - Char.code '0'
    | 'a' .. 'f' as c -> Char.code c - Char.code 'a' + 10
    | _ -> assert false
  in
  String.init 32 (fun i ->
      Char.chr ((digit hex.[i * 2] lsl 4) lor digit hex.[(i * 2) + 1]))

let () =
  Crowbar.add_test ~name:"key parsing"
    [ Crowbar.range 4; Crowbar.bytes ]
    (fun kem_selector bytes ->
      let kem =
        match kem_selector with
        | 0 -> Kem.P256
        | 1 -> Kem.P384
        | 2 -> Kem.P521
        | _ -> Kem.X25519
      in
      ignore (Public_key.of_bytes ~kem bytes);
      ignore (Private_key.of_bytes ~kem bytes));
  Crowbar.add_test ~name:"receiver setup" [ Crowbar.bytes ]
    (fun encapsulated_key ->
      ignore
        (Rfc9180.setup_base_receiver suite ~recipient ~encapsulated_key
           ~info:"fuzz"));
  Crowbar.add_test ~name:"ciphertext opening" [ Crowbar.bytes; Crowbar.bytes ]
    (fun aad ciphertext ->
      match
        Rfc9180.setup_base_receiver suite ~recipient
          ~encapsulated_key:valid_encapsulation ~info:"fuzz"
      with
      | Error _ -> ()
      | Ok context -> ignore (Rfc9180.Receiver.open_ context ~aad ~ciphertext))
