open Hpke

let hex_value = function
  | '0' .. '9' as c -> Char.code c - Char.code '0'
  | 'a' .. 'f' as c -> Char.code c - Char.code 'a' + 10
  | 'A' .. 'F' as c -> Char.code c - Char.code 'A' + 10
  | _ -> invalid_arg "hex"

let hex value =
  let value = String.concat "" (String.split_on_char ' ' value) in
  String.init
    (String.length value / 2)
    (fun index ->
      Char.chr
        ((hex_value value.[index * 2] lsl 4)
        lor hex_value value.[(index * 2) + 1]))

let to_hex value =
  let alphabet = "0123456789abcdef" in
  String.init
    (String.length value * 2)
    (fun index ->
      let byte = Char.code value.[index / 2] in
      if index mod 2 = 0 then alphabet.[byte lsr 4]
      else alphabet.[byte land 0x0f])

let error_to_string error = Format.asprintf "%a" Error.pp error

let ok = function
  | Ok value -> value
  | Error error -> Alcotest.failf "unexpected error: %s" (error_to_string error)

let check_hex label expected actual =
  Alcotest.(check string) label expected (to_hex actual)

let rng () =
  Mirage_crypto_rng.create
    ~seed:(String.init 64 (fun index -> Char.chr (index + 1)))
    (module Mirage_crypto_rng.Fortuna)

let info = hex "4f6465206f6e2061204772656369616e2055726e"
let plaintext = hex "4265617574792069732074727574682c20747275746820626561757479"

let x25519_aes_suite =
  Suite.create ~kem:Kem.X25519 ~kdf:Kdf.Hkdf_sha256 ~aead:Aead.Aes_128_gcm

let rfc9180_base_vector () =
  (* RFC 9180, Appendix A.1.1. The provenance is pinned in
     test-vectors/PROVENANCE.md. *)
  let ikm_r =
    hex "6db9df30aa07dd42ee5e8181afdb977e538f5e1fec8a06223f33f7013e525037"
  in
  let expected_pk =
    "3948cfe0ad1ddb695d780e59077195da6c56506b027329794ab02bca80815c4d"
  in
  let recipient, derived_public = ok (derive_key_pair Kem.X25519 ~ikm:ikm_r) in
  check_hex "derived recipient public key" expected_pk
    (Public_key.to_bytes derived_public);
  let encapsulated_key =
    hex "37fda3567bdbd628e88668c3c8d7e97d1d1253b6d4ea6d44c150f741f1bf4431"
  in
  let context =
    ok
      (Rfc9180.setup_base_receiver x25519_aes_suite ~recipient ~encapsulated_key
         ~info)
  in
  let exported = ok (Rfc9180.Receiver.export context ~context:"" ~length:32) in
  check_hex "base export"
    "3853fe2b4035195a573ffc53856e77058e15d9ea064de3e59f4961d0095250ee" exported;
  let ciphertexts =
    [
      ( "436f756e742d30",
        "f938558b5d72f1a23810b4be2ab4f84331acc02fc97babc53a52ae8218a355a96d8770ac83d07bea87e13c512a"
      );
      ( "436f756e742d31",
        "af2d7e9ac9ae7e270f46ba1f975be53c09f8d875bdc8535458c2494e8a6eab251c03d0c22a56b8ca42c2063b84"
      );
      ( "436f756e742d32",
        "498dfcabd92e8acedc281e85af1cb4e3e31c7dc394a1ca20e173cb72516491588d96a19ad4a683518973dcc180"
      );
    ]
  in
  List.iteri
    (fun sequence (aad, ciphertext) ->
      let opened =
        ok
          (Rfc9180.Receiver.open_ context ~aad:(hex aad)
             ~ciphertext:(hex ciphertext))
      in
      Alcotest.(check string)
        (Format.sprintf "base plaintext %d" sequence)
        plaintext opened)
    ciphertexts;
  let exported_after =
    ok (Rfc9180.Receiver.export context ~context:"" ~length:32)
  in
  Alcotest.(check string) "export does not mutate" exported exported_after

let rfc9180_psk_vector () =
  (* RFC 9180, Appendix A.1.2. *)
  let recipient =
    ok
      (Private_key.of_bytes ~kem:Kem.X25519
         (hex "c5eb01eb457fe6c6f57577c5413b931550a162c71a03ac8d196babbd4e5ce0fd"))
  in
  let psk =
    ok
      (Psk.create
         ~secret:
           (hex
              "0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82")
         ~id:(hex "456e6e796e20447572696e206172616e204d6f726961"))
  in
  let context =
    ok
      (Rfc9180.setup_psk_receiver x25519_aes_suite ~recipient ~psk
         ~encapsulated_key:
           (hex
              "0ad0950d9fb9588e59690b74f1237ecdf1d775cd60be2eca57af5a4b0471c91b")
         ~info)
  in
  let exported = ok (Rfc9180.Receiver.export context ~context:"" ~length:32) in
  check_hex "psk export"
    "dff17af354c8b41673567db6259fd6029967b4e1aad13023c2ae5df8f4f43bf6" exported;
  let ciphertexts =
    [
      ( "436f756e742d30",
        "e52c6fed7f758d0cf7145689f21bc1be6ec9ea097fef4e959440012f4feb73fb611b946199e681f4cfc34db8ea"
      );
      ( "436f756e742d31",
        "49f3b19b28a9ea9f43e8c71204c00d4a490ee7f61387b6719db765e948123b45b61633ef059ba22cd62437c8ba"
      );
      ( "436f756e742d32",
        "257ca6a08473dc851fde45afd598cc83e326ddd0abe1ef23baa3baa4dd8cde99fce2c1e8ce687b0b47ead1adc9"
      );
    ]
  in
  List.iter
    (fun (aad, ciphertext) ->
      Alcotest.(check string)
        "psk plaintext" plaintext
        (ok
           (Rfc9180.Receiver.open_ context ~aad:(hex aad)
              ~ciphertext:(hex ciphertext))))
    ciphertexts

let rfc9180_chacha_vector () =
  (* RFC 9180, Appendix A.2.1. *)
  let suite =
    Suite.create ~kem:Kem.X25519 ~kdf:Kdf.Hkdf_sha256
      ~aead:Aead.Chacha20_poly1305
  in
  let recipient =
    ok
      (Private_key.of_bytes ~kem:Kem.X25519
         (hex "8057991eef8f1f1af18f4a9491d16a1ce333f695d4db8e38da75975c4478e0fb"))
  in
  let context =
    ok
      (Rfc9180.setup_base_receiver suite ~recipient
         ~encapsulated_key:
           (hex
              "1afa08d3dec047a643885163f1180476fa7ddb54c6a8029ea33f95796bf2ac4a")
         ~info)
  in
  Alcotest.(check string)
    "chacha plaintext" plaintext
    (ok
       (Rfc9180.Receiver.open_ context ~aad:(hex "436f756e742d30")
          ~ciphertext:
            (hex
               "1c5250d8034ec2b784ba2cfd69dbdb8af406cfe3ff938e131f0def8c8b60b4db21993c62ce81883d2dd1b51a28")))

let successor_rejection_sampling_vector () =
  (* draft-ietf-hpke-hpke-04, Appendix D.1. The counter=0 candidate is
     deliberately above the P-256 group order. *)
  let ikm =
    hex "68706b652d656467652d703235362d72656a656374696f6e00000001c6be4ce7"
  in
  let private_key, public_key = ok (derive_key_pair Kem.P256 ~ikm) in
  check_hex "P-256 rejection-sampled private key"
    "d9cbff7adaa1c604a2e4fcfb762c9e1c5ed7d2e33b15fcad4c6c3f23a9637325"
    (Private_key.to_bytes private_key);
  check_hex "P-256 rejection-sampled public key"
    "04d3bec6a691f47bbedd5caa1d51c7228f6afeeec5576495b855bbe6595e49643570be005fc177b3d80f6eeef280b1cf8a565d7ca28116dee2e875550ef3050ca8"
    (Public_key.to_bytes public_key)

let successor_edge_input_vectors () =
  (* draft-ietf-hpke-hpke-04, Appendix D.2. *)
  let recipient =
    ok
      (Private_key.of_bytes ~kem:Kem.X25519
         (hex "4612c550263fc8ad58375df3f557aac531d26850903e55a9f23f21d8534e8ac8"))
  in
  let encapsulated_key =
    hex "37fda3567bdbd628e88668c3c8d7e97d1d1253b6d4ea6d44c150f741f1bf4431"
  in
  let context =
    ok
      (Rfc9180.setup_base_receiver x25519_aes_suite ~recipient ~encapsulated_key
         ~info)
  in
  let cases =
    [
      ("436f756e742d30", "3f431133aa05608a56675bec51d03e0f", "");
      ( "",
        "af2d7e9ac9ae7e270f46ba1f975be53c09f8d875bdc8535458c2494e8aa7d2bb71109b5730bb714a8e64e5cc16",
        "4265617574792069732074727574682c20747275746820626561757479" );
      ( "436f756e742d30",
        "0be99ddcad54aabf548b3dbae884aff7aaeb0afc9ab60f",
        "00010002000300" );
      ( "00ff00ff00",
        "6b0f4cd351730cd25993d8ad0f11bff1ef2c3a957cb4d8694bb06c60a2f65e4f4cf8c1ae35431071bb18eff3e8",
        "4265617574792069732074727574682c20747275746820626561757479" );
    ]
  in
  List.iter
    (fun (aad, ciphertext, expected) ->
      Alcotest.(check string)
        "empty/zero-byte input" (hex expected)
        (ok
           (Rfc9180.Receiver.open_ context ~aad:(hex aad)
              ~ciphertext:(hex ciphertext))))
    cases;
  check_hex "embedded-zero exporter context"
    "73ac25f70dd55c215b4220e6978533ee2d3a559a48c507b11e200af81e64337a"
    (ok
       (Rfc9180.Receiver.export context ~context:(hex "0011002200") ~length:32))

let successor_info_vectors () =
  let recipient =
    ok
      (Private_key.of_bytes ~kem:Kem.X25519
         (hex "4612c550263fc8ad58375df3f557aac531d26850903e55a9f23f21d8534e8ac8"))
  in
  let encapsulated_key =
    hex "37fda3567bdbd628e88668c3c8d7e97d1d1253b6d4ea6d44c150f741f1bf4431"
  in
  let check_case label info ciphertext expected_export =
    let context =
      ok
        (Rfc9180.setup_base_receiver x25519_aes_suite ~recipient
           ~encapsulated_key ~info)
    in
    Alcotest.(check string)
      label plaintext
      (ok
         (Rfc9180.Receiver.open_ context ~aad:(hex "436f756e742d30")
            ~ciphertext:(hex ciphertext)));
    check_hex (label ^ " export") expected_export
      (ok
         (Rfc9180.Receiver.export context
            ~context:(hex "54657374436f6e74657874")
            ~length:32))
  in
  (* draft-ietf-hpke-hpke-04, Appendices D.3 and D.4. *)
  check_case "empty info" ""
    "2a19b5c53b9bc4d52723cfa64b0c0532b9fd5473e8c1105285be1a5fd763463c3d34236f5d26ebfe906277e094"
    "8a02de446479bb7d27490ed85a69c6bbaddd0969fbc84f7661ab038c9008f053";
  check_case "embedded-zero info" (hex "f0000f00ff")
    "dccc58fdd5dd0f80a162809a6bd47bf881ce2821b5ab718892dd568e2dcef6c98750fa1dc39a6182802ef3416c"
    "b16979c789e60ff4a21a3975b785ed3114d44525a3f660a4a848891dcf54446a"

let successor_psk_zero_bytes_vector () =
  (* draft-ietf-hpke-hpke-04, Appendix D.5. *)
  let recipient =
    ok
      (Private_key.of_bytes ~kem:Kem.X25519
         (hex "c5eb01eb457fe6c6f57577c5413b931550a162c71a03ac8d196babbd4e5ce0fd"))
  in
  let psk =
    ok
      (Psk.create
         ~secret:
           (hex
              "0000000000000000111111111111111100000000000000002222222222222222")
         ~id:(hex "0050534b00696400"))
  in
  let context =
    ok
      (Rfc9180.setup_psk_receiver x25519_aes_suite ~recipient ~psk
         ~encapsulated_key:
           (hex
              "0ad0950d9fb9588e59690b74f1237ecdf1d775cd60be2eca57af5a4b0471c91b")
         ~info)
  in
  Alcotest.(check string)
    "embedded-zero PSK plaintext" plaintext
    (ok
       (Rfc9180.Receiver.open_ context ~aad:(hex "436f756e742d30")
          ~ciphertext:
            (hex
               "cf34c6d0f86cd81c527cff7a2a20541cd017877d6e95f82f9dc13e6937bef65723bf43d4a2362690c20591ce67")));
  check_hex "embedded-zero PSK export"
    "000521bf952f7f7c56cf7dbf40ec1f6943a3233abe36a72d20aa4f87e0d90a95"
    (ok
       (Rfc9180.Receiver.export context
          ~context:(hex "54657374436f6e74657874")
          ~length:32))

let successor_export_only_vector () =
  (* draft-ietf-hpke-hpke-04, Appendix C.8.1. *)
  let suite = Suite.export_only ~kem:Kem.X25519 ~kdf:Kdf.Hkdf_sha256 in
  let recipient =
    ok
      (Private_key.of_bytes ~kem:Kem.X25519
         (hex "33d196c830a12f9ac65d6e565a590d80f04ee9b19c83c87f2c170d972a812848"))
  in
  let context =
    ok
      (Rfc9180.setup_base_receiver suite ~recipient
         ~encapsulated_key:
           (hex
              "e5e8f9bfff6c2f29791fc351d2c25ce1299aa5eaca78a757c0b4fb4bcd830918")
         ~info)
  in
  check_hex "successor export-only"
    "ffaabc85a776136ca0c378e5d084c9140ab552b78f039d2e8775f26efff4c70e"
    (ok
       (Rfc9180.Receiver.export context
          ~context:(hex "54657374436f6e74657874")
          ~length:32))

let go_p384_differential_fixture () =
  (* Generated by tools/differential/go/main.go with Go 1.26.5 crypto/hpke. *)
  let suite =
    Suite.create ~kem:Kem.P384 ~kdf:Kdf.Hkdf_sha384 ~aead:Aead.Aes_256_gcm
  in
  let expected_private =
    "826db63209d0586a4db99b8e8ba1094ee2baf43c47b4eb79a79f81f80dfcab5dd85d07feea65cb18fc07dee76cc765dc"
  in
  let recipient, derived_public =
    ok (derive_key_pair Kem.P384 ~ikm:(String.make 48 '\x42'))
  in
  check_hex "Go P-384 recipient private key" expected_private
    (Private_key.to_bytes recipient);
  check_hex "Go P-384 recipient public key"
    "046c4b4f33950fcf318da856fae44b1889ca66783421aa1a557051cfaa4eb33d114b4dced6cbbf4dd13a72bfd8c3e5afe5d3c1437453ed8b02affd37c74817e7bc045ad2d03080aadd116c7bc8a1c965175074f98c23a755ef91c4e9f4a3a80b7e"
    (Public_key.to_bytes derived_public);
  let context =
    ok
      (Rfc9180.setup_base_receiver suite ~recipient
         ~encapsulated_key:
           (hex
              "0445c64dc4a93b60dab7fd82fed66873adedf2ef6d2c348071fe3d8278133aaaee424915f3d506f47eda0b2f444e90f24e56e80458caa66d8619fed610518d7a168d41140815d2943a8adbe0bb0a953be770adfe0712b5e9d3edca3488c954dabe")
         ~info:"p384-differential")
  in
  Alcotest.(check string)
    "Go P-384 plaintext" "independent P-384 fixture"
    (ok
       (Rfc9180.Receiver.open_ context ~aad:(hex "00010002")
          ~ciphertext:
            (hex
               "fc853f05096d597ead87d63cbbf1cd5f3b794f1fa8c102291b2e3dbf1219043bd1972067a4769f2372")));
  check_hex "Go P-384 export"
    "47ea0642c86be35bd2fba04bae1679bd2f6da2622e8b7d464165341f10d0bf659ff69cad1d18a8e0765ee2063e829f6f"
    (ok (Rfc9180.Receiver.export context ~context:"export-context" ~length:48))

let all_kems = [ Kem.P256; Kem.P384; Kem.P521; Kem.X25519 ]
let all_kdfs = [ Kdf.Hkdf_sha256; Kdf.Hkdf_sha384; Kdf.Hkdf_sha512 ]
let all_aeads = [ Aead.Aes_128_gcm; Aead.Aes_256_gcm; Aead.Chacha20_poly1305 ]

let all_suite_round_trips () =
  let generator = rng () in
  List.iter
    (fun kem ->
      let recipient, public = ok (generate_key_pair ~rng:generator kem) in
      List.iter
        (fun kdf ->
          List.iter
            (fun aead ->
              let suite = Suite.create ~kem ~kdf ~aead in
              let message = "\000message\255" in
              let aad = "suite-aad" in
              let sealed =
                ok
                  (Rfc9180.seal_base ~rng:generator suite ~recipient:public
                     ~info:"suite-info" ~aad ~plaintext:message)
              in
              let opened =
                ok
                  (Rfc9180.open_base suite ~recipient ~info:"suite-info" ~aad
                     ~ciphertext:sealed)
              in
              Alcotest.(check string) "all-suite base round trip" message opened)
            all_aeads)
        all_kdfs)
    all_kems

let psk_round_trips () =
  let generator = rng () in
  let psk = ok (Psk.create ~secret:(String.make 32 '\x5a') ~id:"test-psk") in
  List.iter
    (fun kem ->
      let recipient, public = ok (generate_key_pair ~rng:generator kem) in
      let suite =
        Suite.create ~kem ~kdf:Kdf.Hkdf_sha512 ~aead:Aead.Chacha20_poly1305
      in
      let ciphertext =
        ok
          (Rfc9180.seal_psk ~rng:generator suite ~recipient:public ~psk ~info:""
             ~aad:"" ~plaintext:"")
      in
      Alcotest.(check string)
        "PSK empty-message round trip" ""
        (ok
           (Rfc9180.open_psk suite ~recipient ~psk ~info:"" ~aad:"" ~ciphertext)))
    all_kems

let failed_open_does_not_advance () =
  let recipient =
    ok
      (Private_key.of_bytes ~kem:Kem.X25519
         (hex "4612c550263fc8ad58375df3f557aac531d26850903e55a9f23f21d8534e8ac8"))
  in
  let encapsulated_key =
    hex "37fda3567bdbd628e88668c3c8d7e97d1d1253b6d4ea6d44c150f741f1bf4431"
  in
  let context =
    ok
      (Rfc9180.setup_base_receiver x25519_aes_suite ~recipient ~encapsulated_key
         ~info)
  in
  let ciphertext =
    hex
      "f938558b5d72f1a23810b4be2ab4f84331acc02fc97babc53a52ae8218a355a96d8770ac83d07bea87e13c512a"
  in
  let tampered = Bytes.of_string ciphertext in
  Bytes.set_uint8 tampered 0 (Bytes.get_uint8 tampered 0 lxor 1);
  (match
     Rfc9180.Receiver.open_ context ~aad:(hex "436f756e742d30")
       ~ciphertext:(Bytes.unsafe_to_string tampered)
   with
  | Error Error.Open_error -> ()
  | Error error -> Alcotest.failf "wrong error: %s" (error_to_string error)
  | Ok _ -> Alcotest.fail "tampered ciphertext opened");
  Alcotest.(check string)
    "state retained after failed open" plaintext
    (ok
       (Rfc9180.Receiver.open_ context ~aad:(hex "436f756e742d30") ~ciphertext))

let malformed_inputs () =
  let expect_error label = function
    | Error _ -> ()
    | Ok _ -> Alcotest.failf "%s unexpectedly succeeded" label
  in
  List.iter
    (fun (name, kem) ->
      let public_size = Kem.public_key_size kem in
      expect_error
        ("short " ^ name ^ " public key")
        (Public_key.of_bytes ~kem (String.make (public_size - 1) '\000'));
      expect_error
        ("invalid-prefix " ^ name ^ " point")
        (Public_key.of_bytes ~kem
           ("\002" ^ String.make (public_size - 1) '\000'));
      expect_error
        ("off-curve " ^ name ^ " point")
        (Public_key.of_bytes ~kem
           ("\004" ^ String.make (public_size - 1) '\000'));
      expect_error
        ("zero " ^ name ^ " scalar")
        (Private_key.of_bytes ~kem
           (String.make (Kem.private_key_size kem) '\000')))
    [ ("P-256", Kem.P256); ("P-384", Kem.P384); ("P-521", Kem.P521) ];
  expect_error "short X25519 public key"
    (Public_key.of_bytes ~kem:Kem.X25519 "x");
  expect_error "short X25519 private key"
    (Private_key.of_bytes ~kem:Kem.X25519 "x");
  expect_error "short PSK" (Psk.create ~secret:(String.make 31 'p') ~id:"id");
  expect_error "empty PSK id" (Psk.create ~secret:(String.make 32 'p') ~id:"");
  let generator = rng () in
  let recipient, _ = ok (generate_key_pair ~rng:generator Kem.X25519) in
  let low_order_encodings =
    [ String.make 32 '\000'; "\001" ^ String.make 31 '\000' ]
  in
  List.iteri
    (fun index encoding ->
      let public = ok (Public_key.of_bytes ~kem:Kem.X25519 encoding) in
      expect_error
        (Format.sprintf "low-order X25519 public key %d" index)
        (Rfc9180.setup_base_sender ~rng:generator x25519_aes_suite
           ~recipient:public ~info:"");
      expect_error
        (Format.sprintf "low-order X25519 encapsulation %d" index)
        (Rfc9180.setup_base_receiver x25519_aes_suite ~recipient
           ~encapsulated_key:encoding ~info:""))
    low_order_encodings;
  expect_error "short X25519 encapsulation"
    (Rfc9180.setup_base_receiver x25519_aes_suite ~recipient
       ~encapsulated_key:(String.make 31 '\000') ~info:"")

let normalized_single_shot_error () =
  let generator = rng () in
  let recipient, public = ok (generate_key_pair ~rng:generator Kem.X25519) in
  let sealed =
    ok
      (Rfc9180.seal_base ~rng:generator x25519_aes_suite ~recipient:public
         ~info:"right" ~aad:"aad" ~plaintext:"message")
  in
  match
    Rfc9180.open_base x25519_aes_suite ~recipient ~info:"wrong" ~aad:"aad"
      ~ciphertext:sealed
  with
  | Error Error.Open_error -> ()
  | Error error ->
      Alcotest.failf "error was not normalized: %s" (error_to_string error)
  | Ok _ -> Alcotest.fail "wrong info opened"

let adversarial_mismatches () =
  let generator = rng () in
  let expect_open_error label result =
    match result with
    | Error Error.Open_error -> ()
    | Error error ->
        Alcotest.failf "%s returned %s" label (error_to_string error)
    | Ok _ -> Alcotest.failf "%s unexpectedly opened" label
  in
  let cases =
    [
      ( "P-256/AES-128",
        Kem.P256,
        Kdf.Hkdf_sha256,
        Aead.Aes_128_gcm,
        Aead.Chacha20_poly1305 );
      ( "P-384/AES-256",
        Kem.P384,
        Kdf.Hkdf_sha384,
        Aead.Aes_256_gcm,
        Aead.Aes_128_gcm );
      ( "P-521/ChaCha",
        Kem.P521,
        Kdf.Hkdf_sha512,
        Aead.Chacha20_poly1305,
        Aead.Aes_256_gcm );
      ( "X25519/ChaCha",
        Kem.X25519,
        Kdf.Hkdf_sha256,
        Aead.Chacha20_poly1305,
        Aead.Aes_128_gcm );
    ]
  in
  List.iter
    (fun (name, kem, kdf, aead, other_aead) ->
      let suite = Suite.create ~kem ~kdf ~aead in
      let other_suite = Suite.create ~kem ~kdf ~aead:other_aead in
      let recipient, public = ok (generate_key_pair ~rng:generator kem) in
      let other_recipient, _ = ok (generate_key_pair ~rng:generator kem) in
      let sealed =
        ok
          (Rfc9180.seal_base ~rng:generator suite ~recipient:public
             ~info:"bound-info" ~aad:"bound-aad" ~plaintext:"bound-message")
      in
      expect_open_error
        (name ^ " wrong recipient")
        (Rfc9180.open_base suite ~recipient:other_recipient ~info:"bound-info"
           ~aad:"bound-aad" ~ciphertext:sealed);
      expect_open_error (name ^ " wrong info")
        (Rfc9180.open_base suite ~recipient ~info:"wrong-info" ~aad:"bound-aad"
           ~ciphertext:sealed);
      expect_open_error (name ^ " wrong AAD")
        (Rfc9180.open_base suite ~recipient ~info:"bound-info" ~aad:"wrong-aad"
           ~ciphertext:sealed);
      expect_open_error (name ^ " wrong suite")
        (Rfc9180.open_base other_suite ~recipient ~info:"bound-info"
           ~aad:"bound-aad" ~ciphertext:sealed);
      let tampered_bytes = Bytes.of_string sealed.ciphertext in
      let last = Bytes.length tampered_bytes - 1 in
      Bytes.set_uint8 tampered_bytes last
        (Bytes.get_uint8 tampered_bytes last lxor 1);
      let tampered =
        { sealed with ciphertext = Bytes.unsafe_to_string tampered_bytes }
      in
      expect_open_error
        (name ^ " tampered ciphertext")
        (Rfc9180.open_base suite ~recipient ~info:"bound-info" ~aad:"bound-aad"
           ~ciphertext:tampered);
      let truncated =
        {
          sealed with
          ciphertext =
            String.sub sealed.ciphertext 0 (String.length sealed.ciphertext - 1);
        }
      in
      expect_open_error
        (name ^ " truncated ciphertext")
        (Rfc9180.open_base suite ~recipient ~info:"bound-info" ~aad:"bound-aad"
           ~ciphertext:truncated);
      let psk = ok (Psk.create ~secret:(String.make 32 '\x11') ~id:"psk") in
      let wrong_psk =
        ok (Psk.create ~secret:(String.make 32 '\x12') ~id:"other-psk")
      in
      let sealed_psk =
        ok
          (Rfc9180.seal_psk ~rng:generator suite ~recipient:public ~psk
             ~info:"psk-info" ~aad:"psk-aad" ~plaintext:"psk-message")
      in
      expect_open_error (name ^ " wrong PSK")
        (Rfc9180.open_psk suite ~recipient ~psk:wrong_psk ~info:"psk-info"
           ~aad:"psk-aad" ~ciphertext:sealed_psk))
    cases;
  let recipient, _ = ok (generate_key_pair ~rng:generator Kem.X25519) in
  let p256_suite =
    Suite.create ~kem:Kem.P256 ~kdf:Kdf.Hkdf_sha256 ~aead:Aead.Aes_128_gcm
  in
  (match
     Rfc9180.setup_base_receiver p256_suite ~recipient
       ~encapsulated_key:(String.make 65 '\000') ~info:""
   with
  | Error Error.Key_mismatch -> ()
  | _ -> Alcotest.fail "suite/key mismatch was not reported");
  match
    Rfc9180.setup_base_receiver x25519_aes_suite ~recipient
      ~encapsulated_key:(String.make 31 '\000') ~info:""
  with
  | Error (Error.Invalid_encapsulation _) -> ()
  | _ -> Alcotest.fail "invalid encapsulation was not structured"

let export_only () =
  let generator = rng () in
  let recipient, public = ok (generate_key_pair ~rng:generator Kem.P384) in
  let suite = Suite.export_only ~kem:Kem.P384 ~kdf:Kdf.Hkdf_sha384 in
  let sender =
    ok
      (Rfc9180.setup_base_sender ~rng:generator suite ~recipient:public
         ~info:"export")
  in
  let receiver =
    ok
      (Rfc9180.setup_base_receiver suite ~recipient
         ~encapsulated_key:sender.encapsulated_key ~info:"export")
  in
  let sender_value =
    ok (Rfc9180.Sender.export sender.context ~context:"ctx" ~length:48)
  in
  let receiver_value =
    ok (Rfc9180.Receiver.export receiver ~context:"ctx" ~length:48)
  in
  Alcotest.(check string) "export-only agreement" sender_value receiver_value;
  (match Rfc9180.Sender.export sender.context ~context:"" ~length:(-1) with
  | Error Error.Export_length_out_of_range -> ()
  | _ -> Alcotest.fail "negative export length was not rejected");
  match
    Rfc9180.Sender.export sender.context ~context:"" ~length:((255 * 48) + 1)
  with
  | Error Error.Export_length_out_of_range -> ()
  | _ -> Alcotest.fail "oversized export was not rejected"

let all_kdfs = [ Kdf.Hkdf_sha256; Kdf.Hkdf_sha384; Kdf.Hkdf_sha512 ]
let all_aeads = [ Aead.Aes_128_gcm; Aead.Aes_256_gcm; Aead.Chacha20_poly1305 ]

let algorithm_sizes () =
  (* RFC 9180, Sections 7.1 to 7.3. *)
  List.iter
    (fun (kem, expected) ->
      Alcotest.(check int) "Nsecret" expected (Kem.secret_size kem))
    [ (Kem.P256, 32); (Kem.P384, 48); (Kem.P521, 64); (Kem.X25519, 32) ];
  List.iter
    (fun (kdf, expected) ->
      Alcotest.(check int) "Nh" expected (Kdf.hash_size kdf))
    [ (Kdf.Hkdf_sha256, 32); (Kdf.Hkdf_sha384, 48); (Kdf.Hkdf_sha512, 64) ];
  List.iter
    (fun (aead, expected) ->
      Alcotest.(check int) "Nk" expected (Aead.key_size aead);
      Alcotest.(check int) "Nn" 12 (Aead.nonce_size aead);
      Alcotest.(check int) "Nt" 16 (Aead.tag_size aead))
    [
      (Aead.Aes_128_gcm, 16);
      (Aead.Aes_256_gcm, 32);
      (Aead.Chacha20_poly1305, 32);
    ]

let expect_invalid_length label = function
  | Error (Error.Invalid_length _) -> ()
  | Ok _ -> Alcotest.failf "%s was accepted" label
  | Error error ->
      Alcotest.failf "%s: unexpected %s" label (error_to_string error)

let unlabeled_kdf_bounds () =
  List.iter
    (fun kdf ->
      let size = Kdf.hash_size kdf in
      let prk = Kdf.extract kdf ~salt:"salt" "input keying material" in
      Alcotest.(check int) "PRK length" size (String.length prk);
      Alcotest.(check int)
        "empty output" 0
        (String.length (ok (Kdf.expand kdf ~prk ~info:"" 0)));
      let longest = ok (Kdf.expand kdf ~prk ~info:"info" (255 * size)) in
      Alcotest.(check int) "longest output" (255 * size) (String.length longest);
      Alcotest.(check string)
        "outputs share a prefix"
        (String.sub longest 0 size)
        (ok (Kdf.expand kdf ~prk ~info:"info" size));
      expect_invalid_length "negative length"
        (Kdf.expand kdf ~prk ~info:"" (-1));
      expect_invalid_length "oversized length"
        (Kdf.expand kdf ~prk ~info:"" ((255 * size) + 1));
      expect_invalid_length "short PRK"
        (Kdf.expand kdf ~prk:(String.sub prk 0 (size - 1)) ~info:"" size))
    all_kdfs

let single_shot_aead () =
  List.iter
    (fun aead ->
      let key = String.make (Aead.key_size aead) '\x2a' in
      let nonce = String.make (Aead.nonce_size aead) '\x07' in
      List.iter
        (fun (aad, plaintext) ->
          let sealed = ok (Aead.seal aead ~key ~nonce ~aad ~plaintext) in
          Alcotest.(check int)
            "ciphertext length"
            (String.length plaintext + Aead.tag_size aead)
            (String.length sealed);
          Alcotest.(check string)
            "round trip" plaintext
            (ok (Aead.open_ aead ~key ~nonce ~aad ~ciphertext:sealed));
          let expect_open_error label ciphertext ~aad =
            match Aead.open_ aead ~key ~nonce ~aad ~ciphertext with
            | Error Error.Open_error -> ()
            | Ok _ -> Alcotest.failf "%s was accepted" label
            | Error error ->
                Alcotest.failf "%s: unexpected %s" label (error_to_string error)
          in
          let tampered = Bytes.of_string sealed in
          Bytes.set_uint8 tampered 0 (Bytes.get_uint8 tampered 0 lxor 1);
          expect_open_error "tampered ciphertext"
            (Bytes.unsafe_to_string tampered)
            ~aad;
          expect_open_error "wrong AAD" sealed ~aad:(aad ^ "x");
          expect_open_error "truncated ciphertext"
            (String.sub sealed 0 (String.length sealed - 1))
            ~aad;
          expect_open_error "shorter than a tag"
            (String.make (Aead.tag_size aead - 1) '\000')
            ~aad;
          expect_open_error "empty ciphertext" "" ~aad)
        [ ("", ""); ("aad", ""); ("", "message"); ("\000aad", "\000message") ];
      let short_key = String.sub key 0 (String.length key - 1) in
      let long_nonce = nonce ^ "\000" in
      expect_invalid_length "short key on seal"
        (Aead.seal aead ~key:short_key ~nonce ~aad:"" ~plaintext:"");
      expect_invalid_length "long nonce on seal"
        (Aead.seal aead ~key ~nonce:long_nonce ~aad:"" ~plaintext:"");
      expect_invalid_length "short key on open"
        (Aead.open_ aead ~key:short_key ~nonce ~aad:""
           ~ciphertext:(String.make 16 '\000'));
      expect_invalid_length "long nonce on open"
        (Aead.open_ aead ~key ~nonce:long_nonce ~aad:""
           ~ciphertext:(String.make 16 '\000')))
    all_aeads

let deterministic_sender () =
  let generator = rng () in
  let recipient, public = ok (generate_key_pair ~rng:generator Kem.X25519) in
  let ephemeral, ephemeral_public =
    ok (derive_key_pair Kem.X25519 ~ikm:(String.make 32 '\x45'))
  in
  let setup () =
    ok
      (Hpke_for_testing.setup_base_sender x25519_aes_suite ~ephemeral
         ~recipient:public ~info)
  in
  let first = setup () and second = setup () in
  Alcotest.(check string)
    "encapsulated key is the ephemeral public key"
    (Public_key.to_bytes ephemeral_public)
    first.encapsulated_key;
  let sealed = ok (Rfc9180.Sender.seal first.context ~aad:"aad" ~plaintext) in
  Alcotest.(check string)
    "same ephemeral key, same ciphertext" sealed
    (ok (Rfc9180.Sender.seal second.context ~aad:"aad" ~plaintext));
  let receiver =
    ok
      (Rfc9180.setup_base_receiver x25519_aes_suite ~recipient
         ~encapsulated_key:first.encapsulated_key ~info)
  in
  Alcotest.(check string)
    "an ordinary receiver opens it" plaintext
    (ok (Rfc9180.Receiver.open_ receiver ~aad:"aad" ~ciphertext:sealed));
  let p256_ephemeral, p256_public =
    ok (derive_key_pair Kem.P256 ~ikm:(String.make 32 '\x46'))
  in
  let expect_key_mismatch label = function
    | Error Error.Key_mismatch -> ()
    | _ -> Alcotest.failf "%s was not reported as a key mismatch" label
  in
  expect_key_mismatch "ephemeral key of another KEM"
    (Hpke_for_testing.setup_base_sender x25519_aes_suite
       ~ephemeral:p256_ephemeral ~recipient:public ~info);
  expect_key_mismatch "recipient key of another KEM"
    (Hpke_for_testing.setup_base_sender x25519_aes_suite ~ephemeral
       ~recipient:p256_public ~info);
  let psk = ok (Psk.create ~secret:(String.make 32 '\x11') ~id:"psk") in
  let psk_sender =
    ok
      (Hpke_for_testing.setup_psk_sender x25519_aes_suite ~ephemeral
         ~recipient:public ~psk ~info)
  in
  let psk_receiver =
    ok
      (Rfc9180.setup_psk_receiver x25519_aes_suite ~recipient ~psk
         ~encapsulated_key:psk_sender.encapsulated_key ~info)
  in
  let psk_sealed =
    ok (Rfc9180.Sender.seal psk_sender.context ~aad:"" ~plaintext)
  in
  Alcotest.(check bool)
    "PSK mode changes the key schedule" false
    (String.equal sealed psk_sealed);
  Alcotest.(check string)
    "PSK round trip" plaintext
    (ok (Rfc9180.Receiver.open_ psk_receiver ~aad:"" ~ciphertext:psk_sealed))

let qcheck_round_trip =
  let generator = QCheck2.Gen.string_size (QCheck2.Gen.int_bound 1024) in
  QCheck2.Test.make ~name:"arbitrary binary messages round trip" ~count:100
    generator (fun message ->
      let generator = rng () in
      let recipient, public =
        ok (generate_key_pair ~rng:generator Kem.X25519)
      in
      let sealed =
        ok
          (Rfc9180.seal_base ~rng:generator x25519_aes_suite ~recipient:public
             ~info:"property" ~aad:"\000aad" ~plaintext:message)
      in
      match
        Rfc9180.open_base x25519_aes_suite ~recipient ~info:"property"
          ~aad:"\000aad" ~ciphertext:sealed
      with
      | Ok opened -> String.equal message opened
      | Error _ -> false)

let qcheck_peer_input_total =
  let generator = QCheck2.Gen.string_size (QCheck2.Gen.int_bound 256) in
  QCheck2.Test.make ~name:"peer input never raises" ~count:500 generator
    (fun input ->
      let recipient, _ =
        ok (derive_key_pair Kem.X25519 ~ikm:(String.make 32 '\x42'))
      in
      ignore (Public_key.of_bytes ~kem:Kem.X25519 input);
      ignore
        (Rfc9180.setup_base_receiver x25519_aes_suite ~recipient
           ~encapsulated_key:input ~info:"fuzz");
      true)

let () =
  Alcotest.run "hpke"
    [
      ( "RFC 9180 vectors",
        [
          Alcotest.test_case "X25519 AES Base" `Quick rfc9180_base_vector;
          Alcotest.test_case "X25519 AES PSK" `Quick rfc9180_psk_vector;
          Alcotest.test_case "X25519 ChaCha Base" `Quick rfc9180_chacha_vector;
        ] );
      ( "successor draft vectors",
        [
          Alcotest.test_case "P-256 rejection sampling" `Quick
            successor_rejection_sampling_vector;
          Alcotest.test_case "empty and zero-byte AEAD inputs" `Quick
            successor_edge_input_vectors;
          Alcotest.test_case "empty and embedded-zero info" `Quick
            successor_info_vectors;
          Alcotest.test_case "embedded-zero PSK inputs" `Quick
            successor_psk_zero_bytes_vector;
          Alcotest.test_case "export-only" `Quick successor_export_only_vector;
        ] );
      ( "differential fixtures",
        [
          Alcotest.test_case "Go crypto/hpke P-384" `Quick
            go_p384_differential_fixture;
        ] );
      ( "suites",
        [
          Alcotest.test_case "all 36 Base combinations" `Quick
            all_suite_round_trips;
          Alcotest.test_case "PSK all KEMs" `Quick psk_round_trips;
          Alcotest.test_case "export-only" `Quick export_only;
        ] );
      ( "invariants",
        [
          Alcotest.test_case "failed open retains sequence" `Quick
            failed_open_does_not_advance;
          Alcotest.test_case "malformed inputs" `Quick malformed_inputs;
          Alcotest.test_case "single-shot error normalization" `Quick
            normalized_single_shot_error;
          Alcotest.test_case "adversarial mismatches" `Quick
            adversarial_mismatches;
        ] );
      ( "suite primitives",
        [
          Alcotest.test_case "algorithm sizes" `Quick algorithm_sizes;
          Alcotest.test_case "unlabeled KDF bounds" `Quick unlabeled_kdf_bounds;
          Alcotest.test_case "single-shot AEAD" `Quick single_shot_aead;
        ] );
      ( "for testing",
        [
          Alcotest.test_case "deterministic sender" `Quick deterministic_sender;
        ] );
      ( "properties",
        [
          QCheck_alcotest.to_alcotest ~speed_level:`Quick qcheck_round_trip;
          QCheck_alcotest.to_alcotest ~speed_level:`Quick
            qcheck_peer_input_total;
        ] );
    ]
