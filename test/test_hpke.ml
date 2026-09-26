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

(* Returns the bytes it was made with, in order, and raises once they run out.
   Whatever draws from it has then drawn exactly those bytes. *)
module Fixed_rng = struct
  type g = { data : string; mutable offset : int }

  let make data = { data; offset = 0 }
  let block = 1
  let create ?time:_ () = make ""

  let generate_into ~g buffer ~off length =
    if length > String.length g.data - g.offset then
      invalid_arg "fixed test RNG exhausted";
    Bytes.blit_string g.data g.offset buffer off length;
    g.offset <- g.offset + length

  let reseed ~g:_ _ = ()
  let accumulate ~g:_ _ = `Acc (fun _ -> ())
  let seeded ~g:_ = true
  let pools = 0
end

let fixed_rng data =
  Mirage_crypto_rng.create ~g:(Fixed_rng.make data) (module Fixed_rng)

let info = hex "4f6465206f6e2061204772656369616e2055726e"
let plaintext = hex "4265617574792069732074727574682c20747275746820626561757479"

let x25519_aes_suite =
  Suite.create ~kem:Kem.X25519 ~kdf:Kdf.Hkdf_sha256 ~aead:Aead.Aes_128_gcm

let x448_aes_suite =
  Suite.create ~kem:Kem.X448 ~kdf:Kdf.Hkdf_sha512 ~aead:Aead.Aes_256_gcm

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

let rfc9180_auth_vector () =
  (* RFC 9180, Appendix A.1.3. *)
  let recipient =
    ok
      (Private_key.of_bytes ~kem:Kem.X25519
         (hex "fdea67cf831f1ca98d8e27b1f6abeb5b7745e9d35348b80fa407ff6958f9137e"))
  in
  let sender =
    ok
      (Public_key.of_bytes ~kem:Kem.X25519
         (hex "8b0c70873dc5aecb7f9ee4e62406a397b350e57012be45cf53b7105ae731790b"))
  in
  let context =
    ok
      (Rfc9180.setup_auth_receiver x25519_aes_suite ~recipient ~sender
         ~encapsulated_key:
           (hex
              "23fb952571a14a25e3d678140cd0e5eb47a0961bb18afcf85896e5453c312e76")
         ~info)
  in
  check_hex "auth export"
    "28c70088017d70c896a8420f04702c5a321d9cbf0279fba899b59e51bac72c85"
    (ok (Rfc9180.Receiver.export context ~context:"" ~length:32));
  let ciphertexts =
    [
      ( "436f756e742d30",
        "5fd92cc9d46dbf8943e72a07e42f363ed5f721212cd90bcfd072bfd9f44e06b80fd17824947496e21b680c141b"
      );
      ( "436f756e742d31",
        "d3736bb256c19bfa93d79e8f80b7971262cb7c887e35c26370cfed62254369a1b52e3d505b79dd699f002bc8ed"
      );
      ( "436f756e742d32",
        "122175cfd5678e04894e4ff8789e85dd381df48dcaf970d52057df2c9acc3b121313a2bfeaa986050f82d93645"
      );
    ]
  in
  List.iter
    (fun (aad, ciphertext) ->
      Alcotest.(check string)
        "auth plaintext" plaintext
        (ok
           (Rfc9180.Receiver.open_ context ~aad:(hex aad)
              ~ciphertext:(hex ciphertext))))
    ciphertexts

let rfc9180_auth_psk_vector () =
  (* RFC 9180, Appendix A.1.4. The PSK is the one of Appendix A.1.2. *)
  let recipient =
    ok
      (Private_key.of_bytes ~kem:Kem.X25519
         (hex "cb29a95649dc5656c2d054c1aa0d3df0493155e9d5da6d7e344ed8b6a64a9423"))
  in
  let sender =
    ok
      (Public_key.of_bytes ~kem:Kem.X25519
         (hex "2bfb2eb18fcad1af0e4f99142a1c474ae74e21b9425fc5c589382c69b50cc57e"))
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
      (Rfc9180.setup_auth_psk_receiver x25519_aes_suite ~recipient ~sender ~psk
         ~encapsulated_key:
           (hex
              "820818d3c23993492cc5623ab437a48a0a7ca3e9639c140fe1e33811eb844b7c")
         ~info)
  in
  check_hex "auth-psk export"
    "08f7e20644bb9b8af54ad66d2067457c5f9fcb2a23d9f6cb4445c0797b330067"
    (ok (Rfc9180.Receiver.export context ~context:"" ~length:32));
  let ciphertexts =
    [
      ( "436f756e742d30",
        "a84c64df1e11d8fd11450039d4fe64ff0c8a99fca0bd72c2d4c3e0400bc14a40f27e45e141a24001697737533e"
      );
      ( "436f756e742d31",
        "4d19303b848f424fc3c3beca249b2c6de0a34083b8e909b6aa4c3688505c05ffe0c8f57a0a4c5ab9da127435d9"
      );
      ( "436f756e742d32",
        "0c085a365fbfa63409943b00a3127abce6e45991bc653f182a80120868fc507e9e4d5e37bcc384fc8f14153b24"
      );
    ]
  in
  List.iter
    (fun (aad, ciphertext) ->
      Alcotest.(check string)
        "auth-psk plaintext" plaintext
        (ok
           (Rfc9180.Receiver.open_ context ~aad:(hex aad)
              ~ciphertext:(hex ciphertext))))
    ciphertexts

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

let mlkem_kems = [ Kem.Mlkem512; Kem.Mlkem768; Kem.Mlkem1024 ]
let hybrid_kems = [ Kem.Mlkem768_p256; Kem.Mlkem768_x25519; Kem.Mlkem1024_p384 ]

let all_kems =
  [ Kem.P256; Kem.P384; Kem.P521; Kem.X25519; Kem.X448 ]
  @ mlkem_kems @ hybrid_kems

(* The KEMs with Auth and AuthPSK modes. [algorithm_sizes] checks the predicate
   itself against literals. *)
let auth_kems = List.filter Kem.supports_auth all_kems
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
      List.iter
        (fun kdf ->
          let suite = Suite.create ~kem ~kdf ~aead:Aead.Chacha20_poly1305 in
          let ciphertext =
            ok
              (Rfc9180.seal_psk ~rng:generator suite ~recipient:public ~psk
                 ~info:"" ~aad:"" ~plaintext:"")
          in
          Alcotest.(check string)
            "PSK empty-message round trip" ""
            (ok
               (Rfc9180.open_psk suite ~recipient ~psk ~info:"" ~aad:""
                  ~ciphertext)))
        all_kdfs)
    all_kems

let authenticated_round_trips () =
  let generator = rng () in
  let psk = ok (Psk.create ~secret:(String.make 32 '\x5a') ~id:"test-psk") in
  List.iter
    (fun kem ->
      let recipient, public = ok (generate_key_pair ~rng:generator kem) in
      let sender, sender_public = ok (generate_key_pair ~rng:generator kem) in
      List.iter
        (fun kdf ->
          let suite = Suite.create ~kem ~kdf ~aead:Aead.Aes_256_gcm in
          let sealed =
            ok
              (Rfc9180.seal_auth ~rng:generator suite ~recipient:public ~sender
                 ~info:"auth-info" ~aad:"auth-aad" ~plaintext:"auth-message")
          in
          Alcotest.(check string)
            "Auth round trip" "auth-message"
            (ok
               (Rfc9180.open_auth suite ~recipient ~sender:sender_public
                  ~info:"auth-info" ~aad:"auth-aad" ~ciphertext:sealed));
          let sealed =
            ok
              (Rfc9180.seal_auth_psk ~rng:generator suite ~recipient:public
                 ~sender ~psk ~info:"" ~aad:"" ~plaintext:"")
          in
          Alcotest.(check string)
            "AuthPSK empty-message round trip" ""
            (ok
               (Rfc9180.open_auth_psk suite ~recipient ~sender:sender_public
                  ~psk ~info:"" ~aad:"" ~ciphertext:sealed));
          let exporter = Suite.export_only ~kem ~kdf in
          let setup =
            ok
              (Rfc9180.setup_auth_sender ~rng:generator exporter
                 ~recipient:public ~sender ~info:"auth-export")
          in
          let receiver =
            ok
              (Rfc9180.setup_auth_receiver exporter ~recipient
                 ~sender:sender_public ~encapsulated_key:setup.encapsulated_key
                 ~info:"auth-export")
          in
          Alcotest.(check string)
            "Auth export-only agreement"
            (ok (Rfc9180.Sender.export setup.context ~context:"ctx" ~length:32))
            (ok (Rfc9180.Receiver.export receiver ~context:"ctx" ~length:32)))
        all_kdfs)
    auth_kems

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
  expect_error "short PSK" (Psk.create ~secret:(String.make 31 'p') ~id:"id");
  expect_error "empty PSK id" (Psk.create ~secret:(String.make 32 'p') ~id:"");
  let generator = rng () in
  List.iter
    (fun (name, kem, suite, low_order_encodings) ->
      let size = Kem.public_key_size kem in
      expect_error
        ("short " ^ name ^ " public key")
        (Public_key.of_bytes ~kem "x");
      expect_error
        ("long " ^ name ^ " public key")
        (Public_key.of_bytes ~kem (String.make (size + 1) '\000'));
      expect_error
        ("short " ^ name ^ " private key")
        (Private_key.of_bytes ~kem "x");
      expect_error
        ("long " ^ name ^ " private key")
        (Private_key.of_bytes ~kem
           (String.make (Kem.private_key_size kem + 1) '\001'));
      let recipient, recipient_public =
        ok (generate_key_pair ~rng:generator kem)
      in
      let sender, sender_public = ok (generate_key_pair ~rng:generator kem) in
      let psk = ok (Psk.create ~secret:(String.make 32 'p') ~id:"id") in
      let valid =
        ok
          (Rfc9180.setup_base_sender ~rng:generator suite
             ~recipient:recipient_public ~info:"")
      in
      (* Every encoding of the right length parses; a low-order value is only
         recognized by the all-zero Diffie-Hellman output it produces. *)
      List.iteri
        (fun index encoding ->
          let public = ok (Public_key.of_bytes ~kem encoding) in
          (match
             Rfc9180.setup_base_sender ~rng:generator suite ~recipient:public
               ~info:""
           with
          | Error (Error.Invalid_public_key _) -> ()
          | _ -> Alcotest.failf "low-order %s public key %d" name index);
          (match
             Rfc9180.setup_auth_sender ~rng:generator suite ~recipient:public
               ~sender ~info:""
           with
          | Error (Error.Invalid_public_key _) -> ()
          | _ -> Alcotest.failf "low-order %s Auth recipient %d" name index);
          (match
             Rfc9180.setup_base_receiver suite ~recipient
               ~encapsulated_key:encoding ~info:""
           with
          | Error (Error.Invalid_encapsulation _) -> ()
          | _ -> Alcotest.failf "low-order %s encapsulation %d" name index);
          (match
             Rfc9180.setup_auth_receiver suite ~recipient ~sender:sender_public
               ~encapsulated_key:encoding ~info:""
           with
          | Error (Error.Invalid_encapsulation _) -> ()
          | _ -> Alcotest.failf "low-order %s Auth encapsulation %d" name index);
          (match
             Rfc9180.setup_auth_psk_receiver suite ~recipient
               ~sender:sender_public ~psk ~encapsulated_key:encoding ~info:""
           with
          | Error (Error.Invalid_encapsulation _) -> ()
          | _ ->
              Alcotest.failf "low-order %s AuthPSK encapsulation %d" name index);
          (* A sender key is not part of the encapsulation, so it is reported as
             an invalid public key. *)
          (match
             Rfc9180.setup_auth_receiver suite ~recipient ~sender:public
               ~encapsulated_key:valid.encapsulated_key ~info:""
           with
          | Error (Error.Invalid_public_key _) -> ()
          | _ -> Alcotest.failf "low-order %s sender key %d" name index);
          match
            Rfc9180.open_auth suite ~recipient ~sender:public ~info:"" ~aad:""
              ~ciphertext:
                {
                  Rfc9180.encapsulated_key = valid.encapsulated_key;
                  ciphertext = "";
                }
          with
          | Error Error.Open_error -> ()
          | _ -> Alcotest.failf "low-order %s sender key %d at open" name index)
        low_order_encodings;
      expect_error
        ("short " ^ name ^ " encapsulation")
        (Rfc9180.setup_base_receiver suite ~recipient
           ~encapsulated_key:(String.make (size - 1) '\000')
           ~info:""))
    [
      ( "X25519",
        Kem.X25519,
        x25519_aes_suite,
        [ String.make 32 '\000'; "\001" ^ String.make 31 '\000' ] );
      (* 0, 1, p - 1, and the unreduced p and p + 1, for p = 2^448 - 2^224 - 1.
         RFC 7748 does not mask any bit of an X448 u-coordinate. *)
      ( "X448",
        Kem.X448,
        x448_aes_suite,
        [
          String.make 56 '\000';
          "\001" ^ String.make 55 '\000';
          "\254" ^ String.make 27 '\255' ^ "\254" ^ String.make 27 '\255';
          String.make 28 '\255' ^ "\254" ^ String.make 27 '\255';
          String.make 28 '\000' ^ String.make 28 '\255';
        ] );
    ]

let montgomery_private_key_clamping () =
  (* RFC 9180, Section 7.1.2, requires DeserializePrivateKey and
     SerializePrivateKey to clamp as RFC 7748, Section 5, does.
     decodeScalar25519 clears the three least significant bits of the first byte
     and the most significant bit of the last, and sets the second most
     significant bit of the last. decodeScalar448 clears the two least
     significant bits of the first byte and sets the most significant bit of the
     last. The expected bytes are literals: the vector corpus compares
     serializations that have both passed through the library's own clamp, and
     the primitives clamp again when they use a scalar, so neither would notice
     a wrong clamp here. *)
  List.iter
    (fun (name, kem, every_bit_set, no_bit_set) ->
      let size = Kem.private_key_size kem in
      let parse bytes = ok (Private_key.of_bytes ~kem bytes) in
      let all_set = parse (String.make size '\xff') in
      check_hex (name ^ " every bit set") every_bit_set
        (Private_key.to_bytes all_set);
      check_hex (name ^ " no bit set") no_bit_set
        (Private_key.to_bytes (parse (String.make size '\x00')));
      let reparsed = parse (Private_key.to_bytes all_set) in
      Alcotest.(check string)
        (name ^ " clamping is idempotent")
        (Private_key.to_bytes all_set)
        (Private_key.to_bytes reparsed);
      Alcotest.(check string)
        (name ^ " both encodings name one key")
        (Public_key.to_bytes (Private_key.public_key all_set))
        (Public_key.to_bytes (Private_key.public_key reparsed)))
    [
      ( "X25519",
        Kem.X25519,
        "f8" ^ String.make 60 'f' ^ "7f",
        String.make 62 '0' ^ "40" );
      ("X448", Kem.X448, "fc" ^ String.make 110 'f', String.make 110 '0' ^ "80");
    ]

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

let expect_open_error label result =
  match result with
  | Error Error.Open_error -> ()
  | Error error -> Alcotest.failf "%s returned %s" label (error_to_string error)
  | Ok _ -> Alcotest.failf "%s unexpectedly opened" label

let expect_key_mismatch label = function
  | Error Error.Key_mismatch -> ()
  | _ -> Alcotest.failf "%s was not reported as a key mismatch" label

let adversarial_mismatches () =
  let generator = rng () in
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
      ( "X448/AES-256",
        Kem.X448,
        Kdf.Hkdf_sha512,
        Aead.Aes_256_gcm,
        Aead.Chacha20_poly1305 );
      (* For ML-KEM a wrong recipient decapsulates without an error, to a secret
         of its own (implicit rejection), and fails to open like the rest. *)
      ( "ML-KEM-512/AES-128",
        Kem.Mlkem512,
        Kdf.Hkdf_sha256,
        Aead.Aes_128_gcm,
        Aead.Chacha20_poly1305 );
      ( "ML-KEM-768/ChaCha",
        Kem.Mlkem768,
        Kdf.Hkdf_sha384,
        Aead.Chacha20_poly1305,
        Aead.Aes_256_gcm );
      ( "ML-KEM-1024/AES-256",
        Kem.Mlkem1024,
        Kdf.Hkdf_sha512,
        Aead.Aes_256_gcm,
        Aead.Aes_128_gcm );
      (* So does a hybrid's ML-KEM half, and its group half then yields another
         secret as well. *)
      ( "MLKEM768-P256/AES-128",
        Kem.Mlkem768_p256,
        Kdf.Hkdf_sha256,
        Aead.Aes_128_gcm,
        Aead.Aes_256_gcm );
      ( "MLKEM768-X25519/ChaCha",
        Kem.Mlkem768_x25519,
        Kdf.Hkdf_sha256,
        Aead.Chacha20_poly1305,
        Aead.Aes_128_gcm );
      ( "MLKEM1024-P384/AES-256",
        Kem.Mlkem1024_p384,
        Kdf.Hkdf_sha384,
        Aead.Aes_256_gcm,
        Aead.Chacha20_poly1305 );
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

(* A message opens only in the mode it was sealed in, and in an authenticated
   mode only as coming from its sender. *)
let authenticated_mismatches () =
  let generator = rng () in
  let psk = ok (Psk.create ~secret:(String.make 32 '\x11') ~id:"psk") in
  let other_psk =
    ok (Psk.create ~secret:(String.make 32 '\x12') ~id:"other-psk")
  in
  let info = "auth-info" and aad = "auth-aad" in
  List.iter
    (fun kem ->
      let name = Format.asprintf "%a" Kem.pp kem in
      let suite =
        Suite.create ~kem ~kdf:Kdf.Hkdf_sha256 ~aead:Aead.Chacha20_poly1305
      in
      let recipient, public = ok (generate_key_pair ~rng:generator kem) in
      let sender, sender_public = ok (generate_key_pair ~rng:generator kem) in
      let _, other_sender = ok (generate_key_pair ~rng:generator kem) in
      let expect label = expect_open_error (name ^ " " ^ label) in
      let sealed =
        ok
          (Rfc9180.seal_auth ~rng:generator suite ~recipient:public ~sender
             ~info ~aad ~plaintext:"auth-message")
      in
      expect "Auth from another sender"
        (Rfc9180.open_auth suite ~recipient ~sender:other_sender ~info ~aad
           ~ciphertext:sealed);
      expect "Auth opened as Base"
        (Rfc9180.open_base suite ~recipient ~info ~aad ~ciphertext:sealed);
      expect "Auth opened as AuthPSK"
        (Rfc9180.open_auth_psk suite ~recipient ~sender:sender_public ~psk ~info
           ~aad ~ciphertext:sealed);
      let sealed =
        ok
          (Rfc9180.seal_auth_psk ~rng:generator suite ~recipient:public ~sender
             ~psk ~info ~aad ~plaintext:"auth-psk-message")
      in
      expect "AuthPSK from another sender"
        (Rfc9180.open_auth_psk suite ~recipient ~sender:other_sender ~psk ~info
           ~aad ~ciphertext:sealed);
      expect "AuthPSK with another PSK"
        (Rfc9180.open_auth_psk suite ~recipient ~sender:sender_public
           ~psk:other_psk ~info ~aad ~ciphertext:sealed);
      expect "AuthPSK opened as PSK"
        (Rfc9180.open_psk suite ~recipient ~psk ~info ~aad ~ciphertext:sealed);
      expect "AuthPSK opened as Auth"
        (Rfc9180.open_auth suite ~recipient ~sender:sender_public ~info ~aad
           ~ciphertext:sealed);
      let sealed =
        ok
          (Rfc9180.seal_base ~rng:generator suite ~recipient:public ~info ~aad
             ~plaintext:"base-message")
      in
      expect "Base opened as Auth"
        (Rfc9180.open_auth suite ~recipient ~sender:sender_public ~info ~aad
           ~ciphertext:sealed);
      let sealed =
        ok
          (Rfc9180.seal_psk ~rng:generator suite ~recipient:public ~psk ~info
             ~aad ~plaintext:"psk-message")
      in
      expect "PSK opened as AuthPSK"
        (Rfc9180.open_auth_psk suite ~recipient ~sender:sender_public ~psk ~info
           ~aad ~ciphertext:sealed))
    auth_kems;
  (* A sender key of another KEM is the caller's mistake, so it stays
     distinguishable, single-shot opens included. Each one is paired with an
     input that would fail on its own, a low-order recipient key or an empty
     encapsulation, to show that the check comes before any cryptography. *)
  let recipient, _ = ok (generate_key_pair ~rng:generator Kem.X25519) in
  let low_order =
    ok (Public_key.of_bytes ~kem:Kem.X25519 (String.make 32 '\000'))
  in
  let p256_sender, p256_sender_public =
    ok (generate_key_pair ~rng:generator Kem.P256)
  in
  let ciphertext = { Rfc9180.encapsulated_key = ""; ciphertext = "" } in
  expect_key_mismatch "Auth sender private key"
    (Rfc9180.setup_auth_sender ~rng:generator x25519_aes_suite
       ~recipient:low_order ~sender:p256_sender ~info);
  expect_key_mismatch "AuthPSK sender private key"
    (Rfc9180.setup_auth_psk_sender ~rng:generator x25519_aes_suite
       ~recipient:low_order ~sender:p256_sender ~psk ~info);
  expect_key_mismatch "single-shot Auth sender private key"
    (Rfc9180.seal_auth ~rng:generator x25519_aes_suite ~recipient:low_order
       ~sender:p256_sender ~info ~aad ~plaintext);
  expect_key_mismatch "Auth sender public key"
    (Rfc9180.setup_auth_receiver x25519_aes_suite ~recipient
       ~sender:p256_sender_public ~encapsulated_key:"" ~info);
  expect_key_mismatch "AuthPSK sender public key"
    (Rfc9180.setup_auth_psk_receiver x25519_aes_suite ~recipient
       ~sender:p256_sender_public ~psk ~encapsulated_key:"" ~info);
  expect_key_mismatch "single-shot Auth sender public key"
    (Rfc9180.open_auth x25519_aes_suite ~recipient ~sender:p256_sender_public
       ~info ~aad ~ciphertext);
  expect_key_mismatch "single-shot AuthPSK sender public key"
    (Rfc9180.open_auth_psk x25519_aes_suite ~recipient
       ~sender:p256_sender_public ~psk ~info ~aad ~ciphertext)

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
  (* RFC 9180, Sections 7.1 to 7.3, and for ML-KEM and the hybrids
     draft-ietf-hpke-pq-05, Sections 8.1 and 8.2. *)
  let sizes =
    [
      (Kem.P256, 0x0010, 32, 65, 65, 32, true);
      (Kem.P384, 0x0011, 48, 97, 97, 48, true);
      (Kem.P521, 0x0012, 64, 133, 133, 66, true);
      (Kem.X25519, 0x0020, 32, 32, 32, 32, true);
      (Kem.X448, 0x0021, 64, 56, 56, 56, true);
      (Kem.Mlkem512, 0x0040, 32, 768, 800, 64, false);
      (Kem.Mlkem768, 0x0041, 32, 1088, 1184, 64, false);
      (Kem.Mlkem1024, 0x0042, 32, 1568, 1568, 64, false);
      (Kem.Mlkem768_p256, 0x0050, 32, 1153, 1249, 32, false);
      (Kem.Mlkem1024_p384, 0x0051, 32, 1665, 1665, 32, false);
      (Kem.Mlkem768_x25519, 0x647a, 32, 1120, 1216, 32, false);
    ]
  in
  Alcotest.(check int)
    "every KEM is listed" (List.length all_kems) (List.length sizes);
  List.iter
    (fun (kem, identifier, secret, encapsulated, public, private_, auth) ->
      Alcotest.(check int) "KEM identifier" identifier (Kem.to_int kem);
      Alcotest.(check bool)
        "KEM identifier round trip" true
        (Kem.of_int identifier = Ok kem);
      Alcotest.(check int) "Nsecret" secret (Kem.secret_size kem);
      Alcotest.(check int) "Nenc" encapsulated (Kem.encapsulated_key_size kem);
      Alcotest.(check int) "Npk" public (Kem.public_key_size kem);
      Alcotest.(check int) "Nsk" private_ (Kem.private_key_size kem);
      Alcotest.(check bool) "Auth" auth (Kem.supports_auth kem))
    sizes;
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
      let secret = String.make (Aead.key_size aead) '\x2a' in
      let key = ok (Aead.key aead secret) in
      let nonce = String.make (Aead.nonce_size aead) '\x07' in
      List.iter
        (fun (aad, plaintext) ->
          let sealed = ok (Aead.seal key ~nonce ~aad ~plaintext) in
          Alcotest.(check int)
            "ciphertext length"
            (String.length plaintext + Aead.tag_size aead)
            (String.length sealed);
          Alcotest.(check string)
            "round trip" plaintext
            (ok (Aead.open_ key ~nonce ~aad ~ciphertext:sealed));
          Alcotest.(check string)
            "a key prepared again seals the same" sealed
            (ok (Aead.seal (ok (Aead.key aead secret)) ~nonce ~aad ~plaintext));
          let expect_open_error label ciphertext ~aad =
            match Aead.open_ key ~nonce ~aad ~ciphertext with
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
      let expect_invalid_key label secret =
        match Aead.key aead secret with
        | Error (Error.Invalid_length _) -> ()
        | Ok _ -> Alcotest.failf "%s was accepted" label
        | Error error ->
            Alcotest.failf "%s: unexpected %s" label (error_to_string error)
      in
      expect_invalid_key "short key"
        (String.sub secret 0 (String.length secret - 1));
      expect_invalid_key "long key" (secret ^ "\000");
      expect_invalid_key "empty key" "";
      (* A 16-byte key is a valid AES key, but not for an AEAD that takes 32. *)
      if Aead.key_size aead <> 16 then
        expect_invalid_key "key of another AEAD" (String.make 16 '\x2a');
      let long_nonce = nonce ^ "\000" in
      expect_invalid_length "long nonce on seal"
        (Aead.seal key ~nonce:long_nonce ~aad:"" ~plaintext:"");
      expect_invalid_length "short nonce on seal"
        (Aead.seal key ~nonce:"" ~aad:"" ~plaintext:"");
      expect_invalid_length "long nonce on open"
        (Aead.open_ key ~nonce:long_nonce ~aad:""
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

let deterministic_authenticated_sender () =
  let generator = rng () in
  let recipient, public = ok (generate_key_pair ~rng:generator Kem.X25519) in
  let sender, sender_public =
    ok (generate_key_pair ~rng:generator Kem.X25519)
  in
  let other_sender, _ = ok (generate_key_pair ~rng:generator Kem.X25519) in
  let ephemeral, ephemeral_public =
    ok (derive_key_pair Kem.X25519 ~ikm:(String.make 32 '\x45'))
  in
  let seal_first setup =
    ok (Rfc9180.Sender.seal (ok setup).Rfc9180.context ~aad:"aad" ~plaintext)
  in
  let setup ~sender =
    Hpke_for_testing.setup_auth_sender x25519_aes_suite ~ephemeral
      ~recipient:public ~sender ~info
  in
  let first = ok (setup ~sender) in
  Alcotest.(check string)
    "encapsulated key is the ephemeral public key"
    (Public_key.to_bytes ephemeral_public)
    first.encapsulated_key;
  let sealed = ok (Rfc9180.Sender.seal first.context ~aad:"aad" ~plaintext) in
  Alcotest.(check string)
    "same keys, same ciphertext" sealed
    (seal_first (setup ~sender));
  Alcotest.(check bool)
    "the sender key enters the shared secret" false
    (String.equal sealed (seal_first (setup ~sender:other_sender)));
  Alcotest.(check bool)
    "Auth and Base modes differ" false
    (String.equal sealed
       (seal_first
          (Hpke_for_testing.setup_base_sender x25519_aes_suite ~ephemeral
             ~recipient:public ~info)));
  let receiver =
    ok
      (Rfc9180.setup_auth_receiver x25519_aes_suite ~recipient
         ~sender:sender_public ~encapsulated_key:first.encapsulated_key ~info)
  in
  Alcotest.(check string)
    "an ordinary receiver opens it" plaintext
    (ok (Rfc9180.Receiver.open_ receiver ~aad:"aad" ~ciphertext:sealed));
  let psk = ok (Psk.create ~secret:(String.make 32 '\x11') ~id:"psk") in
  let psk_setup =
    Hpke_for_testing.setup_auth_psk_sender x25519_aes_suite ~ephemeral
      ~recipient:public ~sender ~psk ~info
  in
  let psk_sealed = seal_first psk_setup in
  Alcotest.(check bool)
    "AuthPSK and Auth modes differ" false
    (String.equal sealed psk_sealed);
  let psk_receiver =
    ok
      (Rfc9180.setup_auth_psk_receiver x25519_aes_suite ~recipient
         ~sender:sender_public ~psk
         ~encapsulated_key:(ok psk_setup).encapsulated_key ~info)
  in
  Alcotest.(check string)
    "AuthPSK round trip" plaintext
    (ok (Rfc9180.Receiver.open_ psk_receiver ~aad:"aad" ~ciphertext:psk_sealed));
  let p256_sender, _ =
    ok (derive_key_pair Kem.P256 ~ikm:(String.make 32 '\x46'))
  in
  expect_key_mismatch "Auth sender key of another KEM"
    (setup ~sender:p256_sender);
  expect_key_mismatch "AuthPSK sender key of another KEM"
    (Hpke_for_testing.setup_auth_psk_sender x25519_aes_suite ~ephemeral
       ~recipient:public ~sender:p256_sender ~psk ~info)

let mlkem_suite kem =
  Suite.create ~kem ~kdf:Kdf.Hkdf_sha256 ~aead:Aead.Aes_128_gcm

let kem_name kem = Format.asprintf "%a" Kem.pp kem

let expect_invalid_public_key label = function
  | Error (Error.Invalid_public_key _) -> ()
  | _ -> Alcotest.failf "%s was not reported as an invalid public key" label

let expect_invalid_private_key label = function
  | Error (Error.Invalid_private_key _) -> ()
  | _ -> Alcotest.failf "%s was not reported as an invalid private key" label

let mlkem_keys () =
  List.iter
    (fun (kem, empty_ikm_seed, long_ikm_seed) ->
      let name = kem_name kem in
      (* draft-ietf-hpke-pq-05, Section 3: GenerateKeyPair takes its randomness
         as the seed, unchanged. The generator holds exactly one seed, so a
         library that drew more would raise and one that drew less or hashed it
         would serialize something else. *)
      let seed = String.init 64 (fun index -> Char.chr (index + 1)) in
      let generated, generated_public =
        ok (generate_key_pair ~rng:(fixed_rng seed) kem)
      in
      Alcotest.(check string)
        (name ^ " generated seed") seed
        (Private_key.to_bytes generated);
      Alcotest.(check int)
        (name ^ " public key size")
        (Kem.public_key_size kem)
        (String.length (Public_key.to_bytes generated_public));
      let reparsed = ok (Private_key.of_bytes ~kem seed) in
      Alcotest.(check string)
        (name ^ " a seed names one key pair")
        (Public_key.to_bytes generated_public)
        (Public_key.to_bytes (Private_key.public_key reparsed));
      Alcotest.(check string)
        (name ^ " public key round trip")
        (Public_key.to_bytes generated_public)
        (Public_key.to_bytes
           (ok
              (Public_key.of_bytes ~kem (Public_key.to_bytes generated_public))));
      (* DeriveKeyPair is SHAKE256 over a framed input. These seeds were
         computed with OpenSSL's SHAKE256; an empty input and one that spans two
         blocks of the sponge complement the 64-byte ones of the draft's
         vectors. *)
      check_hex
        (name ^ " seed of an empty ikm")
        empty_ikm_seed
        (Private_key.to_bytes (fst (ok (derive_key_pair kem ~ikm:""))));
      check_hex
        (name ^ " seed of a 200-byte ikm")
        long_ikm_seed
        (Private_key.to_bytes
           (fst (ok (derive_key_pair kem ~ikm:(String.make 200 '\x42')))));
      let public_size = Kem.public_key_size kem in
      expect_invalid_private_key (name ^ " short seed")
        (Private_key.of_bytes ~kem (String.make 63 '\001'));
      expect_invalid_private_key (name ^ " long seed")
        (Private_key.of_bytes ~kem (String.make 65 '\001'));
      expect_invalid_private_key (name ^ " empty seed")
        (Private_key.of_bytes ~kem "");
      expect_invalid_public_key
        (name ^ " short public key")
        (Public_key.of_bytes ~kem (String.make (public_size - 1) '\000'));
      expect_invalid_public_key
        (name ^ " long public key")
        (Public_key.of_bytes ~kem (String.make (public_size + 1) '\000'));
      (* FIPS 203, Section 7.2: coefficients are encoded in 12 bits and must be
         below q = 3329, which 0xfff is not. *)
      expect_invalid_public_key
        (name ^ " unreduced coefficients")
        (Public_key.of_bytes ~kem (String.make public_size '\xff'));
      (* The same bytes as an encapsulation key of another parameter set. *)
      List.iter
        (fun other ->
          if other <> kem && Kem.public_key_size other <> public_size then
            expect_invalid_public_key
              (name ^ " key parsed as " ^ kem_name other)
              (Public_key.of_bytes ~kem:other
                 (Public_key.to_bytes generated_public)))
        mlkem_kems)
    [
      ( Kem.Mlkem512,
        "44d79e4086cce7b07e85a7d934404a896e00088dcf889343dd8bc42591ca16b0b056f70c04cf2cb43c545f207007b472e6b9c12b51676c32d9d9489663790696",
        "7038f6b1e3a3c5304b702ac013367aed789047715ce4efde75093f980de00774f0e63e2770cd8bc592bd2a5bd30bac321710a62deca4f9a3938b9f642d033043"
      );
      ( Kem.Mlkem768,
        "3eb7ff209ae43d9d412322722b7ba42e242b79e6f604fa9f49fcd3583fda61f842404ebf667a820075b0ec2e3926c4300b93487deedf80fe3ae9aefb0bbe5ada",
        "637e96d0162eee739ef5e37b21029a4830a6326f5739cc180bc1a87271bbd81803c605dc4a9a8413655773664ca8d7ba20db91f1eb8463c134ea958011943220"
      );
      ( Kem.Mlkem1024,
        "08bf57ff69b24f500bc08a4cc8a59619d54ba51a9fcc4bfe36731606a98ced600320a252db8b52896d60285fbe489d7d42d708730e7d72be3a159fd60bafe8eb",
        "4fca201ebc825f40a1bc14e8e4f2bb1ad6fd99a500b10ed1c4466f37149415da1c7e6bb7ac26d5dbf8eaa5ca2ec93c264333ec15b336aadb8f8f758665ecb717"
      );
    ]

(* FIPS 203 decapsulation does not fail on a ciphertext of the right length. One
   that was not made for the key yields a secret of its own, so the receiver is
   set up and only then disagrees with the sender. *)
let mlkem_implicit_rejection () =
  let generator = rng () in
  List.iter
    (fun kem ->
      let name = kem_name kem in
      let suite = mlkem_suite kem in
      let recipient, public = ok (generate_key_pair ~rng:generator kem) in
      let sender =
        ok
          (Rfc9180.setup_base_sender ~rng:generator suite ~recipient:public
             ~info)
      in
      Alcotest.(check int)
        (name ^ " encapsulation size")
        (Kem.encapsulated_key_size kem)
        (String.length sender.encapsulated_key);
      let sealed = ok (Rfc9180.Sender.seal sender.context ~aad:"" ~plaintext) in
      let exported =
        ok (Rfc9180.Sender.export sender.context ~context:"" ~length:32)
      in
      let tampered =
        let bytes = Bytes.of_string sender.encapsulated_key in
        Bytes.set_uint8 bytes 0 (Bytes.get_uint8 bytes 0 lxor 1);
        Bytes.unsafe_to_string bytes
      in
      let rejected =
        ok
          (Rfc9180.setup_base_receiver suite ~recipient
             ~encapsulated_key:tampered ~info)
      in
      expect_open_error
        (name ^ " tampered encapsulation")
        (Rfc9180.Receiver.open_ rejected ~aad:"" ~ciphertext:sealed);
      Alcotest.(check bool)
        (name ^ " tampered encapsulation exports another secret")
        false
        (String.equal exported
           (ok (Rfc9180.Receiver.export rejected ~context:"" ~length:32)));
      expect_open_error
        (name ^ " tampered encapsulation, single-shot")
        (Rfc9180.open_base suite ~recipient ~info ~aad:""
           ~ciphertext:
             { Rfc9180.encapsulated_key = tampered; ciphertext = sealed });
      let receiver =
        ok
          (Rfc9180.setup_base_receiver suite ~recipient
             ~encapsulated_key:sender.encapsulated_key ~info)
      in
      Alcotest.(check string)
        (name ^ " untampered encapsulation")
        plaintext
        (ok (Rfc9180.Receiver.open_ receiver ~aad:"" ~ciphertext:sealed));
      (* Only a wrong length is a malformed encapsulation. A public key is not
         an encapsulation either, although for a Diffie-Hellman KEM it is. *)
      List.iter
        (fun (label, encapsulated_key) ->
          (match
             Rfc9180.setup_base_receiver suite ~recipient ~encapsulated_key
               ~info
           with
          | Error (Error.Invalid_encapsulation _) -> ()
          | _ -> Alcotest.failf "%s %s was not structured" name label);
          expect_open_error
            (name ^ " " ^ label ^ ", single-shot")
            (Rfc9180.open_base suite ~recipient ~info ~aad:""
               ~ciphertext:{ Rfc9180.encapsulated_key; ciphertext = sealed }))
        ([
           ("empty encapsulation", "");
           ( "short encapsulation",
             String.sub tampered 0 (String.length tampered - 1) );
           ("long encapsulation", tampered ^ "\000");
         ]
        @
        if Kem.public_key_size kem = Kem.encapsulated_key_size kem then []
        else [ ("public key as encapsulation", Public_key.to_bytes public) ]))
    mlkem_kems

let expect_unsupported_mode label = function
  | Error Error.Unsupported_mode -> ()
  | Error error -> Alcotest.failf "%s returned %s" label (error_to_string error)
  | Ok _ -> Alcotest.failf "%s unexpectedly succeeded" label

(* draft-ietf-hpke-pq-05, Section 7.2: ML-KEM and the hybrids have no AuthEncap
   or AuthDecap. *)
let mlkem_has_no_auth_modes () =
  let generator = rng () in
  let psk = ok (Psk.create ~secret:(String.make 32 '\x11') ~id:"psk") in
  let aad = "" in
  let x25519_sender, x25519_sender_public =
    ok (generate_key_pair ~rng:generator Kem.X25519)
  in
  List.iter
    (fun kem ->
      let name = kem_name kem in
      let suite = mlkem_suite kem in
      let exporter = Suite.export_only ~kem ~kdf:Kdf.Hkdf_sha256 in
      let recipient, public = ok (generate_key_pair ~rng:generator kem) in
      let own_sender, own_sender_public =
        ok (generate_key_pair ~rng:generator kem)
      in
      let sealed =
        ok
          (Rfc9180.seal_base ~rng:generator suite ~recipient:public ~info ~aad
             ~plaintext)
      in
      (* It is the suite that lacks the mode, so a sender key of another KEM is
         reported the same way. A generator with nothing to give shows that no
         encapsulation was attempted. *)
      List.iter
        (fun (keys, sender, sender_public) ->
          let expect label =
            expect_unsupported_mode (name ^ " " ^ label ^ keys)
          in
          let rng = fixed_rng "" in
          expect "setup_auth_sender"
            (Rfc9180.setup_auth_sender ~rng suite ~recipient:public ~sender
               ~info);
          expect "setup_auth_sender, export-only"
            (Rfc9180.setup_auth_sender ~rng exporter ~recipient:public ~sender
               ~info);
          expect "setup_auth_psk_sender"
            (Rfc9180.setup_auth_psk_sender ~rng suite ~recipient:public ~sender
               ~psk ~info);
          expect "seal_auth"
            (Rfc9180.seal_auth ~rng suite ~recipient:public ~sender ~info ~aad
               ~plaintext);
          expect "seal_auth_psk"
            (Rfc9180.seal_auth_psk ~rng suite ~recipient:public ~sender ~psk
               ~info ~aad ~plaintext);
          expect "setup_auth_receiver"
            (Rfc9180.setup_auth_receiver suite ~recipient ~sender:sender_public
               ~encapsulated_key:sealed.encapsulated_key ~info);
          expect "setup_auth_psk_receiver"
            (Rfc9180.setup_auth_psk_receiver suite ~recipient
               ~sender:sender_public ~psk
               ~encapsulated_key:sealed.encapsulated_key ~info);
          (* The caller's mistake, which single-shot opens do not normalize. *)
          expect "open_auth"
            (Rfc9180.open_auth suite ~recipient ~sender:sender_public ~info ~aad
               ~ciphertext:sealed);
          expect "open_auth_psk"
            (Rfc9180.open_auth_psk suite ~recipient ~sender:sender_public ~psk
               ~info ~aad ~ciphertext:sealed))
        [
          (" with its own keys", own_sender, own_sender_public);
          (" with X25519 keys", x25519_sender, x25519_sender_public);
        ];
      (* A Diffie-Hellman suite has the mode, and there an ML-KEM sender key is
         a key of another KEM. *)
      let x25519_recipient, x25519_public =
        ok (generate_key_pair ~rng:generator Kem.X25519)
      in
      expect_key_mismatch
        (name ^ " sender private key in an X25519 suite")
        (Rfc9180.setup_auth_sender ~rng:generator x25519_aes_suite
           ~recipient:x25519_public ~sender:own_sender ~info);
      expect_key_mismatch
        (name ^ " sender public key in an X25519 suite")
        (Rfc9180.setup_auth_receiver x25519_aes_suite
           ~recipient:x25519_recipient ~sender:own_sender_public
           ~encapsulated_key:(String.make 32 '\001') ~info);
      (* ML-KEM encapsulates without an ephemeral key, so there is none for
         hpke.for_testing to take. A fixed generator does that job: see
         [mlkem_keys] and the draft's vectors. *)
      expect_invalid_private_key (name ^ " ephemeral key")
        (Hpke_for_testing.setup_base_sender suite ~ephemeral:own_sender
           ~recipient:public ~info);
      expect_invalid_private_key
        (name ^ " ephemeral key, PSK mode")
        (Hpke_for_testing.setup_psk_sender suite ~ephemeral:own_sender
           ~recipient:public ~psk ~info);
      expect_unsupported_mode
        (name ^ " ephemeral key, Auth mode")
        (Hpke_for_testing.setup_auth_sender suite ~ephemeral:own_sender
           ~recipient:public ~sender:own_sender ~info);
      expect_unsupported_mode
        (name ^ " ephemeral key, AuthPSK mode")
        (Hpke_for_testing.setup_auth_psk_sender suite ~ephemeral:own_sender
           ~recipient:public ~sender:own_sender ~psk ~info);
      (* The mode is refused before the keys are compared. *)
      expect_unsupported_mode
        (name ^ " X25519 ephemeral and sender keys, Auth mode")
        (Hpke_for_testing.setup_auth_sender suite ~ephemeral:x25519_sender
           ~recipient:public ~sender:x25519_sender ~info);
      expect_key_mismatch
        (name ^ " X25519 ephemeral key")
        (Hpke_for_testing.setup_base_sender suite ~ephemeral:x25519_sender
           ~recipient:public ~info))
    (mlkem_kems @ hybrid_kems)

(* The ML-KEM parameter set and the group of each hybrid KEM, the latter named
   by the Diffie-Hellman KEM over it. *)
let hybrid_parts = function
  | Kem.Mlkem768_p256 -> (Kem.Mlkem768, Kem.P256)
  | Kem.Mlkem768_x25519 -> (Kem.Mlkem768, Kem.X25519)
  | Kem.Mlkem1024_p384 -> (Kem.Mlkem1024, Kem.P384)
  | kem -> Alcotest.failf "%s is not a hybrid KEM" (kem_name kem)

let expect_invalid_encapsulation label = function
  | Error (Error.Invalid_encapsulation _) -> ()
  | Error error -> Alcotest.failf "%s returned %s" label (error_to_string error)
  | Ok _ -> Alcotest.failf "%s was not reported as malformed" label

let with_byte_flipped bytes index =
  let bytes = Bytes.of_string bytes in
  Bytes.set_uint8 bytes index (Bytes.get_uint8 bytes index lxor 1);
  Bytes.unsafe_to_string bytes

(* draft-ietf-hpke-pq-05, Section 4: a hybrid private key is a 32-byte seed,
   which GenerateKeyPair draws and DeriveKeyPair derives with SHAKE256, and a
   public key is the ML-KEM key followed by the group element. *)
let hybrid_keys () =
  let generator = rng () in
  List.iter
    (fun (kem, empty_ikm_seed, long_ikm_seed) ->
      let name = kem_name kem in
      let pq, group = hybrid_parts kem in
      (* The generator holds exactly one seed, so a library that drew more would
         raise and one that drew less or hashed it would serialize something
         else. *)
      let seed = String.init 32 (fun index -> Char.chr (index + 1)) in
      let generated, generated_public =
        ok (generate_key_pair ~rng:(fixed_rng seed) kem)
      in
      Alcotest.(check string)
        (name ^ " generated seed") seed
        (Private_key.to_bytes generated);
      let public_bytes = Public_key.to_bytes generated_public in
      Alcotest.(check int)
        (name ^ " public key size")
        (Kem.public_key_size kem)
        (String.length public_bytes);
      Alcotest.(check string)
        (name ^ " a seed names one key pair")
        public_bytes
        (Public_key.to_bytes
           (Private_key.public_key (ok (Private_key.of_bytes ~kem seed))));
      Alcotest.(check string)
        (name ^ " public key round trip")
        public_bytes
        (Public_key.to_bytes (ok (Public_key.of_bytes ~kem public_bytes)));
      (* SHAKE256 over a framed input, as for ML-KEM, but 32 bytes of it. These
         seeds were computed with OpenSSL's SHAKE256. *)
      check_hex
        (name ^ " seed of an empty ikm")
        empty_ikm_seed
        (Private_key.to_bytes (fst (ok (derive_key_pair kem ~ikm:""))));
      check_hex
        (name ^ " seed of a 200-byte ikm")
        long_ikm_seed
        (Private_key.to_bytes
           (fst (ok (derive_key_pair kem ~ikm:(String.make 200 '\x42')))));
      expect_invalid_private_key (name ^ " short seed")
        (Private_key.of_bytes ~kem (String.make 31 '\001'));
      expect_invalid_private_key (name ^ " long seed")
        (Private_key.of_bytes ~kem (String.make 33 '\001'));
      expect_invalid_private_key (name ^ " ML-KEM seed")
        (Private_key.of_bytes ~kem (String.make 64 '\001'));
      let public_size = Kem.public_key_size kem in
      let pq_size = Kem.public_key_size pq in
      let element = String.sub public_bytes pq_size (public_size - pq_size) in
      Alcotest.(check int)
        (name ^ " element size")
        (Kem.public_key_size group)
        (String.length element);
      expect_invalid_public_key
        (name ^ " short public key")
        (Public_key.of_bytes ~kem (String.sub public_bytes 0 (public_size - 1)));
      expect_invalid_public_key
        (name ^ " long public key")
        (Public_key.of_bytes ~kem (public_bytes ^ "\000"));
      expect_invalid_public_key
        (name ^ " ML-KEM half alone")
        (Public_key.of_bytes ~kem (String.sub public_bytes 0 pq_size));
      (* FIPS 203, Section 7.2, holds for the ML-KEM half. *)
      expect_invalid_public_key
        (name ^ " unreduced coefficients")
        (Public_key.of_bytes ~kem (String.make pq_size '\xff' ^ element));
      let with_element element =
        Public_key.of_bytes ~kem (String.sub public_bytes 0 pq_size ^ element)
      in
      match group with
      | Kem.X25519 ->
          (* Every value parses, and a low-order one fails when it is used. *)
          List.iter
            (fun (label, element) ->
              let public = ok (with_element element) in
              expect_invalid_public_key
                (name ^ " " ^ label ^ " as recipient element")
                (Rfc9180.seal_base ~rng:generator (mlkem_suite kem)
                   ~recipient:public ~info ~aad:"" ~plaintext))
            [
              ("zero", String.make 32 '\000');
              ("one", "\001" ^ String.make 31 '\000');
            ]
      | _ ->
          expect_invalid_public_key
            (name ^ " compressed element")
            (with_element
               ("\002" ^ String.sub element 1 (String.length element - 1)));
          expect_invalid_public_key
            (name ^ " element off the curve")
            (with_element
               ("\004" ^ String.make (String.length element - 1) '\000')))
    [
      ( Kem.Mlkem768_p256,
        "1dcb72581fff704b0a515546a069c4f472029270e1ed2d8d20879b3a98799d4f",
        "86f8444213b7ee8b310161c918437fecb6b7154cd17bffe6db6195e3b04dec90" );
      ( Kem.Mlkem768_x25519,
        "a1313c048b30e1aba5ecb9ec783c7fa8e9c6a48f568a685fbe48ba5e2a5ca66c",
        "ba630bc9ac9a88e2ae33e5ba4bbd378b9159be0e16757ea0ffe42e156443d1cc" );
      ( Kem.Mlkem1024_p384,
        "c13ff089f94b257e33c1ff61e3eff983b9837b7cb76b8a0980b3509fee0806c0",
        "697fe7767cd7ead3cf61db4a58f303f4e6ff534dca1a1cc79156ca9768b2cd46" );
    ]

(* A hybrid encapsulated key is an ML-KEM ciphertext, which decapsulates
   whatever it holds, followed by an ephemeral element, which is validated. *)
let hybrid_encapsulations () =
  let generator = rng () in
  List.iter
    (fun kem ->
      let name = kem_name kem in
      let pq, group = hybrid_parts kem in
      let suite = mlkem_suite kem in
      let recipient, public = ok (generate_key_pair ~rng:generator kem) in
      let sender =
        ok
          (Rfc9180.setup_base_sender ~rng:generator suite ~recipient:public
             ~info)
      in
      let encapsulated_key = sender.encapsulated_key in
      Alcotest.(check int)
        (name ^ " encapsulation size")
        (Kem.encapsulated_key_size kem)
        (String.length encapsulated_key);
      let sealed = ok (Rfc9180.Sender.seal sender.context ~aad:"" ~plaintext) in
      let receive encapsulated_key =
        Rfc9180.setup_base_receiver suite ~recipient ~encapsulated_key ~info
      in
      let open_single_shot encapsulated_key =
        Rfc9180.open_base suite ~recipient ~info ~aad:""
          ~ciphertext:{ Rfc9180.encapsulated_key; ciphertext = sealed }
      in
      Alcotest.(check string)
        (name ^ " untampered encapsulation")
        plaintext
        (ok
           (Rfc9180.Receiver.open_
              (ok (receive encapsulated_key))
              ~aad:"" ~ciphertext:sealed));
      (* Implicit rejection: another secret, and no error until the open. *)
      let tampered_pq = with_byte_flipped encapsulated_key 0 in
      expect_open_error
        (name ^ " tampered ML-KEM ciphertext")
        (Rfc9180.Receiver.open_
           (ok (receive tampered_pq))
           ~aad:"" ~ciphertext:sealed);
      expect_open_error
        (name ^ " tampered ML-KEM ciphertext, single-shot")
        (open_single_shot tampered_pq);
      let pq_size = Kem.encapsulated_key_size pq in
      let element_size = Kem.public_key_size group in
      let with_element element =
        String.sub encapsulated_key 0 pq_size ^ element
      in
      let malformed =
        [
          ("empty encapsulation", "");
          ( "short encapsulation",
            String.sub encapsulated_key 0 (String.length encapsulated_key - 1)
          );
          ("long encapsulation", encapsulated_key ^ "\000");
          ("ML-KEM ciphertext alone", String.sub encapsulated_key 0 pq_size);
        ]
        (* MLKEM1024-P384's public key is as long as its encapsulation. *)
        @ (if Kem.public_key_size kem = Kem.encapsulated_key_size kem then []
           else [ ("public key as encapsulation", Public_key.to_bytes public) ])
        @
        match group with
        | Kem.X25519 ->
            [
              ("zero element", with_element (String.make 32 '\000'));
              ("element one", with_element ("\001" ^ String.make 31 '\000'));
            ]
        | _ ->
            [
              ( "compressed element",
                with_element
                  ("\002"
                  ^ String.sub encapsulated_key (pq_size + 1) (element_size - 1)
                  ) );
              ( "element off the curve",
                with_element ("\004" ^ String.make (element_size - 1) '\000') );
              ( "tampered element",
                with_byte_flipped encapsulated_key
                  (String.length encapsulated_key - 1) );
            ]
      in
      List.iter
        (fun (label, encapsulated_key) ->
          expect_invalid_encapsulation
            (name ^ " " ^ label)
            (receive encapsulated_key);
          expect_open_error
            (name ^ " " ^ label ^ ", single-shot")
            (open_single_shot encapsulated_key))
        malformed;
      (* Any other X25519 value of full order is an element, and yields another
         secret. *)
      if group = Kem.X25519 then
        expect_open_error
          (name ^ " tampered element")
          (Rfc9180.Receiver.open_
             (ok
                (receive
                   (with_byte_flipped encapsulated_key
                      (String.length encapsulated_key - 1))))
             ~aad:"" ~ciphertext:sealed))
    hybrid_kems

(* The ephemeral scalar of a P-256 or P-384 hybrid is drawn from the
   encapsulation's randomness by rejection sampling
   (draft-irtf-cfrg-concrete-hybrid-kems, Section 3.1.1). A seed without a valid
   candidate, which occurs with negligible probability, is drawn again. *)
let hybrid_rejection_sampling () =
  List.iter
    (fun kem ->
      let name = kem_name kem in
      let _, group = hybrid_parts kem in
      let suite = mlkem_suite kem in
      let recipient, public =
        ok (derive_key_pair kem ~ikm:(String.make 32 '\x07'))
      in
      let scalar_size = Kem.private_key_size group in
      let seed_size = if group = Kem.P256 then 128 else 48 in
      let candidates = seed_size / scalar_size in
      let zero = String.make scalar_size '\000' in
      let too_large = String.make scalar_size '\xff' in
      let valid = String.make scalar_size '\x01' in
      let pq_randomness = String.make 32 '\x33' in
      let encapsulate randomness =
        Rfc9180.setup_base_sender ~rng:(fixed_rng randomness) suite
          ~recipient:public ~info
      in
      let element encapsulated_key =
        String.sub encapsulated_key
          (String.length encapsulated_key - Kem.public_key_size group)
          (Kem.public_key_size group)
      in
      let public_of scalar =
        Public_key.to_bytes
          (Private_key.public_key (ok (Private_key.of_bytes ~kem:group scalar)))
      in
      (* The last candidate is the first valid one. *)
      let seed =
        String.concat ""
          (List.init candidates (fun index ->
               if index = candidates - 1 then valid
               else if index mod 2 = 0 then zero
               else too_large))
      in
      let sender = ok (encapsulate (pq_randomness ^ seed)) in
      Alcotest.(check string)
        (name ^ " first valid candidate")
        (public_of valid)
        (element sender.encapsulated_key);
      let receiver =
        ok
          (Rfc9180.setup_base_receiver suite ~recipient
             ~encapsulated_key:sender.encapsulated_key ~info)
      in
      Alcotest.(check string)
        (name ^ " round trip") plaintext
        (ok
           (Rfc9180.Receiver.open_ receiver ~aad:""
              ~ciphertext:
                (ok (Rfc9180.Sender.seal sender.context ~aad:"" ~plaintext))));
      (* A seed without a valid candidate is drawn again, with the ML-KEM
         randomness. *)
      let rejected = pq_randomness ^ String.make seed_size '\xff' in
      let drawn_again =
        String.make 32 '\x44' ^ valid
        ^ String.make (seed_size - scalar_size) '\000'
      in
      Alcotest.(check string)
        (name ^ " seed drawn again")
        (ok (encapsulate drawn_again)).encapsulated_key
        (ok (encapsulate (rejected ^ drawn_again))).encapsulated_key;
      match
        encapsulate (String.concat "" (List.init 8 (fun _ -> rejected)))
      with
      | Error (Error.Internal_error _) -> ()
      | Error error ->
          Alcotest.failf "%s exhausted sampling returned %s" name
            (error_to_string error)
      | Ok _ -> Alcotest.failf "%s sampled a scalar from no candidate" name)
    [ Kem.Mlkem768_p256; Kem.Mlkem1024_p384 ]

(* Hpke.Draft_hpke_04 *)

let draft_kdfs =
  Draft_hpke_04.Kdf.
    [
      Hkdf_sha256;
      Hkdf_sha384;
      Hkdf_sha512;
      Shake128;
      Shake256;
      Turboshake128;
      Turboshake256;
    ]

let draft_registry () =
  List.iter
    (fun (kdf, identifier, nh, two_stage) ->
      let name = Format.asprintf "%a" Draft_hpke_04.Kdf.pp kdf in
      Alcotest.(check int)
        (name ^ " identifier") identifier
        (Draft_hpke_04.Kdf.to_int kdf);
      Alcotest.(check bool)
        (name ^ " identifier round trip")
        true
        (Draft_hpke_04.Kdf.of_int identifier = Ok kdf);
      Alcotest.(check int) (name ^ " Nh") nh (Draft_hpke_04.Kdf.hash_size kdf);
      Alcotest.(check bool)
        (name ^ " two-stage") true
        (Draft_hpke_04.Kdf.two_stage kdf = two_stage);
      (* A two-stage KDF has no Derive, and a one-stage one derives. *)
      match (two_stage, Draft_hpke_04.Kdf.derive kdf "ikm" 5) with
      | Some _, Error (Error.Unsupported_algorithm id) ->
          Alcotest.(check int) (name ^ " Derive refused") identifier id
      | None, Ok output ->
          Alcotest.(check int)
            (name ^ " Derive length") 5 (String.length output)
      | _ -> Alcotest.failf "%s Derive" name)
    [
      (Draft_hpke_04.Kdf.Hkdf_sha256, 0x0001, 32, Some Kdf.Hkdf_sha256);
      (Draft_hpke_04.Kdf.Hkdf_sha384, 0x0002, 48, Some Kdf.Hkdf_sha384);
      (Draft_hpke_04.Kdf.Hkdf_sha512, 0x0003, 64, Some Kdf.Hkdf_sha512);
      (Draft_hpke_04.Kdf.Shake128, 0x0010, 32, None);
      (Draft_hpke_04.Kdf.Shake256, 0x0011, 64, None);
      (Draft_hpke_04.Kdf.Turboshake128, 0x0012, 32, None);
      (Draft_hpke_04.Kdf.Turboshake256, 0x0013, 64, None);
    ];
  Alcotest.(check int) "every draft KDF is listed" (List.length draft_kdfs) 7;
  (* SHAKE of FIPS 202, from OpenSSL's hashlib: an empty input, cut to 8. *)
  check_hex "SHAKE128 Derive" "7f9c2ba4e88f827d"
    (ok (Draft_hpke_04.Kdf.derive Draft_hpke_04.Kdf.Shake128 "" 8));
  check_hex "SHAKE256 Derive" "46b9dd2b0ba88d13"
    (ok (Draft_hpke_04.Kdf.derive Draft_hpke_04.Kdf.Shake256 "" 8));
  (match Draft_hpke_04.Kdf.derive Draft_hpke_04.Kdf.Shake256 "" (-1) with
  | Error (Error.Invalid_length _) -> ()
  | _ -> Alcotest.fail "negative Derive length");
  (* TurboSHAKE and unknown identifiers are refused. *)
  List.iter
    (fun identifier ->
      match Draft_hpke_04.Kdf.of_int identifier with
      | Error (Error.Unsupported_algorithm id) when id = identifier -> ()
      | _ -> Alcotest.failf "KDF 0x%04x was accepted" identifier)
    [ 0x0000; 0x0004; 0x0014; 0xffff ]

(* Every KEM with every one-stage KDF and AEAD, in both modes. *)
let draft_round_trips () =
  let generator = rng () in
  let psk = ok (Psk.create ~secret:(String.make 32 '\x5a') ~id:"draft-psk") in
  List.iter
    (fun kem ->
      let recipient, public = ok (generate_key_pair ~rng:generator kem) in
      List.iter
        (fun kdf ->
          List.iter
            (fun aead ->
              let suite = Draft_hpke_04.Suite.create ~kem ~kdf ~aead in
              let sealed =
                ok
                  (Draft_hpke_04.seal_base ~rng:generator suite
                     ~recipient:public ~info:"draft-info" ~aad:"draft-aad"
                     ~plaintext:"\000draft\255")
              in
              Alcotest.(check string)
                "draft Base round trip" "\000draft\255"
                (ok
                   (Draft_hpke_04.open_base suite ~recipient ~info:"draft-info"
                      ~aad:"draft-aad" ~ciphertext:sealed));
              let sealed =
                ok
                  (Draft_hpke_04.seal_psk ~rng:generator suite ~recipient:public
                     ~psk ~info:"" ~aad:"" ~plaintext:"")
              in
              Alcotest.(check string)
                "draft PSK round trip" ""
                (ok
                   (Draft_hpke_04.open_psk suite ~recipient ~psk ~info:""
                      ~aad:"" ~ciphertext:sealed));
              (* The modes are bound: a PSK message does not open in Base. *)
              expect_open_error "draft PSK message opened in Base mode"
                (Draft_hpke_04.open_base suite ~recipient ~info:"" ~aad:""
                   ~ciphertext:sealed))
            all_aeads;
          let exporter = Draft_hpke_04.Suite.export_only ~kem ~kdf in
          let setup =
            ok
              (Draft_hpke_04.setup_base_sender ~rng:generator exporter
                 ~recipient:public ~info:"export")
          in
          let receiver =
            ok
              (Draft_hpke_04.setup_base_receiver exporter ~recipient
                 ~encapsulated_key:setup.encapsulated_key ~info:"export")
          in
          Alcotest.(check string)
            "draft exports agree"
            (ok (Rfc9180.Sender.export setup.context ~context:"c" ~length:64))
            (ok (Rfc9180.Receiver.export receiver ~context:"c" ~length:64)))
        Draft_hpke_04.Kdf.[ Shake128; Shake256; Turboshake128; Turboshake256 ])
    all_kems

(* With an HKDF the draft is RFC 9180: from the same randomness, the same
   encapsulation, ciphertext and export. With SHAKE it is something else. *)
let draft_hkdf_is_rfc9180 () =
  let recipient, public =
    ok (derive_key_pair Kem.X25519 ~ikm:(String.make 32 '\x31'))
  in
  let seal_with setup =
    let (setup : _ Rfc9180.sender_setup) = ok setup in
    ( setup.Rfc9180.encapsulated_key,
      ok (Rfc9180.Sender.seal setup.context ~aad:"a" ~plaintext:"p"),
      ok (Rfc9180.Sender.export setup.context ~context:"c" ~length:32) )
  in
  let randomness = String.make 32 '\x77' in
  List.iter
    (fun (draft_kdf, kdf) ->
      let rfc =
        seal_with
          (Rfc9180.setup_base_sender ~rng:(fixed_rng randomness)
             (Suite.create ~kem:Kem.X25519 ~kdf ~aead:Aead.Aes_128_gcm)
             ~recipient:public ~info:"i")
      in
      let draft =
        seal_with
          (Draft_hpke_04.setup_base_sender ~rng:(fixed_rng randomness)
             (Draft_hpke_04.Suite.create ~kem:Kem.X25519 ~kdf:draft_kdf
                ~aead:Aead.Aes_128_gcm)
             ~recipient:public ~info:"i")
      in
      Alcotest.(check bool)
        "HKDF draft suite is the RFC 9180 suite" true (rfc = draft))
    Draft_hpke_04.Kdf.
      [
        (Hkdf_sha256, Kdf.Hkdf_sha256);
        (Hkdf_sha384, Kdf.Hkdf_sha384);
        (Hkdf_sha512, Kdf.Hkdf_sha512);
      ];
  let shake =
    ok
      (Draft_hpke_04.setup_base_sender ~rng:(fixed_rng randomness)
         (Draft_hpke_04.Suite.create ~kem:Kem.X25519
            ~kdf:Draft_hpke_04.Kdf.Shake128 ~aead:Aead.Aes_128_gcm)
         ~recipient:public ~info:"i")
  in
  let rfc =
    ok
      (Rfc9180.setup_base_sender ~rng:(fixed_rng randomness) x25519_aes_suite
         ~recipient:public ~info:"i")
  in
  Alcotest.(check string)
    "the KEM does not depend on the KDF" rfc.encapsulated_key
    shake.encapsulated_key;
  Alcotest.(check bool)
    "SHAKE128 derives other keys" false
    (ok (Rfc9180.Sender.seal shake.context ~aad:"a" ~plaintext:"p")
    = ok (Rfc9180.Sender.seal rfc.context ~aad:"a" ~plaintext:"p"));
  ignore recipient

(* draft-ietf-hpke-hpke-04, Section 7.2.1: a one-stage KDF frames info, the PSK
   and its identifier in two bytes, and an export's length in two bytes. *)
let draft_one_stage_limits () =
  let generator = rng () in
  let recipient, public = ok (generate_key_pair ~rng:generator Kem.X25519) in
  let suite =
    Draft_hpke_04.Suite.create ~kem:Kem.X25519 ~kdf:Draft_hpke_04.Kdf.Shake256
      ~aead:Aead.Chacha20_poly1305
  in
  let longest = String.make 0xffff 'i' and too_long = String.make 0x10000 'i' in
  let setup =
    ok
      (Draft_hpke_04.setup_base_sender ~rng:generator suite ~recipient:public
         ~info:longest)
  in
  let receiver =
    ok
      (Draft_hpke_04.setup_base_receiver suite ~recipient
         ~encapsulated_key:setup.encapsulated_key ~info:longest)
  in
  Alcotest.(check string)
    "65535-byte info" "m"
    (ok
       (Rfc9180.Receiver.open_ receiver ~aad:""
          ~ciphertext:
            (ok (Rfc9180.Sender.seal setup.context ~aad:"" ~plaintext:"m"))));
  (match
     Draft_hpke_04.setup_base_sender ~rng:generator suite ~recipient:public
       ~info:too_long
   with
  | Error (Error.Invalid_length _) -> ()
  | _ -> Alcotest.fail "a 65536-byte info was accepted");
  (match
     Draft_hpke_04.setup_base_receiver suite ~recipient
       ~encapsulated_key:setup.encapsulated_key ~info:too_long
   with
  | Error (Error.Invalid_length _) -> ()
  | _ -> Alcotest.fail "a 65536-byte info was accepted by the receiver");
  expect_open_error "a 65536-byte info, single-shot"
    (Draft_hpke_04.open_base suite ~recipient ~info:too_long ~aad:""
       ~ciphertext:
         {
           Draft_hpke_04.encapsulated_key = setup.encapsulated_key;
           ciphertext = "";
         });
  let long_psk = ok (Psk.create ~secret:too_long ~id:"id") in
  (match
     Draft_hpke_04.setup_psk_sender ~rng:generator suite ~recipient:public
       ~psk:long_psk ~info:""
   with
  | Error (Error.Invalid_length _) -> ()
  | _ -> Alcotest.fail "a 65536-byte PSK was accepted");
  let long_id = ok (Psk.create ~secret:(String.make 32 'k') ~id:too_long) in
  (match
     Draft_hpke_04.setup_psk_sender ~rng:generator suite ~recipient:public
       ~psk:long_id ~info:""
   with
  | Error (Error.Invalid_length _) -> ()
  | _ -> Alcotest.fail "a 65536-byte PSK identifier was accepted");
  let export length = Rfc9180.Sender.export setup.context ~context:"" ~length in
  Alcotest.(check int)
    "65535-byte export" 0xffff
    (String.length (ok (export 0xffff)));
  List.iter
    (fun length ->
      match export length with
      | Error Error.Export_length_out_of_range -> ()
      | _ -> Alcotest.failf "export of %d bytes" length)
    [ -1; 0x10000 ];
  (* An HKDF suite keeps RFC 9180's bound of 255 Nh and has no bound on info. *)
  let hkdf =
    Draft_hpke_04.Suite.create ~kem:Kem.X25519
      ~kdf:Draft_hpke_04.Kdf.Hkdf_sha256 ~aead:Aead.Chacha20_poly1305
  in
  let setup =
    ok
      (Draft_hpke_04.setup_base_sender ~rng:generator hkdf ~recipient:public
         ~info:too_long)
  in
  (match
     Rfc9180.Sender.export setup.context ~context:"" ~length:((255 * 32) + 1)
   with
  | Error Error.Export_length_out_of_range -> ()
  | _ -> Alcotest.fail "an HKDF export beyond 255 Nh");
  (* A key of another KEM. *)
  let p256, _ = ok (generate_key_pair ~rng:generator Kem.P256) in
  expect_key_mismatch "draft recipient key of another KEM"
    (Draft_hpke_04.setup_base_receiver suite ~recipient:p256
       ~encapsulated_key:setup.encapsulated_key ~info:"");
  expect_key_mismatch "draft recipient key of another KEM, single-shot"
    (Draft_hpke_04.open_base suite ~recipient:p256 ~info:"" ~aad:""
       ~ciphertext:{ Draft_hpke_04.encapsulated_key = ""; ciphertext = "" })

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
      let _, sender =
        ok (derive_key_pair Kem.X25519 ~ikm:(String.make 32 '\x43'))
      in
      (* Arbitrary bytes are at worst a malformed encapsulation. *)
      let reported = function
        | Ok _ | Error (Error.Invalid_encapsulation _) -> true
        | Error _ -> false
      in
      ignore (Public_key.of_bytes ~kem:Kem.X25519 input);
      reported
        (Rfc9180.setup_base_receiver x25519_aes_suite ~recipient
           ~encapsulated_key:input ~info:"fuzz")
      && reported
           (Rfc9180.setup_auth_receiver x25519_aes_suite ~recipient ~sender
              ~encapsulated_key:input ~info:"fuzz"))

let qcheck_mlkem_peer_input_total =
  let recipients =
    lazy
      (List.map
         (fun kem ->
           (kem, fst (ok (derive_key_pair kem ~ikm:(String.make 64 '\x42')))))
         mlkem_kems)
  in
  let generator =
    let open QCheck2.Gen in
    let* kem =
      map (List.nth mlkem_kems) (int_bound (List.length mlkem_kems - 1))
    in
    let* exact = bool in
    let* input =
      string_size
        (if exact then return (Kem.encapsulated_key_size kem)
         else int_bound 2048)
    in
    return (kem, input)
  in
  QCheck2.Test.make ~name:"ML-KEM peer input never raises" ~count:200 generator
    (fun (kem, input) ->
      let recipient = List.assoc kem (Lazy.force recipients) in
      ignore (Public_key.of_bytes ~kem input);
      (* Any bytes of the right length decapsulate, to a secret nothing was
         sealed under; any others are a malformed encapsulation. *)
      match
        Rfc9180.setup_base_receiver (mlkem_suite kem) ~recipient
          ~encapsulated_key:input ~info:"fuzz"
      with
      | Ok receiver -> (
          String.length input = Kem.encapsulated_key_size kem
          &&
          match
            Rfc9180.Receiver.open_ receiver ~aad:""
              ~ciphertext:(String.make 32 '\000')
          with
          | Error Error.Open_error -> true
          | _ -> false)
      | Error (Error.Invalid_encapsulation _) ->
          String.length input <> Kem.encapsulated_key_size kem
      | Error _ -> false)

let qcheck_hybrid_peer_input_total =
  let recipients =
    lazy
      (List.map
         (fun kem ->
           (kem, fst (ok (derive_key_pair kem ~ikm:(String.make 32 '\x42')))))
         hybrid_kems)
  in
  let generator =
    let open QCheck2.Gen in
    let* kem =
      map (List.nth hybrid_kems) (int_bound (List.length hybrid_kems - 1))
    in
    let* exact = bool in
    let* input =
      string_size
        (if exact then return (Kem.encapsulated_key_size kem)
         else int_bound 2048)
    in
    return (kem, input)
  in
  QCheck2.Test.make ~name:"hybrid peer input never raises" ~count:200 generator
    (fun (kem, input) ->
      let recipient = List.assoc kem (Lazy.force recipients) in
      ignore (Public_key.of_bytes ~kem input);
      (* Bytes of the right length decapsulate, to a secret nothing was sealed
         under, unless their element is invalid; any others are a malformed
         encapsulation. *)
      match
        Rfc9180.setup_base_receiver (mlkem_suite kem) ~recipient
          ~encapsulated_key:input ~info:"fuzz"
      with
      | Ok receiver -> (
          String.length input = Kem.encapsulated_key_size kem
          &&
          match
            Rfc9180.Receiver.open_ receiver ~aad:""
              ~ciphertext:(String.make 32 '\000')
          with
          | Error Error.Open_error -> true
          | _ -> false)
      | Error (Error.Invalid_encapsulation _) -> true
      | Error _ -> false)

let () =
  Alcotest.run "hpke"
    [
      ( "RFC 9180 vectors",
        [
          Alcotest.test_case "X25519 AES Base" `Quick rfc9180_base_vector;
          Alcotest.test_case "X25519 AES PSK" `Quick rfc9180_psk_vector;
          Alcotest.test_case "X25519 ChaCha Base" `Quick rfc9180_chacha_vector;
          Alcotest.test_case "X25519 AES Auth" `Quick rfc9180_auth_vector;
          Alcotest.test_case "X25519 AES AuthPSK" `Quick rfc9180_auth_psk_vector;
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
          Alcotest.test_case "all 99 Base combinations" `Quick
            all_suite_round_trips;
          Alcotest.test_case "PSK all KEMs" `Quick psk_round_trips;
          Alcotest.test_case "Auth and AuthPSK all Diffie-Hellman KEMs" `Quick
            authenticated_round_trips;
          Alcotest.test_case "export-only" `Quick export_only;
        ] );
      ( "invariants",
        [
          Alcotest.test_case "failed open retains sequence" `Quick
            failed_open_does_not_advance;
          Alcotest.test_case "malformed inputs" `Quick malformed_inputs;
          Alcotest.test_case "Montgomery private-key clamping" `Quick
            montgomery_private_key_clamping;
          Alcotest.test_case "single-shot error normalization" `Quick
            normalized_single_shot_error;
          Alcotest.test_case "adversarial mismatches" `Quick
            adversarial_mismatches;
          Alcotest.test_case "authenticated-mode mismatches" `Quick
            authenticated_mismatches;
        ] );
      ( "ML-KEM",
        [
          Alcotest.test_case "keys" `Quick mlkem_keys;
          Alcotest.test_case "implicit rejection" `Quick
            mlkem_implicit_rejection;
          Alcotest.test_case "no Auth or AuthPSK mode" `Quick
            mlkem_has_no_auth_modes;
        ] );
      ( "PQ/T hybrid KEMs",
        [
          Alcotest.test_case "keys" `Quick hybrid_keys;
          Alcotest.test_case "encapsulations" `Quick hybrid_encapsulations;
          Alcotest.test_case "rejection sampling" `Quick
            hybrid_rejection_sampling;
        ] );
      ( "draft-ietf-hpke-hpke-04",
        [
          Alcotest.test_case "KDF registry" `Quick draft_registry;
          Alcotest.test_case "one-stage round trips" `Quick draft_round_trips;
          Alcotest.test_case "HKDF suites are RFC 9180's" `Quick
            draft_hkdf_is_rfc9180;
          Alcotest.test_case "one-stage limits" `Quick draft_one_stage_limits;
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
          Alcotest.test_case "deterministic Auth and AuthPSK senders" `Quick
            deterministic_authenticated_sender;
        ] );
      ( "properties",
        [
          QCheck_alcotest.to_alcotest ~speed_level:`Quick qcheck_round_trip;
          QCheck_alcotest.to_alcotest ~speed_level:`Quick
            qcheck_peer_input_total;
          QCheck_alcotest.to_alcotest ~speed_level:`Quick
            qcheck_mlkem_peer_input_total;
          QCheck_alcotest.to_alcotest ~speed_level:`Quick
            qcheck_hybrid_peer_input_total;
        ] );
    ]
