open Hpke
open Yojson.Safe.Util

let hex_value = function
  | '0' .. '9' as character -> Char.code character - Char.code '0'
  | 'a' .. 'f' as character -> Char.code character - Char.code 'a' + 10
  | 'A' .. 'F' as character -> Char.code character - Char.code 'A' + 10
  | _ -> invalid_arg "invalid hexadecimal digit"

let hex value =
  if String.length value mod 2 <> 0 then invalid_arg "odd hexadecimal string";
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

let ok = function
  | Ok value -> value
  | Error error -> Alcotest.failf "unexpected HPKE error: %a" Error.pp error

let check_hex label expected actual =
  Alcotest.(check string) label expected (to_hex actual)

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

let member_int field vector = vector |> member field |> to_int
let member_string field vector = vector |> member field |> to_string
let member_hex field vector = member_string field vector |> hex
let kem vector = member_int "kem_id" vector |> Kem.of_int |> ok
let kdf vector = member_int "kdf_id" vector |> Kdf.of_int |> ok

let psk vector =
  match member_int "mode" vector with
  | 0 -> None
  | 1 ->
      Some
        (ok
           (Psk.create ~secret:(member_hex "psk" vector)
              ~id:(member_hex "psk_id" vector)))
  | mode -> Alcotest.failf "unsupported test-vector mode %d" mode

let serialized_private_key kem encoded =
  match kem with
  | Kem.X25519 ->
      (* RFC vectors retain the pre-clamping input; the public API serializes
         canonical X25519 private keys after clamping. *)
      Private_key.of_bytes ~kem (hex encoded) |> ok |> Private_key.to_bytes
  | Kem.P256 | Kem.P384 | Kem.P521 -> hex encoded

let prepare_keys vector kem =
  let recipient, recipient_public =
    ok (derive_key_pair kem ~ikm:(member_hex "ikmR" vector))
  in
  Alcotest.(check string)
    "recipient private key"
    (serialized_private_key kem (member_string "skRm" vector))
    (Private_key.to_bytes recipient);
  check_hex "recipient public key"
    (member_string "pkRm" vector)
    (Public_key.to_bytes recipient_public);
  let ephemeral, ephemeral_public =
    ok (derive_key_pair kem ~ikm:(member_hex "ikmE" vector))
  in
  Alcotest.(check string)
    "ephemeral private key"
    (serialized_private_key kem (member_string "skEm" vector))
    (Private_key.to_bytes ephemeral);
  check_hex "ephemeral public key"
    (member_string "pkEm" vector)
    (Public_key.to_bytes ephemeral_public);
  (recipient, recipient_public)

let setup_sender : type capability.
    capability Suite.t ->
    rng:Mirage_crypto_rng.g ->
    recipient:Public_key.t ->
    psk:Psk.t option ->
    info:string ->
    (capability Rfc9180.sender_setup, Error.t) result =
 fun suite ~rng ~recipient ~psk ~info ->
  match psk with
  | None -> Rfc9180.setup_base_sender ~rng suite ~recipient ~info
  | Some psk -> Rfc9180.setup_psk_sender ~rng suite ~recipient ~psk ~info

let setup_receiver : type capability.
    capability Suite.t ->
    recipient:Private_key.t ->
    psk:Psk.t option ->
    encapsulated_key:string ->
    info:string ->
    (capability Rfc9180.Receiver.t, Error.t) result =
 fun suite ~recipient ~psk ~encapsulated_key ~info ->
  match psk with
  | None -> Rfc9180.setup_base_receiver suite ~recipient ~encapsulated_key ~info
  | Some psk ->
      Rfc9180.setup_psk_receiver suite ~recipient ~psk ~encapsulated_key ~info

let check_exports vector sender receiver =
  vector |> member "exports" |> to_list
  |> List.iteri (fun index export ->
      let context = member_hex "exporter_context" export in
      let length = member_int "L" export in
      let expected = member_string "exported_value" export in
      check_hex
        (Format.sprintf "sender export %d" index)
        expected
        (ok (Rfc9180.Sender.export sender ~context ~length));
      check_hex
        (Format.sprintf "receiver export %d" index)
        expected
        (ok (Rfc9180.Receiver.export receiver ~context ~length)))

let test_encryption_vector vector kem kdf aead =
  let suite = Suite.create ~kem ~kdf ~aead in
  let recipient, recipient_public = prepare_keys vector kem in
  let psk = psk vector in
  let info = member_hex "info" vector in
  let sender =
    ok
      (setup_sender suite
         ~rng:(fixed_rng (member_hex "ikmE" vector))
         ~recipient:recipient_public ~psk ~info)
  in
  check_hex "encapsulated key"
    (member_string "enc" vector)
    sender.encapsulated_key;
  let receiver =
    ok
      (setup_receiver suite ~recipient ~psk
         ~encapsulated_key:(member_hex "enc" vector) ~info)
  in
  vector |> member "encryptions" |> to_list
  |> List.iteri (fun index encryption ->
      let aad = member_hex "aad" encryption in
      let plaintext = member_hex "pt" encryption in
      let expected_ciphertext = member_string "ct" encryption in
      check_hex
        (Format.sprintf "sender ciphertext %d" index)
        expected_ciphertext
        (ok (Rfc9180.Sender.seal sender.context ~aad ~plaintext));
      check_hex
        (Format.sprintf "receiver plaintext %d" index)
        (member_string "pt" encryption)
        (ok
           (Rfc9180.Receiver.open_ receiver ~aad
              ~ciphertext:(hex expected_ciphertext))));
  check_exports vector sender.context receiver

let test_export_vector vector kem kdf =
  let suite = Suite.export_only ~kem ~kdf in
  let recipient, recipient_public = prepare_keys vector kem in
  let psk = psk vector in
  let info = member_hex "info" vector in
  let sender =
    ok
      (setup_sender suite
         ~rng:(fixed_rng (member_hex "ikmE" vector))
         ~recipient:recipient_public ~psk ~info)
  in
  check_hex "encapsulated key"
    (member_string "enc" vector)
    sender.encapsulated_key;
  let receiver =
    ok
      (setup_receiver suite ~recipient ~psk
         ~encapsulated_key:(member_hex "enc" vector) ~info)
  in
  check_exports vector sender.context receiver

let test_vector vector =
  let kem = kem vector and kdf = kdf vector in
  match member_int "aead_id" vector with
  | 0xffff -> test_export_vector vector kem kdf
  | identifier ->
      let aead = Aead.of_int identifier |> ok in
      test_encryption_vector vector kem kdf aead

let vector_name vector =
  Format.sprintf "mode-%d-kem-%04x-kdf-%04x-aead-%04x"
    (member_int "mode" vector)
    (member_int "kem_id" vector)
    (member_int "kdf_id" vector)
    (member_int "aead_id" vector)

let () =
  let path = Sys.getenv "HPKE_TEST_VECTORS" in
  let document = Yojson.Safe.from_file path in
  let vectors = document |> member "vectors" |> to_list in
  Alcotest.(check int) "supported vector count" 48 (List.length vectors);
  let tests =
    List.map
      (fun vector ->
        Alcotest.test_case (vector_name vector) `Quick (fun () ->
            test_vector vector))
      vectors
  in
  Alcotest.run "hpke known-answer vectors" [ ("RFC 9180", tests) ]
