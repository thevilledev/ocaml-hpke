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
  | 0 | 2 -> None
  | 1 | 3 ->
      Some
        (ok
           (Psk.create ~secret:(member_hex "psk" vector)
              ~id:(member_hex "psk_id" vector)))
  | mode -> Alcotest.failf "unsupported test-vector mode %d" mode

let serialized_private_key kem encoded =
  match kem with
  | Kem.X25519 | Kem.X448 ->
      (* RFC vectors retain the pre-clamping input; the public API serializes
         canonical X25519 and X448 private keys after clamping. *)
      Private_key.of_bytes ~kem (hex encoded) |> ok |> Private_key.to_bytes
  | Kem.P256 | Kem.P384 | Kem.P521 -> hex encoded

let derive_key_pair_of vector kem ~role ~ikm ~private_key ~public_key =
  let derived_private, derived_public =
    ok (derive_key_pair kem ~ikm:(member_hex ikm vector))
  in
  Alcotest.(check string)
    (role ^ " private key")
    (serialized_private_key kem (member_string private_key vector))
    (Private_key.to_bytes derived_private);
  check_hex (role ^ " public key")
    (member_string public_key vector)
    (Public_key.to_bytes derived_public);
  (derived_private, derived_public)

(* Returns the recipient's key pair, and the sender's static key pair in the
   Auth and AuthPSK modes. *)
let prepare_keys vector kem =
  let recipient =
    derive_key_pair_of vector kem ~role:"recipient" ~ikm:"ikmR"
      ~private_key:"skRm" ~public_key:"pkRm"
  in
  let _ephemeral =
    derive_key_pair_of vector kem ~role:"ephemeral" ~ikm:"ikmE"
      ~private_key:"skEm" ~public_key:"pkEm"
  in
  let sender =
    match member_int "mode" vector with
    | 2 | 3 ->
        Some
          (derive_key_pair_of vector kem ~role:"sender" ~ikm:"ikmS"
             ~private_key:"skSm" ~public_key:"pkSm")
    | _ -> None
  in
  (recipient, sender)

let setup_sender : type capability.
    capability Suite.t ->
    rng:Mirage_crypto_rng.g ->
    recipient:Public_key.t ->
    sender:Private_key.t option ->
    psk:Psk.t option ->
    info:string ->
    (capability Rfc9180.sender_setup, Error.t) result =
 fun suite ~rng ~recipient ~sender ~psk ~info ->
  match (sender, psk) with
  | None, None -> Rfc9180.setup_base_sender ~rng suite ~recipient ~info
  | None, Some psk -> Rfc9180.setup_psk_sender ~rng suite ~recipient ~psk ~info
  | Some sender, None ->
      Rfc9180.setup_auth_sender ~rng suite ~recipient ~sender ~info
  | Some sender, Some psk ->
      Rfc9180.setup_auth_psk_sender ~rng suite ~recipient ~sender ~psk ~info

let setup_receiver : type capability.
    capability Suite.t ->
    recipient:Private_key.t ->
    sender:Public_key.t option ->
    psk:Psk.t option ->
    encapsulated_key:string ->
    info:string ->
    (capability Rfc9180.Receiver.t, Error.t) result =
 fun suite ~recipient ~sender ~psk ~encapsulated_key ~info ->
  match (sender, psk) with
  | None, None ->
      Rfc9180.setup_base_receiver suite ~recipient ~encapsulated_key ~info
  | None, Some psk ->
      Rfc9180.setup_psk_receiver suite ~recipient ~psk ~encapsulated_key ~info
  | Some sender, None ->
      Rfc9180.setup_auth_receiver suite ~recipient ~sender ~encapsulated_key
        ~info
  | Some sender, Some psk ->
      Rfc9180.setup_auth_psk_receiver suite ~recipient ~sender ~psk
        ~encapsulated_key ~info

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
  let (recipient, recipient_public), sender_keys = prepare_keys vector kem in
  let psk = psk vector in
  let info = member_hex "info" vector in
  let sender =
    ok
      (setup_sender suite
         ~rng:(fixed_rng (member_hex "ikmE" vector))
         ~recipient:recipient_public
         ~sender:(Option.map fst sender_keys)
         ~psk ~info)
  in
  check_hex "encapsulated key"
    (member_string "enc" vector)
    sender.encapsulated_key;
  let receiver =
    ok
      (setup_receiver suite ~recipient
         ~sender:(Option.map snd sender_keys)
         ~psk ~encapsulated_key:(member_hex "enc" vector) ~info)
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
  let (recipient, recipient_public), sender_keys = prepare_keys vector kem in
  let psk = psk vector in
  let info = member_hex "info" vector in
  let sender =
    ok
      (setup_sender suite
         ~rng:(fixed_rng (member_hex "ikmE" vector))
         ~recipient:recipient_public
         ~sender:(Option.map fst sender_keys)
         ~psk ~info)
  in
  check_hex "encapsulated key"
    (member_string "enc" vector)
    sender.encapsulated_key;
  let receiver =
    ok
      (setup_receiver suite ~recipient
         ~sender:(Option.map snd sender_keys)
         ~psk ~encapsulated_key:(member_hex "enc" vector) ~info)
  in
  check_exports vector sender.context receiver

let test_vector vector =
  let kem = kem vector and kdf = kdf vector in
  match member_int "aead_id" vector with
  | 0xffff -> test_export_vector vector kem kdf
  | identifier ->
      let aead = Aead.of_int identifier |> ok in
      test_encryption_vector vector kem kdf aead

(* The vectors publish skEm as well as ikmE. Hpke_for_testing takes the
   ephemeral private key itself, so it must reach the same encapsulation,
   ciphertexts, and exports as the fixed-randomness path above. *)
let setup_deterministic_sender : type capability.
    capability Suite.t ->
    ephemeral:Private_key.t ->
    recipient:Public_key.t ->
    sender:Private_key.t option ->
    psk:Psk.t option ->
    info:string ->
    (capability Rfc9180.sender_setup, Error.t) result =
 fun suite ~ephemeral ~recipient ~sender ~psk ~info ->
  match (sender, psk) with
  | None, None ->
      Hpke_for_testing.setup_base_sender suite ~ephemeral ~recipient ~info
  | None, Some psk ->
      Hpke_for_testing.setup_psk_sender suite ~ephemeral ~recipient ~psk ~info
  | Some sender, None ->
      Hpke_for_testing.setup_auth_sender suite ~ephemeral ~recipient ~sender
        ~info
  | Some sender, Some psk ->
      Hpke_for_testing.setup_auth_psk_sender suite ~ephemeral ~recipient ~sender
        ~psk ~info

let check_sender_exports vector sender =
  vector |> member "exports" |> to_list
  |> List.iteri (fun index export ->
      check_hex
        (Format.sprintf "sender export %d" index)
        (member_string "exported_value" export)
        (ok
           (Rfc9180.Sender.export sender
              ~context:(member_hex "exporter_context" export)
              ~length:(member_int "L" export))))

let test_deterministic_sender vector =
  let kem = kem vector and kdf = kdf vector in
  let (_, recipient), sender_keys = prepare_keys vector kem in
  let ephemeral = ok (Private_key.of_bytes ~kem (member_hex "skEm" vector)) in
  (* Like the ephemeral key, the sender's static key is parsed from its
     published serialization. *)
  let sender =
    Option.map
      (fun _ -> ok (Private_key.of_bytes ~kem (member_hex "skSm" vector)))
      sender_keys
  in
  let psk = psk vector in
  let info = member_hex "info" vector in
  match member_int "aead_id" vector with
  | 0xffff ->
      let sender =
        ok
          (setup_deterministic_sender
             (Suite.export_only ~kem ~kdf)
             ~ephemeral ~recipient ~sender ~psk ~info)
      in
      check_hex "encapsulated key"
        (member_string "enc" vector)
        sender.encapsulated_key;
      check_sender_exports vector sender.context
  | identifier ->
      let aead = Aead.of_int identifier |> ok in
      let sender =
        ok
          (setup_deterministic_sender
             (Suite.create ~kem ~kdf ~aead)
             ~ephemeral ~recipient ~sender ~psk ~info)
      in
      check_hex "encapsulated key"
        (member_string "enc" vector)
        sender.encapsulated_key;
      vector |> member "encryptions" |> to_list
      |> List.iteri (fun index encryption ->
          check_hex
            (Format.sprintf "sender ciphertext %d" index)
            (member_string "ct" encryption)
            (ok
               (Rfc9180.Sender.seal sender.context
                  ~aad:(member_hex "aad" encryption)
                  ~plaintext:(member_hex "pt" encryption))));
      check_sender_exports vector sender.context

let i2osp2 value =
  String.init 2 (function
    | 0 -> Char.chr ((value lsr 8) land 0xff)
    | _ -> Char.chr (value land 0xff))

(* RFC 9180 builds its key schedule from LabeledExtract and LabeledExpand, which
   are the unlabeled HKDF functions over a framed input. Rebuilding that framing
   here turns the published intermediates into known answers for the public
   Kdf.extract and Kdf.expand. *)
let test_unlabeled_kdf vector =
  let kdf = kdf vector in
  let aead_id = member_int "aead_id" vector in
  let suite_id =
    "HPKE"
    ^ i2osp2 (member_int "kem_id" vector)
    ^ i2osp2 (Kdf.to_int kdf)
    ^ i2osp2 aead_id
  in
  let psk_secret =
    match psk vector with None -> "" | Some _ -> member_hex "psk" vector
  in
  let secret =
    Kdf.extract kdf
      ~salt:(member_hex "shared_secret" vector)
      ("HPKE-v1" ^ suite_id ^ "secret" ^ psk_secret)
  in
  check_hex "secret" (member_string "secret" vector) secret;
  let labeled_expand label length =
    ok
      (Kdf.expand kdf ~prk:secret
         ~info:
           (i2osp2 length ^ "HPKE-v1" ^ suite_id ^ label
           ^ member_hex "key_schedule_context" vector)
         length)
  in
  check_hex "exporter secret"
    (member_string "exporter_secret" vector)
    (labeled_expand "exp" (Kdf.hash_size kdf));
  if aead_id <> 0xffff then begin
    let aead = Aead.of_int aead_id |> ok in
    check_hex "key"
      (member_string "key" vector)
      (labeled_expand "key" (Aead.key_size aead));
    check_hex "base nonce"
      (member_string "base_nonce" vector)
      (labeled_expand "base_nonce" (Aead.nonce_size aead))
  end

(* Every encryption record carries the nonce it was sealed under, so the
   published key makes each one a known answer for Aead.seal and Aead.open_. *)
let test_single_shot_aead vector =
  let aead = member_int "aead_id" vector |> Aead.of_int |> ok in
  (* Prepared once for the whole sequence, as a layered protocol would. *)
  let key = ok (Aead.key aead (member_hex "key" vector)) in
  vector |> member "encryptions" |> to_list
  |> List.iteri (fun index encryption ->
      let nonce = member_hex "nonce" encryption in
      let aad = member_hex "aad" encryption in
      check_hex
        (Format.sprintf "sealed %d" index)
        (member_string "ct" encryption)
        (ok (Aead.seal key ~nonce ~aad ~plaintext:(member_hex "pt" encryption)));
      check_hex
        (Format.sprintf "opened %d" index)
        (member_string "pt" encryption)
        (ok
           (Aead.open_ key ~nonce ~aad ~ciphertext:(member_hex "ct" encryption))))

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
  Alcotest.(check int) "supported vector count" 128 (List.length vectors);
  let tests_of test vectors =
    List.map
      (fun vector ->
        Alcotest.test_case (vector_name vector) `Quick (fun () -> test vector))
      vectors
  in
  let encryption_vectors =
    List.filter (fun vector -> member_int "aead_id" vector <> 0xffff) vectors
  in
  Alcotest.run "hpke known-answer vectors"
    [
      ("RFC 9180", tests_of test_vector vectors);
      ("deterministic sender", tests_of test_deterministic_sender vectors);
      ("unlabeled KDF", tests_of test_unlabeled_kdf vectors);
      ("single-shot AEAD", tests_of test_single_shot_aead encryption_vectors);
    ]
