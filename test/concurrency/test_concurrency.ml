open Hpke

let ok = function
  | Ok value -> value
  | Error error ->
      failwith (Format.asprintf "unexpected error: %a" Error.pp error)

let rng =
  Mirage_crypto_rng.create ~seed:(String.make 64 '\x71')
    (module Mirage_crypto_rng.Fortuna)

let suite =
  Suite.create ~kem:Kem.X25519 ~kdf:Kdf.Hkdf_sha256 ~aead:Aead.Aes_128_gcm

let recipient, public = ok (generate_key_pair ~rng Kem.X25519)

let contend () =
  let setup =
    ok
      (Rfc9180.setup_base_sender ~rng suite ~recipient:public ~info:"concurrent")
  in
  let start = Atomic.make false in
  let message = String.make (4 * 1024 * 1024) '\x5a' in
  let operation aad () =
    while not (Atomic.get start) do
      Domain.cpu_relax ()
    done;
    Rfc9180.Sender.seal setup.context ~aad ~plaintext:message
  in
  let left = Domain.spawn (operation "left") in
  let right = Domain.spawn (operation "right") in
  Atomic.set start true;
  let left = Domain.join left and right = Domain.join right in
  match (left, right) with
  | Ok ciphertext, Error Error.Concurrent_use -> Some (setup, "left", ciphertext)
  | Error Error.Concurrent_use, Ok ciphertext ->
      Some (setup, "right", ciphertext)
  | Ok _, Ok _ -> None
  | Error error, _ | _, Error error ->
      failwith
        (Format.asprintf "unexpected contention result: %a" Error.pp error)

let rec find_overlap attempts =
  if attempts = 0 then failwith "could not schedule overlapping context calls"
  else
    match contend () with
    | Some result -> result
    | None -> find_overlap (attempts - 1)

let () =
  let setup, aad, ciphertext = find_overlap 20 in
  let receiver =
    ok
      (Rfc9180.setup_base_receiver suite ~recipient
         ~encapsulated_key:setup.encapsulated_key ~info:"concurrent")
  in
  let opened = ok (Rfc9180.Receiver.open_ receiver ~aad ~ciphertext) in
  if String.length opened <> 4 * 1024 * 1024 then
    failwith "concurrent winner produced the wrong plaintext"
