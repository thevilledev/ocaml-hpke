(* Seals while a timer's signal handler raises. OCaml runs the handler at a poll
   point, and incrementing the sequence number byte by byte from the last byte,
   with a poll between stores, let the exception stop a carry halfway and leave
   a number already used. The sequence must never go back: under one context, a
   repeated ciphertext of the empty plaintext is a repeated nonce.

   The handler raises only while Sender.seal runs. The test stops after a fixed
   number of interrupted seals, which catches the old increment within a few
   thousand of them, or after a time limit where the timer fires too slowly to
   reach that number. *)

open Hpke

exception Interrupt

let ok = function
  | Ok value -> value
  | Error error ->
      failwith (Format.asprintf "unexpected error: %a" Error.pp error)

let rng =
  Mirage_crypto_rng.create ~seed:(String.make 64 '\x73')
    (module Mirage_crypto_rng.Fortuna)

let suite =
  Suite.create ~kem:Kem.X25519 ~kdf:Kdf.Hkdf_sha256 ~aead:Aead.Aes_128_gcm

let _, public = ok (generate_key_pair ~rng Kem.X25519)

let fresh () =
  (ok (Rfc9180.setup_base_sender ~rng suite ~recipient:public ~info:"signals"))
    .context

let timer interval =
  ignore
    (Unix.setitimer Unix.ITIMER_REAL
       { Unix.it_interval = interval; it_value = interval })

(* Each context carries 2^16 + 1 messages, past a two-byte carry, and its
   ciphertexts are kept to find a repeat. *)
let per_context = 65537
let interruptions = 20_000
let time_limit = 20.0

let () =
  if Sys.os_type = "Unix" then begin
    let armed = ref false in
    Sys.set_signal Sys.sigalrm
      (Sys.Signal_handle (fun _ -> if !armed then raise Interrupt));
    let deadline = Unix.gettimeofday () +. time_limit in
    let context = ref (fresh ()) in
    let seen = Hashtbl.create per_context in
    let sealed = ref 0 and interrupted = ref 0 in
    let restart () =
      context := fresh ();
      Hashtbl.reset seen;
      sealed := 0
    in
    timer 0.00005;
    while !interrupted < interruptions && Unix.gettimeofday () < deadline do
      let result =
        try
          armed := true;
          let result = Rfc9180.Sender.seal !context ~aad:"" ~plaintext:"" in
          armed := false;
          Some result
        with Interrupt ->
          armed := false;
          None
      in
      match result with
      | None -> incr interrupted
      | Some (Ok ciphertext) ->
          if Hashtbl.mem seen ciphertext then begin
            timer 0.;
            failwith "an interrupted seal made the context reuse a nonce"
          end;
          Hashtbl.replace seen ciphertext ();
          incr sealed;
          if !sealed = per_context then restart ()
      (* An interrupted call can also leave a context busy for good, which is
         not what this checks. *)
      | Some (Error Error.Concurrent_use) -> restart ()
      | Some (Error error) ->
          timer 0.;
          failwith (Format.asprintf "unexpected error: %a" Error.pp error)
    done;
    timer 0.;
    Sys.set_signal Sys.sigalrm Sys.Signal_default;
    if !interrupted = 0 then failwith "the timer never interrupted a seal"
  end
