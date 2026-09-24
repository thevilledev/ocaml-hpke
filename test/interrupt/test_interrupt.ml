(* Seals while a timer's signal handler raises. OCaml runs the handler at a poll
   point, which an allocation is. An exception between setting a context's busy
   flag and installing the handler that clears it would leave the flag set for
   good, and every later call would fail with Concurrent_use. With one domain,
   no call may ever return Concurrent_use.

   The handler raises only while Sender.seal runs, until a fixed number of seals
   have been interrupted or a time limit passes. *)

open Hpke

exception Interrupt

let ok = function
  | Ok value -> value
  | Error error ->
      failwith (Format.asprintf "unexpected error: %a" Error.pp error)

let rng =
  Mirage_crypto_rng.create ~seed:(String.make 64 '\x62')
    (module Mirage_crypto_rng.Fortuna)

let suite =
  Suite.create ~kem:Kem.X25519 ~kdf:Kdf.Hkdf_sha256 ~aead:Aead.Aes_128_gcm

let _, public = ok (generate_key_pair ~rng Kem.X25519)
let interruptions = 5_000
let time_limit = 20.0

let timer interval =
  ignore
    (Unix.setitimer Unix.ITIMER_REAL
       { Unix.it_interval = interval; it_value = interval })

let () =
  if Sys.os_type = "Unix" then begin
    let context =
      (ok
         (Rfc9180.setup_base_sender ~rng suite ~recipient:public
            ~info:"interrupt"))
        .context
    in
    let armed = ref false in
    Sys.set_signal Sys.sigalrm
      (Sys.Signal_handle (fun _ -> if !armed then raise Interrupt));
    let deadline = Unix.gettimeofday () +. time_limit in
    let interrupted = ref 0 in
    timer 0.00005;
    while !interrupted < interruptions && Unix.gettimeofday () < deadline do
      let result =
        try
          armed := true;
          let result = Rfc9180.Sender.seal context ~aad:"" ~plaintext:"" in
          armed := false;
          Some result
        with Interrupt ->
          armed := false;
          None
      in
      match result with
      | None -> incr interrupted
      | Some (Ok _) -> ()
      | Some (Error error) ->
          timer 0.;
          failwith
            (Format.asprintf "an interrupted seal left: %a" Error.pp error)
    done;
    timer 0.;
    Sys.set_signal Sys.sigalrm Sys.Signal_default;
    if !interrupted = 0 then failwith "the timer never interrupted a seal"
  end
