module Aead = Hpke_internal.Aead

(* The longest plaintext is the one whose 32-bit block counter just does not
   wrap: 2^32 - 2 blocks of 16 bytes for AES-GCM, whose counter starts at 2
   (NIST SP 800-38D), and 2^32 - 1 blocks of 64 bytes for ChaCha20-Poly1305,
   whose counter starts at 1 (RFC 8439). mirage-crypto raises beyond these, so a
   longer plaintext must be refused before it gets there. The public functions
   reach this only through a 64 GiB plaintext. *)
let plaintext_limits () =
  let check aead limit =
    let name = Format.asprintf "%a" Aead.pp aead in
    Alcotest.(check bool)
      (name ^ " at the limit") true
      (Aead.plaintext_fits aead limit);
    Alcotest.(check bool)
      (name ^ " one byte over") false
      (Aead.plaintext_fits aead (limit + 1))
  in
  check Aead.Aes_128_gcm (((1 lsl 32) - 2) * 16);
  check Aead.Aes_256_gcm (((1 lsl 32) - 2) * 16);
  check Aead.Chacha20_poly1305 (((1 lsl 32) - 1) * 64)

let () =
  Alcotest.run "hpke internals"
    [
      ("AEAD", [ Alcotest.test_case "plaintext limits" `Quick plaintext_limits ]);
    ]
