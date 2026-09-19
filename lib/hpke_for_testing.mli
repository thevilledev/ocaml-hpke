(** Deterministic RFC 9180 entry points for known-answer testing only.

    RFC 9180 requires the sender's ephemeral key to be fresh and secret for
    every context. The functions here let the caller choose it instead, so that
    published test vectors which fix [skE] can be reproduced byte for byte,
    including those of protocols layered on HPKE such as RFC 9458. Reusing or
    disclosing an ephemeral key breaks the confidentiality of every message
    sealed under it, so this library must not be used by production protocols.
    Use {!Hpke.Rfc9180} instead. *)

val setup_base_sender :
  'capability Hpke.Suite.t ->
  ephemeral:Hpke.Private_key.t ->
  recipient:Hpke.Public_key.t ->
  info:string ->
  ('capability Hpke.Rfc9180.sender_setup, Hpke.Error.t) result
(** [setup_base_sender suite ~ephemeral ~recipient ~info] is
    {!Hpke.Rfc9180.setup_base_sender} with [ephemeral] as [skE] in place of a
    freshly generated key. The encapsulated key is the public key of
    [ephemeral]. Returns {!Hpke.Error.Key_mismatch} unless the suite, the
    ephemeral key, and the recipient key share one KEM. *)

val setup_psk_sender :
  'capability Hpke.Suite.t ->
  ephemeral:Hpke.Private_key.t ->
  recipient:Hpke.Public_key.t ->
  psk:Hpke.Psk.t ->
  info:string ->
  ('capability Hpke.Rfc9180.sender_setup, Hpke.Error.t) result
(** The PSK-mode counterpart of {!setup_base_sender}. *)

val setup_auth_sender :
  'capability Hpke.Suite.t ->
  ephemeral:Hpke.Private_key.t ->
  recipient:Hpke.Public_key.t ->
  sender:Hpke.Private_key.t ->
  info:string ->
  ('capability Hpke.Rfc9180.sender_setup, Hpke.Error.t) result
(** The Auth-mode counterpart of {!setup_base_sender}:
    {!Hpke.Rfc9180.setup_auth_sender} with [ephemeral] as [skE]. [sender] is the
    sender's static key [skS], as there. Returns {!Hpke.Error.Key_mismatch}
    unless the suite and all three keys share one KEM. *)

val setup_auth_psk_sender :
  'capability Hpke.Suite.t ->
  ephemeral:Hpke.Private_key.t ->
  recipient:Hpke.Public_key.t ->
  sender:Hpke.Private_key.t ->
  psk:Hpke.Psk.t ->
  info:string ->
  ('capability Hpke.Rfc9180.sender_setup, Hpke.Error.t) result
(** The AuthPSK-mode counterpart of {!setup_base_sender}. *)
