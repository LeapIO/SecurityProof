From LeapSecurity Require Export Definitions.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Import ListNotations.

Parameter PWD: password.
Parameter Salt: salt.
Parameter MEK: key.
Parameter MK DK: key_pair.

Definition KEK := Kdf PWD Salt.
Definition KEK_MEK := E_Sym KEK MEK.
Definition H_MEK := Hash MEK.

Definition MSign t := Sign (pr MK) t.
Definition MVerify t sig :=
  Verify (pub MK) t sig.
Definition SIG := MSign (pub DK).

Definition Pipe t (trusted:bool) :=
  if trusted 
    then {|data := t;
           leaked := (as_set [])|}
    else {|data := t;
           leaked := (as_set [t])|}.

Parameter EnterPwd: password.
Parameter FetchPub: key.
Parameter FetchSig: text.
Parameter GenNonce: nat.

Definition Auth PWD_t :=
  let KEK_t := Kdf PWD_t Salt in
  let MEK_t := D_Sym KEK_t KEK_MEK in
  if (beq_text (Hash MEK_t) H_MEK)
    then ASome MEK_t else AFail.

Definition Wrap mek k sig n :=
  if (MVerify k sig)
    then let w := {|mek := mek;
                  nonce := n|} in
    WSome (E_Asym k (Conc w))
    else WFail.

Definition Unwrap w n:=
  let uw :=
    Splt (D_Asym (pr DK) w) in
  if (beq_text (nonce uw) n)
    then USome (mek uw)
    else UFail.

Definition AnalyzeLeapSecurity
  (Pipe_t : text->bool->pipeout)
  (EnterPwd_t : password)
  (FetchPub_t: key)
  (FetchSig_t: text)
  (GenNonce_t : nat)
  (Auth_t : password->auth_option)
  (Wrap_t : text->key->text->nat->wrap_option)
  (Unwrap_t : text->nat->unwrap_option) :=
  let eout := EnterPwd_t in
  let etoa := Pipe_t eout true in
  let aout := Auth_t (data etoa) in
  match aout with
  | AFail => LFail
  | ASome mek =>
    let atow := Pipe_t mek true in
    let pubk := FetchPub_t in
    let ptow := Pipe_t pubk false in
    let sig := FetchSig_t in
    let stow := Pipe_t sig false in
    let nonce := GenNonce_t in
    let ntow := Pipe_t nonce false in
    let wout := Wrap_t (data atow) pubk sig nonce in
    match wout with
    | WFail => LFail
    | WSome w =>
      let wtou := Pipe_t w false in
      let uout := Unwrap_t (data wtou) nonce in
      match uout with
      | UFail => LFail
      | USome res =>
        let unsafe :=
          Union text (leaked etoa)
          (Union text (leaked atow)
           (Union text (leaked ptow)
            (Union text (leaked stow)
             (Union text (leaked ntow)
                          (leaked wtou))))) in
        let result := {|final := res;
                     unsafe := unsafe|} in
        LSome result
      end
    end
  end.

Definition NormalProcess :=
  AnalyzeLeapSecurity 
    Pipe
    EnterPwd
    FetchPub
    FetchSig
    GenNonce
    Auth
    Wrap
    Unwrap.