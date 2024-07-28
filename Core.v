From LeapSecurity Require Export Environment.
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

Definition ID_BASE := 100.
Definition ENV_BASE := {|rel_env := []; leaked_env := []; id_env := ID_BASE|}.

Definition PWD_with_id := {| identity := 1; content := PWD|}.
Definition Salt_with_id := {| identity := 2; content := Salt|}.
Definition MEK_with_id := {| identity := 3; content := MEK|}.
Definition KEK_with_id := {| identity := 4; content := KEK|}.
Definition KEK_MEK_with_id := {| identity := 5; content := KEK_MEK|}.
Definition H_MEK_with_id := {| identity := 6; content := H_MEK|}.
Definition MK_with_id := {|
  pub_with_id := {| identity := 7; content := pub MK|};
  pr_with_id := {| identity := 8; content := pr MK|}|}.
Definition DK_with_id := {|
  pub_with_id := {| identity := 9; content := pub DK|};
  pr_with_id := {| identity := 10; content := pr DK|}|}.

Definition MSign t := Sign (pr MK) t.
Definition MVerify t sig :=
  Verify (pub MK) t sig.
Definition SIG := MSign (pub DK).

Definition MSign_rel t env :=
  Sign_rel (pr_with_id DK_with_id) t env.

Definition MVerify_rel t sig :=
  Verify (content (pub_with_id MK_with_id)) (content t) (content sig).

Definition Pipe t (trusted:bool) :=
  if trusted 
    then {|data := t;
           leaked := {} |}
    else {|data := t;
           leaked := {t} |}.

Definition SafePipe (t: text_with_id) (env: environment) := (t, env).
Definition UnsafePipe (t: text_with_id) (env: environment) := (t, add_leaked t env).

Parameter EnterPwd: password.
Parameter FetchPub: key.
Parameter FetchSig: text.
Parameter FetchNonce: nat.

Definition EnterPwd_ref env := 
  let idcnt := id_env env in
  let pwd := {| identity := idcnt+1; content := EnterPwd|} in
  (pwd, {|rel_env := rel_env env; leaked_env := leaked_env env; id_env := idcnt+1|}).

Definition FetchPub_ref env :=
  let idcnt := id_env env in
  let pubk := {| identity := idcnt+1; content := FetchPub|} in
  (pubk, {|rel_env := rel_env env; leaked_env := leaked_env env; id_env := idcnt+1|}).

Definition FetchSig_ref env :=
  let idcnt := id_env env in
  let sig := {| identity := idcnt+1; content := FetchSig|} in
  (sig, {|rel_env := rel_env env; leaked_env := leaked_env env; id_env := idcnt+1|}).

Definition FetchNonce_ref env :=
  let idcnt := id_env env in
  let nonce := {| identity := idcnt+1; content := FetchNonce|} in
  (nonce, {|rel_env := rel_env env; leaked_env := leaked_env env; id_env := idcnt+1|}).

Definition Auth PWD_t :=
  let KEK_t := Kdf PWD_t Salt in
  let MEK_t := D_Sym KEK_t KEK_MEK in
  if (beq_text (Hash MEK_t) H_MEK)
    then ASome MEK_t else AFail.

Inductive auth_with_id_option :=
  | ASome_with_id (mek : text_with_id)
  | AFail_with_id.

Definition ASomeEquals asome_result ctt :=
  match asome_result with
  | ASome_with_id mek => content mek = ctt
  | AFail_with_id => False
  end.

Definition Auth_rel PWD_t_with_id env :=
  let rel := rel_env env in
  let idcnt := id_env env in
  let (KEK_t_with_id, env1) := Kdf_rel PWD_t_with_id Salt_with_id env in
  let '(MEK_t_with_id, env2) := D_Sym_rel KEK_t_with_id KEK_MEK_with_id env1 in
  if (beq_text (Hash (content MEK_t_with_id)) (content H_MEK_with_id))
    then (ASome_with_id MEK_t_with_id, env2)
  else (AFail_with_id, env).

Definition Wrap mek k sig n :=
  if (MVerify k sig)
    then let w := {|mek := mek;
                  nonce := n|} in
    WSome (E_Asym k (Conc w))
    else WFail.

Inductive wrap_with_id_option :=
  | WSome_with_id (e_mek : text_with_id)
  | WFail_with_id.

Definition WSomeEquals wsome_result ctt :=
  match wsome_result with
  | WSome_with_id e_mek => content e_mek = ctt
  | WFail_with_id => False
  end.

Definition Wrap_rel mek k sig n env :=
  if (MVerify_rel k sig)
    then let w := {|mek_with_id := mek; nonce_with_id := n|} in
    let (w_with_id, env1) := Conc_rel w env in
    let (e_mek_with_id, env2) := E_Asym_rel k w_with_id env1 in
    (WSome_with_id e_mek_with_id, env2)
  else (WFail_with_id, env).

Definition Unwrap w n:=
  let uw :=
    Splt (D_Asym (pr DK) w) in
  if (beq_text (nonce uw) n)
    then USome (mek uw)
    else UFail.

Inductive unwrap_with_id_option :=
  | USome_with_id (mek : text_with_id)
  | UFail_with_id.

Definition USomeEquals usome_result ctt :=
  match usome_result with
  | USome_with_id mek => content mek = ctt
  | UFail_with_id => False
  end.

Definition Unwrap_rel w n env :=
  let (d_asym_with_id, env1) := D_Asym_rel (pr_with_id DK_with_id) w env in
  let (uw_with_id, env2) := Splt_rel d_asym_with_id env1 in
  if (beq_text (content (nonce_with_id uw_with_id)) (content n))
    then (USome_with_id (mek_with_id uw_with_id), env2)
  else (UFail_with_id, env).

Definition AnalyzeLeapSecurity
  (Pipe_t : text->bool->pipeout)
  (EnterPwd_t : password)
  (FetchPub_t: key)
  (FetchSig_t: text)
  (FetchNonce_t : nat)
  (Auth_t : password->auth_option)
  (Wrap_t : text->key->text->nat->wrap_option)
  (Unwrap_t : text->nat->unwrap_option) :=
  let eout := EnterPwd_t in
  let etoa := Pipe_t eout true in
  let unsafe1 := leaked etoa in
  let aout := Auth_t (data etoa) in
  match aout with
  | AFail => LAuthFail unsafe1
  | ASome mek =>
    let atow := Pipe_t mek true in
    let pubk := FetchPub_t in
    let ptow := Pipe_t pubk false in
    let sig := FetchSig_t in
    let stow := Pipe_t sig false in
    let nonce := FetchNonce_t in
    let ntow := Pipe_t nonce false in
    let unsafe2 :=
         unsafe1 ∪ (leaked atow) ∪ (leaked ptow) ∪
            (leaked stow) ∪ (leaked ntow) in
    let wout := Wrap_t (data atow) pubk sig nonce in
    match wout with
    | WFail => LWrapFail unsafe2
    | WSome w =>
      let wtou := Pipe_t w false in
      let unsafe3 := unsafe2 ∪ (leaked wtou) in
      let uout := Unwrap_t (data wtou) nonce in
      match uout with
      | UFail => LUnwrapFail unsafe3
      | USome res =>
        let result := {|final := res;
                     unsafe := unsafe3|} in
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
    FetchNonce
    Auth
    Wrap
    Unwrap.

Definition FakePubSig FakePub FakeSig :=
  AnalyzeLeapSecurity 
    Pipe
    EnterPwd
    FakePub
    FakeSig
    FetchNonce
    Auth
    Wrap
    Unwrap.

(* Definition FakePubSig
    Any_Pipe
    Any_EnterPwd
    Fake_Pub
    Fake_Sig
    Any_Nonce
    Any_Auth
    Any_Wrap
    Any_Unwrap :=
  AnalyzeLeapSecurity 
    Any_Pipe
    Any_EnterPwd
    Fake_Pub
    Fake_Sig
    Any_Nonce
    Any_Auth
    Any_Wrap
    Any_Unwrap. *)