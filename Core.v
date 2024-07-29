From LeapSecurity Require Export Environment.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Import ListNotations.

Parameter PWD: password.
Parameter Salt: salt.
Parameter MEK: key.
Parameter MK DK: key_pair.

Definition KEK := Kdf PWD Salt.
Definition KEK_MEK := ESym KEK MEK.
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

Definition MSignEnv t env :=
  SignEnv (pr_with_id DK_with_id) t env.

Definition MVerifyEnv t sig :=
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

Definition EnterPwdEnv env := 
  let idcnt := id_env env in
  let pwd := {| identity := idcnt+1; content := EnterPwd|} in
  (pwd, {|rel_env := rel_env env; leaked_env := leaked_env env; id_env := idcnt+1|}).

Definition FetchPubEnv env :=
  let idcnt := id_env env in
  let pubk := {| identity := idcnt+1; content := FetchPub|} in
  (pubk, {|rel_env := rel_env env; leaked_env := leaked_env env; id_env := idcnt+1|}).

Definition FetchSigEnv env :=
  let idcnt := id_env env in
  let sig := {| identity := idcnt+1; content := FetchSig|} in
  (sig, {|rel_env := rel_env env; leaked_env := leaked_env env; id_env := idcnt+1|}).

Definition FetchNonceEnv env :=
  let idcnt := id_env env in
  let nonce := {| identity := idcnt+1; content := FetchNonce|} in
  (nonce, {|rel_env := rel_env env; leaked_env := leaked_env env; id_env := idcnt+1|}).

Definition Auth PWD_t :=
  let KEK_t := Kdf PWD_t Salt in
  let MEK_t := DSym KEK_t KEK_MEK in
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

Definition AuthEnv PWD_t_with_id env :=
  let rel := rel_env env in
  let idcnt := id_env env in
  let (KEK_t_with_id, env1) := KdfEnv PWD_t_with_id Salt_with_id env in
  let '(MEK_t_with_id, env2) := DSymEnv KEK_t_with_id KEK_MEK_with_id env1 in
  if (beq_text (Hash (content MEK_t_with_id)) (content H_MEK_with_id))
    then (ASome_with_id MEK_t_with_id, env2)
  else (AFail_with_id, env).

Definition Wrap mek k sig n :=
  if (MVerify k sig)
    then let w := {|mek := mek;
                  nonce := n|} in
    WSome (EASym k (Conc w))
    else WFail.

Inductive wrap_with_id_option :=
  | WSome_with_id (e_mek : text_with_id)
  | WFail_with_id.

Definition WSomeEquals wsome_result ctt :=
  match wsome_result with
  | WSome_with_id e_mek => content e_mek = ctt
  | WFail_with_id => False
  end.

Definition WrapEnv mek k sig n env :=
  if (MVerifyEnv k sig)
    then let w := {|mek_with_id := mek; nonce_with_id := n|} in
    let (w_with_id, env1) := ConcEnv w env in
    let (e_mek_with_id, env2) := EAsymEnv k w_with_id env1 in
    (WSome_with_id e_mek_with_id, env2)
  else (WFail_with_id, env).

Definition Unwrap w n:=
  let uw :=
    Splt (DASym (pr DK) w) in
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

Definition UnWrapEnv w n env :=
  let (DASym_with_id, env1) := DAsymEnv (pr_with_id DK_with_id) w env in
  let (uw_with_id, env2) := SpltEnv DASym_with_id env1 in
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

Inductive leap_with_id_option :=
  | LSome_with_id (res : text_with_id)
  | LAuthFail_with_id
  | LWrapFail_with_id
  | LUnwrapFail_with_id.

Definition AnalyzeLeapSecurity_rel
  (HostPipe_t : text_with_id->environment->text_with_id*environment)
  (PCIePipe_t : text_with_id->environment->text_with_id*environment)
  (EnterPwd_t : environment->text_with_id*environment)
  (FetchPub_t: environment->text_with_id*environment)
  (FetchSig_t: environment->text_with_id*environment)
  (FetchNonce_t : environment->text_with_id*environment)
  (Auth_t : text_with_id->environment->auth_with_id_option*environment)
  (Wrap_t : text_with_id->text_with_id->text_with_id->text_with_id->environment->wrap_with_id_option*environment)
  (Unwrap_t : text_with_id->text_with_id->environment->unwrap_with_id_option*environment)
  (env: environment) :=
  let (eout, env1) := EnterPwd_t env in
  let (e2a, env2) := HostPipe_t eout env1 in
  let (aout, env3) := Auth_t e2a env2 in
  match aout with
  | AFail_with_id => (LAuthFail_with_id, env3)
  | ASome_with_id mek_with_id =>
    let (a2w, env4) := HostPipe_t mek_with_id env3 in
    let (pubk_with_id, env5) := FetchPub_t env4 in
    let (p2w, env6) := PCIePipe_t pubk_with_id env5 in
    let (sig_with_id, env7) := FetchSig_t env6 in
    let (s2w, env8) := PCIePipe_t sig_with_id env7 in
    let (nonce_with_id, env9) := FetchNonce_t env8 in
    let (n2w, env10) := PCIePipe_t nonce_with_id env9 in
    let (wout, env11) := Wrap_t a2w pubk_with_id sig_with_id nonce_with_id env10 in
    match wout with
    | WFail_with_id => (LWrapFail_with_id, env11)
    | WSome_with_id w_with_id =>
      let (w2u, env12) := PCIePipe_t w_with_id env11 in
      let (uout, env13) := Unwrap_t w_with_id nonce_with_id env12 in
      match uout with
      | UFail_with_id => (LUnwrapFail_with_id, env13)
      | USome_with_id res_with_id => (LSome_with_id res_with_id, env13)
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

Definition NormalProcess_rel :=
  AnalyzeLeapSecurity_rel
    SafePipe
    UnsafePipe
    EnterPwdEnv
    FetchPubEnv
    FetchSigEnv
    FetchNonceEnv
    AuthEnv
    WrapEnv
    UnWrapEnv.

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