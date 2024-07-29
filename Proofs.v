From LeapSecurity Require Export Core.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Lists.List.
Import ListNotations.
Import ListEnsemble.

Lemma unrelatedSafe: forall uset t,
  Finite text uset -> UnrelatedSet uset t ->
  Safe uset t.
Proof.
  intros ll t l.
  induction l as [| l' l'f H m H0].
  - intro H1.
    apply nilSafe.
  - intro H1.
    apply incSafe.
    split.
    apply H.
    intros h H2.
    specialize (H1 h).
    specialize (Add_intro1 text l' m h) as H3.
    auto.
    specialize (H1 m).
    specialize (Add_intro2 text l' m) as H4.
    auto.
Qed.

Lemma unionTwoUnrelatedSafe:
  forall s1 s2 t, Finite text s1 ->
  Finite text s2 ->
  UnrelatedSet s1 t /\ UnrelatedSet s2 t ->
  Safe (s1 ∪ s2) t.
Proof.
  intros ll1 ll2 t l1 l2 H.
  apply unrelatedSafe.
  now apply Union_preserves_Finite.
  intros h H3.
  destruct H as [H1 H2].
  specialize (H1 h).
  specialize (H2 h).
  specialize (Union_inv text ll1 ll2 h) as H4.
  now elim H4.
Qed.

Lemma unionUnrelatedSafe:
  forall s s' t, Finite text s ->
  Finite text s' -> UnrelatedSet s' t ->
  Safe s t ->
  Safe (s ∪ s') t.
Proof.
  intros ll1 ll2 t l1 l2 H H0.
  induction l2 as [| l' l'f H1 m H2].
  - specialize (Empty_set_zero text ll1) as H1.
    specialize (Union_commutative text (Empty_set text) ll1) as H2.
    rewrite H2 in H1.
    rewrite H1.
    trivial.
  - specialize (Union_add text ll1 l' m) as H3.
    rewrite <- H3.
    apply incSafe.
    split.
    apply H1.
    assert (H4: UnrelatedSet (m :: l') t -> UnrelatedSet l' t).
    {
      unfold UnrelatedSet.
      intros A h.
      specialize (Add_intro1 text l' m h) as B.
      auto.
    }
    auto.
    assert (H5: UnrelatedSet (m :: l') t -> t ≁ m).
    {
      unfold UnrelatedSet.
      intros C.
      specialize (C m) as D.
      specialize (Add_intro2 text l' m) as E.
      auto.
    }
    auto.
Qed.

(*
  A correct password is able to unlock the MEK
*)
Lemma correctAuth: Auth PWD = ASome MEK.
Proof.
  unfold Auth.
  fold KEK.
  assert (H1: DSym KEK KEK_MEK = MEK).
  {
    unfold KEK_MEK.
    now rewrite symEnDe.
  }
  rewrite H1.
  assert (H2: beq_text (Hash MEK) H_MEK = true).
  {
    fold H_MEK.
    now rewrite Nat.eqb_eq.
  }
  now rewrite H2.
Qed.

Lemma beq_id: forall x, x =? x = true.
Proof.
  intro x.
  induction x as [| n IH].
  - simpl. reflexivity.
  - simpl. apply IH.
Qed.

Lemma ignore_cond :
  forall cond:bool, (if cond then true else true) = true.
Proof.
  intros.
  destruct cond; reflexivity.
Qed.

Lemma correctAuthEnv: forall res env,
  (res, env) = AuthEnv PWD_with_id ENV_BASE ->
  ASomeEquals res MEK /\
  (list_eq_relation (get_root_leaf_pairs (rel_env env))
  [pair PWD_with_id MEK_with_id; pair Salt_with_id MEK_with_id; pair KEK_MEK_with_id MEK_with_id]) = true.
Proof.
  intros res env.
  unfold AuthEnv, KdfEnv, DSymEnv. simpl.
  fold KEK.
  assert (H1: DSym KEK KEK_MEK = MEK).
  {
    unfold KEK_MEK.
    now rewrite symEnDe.
  }
  rewrite H1.
  assert (H2: beq_text (Hash MEK) H_MEK = true).
  {
    fold H_MEK.
    now rewrite Nat.eqb_eq.
  }
  rewrite H2.
  intro H3.
  inversion H3.
  split.
  unfold ASomeEquals.
  auto.
  unfold get_root_leaf_pairs.
  unfold list_eq_relation.
  simpl.
  unfold beq_text_content.
  simpl.
  specialize (beq_id PWD) as H_PWD.
  specialize (beq_id MEK) as H_MEK.
  specialize (beq_id Salt) as H_Salt.
  specialize (beq_id KEK_MEK) as H_KEK_MEK.
  rewrite H_PWD, H_MEK, H_Salt, H_KEK_MEK. simpl.
  specialize (ignore_cond ((Salt =? PWD) && true)) as H_Salt_PWD.
  rewrite H_Salt_PWD.
  specialize (ignore_cond ((KEK_MEK =? Salt) && true)) as H_KEKMEK_Salt.
  rewrite H_KEKMEK_Salt.
  specialize (ignore_cond ((KEK_MEK =? PWD) && true)) as H_KEKMEK_PWD.
  rewrite H_KEKMEK_PWD.
  auto.
Qed.

(*
  Only correct password can get something from Auth, except cracked cases
*)
Lemma getSomethingFromAuth: forall p k,
  Auth p = ASome k -> p = PWD \/ CrackHash.
Proof.
  intros p k H1.
  assert (H2: Hash (DSym (Kdf p Salt) KEK_MEK) = H_MEK).
  {
    unfold Auth in H1.
    case_eq (beq_text (Hash (DSym (Kdf p Salt) KEK_MEK)) H_MEK).
    - intro HP.
      rewrite Nat.eqb_eq in HP.
      auto.
    - intro HP.
      rewrite HP in H1.
      inversion H1.
  }
  clear H1.
  unfold H_MEK in H2.
  apply conflictHash in H2.
  inversion H2 as [H3 | H4].
  - assert (H5: KEK_MEK = ESym (Kdf p Salt) MEK).
    {
      rewrite <- H3.
      specialize (symDeEn (Kdf p Salt) KEK_MEK) as H6.
      auto.
    }
    unfold KEK_MEK in H5.
    apply bijectiveSym in H5.
    unfold KEK in H5.
    destruct (Nat.eq_dec p PWD) as [Heq | Hneq].
    auto.
    specialize (injectiveKdf p PWD Salt) as H6.
    rewrite H5 in H6.
    apply H6 in Hneq.
    contradiction.
  - auto.
Qed.

Lemma crackAuth: forall p,
  p <> PWD /\ Auth p = ASome MEK -> CrackHash.
Proof.
  intros p H1.
  destruct H1 as [H2 H3].
  apply getSomethingFromAuth in H3.
  now destruct H3 as [H4 | H5].
Qed.

(*
  Auth only returns MEK or fails, except cracked cases
*)
Lemma anyAuth: forall p,
  Auth p = ASome MEK \/ Auth p = AFail \/ CrackHash.
Proof.
  intro p.
  case_eq (Auth p).
  - intros k H1.
    apply NNPP.
    intro H2.
    apply not_or_and in H2.
    destruct H2 as [H3 H4].
    apply not_or_and in H4.
    destruct H4 as [H5 H6].
    assert (H7: k <> MEK).
    {
      auto.
    }
    clear H3 H5.
    case_eq (beq_text p PWD).
    * intro HA.
      rewrite Nat.eqb_eq in HA.
      rewrite HA in H1.
      rewrite correctAuth in H1.
      inversion H1 as [HB].
      apply H7.
      auto.
    * intro HA.
      rewrite Nat.eqb_neq in HA.
      apply getSomethingFromAuth in H1.
      now destruct H1 as [HB | HC].
  - auto.
Qed.

(*
  A correct k+sig is able to retrieve the wrapped MEK
*)
Lemma correctWrap:
  forall mek k sig n,
  sig = MSign k ->
  Wrap mek k sig n =
    WSome (EASym k
          (Conc {|mek := mek;
                  nonce := n|})).
Proof.
  intros mek k sig n H1.
  unfold Wrap.
  assert (H2: MVerify k sig = true).
  {
    rewrite H1.
    apply signCorrect.
    auto.
  }
  now rewrite H2.
Qed.

Lemma correctWrapEnv: forall mek k sig n res env,
  (content sig) = MSign (content k) ->
  (res, env) = WrapEnv mek k sig n ENV_BASE ->
  WSomeEquals res (EASym (content k) (Conc {|mek := content mek; nonce := content n|})).
Proof.
  intros mek k sig n res env H1.
  unfold WrapEnv.
  simpl.
  assert (H2: MVerifyEnv k sig = true).
  {
    unfold MVerifyEnv.
    rewrite H1.
    apply signCorrect.
    auto.
  }
  rewrite H2.
  intro H3.
  inversion H3.
  unfold WSomeEquals.
  simpl.
  auto.
Qed.

(* 
  Only verified k+sig leads to WSome w, except rare cases
*)
Lemma someWrap: forall mek k sig n w,
  Wrap mek k sig n = WSome w ->
  sig = MSign k \/ CrackSignature.
Proof.
  intros mek k sign n w.
  unfold Wrap.
  case_eq (MVerify k sign).
  - intros H1 H2.
    apply signCorrect.
    auto.
  - intros H1 H2.
    inversion H2.
Qed.

Lemma correctUnwrap:
  forall w n,
  nonce w = n ->
  Unwrap (EASym (pub DK) (Conc w)) n = USome (mek w).
Proof.
  intros w n H1.
  unfold Unwrap.
  specialize (asymEnDe DK (Conc w)) as H2.
  specialize (serialCorrect w) as H3.
  assert (H4: nonce (Splt (DASym (pr DK) (EASym (pub DK) (Conc w)))) = n).
  {
    rewrite H2.
    rewrite <- H3.
    auto.
  }
  rewrite H4.
  rewrite Nat.eqb_refl.
  rewrite H2.
  rewrite <- H3.
  auto.
Qed.

Lemma correctUnwrapEnv: forall w n res env,
  content (nonce_with_id w) = content n ->
  let (res1, env1) := ConcEnv w env in
  let (res2, env2) := EAsymEnv (pub_with_id DK_with_id) res1 env1 in
  (res, env) = UnWrapEnv res2 n ENV_BASE ->
  USomeEquals res (content (mek_with_id w)).
Proof.
  intros w n res env.
  unfold UnWrapEnv.
  simpl.
  specialize (asymEnDe DK (Conc {| mek := content (mek_with_id w); nonce := content (nonce_with_id w) |})) as H2.
  rewrite H2.
  specialize (serialCorrect {| mek := content (mek_with_id w); nonce := content (nonce_with_id w) |}) as H3.
  rewrite <- H3.
  intro H4. rewrite H4.
  simpl.
  unfold beq_text.
  specialize (beq_id (content n)) as H5.
  rewrite H5.
  intro H6.
  inversion H6.
  unfold USomeEquals.
  simpl.
  auto.
Qed.

Theorem correctLeapSecurity:
  let w := EASym (pub DK) (
           Conc {|mek := MEK;
                  nonce := FetchNonce|})
  in EnterPwd = PWD ->
     FetchPub = pub DK ->
     FetchSig = SIG ->
  NormalProcess =
    LSome {|final := MEK;
            unsafe := 
             {w; FetchNonce; SIG; pub DK}|}.
Proof.
  intros w H1 H2 H3.
  unfold NormalProcess.
  rewrite H1.
  rewrite H2.
  rewrite H3.
  unfold AnalyzeLeapSecurity.
  unfold Pipe.
  unfold w.
  simpl.
  rewrite correctAuth.
  rewrite correctWrap.
  rewrite correctUnwrap.
  f_equal.
  f_equal.
  rewrite ?Empty_set_zero.
  rewrite ?Empty_set_zero'.
  unfold Ensembles.Add.
  auto 11 with sets.
  trivial.
  trivial.
Qed.

(*
  TODO: Analyze how much infomation an attacker can get
Theorem anyFakePubSig: forall fp fs,
  fs <> MSign fp ->
  EnterPwd = PWD ->
  FakePubSig fp fs = LWrapFail \/ CrackSignature.
Proof.
  intros fp fs H1 H2.
  unfold FakePubSig.
  rewrite H2.
  unfold AnalyzeLeapSecurity.
  unfold Pipe.
  simpl.
  rewrite correctAuth.
  unfold Wrap.
  case_eq (MVerify fp fs).
  - intro H3.
    unfold MVerify in H3.
    rewrite <- signCorrect in H3.
    destruct H3.
    contradiction.
    auto.
  - auto.
Qed.
*)
