From LeapSecurity Require Export Core.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Powerset_facts.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.PeanoNat.
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
    unfold in_set in *.
    auto.
    specialize (H1 m).
    specialize (Add_intro2 text l' m) as H4.
    auto.
Qed.

Lemma unionTwoUnrelatedSafe:
  forall s1 s2 t, Finite text s1 ->
  Finite text s2 ->
  UnrelatedSet s1 t /\ UnrelatedSet s2 t ->
  Safe (Union text s1 s2) t.
Proof.
  intros ll1 ll2 t l1 l2 H.
  apply unrelatedSafe.
  apply Union_preserves_Finite.
  auto. auto.
  intros h H3.
  destruct H as [H1 H2].
  specialize (H1 h).
  specialize (H2 h).
  specialize (Union_inv text ll1 ll2 h) as H4.
  elim H4.
  auto. auto. auto.
Qed.

Lemma unionUnrelatedSafe:
  forall s s' t, Finite text s ->
  Finite text s' -> UnrelatedSet s' t ->
  Safe s t ->
  Safe (Union text s s') t.
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
    assert (H4: UnrelatedSet (add_set text l' m) t -> UnrelatedSet l' t).
    {
      unfold UnrelatedSet.
      intros A h.
      specialize (Add_intro1 text l' m h) as B.
      unfold in_set in *.
      auto.
    }
    auto.
    assert (H5: UnrelatedSet (add_set text l' m) t -> ~ TextRelated t m).
    {
      unfold UnrelatedSet.
      intros C.
      specialize (C m) as D.
      specialize (Add_intro2 text l' m) as E.
      auto.
    }
    auto.
Qed.

Lemma onewayHash: forall t,
  Safe (as_set [Hash t]) t.
Proof.
  intro t.
  apply rareConflictHash.
  trivial.
Qed.

(*
  A correct password is able to unlock the MEK
*)
Lemma correctAuth: Auth PWD = ASome MEK.
Proof.
  unfold Auth.
  fold KEK.
  assert (H1: D_Sym KEK KEK_MEK = MEK).
  {
    unfold KEK_MEK.
    rewrite symEnDe.
    reflexivity.
  }
  rewrite H1.
  assert (H2: beq_text (Hash MEK) H_MEK = true).
  {
    fold H_MEK.
    trivial.
    rewrite Nat.eqb_eq.
    reflexivity.
  }
  rewrite H2.
  reflexivity.
Qed.

(*
  Only correct password leads to ASome MEK, except rare cases
*)
Lemma someAuth: forall p,
  Auth p = ASome MEK -> p = PWD \/ Rare p.
Proof.
  intros p H1.
  apply NNPP.
  intro H2.
  apply not_or_and in H2.
  destruct H2 as [H3 H4].
  unfold Auth in H1.
  assert (H5: Hash (D_Sym (Kdf p Salt) KEK_MEK) = H_MEK).
  {
    case_eq (beq_text (Hash (D_Sym (Kdf p Salt) KEK_MEK)) H_MEK).
    - intro HP.
      rewrite Nat.eqb_eq in HP.
      auto.
    - intro HP.
      rewrite HP in H1.
      inversion H1.
  }
  clear H1.
  unfold H_MEK in H5.
  specialize (rareConflictHash MEK (D_Sym (Kdf p Salt) KEK_MEK)) as H6.
  assert (H7: Rare (D_Sym (Kdf p Salt) KEK_MEK)).
  {
    assert (H8: Rare (D_Sym (Kdf p Salt) KEK_MEK) /\
      Safe (as_set [Hash MEK]) (D_Sym (Kdf p Salt) KEK_MEK) ).
    {
      auto.
    }
    apply proj1 in H8.
    auto.
  }
  clear H5 H6.
  specialize (invRare (fun x => D_Sym x KEK_MEK) (Kdf p Salt)) as H9.
  specialize (invRare (fun x => Kdf x Salt) p) as H10.
  assert (H11: Rare p).
  {
    auto.
  }
  contradiction.
Qed.

(*
  Auth only returns MEK or fails, except rare cases
*)
Lemma anyAuth: forall p,
  Auth p = ASome MEK \/ Auth p = AFail \/ Rare p.
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
      unfold Auth in H1.
      assert (HB: Hash (D_Sym (Kdf p Salt) KEK_MEK) = H_MEK).
      {
        case_eq (beq_text (Hash (D_Sym (Kdf p Salt) KEK_MEK)) H_MEK).
        + intro HP.
          rewrite Nat.eqb_eq in HP.
          auto.
        + intro HP.
          rewrite HP in H1.
          inversion H1.
      }
      clear H1.
      unfold H_MEK in HB.
      specialize (rareConflictHash MEK (D_Sym (Kdf p Salt) KEK_MEK)) as HC.
      assert (HD: Rare (D_Sym (Kdf p Salt) KEK_MEK)).
      {
        assert (HP: Rare (D_Sym (Kdf p Salt) KEK_MEK) /\
          Safe (as_set [Hash MEK]) (D_Sym (Kdf p Salt) KEK_MEK) ).
        {
          auto.
        }
        apply proj1 in HP.
        auto.
      }
      clear HB HC.
      specialize (invRare (fun x => D_Sym x KEK_MEK) (Kdf p Salt)) as HE.
      specialize (invRare (fun x => Kdf x Salt) p) as HF.
      assert (HG: Rare p).
      {
        auto.
      }
      contradiction.
  - auto.
Qed.

Lemma correctWrap:
  forall mek k sig n,
  sig = MSign k ->
  Wrap mek k sig n =
    WSome (E_Asym k
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
  rewrite H2.
  auto.
Qed.

(*
  Only verified k+sig leads to WSome w, except rare cases
*)
Lemma someWrap: forall mek k sig n,
  exists w, Wrap mek k sig n = WSome w ->
  sig = MSign k \/ Rare sig.
Proof.
  intros mek k sign n.
  exists (E_Asym k (Conc {|mek := mek;
                           nonce := n|})).
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
  Unwrap ( E_Asym (pub DK) (Conc w)) n = USome (mek w).
Proof.
  intros w n H1.
  unfold Unwrap.
  specialize (asymEnDe DK (Conc w)) as H2.
  specialize (SplitConcatenation w) as H3.
  assert (H4: nonce (Splt (D_Asym (pr DK) (E_Asym (pub DK) (Conc w)))) = n).
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

Lemma WrapUnwrap:
  forall k n, exists e,
  Wrap k (pub DK) SIG n = WSome e /\
  Unwrap e n = USome k.
Proof.
  intros k n.
  exists (E_Asym (pub DK) (Conc {|mek := k; nonce := n|})).
  split.
  - apply correctWrap.
    unfold SIG.
    auto.
  - apply correctUnwrap.
    auto.
Qed.

(*

(* TODO:  instead of ~ *)
Axiom signAuthority:
  forall s k, Safe s k  ->
  forall kp t sig, pr kp = k ->
  ~(Verify (pub kp) t sig).
Axiom signIntegrity:.

Axiom goodKdf: forall p s p',
  let kek := (Kdf p s) in
  kek = Kdf p' s ->
  (Rare p' /\
  Safe (as_set [s;kek]) p' ).
Lemma rareConflictKdf: forall p s p',
  p <> p' /\ Kdf p s = Kdf p' s ->
  Rare p'.
Proof.
  intros p s p' H.
  destruct H as [H1 H2].
  specialize (goodKdf p s p') as H3.
  destruct H3 as [H4 H5].
  auto. auto.
Qed.
Theorem saltyKdf: forall p s, Safe (as_set [p]) (Kdf p s).
Axiom onewayKdf: forall p s, Safe (as_set [Kdf p s]) p.
Axiom incEasySafe: forall t h l, (Safe l t <> ) -> (Safe (add_set text l h) t <> ).

Parameter TextStrength: text -> strength.
Parameter WeakSet: textSet.
(* TODO: Change to Definition *)
Axiom prioriLeaked: forall t, TextStrength t = Weak -> in_set text WeakSet t.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Pred_Type.

Axiom relationEquivalence: Equivalence TextRelated.

Fixpoint SetStrength (l: list text) :=
  match l with
  | nil => Strong
  | h :: t => match (TextStrength h) with
    | Weak => Weak
    | Strong => SetStrength t
    end
  end.
*)

