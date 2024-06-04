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
Module ListEnsemble.
  Definition in_set := Ensembles.In.
  Definition add_set := Ensembles.Add.
End ListEnsemble.
Import ListEnsemble.

Inductive difficulty : Type := Hard | Easy.
Inductive strength : Type := Strong | Weak.
Inductive safety : Type := Safe | Dangerous.

Definition text := nat.
Definition key := text.
Definition salt := text.
Definition password := text.
Definition ciphertext := text.
Definition textSet := Ensemble text.
Definition beq_text := Nat.eqb.
Record key_pair := {pub: key; pr: key}.

Parameter PWD: password.
Parameter Salt: salt.
Parameter MEK: key.
Parameter MK DK: key_pair.

Parameter TextRelated: text -> text -> Prop.
Definition UnrelatedSet l t := forall h,
  (in_set text l h) -> ~(TextRelated t h).

Fixpoint as_set (l: list text) : textSet :=
  match l with
  | [] => Empty_set text
  | x :: xs => add_set text (as_set xs) x
  end.

Parameter Guess:
  textSet -> text -> difficulty.
Axiom nilGuess:
  forall t, Guess (as_set []) t = Hard.
Axiom incHardGuess: forall t h l,
  (Guess l t = Hard) /\ ~(TextRelated t h) ->
  (Guess (add_set text l h) t = Hard).

Lemma unrelatedGuess: forall uset t,
  Finite text uset -> UnrelatedSet uset t ->
  Guess uset t = Hard.
Proof.
  intros ll t l.
  induction l as [| l' l'f H m H0].
  - intro H1.
    apply nilGuess.
  - intro H1.
    apply incHardGuess.
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

Lemma unionTwoUnrelatedHardGuess:
  forall s1 s2 t, Finite text s1 ->
  Finite text s2 ->
  UnrelatedSet s1 t /\ UnrelatedSet s2 t ->
  Guess (Union text s1 s2) t = Hard.
Proof.
  intros ll1 ll2 t l1 l2 H.
  apply unrelatedGuess.
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

Lemma unionUnrelatedHardGuess:
  forall s s' t, Finite text s ->
  Finite text s' -> UnrelatedSet s' t ->
  Guess s t = Hard ->
  Guess (Union text s s') t = Hard.
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
    apply incHardGuess.
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

Parameter Rare: text -> Prop.
Axiom invRare: forall f t,
  Rare (f t) -> Rare t.

Parameter E_Sym D_Sym:
  key -> text -> text.
Axiom symEnDe:
  forall k t, D_Sym k (E_Sym k t) = t.
Axiom symDeEn:
  forall k t, E_Sym k (D_Sym k t) = t.
Axiom symTextSafety: forall k t,
  Guess (as_set [E_Sym k t]) t = Hard.

Axiom asymKeySafety: forall kp,
  Guess (as_set [pr kp]) (pub kp) = Hard.

Parameter E_Asym D_Asym:
  key -> text -> text.
Axiom asymEnDe: forall kp t,
  D_Asym (pr kp) (E_Asym (pub kp) t) = t.
Axiom asymDeEn: forall kp t,
  E_Asym (pub kp) (D_Asym (pr kp) t) = t.

Parameter Hash: text -> text.
Axiom rareConflictHash: forall t1 t2,
  Hash t1 = Hash t2 ->
  (Rare t2 /\
  Guess (as_set [Hash t1]) t2 = Hard).
Lemma onewayHash: forall t,
  Guess (as_set [Hash t]) t = Hard.
Proof.
  intro t.
  apply rareConflictHash.
  trivial.
Qed.

Parameter Kdf: password -> salt -> key.

Definition KEK := Kdf PWD Salt.
Definition KEK_MEK := E_Sym KEK MEK.
Definition H_MEK := Hash MEK.
Inductive auth_option :=
  | ASome (mek : key)
  | AFail.

Definition Auth (PWD_t:password) :=
  let KEK_t := Kdf PWD_t Salt in
  let MEK_t := D_Sym KEK_t KEK_MEK in
  if (beq_text (Hash MEK_t) H_MEK)
    then ASome MEK_t else AFail.

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
          Guess (as_set [Hash MEK]) (D_Sym (Kdf p Salt) KEK_MEK) = Hard).
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

Parameter Sign: key -> text -> text.
Parameter Verify:
  key -> text -> text -> bool.
Axiom signCorrect: forall kp t,
  let sig := Sign (pr kp) t in
  (Verify (pub kp) t sig) = true.
Definition SIG :=
  Sign (pr MK) (pub DK).

Inductive wrap_option :=
  | WSome (e_mek : text)
  | WFail.
Record wrapped := {mek: key; nonce: nat}.
Parameter Conc: wrapped -> text.
Parameter Splt: text -> wrapped.
Axiom SplitConcatenation:
  forall w, w = Splt (Conc w).

Definition Wrap mek k sig n :=
  if (Verify (pub MK) k sig)
    then let w := {|mek := mek;
                  nonce := n|} in
    WSome (E_Asym k (Conc w))
    else WFail.

Lemma correctWrap:
  forall mek k sig n,
  sig = Sign (pr MK) k ->
  Wrap mek k sig n =
    WSome (E_Asym k
          (Conc {|mek := mek;
                  nonce := n|})).
Proof.
  intros mek k sig n H1.
  unfold Wrap.
  assert (H2: Verify (pub MK) k sig = true).
  {
    rewrite H1.
    apply signCorrect.
  }
  rewrite H2.
  auto.
Qed.

Inductive unwrap_option :=
  | USome (mek : text)
  | UFail.
Definition Unwrap w n:=
  let uw :=
    Splt (D_Asym (pr DK) w) in
  if (beq_text (nonce uw) n)
    then USome (mek uw)
    else UFail.

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

(* TODO: Hard instead of ~ *)
Axiom signAuthority:
  forall s k, Guess s k = Hard ->
  forall kp t sig, pr kp = k ->
  ~(Verify (pub kp) t sig).
Axiom signIntegrity:.

Axiom goodKdf: forall p s p',
  let kek := (Kdf p s) in
  kek = Kdf p' s ->
  (Rare p' /\
  Guess (as_set [s;kek]) p' = Hard).
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
Theorem saltyKdf: forall p s, Guess (as_set [p]) (Kdf p s) = Hard.
Axiom onewayKdf: forall p s, Guess (as_set [Kdf p s]) p = Hard.
Axiom incEasyGuess: forall t h l, (Guess l t <> Hard) -> (Guess (add_set text l h) t <> Hard).

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

