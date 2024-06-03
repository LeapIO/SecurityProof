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
  D_Asym (pub kp) (E_Asym (pr kp) t) = t.
Axiom asymDeEn: forall kp t,
  E_Asym (pr kp) (D_Asym (pub kp) t) = t.

Parameter Hash: text -> text.
Axiom rareConflictHash: forall t1 t2,
  Hash t1 = Hash t2 ->
  Guess (as_set [Hash t1]) t2 = Hard.
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
Lemma correctPwd: Auth PWD = ASome MEK.
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

Parameter Sign: key -> text -> text.
Parameter Verify:
  key -> text -> text -> bool.
Axiom signCorrect: forall kp t,
  let sig := Sign (pr kp) t in
  (Verify (pub kp) t sig) = true.

Inductive wrap_option :=
  | WSome (e_mek : text)
  | WFail.
Record wrapped := {mek: key; nonce: nat}.
Parameter Conc: wrapped -> text.
Parameter Splt: text -> wrapped.
Axiom SplitConcatenation:
  forall w, w = Splt (Conc w).

(* TODO
  Currently use MEK directly
  It should be fetched from Auth
  Some funcionic things may help
*)
Definition Wrap PUB_t SIG_t (N_t:nat) :=
  if (Verify (pub MK) PUB_t SIG_t)
    then let w := {|mek := MEK;
                  nonce := N_t|} in
    WSome (E_Asym PUB_t (Conc w))
    else WFail.

(*

(* TODO: Hard instead of ~ *)
Axiom signAuthority:
  forall s k, Guess s k = Hard ->
  forall kp t sig, pr kp = k ->
  ~(Verify (pub kp) t sig).
Axiom signIntegrity:.

Axiom rareConflictKdf: forall p s,
  (forall p', Kdf p s = Kdf p' s -> Guess (as_set [s;(Kdf p s)]) p' = Hard) /\
  (forall s', Kdf p s = Kdf p s' -> Guess (as_set [p;(Kdf p s)]) s' = Hard).
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

