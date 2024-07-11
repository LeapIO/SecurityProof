Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Import ListNotations.

Definition text := nat.

Module ListEnsemble.
  Notation "t ∈ s" := (Ensembles.In text s t)
    (at level 60, right associativity).
  Notation "t ∉ s" := (~(t ∈ s))
    (at level 60, right associativity).
  Notation "t :: s" := (Ensembles.Add text s t)
    (at level 60, right associativity).
End ListEnsemble.
Import ListEnsemble.
Notation "a ∪ b" := (Union text a b)
    (at level 60, right associativity).

Definition key := text.
Definition salt := text.
Definition password := text.
Definition ciphertext := text.
Definition textSet := Ensemble text.
Definition beq_text := Nat.eqb.

Record key_pair := {pub: key; pr: key}.
Record wrapped := {mek: key; nonce: nat}.
Record pipeout := {data: text;
                   leaked: textSet}.
Record leapout := {final: key;
                   unsafe: textSet}.

Inductive auth_option :=
  | ASome (mek : key)
  | AFail.
Inductive wrap_option :=
  | WSome (e_mek : text)
  | WFail.
Inductive unwrap_option :=
  | USome (mek : text)
  | UFail.
Inductive leap_option :=
  | LSome (res : leapout)
  | LAuthFail (unsafe: textSet)
  | LWrapFail (unsafe: textSet)
  | LUnwrapFail (unsafe: textSet).

Parameter TextRelated: text -> text -> Prop.
Notation "x ~ y" := (TextRelated x y)
  (at level 60, right associativity).
Notation "x ≁ y" := (~(x ~ y))
  (at level 60, right associativity).
Definition UnrelatedSet s t := forall h,
  h ∈ s -> t ≁ h.

Fixpoint as_set (l: list text) : textSet :=
  match l with
  | [] => Empty_set text
  | cons x xs => x :: (as_set xs)
  end.
Notation "{ }" := (as_set []).
Notation "{ x ; .. ; y }" :=
  (as_set (cons x .. (cons y nil) ..)).

Parameter Infer: textSet -> textSet.
Definition Safe s t := t ∉ (Infer s).

Parameter CrackSignature: Prop.
Parameter CrackHash: Prop.
Parameter E_Sym D_Sym:
  key -> text -> text.
Parameter E_Asym D_Asym:
  key -> text -> text.
Parameter Hash: text -> text.
Parameter Kdf: password -> salt -> key.
Parameter Sign: key -> text -> text.
Parameter Verify:
  key -> text -> text -> bool.
Parameter Conc: wrapped -> text.
Parameter Splt: text -> wrapped.

Axiom nilInfer: Infer {} = {}.
Lemma nilSafe: forall t, Safe {} t.
Proof.
  intro t.
  unfold Safe.
  rewrite nilInfer.
  intros H.
  inversion H.
Qed.
Axiom incSafe: forall t h s,
  (Safe s t) /\ (t ≁ h) ->
  (Safe (h :: s) t).

Axiom symEnDe:
  forall k t, D_Sym k (E_Sym k t) = t.
Axiom symDeEn:
  forall k t, E_Sym k (D_Sym k t) = t.
Axiom symSafety: forall k t,
  Safe {E_Sym k t} t.
Axiom asymKeySafety: forall kp,
  Safe {pr kp} (pub kp).
Axiom asymEnDe: forall kp t,
  D_Asym (pr kp) (E_Asym (pub kp) t) = t.
Axiom conflictHash: forall t1 t2,
  Hash t1 = Hash t2 -> (t1 = t2 \/ CrackHash).
Axiom injectiveKdf: forall p1 p2 salt,
  p1 <> p2 -> Kdf p1 salt <> Kdf p2 salt.
Axiom bijectiveSym: forall k1 k2 t,
  k1 = k2 <-> E_Sym k1 t = E_Sym k2 t.
Axiom signCorrect: forall kp t sig,
  sig = Sign (pr kp) t \/ CrackSignature <->
  Verify (pub kp) t sig = true.
Axiom serialCorrect:
  forall w, w = Splt (Conc w).