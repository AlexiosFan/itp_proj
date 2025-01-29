Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Import ListNotations.


Parameter W: Type. (* set for worlds*)
Parameter u: Type. (* type for individuals*)
Definition o := W -> Prop. (* type of modal propositions *)

(* Basic semantics of modal logic with implication, false and necessity only*)
Inductive mformula : Type := 
| Var : W-> mformula 
| Bot : mformula
| Imp : mformula -> mformula -> mformula
| Box : mformula -> mformula.

(* Other logical operators *)
Definition Not (A: mformula) := Imp A Bot.
Definition Diamond (A: mformula) := Not (Box (Not A)).
Definition And (A B: mformula) := Not (Imp A (Not B)).
Definition Or (A B: mformula) := Not (And (Not A) (Not B)).

(* Kripke frames, models and validity *)
Record Frame := {
  worlds : list W;                      
  accessibility : W -> W -> Prop; 
  domain : forall u w : W, accessibility u w -> In u (worlds) /\ In w (worlds);
}.

Record Model := {
  frame : Frame;  
  evaluation : W -> mformula -> Prop;
  neg : forall w : W, forall A : mformula, In w (worlds frame) -> ~(evaluation w A) <-> (evaluation w (Not A));
  imp : forall w : W, forall A B : mformula, In w (worlds frame) -> (evaluation w (Imp A B)) <-> (~(evaluation w A) \/ (evaluation w B));
  box : forall w : W, forall A : mformula, In w (worlds frame) -> (evaluation w (Box A)) <-> (forall v : W, In v (worlds frame) -> frame.(accessibility) w v -> evaluation v A);
}.

Definition mvalid (M: Model) (A: mformula) := forall w: W, In w (worlds (frame M)) -> M.(evaluation) w A.
Definition fvalid (F: Frame) (A: mformula) := forall M: Model, M.(frame) = F -> mvalid M A.
Definition mvalid_class (MC: Model -> Prop) (A: mformula) := forall M: Model, MC M -> mvalid M A.
Definition fvalid_class (FC: Frame -> Prop) (A: mformula) := forall F: Frame, FC F -> fvalid F A.


(*(box. a -> b) -> (box. a -> box. b)*)
Lemma box_imp_aux: forall M: Model, forall A B: mformula, mvalid M (Imp (Box (Imp A B)) (Imp (Box A) (Box B))).
Proof.
  unfold mvalid.
  intros.
  apply imp. apply H. apply imply_to_or. intros.
  apply imp. apply H. apply imply_to_or. intros.
  apply box. apply H. intros.
  rewrite box in H0. assert (H0' := H0 v). assert (H0'' := H0' H2).
    apply imp in H0''. 
  rewrite box in H1. assert (H1' := H1 v). assert (H1'' := H1' H2). assert (H1''' := H1'' H3).
  specialize or_to_imply with (P := evaluation M v A) (Q := evaluation M v B). intros.
  specialize (H4 H0'' H1'''). apply H4.
  apply H. 
  apply H2.
  apply H3.
  apply H.
Qed.  

Theorem box_imp: forall (FC: Frame -> Prop) (w: W) (A B: mformula), fvalid_class FC (Imp (Box (Imp A B)) (Imp (Box A) (Box B))).
Proof.
  unfold fvalid_class.
  unfold fvalid.
  intros.
  apply box_imp_aux.
Qed.

(*Further lemmas to proof*)

Definition Serial (f : Frame) := forall w: W, exists v: W, accessibility f w v.

Theorem D: forall A : mformula, 
    fvalid_class Serial (Imp (Box A) (Diamond A)).
Proof. 
  unfold fvalid_class.
  unfold fvalid.
  unfold Serial.
  unfold mvalid.
  intros.
  apply imp. apply H1. apply imply_to_or. intros.
  unfold Diamond. apply neg. apply H1. unfold not. intros. 
  rewrite box in H2. 
    specialize (H w). destruct H as [v H].
    assert(H' := domain F w v H).
    assert(L := proj1 H'). assert(R := proj2 H'). 
    rewrite H0 in H2.
    specialize (H2 v R H).
  rewrite box in H3.
    rewrite H0 in H3.
    specialize (H3 v R H).
    apply neg in H3.
  auto. 
  rewrite H0. auto. 
  rewrite H0. auto. 
  auto.
Qed. 

Definition Reflexive (f : Frame) := forall w: W, accessibility f w w.

Theorem M: forall A : mformula, 
    fvalid_class Reflexive (Imp (Box A) A).
Proof. 
  unfold fvalid_class.
  unfold fvalid.
  unfold Reflexive.
  unfold mvalid.
  intros.
  apply imp. apply H1. apply imply_to_or. intros.
  rewrite box in H2. 
    specialize (H2 w H1). rewrite H0 in H2.
    specialize (H w). 
    specialize(H2 H).
  auto. auto.
Qed.

Definition Transitive (f : Frame) := forall w v u: W, accessibility f w v /\ accessibility f v u -> accessibility f w u.

Theorem Four: forall A : mformula,
  fvalid_class Transitive (Imp (Box A) (Box (Box A)) ).
Proof.
  unfold fvalid_class.
  unfold fvalid.
  unfold Transitive.
  unfold mvalid.
  intros.
  apply imp. apply H1. apply imply_to_or. intros.
  apply box. apply H1. intros. 
  apply box. apply H3. intros.
    specialize (H w v v0).
    rewrite H0 in H4. rewrite H0 in H6.
    assert(H' := conj H4 H6).
    specialize (H H').
  rewrite box in H2.
    specialize (H2 v0 H5).
    rewrite H0 in H2.
    specialize (H2 H).
  auto. auto.
Qed.
 

