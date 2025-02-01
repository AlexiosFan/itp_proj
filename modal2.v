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
  
  imp : forall w : W, forall A B : mformula, In w (worlds frame) -> (evaluation w (Imp A B)) <-> ((evaluation w A) -> (evaluation w B));
  box : forall w : W, forall A : mformula, In w (worlds frame) -> (evaluation w (Box A)) <-> (forall v : W, In v (worlds frame) -> frame.(accessibility) w v -> evaluation v A);
}.


Definition mvalid (M: Model) (A: mformula) := forall w: W, In w (worlds (frame M)) -> M.(evaluation) w A.
Definition fvalid (F: Frame) (A: mformula) := forall M: Model, M.(frame) = F -> mvalid M A.
Definition mvalid_class (MC: Model -> Prop) (A: mformula) := forall M: Model, MC M -> mvalid M A.
Definition fvalid_class (FC: Frame -> Prop) (A: mformula) := forall F: Frame, FC F -> fvalid F A.

Lemma or_not_l : forall P Q : Prop, (P \/ Q) <-> (~ P -> Q).
Proof.
  intros P Q.
  split.
  
  - (* P \/ Q -> (~P -> Q) *)
    intros [HP | HQ] HNP.
    + (* P is true *)
      exfalso. apply HNP. assumption.
    + (* Q is true *)
      assumption.

  - (* (~P -> Q) -> P \/ Q *)
    intros H.
    destruct (classic P) as [HP | HNP].
    + left. assumption.  
    + right. apply H. assumption. 
Qed.

Lemma not_impl : forall P X : Prop,
  ~(P -> X) -> (P /\ ~X).
Proof.
  intros P X H.
  unfold not in H.
  split.
  - (* prove P *)
    (* Law of Excluded Middle (LEM) For any proposition 𝑃, either P is true or P is false.*)
    destruct (classic P) as [HP | HnP].
    + (* P is true *)
      assumption.
    + (* P is false *)
      exfalso. apply H. intro HP'.  
      exfalso. apply HnP. exact HP'.
  - (* prove ~X *)
    intro HX. apply H. intros _.
    exact HX.
Qed.

Lemma or_comm : forall A B : Prop, A \/ B -> B \/ A.
Proof.
  intros A B H.
  destruct H as [HA | HB].
  - right. assumption. 
  - left. assumption.
Qed.


Lemma diamond_exists :
  forall (M : Model) (w : W) (A : mformula),
    In w (worlds (frame M)) ->
    M.(evaluation) w (Diamond A) ->
    exists u : W, (frame M).(accessibility) w u /\ M.(evaluation) u A.
Proof.
  intros M w A Hw Hdiamond. unfold Diamond in Hdiamond. apply M.(neg) in Hdiamond; auto.
  rewrite box in Hdiamond. apply not_all_ex_not in Hdiamond. destruct Hdiamond as [v H].
  apply not_impl in H. destruct H as [H1 H2]. apply not_impl in H2. destruct H2 as [H2 H3].
  rewrite <- neg in H3.  apply NNPP in H3. exists v. split; assumption. auto. auto.
Qed.


Lemma diamond_equiv_exists :
  forall (M : Model) (w : W) (A : mformula),
    In w (worlds (frame M)) ->
    ( M.(evaluation) w (Diamond A)
      <-> exists u : W, (frame M).(accessibility) w u /\ M.(evaluation) u A ).
Proof.
  intros M w A Hw.
  split.
  - intros Hdiamond.
    eapply diamond_exists; eauto.
  - intros [u [Hwu HuA]].
    unfold Diamond. apply M.(neg).
    + exact Hw.    
    + unfold not. intros HboxNotA.
      rewrite (M.(box) w (Not A)) in HboxNotA; [|exact Hw].
      specialize (HboxNotA u).
      assert (Hwu2:=Hwu).
      apply domain in Hwu2.
      destruct Hwu2 as [ Q W].
      assert (Y:=HboxNotA W Hwu).
      rewrite <- neg in Y.
      auto. auto.
Qed.



(*(box. a -> b) -> (box. a -> box. b)*)
Lemma box_imp_aux: forall M: Model, forall A B: mformula, mvalid M (Imp (Box (Imp A B)) (Imp (Box A) (Box B))).
Proof.
  unfold mvalid.
  intros.
  apply imp.  apply H.  intros.
  apply imp. apply H. intros.
  rewrite box. intros. 
  rewrite box in H0. assert (H0':= H0 v H2 H3).
  rewrite imp in H0'. 
  rewrite box in H1. assert (H1':= H1 v H2 H3).
  assert (He:= H0' H1'). apply He. apply H. apply H2. apply H. apply H.
Qed.  


Theorem box_imp: forall (FC: Frame -> Prop) (w: W) (A B: mformula), fvalid_class FC (Imp (Box (Imp A B)) (Imp (Box A) (Box B))).
Proof.
  unfold fvalid_class.
  unfold fvalid.
  intros.
  apply box_imp_aux.
Qed.

(* Further lemmas to proof*)



(* Serial *)
Definition Serial (f : Frame) := forall w: W, exists v: W, accessibility f w v.

Theorem D: forall A : mformula, 
    fvalid_class Serial (Imp (Box A) (Diamond A)).
Proof. 
  unfold fvalid_class.
  unfold fvalid.
  unfold Serial.
  unfold mvalid.
  unfold Diamond.
  intros.
  apply imp. apply H1.  intros.
  apply neg. apply H1.  rewrite box. rewrite box in H2. 
  unfold not. intros.
  assert (H' :=H w).
  destruct H' as [v0 H'']. 
  rewrite <- H0 in H''.
  assert (H2':= H2 v0). assert (H4:= domain (frame M) w v0 H'' ).
  destruct H4 as [Hw Hv0].
  assert (He:=H2' Hv0 H'').
  assert (H3':= H3 v0 Hv0 H'').
  rewrite <- neg in H3'.
  apply H3'. apply He. auto. auto. auto.
Qed. 


(* Reflexive *)
Definition Reflexive (f : Frame) := forall w: W, accessibility f w w.

Theorem M_Reflexive: forall A : mformula, 
    fvalid_class Reflexive (Imp (Box A) A).
Proof. 
  unfold fvalid_class.
  unfold fvalid.
  unfold Reflexive.
  unfold mvalid.
  intros.
  apply imp. apply H1. intros.
  rewrite box in H2. 
    specialize (H2 w H1). rewrite H0 in H2.
    specialize (H w). 
    specialize(H2 H).
  auto. auto.
Qed.

(* Transitive *)
Definition Transitive (f : Frame) := forall w v u: W, accessibility f w v /\ accessibility f v u -> accessibility f w u.

Theorem Four: forall A : mformula,
  fvalid_class Transitive (Imp (Box A) (Box (Box A)) ).
Proof.
  unfold fvalid_class.
  unfold fvalid.
  unfold Transitive.
  unfold mvalid.
  intros.
  apply imp. apply H1. intros.
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

(* Symmetric *)
  
Definition Symmetric (f : Frame) :=
  forall w v : W, accessibility f w v -> accessibility f v w.
  
Theorem Symmetric_Box: forall A : mformula,
  fvalid_class Symmetric (Imp A (Box (Diamond A))).
Proof.
  unfold fvalid_class.
  unfold fvalid.
  unfold Symmetric.
  unfold mvalid.
  unfold Diamond.
  intros.
  apply imp. auto. intros. rewrite box. intros. rewrite <- neg.
  unfold not. intros. rewrite box in H5. rewrite <- H0 in H. assert (H7:= H w v H4). assert (H6:= H5 w H1 H7).
  rewrite <- neg in H6. auto. auto. auto. auto. auto.
Qed.

(* Euclidean *)

Definition Euclidean (f : Frame) :=
  forall w v u : W, accessibility f w v -> accessibility f w u -> accessibility f v u.
  
Theorem Euclidean_Diamond : forall A : mformula,
  fvalid_class Euclidean (Imp (Diamond A) (Box (Diamond A))).
Proof.
  unfold fvalid_class, fvalid, Euclidean, mvalid. 
  intros A F H_euclidean M H_frame w H_valid.
  rewrite <- H_frame in H_euclidean.
  rewrite imp. intros.
  rewrite box. intros.
  rewrite diamond_equiv_exists in H. 
  destruct H as [u [H3 H4] ].
  rewrite diamond_equiv_exists.
  exists u.
  specialize (H_euclidean w v u H1 H3).
  split. auto. auto. assumption. assumption. assumption. assumption.

Qed.

(* Functional *)

Definition Functional (f : Frame) :=
  forall w v u : W, accessibility f w v -> accessibility f w u -> v = u.
  
Theorem Functional_Diamond_Box : forall A : mformula,
  fvalid_class Functional (Imp (Diamond A) (Box A)).
Proof.
  unfold fvalid_class, fvalid, mvalid, Functional.
  intros A F H_functional M H_eqFrame w Hw.
  apply M.(imp).
  - exact Hw.
  - intros H_diamond.
    apply M.(box).
    + exact Hw.
    + intros v Hv Rwv. 
      apply diamond_exists in H_diamond as [u [Hwu HuA]].
      rewrite <- H_eqFrame in H_functional.
      assert (Q:=H_functional w v u Rwv Hwu ).
      rewrite <- Q in HuA.
      auto. auto.
Qed.


(* Shift reflexive *)

Definition ShiftReflexive (F : Frame) :=
  forall w v : W, accessibility F w v -> accessibility F v v.

Theorem C4_ShiftReflexive : forall A : mformula,
  fvalid_class ShiftReflexive (Box (Imp (Box A) A)).
Proof.
  unfold fvalid_class, fvalid, ShiftReflexive, mvalid.
  intros A F H_shift M H_eqFrame w Hw.
  rewrite box.
  - intros. rewrite imp. intro H_box. rewrite box in H_box. rewrite <- H_eqFrame in H_shift.
    specialize (H_shift w v H0). specialize (H_box v H H_shift). auto. auto. auto.
  - auto. 
Qed.


(* Dense *)

Definition Dense (F : Frame) :=
  forall w v : W, accessibility F w v -> exists u : W,
    accessibility F w u /\ accessibility F u v.

Theorem C4_Dense : forall A : mformula,
  fvalid_class Dense (Imp (Box (Box A)) (Box A)).
Proof.
  unfold fvalid_class, fvalid, Dense, mvalid.
  intros A F H_dense M H_eqFrame w Hw.
  apply M.(imp). 
  - exact Hw.
  -  intros H_boxbox.
    apply M.(box).
    + exact Hw.
    + rewrite <- H_eqFrame in H_dense. intros v Hv Rwv.
      destruct (H_dense w v Rwv) as [u [Hwu Hurv]].
      rewrite box in H_boxbox.
      specialize (H_boxbox u).
      destruct (domain (frame M) w u Hwu) as [_ HuWorld].
        specialize(H_boxbox HuWorld Hwu).
      rewrite box in H_boxbox.
      
      specialize (H_boxbox v Hv Hurv). auto. auto. auto.
Qed.

(* Convergent *)

Definition Convergent (F : Frame) :=
  forall w v x : W,
    accessibility F w v -> accessibility F w x ->
    exists u : W, accessibility F v u /\ accessibility F x u.
    

Theorem C_Convergent : forall A : mformula,
  fvalid_class Convergent (Imp (Diamond (Box A)) (Box (Diamond A))).
Proof.
  unfold fvalid_class, fvalid, Convergent, mvalid.
  intros A F H_conv M H_eq w Hw.
  apply M.(imp). 
  - exact Hw.
  - intros H_diamBox.

    apply M.(box). 
    + exact Hw.
    + intros v Hv Rwv.
      apply diamond_exists in H_diamBox.
      destruct H_diamBox as [x [Hwx HxBoxA]].

      rewrite <- H_eq in H_conv.
      assert (I:=H_conv w v x Rwv Hwx).
      destruct I as  [u [HvuH_conv]].
      rewrite box in HxBoxA.
      assert (HH:=H).
      apply domain in H.
      
      destruct H as [H1 H2].
      assert (J:= HxBoxA u H2  HH).
      
      rewrite diamond_equiv_exists.
      exists u.
      split. auto. auto. auto. 
      apply domain in Hwx.
      destruct Hwx as [Hwx1 Hwx2]. auto. auto.
Qed.


