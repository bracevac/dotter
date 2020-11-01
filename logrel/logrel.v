Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Psatz. (* mainly for lia *)
Import ListNotations.

(*
  This file is a reconstruction of "Towards Strong Normalization for
  Dependent Object Types (DOT)" by Wang and Rompf. We simplify the
  logical relation (particularly, no step indices) and give abstract
  types an impredicative existential type semantics, i.e., they are
  nothing special type theoretically.

  Compatible with Coq 8.12.0.

  TODOs
  * Extend with intersections and recursive types.
  * Extend to full paths and eventually full dependent types.
*)


(* ### Syntax ### *)

Definition id := nat.

(* term variables occurring in types *)
Inductive var : Type :=
| varF : id -> var (* free, in concrete environment *)
| varB : id -> var (* locally-bound variable. For variables under dep types *)
.

Inductive ty : Type :=
| TTop  : ty
| TBot  : ty
| TAll  : ty  -> ty -> ty
| TSel  : var -> ty
| TMem  : ty  -> ty -> ty
(* | TBind : ty  -> ty *)
(* | TAnd  : ty  -> ty -> ty *)
.

Inductive tm : Type :=
| tvar    : var -> tm
| ttyp    : ty  -> tm
| tabs    : ty  -> tm -> tm
| tapp    : tm  -> tm -> tm
(* | tunpack : tm  -> tm -> tm *)
.

(* ### Representation of Bindings ### *)

(* An environment is a list of values, indexed by decrementing ids. *)

(* Look up a free variable (deBruijn level) in env   *)
Fixpoint indexr {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' =>
      if (beq_nat n (length l')) then Some a else indexr n l'
  end.

(* Look up a bound variable (deBruijn index) in env *)
Definition indexl {X : Type} (n : id) (l : list X) : option X := nth_error l n.

Inductive vl : Type :=
| vabs : list vl -> ty -> tm -> vl
| vty  : list vl -> ty -> vl
.

Definition tenv := list ty. (* Γ environment: static *)
Definition venv := list vl. (* H environment: run-time *)


(* open define a locally-nameless encoding wrt to TVarB type variables. *)
(* substitute var u for all occurrences of (varB k) *)
Fixpoint open_rec (k: nat) (u: var) (T: ty) { struct T }: ty :=
  match T with
    | TTop          => TTop
    | TBot          => TBot
    | TAll T1 T2    => TAll (open_rec k u T1) (open_rec (S k) u T2)
    | TSel (varF x) => TSel (varF x)
    | TSel (varB i) => if beq_nat k i then TSel u else TSel (varB i)
    | TMem T1 T2    => TMem (open_rec k u T1) (open_rec k u T2)
    (* | TBind T       => TBind (open_rec (S k) u T) *)
    (* | TAnd T1 T2    => TAnd (open_rec k u T1) (open_rec k u T2) *)
  end.

Definition open (n : nat) T := open_rec 0 (varF n) T.
Definition open' {A : Type} (env : list A) T := open_rec 0 (varF (length env)) T.

Fixpoint open_rec_tm (k : nat) (u : var) (t : tm) {struct t} : tm :=
  match t with
  | tvar   (varF x) => tvar (varF x)
  | tvar   (varB x) => if beq_nat k x then tvar u else tvar (varB x)
  | ttyp    T       => ttyp    (open_rec k u T)
  | tabs    T  t    => tabs    (open_rec k u T)     (open_rec_tm (S k) u t)
  | tapp    t1 t2   => tapp    (open_rec_tm k u t1) (open_rec_tm k u t2)
  (* | tunpack t1 t2   => tunpack (open_rec_tm k u t1) (open_rec_tm (S k) u t2) *)
  end
.

Definition open_tm (n : nat) t := open_rec_tm 0 (varF n) t.
Definition open_tm' {A : Type} (env : list A) t := open_rec_tm 0 (varF (length env)) t.


Inductive
  ctx_wf : tenv -> Prop :=
  | wf_nil  :
      ctx_wf []

  | wf_cons : forall Γ T,
      ctx_wf Γ ->
      ty_wf Γ T ->
      ctx_wf (T :: Γ)

with
  ty_wf : tenv -> ty -> Prop :=
  | wf_top : forall Γ,
      ctx_wf Γ ->
      ty_wf Γ TTop

  | wf_bot : forall Γ,
      ctx_wf Γ ->
      ty_wf Γ TBot

  | wf_all : forall Γ T1 T2,
      ty_wf Γ T1 ->
      ty_wf (T1 :: Γ) (open' Γ T2) ->
      ty_wf Γ (TAll T1 T2)

  | wf_sel : forall Γ x T1 T2,
      has_type Γ (tvar (varF x)) (TMem T1 T2) ->
      ty_wf Γ (TSel (varF x))

  | wf_mem : forall Γ T1 T2,
      ty_wf Γ T1 ->
      ty_wf Γ T2 ->
      ty_wf Γ (TMem T1 T2)

  (* | wf_bind : forall Γ T, *)
  (*     ty_wf ((TBind T) :: Γ) (open' Γ T) -> *)
  (*     ty_wf Γ (TBind T) *)

  (* | wf_and : forall Γ T1 T2, *)
  (*     ty_wf Γ T1 -> *)
  (*     ty_wf Γ T2 -> *)
  (*     ty_wf Γ (TAnd T1 T2) *)

with
  has_type : tenv -> tm -> ty -> Prop :=
  | t_var : forall Γ x T,
      ctx_wf Γ ->
      indexr x Γ = Some T ->
      has_type Γ (tvar (varF x)) T

  | t_typ : forall Γ T,
      ty_wf Γ T ->
      has_type Γ (ttyp T) (TMem T T)

  | t_abs: forall Γ T1 T2 t,
      ty_wf Γ T1 ->
      has_type (T1 :: Γ) (open_tm' Γ t) (open' Γ T2) ->
      has_type Γ (tabs T1 t) (TAll T1 T2)

  | t_app : forall Γ t1 t2 T1 T2,
      has_type Γ t1 (TAll T1 T2) ->
      open' Γ T2 = T2 ->
      has_type Γ t2 T1 ->
      has_type Γ (tapp t1 t2) T2

  | t_dapp : forall Γ t x T1 T2,
      has_type Γ t (TAll T1 T2) ->
      has_type Γ (tvar (varF x)) T1 ->
      has_type Γ (tapp t (tvar (varF x))) (open x T2)

  (* | t_and : forall Γ x T1 T2, *)
  (*     has_type Γ (tvar (varF x)) T1 -> *)
  (*     has_type Γ (tvar (varF x)) T2 -> *)
  (*     has_type Γ (tvar (varF x)) (TAnd T1 T2) *)

  (* | t_var_pack : forall Γ x T, *)
  (*     ty_wf Γ (TBind T) ->  *)
  (*     has_type Γ (tvar (varF x)) (open (varF x) T) ->  *)
  (*     has_type Γ (tvar (varF x)) (TBind T) *)

  (* | t_unpack : forall Γ t1 t2 T1 T1' T2, *)
  (*     has_type Γ t1 (TBind T1) -> *)
  (*     T1' = (open (varF (length Γ)) T1) -> *)
  (*     has_type (T1' :: Γ) t2 T2 -> *)
  (*     has_type Γ (tunpack t1 t2) T2 *)

  | t_sub: forall Γ e T1 T2,
      has_type Γ e T1 ->
      stp Γ T1 T2 ->
      has_type Γ e T2

with
  stp : tenv -> ty -> ty -> Prop :=
  | stp_top : forall Γ T,
      ty_wf Γ T ->
      stp Γ T TTop

  | stp_bot : forall Γ T,
      ty_wf Γ T ->
      stp Γ TBot T

  | stp_mem : forall Γ S1 S2 T1 T2,
      stp Γ S2 S1 ->
      stp Γ T1 T2 ->
      stp Γ (TMem S1 T1) (TMem S2  T2)

  | stp_sel1 : forall Γ x T,
      has_type Γ (tvar (varF x)) (TMem T TTop) ->
      stp Γ T (TSel (varF x))

  | stp_sel2 : forall Γ x T,
      has_type Γ (tvar (varF x)) (TMem TBot T) ->
      stp Γ (TSel (varF x)) T

  | stp_selx : forall Γ x T1 T2,
      has_type Γ (tvar (varF x)) (TMem T1 T2) ->
      stp Γ (TSel (varF x)) (TSel (varF x))

  | stp_all : forall Γ S1 S2 T1 T2,
      stp Γ S2 S1 ->
      stp (S2 :: Γ) (open' Γ T1) (open' Γ T2) ->
      stp Γ (TAll S1 T1) (TAll S2 T2)

  | stp_trans : forall Γ S T U,
      stp Γ S T ->
      stp Γ T U ->
      stp Γ S U

  (* TODO subtyping for recursive types and intersections *)
.


(* ### Evaluation (Big-Step Semantics) ### *)

Inductive Result : Type :=
| Done   : vl -> Result
| Error  : Result
| NoFuel : Result
.

Fixpoint eval(fuel : nat)(γ : venv)(t : tm){struct fuel}: Result :=
  match fuel with
  | 0   => NoFuel
  | S n =>
    match t with
    | tvar (varF x) =>
      match (indexr x γ) with
      | Some v => Done v
      | None   => Error
      end
    | tvar (varB x) =>
      match (indexl x γ) with
      | Some v => Done v
      | None => Error
      end
    | ttyp T    => Done (vty γ T)
    | tabs T t  => Done (vabs γ T t)
    | tapp t1 t2 =>
      match eval n γ t2 with
      | Done v2 =>
        match eval n γ t1 with
        | Done (vabs γ' _ t) => eval n (v2 :: γ') t
        | Done _  => Error
        | err => err
        end
      | err => err
      end
    (* | tunpack t1 t2 => *)
    (*   match eval n γ t1 with *)
    (*   | Done v1 => eval n (v1 :: γ) t2 *)
    (*   | err => err *)
    (*   end *)
    end
  end.

Definition evaln γ e v := exists nm, forall n, n > nm -> eval n γ e = Done v.


(* ### Semantic Interpretation of Types (Logical Relations) ### *)

Fixpoint tsize_flat(T: ty) :=
  match T with
    | TTop => 0
    | TBot => 0
    | TAll T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | TSel _ => 0
    | TMem T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    (* | TBind T => S (tsize_flat T) *)
    (* | TAnd T1 T2 => S (tsize_flat T1 + tsize_flat T2) *)
  end.
Lemma open_preserves_size: forall T x j,
  tsize_flat T = tsize_flat (open_rec j (varF x) T).
Proof.
  intros T. induction T; intros; simpl; eauto.
  destruct v; simpl; destruct (beq_nat j i); eauto.
Qed.

Declare Scope dsub.

Notation Dom := (vl -> Prop).

Definition subset (D1 D2 : Dom) : Prop := forall v, D1 v -> D2 v.
Hint Unfold subset : dsub.
Notation "D1 ⊆ D2" := (subset D1 D2) (at level 75).

Definition elem {A} (v : A) (D : A -> Prop) : Prop := D v.
Notation "v ∈ D" := (elem v D) (at level 75).
Hint Unfold elem : dsub.
Definition elem2 {A B} (γ : A) (v : B) (P : A -> B -> Prop) := P γ v.
Notation "⟨ H , v ⟩ ∈ D" := (elem2 H v D) (at level 75).
Hint Unfold elem2 : dsub.

Notation "{{ ' p | P }}" := (fun v => match v with
                                | p => P
                                | _ => False
                                end)
  (at level 200, p pattern).

Definition denv := list Dom.

Notation DTop  := (fun _ => True).
Notation DBot  := (fun _ => False).

Definition DSel (x : id) (ρ : denv) : Dom :=
  match indexr x ρ with
    | Some D => D
    | None   => DBot
  end.
Hint Unfold DSel : dsub.

Definition ℰ (D : Dom) (γ : venv) (t : tm) : Prop :=
  exists k, exists v, eval k γ t = Done v /\ v ∈ D.
Hint Unfold ℰ : dsub.

Variable val_term : vl -> tm. (* TODO turns value into syntactic closed term*)

Require Coq.Program.Wf.
Program Fixpoint ty_interp (ρ : denv) (T : ty) {measure (tsize_flat T)} : Dom :=
  match T with
  | TTop          => DTop
  | TBot          => DBot
  | TAll T1 T2    => (* DAll (ty_interp') ρ T1 T2 *)
    {{ '(vabs γ _ t) | let D := (@ty_interp ρ T1 _) in
                       forall vx, vx ∈ D -> ⟨ (vx :: γ) , t  ⟩ ∈ ℰ (@ty_interp (D :: ρ) (open' γ T2) _) }}
  | TSel (varF x) => DSel x ρ (* TODO what about varB? *)
  | TMem T1 T2    =>
    {{ '(vty γ T) | exists X, (@ty_interp ρ T1 _) ⊆ X /\ X ⊆ (@ty_interp ρ T2 _) /\ (forall v, v ∈ X -> has_type [] (val_term v) T) }} (* TODO fix the side condition *)
  | _             => DBot
  end.
Next Obligation. simpl. lia. Qed.
Next Obligation. simpl. unfold open'. rewrite <-open_preserves_size. lia. Qed.
Next Obligation. simpl. lia. Qed.
Next Obligation. simpl. lia. Qed.
Solve All  Obligations with repeat split; intros; discriminate.


(* Experiment with well-founded recursion.

   This solves the problem of Program Fixpoint unfoldings being
   incomprehensible and a proof of a manual unfolding theorem being
   unbearably slow. Kudos to Chris Casinghino, whose Coq artifact
   for the Zombie language inspired this approach.
*)

(* well-founded relation which captures the recursive calls in the interpretation val_type. *)
Inductive R : ty -> ty -> Prop :=
| RAll1 : forall {T1 T2}, R T1 (TAll T1 T2)
| RAll2 : forall {T1 T2 A} {γ : list A}, R (open' γ T2) (TAll T1 T2)
| RMem1 : forall {T1 T2}, R T1 (TMem T1 T2)
| RMem2 : forall {T1 T2}, R T2 (TMem T1 T2)
.

Hint Constructors Acc : dsub.
Hint Constructors R : dsub.

Lemma wfR' : forall n T, tsize_flat T <= n -> Acc R T.
Proof.
  induction n.
  - destruct T; intros; constructor; intros; simpl in *; inversion H0; try lia.
  - intros. destruct T; constructor; intros; simpl in *; inversion H0; subst; apply IHn; try lia.
    unfold open'. rewrite <- open_preserves_size. lia.
Defined.

Theorem wfR : well_founded R.
Proof.
  red. intros T. eapply wfR'. auto.
Defined.

Definition val_type_naked (T : ty) : (forall T', R T' T -> denv -> Dom) -> denv -> Dom :=
  match T with
  | TTop          => fun _ _ => DTop
  | TBot          => fun _ _ => DBot
  | TAll T1 T2    => fun val_type ρ =>
    {{ '(vabs γ _ t) | let D := (val_type T1 RAll1 ρ) in
                       forall vx, vx ∈ D -> ⟨ (vx :: γ) , t  ⟩ ∈ ℰ (val_type (open' γ T2) RAll2 (D :: ρ)) }}
  | TSel (varF x) => fun _ ρ => DSel x ρ (* TODO what about varB? *)
  | TMem T1 T2    => fun val_type ρ =>
    {{ '(vty γ T) | exists X, (val_type T1 RMem1 ρ) ⊆ X /\ X ⊆ (val_type T2 RMem2 ρ) /\ (forall v, v ∈ X -> has_type [] (val_term v) T) }} (* TODO fix the side condition *)
  | _             => fun _ _ => DBot
  end.

Definition val_type : ty -> denv -> Dom :=
  Fix wfR (fun _ => denv -> Dom) val_type_naked.

(* Providing an unfolding requires extensionality. *)
Axiom extensionality : forall (A : Type) (B : A -> Type)
                              (f g : forall a : A, B a),
     (forall a : A, f a = g a) -> f = g.

Theorem val_type_extensional :
  forall (T1 : ty) (f g : forall T2 : ty, R T2 T1 -> denv -> Dom),
        (forall (T2 : ty) (r : R T2 T1), f T2 r = g T2 r)
     -> val_type_naked T1 f = val_type_naked T1 g.
Proof.
  intros;
  assert (f = g) by (eauto using extensionality); subst; eauto.
Qed.
Hint Resolve val_type_extensional : dsub.

(* unfolding tactics for hypotheses and goal *)
Tactic Notation "prim_unfold_val_type" "in" hyp(H) :=
  unfold val_type in H; rewrite Fix_eq in H;
  [ simpl in H; fold val_type in H | apply val_type_extensional ].

Ltac prim_unfold_interp :=
  unfold val_type; rewrite Fix_eq;
  [ simpl; fold val_type | apply val_type_extensional ].

(* Lemma fundamental : forall Γ e T, has_type Γ e T -> forall γ, (* γ ∈ ⟦ Γ ⟧ *) *)
