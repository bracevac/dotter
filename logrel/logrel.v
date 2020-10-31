Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Omega.
Require Import Coq.Lists.List.
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

Definition tenv := list ty. (* Gamma environment: static *)
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

  | wf_cons : forall Gamma T,
      ctx_wf Gamma ->
      ty_wf Gamma T ->
      ctx_wf (T :: Gamma)

with
  ty_wf : tenv -> ty -> Prop :=
  | wf_top : forall Gamma,
      ctx_wf Gamma ->
      ty_wf Gamma TTop

  | wf_bot : forall Gamma,
      ctx_wf Gamma ->
      ty_wf Gamma TBot

  | wf_all : forall Gamma T1 T2,
      ty_wf Gamma T1 ->
      ty_wf (T1 :: Gamma) (open' Gamma T2) ->
      ty_wf Gamma (TAll T1 T2)

  | wf_sel : forall Gamma x T1 T2,
      has_type Gamma (tvar (varF x)) (TMem T1 T2) ->
      ty_wf Gamma (TSel (varF x))

  | wf_mem : forall Gamma T1 T2,
      ty_wf Gamma T1 ->
      ty_wf Gamma T2 ->
      ty_wf Gamma (TMem T1 T2)

  (* | wf_bind : forall Gamma T, *)
  (*     ty_wf ((TBind T) :: Gamma) (open' Gamma T) -> *)
  (*     ty_wf Gamma (TBind T) *)

  (* | wf_and : forall Gamma T1 T2, *)
  (*     ty_wf Gamma T1 -> *)
  (*     ty_wf Gamma T2 -> *)
  (*     ty_wf Gamma (TAnd T1 T2) *)

with
  has_type : tenv -> tm -> ty -> Prop :=
  | t_var : forall Gamma x T,
      ctx_wf Gamma ->
      indexr x Gamma = Some T ->
      has_type Gamma (tvar (varF x)) T

  | t_typ : forall Gamma T,
      ty_wf Gamma T ->
      has_type Gamma (ttyp T) (TMem T T)

  | t_abs: forall Gamma T1 T2 t,
      ty_wf Gamma T1 ->
      has_type (T1 :: Gamma) (open_tm' Gamma t) (open' Gamma T2) ->
      has_type Gamma (tabs T1 t) (TAll T1 T2)

  | t_app : forall Gamma t1 t2 T1 T2,
      has_type Gamma t1 (TAll T1 T2) ->
      open' Gamma T2 = T2 ->
      has_type Gamma t2 T1 ->
      has_type Gamma (tapp t1 t2) T2

  | t_dapp : forall Gamma t x T1 T2,
      has_type Gamma t (TAll T1 T2) ->
      has_type Gamma (tvar (varF x)) T1 ->
      has_type Gamma (tapp t (tvar (varF x))) (open x T2)

  (* | t_and : forall Gamma x T1 T2, *)
  (*     has_type Gamma (tvar (varF x)) T1 -> *)
  (*     has_type Gamma (tvar (varF x)) T2 -> *)
  (*     has_type Gamma (tvar (varF x)) (TAnd T1 T2) *)

  (* | t_var_pack : forall Gamma x T, *)
  (*     ty_wf Gamma (TBind T) ->  *)
  (*     has_type Gamma (tvar (varF x)) (open (varF x) T) ->  *)
  (*     has_type Gamma (tvar (varF x)) (TBind T) *)

  (* | t_unpack : forall Gamma t1 t2 T1 T1' T2, *)
  (*     has_type Gamma t1 (TBind T1) -> *)
  (*     T1' = (open (varF (length Gamma)) T1) -> *)
  (*     has_type (T1' :: Gamma) t2 T2 -> *)
  (*     has_type Gamma (tunpack t1 t2) T2 *)

  | t_sub: forall Gamma e T1 T2,
      has_type Gamma e T1 ->
      stp Gamma T1 T2 ->
      has_type Gamma e T2

with
  stp : tenv -> ty -> ty -> Prop :=
  | stp_top : forall Gamma T,
      ty_wf Gamma T ->
      stp Gamma T TTop

  | stp_bot : forall Gamma T,
      ty_wf Gamma T ->
      stp Gamma TBot T

  | stp_mem : forall Gamma S1 S2 T1 T2,
      stp Gamma S2 S1 ->
      stp Gamma T1 T2 ->
      stp Gamma (TMem S1 T1) (TMem S2  T2)

  | stp_sel1 : forall Gamma x T,
      has_type Gamma (tvar (varF x)) (TMem T TTop) ->
      stp Gamma T (TSel (varF x))

  | stp_sel2 : forall Gamma x T,
      has_type Gamma (tvar (varF x)) (TMem TBot T) ->
      stp Gamma (TSel (varF x)) T

  | stp_selx : forall Gamma x T1 T2,
      has_type Gamma (tvar (varF x)) (TMem T1 T2) ->
      stp Gamma (TSel (varF x)) (TSel (varF x))

  | stp_all : forall Gamma S1 S2 T1 T2,
      stp Gamma S2 S1 ->
      stp (S2 :: Gamma) (open' Gamma T1) (open' Gamma T2) ->
      stp Gamma (TAll S1 T1) (TAll S2 T2)

  | stp_trans : forall Gamma S T U,
      stp Gamma S T ->
      stp Gamma T U ->
      stp Gamma S U

  (* TODO subtyping for recursive types and intersections *)
.


(* ### Evaluation (Big-Step Semantics) ### *)

Inductive Result : Type :=
| Done   : vl -> Result
| Error  : Result
| NoFuel : Result
.

Fixpoint eval(fuel : nat)(gamma : venv)(t : tm){struct fuel}: Result :=
  match fuel with
  | 0   => NoFuel
  | S n =>
    match t with
    | tvar (varF x) =>
      match (indexr x gamma) with
      | Some v => Done v
      | None   => Error
      end
    | tvar (varB x) =>
      match (indexl x gamma) with
      | Some v => Done v
      | None => Error
      end
    | ttyp T    => Done (vty gamma T)
    | tabs T t  => Done (vabs gamma T t)
    | tapp t1 t2 =>
      match eval n gamma t2 with
      | Done v2 =>
        match eval n gamma t1 with
        | Done (vabs gamma' _ t) => eval n (v2 :: gamma') t
        | Done _  => Error
        | err => err
        end
      | err => err
      end
    (* | tunpack t1 t2 => *)
    (*   match eval n gamma t1 with *)
    (*   | Done v1 => eval n (v1 :: gamma) t2 *)
    (*   | err => err *)
    (*   end *)
    end
  end.

Definition evaln gamma e v := exists nm, forall n, n > nm -> eval n gamma e = Done v.


(* ### Semantic Interpretation of Types (Logical Relations) ### *)

Fixpoint tsize_flat(T: ty) :=
  match T with
    | TTop => 1
    | TBot => 1
    | TAll T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | TSel _ => 1
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

Definition Dom := vl -> Prop.

Definition subset (D1 D2 : Dom) : Prop := forall v, D1 v -> D2 v.
Notation "D1 ⊆ D2" := (subset D1 D2) (at level 75).
Notation "v ∈ D" := (D v) (at level 75).
Notation "⟨ H , v ⟩ ∈ D" := (D H v) (at level 75).

Definition denv := list Dom.

Definition Sem := denv -> ty -> Dom.

Definition TOP : Dom := fun _ => True.
Definition BOT : Dom := fun _ => False.

Definition TSEL (x : id) (ρ : denv) : Dom :=
  match indexr x ρ with
    | Some D => D
    | None   => BOT
  end.

Variable val_term : vl -> tm. (* TODO turns value into syntactic closed term*)

Definition TMEM (D1 D2 : Dom) : Dom :=
  fun v =>
    match v with
    | (vty γ T) => exists X, D1 ⊆ X /\ X ⊆ D2 /\ (forall v, v ∈ X -> has_type [] (val_term v) T) (* TODO fix the side condition *)
    | _         => False
    end.

Definition ℰ (ty_interp : Sem) (ρ : denv) (T : ty) (γ : venv) (t : tm) : Prop :=
  exists k, exists v, eval k γ t = Done v /\ v ∈ (ty_interp ρ T).

Definition TALL (ty_interp : Sem) (ρ : denv) (T1 T2 : ty) : Dom :=
  fun v =>
    match v with
    | vabs γ _ t =>
      let D := (ty_interp ρ T1) in
      forall v, v ∈ D -> ⟨ (v :: γ) , t ⟩ ∈ (ℰ (ty_interp) (D :: ρ) (open' γ T2))
    | _          => False
    end.

(* idea: can syntactic opening be interpreted by semantic env extension as in NbE?*)

Definition ty_interp (ty_interp' : Sem) (ρ : denv) (T : ty) : Dom :=
  match T with
  | TTop          => TOP
  | TBot          => BOT
  | TAll T1 T2    => TALL (ty_interp') ρ T1 T2
  | TSel (varF x) => TSEL x ρ (* TODO what about varB? *)
  | TMem T1 T2    => TMEM (ty_interp' ρ T1) (ty_interp' ρ T2)
  | _             => BOT
  end.

(* TODO construct the fixpoint *)
Fail Fixpoint val_type (ρ : denv) (T : ty) : Dom := ty_interp (val_type) ρ T.
