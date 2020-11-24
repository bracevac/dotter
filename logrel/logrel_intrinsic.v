Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Psatz. (* mainly for lia *)
Require Import Utf8 List Basics FinFun.
Require Import Coq.Init.Nat.
Import ListNotations.

(*
  Extends the SN proof by Wang and Rompf to richer path expressions.
  This version features intrinsically-scoped syntax.

  Compatible with Coq 8.12.1.

  TODOs
  * fix the self-references in the recursive types
  * equality for types
  * evaluator on intrinsically-scoped syntax
  * logrel and sn proofs
*)


(* ### Syntax ### *)

Inductive Fin : nat -> Set :=
| FZ : forall n, Fin (S n)
| FS : forall n, Fin n -> Fin (S n)
.

Notation var := Fin.


Fixpoint var0 {n : nat} : var (S n) :=
  match n with
  | O => FZ O
  | S m => FS (S m) (@var0 m)
  end.

Inductive ty : nat -> Type :=
| TTop  : forall {n}, ty n
| TBot  : forall {n}, ty n
| TAll  : forall {n}, ty n -> ty (S n) -> ty n
| TSel  : forall {n}, tm n -> ty n
| TMem  : forall {n}, ty n -> ty n -> ty n
| TBind : forall {n}, ty (S n)  -> ty n
| TAnd  : forall {n}, ty n -> ty n -> ty n
with tm : nat -> Type :=
| tvar    : forall {n}, var n -> tm n
| ttyp    : forall {n}, ty n -> tm n
| tabs    : forall {n}, ty n -> tm (S n) -> tm n
| tapp    : forall {n}, tm n -> tm n -> tm n
| tunpack : forall {n}, tm n -> tm (S n) -> tm n
.


Inductive vec (T : nat -> Type) : nat -> Type :=
| vnil  : vec T 0
| vcons : forall{n}, vec T n -> T n -> vec T (S n)
.

Notation "∅" := vnil (at level 74).
Notation "G ;; T" := (@vcons _ _ G T) (at level 75).

(* TODO: better use the vector library from the stdlib *)
Variable lookup : forall {T : nat -> Type} {n : nat} (Γ : vec T n) (i : var n), T n.

Definition tenv := vec ty.

Definition Ren (n m : nat) : Type := var n -> var m.
Transparent Ren.

(* TODO is there any nicer way to define this? *)
Definition lift {n m : nat} (ρ : Ren n m) : Ren (S n) (S m).
  refine (fun v => _).
  inversion v as [ k | k v' ].
  apply (FZ m).
  apply (FS m (ρ v')).
Defined.

Fixpoint ren_ty {n m} (ρ : Ren n m) (T : ty n): ty m :=
  match T in ty n , ρ with
  | TTop       , ρ => TTop
  | TBot       , ρ => TBot
  | TAll  T1 T2, ρ => TAll  (ren_ty ρ T1) (ren_ty (lift ρ) T2)
  | TSel  t    , ρ => TSel  (ren_tm ρ t)
  | TMem  T1 T2, ρ => TMem  (ren_ty ρ T1) (ren_ty ρ T2)
  | TBind T    , ρ => TBind (ren_ty (lift ρ) T)
  | TAnd  T1 T2, ρ => TAnd  (ren_ty ρ T1) (ren_ty ρ T2)
  end
with ren_tm {n m} (ρ : Ren n m) (t : tm n) : tm m :=
  match t in tm n, ρ  with
  | tvar    x    , ρ => tvar    (ρ x)
  | ttyp    T    , ρ => ttyp    (ren_ty ρ T)
  | tabs    T  t , ρ => tabs    (ren_ty ρ T)  (ren_tm (lift ρ) t)
  | tapp    t1 t2, ρ => tapp    (ren_tm ρ t1) (ren_tm ρ t2)
  | tunpack t1 t2, ρ => tunpack (ren_tm ρ t1) (ren_tm (lift ρ) t2)
  end.

Definition weaken_tm {n} (t : tm n): tm (S n) := ren_tm (FS n) t.
Definition weaken_ty {n} (T : ty n): ty (S n) := ren_ty (FS n) T.

Definition Sub (n m : nat) : Type := var n -> tm m.

(* FIXME: why does this version fail? *)
(* Definition lifts (n m : nat) (σ : Sub n m) : Sub (S n) (S m) := *)
(*   fun v => *)
(*     match v in var (S n), σ return tm (S m) with *)
(*     | FZ n , σ => tvar (FZ m) *)
(*     | FS n v' , σ => weaken_tm (σ v') *)
(*     end. *)

Definition lifts {n m } (σ : Sub n m) : Sub (S n) (S m).
  refine (fun v => _).
  inversion v as [ k | k v' ].
  apply (tvar (FZ m)).
  apply (weaken_tm (σ v')).
Defined.

(* FIXME: same problems here *)
(* Definition extend {n m} (σ : Sub n m) (t : tm m) : Sub (S n) m := *)
(*   fun v => *)
(*     match v in var (S n), σ , t return tm m with *)
(*     | FZ n    , σ , t => t *)
(*     | FS n v' , σ , t => σ v' *)
(*     end. *)

Definition extend {n m} (σ : Sub n m) (t : tm m) : Sub (S n) m.
  refine (fun v => _).
  inversion v as [ k | k v' ].
  apply t.
  apply (σ v').
Defined.

Fixpoint sub_tm {n m} (σ : Sub n m) (t : tm n) : tm m :=
  match t in tm n, σ  with
  | tvar    x    , σ => (σ x)
  | ttyp    T    , σ => ttyp    (sub_tm_ty σ T)
  | tabs    T  t , σ => tabs    (sub_tm_ty σ T) (sub_tm (lifts σ) t)
  | tapp    t1 t2, σ => tapp    (sub_tm σ t1)   (sub_tm σ t2)
  | tunpack t1 t2, σ => tunpack (sub_tm σ t1)   (sub_tm (lifts σ) t2)
  end
with
sub_tm_ty {n m} (σ : Sub n m) (T : ty n) : ty m :=
  match T in ty n , σ with
  | TTop       , σ => TTop
  | TBot       , σ => TBot
  | TAll  T1 T2, σ => TAll  (sub_tm_ty σ T1) (sub_tm_ty (lifts σ) T2)
  | TSel  t    , σ => TSel  (sub_tm σ t)
  | TMem  T1 T2, σ => TMem  (sub_tm_ty σ T1) (sub_tm_ty σ T2)
  | TBind T    , σ => TBind (sub_tm_ty (lifts σ) T)
  | TAnd  T1 T2, σ => TAnd  (sub_tm_ty σ T1) (sub_tm_ty σ T2)
  end.

Definition sub1_tm    {n} (this : tm n) (there : tm (S n)) : tm n := sub_tm    (extend tvar this) there.
Definition sub1_tm_ty {n} (this : tm n) (there : ty (S n)) : ty n := sub_tm_ty (extend tvar this) there.

Notation "⟨ t1 <~ t2 ⟩"  := (sub1_tm t2 t1) (at level 75).
Notation "⟪ t1 <~ t2 ⟫" := (sub1_tm_ty t2 t1) (at level 75).

(* valid expressions that may appear in type selections *)
Inductive wf_tsel : forall {n : nat}, tm n -> Prop :=
| wf_tsel_var : forall {n} (x : var n), wf_tsel (tvar x)
| wf_tsel_typ : forall {n} (T : ty n), wf_tsel (ttyp T) (*FIXME: should we also check that T is well-formed? *)
| wf_tsel_app : forall {n} (t1 t2 : tm n), wf_tsel t1 -> wf_tsel t2 -> wf_tsel (tapp t1 t2)
| wf_tsel_lam : forall {n} (T : ty n) (t : tm (S n)), wf_tsel t -> wf_tsel (tabs T t) (*FIXME: should we also check that T is well-formed? *)
.

Inductive has_type : forall {n : nat}, tenv n -> tm n -> ty n -> Prop :=
| t_var : forall {n} (Γ : tenv n) (x : var n),
    has_type Γ (tvar x) (lookup Γ x)

| t_typ : forall {n} (Γ : tenv n) (T : ty n),
    has_type Γ (ttyp T) (TMem T T)

| t_abs : forall {n} (Γ : tenv n) (t : tm (S n)) (T1 : ty n) (T2 : ty (S n)),
    has_type (Γ ;; T1) t T2 ->
    has_type Γ (tabs T1 t) (TAll T1 T2)

| t_app : forall {n} (Γ : tenv n) (t1 t2 : tm n) (T1 T2 : ty n),
    has_type Γ t1 (TAll T1 (weaken_ty T2)) ->
    has_type Γ t2 T1 ->
    has_type Γ (tapp t1 t2) T2

| t_dapp : forall {n} (Γ : tenv n) (t1 t2 : tm n) (T1: ty n) (T2 : ty (S n)),
    has_type Γ t1 (TAll T1 T2) ->
    has_type Γ t2 T1 ->
    wf_tsel t2 ->
    has_type Γ (tapp t1 t2) (⟪ T2 <~ t2 ⟫)

| t_and : forall {n} (Γ : tenv n) (x : var n) (T1 T2 : ty n),
    has_type Γ (tvar x) T1 ->
    has_type Γ (tvar x) T2 ->
    has_type Γ (tvar x) (TAnd T1 T2)

| t_var_pack : forall {n} (Γ : tenv n) (x : var n) (T : ty (S n)),
    has_type Γ (tvar x) (⟪ T <~ (tvar x) ⟫) -> (* FIXME: how to express self-reference in the intrinsically-scoped style? *)
    has_type Γ (tvar x) (TBind T)

(* FIXME: how to express self-reference in the intrinsically-scoped style? have second sort of variable? *)
(* | t_unpack : forall {n} (Γ : tenv n) (t1 : tm n) (t2 : tm (S n)) (T1: ty (S n)) (T2 : ty n), *)
(*     has_type Γ t1 (TBind T1) -> *)

(*     has_type (Γ ;; (subst_tm_ty (tvar var0 n) T1)) (weaken_ty T2) -> *)
(*     has_type Γ (tunpack t1 t2) T2 *)

| t_sub: forall {n} (Γ : tenv n) (t : tm n) (T1 T2 : ty n),
      has_type Γ t T1 ->
      stp Γ T1 T2 ->
      has_type Γ t T2

with stp : forall {n : nat}, tenv n -> ty n -> ty n -> Prop :=
| stp_top : forall {n} (Γ : tenv n) (T : ty n),
      stp Γ T TTop

| stp_bot : forall {n} (Γ : tenv n) (T : ty n),
      stp Γ T TBot

| stp_mem : forall {n} (Γ : tenv n) (S1 T1 S2 T2 : ty n),
    stp Γ S2 S1 ->
    stp Γ T1 T2 ->
    stp Γ (TMem S1 T1) (TMem S2 T2)

| stp_sel1 : forall {n} (Γ : tenv n) (t : tm n) (T : ty n),
    has_type Γ t (TMem T TTop) ->
    wf_tsel t ->
    stp Γ T (TSel t)

| stp_sel2 : forall {n} (Γ : tenv n) (t : tm n) (T : ty n),
    has_type Γ t (TMem TBot T) ->
    wf_tsel t ->
    stp Γ (TSel t) T

| stp_selx : forall {n} (Γ : tenv n) (t : tm n) (T1 T2 : ty n),
    has_type Γ t (TMem T1 T2) ->
    wf_tsel t ->
    stp Γ (TSel t) (TSel t)

| stp_all : forall {n} (Γ : tenv n) (S1 S2 : ty n) (T1 T2 : ty (S n)),
    stp Γ S2 S1 ->
    stp (Γ ;; S2) T1 T2 ->
    stp Γ (TAll S1 T1) (TAll S2 T2)

(* FIXME: how to express self-reference in the intrinsically-scoped style? have second sort of variable? *)
(* | stp_bindx: forall Γ T1 T1' T2 T2', *)
(*     stp (T1' :: Γ) T1' T2' -> *)
(*     T1' = (open' Γ T1) -> *)
(*     T2' = (open' Γ T2) -> *)
(*     ty_wf Γ (TBind T1) -> *)
(*     ty_wf Γ (TBind T2) -> *)
(*     stp Γ (TBind T1) (TBind T2) *)

| stp_and11: forall {n} (Γ : tenv n) (T T1 T2 : ty n),
    stp Γ T1 T ->
    stp Γ (TAnd T1 T2) T

| stp_and12: forall {n} (Γ : tenv n) (T T1 T2 : ty n),
    stp Γ T2 T ->
    stp Γ (TAnd T1 T2) T

| stp_and2: forall {n} (Γ : tenv n) (T T1 T2 : ty n),
    stp Γ T T1 ->
    stp Γ T T2 ->
    stp Γ T (TAnd T1 T2)

| stp_trans :  forall {n} (Γ : tenv n) (S T U : ty n),
    stp Γ S T ->
    stp Γ T U ->
    stp Γ S U
.

(* TODO type equality! *)
