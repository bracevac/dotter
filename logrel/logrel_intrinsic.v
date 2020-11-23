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
  * renamings, weakening, subst functions
  * fix the self-references in the recursive types
  * equality for types
  * evaluator on intrinsically-scoped syntax
  * logrel and sn proofs
*)


(* ### Syntax ### *)

Definition id := nat.

Record var n := {
  var_num :> nat;
  var_mem : (var_num <? n) = true;
               }.

Definition var0 {n : nat} : var (S n).
  refine {| var_num := 0  |}.
  auto.
Defined.

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

(* TODO: generalize to heterogeneous lists *)
Inductive ctx : nat -> Type :=
| cnil  : ctx 0
| ccons : forall{n}, ctx n -> ty n -> ctx (S n)
.

Notation "∅" := cnil (at level 74).
Notation "G ;; T" := (ccons G T) (at level 75).

Fixpoint lookup {n : nat} (Γ : ctx n) (i : var n) : ty n := TTop. (*FIXME*)

Variable weaken_tm   : forall {n}, tm n -> tm (S n).
Variable weaken_ty   : forall {n}, ty n -> ty (S n).
Variable subst_tm_ty : forall {n}, tm n -> ty (S n) -> ty n.


(* valid expressions that may appear in type selections *)
Inductive wf_tsel : forall {n : nat}, tm n -> Prop :=
| wf_tsel_var : forall {n} (x : var n), wf_tsel (tvar x)
| wf_tsel_typ : forall {n} (T : ty n), wf_tsel (ttyp T) (*FIXME: should we also check that T is well-formed? *)
| wf_tsel_app : forall {n} (t1 t2 : tm n), wf_tsel t1 -> wf_tsel t2 -> wf_tsel (tapp t1 t2)
| wf_tsel_lam : forall {n} (T : ty n) (t : tm (S n)), wf_tsel t -> wf_tsel (tabs T t) (*FIXME: should we also check that T is well-formed? *)
.

Inductive has_type : forall {n : nat}, ctx n -> tm n -> ty n -> Prop :=
| t_var : forall {n} (Γ : ctx n) (x : var n),
    has_type Γ (tvar x) (lookup Γ x)

| t_typ : forall {n} (Γ : ctx n) (T : ty n),
    has_type Γ (ttyp T) (TMem T T)

| t_abs : forall {n} (Γ : ctx n) (t : tm (S n)) (T1 : ty n) (T2 : ty (S n)),
    has_type (Γ ;; T1) t T2 ->
    has_type Γ (tabs T1 t) (TAll T1 T2)

| t_app : forall {n} (Γ : ctx n) (t1 t2 : tm n) (T1 T2 : ty n),
    has_type Γ t1 (TAll T1 (weaken_ty T2)) ->
    has_type Γ t2 T1 ->
    has_type Γ (tapp t1 t2) T2

| t_dapp : forall {n} (Γ : ctx n) (t1 t2 : tm n) (T1: ty n) (T2 : ty (S n)),
    has_type Γ t1 (TAll T1 T2) ->
    has_type Γ t2 T1 ->
    wf_tsel t2 ->
    has_type Γ (tapp t1 t2) (subst_tm_ty t2 T2)

| t_and : forall {n} (Γ : ctx n) (x : var n) (T1 T2 : ty n),
    has_type Γ (tvar x) T1 ->
    has_type Γ (tvar x) T2 ->
    has_type Γ (tvar x) (TAnd T1 T2)

| t_var_pack : forall {n} (Γ : ctx n) (x : var n) (T : ty (S n)),
    has_type Γ (tvar x) (subst_tm_ty (tvar x) T) -> (* FIXME: how to express self-reference in the intrinsically-scoped style? *)
    has_type Γ (tvar x) (TBind T)

(* FIXME: how to express self-reference in the intrinsically-scoped style? have second sort of variable? *)
(* | t_unpack : forall {n} (Γ : ctx n) (t1 : tm n) (t2 : tm (S n)) (T1: ty (S n)) (T2 : ty n), *)
(*     has_type Γ t1 (TBind T1) -> *)

(*     has_type (Γ ;; (subst_tm_ty (tvar var0 n) T1)) (weaken_ty T2) -> *)
(*     has_type Γ (tunpack t1 t2) T2 *)

| t_sub: forall {n} (Γ : ctx n) (t : tm n) (T1 T2 : ty n),
      has_type Γ t T1 ->
      stp Γ T1 T2 ->
      has_type Γ t T2

with stp : forall {n : nat}, ctx n -> ty n -> ty n -> Prop :=
| stp_top : forall {n} (Γ : ctx n) (T : ty n),
      stp Γ T TTop

| stp_bot : forall {n} (Γ : ctx n) (T : ty n),
      stp Γ T TBot

| stp_mem : forall {n} (Γ : ctx n) (S1 T1 S2 T2 : ty n),
    stp Γ S2 S1 ->
    stp Γ T1 T2 ->
    stp Γ (TMem S1 T1) (TMem S2 T2)

| stp_sel1 : forall {n} (Γ : ctx n) (t : tm n) (T : ty n),
    has_type Γ t (TMem T TTop) ->
    wf_tsel t ->
    stp Γ T (TSel t)

| stp_sel2 : forall {n} (Γ : ctx n) (t : tm n) (T : ty n),
    has_type Γ t (TMem TBot T) ->
    wf_tsel t ->
    stp Γ (TSel t) T

| stp_selx : forall {n} (Γ : ctx n) (t : tm n) (T1 T2 : ty n),
    has_type Γ t (TMem T1 T2) ->
    wf_tsel t ->
    stp Γ (TSel t) (TSel t)

| stp_all : forall {n} (Γ : ctx n) (S1 S2 : ty n) (T1 T2 : ty (S n)),
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

| stp_and11: forall {n} (Γ : ctx n) (T T1 T2 : ty n),
    stp Γ T1 T ->
    stp Γ (TAnd T1 T2) T

| stp_and12: forall {n} (Γ : ctx n) (T T1 T2 : ty n),
    stp Γ T2 T ->
    stp Γ (TAnd T1 T2) T

| stp_and2: forall {n} (Γ : ctx n) (T T1 T2 : ty n),
    stp Γ T T1 ->
    stp Γ T T2 ->
    stp Γ T (TAnd T1 T2)

| stp_trans :  forall {n} (Γ : ctx n) (S T U : ty n),
    stp Γ S T ->
    stp Γ T U ->
    stp Γ S U
.

(* TODO type equality! *)
