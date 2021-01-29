Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Psatz. (* mainly for lia *)
Require Import PeanoNat.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

(*

Prove SN of a System D Calculus with general type selections using NbE, following

    Andreas Abel - Towards Normalization by Evaluation for the βη-Calculus of Constructions (FLOPS '10)

We model partial functions using the fuel-based interpreters from Amin & Rompf 2017.

We omit intersection and self-recursive types for now.
*)

Declare Scope dsub.
(* ### Syntax ### *)

Definition id := nat.

Open Scope dsub.

Inductive sort : Type :=
| star : sort
| box : sort
.

Notation "⋆" := star : dsub.
Notation "◻" := box : dsub.

Inductive tm : Type :=
| TSort   : sort -> tm
| TTop    : tm
| TBot    : tm
| TAll    : tm  -> tm   -> tm
| TSel    : tm  -> tm
| TMem    : tm  -> tm   -> tm
(* | TBind   : tm  -> tm *)
(* | TAnd    : tm  -> tm -> tm *)
| tsubst  : tm  -> subst -> tm
| tvar    : id  -> tm
| ttyp    : tm  -> tm
| tabs    : tm  -> tm    -> tm
| tapp    : tm  -> tm    -> tm
(* | tunpack : tm  -> tm -> tm *)
with subst : Type :=
| sid     : subst
| sweak   : subst
| scomp   : subst -> subst -> subst
| sext    : subst -> tm    -> subst
.

Notation "# i" := (tvar i) (at level 0) : dsub.
Coercion TSort : sort >-> tm.
Notation "[ T ]" := (sext sid T) : dsub.

Definition tenv := list tm. (* Γ environment: static *)

Fixpoint lookup (Γ : tenv) (i : nat) : tm :=
  match Γ, i with
  | T :: [] , 0    => (tsubst T sweak)
  | _ :: Γ , (S n) => (tsubst (lookup Γ n) sweak)
  | _ , _         => TTop (* arbitrary *)
  end.

Inductive ctx_wf : tenv -> Prop :=
| cwf_empty :
    ctx_wf []

| cwf_cons  : forall Γ (s : sort) T,
    ctx_wf Γ ->
    has_type Γ T s ->
    ctx_wf (T :: Γ)

with has_type : tenv -> tm -> tm -> Prop :=
| t_star : forall Γ,
    ctx_wf Γ ->
    has_type Γ ⋆ ◻

| t_TTop : forall Γ,
    ctx_wf Γ ->
    has_type Γ TTop ⋆

| t_TBot : forall Γ,
    ctx_wf Γ ->
    has_type Γ TBot ⋆

| t_TMem : forall Γ T1 T2,
    has_type Γ T1 ⋆ ->
    has_type Γ T2 ⋆ ->
    has_type Γ (TMem T1 T2) ⋆

| t_TAll : forall Γ T1 T2 (s s' : sort),
    has_type Γ T1 s ->
    has_type (T1 :: Γ) T2 s' ->
    has_type Γ (TAll T1 T2) s'

| t_TSel : forall Γ t T1 T2,
    has_type Γ t (TMem T1 T2) ->
    has_type Γ (TSel t) ⋆

| t_var : forall Γ x ,
    ctx_wf Γ ->
    x < length Γ ->
    has_type Γ #x (lookup Γ x)

| t_typ : forall Γ T,
    has_type Γ T ⋆ ->
    has_type Γ (ttyp T) (TMem T T)

| t_abs: forall Γ T1 T2 (s : sort) t,
    has_type (T1 :: Γ) t T2 ->
    has_type Γ (TAll T1 T2) s ->
    has_type Γ (tabs T1 t) (TAll T1 T2)

| t_app : forall Γ t1 t2 T1 T2,
    has_type Γ t1 (TAll T1 T2) ->
    has_type Γ t2 T1 ->
    has_type Γ (tapp t1 t2) (tsubst T2 [ t2 ])

(* | t_and : forall Γ x T1 T2, *)
(*     has_type Γ $x T1 -> *)
(*     has_type Γ $x T2 -> *)
(*     has_type Γ $x (TAnd T1 T2) *)

(* | t_var_pack : forall Γ x T, *)
(*     closed 0 (length Γ) (TBind T) -> *)
(*     has_type Γ $x (open $x T) -> *)
(*     has_type Γ $x (TBind T) *)

(* | t_unpack : forall Γ t1 t2 T1 T1' T2, *)
(*     has_type Γ t1 (TBind T1) -> *)
(*     T1' = (open' Γ T1) -> *)
(*     closed 0 (length Γ) T2 -> *)
(*     closed 1 (length Γ) t2 -> *)
(*     has_type (T1' :: Γ) (open' Γ t2) T2 -> *)
(*     has_type Γ (tunpack t1 t2) T2 *)

| t_subst : forall Γ σ Δ t T,
    type_subst Γ σ Δ ->
    has_type Δ t T ->
    has_type Γ (tsubst t σ) (tsubst T σ)

| t_sub: forall Γ e T1 T2,
    has_type Γ e T1 ->
    stp Γ T1 T2 ->
    has_type Γ e T2

with type_subst : tenv -> subst -> tenv -> Prop :=
| t_sid : forall Γ ,
    ctx_wf Γ ->
    type_subst Γ sid Γ

| t_sweak : forall Γ T (s : sort),
    has_type Γ T s ->
    type_subst (T :: Γ) sweak Γ

| t_sext : forall Γ σ Δ t T (s : sort),
    type_subst Γ σ Δ ->
    has_type Δ T s ->
    has_type Γ t (tsubst T σ) ->
    type_subst Γ (sext σ t) (T :: Δ)

| t_scomp : forall Γ τ Δ σ ϒ,
    type_subst Γ τ Δ ->
    type_subst Δ σ ϒ ->
    type_subst Γ (scomp σ τ) ϒ

with stp : tenv -> tm -> tm -> Prop :=
| stp_refl : forall Γ T1 T2,
    equal_tm Γ T1 T2 ⋆ ->
    stp Γ T1 T2

| stp_top : forall Γ T,
    has_type Γ T ⋆ ->
    stp Γ T TTop

| stp_bot : forall Γ T,
    has_type Γ T ⋆ ->
    stp Γ TBot T

| stp_mem : forall Γ S1 S2 T1 T2,
    stp Γ S2 S1 ->
    stp Γ T1 T2 ->
    stp Γ (TMem S1 T1) (TMem S2 T2)

| stp_sel1 : forall Γ t T,
    has_type Γ t (TMem T TTop) ->
    stp Γ T (TSel t)

| stp_sel2 : forall Γ t T,
    has_type Γ t (TMem TBot T) ->
    stp Γ (TSel t) T

| stp_selx : forall Γ t T1 T2,
    has_type Γ t (TMem T1 T2) ->
    stp Γ (TSel t) (TSel t)

| stp_all : forall Γ S1 S2 T1 T2,
    stp Γ S2 S1 ->
    stp (S2 :: Γ) T1 T2 ->
    has_type Γ (TAll S1 T1) ⋆ ->
    has_type Γ (TAll S2 T2) ⋆ ->
    stp Γ (TAll S1 T1) (TAll S2 T2)

  (* | stp_bindx: forall Γ T1 T1' T2 T2', *)
  (*     stp (T1' :: Γ) T1' T2' -> *)
  (*     T1' = (open' Γ T1) -> *)
  (*     T2' = (open' Γ T2) -> *)
  (*     closed 0 (length  Γ) (TBind T1) -> *)
  (*     closed 0 (length  Γ) (TBind T2) -> *)
  (*     stp Γ (TBind T1) (TBind T2) *)

  (* | stp_and11: forall Γ T1 T2 T, *)
  (*     stp Γ T1 T -> *)
  (*     closed 0 (length Γ) T2 -> *)
  (*     type T2 -> *)
  (*     stp Γ (TAnd T1 T2) T *)

  (* | stp_and12: forall Γ T1 T2 T, *)
  (*     stp Γ T2 T -> *)
  (*     closed 0 (length Γ) T1 -> *)
  (*     type T1 -> *)
  (*     stp Γ (TAnd T1 T2) T *)

  (* | stp_and2: forall Γ T1 T2 T, *)
  (*     stp Γ T T1 -> *)
  (*     stp Γ T T2 -> *)
  (*     stp Γ T (TAnd T1 T2) *)

| stp_trans : forall Γ S T U,
    stp Γ S T ->
    stp Γ T U ->
    stp Γ S U

with equal_tm : tenv -> tm -> tm -> tm -> Prop := (* TODO*)
| eq_refl : forall Γ t T,
    has_type Γ t T ->
    equal_tm Γ t t T

with equal_subst : tenv -> subst -> subst -> Prop := (* TODO*)
.
Hint Constructors has_type : dsub.
Hint Constructors stp : dsub.
Hint Constructors type_subst : dsub.
Hint Constructors equal_tm : dsub.
Hint Constructors equal_subst : dsub.
Hint Constructors ctx_wf : dsub.

(* syntax predicates for normal forms and neutral terms *)
Inductive Nf : tm -> Prop :=
| Nf_TSort : forall (s : sort), Nf (TSort s)
| Nf_TTop  : Nf TTop
| Nf_TBot  : Nf TBot
| Nf_TAll  : forall {T1 T2},
    Nf T1 ->
    Nf T2 ->
    Nf (TAll T1 T2)
| Nf_TMem : forall {T1 T2},
    Nf T1 ->
    Nf T2 ->
    Nf (TMem T1 T2)
| Nf_ttyp : forall {T}, (* TODO not sure if T needs to be normal*)
    Nf T ->
    Nf (ttyp T)
| Nf_tabs : forall {T t},
    Nf T ->
    Nf t ->
    Nf (tabs T t)
| Nf_Ne : forall {t},
    Ne t ->
    Nf t
with Ne : tm -> Prop :=
| Ne_var : forall x, Ne #x
| Ne_tapp : forall {t1 t2},
    Ne t1 ->
    Nf t2 ->
    Ne (tapp t1 t2)
| Ne_TSel : forall {t},
    Ne t ->
    Ne (TSel t)
.

Inductive Dom : Type :=
| DSort : sort -> Dom
| DTop  : Dom
| DBot  : Dom
| DAll  : Dom -> Dom -> Dom
| DMem  : Dom -> Dom -> Dom
| Dabs  : list Dom -> tm -> Dom
| Dtyp  : list Dom -> tm -> Dom (* TODO not sure whether closure or Dom*)
| DNe   : DomNe -> Dom
| Drefl : Dom -> DomNe -> Dom
with DomNf : Type :=
| Dreif : Dom -> Dom -> DomNf
with DomNe : Type :=
| Dvar  : id -> DomNe
| Dapp  : DomNe -> DomNf -> DomNe
| DSel  : DomNe -> DomNe
.

Notation "$ i" := (Dvar i) (at level 0) : dsub.
Coercion DSort : sort >-> Dom.

Definition denv := list Dom.

Inductive Result (T : Type) : Type :=
| Done : T -> Result T
| NoFuel : Result T
| Error : Result T
.
Arguments Done {T}.
Arguments NoFuel {T}.
Arguments Error {T}.

(* evaluation *)
Fixpoint eval (fuel : nat) (γ : denv) (t : tm) : Result Dom :=
  match fuel with
  | 0   => NoFuel
  | S n =>
    match t with
    | TSort s => Done (DSort s)
    | TTop => Done DTop
    | TBot => Done DBot
    | TAll T1 T2 =>
      match (eval n γ T1) with
      | Done D1 => Done (DAll D1 (Dabs γ T2))
      | err     => err
      end
    | TSel t =>
      match (eval n γ t) with
      | Done d => eval_sel n d
      | err    => err
      end
    | TMem T1 T2 =>
      match (eval n γ T1) with
      | Done D1 =>
        match (eval n γ T2) with
        | Done D2 => Done (DMem D1 D2)
        | err     => err
        end
      | err     => err
      end
    | tsubst t σ =>
      match (eval_subst n γ σ) with
      | Done γ' => eval n γ' t
      | Error   => Error
      | NoFuel  => NoFuel
      end
    | #x =>
      match List.nth_error γ x with
      | Some D => Done D
      | None   => Error
      end
    | ttyp T   => Done (Dtyp γ T)
    | tabs T t => Done (Dabs γ t)
    | tapp t1 t2 =>
      match (eval n γ t1) with
      | Done d1 =>
        match (eval n γ t2) with
        | Done d2 => eval_app n d1 d2
        | err     => err
        end
      | err     => err
      end
    end
  end
with eval_subst (fuel : nat) (γ : denv) (σ : subst) : Result denv :=
  match fuel with
  | 0   => NoFuel
  | S n =>
    match σ with
    | sid        => Done γ
    | sweak      =>
      match γ with
      | _ :: γ' => Done γ'
      | _      => Error
      end
    | scomp σ' τ =>
      match (eval_subst n γ τ) with
      | Done γ' => (eval_subst n γ' σ')
      | err => err
      end
    | sext σ t   =>
      match (eval_subst n γ σ) with
      | Done γ' =>
        match (eval n γ t) with
        | Done D => Done (D :: γ')
        | NoFuel => NoFuel
        | Error  => Error
        end
      | err     => err
      end
    end
  end
with eval_app (fuel : nat) (d1 d2 : Dom) : Result Dom :=
  match fuel with
  | 0   => NoFuel
  | S n =>
    match d1 with
    | Dabs γ' t => eval n (d2 :: γ') t
    | Drefl (DAll D1 D2) ne =>
      match eval_app n D2 d2 with
      | Done D2d2 => Done (Drefl D2d2 (Dapp ne (Dreif D1 d2)))
      | err       => err
      end
    | _         => Error
    end
  end
with eval_sel (fuel : nat) (d : Dom) : Result Dom :=
  match fuel with
  | 0   => NoFuel
  | S n =>
    match d with
    | Dtyp γ T => eval n γ T
    | Drefl (DMem D1 D2) ne => Done (Drefl ⋆ (DSel ne))
    | _ => Error
    end
  end.

(* readback *)
Fixpoint reify (fuel lvl : nat) (d : Dom) : Result ({ t : tm | Nf t }) :=
  match fuel with
  | 0 => NoFuel
  | S n =>
    match d with
    | DSort s => Done (exist _ _ (Nf_TSort s))
    | DTop    => Done (exist _ _ Nf_TTop)
    | DBot    => Done (exist _ _ Nf_TBot)
    | DAll D1 D2 =>
      match (reify n lvl D1) with
      | Done (exist _ _ NfT1) =>
        match (eval_app n D2 (Drefl D1 $lvl)) with
        | Done   D2x =>
          match (reify n (S lvl) D2x) with
          | Done (exist _ _ NfT2) =>
            Done (exist _ _ (Nf_TAll NfT1 NfT2))
          | err => err
          end
        | NoFuel     => NoFuel
        | Error      => Error
        end
      | err => err
      end
    | DMem D1 D2 =>
      match (reify n lvl D1) with
      | Done (exist _ _ NfT1) =>
        match (reify n lvl D2) with
        | Done (exist _ _ NfT2) =>
          Done (exist _ _ (Nf_TMem NfT1 NfT2))
        | err => err
        end
      | err => err
      end
    | Dtyp γ T =>
      match (eval n γ T) with
      | Done D =>
        match (reify n lvl D) with
        | Done (exist _ _ NfT) => Done (exist _ _ (Nf_ttyp NfT))
        | err => err
        end
      | Error  => Error
      | NoFuel => NoFuel
      end
    | DNe Dn =>
      match (reify_ne n lvl Dn) with
      | Done (exist _ _ NeN) => Done (exist _ _ (Nf_Ne NeN))
      | Error => Error
      | NoFuel => NoFuel
      end
    | _ => Error
    end
  end
with reify_nf  (fuel lvl : nat) (d : DomNf) : Result ({ t : tm | Nf t }) :=
  match fuel with
  | 0 => NoFuel
  | S n =>
    match d with
    | Dreif (DAll D1 D2) Df =>
      match (reify n lvl D1) with
      | Done (exist _ _ NfT1) =>
        match (eval_app n D2 (Drefl D1 $lvl)) with
        | Done   D2x =>
          match (eval_app n Df (Drefl D1 $lvl)) with
          | Done Dfx =>
            match (reify_nf n (S lvl) (Dreif D2x Dfx)) with
            | Done (exist _ _ Nft) =>
              Done (exist _ _ (Nf_tabs NfT1 Nft))
            | err => err
            end
          | NoFuel   => NoFuel
          | Error    => Error
          end
        | NoFuel     => NoFuel
        | Error      => Error
        end
      | err => err
      end
    | Dreif _ D => (reify n lvl D)
    end
  end
with reify_ne  (fuel lvl : nat) (d : DomNe) : Result ({ t : tm | Ne t }) :=
  match fuel with
  | 0 => NoFuel
  | S n =>
      match d with
      | $x => Done (exist _ _ (Ne_var (Nat.sub lvl (S x))))
      | Dapp nd1 d2 =>
        match (reify_ne n lvl nd1) with
        | Done (exist _ _ Net1) =>
          match (reify_nf n lvl d2) with
          | Done (exist _ _ Nft2) => Done (exist _ _ (Ne_tapp Net1 Nft2))
          | Error => Error
          | NoFuel => NoFuel
          end
        | err => err
        end
      | DSel nd => Error
      end
  end.

(* normalization *)
Fixpoint eval_ctx (fuel : nat) (Γ : tenv) : Result denv :=
  match fuel with
  | 0 => NoFuel
  | S n =>
    match Γ with
    | [] => Done []
    | T :: Γ =>
      match (eval_ctx n Γ) with
      | Done γ =>
        match (eval n γ T) with
        | Done D => Done ((Drefl D $(length Γ)) :: γ)
        | Error  => Error
        | NoFuel => NoFuel
        end
      | err => err
      end
    end
  end.

(* TODO show length Γ = length (eval_ctx n Γ) for sufficient n *)

(* term nbe *)
Definition nbe (fuel : nat) (Γ : tenv) (T t : tm) : Result ({ t : tm | Nf t }) :=
  match (eval_ctx fuel Γ) with
  | Done γ =>
    match (eval fuel γ T) with
    | Done DT =>
      match (eval fuel γ t) with
      | Done Dt => reify_nf fuel (length Γ) (Dreif DT Dt)
      | Error   => Error
      | NoFuel  => NoFuel
      end
    | Error   => Error
    | NoFuel  => NoFuel
    end
  | Error  => Error
  | NoFuel => NoFuel
  end.

(* type nbe *)
Definition Nbe (fuel : nat) (Γ : tenv) (T : tm) := nbe fuel Γ ◻ T.

(* TODO determinism and monotonicity properties for all the partial functions in this file*)
(* TODO it's high time we used monadic syntax and combinators for these *)

Theorem completeness : forall {Γ t t' T}, equal_tm Γ t t' T -> exists n nft nft', nbe n Γ T t = nft /\ nbe n Γ T t' = nft' /\ nft = nft'.
Admitted.

Corollary strong_normalization : forall {Γ t T}, has_type Γ t T -> exists n nft, nbe n Γ T t = nft.
  intros.
  pose (Heq:= completeness (eq_refl _ _ _ H)).
  destruct Heq as [n [nf [_ [norm  _]  ]]].
  exists n. exists nf. assumption.
Qed.
