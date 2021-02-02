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
  * equality for types
  * evaluator on intrinsically-scoped syntax
  * logrel and sn proofs
  * add and fix the self-references in the recursive types
*)


(* ### Syntax ### *)

Inductive Fin : nat -> Set :=
| FZ : forall {n}, Fin (S n)
| FS : forall {n}, Fin n -> Fin (S n)
.

Notation var := Fin.

Check ((fun (x : Fin 2) => x)  (FS FZ)).
Check ((fun (x : Fin 2) => x)  FZ).
Fail Check ((fun (x : Fin 2) => x)  (FS (FS FZ))).

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
(* | TBind : forall {n}, ty (S n)  -> ty n *)
| TAnd  : forall {n}, ty n -> ty n -> ty n
with tm : nat -> Type :=
| tvar    : forall {n}, var n -> tm n
| ttyp    : forall {n}, ty n -> tm n
| tabs    : forall {n}, ty n -> tm (S n) -> tm n
| tapp    : forall {n}, tm n -> tm n -> tm n
(* | tunpack : forall {n}, tm n -> tm (S n) -> tm n *)
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
  (* | TBind T    , ρ => TBind (ren_ty (lift ρ) T) *)
  | TAnd  T1 T2, ρ => TAnd  (ren_ty ρ T1) (ren_ty ρ T2)
  end
with ren_tm {n m} (ρ : Ren n m) (t : tm n) : tm m :=
  match t in tm n, ρ  with
  | tvar    x    , ρ => tvar    (ρ x)
  | ttyp    T    , ρ => ttyp    (ren_ty ρ T)
  | tabs    T  t , ρ => tabs    (ren_ty ρ T)  (ren_tm (lift ρ) t)
  | tapp    t1 t2, ρ => tapp    (ren_tm ρ t1) (ren_tm ρ t2)
  (* | tunpack t1 t2, ρ => tunpack (ren_tm ρ t1) (ren_tm (lift ρ) t2) *)
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
  (* | tunpack t1 t2, σ => tunpack (sub_tm σ t1)   (sub_tm (lifts σ) t2) *)
  end
with
sub_tm_ty {n m} (σ : Sub n m) (T : ty n) : ty m :=
  match T in ty n , σ with
  | TTop       , σ => TTop
  | TBot       , σ => TBot
  | TAll  T1 T2, σ => TAll  (sub_tm_ty σ T1) (sub_tm_ty (lifts σ) T2)
  | TSel  t    , σ => TSel  (sub_tm σ t)
  | TMem  T1 T2, σ => TMem  (sub_tm_ty σ T1) (sub_tm_ty σ T2)
  (* | TBind T    , σ => TBind (sub_tm_ty (lifts σ) T) *)
  | TAnd  T1 T2, σ => TAnd  (sub_tm_ty σ T1) (sub_tm_ty σ T2)
  end.

Definition sub1_tm    {n} (this : tm n) (there : tm (S n)) : tm n := sub_tm    (extend tvar this) there.
Definition sub1_tm_ty {n} (this : tm n) (there : ty (S n)) : ty n := sub_tm_ty (extend tvar this) there.

Notation "t1 <~ t2"  := (sub1_tm t2 t1) (at level 75).
Notation "t1 <*~ t2" := (sub1_tm_ty t2 t1) (at level 75).

(* valid expressions that may appear in type selections *)
Inductive wf_tsel : forall {n : nat}, tm n -> Prop :=
| wf_tsel_var : forall {n} (x : var n), wf_tsel (tvar x)
(* | wf_tsel_typ : forall {n} (T : ty n), wf_tsel (ttyp T) (*FIXME: should we also check that T is well-formed? *) *)
(* | wf_tsel_app : forall {n} (t1 t2 : tm n), wf_tsel t1 -> wf_tsel t2 -> wf_tsel (tapp t1 t2) *)
(* | wf_tsel_lam : forall {n} (T : ty n) (t : tm (S n)), wf_tsel t -> wf_tsel (tabs T t) (*FIXME: should we also check that T is well-formed? *) *)
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
    has_type Γ (tapp t1 t2) (T2 <*~ t2)

| t_and : forall {n} (Γ : tenv n) (x : var n) (T1 T2 : ty n),
    has_type Γ (tvar x) T1 ->
    has_type Γ (tvar x) T2 ->
    has_type Γ (tvar x) (TAnd T1 T2)

(* | t_var_pack : forall {n} (Γ : tenv n) (x : var n) (T : ty (S n)), *)
(*     has_type Γ (tvar x) (T <*~ (tvar x)) -> (* FIXME: how to express self-reference in the intrinsically-scoped style? *) *)
(*     has_type Γ (tvar x) (TBind T) *)

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

Lemma lift_id : forall {n} {v : var (S n)}, lift id v = v.
Proof.
  intros. dependent destruction v; eauto.
Qed.

Open Scope program_scope.
Lemma lift_comp : forall {n m k} {ρ : Ren n m} {ρ' : Ren m k} {v : var (S n)}, lift (ρ' ∘ ρ) v = lift ρ' (lift ρ v).
Proof.
  intros. dependent destruction v; eauto.
Qed.

(* Lemma substitution : forall {n} {Γ : tenv n} {T1 : ty n} {T2 : ty (S n)}  {t : tm (S n)}, *)
(*     has_type (Γ ;; T1) t T2 -> forall {t' : tm n}, has_type Γ t' T1 -> has_type Γ (t <~ t') (T2 <*~ t'). *)
(* Proof. *)
(*   intros n Γ T1 T2 t Hty. *)
(*   dependent induction Hty; intros. *)
(*   - admit. *)
(*   - unfold sub1_tm. unfold sub1_tm_ty. simpl. constructor. *)
(*   - unfold sub1_tm in *. unfold sub1_tm_ty in *. simpl. constructor. *)
(*     admit. *)
(*   - unfold sub1_tm. unfold sub1_tm_ty. *)

Inductive env (T : Type) : nat -> Type :=
| enil  : env T 0
| econs : forall{n}, env T n -> T -> env T (S n)
.
Arguments econs {T n}.
Arguments enil {T}.

Inductive vl : Type :=
| vabs : forall {n : nat}, env vl n -> tm (S n) -> vl
| vty :  forall {n : nat}, env vl n -> ty n -> vl
.

Definition venv := env vl.

Variable get : forall { T : Type } {n : nat}, env T n -> var n -> T.

Inductive Result : Type :=
| Done   : vl -> Result
| Error  : Result
| NoFuel : Result
.

Fixpoint eval{m : nat}(fuel : nat)(γ : venv m)(t : tm m){struct fuel}: Result :=
  match fuel with
  | 0   => NoFuel
  | S n =>
    match t, γ with
    | tvar x, γ => Done (get γ x)
    | ttyp T, γ    => Done (vty γ T)
    | tabs T t, γ  => Done (vabs γ t)
    | tapp t1 t2, γ =>
      match eval n γ t2 with
      | Done v2 =>
        match eval n γ t1 with
        | Done (vabs γ' t) => eval n (econs γ' v2) t
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

Fixpoint vset (n : nat): Type := match n with
                               | 0 => vl -> Prop
                               | S n => vset n -> vl -> Prop
                               end.

Definition vseta  := forall n, vset n.

Notation Dom := vseta.

Definition denv := env Dom.

(* vseta membership *)
Definition vseta_mem (v:vl) (vs1: vseta) (vs2: vseta): Prop :=
  forall n, vs2 (S n) (vs1 n) v.
Notation "⦑ x , y ⦒ ⋵ vs" := (vseta_mem x y vs) (at level 79).

Definition elem2 {A B} (γ : A) (v : B) (P : A -> B -> Prop) := P γ v.
Notation "⟨ H , v ⟩ ∈ D" := (elem2 H v D) (at level 75).
Hint Unfold elem2 : dsub.

(* Subset relation for use in comprehensions with explicit index parameter *)
Definition vset_sub_eq {n:nat}: vset n -> vset n -> Prop :=
  match n with
       | 0 => fun vs1 vs2 => True
       | S n => fun vs1 vs2 => forall vs' v, (vs1 vs' v) -> (vs2 vs' v)
       end.

(* Subset relation closing over all n, for use in the vesta lattice, e.g., monotonicity check*)
Definition vseta_sub_eq (vs1: vseta) (vs2: vseta) :=
  forall n, vset_sub_eq (vs1 n) (vs2 n).

Hint Unfold vset_sub_eq : dsub.
Hint Unfold vseta_sub_eq : dsub.

(* \sqsubseteq *)
Notation "vs1 ⊑# vs2" := (vset_sub_eq vs1 vs2) (at level 75).
Notation "vs1 ⊑  vs2" := (vseta_sub_eq vs1 vs2) (at level 75).

(* vseta comprehension exposing the index in the body *)
Notation "{{ ' p vs n | P }}" := (fun k =>
                                   match k with
                                   | 0   => fun _ => True
                                   | S n => fun (vs : vset n) (v : vl) =>
                                              match v with
                                              | p => P
                                              | _ => False
                                              end
                                   end)
                              (at level 0, p pattern, vs ident, n ident ).

Notation "{{ v vs n | P }}" := (fun k =>
                                   match k with
                                   | 0   => fun _ => True
                                   | S n => fun (vs : vset n) (v : vl) => P
                                   end)
                              (at level 0, v ident, vs ident, n ident ).


(* The domain vseta is a complete lattice, which we require for least and greatest fixpoints of types. *)
Definition vseta_top: vseta := {{ v vs n | True }}.

Definition vseta_bot: vseta := {{ v vs n | False }}.

Definition vseta_join (vs1: vseta) (vs2: vseta): vseta := {{ v vs n | (vs1 (S n) vs v) \/ (vs2 (S n) vs v) }}.
(* \sqcup *)
Notation "vs1 ⊔ vs2" := (vseta_join vs1 vs2) (at level 70, right associativity).

Definition vseta_meet (vs1: vseta) (vs2: vseta): vseta := {{ v vs n | (vs1 (S n) vs v) /\ (vs2 (S n) vs v) }}.
(* \sqcap *)
Notation "vs1 ⊓ vs2" := (vseta_meet vs1 vs2) (at level 65, right associativity).

Lemma subset_refl : forall X, X ⊑ X.
Proof.
  intros. unfold vseta_sub_eq. unfold vset_sub_eq. intros.
  induction n; eauto.
Qed.
Hint Resolve subset_refl : dsub.

Lemma subset_trans : forall {X Y Z}, X ⊑ Y -> Y ⊑ Z -> X ⊑ Z.
Proof.
  intros. unfold vseta_sub_eq in *. induction n.
  - specialize (H 0). specialize (H0 0). simpl. eauto.
  - simpl. intros. specialize (H (S n)). specialize (H0 (S n)).
    eauto.
Qed.

Lemma subset'_refl : forall {n} {X : vset n}, X ⊑# X.
Proof.
  intros. unfold vset_sub_eq.
  induction n; eauto.
Qed.
Hint Resolve subset'_refl : dsub.

Lemma subset'_trans : forall {n} {X Y Z : vset n}, X ⊑# Y -> Y ⊑# Z -> X ⊑# Z.
Proof.
  intros. unfold vset_sub_eq in *. induction n; eauto.
Qed.

Definition ℰ {m : nat} (D : Dom) (γ : venv m) (t : tm m) : Prop :=
  exists k v, eval k γ t = Done v /\ exists vs, ⦑ v, vs ⦒ ⋵ D.

Fixpoint val_type {m : nat} (T : ty m) (ρ : denv m) : Dom :=
  match T , ρ with
  | TTop, _          => vseta_top
  | TAll T1 T2, ρ    =>
     {{ '(vabs γ t) D n | forall vx Dx, ⦑ vx, Dx ⦒ ⋵ (val_type T1 ρ) ->
                                  ⟨ (econs γ vx) , t  ⟩ ∈ ℰ (val_type T2 (econs ρ Dx))  }}
  | TSel (tvar x), ρ => get ρ x
  | TMem T1 T2, ρ    =>
    {{ '(vty γ T) D n | (val_type T1 ρ n) ⊑# D /\ D ⊑# (val_type T2 ρ n) }}
  | TAnd T1 T2 , ρ   => (val_type T1 ρ) ⊓ (val_type T2 ρ)
  | _ , _            => vseta_bot (* we only have this case because we allow arbitrary t in TSel *)
  end.


Inductive 𝒞𝓉𝓍 : forall {n : nat}, (tenv n) -> (denv n) -> (venv n) -> Prop :=
| 𝒞𝓉𝓍_nil :
    𝒞𝓉𝓍 (vnil ty) enil enil
| 𝒞𝓉𝓍_cons : forall {n : nat } {Γ : tenv n} {ρ : denv n} { γ : venv n } {T : ty n} {v D},
    𝒞𝓉𝓍 Γ ρ γ  ->
    ⦑ v, D ⦒ ⋵ (val_type T ρ) ->
    𝒞𝓉𝓍 (Γ ;; T) (econs ρ D) (econs γ v)
.

Lemma fundamental     : (forall {n : nat} {Γ : tenv n} {t : tm n} {T : ty n}, has_type Γ t T -> forall{ρ : denv n} {γ : venv n}, 𝒞𝓉𝓍 Γ ρ γ -> ⟨ γ , t ⟩ ∈ ℰ (val_type T ρ))
with  fundamental_stp : (forall {n : nat} {Γ : tenv n} {S T : ty n}, stp Γ S T -> forall{ρ : denv n} {γ : venv n}, 𝒞𝓉𝓍 Γ ρ γ -> (val_type S ρ) ⊑ (val_type T ρ)).
Proof.
  - clear fundamental. intros m Γ t T Hty. dependent induction Hty; intros ρ γ HΓργ; unfold ℰ in *; unfold elem2 in *.
    + (* t_var *)
      exists 1. exists (get γ x). intuition. exists (get ρ x). admit. (* TODO this is exactly a reasonable lookup lemma *)
    + (* t_typ *)
      exists 1. exists (vty γ T). intuition. exists (val_type T ρ). unfold vseta_mem.
      intros m. simpl. split; apply subset'_refl.
    + (* t_abs *)
      exists 1. exists (vabs γ t). intuition. exists vseta_top. unfold vseta_mem.
      intros m. simpl. intros.
      assert (Hext: 𝒞𝓉𝓍 (Γ;; T1) (econs ρ Dx) (econs γ vx)) by (constructor; eauto).
      apply IHHty in Hext. destruct Hext as [k [vy [Heval [vsy vyvsyT2 ]]]].
      unfold elem2. unfold ℰ. exists k. exists vy. intuition. exists vsy. auto.
    + (* t_app *)
      specialize (IHHty1 _ _ HΓργ). specialize (IHHty2 _ _ HΓργ).
      destruct IHHty1 as [k1 [v1 [evalv1 [vs1 v1vs1inVtyT1T2 ]]]].
      destruct IHHty2 as [k2 [v2 [evalv2 [vs2 v2vs2inVtyT1]]]].
      specialize (v1vs1inVtyT1T2 0). simpl in v1vs1inVtyT1T2.
      destruct v1 as [ i γ' t' | i γ' T' ]; intuition.
      apply v1vs1inVtyT1T2 in v2vs2inVtyT1. unfold elem2 in *. unfold ℰ in *.
      destruct v2vs2inVtyT1 as [k3 [v3 [evalapp [vs3 v3vs3inVtyT2] ]]].
      exists (k1 + k2 + k3). exists v3. split. admit. (* TODO: need to show monotonicity of eval *)
      exists vs3. admit. (* that should be a relatively easy lemma *)
    + (* t_dapp *)
      specialize (IHHty1 _ _ HΓργ). specialize (IHHty2 _ _ HΓργ).
      destruct IHHty1 as [k1 [v1 [evalv1 [vs1 v1vs1inVtyT1T2 ]]]].
      destruct IHHty2 as [k2 [v2 [evalv2 [vs2 v2vs2inVtyT1]]]].
      specialize (v1vs1inVtyT1T2 0). simpl in v1vs1inVtyT1T2.
      destruct v1 as [ i γ' t' | i γ' T' ]; intuition.
      apply v1vs1inVtyT1T2 in v2vs2inVtyT1. unfold elem2 in *. unfold ℰ in *.
      destruct v2vs2inVtyT1 as [k3 [v3 [evalapp [vs3 v3vs3inVtyT2] ]]].
      exists (k1 + k2 + k3). exists v3. split. admit. (* TODO: need to show monotonicity of eval *)
      exists vs3. (* TODO: this one is trickier, maybe first do the original system with single variables in selections? *)
Admitted.
