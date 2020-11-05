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
| tvar    : id  -> tm
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

(* Fixpoint open_rec_tm (k : nat) (u : var) (t : tm) {struct t} : tm := *)
(*   match t with *)
(*   | tvar   (varF x) => tvar (varF x) *)
(*   | tvar   (varB x) => if beq_nat k x then tvar u else tvar (varB x) *)
(*   | ttyp    T       => ttyp    (open_rec k u T) *)
(*   | tabs    T  t    => tabs    (open_rec k u T)     (open_rec_tm (S k) u t) *)
(*   | tapp    t1 t2   => tapp    (open_rec_tm k u t1) (open_rec_tm k u t2) *)
(*   (* | tunpack t1 t2   => tunpack (open_rec_tm k u t1) (open_rec_tm (S k) u t2) *) *)
(*   end *)
(* . *)

(* Definition open_tm (n : nat) t := open_rec_tm 0 (varF n) t. *)
(* Definition open_tm' {A : Type} (env : list A) t := open_rec_tm 0 (varF (length env)) t. *)


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
      has_type Γ (tvar x) (TMem T1 T2) ->
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
      has_type Γ (tvar x) T

  | t_typ : forall Γ T,
      ty_wf Γ T ->
      has_type Γ (ttyp T) (TMem T T)

  | t_abs: forall Γ T1 T2 t,
      ty_wf Γ T1 ->
      has_type (T1 :: Γ) t (open' Γ T2) ->
      has_type Γ (tabs T1 t) (TAll T1 T2)

  | t_app : forall Γ t1 t2 T1 T2,
      has_type Γ t1 (TAll T1 T2) ->
      open' Γ T2 = T2 ->
      has_type Γ t2 T1 ->
      has_type Γ (tapp t1 t2) T2

  | t_dapp : forall Γ t x T1 T2,
      has_type Γ t (TAll T1 T2) ->
      has_type Γ (tvar x) T1 ->
      has_type Γ (tapp t (tvar x)) (open x T2)

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
      has_type Γ (tvar x) (TMem T TTop) ->
      stp Γ T (TSel (varF x))

  | stp_sel2 : forall Γ x T,
      has_type Γ (tvar x) (TMem TBot T) ->
      stp Γ (TSel (varF x)) T

  | stp_selx : forall Γ x T1 T2,
      has_type Γ (tvar x) (TMem T1 T2) ->
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

Scheme has_type_stp_mut := Induction for has_type Sort Prop
with stp_has_type_mut := Induction for stp Sort Prop.

Combined Scheme ind_derivations from has_type_stp_mut, stp_has_type_mut.
(* TODO the combined scheme is too weak, need proper induction over derivations, e.g.,
sometines there is no induction hypothesis applicable for subderivations revealed by inversion..
 *)

Lemma ctx_wf_from_ty_wf   : forall Γ T,     ty_wf Γ T      -> ctx_wf Γ
with  ty_wf_from_has_type : forall Γ t T,   has_type Γ t T -> ty_wf Γ T
with  ty_wf_from_stp      : forall Γ T1 T2, stp Γ T1 T2    -> ty_wf Γ T1 /\ ty_wf Γ T2.
Admitted.


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
    | tvar x =>
      match (indexr x γ) with
      | Some v => Done v
      | None   => Error
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

Lemma eval_monotone : forall {m t γ v}, eval m γ t = Done v -> forall n, m <= n -> eval n γ t = Done v.
Proof.
  induction m; intros.
  - inversion H.
  - destruct n. lia.
    destruct t; try solve [inversion H; eauto]; try lia.
    inversion H.
    simpl.
    remember (eval m γ t2) as t2m.
    symmetry in Heqt2m.
    remember (eval m γ t1) as t1m.
    symmetry in Heqt1m.
    destruct t2m; destruct t1m; eauto.
    apply IHm with (n := n) in Heqt2m; try lia.
    apply IHm with (n := n) in Heqt1m; try lia.
    rewrite Heqt2m. rewrite Heqt1m.
    destruct v1; eauto;
    rewrite H2.
    apply IHm with (n := n) in H2; try lia.
    rewrite H2.
    reflexivity.
    all:  inversion H2.
Qed.

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

Notation "{{ x | P }}" := (fun x => P)
  (at level 200, x ident).


Lemma subset_refl : forall X, X ⊆ X.
Proof.
  intros. unfold subset. auto.
Qed.
Hint Resolve subset_refl : dsub.

Lemma subset_trans : forall {X Y Z}, X ⊆ Y -> Y ⊆ Z -> X ⊆ Z.
Proof.
  intros. unfold subset. auto.
Qed.

Definition denv := list Dom.

Notation DTop  := (fun _ => True).
Notation DBot  := (fun _ => False).

Definition ℰ (D : Dom) (γ : venv) (t : tm) : Prop :=
  exists k, exists v, eval k γ t = Done v /\ v ∈ D.
Hint Unfold ℰ : dsub.

Variable val_term : vl -> tm. (* TODO turns value into syntactic closed term*)

(* Well-founded recursion.

   This solves the problem of Program Fixpoint unfoldings being
   incomprehensible and a proof of a manual unfolding theorem being
   unbearably slow. Kudos to Chris Casinghino, whose Coq artifact
   for the Zombie language inspired this approach.
*)

(* well-founded relation which captures the recursive calls in the interpretation val_type. *)
Inductive R : ty -> ty -> Prop :=
| RAll1  : forall {T1 T2}, R T1 (TAll T1 T2)
| RAll2  : forall {T1 T2 A} {γ : list A}, R (open' γ T2) (TAll T1 T2)
| RMem1  : forall {T1 T2}, R T1 (TMem T1 T2)
| RMem2  : forall {T1 T2}, R T2 (TMem T1 T2)
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

(* This disentangles two concerns in the logical relation *)
Inductive lvl :=
| Typ : lvl (* treat identifiers as type variable, e.g., for (vty gamma T), compute the denotation [[ T ]] *)
| Val : lvl (* treat identifier as term variables, e.g., for (vty gamma T), include it as it is. *).

Definition val_type_naked (T : ty) : (forall T', R T' T -> lvl -> denv -> Dom) -> lvl -> denv -> Dom :=
  match T with
  | TTop          => fun _ _ _ => DTop


  | TAll T1 T2    => fun val_type _ ρ =>
                       {{ '(vabs γ _ t) | let D1 := (val_type T1 RAll1 Val ρ) in
                                          let D2 := (val_type T1 RAll1 Typ ρ) in
                                          forall vx, vx ∈ D1 -> ⟨ (vx :: γ) , t  ⟩ ∈ ℰ (val_type (open' γ T2) RAll2 Val (D2 :: ρ)) }}

  | TSel (varF x) => fun _ _ ρ =>
                       match indexr x ρ with
                       | Some D => D
                       | None   => DBot
                       end

  | TMem T1 T2    => fun val_type lvl ρ =>
                       match lvl with
                       | Val => {{ '(vty gamma T) | exists X, (val_type T1 RMem1 Val ρ) ⊆ X /\ X ⊆ (val_type T2 RMem2 Val ρ) }} (* the side condition is not strictly necessary, but makes sense in the proof *)
                       (* this is the largest set between the Val interp of the bounds: ⋃ { X | [[T1]] ⊆ X ⊆ [[T2]] } *)
                       | Typ => {{ v | exists X, v ∈ X /\ (val_type T1 RMem1 Val ρ) ⊆ X /\ X ⊆ (val_type T2 RMem2 Val ρ) }}
                       end

  | _             => fun _ _ _  => DBot
  end.

Definition val_type : ty -> lvl -> denv -> Dom :=
  Fix wfR (fun _ => lvl -> denv -> Dom) val_type_naked.

(* Providing an unfolding requires extensionality. *)
Axiom extensionality : forall (A : Type) (B : A -> Type)
                              (f g : forall a : A, B a),
     (forall a : A, f a = g a) -> f = g.

Theorem val_type_extensional :
  forall (T1 : ty) (f g : forall T2 : ty, R T2 T1 -> lvl -> denv -> Dom),
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

Ltac prim_unfold_val_type :=
  unfold val_type; rewrite Fix_eq;
  [ simpl; fold val_type | apply val_type_extensional ].

Inductive 𝒞𝓉𝓍 : tenv -> denv -> Prop :=
| 𝒞𝓉𝓍_nil :
    𝒞𝓉𝓍 [] []
| 𝒞𝓉𝓍_cons : forall {Γ ρ T},
    𝒞𝓉𝓍 Γ ρ ->
    𝒞𝓉𝓍 (T :: Γ) ((val_type T Typ ρ) :: ρ)
.

Inductive ℰ𝓃𝓋 : denv -> venv -> Prop :=
| ℰ𝓃𝓋_nil :
    ℰ𝓃𝓋 [] []
| ℰ𝓃𝓋_cons : forall {γ ρ v D},
    ℰ𝓃𝓋 ρ γ ->
    v ∈ D ->
    ℰ𝓃𝓋 (D :: ρ) (v :: γ) (* TODO not compatible with new approach, need a third environment *)
.


Lemma fundamental' :  (forall {Γ t T}, has_type Γ t T -> forall{ρ}, 𝒞𝓉𝓍 Γ ρ -> forall{γ}, ℰ𝓃𝓋 ρ γ -> ⟨ γ , t ⟩ ∈ ℰ (val_type T Val ρ))
                    /\ (forall {Γ S T}, stp Γ S T     -> forall{ρ}, 𝒞𝓉𝓍 Γ ρ -> forall{γ}, ℰ𝓃𝓋 ρ γ -> (val_type S Val ρ) ⊆ (val_type T Val ρ)).
Proof.
  apply ind_derivations.
  - (* t_var *)
    intros.
    admit. (* TODO follows from consistent context/environment assumptions *)
  - (* t_typ *)
    intros Γ T Hty ρ HΓρ γ Hργ.
    unfold ℰ. unfold elem. unfold elem2. prim_unfold_val_type.
    exists 1.
    exists (vty γ T). simpl.
    split. simpl. reflexivity.
    exists (val_type T Val ρ).
    split. apply subset_refl. apply subset_refl.
  - (* t_abs *)
    intros Γ T1 T2 t wfT1 Hty IH ρ HΓρ γ Hργ.
    unfold ℰ in *. unfold elem in *. unfold elem2 in *.
    exists 1. exists (vabs γ T1 t).
    split. simpl. reflexivity.
    prim_unfold_val_type in IH.
    prim_unfold_val_type.
    intros vx vxinT1.
    assert (HextG : 𝒞𝓉𝓍 (T1 :: Γ) (val_type T1 Typ ρ :: ρ)). { (* TODO follows from consistent context/environment assumptions *)
             admit.
             }
    assert (Hextg : ℰ𝓃𝓋 (val_type T1 Typ ρ :: ρ) (vx :: γ)). { (* TODO follows from consistent context/environment assumptions *)
             admit.
    }
    specialize (IH _ HextG _ Hextg).
    destruct IH as [k [vy [evalvy vyinVtyT2 ] ]].
    exists k. exists vy. split. assumption.
    unfold elem.
    prim_unfold_val_type.
    admit. (* TODO goal and vyinVtyT2 are identical, yet not considered equal, need to have better unfolding lemmas for val_type. Look at Zombie artifact. *)
  - (* t_app *)
    intros Γ t1 t2 T1 T2 Hty1 IHt1 HT2open Hty2 IHt2 ρ HΓρ γ Hργ.
    unfold ℰ in *. unfold elem in *. unfold elem2 in *.
    specialize (IHt1 _ HΓρ _ Hργ). specialize (IHt2 _ HΓρ _ Hργ).
    destruct IHt1 as [k1 [v1 [evalv1 v1inVtyT1T2 ]]].
    destruct IHt2 as [k2 [v2 [evalv2 v2inVtyT1 ]]].
    prim_unfold_val_type in v1inVtyT1T2. destruct v1 as [ γ' T' t' | γ' T' ].
    specialize (v1inVtyT1T2 v2 v2inVtyT1).
    unfold ℰ in *. unfold elem in *. unfold elem2 in *.
    destruct v1inVtyT1T2 as [k3 [v3 [evalapp v3inVtyT2 ]]].
    exists (k1 + k2 + k3). exists v3. split.
    destruct k1; destruct k2; destruct k3; try solve [ simpl in *; discriminate].
    admit. (* TODO simple application of eval_monotone and some numbers foo *)
    unfold open' in *.
    assert (Hlen : length Γ = length γ'). {
      admit. (* consequence of context relations in assumptions *)
    }
    rewrite Hlen in *. rewrite HT2open in v3inVtyT2.
    prim_unfold_val_type.
    prim_unfold_val_type in v3inVtyT2.
    admit. (* TODO mismatch of ρ in goal and v3inVtyT2, because non-dependent fun. check proofs in ECOOP version*)
    contradiction.
  - (* t_dapp *)
    intros Γ t x T1 T2 Hty1 IHt1 Hty2 IHt2 ρ HΓρ γ Hργ.
    unfold ℰ in *. unfold elem in *. unfold elem2 in *.
    specialize (IHt1 _ HΓρ _ Hργ). specialize (IHt2 _ HΓρ _ Hργ).
    destruct IHt1 as [k1 [v1 [evalv1 v1inVtyT1T2 ]]].
    destruct IHt2 as [k2 [v2 [evalv2 v2inVtyT1 ]]].
    prim_unfold_val_type in v1inVtyT1T2. destruct v1 as [ γ' T' t' | γ' T' ].
    specialize (v1inVtyT1T2 v2 v2inVtyT1).
    unfold ℰ in *. unfold elem in *. unfold elem2 in *.
    destruct v1inVtyT1T2 as [k3 [v3 [evalapp v3inVtyT2 ]]].
    exists (k1 + k2 + k3). exists v3. split.
    destruct k1; destruct k2; destruct k3; try solve [ simpl in *; discriminate].
    admit. (* TODO simple application of eval_monotone and some numbers foo *)
    unfold open' in *. unfold open in *.
    assert (Hlen : x = length γ'). {
      admit. (* consequence of context relations in assumptions *)
    }
    rewrite Hlen in *.
    admit. (* TODO same problem as in t_app case*)
    contradiction.
  - (* t_sub *)
    intros Γ t T1 T2 Hty1 IH Hstp IHstp ρ HΓρ γ Hργ.
    unfold ℰ in *. unfold elem in *. unfold elem2 in *.
    specialize (IH _ HΓρ _ Hργ).
    destruct IH as [k [v [Heval vinVtyT1 ]]].
    exists k. exists v. split. assumption. eapply IHstp; eauto.
  (*Subtyping*)
  Admitted.

Theorem fundamental : forall {Γ t T}, has_type Γ t T -> forall{ρ}, 𝒞𝓉𝓍 Γ ρ -> forall{γ}, ℰ𝓃𝓋 ρ γ -> ⟨ γ , t ⟩ ∈ ℰ (val_type T Val ρ).
Proof.
  destruct fundamental' as [fund _ ].
  apply fund.
Qed.

Theorem  fundamental_stp : forall {Γ S T}, stp Γ S T -> forall{ρ}, 𝒞𝓉𝓍 Γ ρ -> forall{γ}, ℰ𝓃𝓋 ρ γ -> (val_type S Val ρ) ⊆ (val_type T Val ρ).
Proof.
  destruct fundamental' as [ _ fundstp ].
  apply fundstp.
Qed.

Lemma escape : forall {t T γ ρ}, ⟨ γ , t ⟩ ∈ ℰ (val_type T Val ρ) -> exists k v, eval k γ t = Done v.
Proof.
  intros.
  unfold ℰ in H.
  destruct H as [k [v [He H2]]].
  eauto.
Qed.

Theorem strong_normalization : forall {Γ t T}, has_type Γ t T -> forall{ρ}, 𝒞𝓉𝓍 Γ ρ -> forall{γ}, ℰ𝓃𝓋 ρ γ -> exists k v, eval k γ t = Done v.
Proof.
  intros.
  eapply escape.
  eapply fundamental; eauto.
Qed.
