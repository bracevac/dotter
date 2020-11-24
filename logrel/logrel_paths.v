Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Psatz. (* mainly for lia *)
Import ListNotations.

(*
  Extends the SN proof by Wang and Rompf to richer path expressions.

  Compatible with Coq 8.12.1.
*)


(* ### Syntax ### *)

Definition id := nat.

(* locally nameless for binders in types and terms *)
Inductive var : Type :=
| varF : id -> var (* free var *)
| varB : id -> var (* locally-bound variable *)
.

Inductive ty : Type :=
| TTop  : ty
| TBot  : ty
| TAll  : ty  -> ty -> ty
| TSel  : tm -> ty        (* Allow certain expressions in type selection *)
| TMem  : ty  -> ty -> ty
| TBind : ty  -> ty
| TAnd  : ty  -> ty -> ty
with tm : Type :=
| tvar    : var  -> tm
| ttyp    : ty  -> tm
| tabs    : ty  -> tm -> tm
| tapp    : tm  -> tm -> tm
| tunpack : tm  -> tm -> tm
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

Lemma indexr_length : forall {A B} {xs : list A} {ys : list B}, length xs = length ys -> forall {x}, indexr x xs = None <-> indexr x ys = None.
Proof.
  intros A B xs.
  induction xs; intros; destruct ys; split; simpl in *; intros; eauto; try lia.
  - inversion H. destruct (PeanoNat.Nat.eqb x (length xs)). discriminate.
    specialize (IHxs _ H2 x). destruct IHxs. auto.
  - inversion H. rewrite <- H2 in H0. destruct (PeanoNat.Nat.eqb x (length xs)). discriminate.
    specialize (IHxs _ H2 x). destruct IHxs. auto.
Qed.

Lemma indexr_skip : forall {A} {x : A} {xs : list A} {i}, i <> length xs -> indexr i (x :: xs) = indexr i xs.
Proof.
  intros.
  rewrite <- PeanoNat.Nat.eqb_neq in H. auto.
  simpl. rewrite H. reflexivity.
Qed.

Lemma indexr_var_some :  forall {A} {xs : list A} {i}, (exists x, indexr i xs = Some x) <-> i < length xs.
Proof.
  induction xs; intros; split; intros. inversion H. inversion H0.
  inversion H. inversion H. simpl in H0. destruct (PeanoNat.Nat.eqb i (length xs)) eqn:Heq.
  apply beq_nat_true in Heq. rewrite Heq. auto. inversion H.
  simpl in H. rewrite Heq in H. apply IHxs in H. simpl. lia.
  simpl. destruct (PeanoNat.Nat.eqb i (length xs)) eqn:Heq.
  exists a. reflexivity. apply beq_nat_false in Heq. simpl in H.
  apply IHxs. lia.
Qed.

(* easier to use for assumptions without existential quantifier *)
Lemma indexr_var_some' :  forall {A} {xs : list A} {i x}, indexr i xs = Some x -> i < length xs.
Proof.
  intros. apply indexr_var_some. exists x. auto.
Qed.

Lemma indexr_var_none :  forall {A} {xs : list A} {i}, indexr i xs = None <-> i >= length xs.
Proof.
  induction xs; intros; split; intros.
  simpl in *. lia. auto.
  simpl in H.
  destruct (PeanoNat.Nat.eqb i (length xs)) eqn:Heq.
  discriminate. apply IHxs in H. apply beq_nat_false in Heq. simpl. lia.
  assert (Hleq: i >= length xs). {
    simpl in H. lia.
  }
  apply IHxs in Hleq. rewrite <- Hleq.
  apply indexr_skip. simpl in H. lia.
Qed.

(* Look up a bound variable (deBruijn index) in env *)
Definition indexl {X : Type} (n : id) (l : list X) : option X := nth_error l n.

Inductive vl : Type :=
| vabs : list vl -> ty -> tm -> vl
| vty  : list vl -> ty -> vl
.

Definition tenv := list ty. (* Γ environment: static *)
Definition venv := list vl. (* H environment: run-time *)


Fixpoint open_rec (k: nat) (t: tm) (T: ty) { struct T }: ty :=
  match T with
    | TTop           => TTop
    | TBot           => TBot
    | TAll  T1 T2    => TAll  (open_rec k t T1)    (open_rec (S k) t T2)
    | TSel  e        => TSel  (open_rec_tm k t e)
    | TMem  T1 T2    => TMem  (open_rec k t T1)    (open_rec k t T2)
    | TBind T        => TBind (open_rec (S k) t T)
    | TAnd  T1 T2    => TAnd  (open_rec k t T1)    (open_rec k t T2)
  end

with open_rec_tm (k : nat) (t' : tm) (t : tm) {struct t} : tm :=
  match t with
  | tvar   (varF x) => tvar (varF x)
  | tvar   (varB x) => if beq_nat k x then t' else tvar (varB x)
  | ttyp    T       => ttyp    (open_rec k t' T)
  | tabs    T  t    => tabs    (open_rec k t' T)     (open_rec_tm (S k) t' t)
  | tapp    t1 t2   => tapp    (open_rec_tm k t' t1) (open_rec_tm k t' t2)
  | tunpack t1 t2   => tunpack (open_rec_tm k t' t1) (open_rec_tm (S k) t' t2)
  end
.

Definition open (t : tm) T := open_rec 0 t T.
Definition open' {A : Type} (env : list A) T := open_rec 0 (tvar (varF (length env))) T.
Definition open_tm (t' : tm) t := open_rec_tm 0 t' t.
Definition open_tm' {A : Type} (env : list A) t := open_rec_tm 0 (tvar (varF (length env))) t.

(* valid expressions that may appear in type selections *)
Inductive wf_tsel : tm -> Prop :=
| wf_tsel_var : forall x, wf_tsel (tvar x)
| wf_tsel_typ : forall T, wf_tsel (ttyp T) (*FIXME: should we also check that T is well-formed? *)
| wf_tsel_app : forall t1 t2, wf_tsel t1 -> wf_tsel t2 -> wf_tsel (tapp t1 t2)
| wf_tsel_lam : forall T t, wf_tsel t -> wf_tsel (tabs T t) (*FIXME: should we also check that T is well-formed? *)
.

Fixpoint wf_tsel_open {t} (wft : wf_tsel t) : forall {t'}, wf_tsel t' -> forall {n}, wf_tsel (open_rec_tm n t' t).
  clear wf_tsel_open. induction wft; intros; simpl.
  destruct x. constructor. destruct (Nat.eqb n i). auto.
  constructor. constructor. constructor. eauto. eauto.
  constructor. eauto.
Defined.

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

  | wf_sel : forall Γ t T1 T2,
      has_type Γ t (TMem T1 T2) ->
      wf_tsel t ->
      ty_wf Γ (TSel t)

  | wf_mem : forall Γ T1 T2,
      ty_wf Γ T1 ->
      ty_wf Γ T2 ->
      ty_wf Γ (TMem T1 T2)

  | wf_bind : forall Γ T,
      ty_wf ((TBind T) :: Γ) (open' Γ T) ->
      ty_wf Γ (TBind T)

  | wf_and : forall Γ T1 T2,
      ty_wf Γ T1 ->
      ty_wf Γ T2 ->
      ty_wf Γ (TAnd T1 T2)

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
      ty_wf Γ T2 ->
      has_type Γ t2 T1 ->
      has_type Γ (tapp t1 t2) T2

  | t_dapp : forall Γ t1 t2 T1 T2,
      has_type Γ t1 (TAll T1 T2) ->
      has_type Γ t2 T1 ->
      wf_tsel t2 ->
      has_type Γ (tapp t1 t2) (open t2 T2)

  | t_and : forall Γ x T1 T2,
      has_type Γ (tvar (varF x)) T1 ->
      has_type Γ (tvar (varF x)) T2 ->
      has_type Γ (tvar (varF x)) (TAnd T1 T2)

  | t_var_pack : forall Γ x T,
      ty_wf Γ (TBind T) ->
      has_type Γ (tvar (varF x)) (open (tvar (varF x)) T) ->
      has_type Γ (tvar (varF x)) (TBind T)

  | t_unpack : forall Γ t1 t2 T1 T1' T2,
      has_type Γ t1 (TBind T1) ->
      T1' = (open' Γ T1) ->
      ty_wf Γ T2 ->
      has_type (T1' :: Γ) (open_tm' Γ t2) T2 ->
      has_type Γ (tunpack t1 t2) T2

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
      stp Γ (TMem S1 T1) (TMem S2 T2)

  | stp_sel1 : forall Γ t T,
      has_type Γ t (TMem T TTop) ->
      wf_tsel t ->
      stp Γ T (TSel t)

  | stp_sel2 : forall Γ t T,
      has_type Γ t (TMem TBot T) ->
      wf_tsel t ->
      stp Γ (TSel t) T

  | stp_selx : forall Γ t T1 T2,
      has_type Γ t (TMem T1 T2) ->
      wf_tsel t ->
      stp Γ (TSel t) (TSel t)

  | stp_all : forall Γ S1 S2 T1 T2,
      stp Γ S2 S1 ->
      stp (S2 :: Γ) (open' Γ T1) (open' Γ T2) ->
      ty_wf Γ (TAll S1 T1) ->
      stp Γ (TAll S1 T1) (TAll S2 T2)

  | stp_bindx: forall Γ T1 T1' T2 T2',
      stp (T1' :: Γ) T1' T2' ->
      T1' = (open' Γ T1) ->
      T2' = (open' Γ T2) ->
      ty_wf Γ (TBind T1) ->
      ty_wf Γ (TBind T2) ->
      stp Γ (TBind T1) (TBind T2)

  | stp_and11: forall Γ T1 T2 T,
      stp Γ T1 T ->
      ty_wf Γ T2 ->
      stp Γ (TAnd T1 T2) T

  | stp_and12: forall Γ T1 T2 T,
      stp Γ T2 T ->
      ty_wf Γ T1 ->
      stp Γ (TAnd T1 T2) T

  | stp_and2: forall Γ T1 T2 T,
      stp Γ T T1 ->
      stp Γ T T2 ->
      stp Γ T (TAnd T1 T2)

  | stp_trans : forall Γ S T U,
      stp Γ S T ->
      stp Γ T U ->
      stp Γ S U
.
Hint Constructors ctx_wf : dsub.
Hint Constructors ty_wf : dsub.
Hint Constructors has_type : dsub.
Hint Constructors stp : dsub.

Scheme
  ctx_wf_mut := Induction for ctx_wf Sort Prop
  with
    ty_wf_mut := Induction for ty_wf Sort Prop
  with
    has_type_stp_mut := Induction for has_type Sort Prop
  with
    stp_has_type_mut := Induction for stp Sort Prop.

Combined Scheme ind_derivations from ctx_wf_mut, ty_wf_mut, has_type_stp_mut, stp_has_type_mut.

Fixpoint weaken_ctx  {Γ}     (cwf : ctx_wf Γ)       : forall {T'}, ty_wf Γ T' -> ctx_wf   (T' :: Γ)
with weaken_ty       {Γ T}   (twf : ty_wf Γ T)      : forall {T'}, ty_wf Γ T' -> ty_wf    (T' :: Γ) T
with weaken_has_type {Γ t T} (ht  : has_type Γ t T) : forall {T'}, ty_wf Γ T' -> has_type (T' :: Γ) t T
with weaken_stp      {Γ S T} (st  : stp Γ S T)      : forall {T'}, ty_wf Γ T' -> stp      (T' :: Γ) S T.
  - clear weaken_ctx. induction cwf; intros.
    + constructor. constructor. auto.
    + constructor. apply IHcwf. auto. auto.
  - clear weaken_ty. induction twf; intros; intuition.
    + constructor. apply IHtwf1. auto.
      apply IHtwf1 in twf1. apply IHtwf2 in twf1.
      admit. (* TODO: need to show that we can permute the last two entries of the context *)
    + eapply wf_sel. apply weaken_has_type. eassumption. auto. auto.
    + constructor. admit. (* TODO: need to show that we can permute the last two entries of the context *)
  - clear weaken_has_type. induction ht; intros; intuition.
    + constructor. auto. rewrite indexr_skip. auto.
      apply indexr_var_some' in H0. lia.
    + eapply t_abs. auto. admit. (* TODO: need to show that we can permute the last two entries of the context *)
    + eapply t_app. eauto. auto. auto.
    + eapply t_dapp. eauto. auto. auto.
    + eapply t_unpack. eauto. auto. auto. admit. (* TODO: moar permutation shenanigans *)
    + eapply t_sub. eauto. auto.
  - clear weaken_stp. induction st; intros; intuition.
    + eapply stp_selx. eauto. auto.
    + constructor. auto. admit. (* TODO: moar permutation shenanigans *)
      intuition.
    + subst. eapply stp_bindx.
      admit. (* TODO: moar permutation shenanigans *)
      eauto. eauto. auto. auto.
    + eapply stp_trans. eauto. auto.
Admitted.

Lemma lookup_wf : forall {Γ x T}, ctx_wf Γ -> indexr x Γ = Some T -> ty_wf Γ T.
Proof.
  intros. induction H. inversion H0. inversion H0.
  destruct (Nat.eqb x). inversion H3. subst. apply weaken_ty. auto. auto.
  eapply weaken_ty. eauto. auto.
Qed.

Fixpoint
  ty_wf_open {Γ T1 T2} (cfw : ctx_wf Γ) (wfT1 : ty_wf Γ T1) (twf : ty_wf (T1 :: Γ) (open' Γ T2)) : forall {t}, wf_tsel t -> has_type Γ t T1 -> ty_wf Γ (open t T2)
with has_type_open {Γ t T1 T2} (cfw : ctx_wf Γ) (wfT1 : ty_wf Γ T1) (ht : has_type (T1 :: Γ) t (open' Γ T2)) : forall {t'}, wf_tsel t' -> has_type Γ t' T1 -> has_type Γ (open_tm t' t) (open t' T2).
  - clear ty_wf_open. generalize dependent T1.  generalize dependent Γ. induction T2; intros; intuition.
    + unfold open. simpl. inversion twf. subst. constructor. eauto.
      unfold open' in *. unfold open in *. admit. (*TODO: this looks scary*)
Admitted.


Fixpoint ty_wf_ctx  {Γ T}   (twf : ty_wf Γ T)      : ctx_wf Γ
with has_type_ty_wf {Γ t T} (ht  : has_type Γ t T) : ctx_wf Γ * ty_wf Γ T
with stp_ty_wf      {Γ S T} (st  : stp Γ S T)      : ctx_wf Γ * ty_wf Γ S * ty_wf Γ T.
  - clear ty_wf_ctx. induction twf; auto.
    + apply has_type_ty_wf in H. destruct H. auto.
    + inversion IHtwf. auto.
  - clear has_type_ty_wf. induction ht; split; eauto; intuition.
    + eapply lookup_wf; eauto.
    + inversion b. subst. eapply ty_wf_open; eauto.
    + apply stp_ty_wf in H. intuition.
  - clear stp_ty_wf. induction st; split; eauto; intuition;
                       try solve [constructor; eauto];
                       try solve [eapply wf_sel; eauto];
                       try solve [apply has_type_ty_wf in H; intuition].
    + eauto.
    + apply has_type_ty_wf in H. destruct H. inversion t0. auto.
    + apply has_type_ty_wf in H. destruct H. inversion t0. auto.
Defined.

(* ### Evaluation (Big-Step Semantics) ### *)

Inductive Result : Type :=
| Done   : vl -> Result
| Error  : Result
| NoFuel : Result
.
(* TODO: nice to have: monadic syntax *)
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
    | tunpack t1 t2 =>
      match eval n γ t1 with
      | Done v1 => eval n (v1 :: γ) t2
      | err => err
      end
    end
  end.

Lemma eval_monotone : forall {m t γ v}, eval m γ t = Done v -> forall n, m <= n -> eval n γ t = Done v.
Proof.
  induction m; intros.
  - inversion H.
  - destruct n. lia.
    destruct t; try solve [inversion H; eauto]; try lia.
    + inversion H. simpl.
      remember (eval m γ t2) as t2m. symmetry in Heqt2m.
      remember (eval m γ t1) as t1m. symmetry in Heqt1m.
      destruct t2m; destruct t1m; eauto; try inversion H2.
      apply IHm with (n := n) in Heqt2m; try lia.
      apply IHm with (n := n) in Heqt1m; try lia.
      rewrite Heqt2m. rewrite Heqt1m.
      destruct v1; eauto. rewrite H2.
      apply IHm with (n := n) in H2; try lia.
      rewrite H2.
      reflexivity.
    + inversion H. simpl. remember (eval m γ t1) as t1m.
      symmetry in Heqt1m. destruct t1m; eauto; try inversion H2.
      apply IHm with (n := n) in Heqt1m; try lia.
      rewrite Heqt1m. rewrite H2. apply IHm; try lia. auto.
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
    | TBind T => S (tsize_flat T)
    | TAnd T1 T2 => S (tsize_flat T1 + tsize_flat T2)
  end.
Lemma open_preserves_size: forall T x j,
    tsize_flat T = tsize_flat (open_rec j (tvar (varF x)) T).
Proof.
  intros T. induction T; intros; simpl; eauto.
Qed.

Declare Scope dsub.


Fixpoint vset (n : nat): Type := match n with
                               | 0 => vl -> Prop
                               | S n => vset n -> vl -> Prop
                               end.

Definition vseta := forall n, vset n.

Notation Dom := vseta.

(* vseta membership *)
Definition vseta_mem (v:vl) (vs1: vseta) (vs2: vseta): Prop :=
  forall n, vs2 (S n) (vs1 n) v.
Notation "p ⋵ vs" := (vseta_mem (fst p) (snd p) vs) (at level 79).

Definition elem2 {A B} (γ : A) (v : B) (P : A -> B -> Prop) := P γ v.
Notation "⟨ H , v ⟩ ∈ D" := (elem2 H v D) (at level 75).
Hint Unfold elem2 : dsub.

(* Subset relation for use in comprehensions with explicit index parameter *)
Definition vset_sub_eq {n:nat}: vset n -> vset n -> Prop :=
  match n with
       | 0 => fun vs1 vs2 => forall v, (vs1 v) -> (vs2 v) (* TODO could simplify this to True under assumptions from paper *)
       | S n => fun vs1 vs2 => forall vs' v, (vs1 vs' v) -> (vs2 vs' v)
       end.

(* Subset relation closing over all n, for use in the vesta lattice, e.g., monotonicity check*)
Definition vseta_sub_eq (vs1: vseta) (vs2: vseta) :=
  forall n, vset_sub_eq (vs1 n) (vs2 n).

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

Definition vseta_big_meet (P: vseta -> Prop): vseta :=
  fun n =>
    match n with
    | 0 =>
      fun v => True
    | S n =>
      fun vsn v =>
        (forall vssn, (P vssn) -> (vssn (S n) vsn v))
    end.

(* \bigsqcap *)
Notation "⨅{{ vs | P }}" := (vseta_big_meet (fun vs => P)) (vs at level 99).

Definition vseta_big_join (P: vseta -> Prop): vseta :=
  fun n =>
    match n with
    | 0 =>
      fun v => True
    | S n =>
      fun vsn v =>
        (exists vssn, (P vssn) /\ (vssn (S n) vsn v))
    end.

(* \bigsqcup *)
Notation "⨆{{ vs | P }}" := (vseta_big_join (fun vs => P)) (vs at level 99).

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
| RAnd1  : forall {T1 T2}, R T1 (TAnd T1 T2)
| RAnd2  : forall {T1 T2}, R T2 (TAnd T1 T2)
| RBind  : forall {T A} {γ : list A}, R (open' γ T) (TBind T)
.

Hint Constructors Acc : dsub.
Hint Constructors R : dsub.

Lemma wfR' : forall n T, tsize_flat T <= n -> Acc R T.
Proof.
  induction n.
  - destruct T; intros; constructor; intros; simpl in *; inversion H0; try lia.
  - intros. destruct T; constructor; intros; simpl in *; inversion H0; subst; apply IHn; try lia.
    unfold open'. rewrite <- open_preserves_size. lia. unfold open'. rewrite <- open_preserves_size.
    lia.
Defined.

Theorem wfR : well_founded R.
Proof.
  red. intros T. eapply wfR'. auto.
Defined.

Definition denv := list Dom.

Definition ℰ (D : Dom) (γ : venv) (t : tm) : Prop :=
  exists k v, eval k γ t = Done v /\ exists vs, (v, vs) ⋵ D.
Hint Unfold ℰ : dsub.

Definition val_type_naked (T : ty) : (forall T', R T' T -> denv -> Dom) -> denv -> Dom :=
  match T with
  | TTop          => fun _ _ => vseta_top


  | TAll T1 T2    => fun val_type ρ =>
                      {{ '(vabs γ _ t) D n | forall vx Dx, (vx, Dx) ⋵ (val_type T1 RAll1 ρ) ->
                                                      ⟨ (vx :: γ) , t  ⟩ ∈ ℰ (val_type (open' γ T2) RAll2 (Dx :: ρ))  }}

  | TSel (tvar (varF x)) => fun _ ρ => (* todo general expression evaluation *)
                       match indexr x ρ with
                       | Some D => D
                       | None   => vseta_bot
                       end

  | TMem T1 T2    => fun val_type ρ =>
                      {{ '(vty γ T) D n | (val_type T1 RMem1 ρ n) ⊑# D /\ D ⊑# (val_type T2 RMem2 ρ n) }}

  | TBind T       => fun val_type ρ =>
                      {{ v D n | exists X, X n = D /\ (val_type (open' ρ T) RBind (X :: ρ) (S n) D v) }}

  | TAnd T1 T2    => fun val_type ρ =>
                      (val_type T1 RAnd1 ρ) ⊓ (val_type T2 RAnd2 ρ)
  | _             => fun _ _  => vseta_bot
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

Ltac prim_unfold_val_type :=
  unfold val_type; rewrite Fix_eq;
  [ simpl; fold val_type | apply val_type_extensional ].

Lemma val_type_extend : forall {T 𝓁 ρ E}, val_type T 𝓁 ρ === val_type T 𝓁 (E :: ρ).
Proof.
  unfold subset.
  induction T as [T IHT] using (well_founded_induction wfR).
  intros. destruct T; auto.
  - (* TAll *)
    split; intros; destruct v as [ γ T' t | γ T' ]; prim_unfold_val_type in H; prim_unfold_val_type; auto; intros;
      unfold elem in *; unfold elem2 in *;
        eapply (IHT _ RAll1) in H0; apply H in H0; unfold ℰ in *;
          destruct H0 as [k [vv [Heval HvxinT2]]]; exists k; exists vv; split; try assumption; unfold elem in *;
            apply (IHT _ RAll2); eapply (IHT _ RAll2) in HvxinT2.
    apply (IHT _ RAll2). assumption.
    eapply (IHT _ RAll2). eassumption.
  -  (* TSel *)
    split; intros; destruct v. prim_unfold_val_type in H.
    destruct (indexr i ρ) eqn:Hlookup1; try inversion H.
    assert (Hleq: i < length ρ). {
      eapply indexr_var_some'. eauto.
    }
    prim_unfold_val_type. apply PeanoNat.Nat.lt_neq in Hleq. rewrite <- PeanoNat.Nat.eqb_neq in Hleq.
    rewrite Hleq. rewrite Hlookup1. assumption.
    prim_unfold_val_type in H. auto.
    admit. (* TODO: have to restrict the T so that it is well-formed under ρ *)
    prim_unfold_val_type in H. auto.
  - (* TMem *)
    split; intros; destruct v as [ γ T' t | γ T' ]; prim_unfold_val_type in H; prim_unfold_val_type; auto; intros;
      unfold elem in *; unfold elem2 in *; destruct 𝓁; auto; try destruct H as [X [Helem [T1subX XsubT2]]];
        try destruct H as [X [T1subX XsubT2]]; exists X; repeat split; try assumption;
          try (apply (subset_trans XsubT2); unfold subset; apply (IHT _ RMem2 Val));
            eapply subset_trans; try eassumption; unfold subset; apply (IHT _ RMem1 Val).
Admitted.

Lemma val_type_suffix : forall {T 𝓁 ρ ρ' }, val_type T 𝓁 ρ === val_type T 𝓁 (ρ' ++ ρ).
Admitted. (* TODO also need closedness assms on T here *)

(* Env relations *)
Inductive 𝒞𝓉𝓍 : tenv -> denv -> Prop :=
| 𝒞𝓉𝓍_nil :
    𝒞𝓉𝓍 [] []
| 𝒞𝓉𝓍_cons : forall {Γ ρ T},
    𝒞𝓉𝓍 Γ ρ ->
    𝒞𝓉𝓍 (T :: Γ) ({| ValF := (val_type T Val ρ) ; TypF := (val_type T Typ ρ) |} :: ρ) (* TODO demand a subtype of T here? *)
.
Hint Constructors 𝒞𝓉𝓍 : dsub.

Inductive ℰ𝓃𝓋 : denv -> venv -> Prop :=
| ℰ𝓃𝓋_nil :
    ℰ𝓃𝓋 [] []
| ℰ𝓃𝓋_cons : forall {γ ρ v Dv Dt},
    ℰ𝓃𝓋 ρ γ ->
    v ∈ Dv ->
    ℰ𝓃𝓋 ({| ValF := Dv ; TypF := Dt |} :: ρ) (v :: γ)
.
Hint Constructors ℰ𝓃𝓋 : dsub.

(* TODO: can we put these in record types instead? *)
Definition 𝒞𝓉𝓍_Inv (x : id) (T : ty) (E : DEntry) : Prop :=
  exists Γ, exists ρ, ValF E = (val_type T Val ρ)
            /\ TypF E = (val_type T Typ ρ)
            /\ 𝒞𝓉𝓍 Γ ρ
            /\ length Γ = length ρ
            /\ length Γ = x. (*TODO should also say that the *original* context decomposes into prefix, entry, and suffix *)
Hint Unfold 𝒞𝓉𝓍_Inv : dsub.

Definition ℰ𝓃𝓋_Inv (x : id) (E : DEntry) (v : vl) : Prop :=
  exists ρ, exists γ, v ∈ ValF E
            /\ ℰ𝓃𝓋 ρ γ
            /\ length ρ = length γ
            /\ length ρ = x. (*TODO should also say that the *original* context decomposes into prefix, entry, and suffix *)
Hint Unfold ℰ𝓃𝓋_Inv : dsub.

Definition lookup_agrees {A B} (xs : list A) (ys : list B) (P : id -> A -> B -> Prop) :=
                  forall {x}, (indexr x xs = None <-> indexr x ys = None)
                              /\ (forall {a}, indexr x xs = Some a -> exists b, indexr x ys = Some b /\ P x a b).

Lemma 𝒞𝓉𝓍_length : forall {Γ ρ}, 𝒞𝓉𝓍 Γ ρ -> length Γ = length ρ.
Proof.
  intros Γ ρ HΓρ. induction HΓρ; simpl; auto.
Qed.

Lemma ℰ𝓃𝓋_length : forall {ρ γ}, ℰ𝓃𝓋 ρ γ -> length ρ = length γ.
Proof.
  intros ρ γ Hργ. induction Hργ; simpl; auto.
Qed.

Lemma lookup_𝒞𝓉𝓍 : forall {Γ ρ}, 𝒞𝓉𝓍 Γ ρ -> lookup_agrees Γ ρ 𝒞𝓉𝓍_Inv.
Proof.
  unfold lookup_agrees. unfold 𝒞𝓉𝓍_Inv.
  intros Γ ρ HΓρ x. split. apply indexr_length. apply 𝒞𝓉𝓍_length. assumption.
  induction HΓρ; intros. simpl in *. discriminate.
  assert (Hlen : length Γ = length ρ). {
    apply 𝒞𝓉𝓍_length. auto.
  }
  destruct (Nat.eqb x (length ρ)) eqn:Heqtest.
  - symmetry in Heqtest. simpl in H.
    exists {| ValF := val_type T Val ρ; TypF := val_type T Typ ρ |}.
    split. simpl. rewrite <- Heqtest. reflexivity.
    rewrite <- Hlen in Heqtest. rewrite <- Heqtest in H. inversion H. subst.
    exists Γ. exists ρ. repeat split; simpl. assumption. assumption. rewrite <- PeanoNat.Nat.eqb_eq.
    rewrite PeanoNat.Nat.eqb_sym. symmetry. assumption.
  - rewrite <- Hlen in Heqtest. simpl in H. rewrite Heqtest in H.
    specialize (IHHΓρ _ H). destruct IHHΓρ as [E [HxE Hprefix]].
    exists E. split. simpl. rewrite Hlen in Heqtest. rewrite Heqtest. assumption.
    apply Hprefix.
Qed.

Lemma lookup_ℰ𝓃𝓋 : forall {ρ γ}, ℰ𝓃𝓋 ρ γ -> lookup_agrees ρ γ ℰ𝓃𝓋_Inv.
Proof.
  unfold lookup_agrees. unfold ℰ𝓃𝓋_Inv.
  intros ρ γ Hργ x. split. apply indexr_length. apply ℰ𝓃𝓋_length. assumption.
  induction Hργ; intros. simpl in *. discriminate.
  assert (Hlen : length ρ = length γ). {
    apply ℰ𝓃𝓋_length. auto.
  }
  destruct (Nat.eqb x (length γ)) eqn:Heqtest.
  - symmetry in Heqtest. simpl in H0.
    exists v. split. simpl. rewrite <- Heqtest. reflexivity.
    rewrite <- Hlen in Heqtest. rewrite <- Heqtest in H0. inversion H0. subst.
    exists ρ. exists γ. repeat split; simpl. assumption. assumption. assumption.
    rewrite <- PeanoNat.Nat.eqb_eq. rewrite PeanoNat.Nat.eqb_sym. symmetry. assumption.
  - rewrite <- Hlen in Heqtest. simpl in H0. rewrite Heqtest in H0.
    specialize (IHHργ _ H0). destruct IHHργ as [v' [Hxv Hprefix]].
    exists v'. split. simpl. rewrite Hlen in Heqtest. rewrite Heqtest. assumption.
    apply Hprefix.
Qed.

(* TODO: tactics for dealing with environment lookup_agrees lemmas*)

Lemma fundamental' :  (forall {Γ t T}, has_type Γ t T -> forall{ρ}, 𝒞𝓉𝓍 Γ ρ -> forall{γ}, ℰ𝓃𝓋 ρ γ -> ⟨ γ , t ⟩ ∈ ℰ (val_type T Val ρ))
                    /\ (forall {Γ S T}, stp Γ S T      -> forall{ρ}, 𝒞𝓉𝓍 Γ ρ -> forall{γ}, ℰ𝓃𝓋 ρ γ -> (val_type S Val ρ) ⊆ (val_type T Val ρ)).
Proof.
  apply ind_derivations.
  - (* t_var *)
    intros Γ x T HwfG Hlookup ρ HΓρ γ Hργ.
    unfold ℰ. unfold elem. unfold elem2.
    apply lookup_𝒞𝓉𝓍 in HΓρ. unfold lookup_agrees in *. specialize (HΓρ x). destruct HΓρ as [HΓρN HΓρS].
    apply lookup_ℰ𝓃𝓋 in Hργ. unfold lookup_agrees in *. specialize (Hργ x). destruct Hργ as [HργN HργS].
    apply HΓρS in Hlookup. destruct Hlookup as [E [HxE InvGx]].
    apply HργS in HxE. destruct HxE as [v [Hxv Invrx]].
    exists 1. exists v. split. simpl. rewrite Hxv. reflexivity.
    unfold 𝒞𝓉𝓍_Inv in InvGx. destruct InvGx as [Γ0 [ρ0 [HValF HRest]]].
    (* TODO need show ρ = ρ1 ++ (x :: ρ0) from strengthened lookup_agrees lemma, then apply val_type_suffix *)
    admit.
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
    assert (HextG : 𝒞𝓉𝓍 (T1 :: Γ) ((mkD (val_type T1 Val ρ) (val_type T1 Typ ρ)) :: ρ)). { (* TODO follows from consistent context/environment assumptions *)
             admit.
             }
    assert (Hextg : ℰ𝓃𝓋 ((mkD (val_type T1 Val ρ) (val_type T1 Typ ρ)) :: ρ) (vx :: γ)). { (* TODO follows from consistent context/environment assumptions *)
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
  - (* stp_top *)
    intros Γ T HTwf ρ HΓρ γ Hργ v vinT.
    prim_unfold_val_type. auto.
  - (* stp_bot *)
    intros Γ T HTwf ρ HΓρ γ Hργ v vinBot.
    prim_unfold_val_type in vinBot.
    contradiction.
  - (* stp_mem *)
    intros Γ S1 S2 T1 T2 S2subS1 IHS2S1 T1subT2 IHT1T2 ρ HΓρ γ Hργ v vinS1T1.
    prim_unfold_val_type in vinS1T1. destruct v as [ γ' T t | γ' T ]. contradiction.
    specialize (IHS2S1 _ HΓρ _ Hργ). specialize (IHT1T2 _ HΓρ _ Hργ).
    destruct vinS1T1 as [ X [vS1subX XsubvT1 ]].
    prim_unfold_val_type. exists X. split.
    eapply subset_trans. eauto. assumption.
    eapply subset_trans. eauto. assumption.
  - (* stp_sel1 *)
    intros Γ x T Hty IH ρ HΓρ γ Hργ v vinT.
    specialize (IH _ HΓρ _ Hργ).
    unfold ℰ in *. unfold elem in *. unfold elem2 in *.
    destruct IH as [k [v' [Heval v'inTMem ]]].
    prim_unfold_val_type in v'inTMem. destruct v' as [ γ' T' t | γ' T' ]. contradiction.
    destruct v'inTMem as [X [TsubX XsubTop]].
    inversion Hty; subst.
    -- (* t_var *)
      prim_unfold_val_type.
      assert (Hrho : exists ρ', indexr x ρ = Some {| TypF := val_type (TMem T TTop) Typ ρ' ; ValF := val_type (TMem T TTop) Val ρ'    |}). { (* TODO follows from consistent context/environment assumptions *)
               admit.
      }
      destruct Hrho as [ρ' Hrho ].
      rewrite Hrho. simpl.
      assert (Hext : val_type T Val ρ' ⊆ val_type T Val ρ). { (* TODO need to show that interpretations are stable after extending ρ', maybe undo specialization of IH *)
        admit.
      }
      prim_unfold_val_type.
      exists X. repeat split. unfold elem. apply TsubX. assumption.
      eapply subset_trans. eauto. assumption.
    -- (* t_sub *)
      assert (IHty :  ⟨ γ , (tvar x) ⟩ ∈ ℰ (val_type T1 Val ρ) ). { (* TODO here we need strong induction on the typing and subtyping assumption of t_sub, need to fix the induction scheme*)
               admit.
      }
      assert (IHsub : (val_type T1 Val ρ) ⊆ (val_type (TMem T TTop) Val ρ)). {
        admit.
      }
      unfold ℰ in *. unfold elem in *. unfold elem2 in *.
      destruct IHty as [k' [v' [Heval' vinT1]]].
      prim_unfold_val_type.
      admit.

  - (* stp_sel 2*)
    intros Γ x T Hty IH ρ HΓρ γ Hργ v vinxType.
    specialize (IH _ HΓρ _ Hργ).
    unfold ℰ in *. unfold elem in *. unfold elem2 in *.
    destruct IH as [k [v' [Heval v'inTMem ]]].
    prim_unfold_val_type in v'inTMem. destruct v' as [ γ' T' t | γ' T' ]. contradiction.
    destruct v'inTMem as [X [BotsubX XsubT]].
    inversion Hty; subst.
    -- (* t_var *)
      assert (Hrho : exists ρ', indexr x ρ = Some {| TypF := val_type (TMem TBot T) Typ ρ' ; ValF := val_type (TMem TBot T) Val ρ'    |}). { (* TODO follows from consistent context/environment assumptions *)
               admit.
      }
      destruct Hrho as [ρ' Hrho ].
      prim_unfold_val_type in vinxType. rewrite Hrho in vinxType. simpl in vinxType.
      prim_unfold_val_type in vinxType. destruct vinxType as [X' [MemvX' [BotsubX' X'subT ]]].
      assert (Hext : val_type T Val ρ' ⊆ val_type T Val ρ). { (* TODO need to show that interpretations are stable after extending ρ'*)
        admit.
      }
      apply Hext. apply X'subT. auto.
    -- (* t_sub *)
      admit.
  - (* stp_selx *)
    intros. apply subset_refl.
  - (* stp_all *)
    intros Γ S1 S2 T1 T2 HS2S1 IHS2S1 HT1T2 IHT1T2 ρ HΓρ γ Hργ v vinAllS1T1.
    prim_unfold_val_type in vinAllS1T1. destruct v as [γ' T' t | γ' T'] eqn:Hv; try contradiction.
    prim_unfold_val_type.
    unfold ℰ in *. unfold elem in *. unfold elem2 in *.
    intros vx vxMem. assert (vxMem' := vxMem).
    specialize (IHS2S1 _ HΓρ _ Hργ). apply IHS2S1 in vxMem.
    apply vinAllS1T1 in vxMem.
    destruct vxMem as [k [vy [Heval vyinT1]]].
    exists k. exists vy. split. assumption.
    assert (Hopen1 : (open' Γ T1) = (open' γ' T1)). {
      admit.
    }
    assert (Hopen2 : (open' Γ T2) = (open' γ' T2)). {
      admit.
    }
    rewrite <- Hopen2. eapply IHT1T2.
    constructor. assumption.
    constructor. eassumption. (* TODO this is why it's annoying to carry the Env predicate *)
    unfold elem. eapply vxMem'.
    rewrite Hopen1.
    admit. (* TODO show that replacing ρ a entry with more precise one is allowed   *)
  - (* stp_trans *)
    intros Γ S T U HST IHST HTU IHTU ρ HΓρ γ Hργ v vinS.
    specialize (IHST _ HΓρ _ Hργ). specialize (IHTU _ HΓρ _ Hργ).
    eapply subset_trans; eauto. apply subset_refl.
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
