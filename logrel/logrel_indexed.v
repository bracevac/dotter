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
| TSel  : var -> ty
| TMem  : ty  -> ty -> ty
| TBind : ty  -> ty
| TAnd  : ty  -> ty -> ty
.

Inductive tm : Type :=
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

Fixpoint open_rec (k: nat) (u: var) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TBot        => TBot
    | TAll T1 T2  => TAll (open_rec k u T1) (open_rec (S k) u T2)
    | TSel (varF x) => TSel (varF x)
    | TSel (varB i) => if beq_nat k i then TSel u else TSel (varB i)
    | TMem T1 T2  => TMem (open_rec k u T1) (open_rec k u T2)
    | TBind T => TBind (open_rec (S k) u T)
    | TAnd T1 T2 => TAnd (open_rec k u T1) (open_rec k u T2)
  end.

Fixpoint open_rec_tm (k : nat) (u : var) (t : tm) {struct t} : tm :=
  match t with
  | tvar   (varF x) => tvar (varF x)
  | tvar   (varB x) => if beq_nat k x then tvar u else tvar (varB x)
  | ttyp    T       => ttyp    (open_rec k u T)
  | tabs    T  t    => tabs    (open_rec k u T)     (open_rec_tm (S k) u t)
  | tapp    t1 t2   => tapp    (open_rec_tm k u t1) (open_rec_tm k u t2)
  | tunpack t1 t2   => tunpack (open_rec_tm k u t1) (open_rec_tm (S k) u t2)
  end
.

Definition open (u : var) T := open_rec 0 u T.
Definition open' {A : Type} (env : list A) T := open_rec 0 (varF (length env)) T.
Definition open_tm (u : var) t := open_rec_tm 0 u t.
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

  | t_dapp : forall Γ t1 x T1 T2,
      has_type Γ t1 (TAll T1 T2) ->
      has_type Γ (tvar (varF x)) T1 ->
      has_type Γ (tapp t1 (tvar (varF x))) (open (varF x) T2)

  | t_and : forall Γ x T1 T2,
      has_type Γ (tvar (varF x)) T1 ->
      has_type Γ (tvar (varF x)) T2 ->
      has_type Γ (tvar (varF x)) (TAnd T1 T2)

  | t_var_pack : forall Γ x T,
      ty_wf Γ (TBind T) ->
      has_type Γ (tvar (varF x)) (open (varF x) T) ->
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
    + eapply wf_sel. apply weaken_has_type. eassumption. auto.
    + constructor. admit. (* TODO: need to show that we can permute the last two entries of the context *)
  - clear weaken_has_type. induction ht; intros; intuition.
    + constructor. auto. rewrite indexr_skip. auto.
      apply indexr_var_some' in H0. lia.
    + eapply t_abs. auto. admit. (* TODO: need to show that we can permute the last two entries of the context *)
    + eapply t_app. eauto. auto. auto.
    + eapply t_dapp. eauto. auto.
    + eapply t_unpack. eauto. auto. auto. admit. (* TODO: moar permutation shenanigans *)
    + eapply t_sub. eauto. auto.
  - clear weaken_stp. induction st; intros; intuition.
    + eapply stp_selx. eauto.
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

Fixpoint ty_wf_ctx  {Γ T}   (twf : ty_wf Γ T)      : ctx_wf Γ
with has_type_ty_wf {Γ t T} (ht  : has_type Γ t T) : ctx_wf Γ * ty_wf Γ T
with stp_ty_wf      {Γ S T} (st  : stp Γ S T)      : ctx_wf Γ * ty_wf Γ S * ty_wf Γ T.
  - clear ty_wf_ctx. induction twf; auto.
    + apply has_type_ty_wf in H. destruct H. auto.
    + inversion IHtwf. auto.
  - clear has_type_ty_wf. induction ht; split; eauto; intuition.
    + eapply lookup_wf; eauto.
    + inversion b. subst. admit. (* TODO *)
    + apply stp_ty_wf in H. intuition.
  - clear stp_ty_wf. induction st; split; eauto; intuition; eauto;
                       try solve [constructor; eauto];
                       try solve [eapply wf_sel; eauto];
                       try solve [apply has_type_ty_wf in H; intuition].
    all: apply has_type_ty_wf in H; destruct H as [wfΓ wfMem]; inversion wfMem; auto.
Admitted.

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
    | ttyp T    => Done (vty γ T)
    | tabs T t  => Done (vabs γ T t)
    | tapp t1 t2 =>
      match eval n γ t2 with
      | Done v2 =>
        match eval n γ t1 with
        | Done (vabs γ' _ t) => eval n (v2 :: γ') (open_tm' γ' t)
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
    | _ => Error
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

Lemma eval_deterministic : forall {n m t γ v1 v2}, eval n γ t = Done v1 -> eval m γ t = Done v2 -> v1 = v2.
  intros n m t γ v1 v2 Heval1 Heval2.
  apply eval_monotone with (n0 := n + m) in Heval1.
  apply eval_monotone with (n0 := n + m) in Heval2.
  rewrite Heval1 in Heval2. inversion Heval2. auto. lia. lia.
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
    tsize_flat T = tsize_flat (open_rec j (varF x) T).
Proof.
  intros T. induction T; intros; simpl; eauto.
  destruct v. auto. destruct (Nat.eqb j i); auto.
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
       | 0 => fun vs1 vs2 => True
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

Notation "D1 === D2" := (D1 ⊑ D2 /\ D2 ⊑ D1) (at level 74).
Notation "D1 ==# D2" := (D1 ⊑# D2 /\ D2 ⊑# D1) (at level 74).

Lemma seteq_refl : forall {X}, X === X.
  intuition.
Qed.
Hint Resolve seteq_refl : dsub.

Lemma seteq_sym : forall {X Y}, X === Y -> Y === X.
  intuition.
Qed.
Hint Resolve seteq_sym : dsub.

Lemma seteq_trans : forall {X Y Z}, X === Y -> Y === Z -> X === Z.
  intuition; eapply subset_trans; eauto.
Qed.

Lemma seteq'_refl : forall {n} {X : vset n}, X ==# X.
  intuition.
Qed.
Hint Resolve seteq'_refl : dsub.

Lemma seteq'_sym : forall {n} {X Y : vset n}, X ==# Y -> Y ==# X.
  intuition.
Qed.
Hint Resolve seteq'_sym : dsub.

Lemma seteq'_trans : forall {n} {X Y Z : vset n}, X ==# Y -> Y ==# Z -> X ==# Z.
  intuition; eapply subset'_trans; eauto.
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
                                                     ⟨ (vx :: γ) , (open_tm' γ t)  ⟩ ∈ ℰ (val_type (open' γ T2) RAll2 (Dx :: ρ))  }}

  | TSel (varF x) => fun _ ρ =>
                       match indexr x ρ with
                       | Some D => D
                       | None   => vseta_bot
                       end

  | TMem T1 T2    => fun val_type ρ =>
                      {{ '(vty γ T) D n | (val_type T1 RMem1 ρ n) ⊑# D /\ D ⊑# (val_type T2 RMem2 ρ n) }}

  | TBind T       => fun val_type ρ =>
                      ⨆{{ X | X ⊑ (val_type (open' ρ T) RBind (X :: ρ)) }}
                      (* {{ v D n | exists X, X n = D /\ (val_type (open' ρ T) RBind (X :: ρ) (S n) D v) }} *)

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
  [ simpl in H; repeat fold val_type in H | apply val_type_extensional ].

Ltac prim_unfold_val_type :=
  unfold val_type; rewrite Fix_eq;
  [ simpl; repeat fold val_type | apply val_type_extensional ].


(* Lemma val_type_extend : forall {T 𝓁 ρ E}, val_type T 𝓁 ρ === val_type T 𝓁 (E :: ρ). *)
(* Proof. *)
(*   unfold subset. *)
(*   induction T as [T IHT] using (well_founded_induction wfR). *)
(*   intros. destruct T; auto. *)
(*   - (* TAll *) *)
(*     split; intros; destruct v as [ γ T' t | γ T' ]; prim_unfold_val_type in H; prim_unfold_val_type; auto; intros; *)
(*       unfold elem in *; unfold elem2 in *; *)
(*         eapply (IHT _ RAll1) in H0; apply H in H0; unfold ℰ in *; *)
(*           destruct H0 as [k [vv [Heval HvxinT2]]]; exists k; exists vv; split; try assumption; unfold elem in *; *)
(*             apply (IHT _ RAll2); eapply (IHT _ RAll2) in HvxinT2. *)
(*     apply (IHT _ RAll2). assumption. *)
(*     eapply (IHT _ RAll2). eassumption. *)
(*   -  (* TSel *) *)
(*     split; intros; destruct v. prim_unfold_val_type in H. *)
(*     destruct (indexr i ρ) eqn:Hlookup1; try inversion H. *)
(*     assert (Hleq: i < length ρ). { *)
(*       eapply indexr_var_some'. eauto. *)
(*     } *)
(*     prim_unfold_val_type. apply PeanoNat.Nat.lt_neq in Hleq. rewrite <- PeanoNat.Nat.eqb_neq in Hleq. *)
(*     rewrite Hleq. rewrite Hlookup1. assumption. *)
(*     prim_unfold_val_type in H. auto. *)
(*     admit. (* TODO: have to restrict the T so that it is well-formed under ρ *) *)
(*     prim_unfold_val_type in H. auto. *)
(*   - (* TMem *) *)
(*     split; intros; destruct v as [ γ T' t | γ T' ]; prim_unfold_val_type in H; prim_unfold_val_type; auto; intros; *)
(*       unfold elem in *; unfold elem2 in *; destruct 𝓁; auto; try destruct H as [X [Helem [T1subX XsubT2]]]; *)
(*         try destruct H as [X [T1subX XsubT2]]; exists X; repeat split; try assumption; *)
(*           try (apply (subset_trans XsubT2); unfold subset; apply (IHT _ RMem2 Val)); *)
(*             eapply subset_trans; try eassumption; unfold subset; apply (IHT _ RMem1 Val). *)
(* Admitted. *)

(* Lemma val_type_suffix : forall {T 𝓁 ρ ρ' }, val_type T 𝓁 ρ === val_type T 𝓁 (ρ' ++ ρ). *)
(* Admitted. (* TODO also need closedness assms on T here *) *)

(* Env relations *)
Inductive 𝒞𝓉𝓍 : tenv -> denv -> venv -> Prop :=
| 𝒞𝓉𝓍_nil :
    𝒞𝓉𝓍 [] [] []
| 𝒞𝓉𝓍_cons : forall {Γ ρ γ T v D},
    𝒞𝓉𝓍 Γ ρ γ  ->
    (v, D) ⋵ (val_type T ρ) ->
    𝒞𝓉𝓍 (T :: Γ) (D :: ρ) (v :: γ)
.
Hint Constructors 𝒞𝓉𝓍 : dsub.

(* TODO: can we put these in record types instead? *)
(* Definition 𝒞𝓉𝓍_Inv (x : id) (T : ty) (E : DEntry) : Prop := *)
(*   exists Γ, exists ρ, ValF E = (val_type T Val ρ) *)
(*             /\ TypF E = (val_type T Typ ρ) *)
(*             /\ 𝒞𝓉𝓍 Γ ρ *)
(*             /\ length Γ = length ρ *)
(*             /\ length Γ = x. (*TODO should also say that the *original* context decomposes into prefix, entry, and suffix *) *)
(* Hint Unfold 𝒞𝓉𝓍_Inv : dsub. *)

(* Definition ℰ𝓃𝓋_Inv (x : id) (E : DEntry) (v : vl) : Prop := *)
(*   exists ρ, exists γ, v ∈ ValF E *)
(*             /\ ℰ𝓃𝓋 ρ γ *)
(*             /\ length ρ = length γ *)
(*             /\ length ρ = x. (*TODO should also say that the *original* context decomposes into prefix, entry, and suffix *) *)
(* Hint Unfold ℰ𝓃𝓋_Inv : dsub. *)

(* Definition lookup_agrees {A B} (xs : list A) (ys : list B) (P : id -> A -> B -> Prop) := *)
(*                   forall {x}, (indexr x xs = None <-> indexr x ys = None) *)
(*                               /\ (forall {a}, indexr x xs = Some a -> exists b, indexr x ys = Some b /\ P x a b). *)

(* Lemma 𝒞𝓉𝓍_length : forall {Γ ρ}, 𝒞𝓉𝓍 Γ ρ -> length Γ = length ρ. *)
(* Proof. *)
(*   intros Γ ρ HΓρ. induction HΓρ; simpl; auto. *)
(* Qed. *)

(* Lemma ℰ𝓃𝓋_length : forall {ρ γ}, ℰ𝓃𝓋 ρ γ -> length ρ = length γ. *)
(* Proof. *)
(*   intros ρ γ Hργ. induction Hργ; simpl; auto. *)
(* Qed. *)

(* Lemma lookup_𝒞𝓉𝓍 : forall {Γ ρ}, 𝒞𝓉𝓍 Γ ρ -> lookup_agrees Γ ρ 𝒞𝓉𝓍_Inv. *)
(* Proof. *)
(*   unfold lookup_agrees. unfold 𝒞𝓉𝓍_Inv. *)
(*   intros Γ ρ HΓρ x. split. apply indexr_length. apply 𝒞𝓉𝓍_length. assumption. *)
(*   induction HΓρ; intros. simpl in *. discriminate. *)
(*   assert (Hlen : length Γ = length ρ). { *)
(*     apply 𝒞𝓉𝓍_length. auto. *)
(*   } *)
(*   destruct (Nat.eqb x (length ρ)) eqn:Heqtest. *)
(*   - symmetry in Heqtest. simpl in H. *)
(*     exists {| ValF := val_type T Val ρ; TypF := val_type T Typ ρ |}. *)
(*     split. simpl. rewrite <- Heqtest. reflexivity. *)
(*     rewrite <- Hlen in Heqtest. rewrite <- Heqtest in H. inversion H. subst. *)
(*     exists Γ. exists ρ. repeat split; simpl. assumption. assumption. rewrite <- PeanoNat.Nat.eqb_eq. *)
(*     rewrite PeanoNat.Nat.eqb_sym. symmetry. assumption. *)
(*   - rewrite <- Hlen in Heqtest. simpl in H. rewrite Heqtest in H. *)
(*     specialize (IHHΓρ _ H). destruct IHHΓρ as [E [HxE Hprefix]]. *)
(*     exists E. split. simpl. rewrite Hlen in Heqtest. rewrite Heqtest. assumption. *)
(*     apply Hprefix. *)
(* Qed. *)

(* Lemma lookup_ℰ𝓃𝓋 : forall {ρ γ}, ℰ𝓃𝓋 ρ γ -> lookup_agrees ρ γ ℰ𝓃𝓋_Inv. *)
(* Proof. *)
(*   unfold lookup_agrees. unfold ℰ𝓃𝓋_Inv. *)
(*   intros ρ γ Hργ x. split. apply indexr_length. apply ℰ𝓃𝓋_length. assumption. *)
(*   induction Hργ; intros. simpl in *. discriminate. *)
(*   assert (Hlen : length ρ = length γ). { *)
(*     apply ℰ𝓃𝓋_length. auto. *)
(*   } *)
(*   destruct (Nat.eqb x (length γ)) eqn:Heqtest. *)
(*   - symmetry in Heqtest. simpl in H0. *)
(*     exists v. split. simpl. rewrite <- Heqtest. reflexivity. *)
(*     rewrite <- Hlen in Heqtest. rewrite <- Heqtest in H0. inversion H0. subst. *)
(*     exists ρ. exists γ. repeat split; simpl. assumption. assumption. assumption. *)
(*     rewrite <- PeanoNat.Nat.eqb_eq. rewrite PeanoNat.Nat.eqb_sym. symmetry. assumption. *)
(*   - rewrite <- Hlen in Heqtest. simpl in H0. rewrite Heqtest in H0. *)
(*     specialize (IHHργ _ H0). destruct IHHργ as [v' [Hxv Hprefix]]. *)
(*     exists v'. split. simpl. rewrite Hlen in Heqtest. rewrite Heqtest. assumption. *)
(*     apply Hprefix. *)
(* Qed. *)

(* TODO: tactics for dealing with environment lookup_agrees lemmas*)

Lemma fundamental     : (forall {Γ t T}, has_type Γ t T -> forall{ρ γ}, 𝒞𝓉𝓍 Γ ρ γ -> ⟨ γ , t ⟩ ∈ ℰ (val_type T ρ))
with  fundamental_stp : (forall {Γ S T}, stp Γ S T      -> forall{ρ γ}, 𝒞𝓉𝓍 Γ ρ γ -> (val_type S ρ) ⊑ (val_type T ρ)).
Proof.
  - clear fundamental. intros Γ t T Hty. induction Hty; intros ρ γ HΓργ; unfold ℰ in *; unfold elem2 in *.
    + (* t_var *)
      admit.
      (* apply lookup_𝒞𝓉𝓍 in HΓρ. unfold lookup_agrees in *. specialize (HΓρ x). destruct HΓρ as [HΓρN HΓρS]. *)
      (* apply lookup_ℰ𝓃𝓋 in Hργ. unfold lookup_agrees in *. specialize (Hργ x). destruct Hργ as [HργN HργS]. *)
      (* apply HΓρS in Hlookup. destruct Hlookup as [E [HxE InvGx]]. *)
      (* apply HργS in HxE. destruct HxE as [v [Hxv Invrx]]. *)
      (* exists 1. exists v. split. simpl. rewrite Hxv. reflexivity. *)
      (* unfold 𝒞𝓉𝓍_Inv in InvGx. destruct InvGx as [Γ0 [ρ0 [HValF HRest]]]. *)
    + (* t_typ *)
      exists 1. exists (vty γ T). split. simpl. auto. exists (val_type T ρ). unfold vseta_mem.
      intros. simpl. prim_unfold_val_type. apply seteq'_refl.
    + (* t_abs *)
      exists 1. exists (vabs γ T1 t). split. simpl. reflexivity.
      exists vseta_top. unfold vseta_mem. prim_unfold_val_type. unfold vseta_mem. intros n vx Dx vxDxinT1.
      unfold ℰ in *; unfold elem2 in *.
      assert (HOt : (open_tm' γ t) = (open_tm' Γ t)). {
        admit. (* TODO: consequence of env assms *)
      }
      assert (HOT2 : (open' γ T2) = (open' Γ T2)). {
        admit. (* TODO: consequence of env assms *)
      }
      rewrite HOt. rewrite HOT2. apply IHHty.
      constructor; intuition.
    + (* t_app *)
      unfold vseta_mem in *. simpl in IHHty1. simpl in IHHty2.
      specialize (IHHty1 _ _ HΓργ). specialize (IHHty2 _ _ HΓργ).
      destruct IHHty1 as [k1 [v1 [evalv1 [vs1 v1vs1inVtyT1T2 ]]]].
      destruct IHHty2 as [k2 [v2 [evalv2 [vs2 v2vs2inVtyT1]]]].
      prim_unfold_val_type in v1vs1inVtyT1T2. destruct v1 as [ γ' T' t' | γ' T' ].
      specialize (v1vs1inVtyT1T2 0 v2 vs2 v2vs2inVtyT1).
      unfold ℰ in *. unfold elem2 in *.
      destruct v1vs1inVtyT1T2 as [k3 [v3 [evalapp [vs3 v3vs3inVtyT2] ]]].
      exists (k1 + k2 + k3). exists v3. split.
      destruct k1; destruct k2; destruct k3; try solve [ simpl in *; discriminate].
      eapply eval_monotone in evalv1. eapply eval_monotone in evalapp. eapply eval_monotone in evalv2.
      simpl. erewrite evalv2. simpl. erewrite evalv1. erewrite evalapp.
      reflexivity. lia. lia. lia. exists vs3. simpl.
      assert (HT2open' : (open' γ' T2) = T2). {
        admit. (* consequence of H : ty_wf Γ T2 *)
      }
      rewrite HT2open' in *. unfold vseta_mem in *. simpl in *.
      admit. (* TODO this follows from HT2open and being able to remove the head entry in v3inVtyT (cf. val_type_extend)  *)
      contradiction.
    + (* t_dapp *)
      unfold vseta_mem in *. simpl in IHHty1. simpl in IHHty2.
      specialize (IHHty1 _ _ HΓργ). specialize (IHHty2 _ _ HΓργ).
      destruct IHHty1 as [k1 [v1 [evalv1 [vs1 v1vs1inVtyT1T2 ]]]].
      destruct IHHty2 as [k2 [v2 [evalv2 [vs2 v2vs2inVtyT1]]]].
      prim_unfold_val_type in v1vs1inVtyT1T2. destruct v1 as [ γ' T' t' | γ' T' ].
      specialize (v1vs1inVtyT1T2 0 v2 vs2 v2vs2inVtyT1).
      unfold ℰ in *. unfold elem2 in *.
      destruct v1vs1inVtyT1T2 as [k3 [v3 [evalapp [vs3 v3vs3inVtyT2] ]]].
      exists (k1 + k2 + k3). exists v3. split.
      destruct k1; destruct k2; destruct k3; try solve [ simpl in *; discriminate].
      eapply eval_monotone in evalv1. eapply eval_monotone in evalapp. eapply eval_monotone in evalv2.
      simpl. erewrite evalv2. simpl. erewrite evalv1. erewrite evalapp.
      reflexivity. lia. lia. lia. exists vs3. simpl. unfold vseta_mem in *. simpl in *.
      (* TODO We can argue that what we add something which is already *)
      (* in the environment at x, so it does not matter if we open T2 *)
      (* with x directly or the head of the runtime env γ'. For the same reason, we can
       justify taking the original ρ. Careful: in general, x does not equal |γ'|,
       so we cannot show (open' γ' T2) = (open x T2)! *)
      admit.
      contradiction.
    + (* t_and *)
      admit. (* TODO redo the invert_var lemma*)
    + (* t_var_pack *)
      specialize (IHHty _ _ HΓργ).  destruct IHHty as [k [v [evalv [vs vvsinVtyTx ]]]].
      exists k. exists v. split. auto. exists vs.
      prim_unfold_val_type. unfold vseta_mem. intros. unfold vseta_big_join.
      exists (val_type (open (varF x) T) ρ). split.
      admit. (* TODO *)
      eauto.
    + (* t_unpack *)
      simpl in IHHty1. simpl in IHHty2.
      specialize (IHHty1 _ _ HΓργ). destruct IHHty1 as [k1 [v1 [evalv1 [vs1 v1vs1inVtyT1T2 ]]]].
      remember (val_type (TBind T1) ρ) as F.
      prim_unfold_val_type in HeqF.
      admit. (* TODO *)
    + (* t_sub *)
      specialize (IHHty _ _ HΓργ).
      destruct IHHty as [k [v [Heval [vs vinVtyT1] ]]].
      exists k. exists v. split. assumption. exists vs.
      unfold vseta_mem in *. intros. specialize (vinVtyT1 n).
      specialize (fundamental_stp _ _ _ H _ _ HΓργ).
      unfold vseta_sub_eq in fundamental_stp. specialize (fundamental_stp (S n)).
      eauto.
  (* Subtyping *)
  - intros Γ S T Hst.
    induction Hst; intros ρ γ HΓργ; unfold vseta_sub_eq; intros; unfold vset_sub_eq; destruct n; intros; trivial.
    + (* stp_top *)
      prim_unfold_val_type. trivial.
    + (* stp_bot *)
      destruct H0.
    + (* stp_mem *)
      prim_unfold_val_type in H. destruct v as [ γ' T t | γ' T ]. contradiction.
      specialize (IHHst1 _ _ HΓργ n). specialize (IHHst2 _ _ HΓργ n).
      destruct H as [ S1subX XsubT1 ]. prim_unfold_val_type. split.
      eapply subset'_trans. eauto. assumption.
      eapply subset'_trans. eauto. assumption.
    + (* stp_sel1 *)
      specialize (fundamental Γ (tvar (varF x)) (TMem T TTop) H _ _ HΓργ).
      unfold elem2 in fundamental. unfold ℰ in fundamental.
      destruct fundamental as [k [vt [ evalv [ X vtXinTTop ]]]].
      unfold vseta_mem in vtXinTTop. prim_unfold_val_type in vtXinTTop.
      destruct vt as [ γ' T' t | γ' T' ]. contradiction.
      inversion H; subst.
      -- (* t_var *)
        assert (Hrho : exists D, indexr x ρ = Some D /\ ((vty γ' T'), D) ⋵ (val_type (TMem T TTop) ρ)). {
          admit.
        }
        destruct Hrho as [D [rhoD vtDinTTop]]. unfold vseta_mem in vtDinTTop. simpl in vtDinTTop.
        prim_unfold_val_type. rewrite rhoD. specialize (vtDinTTop (S n)).
        prim_unfold_val_type in vtDinTTop. intuition.
      -- (* t_sub *)
        eapply fundamental_stp in H2; eauto.
        assert (Hrho : exists D, indexr x ρ = Some D /\ ((vty γ' T'), D) ⋵ (val_type T1 ρ)). {
          admit.
        }
        destruct Hrho as [D [rhoD vtDinT1]]. unfold vseta_mem in vtDinT1. simpl in vtDinT1.
        prim_unfold_val_type. rewrite rhoD.
        unfold vseta_sub_eq in H2. specialize (H2 (S (S n))). specialize (vtDinT1 (S n)).
        unfold vset_sub_eq in H2. apply H2 in vtDinT1. prim_unfold_val_type in vtDinT1.
        intuition.
    + (* stp_sel2 *)
      specialize (fundamental Γ (tvar (varF x)) (TMem TBot T) H _ _ HΓργ).
      unfold elem2 in fundamental. unfold ℰ in fundamental.
      destruct fundamental as [k [vt [ evalv [ X vtXinBotT ]]]].
      unfold vseta_mem in vtXinBotT. prim_unfold_val_type in vtXinBotT.
      destruct vt as [ γ' T' t | γ' T' ]. contradiction.
      inversion H; subst.
      -- (* t_var *)
        assert (Hrho : exists D, indexr x ρ = Some D /\ ((vty γ' T'), D) ⋵ (val_type (TMem TBot T) ρ)). {
          admit.
        }
        destruct Hrho as [D [rhoD vtDinBotT]].
        prim_unfold_val_type in H0. rewrite rhoD in H0.
        unfold vseta_mem in vtDinBotT. simpl in vtDinBotT. specialize (vtDinBotT (S n)).
        prim_unfold_val_type in vtDinBotT. intuition.
      -- (* t_sub *)
        eapply fundamental_stp in H2; eauto.
        assert (Hrho : exists D, indexr x ρ = Some D /\ ((vty γ' T'), D) ⋵ (val_type T1 ρ)). {
          admit.
        }
        destruct Hrho as [D [rhoD vtDinT1]]. unfold vseta_mem in vtDinT1. simpl in vtDinT1.
        prim_unfold_val_type in H0. rewrite rhoD in H0.
        unfold vseta_sub_eq in H2. specialize (H2 (S (S n))). specialize (vtDinT1 (S n)).
        unfold vset_sub_eq in H2. apply H2 in vtDinT1. prim_unfold_val_type in vtDinT1.
        intuition.
    + (* stp_all *)
      prim_unfold_val_type in H0. destruct v as [γ' T' t | γ' T'] eqn:Hv; try contradiction.
      prim_unfold_val_type.
      unfold ℰ in *. unfold elem2 in *.
      intros vx Dx vxMem. assert (vxMem' := vxMem).
      specialize (IHHst1 _ _ HΓργ).
      assert (HvsDxS1 : vseta_mem vx Dx (val_type S1 ρ)). {
        (* TODO: it might be better to formulate  ⊑ in terms of vseta_mem, might save a few annoying manual steps *)
        unfold vseta_mem in *.
        intros m. specialize (IHHst1 (S m)).
        intuition.
      }
      eapply H0 in HvsDxS1. destruct HvsDxS1 as [k [vy [Heval [Dy vyinT1]]]].
      exists k. exists vy. split. assumption.
      assert (Hopen1 : (open' Γ T1) = (open' γ' T1)). {
        admit.
      }
      assert (Hopen2 : (open' Γ T2) = (open' γ' T2)). {
        admit.
      }
      rewrite <- Hopen2. exists Dy.
      unfold vseta_mem. intros m. simpl.
      unfold vseta_sub_eq in IHHst2.
      assert (HC: 𝒞𝓉𝓍 (S2 :: Γ) (Dx :: ρ) (vx :: γ)). {
        admit.
      }
      specialize (IHHst2 _ _ HC (S m)).
      apply IHHst2. rewrite Hopen1. intuition.
    + (* stp_bindx *)
      subst.
      prim_unfold_val_type in H3.
      prim_unfold_val_type.
      destruct H3 as [F [Fsub FMem]].
      exists F.
      assert (HOT1 : (open' ρ T1) = (open' Γ T1)). {
        admit. (* TODO: consequence of env assms *)
      }
      assert (HOT2 : (open' ρ T2) = (open' Γ T2)). {
        admit. (* TODO: consequence of env assms *)
      }
      rewrite HOT1 in *. rewrite HOT2 in *.
      split. eapply subset_trans. eapply Fsub.
      eapply IHHst.
      admit.
      assumption.
    + (* stp_and11 *)
      specialize (IHHst _ _ HΓργ (S n)).
      prim_unfold_val_type in H0. intuition.
    + (* stp_and12 *)
      specialize (IHHst _ _ HΓργ (S n)).
      prim_unfold_val_type in H0. intuition.
    + (* stp_and2 *)
      specialize (IHHst1 _ _ HΓργ (S n)). specialize (IHHst2 _ _ HΓργ (S n)).
      prim_unfold_val_type. intuition.
    + (* stp_trans *)
      unfold vseta_sub_eq in *.
      specialize (IHHst1 _ _ HΓργ (Datatypes.S n)). specialize (IHHst2 _ _ HΓργ (Datatypes.S n)).
      intuition.
Admitted.

Lemma escape : forall {t T γ ρ}, ⟨ γ , t ⟩ ∈ ℰ (val_type T ρ) -> exists k v, eval k γ t = Done v.
Proof.
  intros.
  unfold ℰ in H.
  destruct H as [k [v [He H2]]].
  eauto.
Qed.

Theorem strong_normalization : forall {Γ t T}, has_type Γ t T -> forall{ρ γ}, 𝒞𝓉𝓍 Γ ρ γ -> exists k v, eval k γ t = Done v.
Proof.
  intros.
  eapply escape.
  eapply fundamental; eauto.
Qed.
