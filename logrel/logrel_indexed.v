Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Psatz. (* mainly for lia *)
Import ListNotations.

(*
  Recreation of Wang and Rompf's SN proof.

  Differences:

  - Locally nameless for terms also, to prepare for extending the path syntax.
  - Overall more high level with definitions that are easier relatable
    to pen and paper formulation.
  - Standard formulation of fundamental lemma for typing and subtyping.
  - Makes clear that self-recursive types have greatest fixpoint semantics.
  - Logical relation definition (val_type) with better performance, using Coq's
    well-founded recursion library.

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

Lemma indexr_head : forall {A} {x : A} {xs}, indexr (length xs) (x :: xs) = Some x.
  intros. simpl. destruct (Nat.eqb (length xs) (length xs)) eqn:Heq. auto.
  apply beq_nat_false in Heq. contradiction.
Qed.

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

Inductive vl : Type :=
| vabs : list vl -> ty -> tm -> vl
| vty  : list vl -> ty -> vl
.

Definition tenv := list ty. (* Γ environment: static *)
Definition venv := list vl. (* H environment: run-time *)

Fixpoint open_rec (k: nat) (u: var) (T: ty) { struct T }: ty :=
  match T with
  | TTop           => TTop
  | TBot           => TBot
  | TAll  T1 T2    => TAll (open_rec k u T1) (open_rec (S k) u T2)
  | TSel  (varF x) => TSel (varF x)
  | TSel  (varB i) => if beq_nat k i then TSel u else TSel (varB i)
  | TMem  T1 T2    => TMem  (open_rec k u T1)    (open_rec k u T2)
  | TBind T        => TBind (open_rec (S k) u T)
  | TAnd  T1 T2    => TAnd  (open_rec k u T1)    (open_rec k u T2)
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

Lemma open_rec_commute : forall T i j x y, i <> j -> open_rec i (varF x) (open_rec j (varF y) T) = open_rec j (varF y) (open_rec i (varF x) T).
  induction T; intros; simpl; eauto;
  try solve [rewrite IHT1; eauto; rewrite IHT2; eauto].
  destruct v. intuition.
  destruct (Nat.eqb i i0) eqn:Hii0; destruct (Nat.eqb j i0) eqn:Hji0; simpl;
    try rewrite Hii0; try rewrite Hji0; auto.
  apply beq_nat_true in Hii0. apply beq_nat_true in Hji0. subst. contradiction.
  rewrite IHT; intuition.
Qed.

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

  | stp_sel1 : forall Γ x T1 T,
      indexr x Γ = Some T1 ->
      stp Γ T1 (TMem T TTop) ->
      stp Γ T (TSel (varF x))

  | stp_sel2 : forall Γ x T1 T,
      indexr x Γ = Some T1 ->
      stp Γ T1 (TMem TBot T) ->
      stp Γ (TSel (varF x)) T

  | stp_selx : forall Γ x T1 T2,
      has_type Γ (tvar (varF x)) (TMem T1 T2) ->
      stp Γ (TSel (varF x)) (TSel (varF x))

  | stp_all : forall Γ S1 S2 T1 T2,
      stp Γ S2 S1 ->
      stp (S2 :: Γ) (open' Γ T1) (open' Γ T2) ->
      ty_wf Γ (TAll S1 T1) ->
      ty_wf Γ (TAll S2 T2) ->
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

Inductive closed_ty: nat(*B*) -> nat(*F*) -> ty -> Prop :=
| cl_top: forall b f,
    closed_ty b f TTop
| cl_bot: forall b f,
    closed_ty b f TBot
| cl_all: forall b f T1 T2,
    closed_ty b f T1 ->
    closed_ty (S b) f T2 ->
    closed_ty b f (TAll T1 T2)
| cl_sel_f: forall b f x,
    x < f ->
    closed_ty b f (TSel (varF x))
| cl_sel_b: forall b f x,
    x < b ->
    closed_ty b f (TSel (varB x))
| cl_mem: forall b f T1 T2,
    closed_ty b f T1 ->
    closed_ty b f T2 ->
    closed_ty b f (TMem T1 T2)
| cl_bind: forall b f T,
    closed_ty (S b) f T ->
    closed_ty b f (TBind T)
| cl_and: forall b f T1 T2,
    closed_ty b f T1 ->
    closed_ty b f T2 ->
    closed_ty b f (TAnd T1 T2)
.

Inductive closed_tm: nat(*B*) -> nat(*F*) -> tm -> Prop :=
| cl_tvarb: forall b f x,
    x < b ->
    closed_tm b f (tvar (varB x))
| cl_tvarf: forall b f x,
    x < f ->
    closed_tm b f (tvar (varF x))
| cl_ttyp:  forall b f T,
    closed_ty b f T ->
    closed_tm b f (ttyp T)
| cl_tabs:  forall b f T tm,
    closed_ty b f T ->
    closed_tm (S b) f tm ->
    closed_tm b f (tabs T tm)
| cl_tapp:  forall b f tm1 tm2,
    closed_tm b f tm1 ->
    closed_tm b f tm2 ->
    closed_tm b f (tapp tm1 tm2)
| cl_tunpack: forall b f tm1 tm2,
    closed_tm b f tm1 ->
    closed_tm (S b) f tm2 ->
    closed_tm b f (tunpack tm1 tm2)
.
Hint Constructors closed_ty : dsub.
Hint Constructors closed_tm : dsub.

Lemma closed_ty_monotone : forall {b f T}, closed_ty b f T -> forall {b' f'}, b <= b' -> f <= f' -> closed_ty b' f' T.
  intros b f T H.
  induction H; intros; intuition.
Qed.

Lemma closed_tm_monotone : forall {b f t}, closed_tm b f t -> forall {b' f'}, b <= b' -> f <= f' -> closed_tm b' f' t.
  intros b f t H.
  induction H; intros; intuition.
  constructor. eapply closed_ty_monotone; eauto.
  constructor. eapply closed_ty_monotone; eauto.
  intuition.
Qed.

Lemma closed_ty_varb : forall {b f x}, x < b <-> closed_ty b f (TSel (varB x)).
  intuition. inversion H. auto.
Qed.

Lemma closed_ty_varf : forall {b f x}, x < f <-> closed_ty b f (TSel (varF x)).
  intuition. inversion H. auto.
Qed.

Lemma closed_tm_varb : forall {b f x}, x < b <-> closed_tm b f (tvar (varB x)).
  intuition. inversion H. auto.
Qed.

Lemma closed_tm_varf : forall {b f x}, x < f <-> closed_tm b f (tvar (varF x)).
  intuition. inversion H. auto.
Qed.

Lemma has_type_var_length : forall {Γ x T}, has_type Γ (tvar (varF x)) T -> x < length Γ.
  intros. dependent induction H; eauto.
  apply indexr_var_some' in H0. auto.
Qed.

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
    + eapply stp_sel1. rewrite indexr_skip. eauto. apply indexr_var_some' in H. lia.
      eauto.
    + eapply stp_sel2. rewrite indexr_skip. eauto. apply indexr_var_some' in H. lia.
      eauto.
    + eapply stp_selx. eauto.
    + constructor. auto. admit. (* TODO: moar permutation shenanigans *)
      intuition. intuition.
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
    + inversion b. subst. admit. (* TODO has_type Γ (tvar (varF x)) T1 -> x < length Γ,  *)
    + apply stp_ty_wf in H. intuition.
  - clear stp_ty_wf. induction st; split; eauto; intuition; eauto;
                       try solve [constructor; eauto];
                       try solve [inversion b; auto];
                       try solve [eapply wf_sel; eauto];
                       try solve [apply has_type_ty_wf in H; intuition].
    eapply wf_sel. eapply t_sub. apply t_var. auto. eauto. eauto.
    eapply wf_sel. eapply t_sub. apply t_var. auto. eauto. eauto.
Admitted.

Fixpoint ty_wf_closed {Γ T}   (twf : ty_wf Γ T)      : closed_ty 0 (length Γ) T
with has_type_closed  {Γ t T} (ht  : has_type Γ t T) : closed_tm 0 (length Γ) t * closed_ty 0 (length Γ) T
with stp_closed       {Γ S T} (stp : stp Γ S T)      : closed_ty 0 (length Γ) S * closed_ty 0 (length Γ) T.
  - clear ty_wf_closed. induction twf; intuition.
    + constructor. auto. admit. (* TODO need to relate closed and opening *)
    + constructor. inversion H; subst. apply indexr_var_some' in H3. auto.
      apply has_type_closed in H. destruct H as [cx  _ ]. inversion cx. auto.
    + admit. (* TODO need to relate closed and opening *)
  - clear has_type_closed. induction ht; intuition.
    + apply indexr_var_some' in H0. intuition.
    + apply lookup_wf in H0. intuition. auto.
    + constructor. intuition. admit. (* TODO need to relate closed and opening *)
    + constructor. intuition. admit. (* TODO need to relate closed and opening *)
    + inversion b. subst. admit.
    + constructor. intuition. admit.
    + apply stp_closed in H. intuition.
  - clear stp_closed. induction stp; intuition.
    + inversion b. intuition.
    + constructor. apply indexr_var_some' in H. auto.
    + constructor. apply indexr_var_some' in H. auto.
    + inversion b. intuition.
    + apply has_type_closed in H. destruct H as [cx _]. inversion cx. intuition.
    + apply has_type_closed in H. destruct H as [cx _]. inversion cx. intuition.
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

Lemma closed_ty_open : forall {n T}, tsize_flat T < n -> forall {b f}, closed_ty (S b) f T -> forall {x}, x < f -> closed_ty b f (open_rec b (varF x) T).
  induction n; destruct T; intros; simpl in H; intuition;
    try solve [simpl; inversion H0; subst; constructor; apply IHn; intuition].
  simpl. destruct v. inversion H0. intuition.
  destruct (Nat.eqb b i) eqn:Heq. intuition.
  apply closed_ty_varb. inversion H0. subst.
  apply beq_nat_false in Heq. lia.
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

(* Logical Relation *)

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
  exists k v, eval k γ t = Done v /\ exists vs, ⦑ v, vs ⦒ ⋵ D.
Hint Unfold ℰ : dsub.

Definition val_type_naked (T : ty) : (forall T', R T' T -> denv -> Dom) -> denv -> Dom :=
  match T with
  | TTop          => fun _ _ => vseta_top


  | TAll T1 T2    => fun val_type ρ =>
                      {{ '(vabs γ _ t) D n | closed_ty 0 (length ρ) T1 /\ closed_ty 1 (length ρ) T2 /\
                                            forall vx Dx, ⦑ vx, Dx ⦒ ⋵ (val_type T1 RAll1 ρ) ->
                                                     ⟨ (vx :: γ) , (open_tm' γ t)  ⟩ ∈ ℰ (val_type (open' ρ T2) RAll2 (Dx :: ρ))  }}

  | TSel (varF x) => fun _ ρ =>
                       match indexr x ρ with
                       | Some D => D
                       | None   => vseta_bot
                       end

  | TMem T1 T2    => fun val_type ρ =>
                      {{ '(vty γ T) D n | closed_ty 0 (length ρ) T1 /\ closed_ty 0 (length ρ) T2 /\ (val_type T1 RMem1 ρ n) ⊑# D /\ D ⊑# (val_type T2 RMem2 ρ n) }}

  | TBind T       => fun val_type ρ =>
                      ⨆{{ X | X ⊑ (val_type (open' ρ T) RBind (X :: ρ)) /\ closed_ty 1 (length ρ) T }}
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
Tactic Notation "unfold_val_type" "in" hyp(H) :=
  unfold val_type in H; rewrite Fix_eq in H;
  [ simpl in H; repeat fold val_type in H | apply val_type_extensional ].

Ltac unfold_val_type :=
  unfold val_type; rewrite Fix_eq;
  [ simpl; repeat fold val_type | apply val_type_extensional ].

(* Env relations *)
Inductive 𝒞𝓉𝓍 : tenv -> denv -> venv -> Prop :=
| 𝒞𝓉𝓍_nil :
    𝒞𝓉𝓍 [] [] []
| 𝒞𝓉𝓍_cons : forall {Γ ρ γ T v D},
    𝒞𝓉𝓍 Γ ρ γ  ->
    ⦑ v, D ⦒ ⋵ (val_type T ρ) ->
    𝒞𝓉𝓍 (T :: Γ) (D :: ρ) (v :: γ)
.
Hint Constructors 𝒞𝓉𝓍 : dsub.

Lemma 𝒞𝓉𝓍_length : forall {Γ ρ γ}, 𝒞𝓉𝓍 Γ ρ γ -> length Γ = length γ /\ length γ = length ρ.
  intros Γ ρ γ C. induction C; simpl; intuition.
Qed.

Lemma 𝒞𝓉𝓍_lengthρ : forall {Γ ρ γ}, 𝒞𝓉𝓍 Γ ρ γ -> length Γ = length ρ.
  intros Γ ρ γ C. apply 𝒞𝓉𝓍_length in C. intuition.
Qed.

Lemma 𝒞𝓉𝓍_lengthγ : forall {Γ ρ γ}, 𝒞𝓉𝓍 Γ ρ γ -> length Γ = length γ.
  intros Γ ρ γ C. apply 𝒞𝓉𝓍_length in C. intuition.
Qed.

Lemma val_type_open_permute : forall {n T ρ δ},
    tsize_flat T < n ->
    closed_ty (S (S (length δ))) (length ρ) T ->
    forall {v vs Dx Dy}, ⦑ v, vs ⦒ ⋵ val_type (open_rec (length δ) (varF (S (length ρ))) (open_rec (S (length δ)) (varF (length ρ))     T)) (δ ++ (Dx :: Dy :: ρ))
                  <-> ⦑ v, vs ⦒ ⋵ val_type (open_rec (length δ) (varF (length ρ))     (open_rec (S (length δ)) (varF (S (length ρ))) T)) (δ ++ (Dy :: Dx :: ρ)).
  induction n; intros T ρ δ Hsz Hcl; simpl in Hsz; destruct T; intuition.
  - (* TAll -> *)
    unfold vseta_mem in *. intros. simpl. simpl in H.
    unfold_val_type. specialize (H n0). unfold_val_type in H.
    destruct v as [ γ' T' t | γ' T' ]; simpl in * ; intuition.
    admit. admit. (* TODO: remove the closedness predicates in logrel, strengthen the context relation instead.*)
    specialize (H2 vx Dx0). unfold vseta_mem in *. unfold elem2 in *. unfold ℰ in *.
    rewrite <- IHn in H1; try lia; auto. apply H2 in H1. destruct H1 as [k [vy [Heval [Vy vyVyT2]]]].
    exists k. exists vy. intuition. exists Vy.
    unfold open' in *.
    rewrite (open_rec_commute _ 0 _ _ _) in vyVyT2; eauto.
    rewrite (open_rec_commute _ 0 _ _ _) in vyVyT2; eauto.
    rewrite (open_rec_commute _ 0 _ _ _); eauto.
    rewrite (open_rec_commute _ 0 _ _ _); eauto.
    assert (Hr : Dx0 :: δ ++ Dx :: Dy :: ρ = (Dx0 :: δ) ++ Dx :: Dy :: ρ) by auto.
    assert (Hr' : Dx0 :: δ ++ Dy :: Dx :: ρ = (Dx0 :: δ) ++ Dy :: Dx :: ρ) by auto.
    assert (Hl : S (length δ) = length (Dx0 :: δ)) by auto.
    rewrite Hl in *. rewrite Hr in *. rewrite Hr' in *.
    unfold vseta_mem in *. rewrite <- IHn.
    replace (length (δ ++ Dy :: Dx :: ρ)) with (length (δ ++ Dx :: Dy :: ρ)). auto.
    repeat rewrite app_length. auto.
    rewrite <- open_preserves_size. lia.
    inversion Hcl. subst.
    admit. (* FIXME: doesn't seem provable, but we need the closed condition for TSel case *)
    inversion Hcl. auto.
  - (* TAll <- *)
    unfold vseta_mem in *. intros. simpl. simpl in H.
    unfold_val_type. specialize (H n0). unfold_val_type in H.
    destruct v as [ γ' T' t | γ' T' ]; simpl in * ; intuition.
    admit. admit. (* TODO: remove the closedness predicates in logrel, strengthen the context relation instead.*)
    specialize (H2 vx Dx0). unfold vseta_mem in *. unfold elem2 in *. unfold ℰ in *.
    rewrite IHn in H1; try lia; auto. apply H2 in H1. destruct H1 as [k [vy [Heval [Vy vyVyT2]]]].
    exists k. exists vy. intuition. exists Vy.
    unfold open' in *.
    rewrite (open_rec_commute _ 0 _ _ _) in vyVyT2; eauto.
    rewrite (open_rec_commute _ 0 _ _ _) in vyVyT2; eauto.
    rewrite (open_rec_commute _ 0 _ _ _); eauto.
    rewrite (open_rec_commute _ 0 _ _ _); eauto.
    assert (Hr : Dx0 :: δ ++ Dx :: Dy :: ρ = (Dx0 :: δ) ++ Dx :: Dy :: ρ) by auto.
    assert (Hr' : Dx0 :: δ ++ Dy :: Dx :: ρ = (Dx0 :: δ) ++ Dy :: Dx :: ρ) by auto.
    assert (Hl : S (length δ) = length (Dx0 :: δ)) by auto.
    rewrite Hl in *. rewrite Hr in *. rewrite Hr' in *.
    unfold vseta_mem in *. rewrite IHn.
    replace (length (δ ++ Dx :: Dy :: ρ)) with (length (δ ++ Dy :: Dx :: ρ)). auto.
    repeat rewrite app_length. auto.
    rewrite <- open_preserves_size. lia.
    inversion Hcl. subst.
    admit. (* FIXME *)
    inversion Hcl. auto.
  - (* TSel -> *)
    simpl in *. destruct v eqn:Hv. simpl in *.
    inversion Hcl. subst.
    unfold_val_type.
Admitted.

Lemma val_type_open : forall {n T ρ},
    tsize_flat T < n ->
    closed_ty 1 (length ρ) T ->
    forall {ρ' v vs Dx}, ⦑ v, vs ⦒ ⋵ val_type (open' ρ T) (Dx :: ρ) <-> ⦑ v, vs ⦒ ⋵ val_type (open' (ρ' ++ ρ) T) (Dx :: (ρ' ++ ρ)).
  induction n; intros; destruct T; intuition.
  - inversion H0. subst. simpl in H.
    unfold vseta_mem in *. intros. unfold_val_type.
    destruct v as [ γ' T' t | γ' T' ]. specialize (H1 n).
    unfold_val_type in H1. intuition.
    admit. admit.  (* TODO these seem provable *)
    unfold elem2 in *. unfold ℰ in *.
    specialize (H4 vx Dx0).
    unfold open' in *. unfold vseta_mem in *.
    erewrite <- IHn in H3; eauto; try lia. apply H4 in H3.
    destruct H3 as [k [vy [Heval [Dy vyDyT2]]]]. exists k. exists vy. intuition.
    exists Dy.
    assert (Hr : Dx :: ρ' ++ ρ = [Dx] ++ (ρ' ++ ρ)) by auto.
    rewrite Hr. erewrite <- IHn. erewrite <- IHn.
    assert (Hr' : Dx :: ρ = [Dx] ++ ρ) by auto.
    rewrite Hr' in vyDyT2. erewrite <- IHn in vyDyT2.
    (* Problem: mismatch between  *)
    (* (open_rec 1 (varF (length ρ)) T2) *)
    (* and (open_rec 1 (varF (length (ρ' ++ ρ))) T2) *)
    admit.
Admitted.

Lemma val_type_extend  : forall {T ρ D}, closed_ty 0 (length ρ) T -> val_type T ρ       ⊑ val_type T (D :: ρ)
with  val_type_shrink  : forall {T ρ D}, closed_ty 0 (length ρ) T -> val_type T (D :: ρ) ⊑ val_type T ρ.
  - clear val_type_extend.
    induction T as [T IHT] using (well_founded_induction wfR).
    intros. unfold vseta_sub_eq.
    intros. destruct T; destruct n; intuition.
    + (* TAll *)
      unfold_val_type. intros. destruct v as [ γ' T' t | γ' T' ]; eauto.
      unfold elem2 in *. unfold ℰ in *.
      destruct H0 as [HclT1 [HclT2 H0]]. intuition.
      eapply closed_ty_monotone; eauto.
      eapply closed_ty_monotone; eauto.
      specialize (H0 vx Dx).
      assert (HT1 : vseta_mem vx Dx (val_type T1 ρ)).  {
        unfold vseta_sub_eq in *. unfold vseta_mem in *.
        unfold vset_sub_eq in *.  intros m.
        specialize (val_type_shrink _ _ D HclT1).
        specialize (val_type_shrink (S m)). simpl in val_type_shrink.
        apply val_type_shrink. eauto.
      }
      apply H0 in HT1. destruct HT1 as [k [vy [Heval [vsy HvyinT2]]]].
      exists k. exists vy. intuition. exists vsy. specialize (IHT _ (@RAll2 _ _ _ ρ) (Dx :: ρ) D).
      (* TODO better to reformulate vseteq_subeq in terms of vseta_mem *)
      admit. (* TODO: can show in assms that val_type (open' ρ T2) (D :: Dx :: ρ) , need to permute the front entries *)
    + (* TSel *)
      unfold vseta_sub_eq in *. unfold vset_sub_eq. intros.
      unfold_val_type in H0. inversion H; subst. unfold_val_type. destruct (indexr x ρ) eqn:Hlookup1.
      apply PeanoNat.Nat.lt_neq in H4. rewrite <- PeanoNat.Nat.eqb_neq in H4. rewrite H4.
      assumption. simpl in H0. contradiction. lia.
    + (* TMem *)
      inversion H. subst. unfold vseta_sub_eq in *. unfold vset_sub_eq in *. intros. unfold_val_type in H0.
      destruct v as [ γ' T' t | γ' T' ]; eauto. unfold_val_type. destruct n; intuition.
      eapply closed_ty_monotone; eauto. eapply closed_ty_monotone; eauto.
      eapply closed_ty_monotone; eauto. eapply closed_ty_monotone; eauto.
      -- specialize (IHT _ RMem1 _ D H1 (S n)). simpl in IHT.
         specialize (val_type_shrink T1 _ D H1 (S n)). simpl in val_type_shrink.
         intuition.
      -- specialize (IHT _ RMem2 _ D H0 (S n)). simpl in IHT. intuition.
    + (* TBind *)
      unfold_val_type. intros.
      admit.
    + (* TAnd *)
      admit.
  - clear val_type_shrink.
    induction T as [T IHT] using (well_founded_induction wfR).
    intros. unfold vseta_sub_eq. destruct T; destruct n; intuition.
    + (* TAll *)
      admit.
    + (* TSel *)
      admit.
    + (* TMem *)
      admit.
    + (* TBind *)
      admit.
    + (* TAnd *)
Admitted.

Lemma val_type_closed : forall {T ρ v D}, ⦑ v, D ⦒ ⋵ (val_type T ρ) -> closed_ty 0 (length ρ) T.
  unfold vseta_mem. simpl.
  induction T as [T IHT] using (well_founded_induction wfR).
  intros. destruct T; intuition.
  - unfold_val_type in H. specialize (H 0). destruct v as [ γ' T' t | γ' T' ]; intuition.
  - unfold_val_type in H. destruct v0. destruct (indexr i ρ) eqn:Heq.
    apply indexr_var_some' in Heq. intuition. specialize (H 0). simpl in H. contradiction.
    specialize (H 0). simpl in H. contradiction.
  - specialize (H 0). unfold_val_type in H. destruct v as [ γ' T' t | γ' T' ]; intuition.
  - specialize (H 0). unfold_val_type in H. repeat destruct H. intuition.
  - unfold_val_type in H. constructor.
    + specialize (IHT _ RAnd1 ρ v D). apply IHT.
      intros n. specialize (H n). intuition.
    + specialize (IHT _ RAnd2 ρ v D). apply IHT.
      intros n. specialize (H n). intuition.
Qed.

(* TODO this wouldn't be necessary if ⊑ was formulated in terms of ⋵ *)
Lemma val_type_extend_mem  : forall {T ρ v D D'}, ⦑ v, D ⦒ ⋵ (val_type T ρ) -> ⦑ v, D ⦒ ⋵ (val_type T (D' :: ρ)).
  intros. assert (Hc : closed_ty 0 (length ρ) T) by (apply (val_type_closed H)).
  apply (@val_type_extend _ _ D') in Hc.
  unfold vseta_mem in *. unfold vseta_sub_eq in *. intros.
  specialize (Hc (S n)). unfold vset_sub_eq in *. simpl in *.
  eauto.
Qed.

(* TODO dito here *)
Lemma val_type_shrink'  : forall {T ρ v D D' n}, closed_ty 0 (length ρ) T -> (val_type T (D' :: ρ) (S n) (D n) v) -> (val_type T ρ (S n) (D n) v).
  intros.
  specialize (@val_type_shrink T ρ D' H (S n) (D n) v) as Hv.
  auto.
Qed.

(* Bundles facts about lookups in related envs *)
Record LookupT (x : id) (Γ : tenv) (ρ : denv) (γ : venv) : Type :=
  mkLookupT
    {
      l_T  : ty;   l_D  : Dom;  l_v  : vl;
      (* l_Γ1 : tenv; l_Γ2 : tenv; l_ρ1 : denv; *)
      (* l_ρ2 : denv; l_γ1 : venv; l_γ2 : venv; *)
      l_x_in_Dom : x < length Γ;
      l_x_Γ_T    : indexr x Γ = Some l_T;
      l_x_ρ_D    : indexr x ρ = Some l_D;
      l_x_γ_v    : indexr x γ = Some l_v;
      (* l_𝒞𝓉𝓍      : 𝒞𝓉𝓍 (l_T :: l_Γ2) (l_D :: l_ρ2) (l_v :: l_γ2); *)
      l_vD_in_Tρ : ⦑ l_v, l_D ⦒ ⋵ (val_type l_T ρ);
      (* l_Γ_split  : Γ = l_Γ1 ++ (l_T :: l_Γ2); *)
      (* l_ρ_split  : ρ = l_ρ1 ++ (l_D :: l_ρ2); *)
      (* l_γ_split  : γ = l_γ1 ++ (l_v :: l_γ2); *)
    }.
Arguments l_T        {x Γ ρ γ}.
Arguments l_D        {x Γ ρ γ}.
Arguments l_v        {x Γ ρ γ}.
Arguments l_v        {x Γ ρ γ}.
Arguments l_x_Γ_T    {x Γ ρ γ}.
Arguments l_x_ρ_D    {x Γ ρ γ}.
Arguments l_x_γ_v    {x Γ ρ γ}.
Arguments l_vD_in_Tρ {x Γ ρ γ}.
Arguments l_x_in_Dom {x Γ ρ γ}.

(* Enables doing induction on C in the lookup lemma *)
Inductive Lookup (x : id) Γ ρ γ : Prop :=
  | lkT : LookupT x Γ ρ γ -> Lookup x Γ ρ γ.

Lemma lookup {Γ ρ γ} (C : 𝒞𝓉𝓍 Γ ρ γ) : forall {x}, x < length Γ -> Lookup x Γ ρ γ.
  induction C; simpl; intros.
  - lia.
  - inversion H0.
    + constructor. econstructor.
      simpl. lia.
      apply indexr_head.
      rewrite (𝒞𝓉𝓍_lengthρ C). apply indexr_head.
      rewrite (𝒞𝓉𝓍_lengthγ C). apply indexr_head.
      apply val_type_extend_mem. assumption.
    + apply IHC in H2. inversion H2. destruct X.
      constructor. econstructor.
      simpl. lia.
      rewrite indexr_skip. eauto. lia.
      rewrite indexr_skip. eauto. rewrite <- (𝒞𝓉𝓍_lengthρ C). lia.
      rewrite indexr_skip. eauto. rewrite <- (𝒞𝓉𝓍_lengthγ C). lia.
      apply val_type_extend_mem. assumption.
Qed.

Lemma fundamental     : (forall {Γ t T}, has_type Γ t T -> forall{ρ γ}, 𝒞𝓉𝓍 Γ ρ γ -> ⟨ γ , t ⟩ ∈ ℰ (val_type T ρ))
with  fundamental_stp : (forall {Γ S T}, stp Γ S T      -> forall{ρ γ}, 𝒞𝓉𝓍 Γ ρ γ -> (val_type S ρ) ⊑ (val_type T ρ)).
Proof.
  - clear fundamental. intros Γ t T Hty. induction Hty; intros ρ γ HΓργ; unfold ℰ in *; unfold elem2 in *.
    + (* t_var *)
      pose (HL := H0). apply indexr_var_some' in HL. apply (lookup HΓργ) in HL. inversion HL as [L].
      exists 1. exists (l_v L). split. simpl. rewrite (l_x_γ_v L). auto.
      exists (l_D L). rewrite (l_x_Γ_T L) in H0. inversion H0. subst. apply (l_vD_in_Tρ L).
    + (* t_typ *)
      exists 1. exists (vty γ T). split. simpl. auto. exists (val_type T ρ). unfold vseta_mem.
      intros. simpl. unfold_val_type. repeat split.
      rewrite <- (𝒞𝓉𝓍_lengthρ HΓργ). eapply ty_wf_closed. eauto.
      rewrite <- (𝒞𝓉𝓍_lengthρ HΓργ). eapply ty_wf_closed. eauto.
      apply seteq'_refl. apply seteq'_refl.
    + (* t_abs *)
      exists 1. exists (vabs γ T1 t). split. simpl. reflexivity.
      exists vseta_top. unfold vseta_mem. unfold_val_type. unfold vseta_mem. intros n.
      repeat split. rewrite <- (𝒞𝓉𝓍_lengthρ HΓργ). eapply ty_wf_closed. eauto.
      rewrite <- (𝒞𝓉𝓍_lengthρ HΓργ). apply has_type_closed in Hty. destruct Hty.
      admit. (* TODO relation between closed and open *)
      intros vx Dx vxDxinT1.
      unfold ℰ in *; unfold elem2 in *.
      assert (HOt : (open_tm' γ t) = (open_tm' Γ t)). {
        apply 𝒞𝓉𝓍_length in HΓργ. unfold open_tm'. destruct HΓργ.
        rewrite H0. rewrite H1. auto.
      }
      assert (HOT2 : (open' ρ T2) = (open' Γ T2)). {
        apply 𝒞𝓉𝓍_length in HΓργ. unfold open'. destruct HΓργ.
        rewrite H0. rewrite H1. auto.
      }
      rewrite HOt. rewrite HOT2. apply IHHty.
      constructor; intuition.
    + (* t_app *)
      unfold vseta_mem in *. simpl in IHHty1. simpl in IHHty2.
      specialize (IHHty1 _ _ HΓργ). specialize (IHHty2 _ _ HΓργ).
      destruct IHHty1 as [k1 [v1 [evalv1 [vs1 v1vs1inVtyT1T2 ]]]].
      destruct IHHty2 as [k2 [v2 [evalv2 [vs2 v2vs2inVtyT1]]]].
      unfold_val_type in v1vs1inVtyT1T2. destruct v1 as [ γ' T' t' | γ' T' ].
      specialize (v1vs1inVtyT1T2 0). destruct v1vs1inVtyT1T2 as [cT1 [cT2 v1vs1inVtyT1T2]].
      specialize (v1vs1inVtyT1T2 v2 vs2 v2vs2inVtyT1).
      unfold ℰ in *. unfold elem2 in *.
      destruct v1vs1inVtyT1T2 as [k3 [v3 [evalapp [vs3 v3vs3inVtyT2] ]]].
      exists (k1 + k2 + k3). exists v3. split.
      destruct k1; destruct k2; destruct k3; try solve [ simpl in *; discriminate].
      eapply eval_monotone in evalv1. eapply eval_monotone in evalapp. eapply eval_monotone in evalv2.
      simpl. erewrite evalv2. simpl. erewrite evalv1. erewrite evalapp.
      reflexivity. lia. lia. lia. exists vs3. simpl.
      assert (HT2open' : (open' ρ T2) = T2). {
        admit. (* consequence of H : ty_wf Γ T2 *)
      }
      rewrite HT2open' in *. unfold vseta_mem in *.
      intros n. eapply val_type_shrink'.
      rewrite <- (𝒞𝓉𝓍_lengthρ HΓργ). eapply ty_wf_closed. auto.
      eauto.
      contradiction.
    + (* t_dapp *)
      unfold vseta_mem in *. simpl in IHHty1. simpl in IHHty2.
      specialize (IHHty1 _ _ HΓργ). specialize (IHHty2 _ _ HΓργ).
      destruct IHHty1 as [k1 [v1 [evalv1 [vs1 v1vs1inVtyT1T2 ]]]].
      destruct IHHty2 as [k2 [v2 [evalv2 [vs2 v2vs2inVtyT1]]]].
      unfold_val_type in v1vs1inVtyT1T2. destruct v1 as [ γ' T' t' | γ' T' ].
      specialize (v1vs1inVtyT1T2 0). destruct v1vs1inVtyT1T2 as [cT1 [cT2 v1vs1inVtyT1T2]].
      specialize (v1vs1inVtyT1T2 v2 vs2 v2vs2inVtyT1).
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
      unfold_val_type. unfold vseta_mem. intros. unfold vseta_big_join.
      exists (val_type (open (varF x) T) ρ). split.
      admit. (* TODO *)
      eauto.
    + (* t_unpack *)
      simpl in IHHty1. simpl in IHHty2.
      specialize (IHHty1 _ _ HΓργ). destruct IHHty1 as [k1 [v1 [evalv1 [vs1 v1vs1inVtyT1T2 ]]]].
      remember (val_type (TBind T1) ρ) as F.
      unfold_val_type in HeqF.
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
  - clear fundamental_stp. intros Γ S T Hst.
    induction Hst; intros ρ γ HΓργ; unfold vseta_sub_eq; intros; unfold vset_sub_eq; destruct n; intros; trivial.
    + (* stp_top *)
      unfold_val_type. trivial.
    + (* stp_bot *)
      destruct H0.
    + (* stp_mem *)
      unfold_val_type in H. destruct v as [ γ' T t | γ' T ]. contradiction.
      specialize (IHHst1 _ _ HΓργ n). specialize (IHHst2 _ _ HΓργ n).
      destruct H as [ clS1 [clT1 [S1subX XsubT1 ]]]. unfold_val_type. repeat split.
      rewrite <- (𝒞𝓉𝓍_lengthρ HΓργ). apply stp_closed in Hst1. intuition.
      rewrite <- (𝒞𝓉𝓍_lengthρ HΓργ). apply stp_closed in Hst2. intuition.
      eapply subset'_trans. eauto. assumption.
      eapply subset'_trans. eauto. assumption.
    + (* stp_sel1 *)
      specialize (IHHst _ _ HΓργ). pose (HL := H). apply indexr_var_some' in HL.
      apply (lookup HΓργ) in HL. inversion HL as [L]. destruct L.
      rewrite l_x_Γ_T0 in H. inversion H. subst.
      unfold vseta_mem in *. simpl in *. unfold vseta_sub_eq in IHHst.
      specialize (IHHst (S (S n))). unfold vset_sub_eq in IHHst.
      specialize (l_vD_in_Tρ0 (S n)). apply IHHst in l_vD_in_Tρ0.
      unfold_val_type in l_vD_in_Tρ0. destruct l_v0 as [ γ' T' t | γ' T' ]. contradiction.
      unfold_val_type. rewrite l_x_ρ_D0. intuition.
    + (* stp_sel2 *)
      specialize (IHHst _ _ HΓργ). pose (HL := H). apply indexr_var_some' in HL.
      apply (lookup HΓργ) in HL. inversion HL as [L]. destruct L.
      rewrite l_x_Γ_T0 in H. inversion H. subst.
      unfold vseta_mem in *. simpl in *. unfold vseta_sub_eq in IHHst.
      specialize (IHHst (S (S n))). unfold vset_sub_eq in IHHst.
      specialize (l_vD_in_Tρ0 (S n)). apply IHHst in l_vD_in_Tρ0.
      unfold_val_type in l_vD_in_Tρ0. destruct l_v0 as [ γ' T' t | γ' T' ]. contradiction.
      unfold_val_type in H0. rewrite l_x_ρ_D0 in H0. intuition.
    + (* stp_all *)
      unfold_val_type in H1. destruct v as [γ' T' t | γ' T'] eqn:Hv; try contradiction.
      destruct H1 as [clS1 [clT1 H1]]. unfold_val_type.
      unfold ℰ in *. unfold elem2 in *. repeat split.
      rewrite <- (𝒞𝓉𝓍_lengthρ HΓργ). apply stp_closed in Hst1. intuition.
      rewrite <- (𝒞𝓉𝓍_lengthρ HΓργ). apply stp_closed in Hst2. admit. (*TODO relation between closed and open*)
      intros vx Dx vxMem. specialize (IHHst1 _ _ HΓργ).
      assert (HvsDxS1 : vseta_mem vx Dx (val_type S1 ρ)). {
        (* TODO: it might be better to formulate  ⊑ in terms of vseta_mem, might save a few annoying manual steps *)
        unfold vseta_mem in *.
        intros m. specialize (IHHst1 (S m)).
        intuition.
      }
      eapply H1 in HvsDxS1. destruct HvsDxS1 as [k [vy [Heval [Dy vyinT1]]]].
      exists k. exists vy. split. assumption.
      assert (Hopen1 : (open' Γ T1) = (open' ρ T1)). {
        apply 𝒞𝓉𝓍_lengthρ in HΓργ. unfold open'. rewrite HΓργ. auto.
      }
      assert (Hopen2 : (open' Γ T2) = (open' ρ T2)). {
        apply 𝒞𝓉𝓍_lengthρ in HΓργ. unfold open'. rewrite HΓργ. auto.
      }
      rewrite <- Hopen2. exists Dy.
      unfold vseta_mem. intros m. simpl.
      unfold vseta_sub_eq in IHHst2.
      assert (HC: 𝒞𝓉𝓍 (S2 :: Γ) (Dx :: ρ) (vx :: γ)) by intuition.
      specialize (IHHst2 _ _ HC (S m)).
      apply IHHst2. rewrite Hopen1. intuition.
    + (* stp_bindx *)
      subst. unfold_val_type in H3. unfold_val_type.
      destruct H3 as [F [[Fsub clT1] FMem]]. exists F.
      assert (HOT1 : (open' ρ T1) = (open' Γ T1)). {
        unfold open'. rewrite (𝒞𝓉𝓍_lengthρ HΓργ). auto.
      }
      assert (HOT2 : (open' ρ T2) = (open' Γ T2)). {
        unfold open'. rewrite (𝒞𝓉𝓍_lengthρ HΓργ). auto.
      }
      rewrite HOT1 in *. rewrite HOT2 in *.
      repeat split. eapply subset_trans. eapply Fsub.
      eapply IHHst. constructor. eauto. unfold vseta_mem.
      intros. simpl. unfold vseta_sub_eq in Fsub. specialize (Fsub (S n0)).
      unfold vset_sub_eq in Fsub.
      admit.
      rewrite <- (𝒞𝓉𝓍_lengthρ HΓργ). apply stp_closed in Hst. admit. (*TODO relation between closed and open*)
      assumption.
    + (* stp_and11 *)
      specialize (IHHst _ _ HΓργ (S n)).
      unfold_val_type in H0. intuition.
    + (* stp_and12 *)
      specialize (IHHst _ _ HΓργ (S n)).
      unfold_val_type in H0. intuition.
    + (* stp_and2 *)
      specialize (IHHst1 _ _ HΓργ (S n)). specialize (IHHst2 _ _ HΓργ (S n)).
      unfold_val_type. intuition.
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
