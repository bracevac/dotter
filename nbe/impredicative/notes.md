# Towards a PER Semantics for Abstract Types

We consider the different notions of existential types and sigma
types, attempting to derive their PER semantics for NbE.  Then we
bridge the gap to DOT's lower- and upper-bounded type members, which
intuitively correspond to a form of impredicative existential type.

Most NbE works that I know of address predicative type theories.  The
notable exception being Abel's FLOPS'10 paper on NbE and its
completeness for the impredicative Calculus of Constructions (CoC).
I am building on that work, particularly because it claims to
be implementable in Coq or a similar system.

Moreover, I am not aware of any work on NbE and its metatheory for the
impredicative existential type. Regarding NbE for strong sigma types,
I am only aware of Miguel Pagano's PhD 2012 thesis based on Martin-Lof type
theory.

Geuver's 1994 paper features an extensible strong normalization proof
for CoC based on the Girard-Tait method. However, the system lacks
large eliminations and is thus erasable into Fω. He covers sigma types
and existential types.

Werner's 1992 proves SN for CoC with large eliminations, where erasure
into Fω is not possible. As with Geuver's work, it is not clear if
this pen and paper formalization can be easily translated into a proof
assistant.

Impredicativity per se is not straightforward, and we expect analogous
challenges in models for impredicative abstract types.
Miquel and Werner's "The not so simple proof-irrelevant model of CC"
demonstrates that constructing models for the impredicative
CoC are technically subtle and involved. Particularly, function space
models need to treat objects of different (metalanguage) types uniformly.

## DOT Rules for Abstract Types

If we follow Abel's FLOPS paper, what would be the assumptions and
proof obligations in the fundamental lemma?

### Introduction

    Γ ⊢ T : ⋆                --> (nbe T, ⟦ T ⟧) == (nbe T, ⟦ T ⟧) ∈ ⟦ ⋆ ⟧ : ⟪ ⋆ ⟫ = PER Dom×(PER Dom×())  (IH)
    ------------------------
    Γ ⊢ <type T> : TMem T T  --> (type T, ()) == (type T, ()) ∈ ⟦ TMem T T ⟧ : ⟨ ⋆ ⟩ = PER Dom×()      (goal)

The IH above is interesting, since we get the normal form of the type T with its semantic role, similar
to the ECOOP development. We lose this information in the conclusion, because the "type T" term is not
supposed to have a "semantic role" in Abel's terminology. It should hopefully be possible to design
⟦ TMem T T ⟧ in a way that we could recover this pairing. There seems to be a connection to
Geuver's 1994 work, where he enriches the semantics for existentials/sigmas
so that all interpretations are metalanguage functions accepting the witness of an existential
(kind of like a state monad).

### Formation

Consider the proposed formation rule for type selection:

    Γ ⊢ t : TMem T U --> (nbe t, ()) == (nbe t, ()) ∈ ⟦ TMem T U ⟧: ⟨ ⋆ ⟩ = PER Dom×()                 (IH)
    ----------------
    Γ ⊢ t.Type : ⋆   --> (nbe t.Type, ⟦ t.Type ⟧)^2 ∈ ⟦ ⋆ ⟧ : ⟪ ⋆ ⟫ = PER Dom×(PER Dom×())          (goal)

Again, ⟦ TMem T U ⟧ must provide enough information to recover the pairing of nbe t with
its semantic type ⟦ t.Type ⟧.

### Subtyping rules:

The fundamental lemma for subtyping should have the obvious subset
inclusion interpretations.  Experimenting with the ECOOP paper's
proofs, it turned out that it was difficult to have the fundamental
lemma satisfy all the subtyping rules on type selections and dependent
function types simultaneously. So far we only know that the proof goes
through with the peculiar choice of a number-indexed semantic domain
pairing values and sets.  It was so far *not* possible to have a
separation of values and the associated sets of values they represent
in the semantics.

The pairing of semantic normal forms with their semantic role in
Abel's nbe development serves a very similar function, but does not
require the number index (I am hesitant to call it a step index, since
it is not an approximation of evaluation steps). This index might not be
needed after all.

Consider subtyping of abstract types:

     stp_sel1 : forall Γ t T,
        has_type Γ t (TMem T TTop)  --> (nbe t, ()) == (nbe t, ()) ∈ ⟦TMem T TTop⟧ :  ⟨ ⋆ ⟩ = PER Dom×() (IH)
        ---------------------------
        stp Γ T (TSel t)            --> ⟦T⟧ ⊆ ⟦TSel t⟧

     stp_sel2 : forall Γ t T,
        has_type Γ t (TMem TBot T)  --> (nbe t, ()) == (nbe t, ()) ∈ ⟦TMem TBot T⟧ :  ⟨ ⋆ ⟩ = PER Dom×() (IH)
        --------------------------
        stp Γ (TSel t) T            --> ⟦TSel t⟧ ⊆ ⟦T⟧

We have the same issue as before, ⟦ TMem T U ⟧ must be defined just
right, plus we have to define the ⟦TSel t⟧ interpretation.

The last rule is not problematic

     stp_selx : forall Γ t T1 T2,
        has_type Γ t (TMem T1 T2)
        -------------------------
        stp Γ (TSel t) (TSel t)     --> ⟦TSel t⟧ ⊆ ⟦TSel t⟧ trivial

However, it will eventually be replaced by a general reflexivity rule

     Γ ⊢ T == T' : ⋆
     ----------------
     Γ ⊢ T <: T

connecting judgmental equality with subtyping.

## Interlude: Pi Types

Abel defines a generic Pi type PER-semantics, which is indexed by the (erased) kinds.
Here is the definition from our Coq file:

	Definition ℿ (κ1 κ2 : Knd) (𝒦1 : ⟪ κ1 ⟫) (𝒦2 : ∀ {x}, x ⋵ 𝒦1 -> ⟪ κ2 ⟫): ⟪ κ1 ⇒ κ2 ⟫ :=
		{{ (F, ℱ), (F', ℱ') |
		  ∀ A B 𝒜 ℬ, ∀ (p : (A, 𝒜) == (B, ℬ) ∈ 𝒦1),
			  ∃ fuel FA F'B, eval_app fuel F A = Done FA /\ eval_app fuel F' B = Done F'B ->
								  (FA, ℱ (A, 𝒜)) == (F'B, ℱ'(B, ℬ)) ∈ (𝒦2 (meml p)) }}.

This is going to be useful in the context of existentials later on.

A (potentially major?) pain point: Abel's paper stipulates that simple
kinds of the form κ ⇒ ⋄ should be treated as ⋄ (which marks an erased term dependency).
The justification being that the former is a "subset" of the latter.  This would
complicate all our definitions indexed by a simple kind/skeleton syntax.

Consider the particular instantiation of ℿ which models impredicative universal quantification:

    Check (ℿ ∗ ⋄).  (* forall 𝒦1 : ⟪ ∗ ⟫, (forall x : Dom * ⟨ ∗ ⟩, (x) ⋵ (𝒦1) -> ⟪ ⋄ ⟫) -> ⟪ ∗ ⇒ ⋄ ⟫ *)

This works as expected only if we treat ∗ ⇒ ⋄ = ⋄. Then the type becomes

    forall 𝒦1 : ⟪ ∗ ⟫, (forall x : Dom * ⟨ ∗ ⟩, (x) ⋵ (𝒦1) -> ⟪ ⋄ ⟫) -> ⟪ ⋄ ⟫

which is identical to

    forall 𝒦1 : ⟪ ∗ ⟫, (forall x : Dom * ⟨ ∗ ⟩, (x) ⋵ (𝒦1) -> ⟨ ∗ ⟩) -> ⟨ ∗ ⟩    (by ⟪ ⋄ ⟫ = ⟨ ∗ ⟩)

Let's compare ⟪ ⋄ ⟫ and ⟪ ∗ ⇒ ⋄ ⟫:

    Eval red in ⟪ ⋄ ⟫.     (* Dom * ⟨ ⋄ ⟩     -> Dom * ⟨ ⋄ ⟩      -> Prop *)
    Eval red in ⟪ ∗ ⇒ ⋄ ⟫. (* Dom * ⟨ ∗ ⇒ ⋄ ⟩ -> Dom * ⟨ ∗ ⇒ ⋄ ⟩ -> Prop *)

⟨ ⋄ ⟩ and ⟨ ∗ ⇒ ⋄ ⟩ are different beasts:

    Eval red in ⟨ ⋄ ⟩.     (* unit *)
    Eval red in ⟨ ∗ ⇒ ⋄ ⟩. (* Dom * relation (Dom * unit) -> unit *)

We can justify that ∗ ⇒ ⋄ and ⋄ are "the same", since the former describes
unit-returning functions.
This phenomenon is a consequence of impredicativity and has also been discussed
in detail in: Miquel and Werner - The not so simple proof-irrelevant model of CC.
They argue that any kind of model for impredicative CoC-like systems will exhibit
this issue.

## Existential Types

Intuitively, `<type T>` values should be packages of type `∃x:⋆,Unit`.
So let's develop an understanding of existentials and sigma types.

### Formation

    Γ ⊢ κ : ◻                    --> (nbe κ, ⟦|κ|⟧) == (nbe κ, ⟦|κ|⟧) ∈ eq(|κ|) : Per D×⟨ |κ| ⟩
    Γ, x:κ ⊢ T : ⋆               --> (nbe T, ⟦T⟧) == (nbe T, ⟦T⟧) ∈ ⟦ ⋆ ⟧ : ⟪ ⋆ ⟫ = PER Dom×(PER Dom×())
    ---------------------------
    Γ ⊢ ∃x:κ.T : ⋆               --> (nbe ∃x:κ.T, ⟦∃x:κ.T⟧) == (nbe ∃x:κ.T, ⟦∃x:κ.T⟧) ∈ ⟦ ⋆ ⟧

(note so far, I omitted the associated contexts in the interpretations). Here `| κ |` refers to
Abel's erased kinds/skeletons. His model construction works through being able to erase term
dependency in kinds, so that the kind semantics is just the simply-kinded lambda calculus.
It is however *not* the same kind of erasure of terms in types that Geuvers utilizes to
map CoC to Fω. Abel's work in principle supports large eliminations, which are not expressible
in Fω.

The above rule seems uncontroversial, as long as we can appropriately define ⟦∃x:κ.T⟧
(more on that further below).

### Introduction

    Γ ⊢ T : κ                     --> (nbe T, ⟦T⟧) == (nbe T, ⟦T⟧) ∈ ⟦ |κ| ⟧ : Per D×⟨ |κ| ⟩
    Γ,x:κ ⊢ t : T                 --> (nbe t, ())  == (nbe t, ())  ∈ ⟦ U ⟧   : PER Dom×()
    ---------------------------
    Γ ⊢ pack (T,t) : ∃x:κ.T       --> (nbe pack (T,t), ()) == (nbe pack (T,t), ()) ∈ ⟦ ∃x:κ.T ⟧ : PER Dom×()

### Elimination

Weak existentials have the usual `unpack` elimination form:

    Γ ⊢ t1 : ∃x:κ.T                  --> (nbe t1, ()) == (nbe t1, ()) ∈ ⟦ ∃x:κ.T ⟧ : PER Dom×()
    Γ,x:κ,y:T ⊢ t2 : U               --> (nbe t2, ()) == (nbe t2, ()) ∈ ⟦ U ⟧      : Per Dom×()
    ------------------------------
    Γ ⊢ unpack t1 as (x,y) in t2 : U --> (nbe unpack .., ())^2 ∈ ⟦ U ⟧

Any particular conditions on `U`? if existentials are weak, then `x,y` cannot occur in `U`, e.g., `Γ ⊢ U : ⋆`
Considering that we could express the first projection of the type as `(unpack t1 as (x,_) in x : ⋆)`,
thus having an analogue for type selection, we then realize that `U` should be
at the kind level, i.e., `Γ ⊢ U : ◻` (resp. specialized to `⋆` if we just care about existential types).
Thus, we have another eliminator at the type level:

    Γ ⊢ t1 : ∃x:κ.T                  --> (nbe t1, ()) == (nbe t1, ()) ∈ ⟦ ∃x:κ.T ⟧ : PER Dom×()
    Γ,x:κ,y:T ⊢ x : κ                --> (nbe x, ⟦ x ⟧) == (nbe x, ⟦ x ⟧) ∈ ⟦ |κ| ⟧      : Per Dom×⟨ |κ| ⟩
                                         trivial, since x will be bound in an env assigning an appropriate semantic element
    --------------------------------
    Γ ⊢ unpack t1 as (x,y) in x : κ  --> (nbe unpack t1 ..., ⟦unpack ... ⟧) == (nbe unpack t1, ⟦unpack ... ⟧) ∈ ⟦ |κ| ⟧ : PER Dom×⟨ |κ| ⟩

which leads to no ambiguity. We could hence stipulate `t.type := unpack t as (x,y) in x` as derived syntax.
This also shows that we need different semantic treatments of these projections.

Another important remaining question is if the type-level projection
above is already sufficient to make the system inconsistent, or
whether inconsistency only occurs if the strong second projection is
added. I.e., when do we cross the red line into inconsistency
territory?

In Abel's framework, the fundamental lemma for the type-level `unpack`
requires an interpretation `⟦unpack ...⟧`.  We face the same challenges
from DOT's abstract type rules above.

### Second Projection and Subtyping

The second projection is forbidden, since the type we eliminate into
cannot be a dependent on the locally unpacked terms. The proper
definition of unpack's typing rule should thus be

    Γ ⊢ t1 : ∃x:T.U   Γ,x:T,y:U ⊢ t2 : V    Γ ⊢ V : ⋆
    --------------------------------------------------
    Γ ⊢ unpack t1 as (x,y) in t2 : V

However, with subtyping and subsumption, `unpack t1 as (x,y) in y` is
typeable! But the type `V` can never be of the form `U[x]`, but a
supertype `U' >: U[x]` that has no free occurrence of `x`.

In the subsequent discussions, we will analyze why this restriction is
necessary and what problems occur for unrestricted strong sigma types.

### NbE for unpack

The usual recipe for NbE is defining an appropriate (partial) function on the
domain that defines the evaluation semantics of an elimination form. Especially, it
requires handling neutral terms, because an eliminator is stuck if the scrutinee
is stuck. First attempt:

    eval_unpack' : Dom -> Dom -> Dom ⇀ Dom
    eval_unpack' (pair D d)      d' = (eval_app (eval_app d' D) d) <- the usual elimination, can be normalized away (assuming the unpack body is a curried function)
    eval_unpack' (↑⟨ ∃D1.D2 ⟩ ne) d' = (↑⟨ ??? ⟩ (unpack ne d'))     <- this shows we need to annotate the unpack eliminator with an explicit result type

The NbE we consider here is type-directed, and thus we need to explicitly annotate
what type of thing the eliminator produces, as an additional argument:

    eval_unpack : Dom -> Dom -> Dom -> Dom ⇀ Dom
    eval_unpack _ (pair D d)      d' = (eval_app (eval_app d' D) d)
    eval_unpack D (↑⟨ ∃D1.D2 ⟩ ne) d' = (↑⟨ D ⟩ (unpack ne (↓⟨ ΠD1.(D2 -> D) ⟩d')))

Here, `D1 -> D2` stands for the encoding `ΠD1.((dlam [D2] #1)) ` of a non-dependent function type.

Remark: I intend to encode partial functions using total functions with fuel, but will
leave the fuel implicit everywhere.

**TODO**: Compare with the strong sigma type.

### Existential Type PER Semantics

What should be the interpretation of an existential type?  For
(strong) Σ-types, we expect that the first components should be
(judgmentally) equal, and for any proof that the first components are
equal, we can produce a proof that the second components are equal
under a type that is dependent on the first projection.  Without
further restrictions, the strong Σ-type leads to logical inconsistency
of the system. For the weak version (i.e., the existential type), we
have to weaken the equality notion accordingly, since the strong
second projection is not definable.  The next best thing we can come
up with is: under all possible eliminations (unpack), the evaluation
yields equal outcomes.

#### Equality in terms of evaluation

**TODO** Also provide the judgmental equality rules.

Let's attempt a PER semantics for the weak existential types:

    ⟦ ∃x:⋆.T ⟧ : ctx -> PER Dom×() =
        η γ ρ => {{ (d1, ()), (d2, ()) |
                    // first components are equal at ⋆
                    ∃ D1 D2, eval_unpack d⋆ d1 (dabs [] (lam #1)) = D1 /\ eval_unpack d⋆ d2 (dabs [] (lam #1)) = D2
                    /\ ∃ 𝒟1 𝒟2, (D1, 𝒟1) == (D2, 𝒟2) ∈ ⟦ ⋆ ⟧ // also entails that we can assign a semantic role living in ⋆
                      // all possible eliminations yield equal outcomes
                    ∀ D3 𝒟3 D3' 𝒟3', (D3,𝒟3) == (D3',𝒟3') ∈ ⟦ ⋆ ⟧,
                         ∃ d3 d3', eval_unpack D3 d1 ??? = d3 /\ eval_unpack D3' d2 ??? = d3'
                                   /\  (d3,()) == (d3',()) ∈ 𝒟3 (and in 𝒟3'!)

We now have the problem of defining the `???` parameters to
`eval_unpack`.  Intuitively, they should be functions (=lambdas in
Dom, the semantic domain for normal forms) from a semantic type and
term pair (from the interpretation ⟦T⟧!) to semantic values living in
`𝒟3`, into which we eliminate the existential. How can we pick
the right semantic values we are looking for? Fortunately, NbE is
type-directed, and we have enough information to
specify the type (also a semantic value!) of these values.
They should be reifiable at the appropriate curried function type,
i.e., every `df ∈ Dom` representing a body for `unpack` qualifies, i.e.,

    ∃ nf, reify n ↓⟨ dΠ d⋆. ??? -> D3 ⟩ df = nf,

where `n` is length of the interpretation context/environment ρ/γ/η
above (needed for converting from deBruijn levels to indices).

The next problem is the type code `???`, which should represent type T
dependent on x:⋆. We have access to `⟦ T ⟧`, but it needs a binding
for `x` (resp. the deBruijn index 0) in the interpretation's environment(s),
specifying 1) a semantic normal form `DX`
representing the type `X` bound to `x`, 2) the kind (⋆ in this case), and
3) the semantic role `𝒳` of `DX`. For types, `𝒳` is the PER of the semantic
values of type `X`, having metalanguage type `PER Dom×()`.
For 1), we may bind the free variable to the neutral term `↑⟨ ⋆ ⟩ $n`, but how
should we choose 2) and 3)? We cannot rely on `⟦ T ⟧`, and all we truly care about
here is the code for T. Instead, we may just normalize `T` using nbe!

    ∃ DT, ((nbe (↑⟨ ⋆ ⟩ $n); η) T) = DT /\ ∃ nf, reify n ↓⟨ dΠ d⋆. DT -> D3 ⟩ df = nf.

Putting everything together, we obtain

    ⟦ ∃x:⋆.T ⟧ : ctx -> PER Dom×() =
        η γ ρ => {{ (d1, ()), (d2, ()) |
                    // first components are equal at ⋆
                    ∃ D1 D2, eval_unpack d⋆ d1 (dabs [] (lam #1)) = D1 /\ eval_unpack d⋆ d2 (dabs [] (lam #1)) = D2
                    /\ ∃ 𝒟1 𝒟2, (D1, 𝒟1) == (D2, 𝒟2) ∈ ⟦ ⋆ ⟧ // also entails that we can assign a semantic role living in ⋆
                    // all possible eliminations yield equal outcomes
                    ∃ DT, ((nbe (↑⟨ ⋆ ⟩ $n); η) T) = DT
                         /\  ∀ D3 𝒟3 D3' 𝒟3', (D3,𝒟3) == (D3',𝒟3') ∈ ⟦ ⋆ ⟧,
                                ∀ df, (∃ nf, reify n ↓⟨ dΠ d⋆. DT -> D3 ⟩ df = nf) ->
                                           ∃ d3 d3', eval_unpack D3 d1 df = d3 /\ eval_unpack D3' d2 df = d3'
                                                     /\  (d3,()) == (d3',()) ∈ 𝒟3

Notably, this definition appeals to the evaluation, normalization and reification functions.

**TODO**: exercise the proof cases for formation, introduction, and elimination in detail.
Intro and elim seem to work out, formation is unclear. The main hardship here is
proving that something is a member of ⟦ ∃x:⋆.T ⟧, because we need to reason
about the `nbe`, `reify` and `eval_unpack` functions.
**TODO**: Refer to Sam Lindley's talk slides on the general problem of NbE with these kinds of
eliminators. This phenomenon also occurs for any kind of type with a case/pattern matching
eliminator, such as sums.

#### Equality by reducing to universal quantification

It is well-known that

    ∃x:⋆.T ≡ ∀α:⋆.((β : ⋆) → T[β] → α) → α ≡ Πα:⋆.(Π_:(Πβ:⋆.Π_:T[β].α). α)

and unsurprisingly, we have a corresponding occurrence in the
evaluation-based semantics above, since we reify eliminators at
`↓⟨ dΠ d⋆. DT -> D3 ⟩`. That version does not need any fancy metalanguage
acrobatics. However, instead of an object-level description, we may
also define the semantics for ∃ in terms of the semantics of Π (given
in Abel's paper) at the meta level. By mechanically translating the
above equation, we should obtain

    ⟦ ∃x:⋆.T ⟧ : ctx -> PER Dom×() =
        η γ ρ => ℿ ⟦ ⋆ ⟧ (𝝺 (𝝰,𝒜) ⇒
                                   ℿ (ℿ ⟦ ⋆ ⟧ (𝝺 (𝝱,ℬ) ⇒
								                         ℿ ( ⟦ T ⟧(𝝱;η|⋆;γ|ℬ;ρ) ) (𝝺 _ ⇒ 𝒜)))
                                     (𝝺 _ ⇒ 𝒜))

Here, I neglected the (erased) kind parameters 𝓀, 𝓁 for ℿ. Given the ⟪ ⋄ ⟫
vs. ⟪ ∗ ⇒ ⋄ ⟫ problem above, we should check if this works out, expecting
that we need to coerce one into the other in places.
Let's look at the different ℿs in the above expression (from innermost to outermost):

1. `ℿ ( ⟦ T ⟧(𝝱;η|⋆;γ|ℬ;ρ) ) (𝝺 _ ⇒ 𝒜)` has `𝓀 = 𝓁 = ⋄`, thus type `⟪ ⋄ ⇒ ⋄ ⟫`, which is marked as a dependent function space in the Abel paper.
    On the other hand, ⋄ ⇒ ⋄ is not a legal erased kind. I suppose it needs to be coerced into just ⋄, analogously to the `∗ ⇒ ⋄` case.
2. `ℿ ⟦ ⋆ ⟧ (𝝺 (𝝱,ℬ) ⇒ {no 1.})` has `𝓀 = ∗` and `𝓁 = ⋄ ⇒ ⋄`, thus type `⟪ ∗ ⇒ ⋄ ⇒ ⋄ ⟫`.
3. `ℿ {no. 2} (𝝺 _ ⇒ 𝒜)` has `𝓀 = ∗ ⇒ ⋄ ⇒ ⋄ ` and `𝓁 = ⋄`, thus type `⟪ (∗ ⇒ ⋄ ⇒ ⋄) ⇒ ⋄ ⟫`.
4. `ℿ ⟦ ⋆ ⟧ (𝝺 (𝝰,𝒜) ⇒ {no. 3})` has `𝓀 = ∗` and `𝓁 = (∗ ⇒ ⋄ ⇒ ⋄) ⇒ ⋄`, thus type `⟪ ∗ ⇒ (∗ ⇒ ⋄ ⇒ ⋄) ⇒ ⋄ ⟫`.

In the end, we expect ⟦ ∃x:⋆.T ⟧ to be the interpretation of a type, which is of metalanguage type `PER Dom×()`, i.e.,
the normal forms living in this type. Since these have no particular semantic role, they are paired with the unit value.
But `⟪ ∗ ⇒ (∗ ⇒ ⋄ ⇒ ⋄) ⇒ ⋄ ⟫` indicates the metalanguage type is `PER Dom×<some function space>`.
We must insist that both ∗ ⇒ ⋄ and ⋄ ⇒ ⋄ are equivalent to ⋄, due to impredicativity of the object language.
That seems to be a rather annoying technical detail if we were to attempt this approach in Coq,
and could probably be mitigated by having multiple specialized definitions of ℿ.

#### Type-level projection

As noted above, we have to treat the first projection of an existential type differently, since it
is a type-level computation. `t.type = unpack ⋆ t as (x,y) in x`

    ⟦ unpack ⋆ t as (x,y) in x ⟧ : ctx -> PER Dom×()

We want the unpack to be the PER that contains the equivalence class of the first component x.
Since we have the `nbe` function, it does not pose a problem to provide an interpretation
for the term `t` and the entire unpack expression:

    ⟦ unpack ⋆ t as (x,y) in x ⟧ =
        η γ ρ => {{ (d1,()), (d2,()) | ∃ X : Dom, nbe η (unpack ⋆ t as (x,y) in x) = X
                                         /\ ∃ 𝒳 : ⟨ ⋆ ⟩, (X, 𝒳) ∈ dom ⟦ ⋆ ⟧ /\ (d1, ()) == (d2,()) ∈ 𝒳 }}

The interpretation of unpack should contain all the "equal" semantic values that are living
in the interpretation of the type we are projecting out of the existential.

Consider now the respective case of the fundamental lemma, using the definitions we developed thus far:

    IH1:     Γ ⊢ t1 : ∃x:⋆.T                  --> (nbe t1, ()) == (nbe t1, ()) ∈ ⟦ ∃x:⋆.T ⟧ : PER Dom×()
    IH2:     Γ,x:⋆,y:T ⊢ x : ⋆                --> (nbe x, ⟦ x ⟧) == (nbe x, ⟦ x ⟧) ∈ ⟦ ⋆ ⟧  : Per Dom×⟨ ⋆ ⟩
                                         trivial, since x will be bound in an env assigning an appropriate semantic element
             --------------------------------
    Goal:    Γ ⊢ unpack ⋆ t1 as (x,y) in x : ⋆  --> (nbe unpack t1 ..., ⟦unpack ... ⟧) == (nbe unpack t1, ⟦unpack ... ⟧) ∈ ⟦ ⋆ ⟧ : PER Dom×⟨ ⋆ ⟩

First, by definition of `nbe` we have that

    nbe η (unpack ⋆ t1 as (x,y) in x) = eval_unpack d⋆ (nbe t1) (dabs [] (lam #1))

By IH1 and definition of `⟦ ∃x:⋆.T ⟧`, we have

    // first components are equal at ⋆
    ∃ D1 D2, eval_unpack d⋆ (nbe t) (dabs [] (lam #1)) = D1 /\ eval_unpack d⋆ (nbe t) (dabs [] (lam #1)) = D2
            /\ ∃ 𝒟1 𝒟2, (D1, 𝒟1) == (D2, 𝒟2) ∈ ⟦ ⋆ ⟧ // also entails that we can assign a semantic role living in ⋆

which is to say

    ∃ X : Dom, nbe η (unpack ⋆ t1 as (x,y) in x) = X /\ ∃ 𝒳 : ⟨ ⋆ ⟩, (X,𝒳) ∈ dom ⟦ ⋆ ⟧

Now we need to show `(X, ⟦unpack ⋆ t1 ... ⟧) == (X, ⟦unpack ⋆ t1 ... ⟧) ∈ ⟦ ⋆ ⟧`.
Is the `𝒳` from above good enough? I.e., is it the case that `𝒳 ⊆ ⟦unpack ⋆ t1 ... ⟧` and
`⟦unpack ⋆ t1 ... ⟧ ⊆ 𝒳`? Intuitively it should, since ⟦ ⋆ ⟧ is a PER and the coherence
conditions ensure that `(X,𝒳) ∈ dom ⟦ ⋆ ⟧` and `(X,𝒴) ∈ dom ⟦ ⋆ ⟧` implies `𝒳 ≡ 𝒴`
(cf. "equality candidates" in the Abel paper).

The `⊆` direction is trivial. ✓

The `⊇` direction is also straightforward:

Assume `(d1,()) == (d2,()) ∈ ⟦unpack ⋆ t1 ... ⟧`, hence

    ∃ Y : Dom, nbe η (unpack ⋆ t as (x,y) in x) = Y
                                         /\ ∃ 𝒴 : ⟨ ⋆ ⟩, (Y, 𝒴) ∈ dom ⟦ ⋆ ⟧ /\ (d1, ()) == (d2,()) ∈ 𝒴

By determinism of `nbe`, we obtain `X = Y` and hence

    ∃ 𝒴 : ⟨ ⋆ ⟩, (X, 𝒴) ∈ dom ⟦ ⋆ ⟧ /\ (d1, ()) == (d2,()) ∈ 𝒴

By the coherence conditions of ⟦ ⋆ ⟧, `𝒳 ≡ 𝒴` are equivalent sets, thus `(d1, ()) == (d2,()) ∈ 𝒳`. ✓

**TODO** Compare to the vseta construction from ECOOP. It generally lacks such a coherence condition
(should probably demand it).

## Sigma Types

### Formation

    Γ ⊢ T : s1
    Γ,x:T ⊢ U : s2
    -----------------------
    Γ ⊢ Σx:T.U : max(s1,s2)

where `⋆ ≤ ◻`. For each instantiation of `s1` and `s2`, the fundamental lemma case is different.

Case `s1 = s2 = ⋆`:

    Γ ⊢ T : ⋆                    --> (nbe T, ⟦T⟧) == (nbe T, ⟦T⟧) ∈ ⟦ ⋆ ⟧ : ⟪ ⋆ ⟫ = PER Dom×(PER Dom×())
    Γ, x:T ⊢ U : ⋆               --> (nbe U, ⟦U⟧) == (nbe U, ⟦U⟧) ∈ ⟦ ⋆ ⟧ : ⟪ ⋆ ⟫ = PER Dom×(PER Dom×())
    ---------------------------
    Γ ⊢ Σx:T.U : ⋆               --> (nbe Σx:T.U, ⟦Σx:T.U⟧) == (nbe Σx:T.U, ⟦Σx:T.U⟧) ∈ ⟦ ⋆ ⟧

Case `s1 = ◻`, `s2 = ⋆`:

    Γ ⊢ κ : ◻                    --> (nbe κ, ⟦ |κ| ⟧) == (nbe κ, ⟦ |κ| ⟧) ∈ eq(|κ|): ⟪ |κ| ⟫ = PER Dom×⟨ |κ| ⟩ (semantic role depends on shape of κ)
    Γ, x:κ ⊢ U : ⋆               --> (nbe U, ⟦U⟧) == (nbe U, ⟦U⟧) ∈ ⟦ ⋆ ⟧ : ⟪ ⋆ ⟫ = PER Dom×(PER Dom×())
    ---------------------------
    Γ ⊢ Σx:κ.U : ◻               --> (nbe Σx:κ.U, ⟦ |Σx:κ.U| ⟧) == (nbe Σx:κ.U., ⟦ |Σx:κ.U| ⟧) ∈ eq(|Σx:κ.U|)

Note the difference to the formation rule of the existential type in the conclusion.
There is no uniform box interpretation ⟦ ◻ ⟧ in the model, but for each κ that we can type as ◻,
we demand that (nbe κ, ⟦ |κ| ⟧) is related to itself in the PER eq(|κ|). Here, `eq` is the "double overbar" operator
(cf. "equality of candidates" in the Abel paper), and `|κ|` is the skeleton (i.e. erased form) of kind `κ`.

Case `s1 = ⋆`, `s2 = ◻`:

    Γ ⊢ T : ⋆                    --> (nbe T, ⟦T⟧) == (nbe T, ⟦T⟧) ∈ ⟦ ⋆ ⟧ : ⟪ ⋆ ⟫ = PER Dom×(PER Dom×())
    Γ, x:T ⊢ κ : ◻               --> (nbe κ, ⟦ |κ| ⟧) == (nbe κ, ⟦ |κ| ⟧) ∈ eq(|κ|): ⟪ |κ| ⟫ = PER Dom×⟨ |κ| ⟩
    ---------------------------
    Γ ⊢ Σx:T.κ : ◻               --> (nbe Σx:T.κ, ⟦ |Σx:T.κ| ⟧) == (nbe Σx:T.κ, ⟦ |Σx:T.κ| ⟧) ∈ eq(|Σx:T.κ|)

Case `s1 = ◻`, `s2 = ⋆`: Similar to previous case.

Case `s1 = s2 = ◻`:

    Γ ⊢ κ1 : ◻                   --> (nbe κ1, ⟦ |κ1| ⟧) == (nbe κ1, ⟦ |κ1| ⟧) ∈ eq(|κ1|): ⟪ |κ1| ⟫ = PER Dom×⟨ |κ1| ⟩
    Γ, x:κ1 ⊢ κ2 : ◻             --> (nbe κ2, ⟦ |κ2| ⟧) == (nbe κ2, ⟦ |κ2| ⟧) ∈ eq(|κ2|): ⟪ |κ2| ⟫ = PER Dom×⟨ |κ2| ⟩
    ---------------------------
    Γ ⊢ Σx:κ1.κ2 : ◻             --> (nbe Σx:κ1.κ2, ⟦ |Σx:κ1.κ2| ⟧) == (nbe Σx:κ1.κ2, ⟦ |Σx:κ1.κ2| ⟧) ∈ eq(|Σx:κ1.κ2|)

What about the forbidden/inconsistent combinations? It is not apparent at this point what could go wrong.

### Kind Erasure and Interpretation for Σ

Kind erasure eliminates term-dependency in kinds, thus requiring
different semantic interpretations of the Σ type variants. We can
analogously adapt the interpretations from Geuvers' 1994 paper into
the Abel framework:

Simple kind syntax :

    k ::= ... | k ⊗ k

(I use ⊗ as a syntactic symbol, to avoid confusion with the metalanguage product type)

Erasure from terms into simple kinds:

    |Σx:T.U|   = case |T|, |U| of
                 | ♢,  ♢  -> ♢       <-- term-level content is erased, so no semantic role at kind level
                 | k,  ♢  -> k       <-- for the same reason, only the first component is relevant
                 | ♢,  k  -> k       <-- and so is the second component here
                 | k1, k2 -> k1 ⊗ k2 <-- proper product of kinds, both components are relevant
    | π1 T |   = k1 if |T| = k1 ⊗ k2
                 ♢  otherwise
    | π2 T |   = k2 if |T| = k1 ⊗ k2
                 ♢  otherwise

Accordingly, the raw kind interpretation is

    ⟨ k1 ⊗ k2 ⟩ = ⟨ k1 ⟩ × ⟨ k2 ⟩

Notably, ⟨ k1 ⊗ k2 ⟩ denotes a non-dependent product type.

Example:

    ⟪ |Σx:⋆.⋆| ⟫ = PER Dom × (⟨ ⋆ ⟩ × ⟨ ⋆ ⟩) = PER Dom × ((PER Dom×()) × (PER Dom×())

defines the semantic type of dependent pairs of types, i.e., it tags
semantic normal forms of pairs of types with their semantic role, which is
the product of the semantic roles of the components.

### Introduction

As before, we need a case distinction for the different Σ-type
variants in the fundamental lemma.  To make the proof go through
smoothly, it makes sense to strengthen the rules with evidence how the
respective Σ-type is classified by the system.  This is usually
handled by a classification theorem about the type system, but then we
would not obtain any usable induction hypothesis about the Σ-type's components.

Case `s1 = s2 = ⋆`:

    Γ ⊢ t1 : T           --> (nbe t1, ())^2    ∈ ⟦ T ⟧
    Γ ⊢ t2 : U[t1/x]     --> (nbe t2, ())^2    ∈ ⟦ U[t1/x] ⟧ <-- note: we have explicit substitutions in the calculus and a semantics for substitutions (not shown here)
    Γ ⊢ T : ⋆            --> (nbe T,  ⟦ T ⟧)^2 ∈ ⟦ ⋆ ⟧
    Γ,x:T ⊢ U : ⋆        --> (nbe U,  ⟦ U ⟧)^2 ∈ ⟦ ⋆ ⟧
    --------------------
    Γ ⊢ (t1,t2) : Σx:T.U --> (nbe (t1,t2), ())^2 ∈ ⟦ Σx:T.U ⟧ : Per Dom×⟨ |Σx:T.U| ⟩ = Per Dom×⟨ ♢ ⟩ = Per (Dom×())

Case `s1 = ◻`, `s2 = ⋆`:

    Γ ⊢ t1 : κ           --> (nbe t1, ⟦ t1 ⟧)^2  ∈ ⟦ |κ| ⟧
    Γ ⊢ t2 : U[t1/x]     --> (nbe t2, ())^2     ∈ ⟦ U[t1/x] ⟧
    Γ ⊢ κ : ◻            --> (nbe κ,  ⟦ |κ| ⟧)^2 ∈ eq(|κ|)
    Γ,x:κ ⊢ U : ⋆        --> (nbe U,  ⟦ U ⟧)^2   ∈ ⟦ ⋆ ⟧
    --------------------
    Γ ⊢ (t1,t2) : Σx:κ.U --> (nbe (t1,t2), ⟦ (t1,t2) ⟧)^2 ∈ ⟦ Σx:κ.U ⟧ : Per Dom×⟨ |Σx:κ.U| ⟩ = Per Dom×⟨ |κ| ⟩

This case shows how we need to deal with the `⟦ (t1,t2) ⟧` interpretation: It crucially depends
on the formation of the Σ type! In this case, only the first component's semantics matters,
by the kind erasure definition. Thus ⟦ (t1,t2) ⟧ = ⟦ t1 ⟧.

Case `s1 = ⋆`, `s2 = ◻`: Similar to the previous case, but this time, the second component counts: ⟦ (t1,t2) ⟧ = ⟦ t2 ⟧.

Case `s1 = s2 = ◻`:

	Γ ⊢ t1 : κ1            --> (nbe t1, ⟦ t1 ⟧)^2  ∈ ⟦ |κ| ⟧
    Γ ⊢ t2 : κ2[t1/x]      --> (nbe t2, ⟦ t2 ⟧)^2  ∈ ⟦ κ2[t1/x] ⟧
    Γ ⊢ κ1 : ◻             --> (nbe κ1, ⟦ |κ1| ⟧)^2 ∈ eq(|κ1|)
    Γ,x:κ1 ⊢ κ2 : ◻        --> (nbe κ1, ⟦ |κ1| ⟧)^2 ∈ eq(|κ1|)
    ---------------------
    Γ ⊢ (t1,t2) : Σx:κ1.κ2 --> (nbe (t1,t2), ⟦ (t1,t2) ⟧)^2 ∈ ⟦ Σx:κ1.κ2 ⟧ : Per Dom×⟨ |Σx:κ1.κ2| ⟩ = Per Dom×⟨ |κ1|×|κ2| ⟩

Thus, ⟦ (t1,t2) ⟧ = (⟦ t1 ⟧, ⟦ t2 ⟧).

#### Avoiding non-uniform pair interpretations

It is a bit unwieldy to let ⟦ (t1,t2) ⟧ have non-uniform shape, since we would need to pass additional context information for the
definition. Since `⟨ ♢ ⟩ = unit`, we could simplify the erasure to be |Σx:T.U| = |T| ⊗ |U|, and thus
⟨ |Σx:κ1.κ2| ⟩ = |κ1|×|κ2| and  ⟦ (t1,t2) ⟧ = (⟦ t1 ⟧, ⟦ t2 ⟧) once and for all.
For instance, the `s1 = ⋆`, `s2 = ◻` case would interpret ⟦ (t1,t2) ⟧ as a `Per Dom×⟨ ♢ ⊗ |κ| ⟩ = Per Dom×⟨ ♢ ⊗ |κ| ⟩ = Per Dom×(unit × ⟨ |κ| ⟩)`
which is isomorphic to `Per Dom×⟨ |κ| ⟩`. We could handle this in a similar manner
to the impredicativity problem, i.e., treat type `unit × ⟨ |κ| ⟩` as `⟨ |κ| ⟩` and vice versa by appropriate conversions.

### Elimination

Again, we need the sortedness evidence for respective components of the Σ type.
For brevity, we do not explicitly spell these out in the assumptions.

Case `s1 = s2 = ⋆`:

    Γ ⊢ t : Σx:T.U       --> (nbe t, ())^2 ∈ ⟦ Σx:κ.U ⟧ : Per Dom×()
    --------------
    Γ ⊢ π1 t : T         --> (nbe (π1 t), ())^2 ∈ ⟦ T ⟧

    Γ ⊢ t : Σx:T.U       --> (nbe t, ())^2 ∈ ⟦ Σx:T.U ⟧
    ------------------
    Γ ⊢ π2 t : U[π1 t/x] --> (nbe (π2 t), ())^2 ∈ ⟦ U[π1 t/x] ⟧

(Note: In the explicit substitution model, `U[π1 t/x]` will normalize the first projection and extend the environment with a binding,
which is then used to interpret `U`).

Case `s1 = ◻`, `s2 = ⋆`:

    Γ ⊢ t : Σx:κ.U       --> (nbe t, ⟦ t ⟧)^2 ∈ ⟦ Σx:κ.U ⟧ : Per Dom×⟨ |Σx:κ.U| ⟩ = Per Dom×⟨ |κ| ⊗ |U| ⟩ = Per Dom×(⟨|κ|⟩×unit) ≅ Per Dom×⟨|κ|⟩
    --------------
    Γ ⊢ π1 t : κ         --> (nbe (π1 t), ⟦π1 t⟧)^2 ∈ ⟦ |κ| ⟧

    Γ ⊢ t : Σx:κ.U       --> (nbe t, ⟦ t ⟧)^2 ∈ ⟦ Σx:κ.U ⟧
    ------------------
    Γ ⊢ π2 t : U[π1 t/x] --> (nbe (π2 t), ())^2 ∈ ⟦ U[π1 t/x] ⟧

Note that Σx:κ.U is a *kind* (by the formation rules), while U[π1 t/x] is a *type*.
If we were to treat Σx:κ.U as a type (violating the max rule), then we run into an inconsistency
in the fundamental lemma for the premise Γ ⊢ t : Σx:κ.U. With the max rule, the interpretation ⟦ Σx:κ.U ⟧
has type

    Per Dom×⟨ |Σx:κ.U| ⟩ = Per Dom×⟨ |κ| ⊗ |U| ⟩ = Per Dom×(⟨|κ|⟩×unit) ≅ Per Dom×⟨|κ|⟩

i.e., the erasure semantics treats Σx:κ.U the same as the kind κ! If Σx:κ.U was a type instead, then
the type of ⟦ Σx:κ.U ⟧ should be Per Dom×(), or something isomorphic to that type.

Clearly, Per Dom×⟨|κ|⟩ is not isomorphic to Per Dom×(), e.g., type Per Dom×⟨ ⋆ ⟩ = Per Dom×(Per Dom×())
has more values (partial equivalence relations) than type Per Dom×().

However, this is not necessarily a strong case against violating the
max rule. It just points out that the model construction is flawed if
we violate that rule. There could still be a better model out there
not requiring max rule. The literature tells us of course that we
won't find such a model.

Case `s1 = ⋆`, `s2 = ◻`:

    Γ ⊢ t : Σx:T.κ       --> (nbe t, ⟦ t ⟧)^2 ∈ ⟦ Σx:T.κ ⟧ : Per Dom×⟨ |Σx:T.κ| ⟩ = Per Dom×⟨ |T| ⊗ |κ| ⟩ = Per Dom×(unit×⟨|κ|⟩) ≅ Per Dom×⟨|κ|⟩
    --------------
    Γ ⊢ π1 t : T         --> (nbe (π1 t), ())^2 ∈ ⟦ T ⟧ : Per Dom×() !

    Γ ⊢ t : Σx:T.κ       --> (nbe t, ⟦ t ⟧)^2 ∈ ⟦ Σx:T.κ ⟧
    ------------------
    Γ ⊢ π2 t : κ[π1 t/x] --> (nbe (π2 t), ⟦ π2 t ⟧)^2 ∈ ⟦ κ[π1 t/x] ⟧ : Per Dom×⟨|κ|⟩

Case `s1 = ◻`, `s2 = ◻`:

    Γ ⊢ t : Σx:κ1.κ2     --> (nbe t, ⟦ t ⟧)^2 ∈ ⟦ Σx:κ1.κ2 ⟧ : Per Dom×⟨ |Σx:κ1.κ2| ⟩ = Per Dom×(⟨|κ1|⟩×⟨|κ2|⟩)
    --------------
    Γ ⊢ π1 t : κ1        --> (nbe (π1 t), ⟦π1 t⟧)^2 ∈ ⟦ κ1 ⟧ : Per Dom×⟨|κ1|⟩

    Γ ⊢ t : Σx:κ1.κ2     --> (nbe t, ⟦ t ⟧)^2 ∈ ⟦ Σx:κ1.κ2 ⟧
    ------------------
    Γ ⊢ π2 t : κ2[π1 t/x] --> (nbe (π2 t), ⟦ π2 t ⟧)^2 ∈ ⟦ κ2[π1 t/x] ⟧ : Per Dom×⟨|κ2|⟩

#### Evaluation

The evaluation of the eliminators is straightforward:

    eval_pi1 : Dom ⇀ Dom
    eval_pi1 (dpair d1 d2)   = d1
    eval_pi1 (↑⟨ ΣD1.D2 ⟩ ne) = ↑⟨ D1 ⟩ (π1 ne)

    eval_pi2 : Dom ⇀ Dom
    eval_pi2 (dpair d1 d2)   = d2
    eval_pi2 (↑⟨ ΣD1.D2 ⟩ ne) = ↑⟨ eval_app D2 (eval_pi1 (↑⟨ D1 ⟩ π1 ne))⟩ (π2 ne)

### Sigma Type PER Semantics

With the two projections, the semantics is straightforward:

    ⟦ Σx:T.U ⟧   = η γ ρ => {{ (d1, ()) (d2, ()) | ∃ D1, D2, eval_pi1 d1 = D1 /\ = eval_pi1 d2 = D2 /\ (D1,()) == (D2,()) ∈ ⟦ T ⟧(η|γ|ρ)
                                                            /\ ∃ D'1 D'2, eval_pi2 d1 = D'1 /\ eval_pi2 d2 = D'2 /\ (D'1,()) == (D'2,()) ∈ ⟦ U ⟧(D1;η|⋆;γ|();ρ) }}

    ⟦ Σx:κ.U ⟧   = η γ ρ => {{ (d1, (𝒟1,())) (d2, (𝒟2,())) | ∃ D1, D2, eval_pi1 d1 = D1 /\ = eval_pi1 d2 = D2 /\ (D1,𝒟1) == (D2,𝒟2) ∈ ⟦ κ ⟧(η|γ|ρ)
                                                                      /\ ∃ D'1 D'2, eval_pi2 d1 = D'1 /\ eval_pi2 d2 = D'2 /\ (D'1,()) == (D'2,()) ∈ ⟦ U ⟧(D1;η|⋆;γ|𝒟1;ρ) }}

    ⟦ Σx:T.κ ⟧   = η γ ρ => {{ (d1, ((),𝒟1)) (d2, ((),𝒟2)) | ∃ D1, D2, eval_pi1 d1 = D1 /\ = eval_pi1 d2 = D2 /\ (D1,()) == (D2,()) ∈ ⟦ T ⟧(η|γ|ρ)
                                                                      /\ ∃ D'1 D'2, eval_pi2 d1 = D'1 /\ eval_pi2 d2 = D'2 /\ (D'1,𝒟1) == (D'2,𝒟2) ∈ ⟦ κ ⟧(D1;η|⋆;γ|();ρ) }}

    ⟦ Σx:κ1.κ2 ⟧ = η γ ρ => {{ (d1, (𝒟1,𝒟'1)) (d2, (𝒟2,𝒟'2)) | ∃ D1, D2, eval_pi1 d1 = D1 /\ = eval_pi1 d2 = D2 /\ (D1,𝒟1) == (D2,𝒟1) ∈ ⟦ κ1 ⟧(η|γ|ρ)
                                                                         /\ ∃ D'1 D'2, eval_pi2 d1 = D'1 /\ eval_pi2 d2 = D'2 /\ (D'1,𝒟'1) == (D'2,𝒟'2) ∈ ⟦ κ2 ⟧(D1;η|⋆;γ|𝒟1;ρ) }}

We can define the semantics of the various Σ-types in a single parametric metalanguage definition, just as with ℿ:

    𝝨 𝒳 𝒴 := {{ (d1, (𝒟1, 𝒟'1)) (d2, (𝒟2,𝒟'2)) | ∃ D1, D2, eval_pi1 d1 = D1 /\ = eval_pi1 d2 = D2 /\ (D1,𝒟1) == (D2,𝒟2) ∈ 𝒳
                                                             /\ ∃ D'1 D'2, eval_pi2 d1 = D'1 /\ eval_pi2 d2 = D'2 /\ (D'1,𝒟'1) == (D'2,𝒟'2) ∈ (𝒴 (D1,𝒟1)) }}

Here, it shows that it is useful to have uniform pair interpretations for all possible Σ-type variations, even the ones
where one or more components are erased to unit.
**TODO**: spell the full metalanguage type signature of the above definition.

For instance, the interpretation for `s1 = s2 = ⋆` becomes

     ⟦ Σx:T.U ⟧ = η γ ρ => 𝝨 (⟦ T ⟧(η|γ|ρ)) (𝝺 (D1,𝒟1) ⇒ ⟦ U ⟧(D1;η|⋆;γ|𝒟1;ρ))

the other cases are similar.

#### Why Restrict Formation?

**TODO**

## From Existentials to Bounded Abstract Types

**TODO**
