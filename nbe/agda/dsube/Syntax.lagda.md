# System Dᵉ<:>

An extrinsically-typed for the System Dᵉ<:> calculus in Agda, using a
PTS-style formulation that puts types and terms into the same
syntactic category.  We follow Andreas Abel's thesis for defining NbE
and its metatheory.

```agda
module dsube.Syntax where

open import Data.Nat using (ℕ; zero; suc; _≤′_; _<′_)

```
# Syntax of Dᵉ<:>

Building on Abel's development, we design System Dᵉ<:> as a
predicative system which includes cumulative universes via a subtyping
relation. Thus, his formalization already has important traits we need
for Dᵉ<:>/EDOT. Since he scales his approach to impredicative
quantifiers later on, we expect to find a reasonable
language design that restores impredicativity in the future.

Accordingly, we introduce a countable sets of sorts/universe levels
```agda
ℒ = ℕ
```
and types/kinds `𝑆𝑒𝑡 k`, with the expectation that `𝑆𝑒𝑡 𝒾 ≤ 𝑆𝑒𝑡 𝒿` whenever `𝒾 ≤ 𝒿`.

We group the syntax in to constants Cst and composable expressions Exp.
Constants are either type-level (base types) or term-level (constructors, primitives).
```agda
data Cst : Set where
  𝑁   : Cst     -- nat type
  𝑧   : Cst     -- zero constructor
  𝑠   : Cst     -- succ constructor
  𝑆𝑒𝑡 : ℒ → Cst -- Set_k
  ⊤'  : Cst     -- Top
  ⊥'  : Cst     -- Bottom
```
Note that Abel also includes non-atomic type symbols in the constants, e.g., Π, and
supports partial application/currying. For simplicity, we refrain from doing it.

We reserve ⋆ for the lowest universe, the "types". For readability, ⋆
is overloaded to both mean the lowest sort and the respective constant
symbol.

```agda
pattern ⋆ = 0
pattern ⋆ = 𝑆𝑒𝑡 0
```

Abel's approach is based on a big-step semantics, not unlike the work
by Amin and Rompf, where the semantic domain contains function
closures. He points out an anomaly with closures: if one were to have
an external substitution operation (which is common), then examples
can be constructed where the logical relation (semantic equality)
fails to equate two semantic values which should be "equal" according
to the β-rule in the syntactic definitional equality. This anomaly is
not exhibited by an explicit substitution application syntax, where a
sensible operational semantics for substitution in terms of
environment extension can be defined. We follow suit and add explicit
substitution.

Next, we define the syntax of expressions and substitutions:
```agda
𝒱𝒶𝓇 = ℕ -- Variables. Note: syntax has deBruijn *indices*, whereas semantics will have deBruijn *levels*

data Exp   : Set
data Subst : Set

data Exp where
  `_        : Cst → Exp
  ♯_        : 𝒱𝒶𝓇   → Exp
  Π         : Exp → Exp   → Exp -- concrete Π-types take the form Π S (ƛ T)
  ƛ         : Exp → Exp
  _·_       : Exp → Exp   → Exp
  _·ₛ_      : Exp → Subst → Exp
  ⟨Type_⋯_⟩ : Exp → Exp   → Exp
  Type      : Exp → Exp
  ⟨_⟩∙Type  : Exp → Exp
  -- TODO: add conditionals, to make it more interesting?

data Subst where
  Id   : Subst
  ↑    : Subst
  _∘ₛ_ : Subst → Subst → Subst
  _,ₛ_ : Subst → Exp   → Subst

-- convenience notation for non-dependent function types
pattern _⇒_ S T = Π S (ƛ (T ·ₛ ↑)) -- i.e., abstract over a dummy variable in codomain, cf. Abel2013
-- convenience notation for single substitution
pattern _[_] e e' = e ·ₛ (Id ,ₛ e')

infixl 7 _·_
infixl 7 _·ₛ_
infixr 7 _⇒_
infixl 3 _,ₛ_
infixr 8 _∘ₛ_
infix 9 ♯_
```

# Syntactic Normal Forms

Normal forms are expressions free of any reduction opportunity, even under binders.

```agda
data Nf : Exp → Set
data Ne : Exp → Set

data Nf where
  Nf-cst     : ∀(c : Cst) → Nf (` c)
  Nf-Π       : ∀{S T}     → Nf S     → Nf T        → Nf (Π S T)
  Nf-ƛ       : ∀{e}       → Nf e     → Nf (ƛ e)
  Nf-⟨Type⋯⟩ : ∀{S T}     → Nf S     → Nf T        → Nf ⟨Type S ⋯ T ⟩
  Nf-Type    : ∀{T}       → Nf T     → Nf (Type T)
  Nf-𝑠·      : ∀{e}       → Nf e     → Nf ((` 𝑠) · e)
  Nf-ne      : ∀{e}       → Ne e     → Nf e

data Ne where
  Ne-Var   : ∀{x}    → Ne (♯ x)
  Ne-·     : ∀{ne e} → Ne ne   → Nf e         → Ne (ne · e)
  Ne-𝑠·    : ∀{ne} → Ne ne   → Ne ((` 𝑠) · ne)
  Ne-∙Type : ∀{ne}   → Ne ne   → Ne ⟨ ne ⟩∙Type

```

# Type Assignment

## Constant Typing

First, we define typing of constants, which is context-free:

```agda
infix 3 _⊢ᶜ_
data _⊢ᶜ_ : Cst → Exp → Set where
  T𝑁 : ∀ s →
       ----------- -- TODO: needed when having subsumption? have it just at S 0?
       𝑁 ⊢ᶜ `(𝑆𝑒𝑡 s)

  T𝑧 : --------
       𝑧 ⊢ᶜ ` 𝑁

  T𝑠 : ---------------------
       𝑠 ⊢ᶜ ((` 𝑁) ⇒ (` 𝑁))

  T𝑆𝑒𝑡 : ∀{𝒾 𝒿 : ℒ} → 𝒾 <′ 𝒿 → -- TODO make this evidence implicit?
       ------------------------
       𝑆𝑒𝑡 𝒾 ⊢ᶜ ` (𝑆𝑒𝑡 𝒿)

  T⊤ : ∀{𝒾} →
       ------------ -- TODO is this sensible? needed when having subsumption? have it just at S 0?
       ⊤' ⊢ᶜ ` (𝑆𝑒𝑡 𝒾)

  T⊥ : ∀{𝒾} →
       ------------ -- TODO is this sensible? needed when having subsumption? have it just at S 0?
       ⊥' ⊢ᶜ ` (𝑆𝑒𝑡 𝒾)
```

## Typing Contexts

Next, we define variable contexts and lookup of deBruijn indices:

```agda
data Ctx : Set where -- TODO: better us a list data type?
  ∅   : Ctx
  _,_ : Ctx → Exp → Ctx

infixl 3 _,_

ctx-length : Ctx → ℕ
ctx-length ∅ = 0
ctx-length (Γ , _) = suc (ctx-length Γ)

-- variable lookup, note that we lift the result according to its position
data _⟨_⟩==_ : Ctx → 𝒱𝒶𝓇 → Exp → Set where
  VZ : ∀ {Γ T} →
       ------------------------
       (Γ , T) ⟨ 0 ⟩== (T ·ₛ ↑)

  VS : ∀ {Γ S T i} →
       Γ ⟨ i ⟩== S →
       ----------------------------
       (Γ , T) ⟨ suc i ⟩== (S ·ₛ ↑)

```

And then a whole bunch of mutually dependent judgments:

```agda
-- context well-formedness
data ⊢ᶜᵗˣ    : Ctx →  Set
-- type is well-formed under context
data _⊢_     (Γ : Ctx) : Exp → Set
-- expression typing, careful: use \: for the colon for this and other judgments
data _⊢_∶_   : Ctx → Exp → Exp → Set
-- substitution typing
data _⊢ˢᵘᵇ_∶_  : Ctx → Subst → Ctx → Set
-- subtyping
data _⊢_<∶_  : Ctx → Exp → Exp → Set
-- definitional equality
data _⊢_≈_∶_ : Ctx → Exp → Exp → Exp → Set
-- substitution equality
data _⊢ˢᵘᵇ_≈_∶_ : Ctx → Subst → Subst → Ctx → Set

infix 3 _⊢_
infix 4 _⊢_∶_
infix 4 _⊢ˢᵘᵇ_∶_
infix 4 _⊢_<∶_
infix 5 _⊢_≈_∶_
infix 5 _⊢ˢᵘᵇ_≈_∶_
```

## Well-formed Contexts

```agda
data ⊢ᶜᵗˣ where
  wf∅   :  ⊢ᶜᵗˣ ∅

  wf-,- : ∀ {Γ T} →
          ⊢ᶜᵗˣ Γ →
          Γ ⊢ T →
          ------------
          ⊢ᶜᵗˣ (Γ , T)
```

## Well-formed Types

```agda
data _⊢_ Γ where
  wf-ty : ∀ {T 𝓁} →
          Γ ⊢ T ∶ `(𝑆𝑒𝑡 𝓁) →
          ----------------
          Γ ⊢ T
```

## Typing Relation

```agda
data _⊢_∶_ where
  TCst : ∀ {Γ c T} →
         ⊢ᶜᵗˣ Γ →
         c ⊢ᶜ T →
         -----------
         Γ ⊢ ` c ∶ T

  TVar : ∀ {Γ n T} →
         ⊢ᶜᵗˣ Γ →
         Γ ⟨ n ⟩== T →
         -------------
         Γ ⊢ ♯ n ∶ T

  T·ₛ    : ∀ {Γ σ Δ e T} →
         Γ ⊢ˢᵘᵇ σ ∶ Δ →
         Δ ⊢ e ∶ T →
         ---------------------
         Γ ⊢ e ·ₛ σ ∶ T ·ₛ σ

  TΠ    : ∀ {Γ S T 𝓁} →
         Γ ⊢ S ∶ `(𝑆𝑒𝑡 𝓁) →
         (Γ , S) ⊢ T ∶ `(𝑆𝑒𝑡 𝓁) →
         ------------------------
         Γ ⊢ Π S (ƛ T) ∶ `(𝑆𝑒𝑡 𝓁)

  Tƛ     : ∀ {Γ S T e} →
         Γ ⊢ S →
         (Γ , S) ⊢ e ∶ T →
         ----------------------
         Γ ⊢ ƛ e ∶ Π S (ƛ T)

  T·   : ∀ {Γ T₁ T₂ e₁ e₂} →
         Γ ⊢ e₁ ∶ Π T₁ T₂ →
         Γ ⊢ e₂ ∶ T₁ →
         --------------------
         Γ ⊢ e₁ · e₂ ∶ T₂ · e₂

  T⟨Type⋯⟩ : ∀ {Γ T₁ T₂ 𝓁 𝓀} →
         Γ ⊢ T₁ ∶ `(𝑆𝑒𝑡 𝓁) →
         Γ ⊢ T₂ ∶ `(𝑆𝑒𝑡 𝓀) →
         𝓁 ≤′ 𝓀 →
         ----------------------------------
         Γ ⊢ ⟨Type T₁ ⋯ T₂ ⟩ ∶ `(𝑆𝑒𝑡 (suc 𝓀))

  TType  : ∀ {Γ T} →
         Γ ⊢ T →
         --------------------------
         Γ ⊢ Type T ∶ ⟨Type T ⋯ T ⟩

  T∙Type : ∀ {Γ e T₁ T₂ 𝓁} →
         Γ ⊢ ⟨Type T₁ ⋯ T₂ ⟩ ∶ `(𝑆𝑒𝑡 (suc 𝓁)) →
         Γ ⊢ e ∶ ⟨Type T₁ ⋯ T₂ ⟩ →
         ------------------------------------
         Γ ⊢ ⟨ e ⟩∙Type ∶ `(𝑆𝑒𝑡 𝓁)

  T<∶    : ∀ {Γ e T₁ T₂} →
         Γ ⊢ e ∶ T₁ →
         Γ ⊢ T₁ <∶ T₂ →
         ----------------
         Γ ⊢ e ∶ T₂
```

## Substitution Typing

Explicit substitutions are due to Abadi et al. '90.  Intuitively,
    Γ ⊢ˢᵘᵇ σ ∶ Δ
states that substitution σ is simultaneously substituting
all variables in Δ (!) for terms with free variables in Γ.
In some presentations the judgment is written
    σ ∈ Γ → Δ
which is very confusing, because the notation suggests we are
transforming Γ-terms into Δ-terms, but it is _the other way around_.

```agda
data _⊢ˢᵘᵇ_∶_ where
  TId : ∀ {Γ} →
        ⊢ᶜᵗˣ Γ →
        ------------
        Γ ⊢ˢᵘᵇ Id ∶ Γ

  T↑  : ∀ {Γ T} →
        Γ ⊢ T → -- TODO is this needed?
        ----------------
        (Γ , T) ⊢ˢᵘᵇ ↑ ∶ Γ

  T∘ˢ : ∀ {Γ σ Δ τ Φ} →
        Γ ⊢ˢᵘᵇ τ ∶ Δ →
        Δ ⊢ˢᵘᵇ σ ∶ Φ →
        -----------------
        Γ ⊢ˢᵘᵇ σ ∘ₛ τ ∶ Φ

  T,ˢ : ∀ {Γ σ Δ e T} →
        Γ ⊢ˢᵘᵇ σ ∶ Δ →
        Δ ⊢ T →
        Γ ⊢ e ∶ T ·ₛ σ →
        -----------------------
        Γ ⊢ˢᵘᵇ (σ ,ₛ e) ∶ (Δ , T)
```

## Subtyping

```agda
data _⊢_<∶_ where -- TODO: should subtyping be indexed by universe level?
  <∶Refl : ∀ {Γ T₁ T₂ 𝓁} →
        Γ ⊢ T₁ ≈ T₂ ∶ `(𝑆𝑒𝑡 𝓁) →
        ----------------------
        Γ ⊢ T₁ <∶ T₂

  <∶Lvl : ∀ {Γ 𝓀 𝓁} →
        𝓀 ≤′ 𝓁 →
        --------------------
        Γ ⊢ `(𝑆𝑒𝑡 𝓀) <∶ `(𝑆𝑒𝑡 𝓁)

  <∶Trans : ∀ {Γ T₁ T₂ T₃} →
        Γ ⊢ T₁ <∶ T₂ →
        Γ ⊢ T₂ <∶ T₃ →
        --------------
        Γ ⊢ T₁ <∶ T₃

  <∶⊤ : ∀ {Γ T} →
        Γ ⊢ T →
        ------------- TODO: do we need to fix the universe levels of ⊤ and ⊥, as it might be possible to go down a level?
        Γ ⊢ T <∶ ` ⊤'

  <∶⊥ : ∀ {Γ T} →
        Γ ⊢ T →
        -----------
        Γ ⊢ ` ⊥' <∶ T

  <∶Sel₁ : ∀ {Γ e T} →
        Γ ⊢ e ∶ ⟨Type T ⋯ ` ⊤' ⟩ →
        ---------------------------
        Γ ⊢ T <∶ ⟨ e ⟩∙Type

  <∶Sel₂ : ∀ {Γ e T} →
        Γ ⊢ e ∶ ⟨Type ` ⊥' ⋯ T ⟩ →
        ---------------------------
        Γ ⊢ ⟨ e ⟩∙Type <∶ T

  <∶⟨Type⋯⟩ : ∀ {Γ S₁ T₁ S₂ T₂} → -- TODO this also looks fishy, considering we have different universe levels
        Γ ⊢ S₂ <∶ S₁ →
        Γ ⊢ T₁ <∶ T₂ →
        -------------------------------------
        Γ ⊢ ⟨Type S₁ ⋯ T₁ ⟩ <∶ ⟨Type S₂ ⋯ T₂ ⟩

  <∶Π : ∀ {Γ S₁ T₁ S₂ T₂} →
        Γ ⊢ S₂ <∶ S₁ →
        (Γ , S₂) ⊢ T₁ <∶ T₂ →
        ----------------------------------
        Γ ⊢ Π S₁ (ƛ T₁) <∶ Π S₂ (ƛ T₂)
```

## βη-Equality

```agda
data _⊢_≈_∶_ where
```
### Computation Rules
```agda
  ≈β· : ∀ {Γ S T s t} →
       (Γ , S) ⊢ t ∶ T →
       Γ ⊢ s ∶ S →
       ---------------------------------
       Γ ⊢ (ƛ t) · s ≈ t [ s ] ∶ T [ s ]

  ≈β∙Type : ∀ {Γ T 𝓁} →
       Γ ⊢ T ∶ `(𝑆𝑒𝑡 𝓁) →
       --------------------------------
       Γ ⊢ ⟨ Type T ⟩∙Type ≈ T ∶ `(𝑆𝑒𝑡 𝓁)
```
### Extensionality Rules
```agda
  ≈ξƛ : ∀ {Γ S T e e'} →
       (Γ , S) ⊢ e ≈ e' ∶ T →
       --------------------------
       Γ ⊢ ƛ e ≈ ƛ e' ∶ Π S (ƛ T)

  ≈ηƛ : ∀ {Γ e S T} →
       Γ ⊢ e ∶ Π S (ƛ T) →
       ---------------------------------------
       Γ ⊢ e ≈ ƛ ((e ·ₛ ↑) · (♯ 0)) ∶ Π S (ƛ T)

  ≈η∙Type : ∀ {Γ e T₁ T₂} →
       Γ ⊢ e ∶ ⟨Type T₁ ⋯ T₂ ⟩ →
       ----------------------------------------
       Γ ⊢ e ≈ Type ⟨ e ⟩∙Type ∶ ⟨Type T₁ ⋯ T₂ ⟩ -- TODO: need to investigate if this is reasonable/unproblematic
```
###  Compatibility/Congruence Rules
```agda
  ≈♯ : ∀ {Γ i T} →
       ⊢ᶜᵗˣ Γ →
       Γ ⟨ i ⟩== T →
       ----------------
       Γ ⊢ ♯ i ≈ ♯ i ∶ T

  ≈ᶜ : ∀ {Γ c T} →
       c ⊢ᶜ T → -- TODO demand well-formed Γ?
       -----------------
       Γ ⊢ ` c ≈ ` c ∶ T

  -- these rules, among others, are included in the rule for constants above!
  -- ≈𝑁 : ∀ {Γ 𝓁} →
  --      ------------------------
  --      Γ ⊢ ` 𝑁 ≈ ` 𝑁 ∶ `(𝑆𝑒𝑡 𝓁)

  -- ≈𝑆𝑒𝑡 : ∀ {Γ 𝓁 𝓀} →
  --      𝓁 < 𝓀 →
  --      -------------------------------
  --      Γ ⊢ `(𝑆𝑒𝑡 𝓁) ≈ `(𝑆𝑒𝑡 𝓁) ∶ `(𝑆𝑒𝑡 𝓀)
  --
  -- Furthermore, congruence for successor 𝑠 is a special case of application congruence ≈· below,
  -- relying on ≈ᶜ on the function position.

  ≈∶[ℒ≤] : ∀ {Γ T T' 𝓁 𝓀} →
       𝓁 ≤′ 𝓀 →
       Γ ⊢ T ≈ T' ∶ `(𝑆𝑒𝑡 𝓁) →
       -----------------------
       Γ ⊢ T ≈ T' ∶ `(𝑆𝑒𝑡 𝓀)

  ≈∶[≈] : ∀ {Γ e e' T T' 𝓁} →
       Γ ⊢ e ≈ e' ∶ T →
       Γ ⊢ T ≈ T' ∶ `(𝑆𝑒𝑡 𝓁) →
       -----------------------
       Γ ⊢ e ≈ e' ∶ T'

  ≈[Π] : ∀ {Γ S S' T T' 𝓁} →
       Γ ⊢ S ≈ S' ∶ `(𝑆𝑒𝑡 𝓁) →
       (Γ , S) ⊢ T ≈ T' ∶ `(𝑆𝑒𝑡 𝓁) →
       -------------------------------------
       Γ ⊢ Π S (ƛ T) ≈ Π S' (ƛ T') ∶ `(𝑆𝑒𝑡 𝓁)

  ≈[·] : ∀ {Γ s s' t t' S T} →
       Γ ⊢ s ≈ s' ∶ Π S (ƛ T) →
       Γ ⊢ t ≈ t' ∶ S →
       -----------------------------
       Γ ⊢ s · t ≈ s' · t' ∶ T [ s ]

  ≈[ˢᵘᵇ] : ∀ {Γ Δ e e' T σ σ'} →
       Γ ⊢ˢᵘᵇ σ ≈ σ' ∶ Δ →
       Δ ⊢ e ≈ e' ∶ T →
       -----------------------------
       Γ ⊢ e ·ₛ σ ≈ e' ·ₛ σ' ∶ T ·ₛ σ

  ≈[⟨Type⋯⟩] : ∀ {Γ S S' T T' 𝓁} →
       Γ ⊢ S ≈ S' ∶ `(𝑆𝑒𝑡 𝓁) →
       Γ ⊢ T ≈ T' ∶ `(𝑆𝑒𝑡 𝓁) →
       ----------------------------------------------------
       Γ ⊢ ⟨Type S ⋯ T ⟩ ≈ ⟨Type S' ⋯ T' ⟩ ∶ `(𝑆𝑒𝑡 (suc 𝓁))

  ≈[Type] : ∀ {Γ T T' 𝓁} →
       Γ ⊢ T ≈ T' ∶ `(𝑆𝑒𝑡 𝓁) →
       ----------------------------------------
       Γ ⊢ (Type T) ≈ (Type T') ∶ ⟨Type T ⋯ T ⟩

  ≈[∙Type] : ∀ {Γ e e' S T 𝓁} →
       Γ ⊢ ⟨Type S ⋯ T ⟩ ∶ `(𝑆𝑒𝑡 (suc 𝓁)) →
       Γ ⊢ e ≈ e' ∶ ⟨Type S ⋯ T ⟩ →
       ---------------------------------------------
       Γ ⊢ ⟨ e ⟩∙Type ≈ ⟨ e' ⟩∙Type ∶ `(𝑆𝑒𝑡 𝓁)
```
### Substitution Resolution Rules
```agda
  ≈ˢᵘᵇ↑ : ∀ {Γ i S T} →
       Γ ⟨ i ⟩== T →
       -----------------------------------
       (Γ , S) ⊢ (♯ i) ·ₛ ↑ ≈ ♯ (suc i) ∶ T

  ≈ˢᵘᵇId : ∀ {Γ e T} →
       Γ ⊢ e ∶ T →
       -------------------
       Γ ⊢ e ·ₛ Id ≈ e ∶ T

  ≈ˢᵘᵇ,ₛ-0 : ∀ {Γ Δ σ e T} →
       Γ ⊢ˢᵘᵇ (σ ,ₛ e) ∶ (Δ , T) →
       -------------------------------
       Γ ⊢ ♯ 0 ·ₛ (σ ,ₛ e) ≈ e ∶ T ·ₛ σ

  ≈ˢᵘᵇ,ₛ-suc : ∀ {Γ Δ σ i e S T} →
       Γ ⊢ˢᵘᵇ (σ ,ₛ e) ∶ (Δ , T) →
       Δ ⟨ i ⟩== S →
       -------------------------------------------
       Γ ⊢ ♯ (suc i) ·ₛ (σ ,ₛ e) ≈ ♯ i ·ₛ σ ∶ S ·ₛ σ -- TODO not sure about the action on S
```
### Substitution Propagation Rules
```agda
  ≈ˢᵘᵇ∘ₛ : ∀ {Γ Δ Φ σ τ e T} → --TODO isn't this a consequence of congruence and subst equality?
       Γ ⊢ˢᵘᵇ τ ∶ Δ →
       Δ ⊢ˢᵘᵇ σ ∶ Φ →
       Φ ⊢ e ∶ T →
       ---------------------------------------------
       Γ ⊢ e ·ₛ (σ ∘ₛ τ) ≈ (e ·ₛ σ) ·ₛ τ ∶ T ·ₛ (σ ∘ₛ τ)

  ≈ˢᵘᵇᶜ : ∀ {Γ Δ c T σ} →
       Γ ⊢ˢᵘᵇ σ ∶ Δ →
       c ⊢ᶜ T →
       ----------------------
       Γ ⊢ ` c ·ₛ σ ≈ ` c ∶ T

  ≈ˢᵘᵇΠ : ∀ {Γ Δ σ S T 𝓁} →
       Γ ⊢ˢᵘᵇ σ ∶ Δ →
       Δ ⊢ S ∶ `(𝑆𝑒𝑡 𝓁) →
       (Δ , S) ⊢ T ∶ `(𝑆𝑒𝑡 𝓁) →
       -------------------------------------------------------------------
       Γ ⊢ (Π S (ƛ T)) ·ₛ σ ≈ Π (S ·ₛ σ) (ƛ (T ·ₛ (σ ∘ₛ ↑ ,ₛ ♯ 0))) ∶ `(𝑆𝑒𝑡 𝓁)
       -- it is important that we go under the ƛ and lift+extend σ right away here

  ≈ˢᵘᵇƛ : ∀ {Γ Δ e S T σ} →
       Γ ⊢ˢᵘᵇ σ ∶ Δ →
       (Δ , S) ⊢ e ∶ T →
       ---------------------------------------------------------
       Γ ⊢ (ƛ e) ·ₛ σ ≈ ƛ (e ·ₛ (σ ∘ₛ ↑ ,ₛ ♯ 0)) ∶ (Π S (ƛ T)) ·ₛ σ

  ≈ˢᵘᵇ· : ∀ {Γ Δ σ S T e₁ e₂} →
       Γ ⊢ˢᵘᵇ σ ∶ Δ →
       Δ ⊢ e₁ ∶ Π S (ƛ T) →
       Δ ⊢ e₂ ∶ S →
       ----------------------------------------------------------------
       Γ ⊢ (e₁ · e₂) ·ₛ σ ≈ (e₁ ·ₛ σ) · (e₂ ·ₛ σ) ∶ T ·ₛ (σ ∘ₛ ↑ ,ₛ e₂ ·ₛ σ)

  ≈ˢᵘᵇ⟨Type⋯⟩ : ∀ {Γ Δ σ S T 𝓀 𝓁} →
       Γ ⊢ˢᵘᵇ σ ∶ Δ →
       Δ ⊢ S ∶ `(𝑆𝑒𝑡 𝓁) →
       Δ ⊢ T ∶ `(𝑆𝑒𝑡 𝓀) →
       𝓁 ≤′ 𝓀 →
       -------------------------------------------------------------------
       Γ ⊢ ⟨Type S ⋯ T ⟩ ·ₛ σ ≈ ⟨Type (S ·ₛ σ) ⋯ (T ·ₛ σ) ⟩ ∶ `(𝑆𝑒𝑡 (suc 𝓀))

  ≈ˢᵘᵇType : ∀ {Γ Δ σ T} →
       Γ ⊢ˢᵘᵇ σ ∶ Δ →
       Δ ⊢ T →
       -----------------------------------------------------
       Γ ⊢ (Type T) ·ₛ σ ≈ Type (T ·ₛ σ) ∶ ⟨Type T ⋯ T ⟩ ·ₛ σ

  ≈ˢᵘᵇ∙Type : ∀ {Γ Δ σ e S T 𝓁} →
       Γ ⊢ˢᵘᵇ σ ∶ Δ →
       Δ ⊢ ⟨Type S ⋯ T ⟩ ∶ `(𝑆𝑒𝑡 (suc 𝓁)) →
       Δ ⊢ e ∶ ⟨Type S ⋯ T ⟩ →
       ---------------------------------------------
       Γ ⊢ ⟨ e ⟩∙Type ·ₛ σ ≈ ⟨ e ·ₛ σ ⟩∙Type ∶ `(𝑆𝑒𝑡 𝓁)
```
### Equivalence Rules
```agda
  ≈refl : ∀ {Γ e T} →
       Γ ⊢ e ∶ T →
       --------------
       Γ ⊢ e ≈ e ∶ T

  ≈sym : ∀ {Γ e₁ e₂ T} →
       Γ ⊢ e₁ ≈ e₂ ∶ T →
       -----------------
       Γ ⊢ e₂ ≈ e₁ ∶ T

  ≈trans : ∀ {Γ e₁ e₂ e₃ T} →
       Γ ⊢ e₁ ≈ e₂ ∶ T →
       Γ ⊢ e₂ ≈ e₃ ∶ T →
       ----------------
       Γ ⊢ e₁ ≈ e₂ ∶ T
```
## Substitution Equality
```agda
data _⊢ˢᵘᵇ_≈_∶_ where
```
### Equivalence Rules
```agda
  sub≈refl : ∀ {Γ Δ σ} →
       Γ ⊢ˢᵘᵇ σ ∶ Δ →
       ---------------
       Γ ⊢ˢᵘᵇ σ ≈ σ ∶ Δ

  sub≈sym : ∀ {Γ Δ σ τ} →
       Γ ⊢ˢᵘᵇ σ ≈ τ ∶ Δ →
       ---------------
       Γ ⊢ˢᵘᵇ τ ≈ σ ∶ Δ

  sub≈trans : ∀ {Γ Δ Φ σ₁ σ₂ σ₃} →
       Γ ⊢ˢᵘᵇ σ₁ ≈ σ₂ ∶ Δ →
       Δ ⊢ˢᵘᵇ σ₂ ≈ σ₃ ∶ Φ →
       -------------------
       Γ ⊢ˢᵘᵇ σ₁ ≈ σ₃ ∶ Φ
```
### Computation and Category Laws
```agda
  sub≈↑ : ∀ {Γ Δ σ e T} →
       Γ ⊢ˢᵘᵇ σ ∶ Δ →
       Δ ⊢ T →
       Γ ⊢ e ∶ T ·ₛ σ →
       -------------------------
       Γ ⊢ˢᵘᵇ ↑ ∘ₛ (σ ,ₛ e) ≈ σ ∶ Δ

  sub≈Idₗ : ∀ {Γ Δ σ} →
       Γ ⊢ˢᵘᵇ σ ∶ Δ →
       --------------------
       Γ ⊢ˢᵘᵇ Id ∘ₛ σ ≈ σ ∶ Δ

  sub≈Idᵣ : ∀ {Γ Δ σ} →
       Γ ⊢ˢᵘᵇ σ ∶ Δ →
       --------------------
       Γ ⊢ˢᵘᵇ σ ∘ₛ Id ≈ σ ∶ Δ

  sub≈∘ₛassoc : ∀ {Γ Δ Φ Ψ δ φ ψ} →
       Φ ⊢ˢᵘᵇ δ ∶ Δ →
       Ψ ⊢ˢᵘᵇ φ ∶ Φ →
       Γ ⊢ˢᵘᵇ ψ ∶ Ψ →
       ------------------------------------
       Γ ⊢ˢᵘᵇ (δ ∘ₛ φ) ∘ₛ ψ ≈ δ ∘ₛ (φ ∘ₛ ψ) ∶ Δ
```
### Extensionality
```agda
  sub≈η : ∀ {Γ T} →
       ⊢ᶜᵗˣ (Γ , T) →
       ----------------------------------
       (Γ , T) ⊢ˢᵘᵇ Id ≈ ↑ ,ₛ ♯ 0 ∶ (Γ , T)
```
### Propagation
```agda
  sub≈β : ∀ {Γ Δ Φ σ τ e T} →
       Γ ⊢ˢᵘᵇ τ ∶ Φ →
       Φ ⊢ˢᵘᵇ σ ∶ Δ →
       Φ ⊢ e ∶ T ·ₛ σ →
       ----------------------------------------------
       Γ ⊢ˢᵘᵇ (σ ,ₛ e) ∘ₛ τ ≈ (σ ∘ₛ τ ,ₛ e ·ₛ τ) ∶ (Δ , T)
```
### Compatibility/Congruence
```agda
  sub≈[,ₛ] : ∀ {Γ σ σ' Δ e e' T} →
       Γ ⊢ˢᵘᵇ σ ≈ σ' ∶ Δ →
       Δ ⊢ T →
       Γ ⊢ e ≈ e' ∶ T ·ₛ σ →
       ------------------------------------
       Γ ⊢ˢᵘᵇ (σ ,ₛ e) ≈ (σ' ,ₛ e') ∶ (Δ , T)

  sub≈[∘ˢ] : ∀ {Γ σ σ' Δ τ τ' Φ} →
        Γ ⊢ˢᵘᵇ τ ≈ τ' ∶ Δ →
        Δ ⊢ˢᵘᵇ σ ≈ σ' ∶ Φ →
        -------------------------
        Γ ⊢ˢᵘᵇ σ ∘ₛ τ ≈ σ' ∘ₛ τ' ∶ Φ

```
