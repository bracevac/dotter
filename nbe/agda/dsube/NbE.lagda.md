# Normalization by Evaluation for Dᵉ<:>

```agda
{-# OPTIONS --allow-unsolved-metas #-} -- TODO remove later
module dsube.NbE where

open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax; _,_)
open import Function using (_∘_; id)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _≤_; _<_; _⊔_; _∸_)

open import dsube.Syntax using (ℒ; Cst; Exp; Subst; Ctx; ctx-length; Nf; Ne)
open Cst
```

A normalizer is essentially a big-step interpreter giving type and
term expressions a denotation into a values domain, along with a
read-back/quotation function that maps values back to syntactic normal
forms. The interpreter is enriched with the notion of neutral values
and evaluation of expressions with free variables, along with
type-directed reification/reflection.  Here, free variables are
considered "unkowns", a bit reminiscent of symbolic execution, instead
of "placeholders" (cf. Abel'13). Of course, for a dependently-typed
object language, there are additionally type values.

# Domains

Instead of fancy domain theory along with the associated baggage, we
can rely on "partial applicative structures" (Abel'13), a kind of
defunctionalized values domain with function spaces, giving a
down-to-earth view on domains.

```agda
data 𝕍   : Set -- values
data 𝕍ᴺᵉ : Set  -- neutral values
Env = ℕ → 𝕍 -- we'll try Abel's style of envs, soundness guarantees that only the right indices are looked up

-- as in the syntax, we group the constant values into a subdomain
data 𝕍𝕔 : Set where
  V𝑁  : 𝕍𝕔
  V𝑆𝑒𝑡 : ℒ → 𝕍𝕔
  V⊥  : 𝕍𝕔
  V⊤  : 𝕍𝕔
  V𝑛  : ℕ → 𝕍𝕔
  V𝑠  : 𝕍𝕔
```

The main benefit of a partial applicative structure is that λ-abstractions have a closure-based
representation in the semantics.

```agda
data 𝕍 where
  Vƛ        : Exp → Env → 𝕍
  ᶜ_        : 𝕍𝕔  → 𝕍
  VΠ        : 𝕍   → 𝕍   → 𝕍
  ⟪Type_⋯_⟫ : 𝕍 → 𝕍 → 𝕍
  VType     : 𝕍   → 𝕍 -- TODO in previous works, we took type closures, do we need them for NbE?
  ↑⟨_⟩      : 𝕍{-type-} → 𝕍ᴺᵉ → 𝕍  -- reflect neutral term at a given type

data 𝕍ᴺᶠ : Set where
  ↓⟨_⟩ : 𝕍{-type-} → 𝕍 → 𝕍ᴺᶠ -- reify a semantic value at a given type

-- neutral values
data 𝕍ᴺᵉ where
  $_        : ℕ  → 𝕍ᴺᵉ       -- deBruijn *level*
  _·ⱽᴺᵉ_     : 𝕍ᴺᵉ → 𝕍ᴺᶠ → 𝕍ᴺᵉ
  ⟪_⟫∙Typeⱽᴺᵉ : 𝕍ᴺᵉ → 𝕍ᴺᵉ
  𝑠·ⱽᴺᵉ_      : 𝕍ᴺᵉ → 𝕍ᴺᵉ

data 𝔹 : 𝕍 → Set where -- classifies the base types
  B𝑁 : 𝔹 (ᶜ V𝑁)
  B⊥ : 𝔹 (ᶜ V⊥)
  B⊤ : 𝔹 (ᶜ V⊤)
  BSet : ∀{𝓁} → 𝔹 (ᶜ (V𝑆𝑒𝑡 𝓁))
  B↑ : ∀{𝓁 E} → 𝔹 (↑⟨ ᶜ (V𝑆𝑒𝑡 𝓁) ⟩ E)

```
## Environments

For simplicity, environments are total functions from natural numbers
(deBruijn *index*) to values.  We are only ever interested in a finite
prefix up to the n variables in the typing context.

```agda
-- the "empty" env
ε : Env
ε n = ᶜ V⊥ -- something arbitrary

-- env extension
_,,_ : Env → 𝕍 → Env
_,,_ ρ v 0 = v
_,,_ ρ v (suc i) = ρ i

infixl 7 _,,_

-- test
_ : (ε ,, (ᶜ (V𝑛 0))) 0 ≡ (ᶜ (V𝑛 0))
_ = refl

-- derived syntax for non-dependent function type values (compare w. _⇒_ in Syntax.lagda.md)
-- for some reason, Agda will not accept a pattern definition, so we make it a function
_⟶_ :  𝕍 → 𝕍 → 𝕍
_⟶_ S T = (VΠ S (Vƛ (Exp.♯ 1) (ε ,, T)))
infixr 7 _⟶_
```

# Evaluation

We have a "partial applicative structure" because we are considering
function application on the domain 𝕍 of values. It is necessarily a
partial operation, since it makes only sense for function values,
resp. neutral expressions at function type.

Again, sticking to the script laid out by Abel'13, we model partial
functions as relations. The metatheory will establish that these
can be cast into total functions.

The partiality of semantic function application induces partiality
practically everywhere else, necessitating relational definitions
throughout, e.g., in the evaluator/normalizer.

The general recipe for elimination forms, such as application or
abstract type selection, is defining a semantic counterpart of the
operation in the evaluator, which next to the "normal" behavior
(reduction is possible) also handles the case when the eliminatee is
stuck on a neutral term.

We shall modularize the evaluation of eliminators into separate
partial function definitions, which will be "called" by the main
evaluator.  It has the following signature, which we declare up front,
since subsequent definitions depend on it.

```agda
data ⟦_⟧_⇓_ : Exp → Env → 𝕍 → Set
```
## Semantic Application
```agda
data _·_⇓_ : 𝕍 → 𝕍 → 𝕍 → Set where
  -- standard function application w. closures
  app-ƛ : ∀ {e ρ v₁ v₂} →
       ⟦ e ⟧ (ρ ,, v₁) ⇓ v₂ →
       --------------------
       (Vƛ e ρ) · v₁ ⇓ v₂

  -- application of a neutral term at function type
  app-ne : ∀{𝑆 𝑇 𝑇·s nv s} →
       𝑇 · s ⇓ 𝑇·s →
       -----------------------------------------------
       (↑⟨ VΠ 𝑆 𝑇 ⟩ nv) · s ⇓ ↑⟨ 𝑇·s ⟩ (nv ·ⱽᴺᵉ (↓⟨ 𝑆 ⟩ s))

  -- application of primitives/constructors
  app-suc : ∀{n} →
       ------------------------------------
       (ᶜ V𝑠) · (ᶜ (V𝑛 n)) ⇓ (ᶜ (V𝑛 (suc n)))

  app-suc-ne : ∀{nv} →
       ---------------------------------------------
       (ᶜ V𝑠) · (↑⟨ ᶜ V𝑁 ⟩ nv ) ⇓ (↑⟨ ᶜ V𝑁 ⟩ (𝑠·ⱽᴺᵉ nv))
```
## Semantic Abstract Type Selection

This is preliminary.

```agda
data ⟪_⟫∙Type⇓_ : 𝕍 → 𝕍 → Set where
  -- standard abstract type selection
  sel-Type : ∀{𝑇} →
     ⟪ VType 𝑇 ⟫∙Type⇓ 𝑇
  -- selection on a neutral term
  sel-ne : ∀{𝓁 𝑆 𝑇 nv} →
     -- TODO : to make this a deterministic function, we need to carry the 𝓁 in the abstract type
     ⟪ (↑⟨ ⟪Type 𝑆 ⋯ 𝑇 ⟫ ⟩ nv) ⟫∙Type⇓ ↑⟨ ᶜ (V𝑆𝑒𝑡 𝓁) ⟩ ⟪ nv ⟫∙Typeⱽᴺᵉ
```
## Substitution Evaluation

Explicit substitutions operationally are environment transformers.
Perhaps confusingly, the direction in which environments are
transformed by the substitution operations is opposite to the reading
of the typing rules (and it also explains why Abel chooses to write
the substitution typing judgment in the order he does, emphasizing the
operational view).

```agda
open Subst renaming (↑ to ↑ˢ)
data ⟦_⟧ˢ_⇓_ : Subst → Env → Env → Set where
  eval-Id : ∀{ρ} →
      ------------
      ⟦ Id ⟧ˢ ρ ⇓ ρ

  eval-↑ : ∀{ρ v} →
      -------------------
      ⟦ ↑ˢ ⟧ˢ (ρ ,, v) ⇓ ρ -- TODO this might require an explicit operation on Env

  eval-,ₛ : ∀{σ ρ ρ' e v} →
      ⟦ σ ⟧ˢ ρ ⇓ ρ' →
      ⟦ e ⟧ ρ ⇓ v →
      -----------------------
      ⟦ σ ,ₛ e ⟧ˢ ρ ⇓ (ρ' ,, v)

  eval-∘ₛ : ∀{σ τ ρ ρ' ρ''} →
      ⟦ τ ⟧ˢ ρ ⇓ ρ' →
      ⟦ σ ⟧ˢ ρ' ⇓ ρ'' →
      -----------------------
      ⟦ σ ∘ₛ τ ⟧ˢ ρ ⇓ ρ''
```
## Constant Evaluation
```agda
open Exp
⟦_⟧ᶜ : Cst → 𝕍𝕔
⟦ 𝑁 ⟧ᶜ     = V𝑁
⟦ 𝑧 ⟧ᶜ     = (V𝑛 0)
⟦ 𝑠 ⟧ᶜ     = V𝑠
⟦ 𝑆𝑒𝑡 𝓁 ⟧ᶜ =  (V𝑆𝑒𝑡 𝓁)
⟦ ⊤' ⟧ᶜ    = V⊤
⟦ ⊥' ⟧ᶜ    = V⊥
```
## Expression Evaluation
```agda
data ⟦_⟧_⇓_ where
  eval-var : ∀{n ρ} →
      ----------------
      ⟦ ♯ n ⟧ ρ ⇓ (ρ n)

  eval-c : ∀{c ρ} →
      -----------------
      ⟦ ` c ⟧ ρ ⇓ (ᶜ ⟦ c ⟧ᶜ)

  eval-Π : ∀{S T ρ 𝑆 𝑇} →
      ⟦ S ⟧ ρ ⇓ 𝑆 →
      ⟦ T ⟧ ρ ⇓ 𝑇 → -- if the Π type is well-typed, then T will be of the form ƛ T', and 𝑇 will be a closure
      ------------------------
      ⟦ Π S T ⟧ ρ ⇓ (VΠ 𝑆 𝑇)

  eval-ƛ : ∀{e ρ} →
      -------------------
      ⟦ ƛ e ⟧ ρ ⇓ (Vƛ e ρ)

  eval-· : ∀{e₁ e₂ ρ v₁ v₂ v₁·v₂} →
      ⟦ e₁ ⟧ ρ ⇓ v₁ →
      ⟦ e₂ ⟧ ρ ⇓ v₂ →
      v₁ · v₂ ⇓ v₁·v₂ →
      ---------------------
      ⟦ e₁ · e₂ ⟧ ρ ⇓ v₁·v₂

  eval-⟨Type⋯⟩ : ∀{S T ρ 𝑆 𝑇} →
      ⟦ S ⟧ ρ ⇓ 𝑆 →
      ⟦ T ⟧ ρ ⇓ 𝑇 →
      ---------------------------------
      ⟦ ⟨Type S ⋯ T ⟩ ⟧ ρ ⇓ ⟪Type 𝑆 ⋯ 𝑇 ⟫

  eval-Type : ∀{T ρ 𝑇} →
      ⟦ T ⟧ ρ ⇓ 𝑇 →
      -----------------------
      ⟦ Type T ⟧ ρ ⇓ VType 𝑇

  eval-∙Type : ∀{e ρ v ⟪v⟫∙Type } →
      ⟦ e ⟧ ρ ⇓ v →
      ⟪ v ⟫∙Type⇓ ⟪v⟫∙Type →
      --------------------------
      ⟦ ⟨ e ⟩∙Type ⟧ ρ ⇓ ⟪v⟫∙Type

  eval-·ₛ : ∀{e σ ρ ρ' v} →
      ⟦ σ ⟧ˢ ρ ⇓ ρ' →
      ⟦ e ⟧ ρ' ⇓ v →
      ---------------
      ⟦ e ·ₛ σ ⟧ ρ ⇓ v
```
## Read-back/Quotation

These partial functions turn semantic values into syntactic normal forms.
To convert from deBruijn levels to indices, they are parameterized over the number of
variable bindings in the environment.

Since we are interested in computing expressions which are in normal form,
the return types of the read-back functions are proper _subsets_ of the Exp type, i.e.,
the normal forms
    Σ[ e ∈ Exp ](Nf e)
and neutral terms
    Σ[ e ∈ Exp ](Ne e)
using the Nf and Ne predicates as defined in the Syntax module.

```agda
open Nf
open Ne
data ℜᴺᶠ⟨_⟩_⇓_ : ℕ{- #vars -} → 𝕍ᴺᶠ → Σ[ e ∈ Exp ](Nf e) → Set
data ℜᴺᵉ⟨_⟩_⇓_ : ℕ{- #vars -} → 𝕍ᴺᵉ → Σ[ e ∈ Exp ](Ne e) → Set
```
### Read-back of constants
```agda
data ℜᴺᶠᶜ⟨_⟩_⇓_ : 𝕍{- type -} → 𝕍𝕔 → Σ[ e ∈ Exp ](Nf e) → Set where
  ℜᴺᶠᶜ-𝑁   : ∀{𝓁} →
             ---------------------------------------
             ℜᴺᶠᶜ⟨ ᶜ (V𝑆𝑒𝑡 𝓁) ⟩ V𝑁 ⇓ (` 𝑁 , Nf-cst 𝑁 )

  ℜᴺᶠᶜ-𝑆𝑒𝑡 : ∀{𝓁 𝓀} →
             ------------------------------------------------------
             ℜᴺᶠᶜ⟨ ᶜ (V𝑆𝑒𝑡 𝓀) ⟩ (V𝑆𝑒𝑡 𝓁) ⇓ (` (𝑆𝑒𝑡 𝓁) , Nf-cst (𝑆𝑒𝑡 𝓁)) --TODO is a check for 𝓁 < 𝓀 necessary?

  ℜᴺᶠᶜ-⊥   : ∀{𝓁} →
             -----------------------------------------
             ℜᴺᶠᶜ⟨ ᶜ (V𝑆𝑒𝑡 𝓁) ⟩ V⊥ ⇓ (` ⊥' , Nf-cst ⊥' )

  ℜᴺᶠᶜ-⊤   : ∀{𝓁} →
             -----------------------------------------
             ℜᴺᶠᶜ⟨ ᶜ (V𝑆𝑒𝑡 𝓁) ⟩ V⊤ ⇓ (` ⊤' , Nf-cst ⊤' )

  ℜᴺᶠᶜ-𝑛-𝑧 :  -------------------------------------
             ℜᴺᶠᶜ⟨ ᶜ V𝑁 ⟩ (V𝑛 0) ⇓ (` 𝑧 , Nf-cst 𝑧 )

  ℜᴺᶠᶜ-𝑛-𝑠 : ∀{n eₙ Nf-eₙ} →
             ℜᴺᶠᶜ⟨ ᶜ V𝑁 ⟩ (V𝑛 n) ⇓ (eₙ , Nf-eₙ ) →
             ----------------------------------------------------
             ℜᴺᶠᶜ⟨ ᶜ V𝑁 ⟩ (V𝑛 (suc n)) ⇓ ((` 𝑠) · eₙ , Nf-𝑠· Nf-eₙ )
```
### Readback of Type & Term Values into Normal Forms
```agda
data ℜᴺᶠ⟨_⟩_⇓_ where
  ℜᴺᶠ-c : ∀{n vc nfc 𝑇} →
          ℜᴺᶠᶜ⟨ 𝑇 ⟩ vc ⇓ nfc →
          ----------------------------
          ℜᴺᶠ⟨ n ⟩ (↓⟨ 𝑇 ⟩ (ᶜ vc)) ⇓ nfc
```
The function case shows why it is more comfy to rely on deBruijn levels in the semantics.
It becomes easy to pick the "fresh" variable for normalizing the function.
In contrast, deBruijn indices would require shifting the other variables.
```agda
  ℜᴺᶠ-ƛ : ∀{n 𝑇 𝑆 f e 𝑇·xₙ₊₁ f·xₙ₊₁ Nf-e } →
          let
            xₙ₊₁ : 𝕍
            xₙ₊₁ = ↑⟨ 𝑆 ⟩ ($(suc n))
          in 𝑇 · xₙ₊₁ ⇓ 𝑇·xₙ₊₁ →
             f · xₙ₊₁ ⇓ f·xₙ₊₁ →
             ℜᴺᶠ⟨ suc n ⟩ (↓⟨ 𝑇·xₙ₊₁ ⟩ f·xₙ₊₁) ⇓ (e , Nf-e) →
             ---------------------------------------------
             ℜᴺᶠ⟨ n ⟩ (↓⟨ VΠ 𝑆 𝑇 ⟩ f) ⇓ (ƛ e , Nf-ƛ Nf-e)

  ℜᴺᶠ-Π : ∀{𝓁 n 𝑆 S 𝑇 T Nf-S Nf-T} →
          ℜᴺᶠ⟨ n ⟩ (↓⟨ ᶜ (V𝑆𝑒𝑡 𝓁) ⟩ 𝑆) ⇓ (S , Nf-S) →
          ℜᴺᶠ⟨ n ⟩ (↓⟨ 𝑆 ⟶ ᶜ (V𝑆𝑒𝑡 𝓁) ⟩ 𝑇) ⇓ (T , Nf-T) →
          ----------------------------------------------------------
          ℜᴺᶠ⟨ n ⟩ (↓⟨ ᶜ V𝑆𝑒𝑡 𝓁 ⟩ (VΠ 𝑆 𝑇)) ⇓ (Π S T , Nf-Π Nf-S Nf-T)

  ℜᴺᶠ-⟪Type⋯⟫ : ∀{𝓁 n 𝑆 S 𝑇 T Nf-S Nf-T} →
          ℜᴺᶠ⟨ n ⟩ (↓⟨ ᶜ (V𝑆𝑒𝑡 𝓁) ⟩ 𝑆) ⇓ (S , Nf-S) →
          ℜᴺᶠ⟨ n ⟩ (↓⟨ ᶜ (V𝑆𝑒𝑡 𝓁) ⟩ 𝑇) ⇓ (T , Nf-T) →
          -----------------------------------------------------------------------------------
          ℜᴺᶠ⟨ n ⟩ (↓⟨ ᶜ V𝑆𝑒𝑡 (suc 𝓁) ⟩ ⟪Type 𝑆 ⋯ 𝑇 ⟫) ⇓ (⟨Type S ⋯ T ⟩ , Nf-⟨Type⋯⟩ Nf-S Nf-T)

  ℜᴺᶠ-Type : ∀{𝓁 n 𝑇 T Nf-T} →
          ℜᴺᶠ⟨ n ⟩ (↓⟨ ᶜ (V𝑆𝑒𝑡 𝓁) ⟩ 𝑇) ⇓ (T , Nf-T) → --TODO similar problems here, the 𝓁 might not be uniquely det. by the input
          ---------------------------------------------------------------
          ℜᴺᶠ⟨ n ⟩ (↓⟨ ⟪Type 𝑇 ⋯ 𝑇 ⟫ ⟩ (VType 𝑇)) ⇓ (Type T , Nf-Type Nf-T)

  ℜᴺᶠ-↑⟨-⟩ : ∀{n nv e Ne-e 𝐵 𝐵'} →
          𝔹 𝐵 → 𝔹 𝐵' →
          ℜᴺᵉ⟨ n ⟩ nv ⇓ (e , Ne-e) →
          ------------------------------------------------
          ℜᴺᶠ⟨ n ⟩ (↓⟨ 𝐵 ⟩ (↑⟨ 𝐵' ⟩ nv)) ⇓ (e , Nf-ne Ne-e) -- Abel argues that 𝐵 and 𝐵' do not need to be equal in this definition
```
### Readback of Neutral Values into Neutral Terms
```agda
data ℜᴺᵉ⟨_⟩_⇓_ where
  ℜᴺᵉ-var : ∀{i n} →
          -----------------------------------------
          ℜᴺᵉ⟨ n ⟩ ($ i) ⇓ (♯ (n ∸ (suc i)), Ne-Var) -- convert deBruijn level to index

  ℜᴺᵉ-· : ∀{n nv ne v e Ne-ne Nf-e} →
          ℜᴺᵉ⟨ n ⟩ nv ⇓ (ne , Ne-ne) →
          ℜᴺᶠ⟨ n ⟩ v  ⇓ (e , Nf-e) →
          -----------------------------------------------
          ℜᴺᵉ⟨ n ⟩ (nv ·ⱽᴺᵉ v) ⇓ (ne · e , Ne-· Ne-ne Nf-e)

  ℜᴺᵉ-𝑠· : ∀{n nv ne Ne-ne} →
          ℜᴺᵉ⟨ n ⟩ nv ⇓ (ne , Ne-ne) →
          -----------------------------------------------
          ℜᴺᵉ⟨ n ⟩ (𝑠·ⱽᴺᵉ nv) ⇓ ((` 𝑠) · ne , Ne-𝑠· Ne-ne)

  ℜᴺᵉ-∙Type : ∀{n nv ne Ne-ne } →
          ℜᴺᵉ⟨ n ⟩ nv ⇓ (ne , Ne-ne) →
          -----------------------------------------------------
          ℜᴺᵉ⟨ n ⟩ ⟪ nv ⟫∙Typeⱽᴺᵉ ⇓ ( ⟨ ne ⟩∙Type , Ne-∙Type Ne-ne)


```
# Normalization by Evaluation

## Initial Environment, deBruijn Indices vs. Levels

There will be an initial environment, ρₙ , that binds the free
deBruijn indices of an expression to the corresponding neutral
deBruijn levels reflected into the values domain, e.g., ρₙ(vᵢ) = ↑⟨A⟩
xⱼ, where j = n ∸ (i+1), and ∸ is subtraction on ℕ. The type value A
will be determined by the corresponding assumption in typing
environment Γ.  Hence, the initial environment depends on the
(partial!) evaluation function ⟦_⟧.

The following partial function transforms typing contexts into the
corresponding initial environment, where each deBruijn index becomes a
reflected neutral deBruijn level variable.

```agda
open Ctx renaming (_,_ to _,ᶜ_)
data ↑_⇓_ : Ctx → Env → Set where
  lift-∅ : ↑ ∅ ⇓ ε
  lift-, : ∀{Γ ρ T vT} →
        ↑ Γ ⇓ ρ →
        ⟦ T ⟧ ρ ⇓ vT → -- this is well-defined for well-formed contexts, which have the telescope property
        -----------------------------------------------
        ↑ (Γ ,ᶜ T) ⇓ (ρ ,, ( ↑⟨ vT ⟩ ($ (ctx-length Γ))))
```
## The Normalizer

The normalizer is a composition of the previous evaluation and read-back functions.

```agda
data nf_⇓⟨_,_⟩_ : Exp{- term -} → Ctx → Exp{- type -} → Σ[ e ∈ Exp ](Nf e) → Set where
  norm : ∀{e eᴺᶠ v Γ ρₙ T 𝑇} →
        ↑ Γ ⇓ ρₙ →
        ⟦ e ⟧ ρₙ ⇓ v →
        ⟦ T ⟧ ρₙ ⇓ 𝑇 →
        ℜᴺᶠ⟨ ctx-length Γ ⟩ (↓⟨ 𝑇 ⟩ v) ⇓ eᴺᶠ →
        -----------------------------------
        nf e ⇓⟨ Γ , T ⟩ eᴺᶠ
```
# TODOs & Open Questions

* Semantic type selection ⟪_⟫∙Type⇓_ : Unclear what is the proper type at which to reflect
when selecting on a neutral value.
* Is subtyping/coercion relevant at all for NbE?

# Properties

We need to show that the relations model actual partial functions, i.e., they
  1. are deterministic relations: at most one output is related with each input (the various `det-` propositions below).
  2. they exhibit irrelevance: there is at most one proof for an input/output combination (the various `irrelevant-` propositions below).

```agda
det-·        : ∀{v₁ v₂ v₃ v₄}   → v₁ · v₂ ⇓ v₃        → v₁ · v₂ ⇓ v₄        → v₃ ≡ v₄
det-⟪-⟫∙Type : ∀{v₁ v₂ v₃}      → ⟪ v₁ ⟫∙Type⇓ v₂     → ⟪ v₁ ⟫∙Type⇓ v₃     → v₂ ≡ v₃
det-⟦-⟧ˢ     : ∀{σ ρ₁ ρ₂ ρ₃}     → ⟦ σ ⟧ˢ ρ₁ ⇓ ρ₂     → ⟦ σ ⟧ˢ ρ₁ ⇓ ρ₃      → ρ₂ ≡ ρ₃
det-⟦-⟧      : ∀{e ρ v₁ v₂}     → ⟦ e ⟧ ρ ⇓ v₁        → ⟦ e ⟧ ρ ⇓ v₂        → v₁ ≡ v₂
det-ℜᴺᶠᶜ     : ∀{𝑇 𝑐 nf₁ nf₂}   → ℜᴺᶠᶜ⟨ 𝑇 ⟩ 𝑐 ⇓ nf₁   → ℜᴺᶠᶜ⟨ 𝑇 ⟩ 𝑐 ⇓ nf₂   → nf₁ ≡ nf₂
det-ℜᴺᶠ      : ∀{n v nf₁ nf₂}   → ℜᴺᶠ⟨ n ⟩ v ⇓ nf₁    → ℜᴺᶠ⟨ n ⟩ v ⇓ nf₂    → nf₁ ≡ nf₂
det-ℜᴺᵉ      : ∀{n v ne₁ ne₂}   → ℜᴺᵉ⟨ n ⟩ v ⇓ ne₁    → ℜᴺᵉ⟨ n ⟩ v ⇓ ne₂    → ne₁ ≡ ne₂
det-↑        : ∀{Γ ρ₁ ρ₂}       → ↑ Γ ⇓ ρ₁            → ↑ Γ ⇓ ρ₂            → ρ₁ ≡ ρ₂ --TODO use pointwise equality, to avoid extensionality
det-nf       : ∀{e Γ T nf₁ nf₂} → nf e ⇓⟨ Γ , T ⟩ nf₁ → nf e ⇓⟨ Γ , T ⟩ nf₂ → nf₁ ≡ nf₂

det-· (app-ƛ x) (app-ƛ x₁)                                                   = det-⟦-⟧ x x₁
det-· (app-ne v₁·v₂⇓v₃) (app-ne v₁·v₂⇓v₄) rewrite det-· v₁·v₂⇓v₃ v₁·v₂⇓v₄ = refl
det-· app-suc app-suc                                                        = refl
det-· app-suc-ne app-suc-ne                                                  = refl

det-⟪-⟫∙Type sel-Type sel-Type = refl
det-⟪-⟫∙Type sel-ne sel-ne     = {!refl!} -- TODO this currently won't work, due to universel level 𝓁 not being an input

det-⟦-⟧ˢ eval-Id eval-Id = refl
det-⟦-⟧ˢ eval-↑ b = {!!} -- TODO see the TODO in the eval-↑ case ;)
det-⟦-⟧ˢ (eval-,ₛ a x) (eval-,ₛ b x₁) with det-⟦-⟧ˢ a b | det-⟦-⟧ x x₁
... | refl | refl = refl
det-⟦-⟧ˢ (eval-∘ₛ a a₁) (eval-∘ₛ b b₁) with det-⟦-⟧ˢ a b
... | refl with det-⟦-⟧ˢ a₁ b₁
... | refl = refl

det-⟦-⟧ eval-var eval-var                       = refl
det-⟦-⟧ eval-c eval-c                           = refl
det-⟦-⟧ (eval-Π a a₁) (eval-Π b b₁) rewrite det-⟦-⟧ a b | det-⟦-⟧ a₁ b₁ = refl
det-⟦-⟧ eval-ƛ eval-ƛ                           = refl
det-⟦-⟧ (eval-· a a₁ x) (eval-· b b₁ x₁) rewrite det-⟦-⟧ a b | det-⟦-⟧ a₁ b₁ | det-· x x₁ = refl
det-⟦-⟧ (eval-⟨Type⋯⟩ a a₁) (eval-⟨Type⋯⟩ b b₁) rewrite det-⟦-⟧ a b | det-⟦-⟧ a₁ b₁ = refl
det-⟦-⟧ (eval-Type a) (eval-Type b) rewrite det-⟦-⟧ a b = refl
det-⟦-⟧ (eval-∙Type a x) (eval-∙Type b x₁) rewrite det-⟦-⟧ a b | det-⟪-⟫∙Type x x₁ = refl
det-⟦-⟧ (eval-·ₛ x a) (eval-·ₛ x₁ b) rewrite det-⟦-⟧ˢ x x₁ | det-⟦-⟧ a b = refl

det-ℜᴺᶠᶜ ℜᴺᶠᶜ-𝑁 ℜᴺᶠᶜ-𝑁 = refl
det-ℜᴺᶠᶜ ℜᴺᶠᶜ-𝑆𝑒𝑡 ℜᴺᶠᶜ-𝑆𝑒𝑡 = refl
det-ℜᴺᶠᶜ ℜᴺᶠᶜ-⊥ ℜᴺᶠᶜ-⊥ = refl
det-ℜᴺᶠᶜ ℜᴺᶠᶜ-⊤ ℜᴺᶠᶜ-⊤ = refl
det-ℜᴺᶠᶜ ℜᴺᶠᶜ-𝑛-𝑧 ℜᴺᶠᶜ-𝑛-𝑧 = refl
det-ℜᴺᶠᶜ (ℜᴺᶠᶜ-𝑛-𝑠 a) (ℜᴺᶠᶜ-𝑛-𝑠 b) with det-ℜᴺᶠᶜ a b
... | refl = refl

det-ℜᴺᶠ (ℜᴺᶠ-c x) (ℜᴺᶠ-c x₁) rewrite det-ℜᴺᶠᶜ x x₁ = refl
det-ℜᴺᶠ (ℜᴺᶠ-ƛ x x₁ a) (ℜᴺᶠ-ƛ x₂ x₃ b) rewrite det-· x x₂ | det-· x₁ x₃ with det-ℜᴺᶠ a b
... | refl = refl
det-ℜᴺᶠ (ℜᴺᶠ-Π a a₁) (ℜᴺᶠ-Π b b₁) with det-ℜᴺᶠ a b | det-ℜᴺᶠ a₁ b₁
... | refl | refl = refl
det-ℜᴺᶠ (ℜᴺᶠ-⟪Type⋯⟫ a a₁) (ℜᴺᶠ-⟪Type⋯⟫ b b₁) with det-ℜᴺᶠ a b | det-ℜᴺᶠ a₁ b₁
... | refl | refl = refl
det-ℜᴺᶠ (ℜᴺᶠ-Type a) (ℜᴺᶠ-Type b) = {!!} --TODO this is also problematic atm
det-ℜᴺᶠ (ℜᴺᶠ-↑⟨-⟩ x x₁ x₂) (ℜᴺᶠ-↑⟨-⟩ x₃ x₄ x₅) with det-ℜᴺᵉ x₂ x₅
... | refl = refl

det-ℜᴺᵉ ℜᴺᵉ-var ℜᴺᵉ-var = refl
det-ℜᴺᵉ (ℜᴺᵉ-· a x) (ℜᴺᵉ-· b x₁) with det-ℜᴺᵉ a b | det-ℜᴺᶠ x x₁
... | refl | refl = refl
det-ℜᴺᵉ (ℜᴺᵉ-𝑠· a) (ℜᴺᵉ-𝑠· b) with det-ℜᴺᵉ a b
... | refl = refl
det-ℜᴺᵉ (ℜᴺᵉ-∙Type a) (ℜᴺᵉ-∙Type b) with det-ℜᴺᵉ a b
... | refl = refl

-- we won't need function extensionality
det-↑ lift-∅ lift-∅ = refl
det-↑ (lift-, a x) (lift-, b x₁) with det-↑ a b
... | refl with det-⟦-⟧ x x₁
... | refl = refl

det-nf (norm ↑Γ⇓ρₙ ⟦e⟧ρₙ⇓v ⟦T⟧ρₙ⇓𝑇 x₃) (norm ↑Γ⇓ρₙ' ⟦e⟧ρₙ'⇓v' ⟦T⟧ρₙ'⇓𝑇' x₇) rewrite det-↑ ↑Γ⇓ρₙ ↑Γ⇓ρₙ' | det-⟦-⟧ ⟦e⟧ρₙ⇓v ⟦e⟧ρₙ'⇓v' | det-⟦-⟧ ⟦T⟧ρₙ⇓𝑇 ⟦T⟧ρₙ'⇓𝑇' | det-ℜᴺᶠ x₃ x₇ = refl

-- TODO next to determinism, we also need to show proof irrelevance
postulate
  irrelevant-·        : ∀ {a b c}    → (prf prf' : a · b ⇓ c)           → prf ≡ prf'
  irrelevant-⟪-⟫∙Type : ∀{v₁ v₂}     → (prf prf' : ⟪ v₁ ⟫∙Type⇓ v₂)     → prf ≡ prf'
  irrelevant-⟦-⟧ˢ     : ∀{σ ρ₁ ρ₂}   → (prf prf' : ⟦ σ ⟧ˢ ρ₁ ⇓ ρ₂)      → prf ≡ prf'
  irrelevant-⟦-⟧      : ∀{e ρ v₁}    → (prf prf' : ⟦ e ⟧ ρ ⇓ v₁)         → prf ≡ prf'
  irrelevant-ℜᴺᶠᶜ     : ∀{𝑇 𝑐 nf₁}   → (prf prf' : ℜᴺᶠᶜ⟨ 𝑇 ⟩ 𝑐 ⇓ nf₁)   → prf ≡ prf'
  irrelevant-ℜᴺᶠ      : ∀{n v nf₁}   → (prf prf' : ℜᴺᶠ⟨ n ⟩ v ⇓ nf₁)    → prf ≡ prf'
  irrelevant-ℜᴺᵉ      : ∀{n v ne₁}   → (prf prf' : ℜᴺᵉ⟨ n ⟩ v ⇓ ne₁)    → prf ≡ prf'
  irrelevant-↑        : ∀{Γ ρ₁}      → (prf prf' : ↑ Γ ⇓ ρ₁)            → prf ≡ prf'
  irrelevant-nf       : ∀{e Γ T nf₁} → (prf prf' : nf e ⇓⟨ Γ , T ⟩ nf₁) → prf ≡ prf'

```
