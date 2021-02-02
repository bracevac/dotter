# System Dᵉ<:>

An intrinsically-typed syntax for the System Dᵉ<:> calculus in Agda.
We try and follow "System F in Agda for Fun and Profit" by Chapman et
al.  as closely as possible, adapting it to dependent types.

Intrinsically-typed syntax is well-scoped and -typed by construction,
preventing common errors of extrinsic approaches.

```agda
module dsube.Syntax where

open import Agda.Primitive using (lzero; lsuc; _⊔_; Level)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _≤_) renaming (_⊔_ to _⊔ₙ_)
open import Relation.Nullary using (¬_)
```

## Renamings

Chapman et al. use intrinsically-typed deBruijn variables that convey
context and type requirements for the use of a variable in its type,
i.e., variables have type `Γ ∋ T`, by a technique originally
due to Altenkirch and Reuss. They define weakening and
substitution on top of renaming morphisms/functions, which exhibits
functor laws and avoids extensionality. The composability properties of
these notions come for free from the usual function composition.

It also has the benefit of *not* polluting the intrinsically-typed
term language with syntax for substitution operations, unlike some
earlier works on the topic (e.g., Chapman 2009 "Type Theory should Eat
Itself").

A complication that shows up in a dependently-typed setting is the
"tangling" introduced by types being dependent on term variables.
Here is our version of contexts and deBruijn variables:

    data Ctx : Set where
       ∅   : Ctx
       -- ⊢⋆ Γ stands for is an object language type in context Γ (def. omitted)
       _,_ : ∀ (Γ : Ctx) → ⊢⋆ Γ →
             -------------------
             Ctx

    data _∋_ where  -- term variables
       Z : ∀ {Γ}{T : ⊢⋆ Γ} →
           ---------
           Γ , T ∋ T

       S : ∀ {Γ Ψ}{T : ⊢⋆ Ψ}{U : ⊢⋆ Γ} →
           Γ ∋ T →
           ---------
           Γ , U ∋ T

Chapman et al. define a type of renamings, which take variables in one
context to variables in another context. Adapted to our setting (they
define it for contexts of type variables, which are not
dependent on term variables), a renaming in their style would be:

    Ren : Ctx → Ctx → Set
    Ren Γ Ψ = ∀ {T} → Γ ∋ T → Ψ ∋ T

However, this is thwarted by `T` being itself context-dependent, i.e.,
`T : ⊢⋆ Φ` for some context `Φ` which is a prefix of context `Γ`.
It is not guaranteed that `Φ` remains a prefix in the new context `Ψ`.

On the other hand, they admit that this style is more general than
necessary.  If we look closer, making some things more explicit, then
we realize that not all hope is lost:

    Ren Γ Ψ = ∀ {Φ}{T : ⊢⋆ Φ} → Γ ∋ T → Ψ ∋ T

It basically means that all a renaming can ever yield is an
*extension* of the context Γ to the right, which seems sufficient for
the uses, e.g., going under binders by weakening.  In fact, the main
purpose of renamings is defining weakening as a function.

Once we have weakening, we can also define substitution on
intrinsically-typed syntax in terms of functions, leaving it out of
the term syntax.

    _⋆[_] = ⊢⋆ Γ , U → Γ ⊢ U → ⊢⋆ Γ   -- subst term variable in types
    _[_]  = Γ , U ⊢ T → Γ ⊢ U → Γ ⊢ T -- subst term variable in terms
    -- these need to be mutually defined (or alternatively, use disjoint sum for one definition)

The function signatures precisely state the substitution lemmas.

```agda
infix  4 _∋_
infix  3 _⊢_
infixl 5 _,_

--infix  6 Π
infixr 7 _⇒_

-- infix  5 ƛ
infixl 7 _·_
infix  9 S

```
We introduce the syntax/typing judgments mutually,
indicated by declaring their signatures first:

```agda
-- TODO: universe polymorphism?
data Ctx            : Set                          -- term contexts
data ⊢⋆_            : Ctx → Set                    -- types
data _∋_            : ∀{Γ} → Ctx → ⊢⋆ Γ → Set      -- term variables
data _⊢_  (Γ : Ctx) : ∀{Φ} → ⊢⋆ Φ → Set                    -- terms
data _<:_ {Γ : Ctx} : ⊢⋆ Γ → ⊢⋆ Γ → Set            -- subtyping TODO moar rules
data _≡⋆_           : ∀{Γ} → ⊢⋆ Γ → ⊢⋆ Γ → Set      -- type equality
data _≡β_           : ∀{Γ T} → Γ ⊢ T → Γ ⊢ T → Set -- term equality

```
It might look puzzling at first that the _⊢_ judgment does not mention a
Γ type on the RHS, but a type Φ which is not related. This is necessary
to form term variables with the intrinsically-typed deBruijn indices in the
first place, since Γ ∋ T only states that T : ⊢⋆ Φ for a _prefix_ of Γ.
A property of the judgment thus is: if Γ ⊢ T is inhabited for T : ⊢⋆ Ψ,
then we have that Ψ is a prefix of Γ.
```


data Ctx where
  ∅   :
        ---
        Ctx

  _,_ : ∀ (Γ : Ctx) →
        ⊢⋆ Γ →
        -------------------
        Ctx

data ⊢⋆_ where
  `⊤ : ∀ {Γ} → -- Top
      ----
      ⊢⋆ Γ

  `⊥ : ∀ {Γ} →  -- Bot
      ----
      ⊢⋆ Γ

  ⟨Type_⋯_⟩ : ∀ {Γ} →  -- Type L U
      ⊢⋆ Γ →
      ⊢⋆ Γ →
      -------
      ⊢⋆ Γ

  ⟨_⟩•Type : ∀ {Γ L U} → -- e.Type
      Γ ⊢ ⟨Type L ⋯ U ⟩ →
      ---------------------
      ⊢⋆ Γ

  _⇒_ : ∀ {Γ} → -- (x : S) → T⟨x⟩
      (S : ⊢⋆ Γ) →
      ⊢⋆ (Γ , S) →
      -------------
      ⊢⋆ Γ

  _[_]⋆ : ∀ {Γ S} →  -- subst term in type T⟨e⟩ TODO: could this be made a function instead?
      ⊢⋆ (Γ , S) →
      Γ ⊢ S →
      -------------
      ⊢⋆ Γ

  cong<: : ∀ {Γ S U} → -- This is for making the subtyping on functions work out. TODO: can we factor out these things into renamings/substs as in the system f in agda paper?
      ⊢⋆ (Γ , U) →
      S <: U →
      --------------
      ⊢⋆ (Γ , S)
      -- what's not nice is that this rule makes the data type indexed, instead of parametric. potentially
      -- inhibiting type inference

data _∋_ where  -- term variables
  Z : ∀ {Γ}{T : ⊢⋆ Γ} →
      ---------
      Γ , T ∋ T

  S : ∀ {Γ Ψ}{T : ⊢⋆ Ψ}{U : ⊢⋆ Γ} →
      Γ ∋ T →
      ---------
      Γ , U ∋ T

mutual
  Renˣ : Ctx → Ctx → Set
  Renˣ Γ Φ = ∀ {Ψ}{T : ⊢⋆ Ψ} → Γ ∋ T → Φ ∋ T
  Ren⋆ : Ctx → Ctx → Set
  Ren⋆ Γ Φ = ⊢⋆ Γ → ⊢⋆ Φ
  ren⋆ : ∀ {Γ Φ} → Renˣ Γ Φ → ⊢⋆ Γ → ⊢⋆ Φ
  ren⋆ ρ `⊤ = `⊤
  ren⋆ ρ `⊥ = `⊥
  ren⋆ ρ ⟨Type T₁ ⋯ T₂ ⟩ = ⟨Type ren⋆ ρ T₁ ⋯ ren⋆ ρ T₂ ⟩
  ren⋆ ρ ⟨ e ⟩•Type = {!!}
  ren⋆ ρ (T ⇒ T₁) = {!!}
  ren⋆ ρ (T [ x ]⋆) = {!⊥!}
  ren⋆ ρ (cong<: T x) = {!!}
  ren : ∀ {Γ Φ} → Renˣ Γ Φ → ⊢⋆ Γ → ⊢⋆ Φ
--lift : ∀ {Γ Φ} → (ρ : Ren Γ Φ) → ∀ {T : ⊢⋆ Γ} → Ren (Γ , T) (Φ , ρ T)


data _⊢_ Γ where -- terms
  ` : ∀ {Ψ}{T : ⊢⋆ Ψ} → -- variable
      Γ ∋ T →
      --------
      Γ ⊢ T

  ƛ : ∀ (S : ⊢⋆ Γ) → ∀{T} → -- we have explicit type annotations, which is useful for information hiding via subtyping
      Γ , S ⊢ T →
      ------------
      Γ ⊢ S ⇒ T

  _·_ : ∀ {S T} → -- dependent application
      Γ ⊢ S ⇒ T  →
      (e : Γ ⊢ S) →
      ------------------
      Γ ⊢ T [ e ]⋆

  Type : -- type values
      (T : ⊢⋆ Γ) →
      ------------------
      Γ ⊢ ⟨Type T ⋯ T ⟩

  subs : ∀ {Ψ}{T U : ⊢⋆ Ψ} → -- subsumption TODO: can we just place subtyping in the app rule and be done?
      Γ ⊢ T → -- TODO should T and U be in the same context Ψ?
      T <: U →  -- TODO would be nice if this was implicit, but I am getting weird errors if I do it
      --------------
      Γ ⊢ U

data _<:_ {Γ} where -- subtyping TODO moar rules
  <:-refl : ∀ {T U} →
      T ≡⋆ U → -- this is similar to Luo's Calculus of Constructions with cumulativity
      ---------
      T <: U -- TODO: limit to type selections? define for β-equal types instead?

  <:-trans : ∀ {T U V} →
      T <: U →
      U <: V →
      ---------
      T <: V

  <:-⊤ : ∀ {U} →
      -----------
      U <: `⊤

  <:-⊥ : ∀ {U} →
     ------------
     `⊥ <: U

  <:-Type[] : ∀ {S₁ U₁ S₂ U₂} →
     S₂ <: S₁ →
     U₁ <: U₂ →
     ---------------------------------------
     ⟨Type S₁ ⋯ U₁ ⟩ <: ⟨Type S₂ ⋯ U₂ ⟩

  <:-⇒ : ∀ {S₁ S₂ U₁ U₂} →
     (s : S₂ <: S₁) →
     (cong<: U₁ s) <: U₂ → -- Γ , x : S₂ ⊢ U₁ <: U₂
                           -- Γ ⊢ S₁ ⇒ U₁
                           -- Γ , x : S₁ ⊢ U₁
     -----------------------------
     (S₁ ⇒ U₁) <: (S₂ ⇒ U₂)

  -- TODO: type selection subtyping, what about subst and ren?

data _≡⋆_ where -- type equality
  ≡⋆-refl : ∀ {Γ}{T : ⊢⋆ Γ} →
     ------
     T ≡⋆ T

  ≡⋆-sym : ∀ {Γ}{S T : ⊢⋆ Γ} →
     S ≡⋆ T →
     ---------
     T ≡⋆ S

  ≡⋆-trans : ∀ {Γ}{T U V : ⊢⋆ Γ} →
     T ≡⋆ U →
     U ≡⋆ V →
     ---------
     T ≡⋆ V

  ≡⋆-⇒ : ∀ {Γ}{S₁ S₂ : ⊢⋆ Γ}{T₁ : ⊢⋆ (Γ , S₁)}{T₂ : ⊢⋆ (Γ , S₂)} →
     (eq : S₁ ≡⋆ S₂) →
     T₁ ≡⋆ (cong<: T₂ (<:-refl eq)) →
     -----------------------------
     (S₁ ⇒ T₁) ≡⋆ (S₂ ⇒ T₂)

  ≡⋆-Type[] : ∀ {Γ}{S₁ T₁ S₂ T₂ : ⊢⋆ Γ} →
     S₁ ≡⋆ S₂ →
     T₁ ≡⋆ T₂ →
     ----------------------------------
     ⟨Type S₁ ⋯ T₁ ⟩ ≡⋆ ⟨Type S₂ ⋯ T₂ ⟩


  ≡⋆-•Type : ∀ {Γ}{S T : ⊢⋆ Γ}{e₁ e₂ : Γ ⊢ ⟨Type S ⋯ T ⟩} →
     e₁ ≡β e₂ →
     -------------------------
     ⟨ e₁ ⟩•Type ≡⋆ ⟨ e₂ ⟩•Type

data _≡β_ where -- term equality
  -- β≡β : ∀{S T} →
  --    (B : Γ , S ⊢ T) →
  --    (A : Γ ⊢ S) →
  --    ------------------------
  --    ƛ B · A ≡β B [ A ]
  -- TODO rest of the rules refl, sym, trans, congruences

-- TODO: try out a PTS style formulation, eliminating most of the stratifications,
-- respectively distinction via disjoint sum.
-- right now, we have inductive-inductive definitions, which are dubious
```
