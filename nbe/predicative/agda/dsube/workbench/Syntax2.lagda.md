# Scratchpad for Syntax and Bindings

```agda
module dsube.Syntax2 where

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

infix  4 _∋_
infix  3 _⊢_
infixl 5 _,_

--infix  6 Π
infixr 7 _⇒_

-- infix  5 ƛ
infixl 7 _·_
infix  9 S

data Ctx            : Set                            -- term contexts
data ⊢⋆_            : Ctx → Set                      -- types
data _∋_            : ∀{Γ} → Ctx → ⊢⋆ Γ → Set        -- term variables
data _⊢_            : (Γ : Ctx ) → ∀{Ψ} → ⊢⋆ Ψ → Set -- terms

data Ctx where
  ∅   :
        ---
        Ctx

  _,_ : ∀ (Γ : Ctx) →
        ⊢⋆ Γ →
        -------------------
        Ctx

-- Substitution op and lemmas: declaration
_⋆[_] : ∀ {Γ U} → ⊢⋆ (Γ , U) → Γ ⊢ U → ⊢⋆ Γ                     -- subst term var in type
_[_]  : ∀ {Γ U T} → (Γ , U ⊢ T) → (e : Γ ⊢ U) → Γ ⊢ (T ⋆[ e ]) -- subst term var in term
-- need special case if we have a (Γ , T) ⊢ T input? seems so
-- ∀ {Γ U T} → (Γ , T ⊢ T) → (e : Γ ⊢ T) → Γ ⊢ T

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

data _∋_ where  -- term variables
  Z : ∀ {Γ}{T : ⊢⋆ Γ} →
      ---------
      Γ , T ∋ T

  S : ∀ {Γ Ψ}{T : ⊢⋆ Ψ}{U : ⊢⋆ Γ} →
      Γ ∋ T →
      ---------
      Γ , U ∋ T

data _⊢_ where -- terms
  ` : ∀ {Γ Ψ}{T : ⊢⋆ Ψ} → -- variable
      Γ ∋ T →
      --------
      Γ ⊢ T

  ƛ : ∀{Γ} → (T₁ : ⊢⋆ Γ) → ∀{T₂} → -- we have explicit type annotations, which is useful for information hiding via subtyping
      Γ , T₁ ⊢ T₂ →
      ------------
      Γ ⊢ T₁ ⇒ T₂

  _·_ : ∀ {Γ T₁ T₂} → -- dependent application
      Γ ⊢ T₁ ⇒ T₂  →
      (e : Γ ⊢ T₁) →
      ------------------
      Γ ⊢ T₂ ⋆[ e ]

  Type : ∀ {Γ} → -- type values
      (T : ⊢⋆ Γ) →
      ------------------
      Γ ⊢ ⟨Type T ⋯ T ⟩

-- Renamings take variables in one context to another context
-- TODO: induction over the context?
Ren : Ctx → Ctx → Set
Ren Γ Φ = ∀ {Ψ}{T : ⊢⋆ Ψ} → Γ ∋ T → Φ ∋ T -- Φ = Γ ++ Γ'

-- Action of renamings on types and terms: declaration
ren⋆ : ∀ {Γ Φ} → Ren Γ Φ → ⊢⋆ Γ → ⊢⋆ Φ                    -- type renaming
ren⊢ : ∀ {Γ Φ T} → (ρ : Ren Γ Φ) → Γ ⊢ T → Φ ⊢ (ren⋆ ρ T) -- term renaming

-- Φ ⊢⋆ K, K ::= ⋆ | K ⇒ K

-- renamings and substitutions : definition
lift : ∀ {Γ Φ} → (ρ : Ren Γ Φ) → ∀ {T : ⊢⋆ Γ} → Ren (Γ , T) (Φ , (ren⋆ ρ T))
lift ρ Z = {!Z!}
lift ρ (S x) = S (ρ x)

ren⋆ ρ `⊤ = `⊤
ren⋆ ρ `⊥ = `⊥
ren⋆ ρ ⟨Type T₁ ⋯ T₂ ⟩ = ⟨Type ren⋆ ρ T₁ ⋯ ren⋆ ρ T₂ ⟩
ren⋆ ρ ⟨ e ⟩•Type = ⟨ ren⊢ ρ e ⟩•Type
ren⋆ ρ (T₁ ⇒ T₂) =  ren⋆ ρ T₁ ⇒ ren⋆ (lift ρ) T₂

ren⊢ ρ (` x) = {! ` (ρ x)!}
ren⊢ ρ (ƛ T e) = ƛ (ren⋆ ρ T) (ren⊢ (lift ρ) e)
ren⊢ ρ (e₁ · e₂) = {!!}
ren⊢ ρ (Type T) = Type (ren⋆ ρ T)

`⊤ ⋆[ e ] = `⊤
`⊥ ⋆[ e ] = `⊥
⟨Type T₁ ⋯ T₂ ⟩ ⋆[ e ] =  ⟨Type T₁ ⋆[ e ] ⋯ T₂ ⋆[ e ] ⟩
⟨ e₁ ⟩•Type ⋆[ e₂ ] =   ⟨ e₁ [ e₂ ] ⟩•Type --
(T₁ ⇒ T₂) ⋆[ e ] = {!!}

-- TODO: it's strange that the Z case is impossible, that cannot be right!
` (S x) [ e' ] = {!!}
ƛ S₁ e [ e' ] = {!!}
(e · e₁) [ e' ] = {!!}
Type T [ e' ] = {!!}

-- alternative renaming encoding
-- seems induction-recursion is needed, because we want to define the renaming actions simultaneously
```
# Core Issue: Renaming Functions for dependently- & intrinsically-typed Syntax

In Chapman et al., the type of renamings is an alias to a polymorphic function,

    Ren Γ Φ = ∀ {T} → Γ ∋ T → Φ ∋ T

for renaming of variables,
which is simple, because the RHS of de Bruijn variables Γ ∋ T is *context independent* in their work.
In dep. typed systems, we have what de Bruijn called "telescopes", i.e., T depends on a
prefix Ψ of Γ, i.e., T : ⊢⋆ Ψ. Telescopes are what makes these definitions more complicated.
We cannot expect that the very same T will be in Φ, since the action of the renaming should somehow affect
Ψ, the context in which T is valid, too. Somehow we need to say that

    Ren Γ Φ = ∀ {T} → Γ ∋ T → Φ ∋ <some type T' which stems from renaming T>

Here, we attempt to give more fine-grained explanation of how telescoped variables/types/terms
can be renamed, by means of an inductive type for renamings. Intuitively, Ren' Γ Ψ still
stands for a renaming function in the sense of Chapman et al. It seems inevitable to have
a mutual resp. inductive-recursive definition of the renamings of variables and their
*action* on types and terms. Chapman et al. could define these entities separately.
It seems we cannot in our setting.

```agda


-- (ρ : Ren Γ Φ) → ∀ T U → (Γ , T) ∋ U → (Φ , ren⋆ ρ T) ∋ ren⋆ ρ U  ACHTUNG! prefix context! important: this coincides with inlining their definition of ren on nf into liftnf (sec. 5.1)

-- (ρ : Ren Γ Φ) → ∀ T → Γ ⊢ T → Φ ⊢ ∋ ren⋆ ρ T    ACHTUNG! prefix context!
-- (ρ : Ren Γ Φ) → ⊢⋆ Γ → ⊢⋆ Φ this is the most unproblematic

-- mutual
--   data Ren' : Ctx → Ctx → Set where
-- --  Ren' Γ Φ = ∀ {Ψ}{T : ⊢⋆ Ψ} → Γ ∋ T → Φ ∋ T
--   RZ :
--   rename⋆ : ∀{Γ Φ} → Ren' Γ Φ → ⊢⋆ Γ → ⊢⋆ Φ
--   rename⋆ ρ `⊤ = `⊤
--   rename⋆ ρ `⊥ = `⊥
--   rename⋆ ρ ⟨Type T₁ ⋯ T₂ ⟩ = ⟨Type rename⋆ ρ T₁ ⋯ rename⋆ ρ T₂ ⟩
--   rename⋆ ρ ⟨ e ⟩•Type = {!!}
--   rename⋆ ρ (T₁ ⇒ T₂) = (rename⋆ ρ T₁) ⇒ rename⋆ (lift' ρ) T₂
--   lift' : ∀{Γ Φ} → (ρ : Ren' Γ Φ) → ∀{T : ⊢⋆ Γ} → Ren' (Γ , T) (Φ , rename⋆ ρ T)
--   lift' ρ Z = {!Z!} -- why impossible???
--   lift' ρ (S x) = S (ρ x)
--   rename⊢ : ∀{Γ Φ} → (ρ : Ren' Γ Φ) → ∀{Ψ}{T : ⊢⋆ Ψ} → Γ ⊢ T → Φ ⊢ T
--   rename⊢ ρ (` x) = {!` (ρ x)!}
--   rename⊢ ρ (ƛ T e) = {!!} --ƛ (rename⋆ ρ T) (rename⊢ (lift' ρ) e)
--   rename⊢ ρ (e₁ · e₂) = {!(rename⊢ ρ e₁) · ?!} -- TODO
--   rename⊢ ρ (Type T) = {!!} --Type (rename⋆ ρ T)


-- mutual
--   data Ren' : Ctx → Ctx → Set where
--     RZ : ∀{Γ} → Ren' Γ Γ
--     RS : ∀{Γ Φ} → (ρ : Ren' Γ Φ) → ∀{T : ⊢⋆ Γ} → Ren' (Γ , T) (Φ , rename⋆ ρ T)
--   rename⋆ : ∀{Γ Φ} → Ren' Γ Φ → ⊢⋆ Γ → ⊢⋆ Φ
--   rename⋆ ρ `⊤ = `⊤
--   rename⋆ ρ `⊥ = `⊥
--   rename⋆ ρ ⟨Type T₁ ⋯ T₂ ⟩ = ⟨Type rename⋆ ρ T₁ ⋯ rename⋆ ρ T₂ ⟩
--   rename⋆ ρ ⟨ e ⟩•Type = ⟨ rename⊢ ρ e ⟩•Type
--   rename⋆ ρ (T₁ ⇒ T₂) = (rename⋆ ρ T₁) ⇒ rename⋆ (RS ρ) T₂
--   rename⊢ : ∀{Γ Φ} → (ρ : Ren' Γ Φ) → ∀{T} → Γ ⊢ T → Φ ⊢ (rename⋆ ρ T)
--   rename⊢ ρ (` x) = {!!}
--   rename⊢ ρ (ƛ T e) = ƛ (rename⋆ ρ T) (rename⊢ (RS ρ) e)
--   rename⊢ ρ (e₁ · e₂) = {!(rename⊢ ρ e₁) · ?!} -- TODO
--   rename⊢ ρ (Type T) = Type (rename⋆ ρ T)
--  rename∋ : ∀{Γ Φ} → (ρ : Ren' Γ Φ) →  ∀ {Ψ}{T : ⊢⋆ Ψ} → Γ ∋ T → Φ ∋ (rename⋆ ρ T)
--  rename∋ (RS ρ) Z = {!!}
--  rename∋ (RS ρ) (S x) = {!!}
```
Defining the lift function, Z case:
    ρ : Ren Γ Φ
    T : ⊢⋆ Ψ
    x : Γ , T ∋ T

by inversion of ∋, we have that
    x = Z
    Ψ = Γ

need:

    Φ , ren⋆ ρ T ∋ T

we have that

    ren⋆ ρ : ⊢⋆ Γ → ⊢⋆ Φ,

hence,

    ren⋆ ρ T : ⊢⋆ Φ

thus

    Φ , ren⋆ ρ T

is a valid context satisfying the telescope property.

problem:

by contract of Ren, the object lang. type  T : ⊢⋆ Γ must still be in (Φ , ren⋆ ρ T)
Chapman and Wadler just define

    lift ρ Z = Z

this'll work since the things they add to contexts are independent of context.
But that is impossible for our case, which has telescopes. We would require T ≡ ren⋆ ρ T by
the signature of Z.

Herein lies the problem: the term variable renaming requires a type renaming
    Ren Γ Φ = ∀ {Ψ}{T : ⊢⋆ Ψ} → Γ ∋ T → Φ ∋ (ren⋆ ??? T)
But where does it come from? Type renamings are induced by renamings!
There is a circularity here.

In Chapman and Walder, Sec5, they have renamings on terms in normal form, which are
_indexed_ by type renamings, and thus have by definition a handle to such a type renaming.
This works in their system, because type do not depend on term-level variables, and
term-level contexts are indexed by type-level contexts!
