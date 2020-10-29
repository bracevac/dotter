# Scratchpad for Syntax and Bindings

```agda
module dsube.Syntax4 where

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
--infixl 7 _·_
infix  9 S

data Ctx            : ℕ → Set                            -- term contexts
data ⊢⋆_            : ∀ {n} → Ctx n → Set                      -- types
data _∋_            : ∀{m n}{Γ : Ctx m} → Ctx n → ⊢⋆ Γ → Set        -- term variables
data _⊢_            : ∀{n}(Γ : Ctx n ) → ∀{m}{Ψ : Ctx m} → ⊢⋆ Ψ → Set -- terms

data Ctx where
  ∅   :
        ---
        Ctx 0

  _,_ : ∀ {n}(Γ : Ctx n) →
        ⊢⋆ Γ →
        -------------------
        Ctx (suc n)

-- Substitution op and lemmas: declaration
--_⋆[_] : ∀ {Γ U} → ⊢⋆ (Γ , U) → Γ ⊢ U → ⊢⋆ Γ                     -- subst term var in type
--_[_]  : ∀ {Γ U T} → (Γ , U ⊢ T) → (e : Γ ⊢ U) → Γ ⊢ (T ⋆[ e ]) -- subst term var in term
-- need special case if we have a (Γ , T) ⊢ T input? seems so
-- ∀ {Γ U T} → (Γ , T ⊢ T) → (e : Γ ⊢ T) → Γ ⊢ T

data ⊢⋆_ where
  `⊤ : ∀ {n}{Γ : Ctx n} → -- Top
      ----
      ⊢⋆ Γ

  `⊥ : ∀ {n}{Γ : Ctx n} →  -- Bot
      ----
      ⊢⋆ Γ

  ⟨Type_⋯_⟩ : ∀ {n}{Γ : Ctx n} →  -- Type L U
      ⊢⋆ Γ →
      ⊢⋆ Γ →
      -------
      ⊢⋆ Γ

  ⟨_⟩•Type : ∀ {n}{Γ : Ctx n}{L U : ⊢⋆ Γ} → -- e.Type
      Γ ⊢ ⟨Type L ⋯ U ⟩ →
      ---------------------
      ⊢⋆ Γ

  _⇒_ : ∀ {n}{Γ : Ctx n} → -- (x : S) → T⟨x⟩
      (S : ⊢⋆ Γ) →
      ⊢⋆ (Γ , S) →
      -------------
      ⊢⋆ Γ

data _∋_ where  -- term variables
  Z : ∀ {n}{Γ : Ctx n}{T : ⊢⋆ Γ} →
      ---------
      Γ , T ∋ T

  S : ∀ {n}{Γ : Ctx n}{m}{Ψ : Ctx m}{T : ⊢⋆ Ψ}{U : ⊢⋆ Γ} →
      Γ ∋ T →
      ---------
      Γ , U ∋ T

data _⊢_ where -- terms
  ` : ∀ {n}{Γ : Ctx n}{m}{Ψ : Ctx m}{T : ⊢⋆ Ψ} → -- variable
      Γ ∋ T →
      --------
      Γ ⊢ T

  ƛ : ∀{n}{Γ : Ctx n} → (T₁ : ⊢⋆ Γ) → ∀{T₂} → -- we have explicit type annotations, which is useful for information hiding via subtyping
      Γ , T₁ ⊢ T₂ →
      ------------
      Γ ⊢ T₁ ⇒ T₂

  -- _·_ : ∀ {Γ T₁ T₂} → -- dependent application
  --     Γ ⊢ T₁ ⇒ T₂  →
  --     (e : Γ ⊢ T₁) →
  --     ------------------
  --     Γ ⊢ T₂ ⋆[ e ]

  Type : ∀ {n}{Γ : Ctx n} → -- type values
      (T : ⊢⋆ Γ) →
      ------------------
      Γ ⊢ ⟨Type T ⋯ T ⟩

-- Renamings take variables in one context to another context
-- TODO: induction over the context?
-- TODO a) can we have a type-level context, which indexes the term-level contexts?
-- TODO b) can the term context be indexed by length? does it give us anything?
-- TODO c) can we have kinds?
-- TODO d) what about PTS style formulation?
-- TODO e) deBruijn levels instead?
-- TODO f) define renaming on entire telescope, i.e., all prefixes
-- TODO g) is there a connection to comonads we can exploit?




Ren⋆ : ℕ → ℕ → Set
Ren⋆ n m = ∀{k} → k ≤ n → k ≤ m

lift⋆ : ∀{n m} → Ren⋆ n m → Ren⋆ (suc n) (suc m)
lift⋆ ρ _≤_.z≤n = _≤_.z≤n
lift⋆ ρ (_≤_.s≤s x) = _≤_.s≤s (ρ x)



--  Ren∋ : ∀ {n m} Γ Φ  → Ren n m → Set
 -- Ren∋ Γ Φ ρ = {T : ⊢⋆ _ } → Γ ∋ T → Φ ∋ (ren⋆ ρ T)
 -- Ren⋆ : ∀ {n m} → Ren n m → Set
--  Ren⋆ ρ = ∀{Γ} → ⊢⋆ Γ → ⊢⋆ ρ Γ
 -- ren⋆ : ∀ {n m} → Ren n m → ∀{Γ : Ctx n}{Φ : Ctx m} → ⊢⋆ Γ → ⊢⋆ Φ
--  ren⋆ ρ T = ?
--  Ren n m = ∀{Γ : Ctx n}{Φ : Ctx m} →    ∀ {Ψ}{T : ⊢⋆ Ψ} → Γ ∋ T → Φ ∋ T
--   ren⋆ : ∀{Γ Φ} → Ren⋆ Γ Φ → ⊢⋆ Γ → ⊢⋆ Φ
--   ren⋆ = {!!}
--   Ren⊢ : ∀ (Γ Φ) → Ren⋆ Γ Φ → Set
--   Ren⊢ Γ Φ ρ⋆ = {T : ⊢⋆ _} → Γ ∋ T → Φ ∋ (ren⋆ ρ⋆ T)
--  lift⋆ : ∀{Γ Φ} → (ρ : Ren⋆ Γ Φ) →

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
    Ren Γ Φ = ∀ {Ψ}{T : ⊢⋆ Ψ} → Γ ∋ T → Φ ∋ (ren ??? T)
But where does it come from? Type renamings are induced by renamings!
There is a circularity here.
