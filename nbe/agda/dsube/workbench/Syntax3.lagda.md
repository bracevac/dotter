# Scratchpad for Syntax and Bindings

```agda
module dsube.Syntax3 where

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

data Ctx            : ℕ → Set                          -- term contexts
data ⊢⋆_            : ∀{n} → Ctx n → Set                    -- types
data _∋_            : ∀{n m}{Γ : Ctx m} → Ctx n → ⊢⋆ Γ → Set      -- term variables
data _⊢_            : ∀{n}(Γ : Ctx n) → ⊢⋆ Γ → Set                    -- terms

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
