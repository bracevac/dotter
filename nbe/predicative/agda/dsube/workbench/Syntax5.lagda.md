# Scratchpad for Syntax and Bindings

```agda
module dsube.Syntax5 where

open import Agda.Primitive using (lzero; lsuc; _⊔_; Level)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
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
data _⊢⋆_           : Ctx → Ctx → Set                      -- types
data _∋_            : (Γ : Ctx) → ∀{Ψ} → Γ ⊢⋆ Ψ → Set        -- term variables
data _⊢_            : (Γ : Ctx ) → ∀{Ψ} → Γ ⊢⋆ Ψ → Set -- terms

data Ctx where
  ∅   :
        ---
        Ctx

  _,_ : ∀ {Γ Ψ : Ctx} →
        Γ ⊢⋆ Ψ →
        -------------------
        Ctx

-- Substitution op and lemmas: declaration
-- _⋆[_] : ∀ {Γ U} → ⊢⋆ (Γ , U) → Γ ⊢ U → ⊢⋆ Γ                     -- subst term var in type
-- _[_]  : ∀ {Γ U T} → (Γ , U ⊢ T) → (e : Γ ⊢ U) → Γ ⊢ (T ⋆[ e ]) -- subst term var in term
-- need special case if we have a (Γ , T) ⊢ T input? seems so
-- ∀ {Γ U T} → (Γ , T ⊢ T) → (e : Γ ⊢ T) → Γ ⊢ T

data _⊢⋆_ where
  `⊤ : ∀ {Γ} → -- Top
      ----
      Γ ⊢⋆ ∅

  `⊥ : ∀ {Γ} →  -- Bot
      ----
      Γ ⊢⋆ ∅

  ⟨Type_⋯_⟩ : ∀ {Γ Ψ} →  -- Type L U
      Γ ⊢⋆ Ψ →
      Γ ⊢⋆ Ψ →
      -------
      Γ ⊢⋆ Ψ

  ⟨_⟩•Type : ∀ {Γ Ψ}{L U : Γ ⊢⋆ Ψ} → -- e.Type
      Γ ⊢ ⟨Type L ⋯ U ⟩ →
      ---------------------
      Γ ⊢⋆ Ψ

  _⇒_ : ∀ {Γ Ψ} → -- (x : S) → T⟨x⟩
      (S : Γ ⊢⋆ Ψ) →
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

-- mutual
-- -- Γ ≼ Φ iff  Φ is an extension of Γ (however, not necessarily a structural suffix, since we include lifting)
--   data _≼_ : Ctx → Ctx → Set where
--     ≼Z : ∀{Γ : Ctx} →
--          -------------
--          Γ ≼ Γ

--     ≼S : ∀{Γ Φ}{T : ⊢⋆ Φ} →
--          Γ ≼ Φ →
--          --------------------------
--          Γ ≼ (Φ , T)

--     ≼Lift : ∀{Γ Φ}{T : ⊢⋆ Γ} →
--           (ρ : Γ ≼ Φ) →
--           --------------------------
--           (Γ , T) ≼ (Φ , ren⋆ ρ T)

--   ren⋆ : ∀{Γ Φ} → Γ ≼ Φ → ⊢⋆ Γ → ⊢⋆ Φ
--   ren⋆ Γ≼Φ `⊤ = `⊤
--   ren⋆ Γ≼Φ `⊥ = `⊥
--   ren⋆ Γ≼Φ ⟨Type T₁ ⋯ T₂ ⟩ = ⟨Type ren⋆ Γ≼Φ T₁ ⋯ ren⋆ Γ≼Φ T₂ ⟩
--   ren⋆ Γ≼Φ ⟨ e ⟩•Type = ⟨ ren⊢ Γ≼Φ e ⟩•Type
--   ren⋆ Γ≼Φ (T₁ ⇒ T₂) = ren⋆ Γ≼Φ T₁ ⇒ ren⋆ (≼Lift Γ≼Φ) T₂

-- --  ren⋆-id :

--   ren⊢ : ∀{Γ Φ} → (ρ : Γ ≼ Φ) → ∀{T} → Γ ⊢ T → Φ ⊢ (ren⋆ ρ T) --this is somewhat wrong, because T can be a prefix type!
--   ren⊢ ρ (` x) = {!!}
--   ren⊢ ρ (ƛ T₁ e) = {!!}
--   ren⊢ ρ (e · e₁) = {!!}
--   ren⊢ ρ (Type T) = {!!}

-- Γ  ≼ Γ , U
-- Γ , T ≼ Γ , U , T  ? clearly not a syntactic prefix
-- so more accurate to read it as context extension and we require lifting as constructor then!
-- and we cannot conclude prefix property, e.g., clearly Γ , T ≼ Γ , T, but not
-- Γ , T ≼ Γ , U , T
