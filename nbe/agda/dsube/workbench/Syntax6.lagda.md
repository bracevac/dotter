# System Dᵉ<:>

An intrinsically-typed syntax for the System Dᵉ<:> calculus in Agda.
We try and follow "System F in Agda for Fun and Profit" by Chapman et
al.  as closely as possible, adapting it to dependent types.

Intrinsically-typed syntax is well-scoped and -typed by construction,
preventing common errors of extrinsic approaches.

```agda
module dsube.Syntax6 where

--open import Agda.Primitive using (lzero; lsuc; _⊔_; Level)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _≤_) renaming (_⊔_ to _⊔ₙ_)
open import Relation.Nullary using (¬_)

-- infix  4 _∋_
-- infix  3 _⊢_
-- infixl 5 _,_
-- infixl 5 _,⋆_
-- --infix  6 Π
-- infixr 7 _⇒_

-- -- infix  5 ƛ
-- infixl 7 _·_
-- infix  9 S

Sort = ℕ
⋆ : Sort
⋆ = 0



data Ctx⋆ : Set where -- kind context
  ∅⋆ : Ctx⋆
  _,⋆_ : Ctx⋆ → Sort → Ctx⋆
data _∋⋆_ : Ctx⋆ → Sort → Set where  -- kind of a variable
  Z⋆ : ∀{n : Sort} → (∅⋆ ,⋆ n) ∋⋆ n
  S⋆ : ∀{Φ m n} → Φ ∋⋆ n → (Φ ,⋆ m) ∋⋆ n

data Ctx : Ctx⋆ → Set                          -- term context


--data _⊢_  (Γ : Ctx) : ∀{Φ} → ⊢⋆ Φ → Set                    -- terms
--data _<:_ {Γ : Ctx} : ⊢⋆ Γ → ⊢⋆ Γ → Set            -- subtyping TODO moar rules
--data _≡⋆_           : ∀{Γ} → ⊢⋆ Γ → ⊢⋆ Γ → Set      -- type equality
--data _≡β_           : ∀{Γ T} → Γ ⊢ T → Γ ⊢ T → Set -- term equality
