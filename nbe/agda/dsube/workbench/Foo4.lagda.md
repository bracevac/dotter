Here, we show an unstratified object language, which is well-scoped,
and a lightweight indexing scheme that asserts intrinsic well-sortedness, but
not full intrinsic typing.

```agda
module dsube.Foo4 where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)

ℒ = ℕ -- universe levels of the object language



data Class : Set where
  tm : Class       -- think of it as set -1
  set : ℒ → Class

mutual
  data Ctx : Set
  data _⊢_ : Ctx → Class → Set

  data Ctx where
    ∅   : Ctx
    _,_ : (Γ : Ctx) → ∀{𝓁} → Γ ⊢ (set 𝓁) → Ctx

  weaken : ∀{Γ 𝓁 𝓀}{S : Γ ⊢ (set 𝓀)} → Γ ⊢ (set 𝓁) → (Γ , S) ⊢ (set 𝓁)

  data _∋_ : (Γ : Ctx) → ∀{𝓁} → Γ ⊢ (set 𝓁) → Set where



  data _⊢_ where
    𝑆𝑒𝑡    : ∀{Γ} → (𝓁 : ℒ) → Γ ⊢ (set (suc 𝓁))
    Nat   : ∀{Γ} → Γ ⊢ (set 0)
    Π     : ∀{𝓁}{Γ} →
            (S : Γ ⊢ (set 𝓁)) → (Γ , S) ⊢ (set 𝓁) →
            --------------------------------------
            Γ ⊢ (set 𝓁)
    -- `_    : ∀{Γ 𝓁}{T : Γ ⊢ (ty 𝓁)} →
    --         Γ ∋ T →
    --         Γ ⊢ (tm T) -- is it a term or type variable? matter of perspective, see next constructor
    z     : ∀{Γ} → Γ ⊢ tm
    s     : ∀{Γ} → Γ ⊢ tm → Γ ⊢ tm
    ƛ     : ∀{Γ 𝓁 c}{S : Γ ⊢ (set  𝓁)} →
           (Γ , S) ⊢ c →
           -------------------
           Γ ⊢ c
    _·_   : ∀{Γ c} →
           Γ ⊢ c → Γ ⊢ c →
           --------------------------------------
           Γ ⊢ c


-- -- a predicative, dependently-typed λ-calculus with natural numbers
-- data _⊢_ where
--   𝑆𝑒𝑡    : ∀{n} → (𝓁 : ℒ) → n ⊢ (set (suc 𝓁))
--   Nat   : ∀{n} → n ⊢ (set 0)
--   Π     : ∀{𝓁}{n} →
--           (S : n ⊢ (ty 𝓁)) → (Γ , S) ⊢ (ty 𝓁) →
--           --------------------------------------
--           Γ ⊢ (ty 𝓁)
--   `_    : ∀{Γ 𝓁}{T : Γ ⊢ (ty 𝓁)} →
--           Γ ∋ T →
--           Γ ⊢ (tm T) -- is it a term or type variable? matter of perspective, see next constructor
--   z     : ∀{Γ} → Γ ⊢ (tm Nat)
--   s     : ∀{Γ} → Γ ⊢ (tm Nat) → Γ ⊢ (tm Nat)
--   ƛ     : ∀{Γ 𝓁}{S : Γ ⊢ (ty {Γ} 𝓁)}{T} →
--          (Γ , S) ⊢ (tm T) →
--          -------------------
--          Γ ⊢ (tm (Π S T))
--   _·ₛₜ_  : ∀{Γ Δ 𝓁} → Γ ⊢ (ty 𝓁) → (σ : Γ ⟹ Δ) → Δ ⊢ (ty 𝓁)                         -- apply subst to type
--   _·ₛₜₘ_ : ∀{Γ Δ 𝓁}{T : Γ ⊢ (ty 𝓁)} → Γ ⊢ (tm T) → (σ : Γ ⟹ Δ) → Δ ⊢ (tm (T ·ₛₜ σ)) -- apply subst to term
--   _·_   : ∀{Γ 𝓁}{S : Γ ⊢ (ty 𝓁)}{T} → -- apply lambda
--          Γ ⊢ (tm (Π S T)) → (e : Γ ⊢ (tm S)) →
--          --------------------------------------
--          Γ ⊢ (tm (T ·ₛₜ [ e ] ))

-- data _⟹_ where
--   Id   : ∀{Γ} → Γ ⟹ Γ
--   ↑    : ∀{Γ 𝓁}{T : Γ ⊢ (ty 𝓁)} → Γ ⟹ (Γ , T)
--   _,ₛ_ : ∀{Γ Δ} → (σ : Γ ⟹ Δ) → ∀{𝓁}{T : Γ ⊢ (ty 𝓁)} → Δ ⊢ (tm (T ·ₛₜ σ)) → (Γ , T) ⟹ Δ
--   _∘ₛ_ : ∀{Γ Δ Ψ} → Δ ⟹ Γ → Ψ ⟹ Δ → Ψ ⟹ Γ

-- -- Important insight from studying extrinsic formulations: we should apply the weakening subst ↑
-- -- to the RHS of the deBruijn variable, which is at the same time the lookup.
-- -- This makes it also easier to work with types which depend on a proper prefix of Γ.
-- data _∋_ where
--   Z : ∀{Γ 𝓁}{T : Γ ⊢ (ty 𝓁)} → (Γ , T) ∋ (T ·ₛₜ ↑)
--   S : ∀{Γ 𝓁 𝓀}{S : Γ ⊢ (ty 𝓁)}{T : Γ ⊢ (ty 𝓀)} → Γ ∋ S → (Γ , T) ∋ (S ·ₛₜ ↑)

-- TODO impl of [_]

-- this won't type check in Agda at the moment, because it doesn't know that Nat = (Nat ·ₛ Id),
-- a drawback of first-order substitutions.
-- σ = Id ,ₛ z
