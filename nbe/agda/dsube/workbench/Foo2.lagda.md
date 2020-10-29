This file shows a way to define an unstratified object language in
intrinsically-typed and well-scoped style.

```agda
module dsube.Foo2 where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)

ℒ = ℕ -- universe levels of the object language

data Ctx⋆ : Set where
  ∅⋆   : Ctx⋆
  _,⋆_ : Ctx⋆ → ℒ → Ctx⋆

data _∋⋆_ : Ctx⋆ → ℒ → Set where
  Z⋆ : ∀{Φ 𝓁} → (Φ ,⋆ 𝓁) ∋⋆ 𝓁
  S⋆ : ∀{Φ 𝓁 𝓀} → Φ ∋⋆ 𝓁 → (Φ ,⋆ 𝓀) ∋⋆ 𝓁

Ren⋆ : Ctx⋆ → Ctx⋆ → Set
Ren⋆ Φ Ψ = ∀{𝓁} → Φ ∋⋆ 𝓁 → Ψ ∋⋆ 𝓁
lift⋆ : ∀{Φ Ψ 𝓁} → Ren⋆ Φ Ψ → Ren⋆ (Φ ,⋆ 𝓁) (Ψ ,⋆ 𝓁)
lift⋆ ρ Z⋆ = Z⋆
lift⋆ ρ (S⋆ p) = S⋆ (ρ p)


data Ctx : Ctx⋆ → Set
data Class : ∀{Φ} → Ctx Φ → ℒ → Set
-- substitutions between contexts
--data _⟹_ : Ctx → Ctx → Set
data _⊢_ : ∀{Φ 𝓁} → (Γ : Ctx Φ) → Class Γ 𝓁 → Set
```
Insight: an unstratified system comes with a classification theorem (cf. Geuvers'94),
essentially discerning the terms in the typing relation into mutually-exclusive groups.
Following this approach, we aim to let the intrinsic term formation/typing judgment
state the classification theorem.

A typing Γ ⊢ e : T induces two classes:
1) e is a *type*, i.e., T = Set(𝓁) for some level 𝓁 ∈ ℒ.
2) e is an *object* (or *term*, *inhabitant*) of type T, i.e., Γ ⊢ T : Set(𝓁) for some 𝓁 (note the difference to case 1).

The inductive type "Class" below discerns these to situations, and we index the
type for intrinsic terms/types with it. Alternatively, we could have used a disjoint sum ⊎, but
that would be less readable.
```agda


data Class where
  ty : ∀{Φ}{Γ : Ctx Φ} → (𝓁 : ℒ) → Class Γ 𝓁
  tm : ∀{Φ}{Γ : Ctx Φ}{𝓁} → Γ ⊢ (ty {Φ} {Γ} 𝓁) → Class Γ 𝓁

data Ctx  where
  ∅   : Ctx ∅⋆
  _,_ : ∀{Φ}→ (Γ : Ctx Φ) → ∀{𝓁} → Γ ⊢ (ty 𝓁) → Ctx (Φ ,⋆ 𝓁)

weaken-ty : ∀{Φ}{Γ : Ctx Φ}{𝓀}{S : Γ ⊢ (ty 𝓀)}{𝓁} → Γ ⊢ (ty 𝓁) → (Γ , S) ⊢ (ty 𝓁)

-- -- deBruijn index
data _∋_ : ∀{Φ} → (Γ : Ctx Φ) → ∀{𝓁} → Γ ⊢ (ty 𝓁) → Set where
  Z : ∀{Φ}{Γ : Ctx Φ}{𝓁}{T : Γ ⊢ (ty 𝓁)} →
      -----------------------
      (Γ , T) ∋ (weaken-ty T)
  S : ∀{Φ}{Γ : Ctx Φ}{𝓀}{S : Γ ⊢ (ty 𝓀)}{𝓁}{T : Γ ⊢ (ty 𝓁)} →
      Γ ∋ T →
      -----------------------
      (Γ , S) ∋ (weaken-ty T)

Ren : ∀{Φ Ψ} → Ctx Φ → Ctx Ψ → Ren⋆ Φ Ψ → Set
ren-ty : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}{ρ : Ren⋆ Φ Ψ} →
         Ren Γ Δ ρ → ∀{𝓁} → Γ ⊢ (ty 𝓁) → Δ ⊢ (ty 𝓁) -- type renaming
ren-tm : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}{ρ : Ren⋆ Φ Ψ} → (ρ' : Ren Γ Δ ρ) →
         ∀{𝓁}{T : Γ ⊢ (ty 𝓁)} → Γ ⊢ (tm T) → Δ ⊢ (tm (ren-ty ρ' T)) -- term renaming
lift : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}{ρ : Ren⋆ Φ Ψ} →
       (ρ' : Ren Γ Δ ρ) → ∀{𝓁}{T : Γ ⊢ (ty 𝓁)} → Ren (Γ , T) (Δ , (ren-ty ρ' T)) (lift⋆ ρ)


-- TODO: have promotion of variables at diff levels like in system f in agda paper?

-- -- induce single substitution


-- -- a predicative, dependently-typed λ-calculus with natural numbers
data _⊢_ where
  𝑆𝑒𝑡    : ∀{Φ}{Γ : Ctx Φ} → (𝓁 : ℒ) → Γ ⊢ (ty (suc 𝓁))
  Nat   : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ (ty 0)
  Π     : ∀{Φ 𝓁}{Γ : Ctx Φ} →
          (S : Γ ⊢ (ty 𝓁)) → (Γ , S) ⊢ (ty 𝓁) →
          --------------------------------------
          Γ ⊢ (ty 𝓁)
  `_    : ∀{Γ 𝓁}{T : Γ ⊢ (ty 𝓁)} →
           Γ ∋ T →
           Γ ⊢ (tm T) -- is it a term or type variable? matter of perspective, see next constructor
--   -- Another insight: what is a type at one level, is a term at next level, which we model by the following:
  ↟     : ∀{𝓁}{Γ} → Γ ⊢ (ty 𝓁) → Γ ⊢ (tm (𝑆𝑒𝑡 𝓁))
  ⟨Type_⋯_⟩ : ∀{Φ 𝓁}{Γ : Ctx Φ} →
          (S : Γ ⊢ (ty 𝓁)) → (T : Γ ⊢ (ty 𝓁)) →
          --------------------------------------
          Γ ⊢ (ty (suc 𝓁))
  Type :  ∀{Φ 𝓁}{Γ : Ctx Φ} →
          (T : Γ ⊢ (ty 𝓁)) →
          --------------------
          Γ ⊢ (tm ⟨Type T ⋯ T ⟩)
  ⟨_⟩∙Type : ∀{Φ 𝓁}{Γ : Ctx Φ}{S : Γ ⊢ (ty 𝓁)}{T : Γ ⊢ (ty 𝓁)} →
           Γ ⊢ (tm ⟨Type S ⋯ T ⟩) →
           Γ ⊢ (ty 𝓁)
--   z     : ∀{Γ} → Γ ⊢ (tm Nat)
--   s     : ∀{Γ} → Γ ⊢ (tm Nat) → Γ ⊢ (tm Nat)
  ƛ     : ∀{Γ 𝓁}{S : Γ ⊢ (ty 𝓁)}{T} →
         (Γ , S) ⊢ (tm T) →
         -------------------
         Γ ⊢ (tm (Π S T))
  -- _·ₛₜ_  : ∀{Γ Δ 𝓁} → Γ ⊢ (ty 𝓁) → (σ : Γ ⟹ Δ) → Δ ⊢ (ty 𝓁)                         -- apply subst to type
  -- _·ₛₜₘ_ : ∀{Γ Δ 𝓁}{T : Γ ⊢ (ty 𝓁)} → Γ ⊢ (tm T) → (σ : Γ ⟹ Δ) → Δ ⊢ (tm (T ·ₛₜ σ)) -- apply subst to term
  -- _·_   : ∀{Γ 𝓁}{S : Γ ⊢ (ty 𝓁)}{T} → -- apply lambda
  --        Γ ⊢ (tm (Π S T)) → (e : Γ ⊢ (tm S)) →
  --        --------------------------------------
  --        Γ ⊢ (tm (T ·ₛₜ [ e ] ))

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

ren-ty ρ (𝑆𝑒𝑡 𝓁) = 𝑆𝑒𝑡 𝓁
ren-ty ρ Nat = Nat
ren-ty ρ (Π T₁ T₂) = Π (ren-ty ρ T₁) (ren-ty (lift ρ) T₂)
ren-ty ρ ⟨Type T₁ ⋯ T₂ ⟩ = ⟨Type (ren-ty ρ T₁) ⋯ (ren-ty ρ T₂) ⟩
ren-ty ρ ⟨ e ⟩∙Type = ⟨ ren-tm ρ e ⟩∙Type

ren-tm ρ (` x) = {!!}
ren-tm ρ (↟ T) = {!↟ (ren-ty ρ T)!}
ren-tm ρ (Type T) = Type (ren-ty ρ T)
ren-tm ρ (ƛ e) = {!ƛ (ren-tm (lift ρ) e)!}

-- renamings and substitutions : definition

-- lift ρ Z = {!Z!}
-- lift ρ (S x) = S (ρ x)

-- ren⋆ ρ `⊤ = `⊤
-- ren⋆ ρ `⊥ = `⊥
-- ren⋆ ρ ⟨Type T₁ ⋯ T₂ ⟩ = ⟨Type ren⋆ ρ T₁ ⋯ ren⋆ ρ T₂ ⟩
-- ren⋆ ρ ⟨ e ⟩•Type = ⟨ ren⊢ ρ e ⟩•Type
-- ren⋆ ρ (T₁ ⇒ T₂) =  ren⋆ ρ T₁ ⇒ ren⋆ (lift ρ) T₂

-- ren⊢ ρ (` x) = {! ` (ρ x)!}
-- ren⊢ ρ (ƛ T e) = ƛ (ren⋆ ρ T) (ren⊢ (lift ρ) e)
-- ren⊢ ρ (e₁ · e₂) = {!!}
-- ren⊢ ρ (Type T) = Type (ren⋆ ρ T)


-- TODO impl of [_]

-- this won't type check in Agda at the moment, because it doesn't know that Nat = (Nat ·ₛ Id),
-- a drawback of first-order substitutions.
-- σ = Id ,ₛ z
