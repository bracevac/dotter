-- A Formalisation of a Dependently Typed Language as an Inductive-Recursive Family
-- http://www.cse.chalmers.se/~nad/publications/danielsson-types2006.pdf

module dsube.Danielsson where

mutual
  data Ctx : Set where
    ε : Ctx
    _▹_ : (Γ : Ctx) → Ty Γ → Ctx

  data Ty : (Γ : Ctx) → Set where
    ⋆ : ∀ {Γ : Ctx} → Ty Γ
    Π : ∀ {Γ : Ctx} → (τ : Ty Γ) → Ty (Γ ▹ τ) → Ty Γ
    El : ∀ {Γ : Ctx} → Γ ⊢ ⋆ → Ty Γ

  data Subst : Ctx → Ctx → Set where
    -- Weakening
    wk : ∀ {Γ} → (σ : Ty Γ) → Subst Γ (Γ ▹ σ)
    -- Substituting a single variable
    sub : ∀ {Γ} {τ : Ty Γ} → Γ ⊢ τ → Subst (Γ ▹ τ) Γ
    -- Lifting
    _↑_ : ∀ {Γ Δ} → (ρ : Subst Γ Δ) → (σ : Ty Γ) → Subst (Γ ▹ σ) (Δ ▹ (σ / ρ))
    -- Identity
    id : (Γ : Ctx) → Subst Γ Γ
    -- Composition
    _⨀_ : ∀ {Γ Δ X} → Subst Γ Δ → Subst Γ X → Subst Γ X

  data _∋_ : (Γ : Ctx) → Ty Γ → Set where
    vz : ∀ {Γ : Ctx} → (τ : Ty Γ) → (Γ ▹ τ) ∋ (τ / wk τ)
    vs : ∀ {Γ : Ctx} {τ : Ty Γ}
       → Γ ∋ τ → (σ : Ty Γ) → (Γ ▹ σ) ∋ (τ / wk σ)

  data _⊢_ : (Γ : Ctx) → Ty Γ → Set where
    var : ∀ {Γ} {τ : Ty Γ}
        → Γ ∋ τ → Γ ⊢ τ
    ƛ : ∀ {Γ} {τ₁ : Ty Γ} {τ₂ : Ty (Γ ▹ τ₁)}
      → (Γ ▹ τ₁) ⊢ τ₂
      → Γ ⊢ Π τ₁ τ₂
    ap : ∀ {Γ} {τ₁ : Ty Γ} {τ₂ : Ty (Γ ▹ τ₁)}
       → Γ ⊢ Π τ₁ τ₂
       → (e2 : Γ ⊢ τ₁)
       → Γ ⊢ (τ₂ / (sub e2))
    _/⊢_ : ∀ {Γ Δ} {τ : Ty Γ}
         → Γ ⊢ τ
         → (ρ : Subst Γ Δ)
         → Δ ⊢ (τ / ρ)

  _/_ : ∀ {Γ Δ} → Ty Γ → Subst Γ Δ → Ty Δ
  ⋆ / ρ = ⋆
  Π τ₁ τ₂ / ρ = Π (τ₁ / ρ) (τ₂ / (ρ ↑ τ₁))
  El t / ρ = ⋆
