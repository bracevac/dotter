This file shows a way to define an unstratified object language in
intrinsically-typed and well-scoped style.

```agda
module dsube.Foo where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)

ℒ = ℕ -- universe levels of the object language


data Ctx : Set
data Class : Ctx → ℒ → Set
-- substitutions between contexts
data _⟹_ : Ctx → Ctx → Set
data _⊢_ : ∀{𝓁} → (Γ : Ctx) → Class Γ 𝓁 → Set
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
  ty : ∀{Γ} → (𝓁 : ℒ) → Class Γ 𝓁
  tm : ∀{Γ : Ctx}{𝓁} → Γ ⊢ (ty {Γ} 𝓁) → Class Γ 𝓁
```
## Examples:

The term `s (s z)` is of type `Nat`, i.e.,
    s (s z) : Γ ⊢ (tm Nat) with Nat : Γ ⊢ ty 0
However, at a higher level, Nat is a constant term, i.e.,
    ↟ Nat : Γ ⊢ (tm (Set 0)) with Set 0 : Γ ⊢ ty 1

What about type constructors? Assume we have in the object language a constant
    List :: Π (Set 0) (Set 0)
First, we have (Π (Set 0) (Set 0)) : Γ ⊢ ty 1.
Hence, we can assign List : Γ ⊢ tm (Π (Set 0) (Set 0)), which is a *term* in the universe Set 0.
Let's now construct the type of lists of natural numbers. Recall that Nat : Γ ⊢ ty 0.
By our application rule, we have to lift Nat to a term first, and then apply to List:
    List · ↟ Nat : Γ ⊢ tm ((Set 0) [ ↟ Nat ]) ≡ tm (Set 0)
However, we cannot use List · ↟ Nat in type positions, since it is a term. Thus, dually, we need
a lowering of terms at one level back into types of the lower level. Thus, we'd expect
    ↡ (List · ↟ Nat) : Γ ⊢ ty 0

Furthermore, we'd need some equality rules for lifting and lowering, e.g.,

    ↡ ↟ e ≡ e ∶ Set 𝓁

    ↟ ↡ e ≡ e : Set 𝓁

The explicit markings could be helpful in determining where to apply normalization.
```agda

data Ctx  where
  ∅   : Ctx
  _,_ : (Γ : Ctx) → ∀{𝓁} → Γ ⊢ (ty 𝓁) → Ctx

-- deBruijn index
data _∋_ : ∀{𝓁} → (Γ : Ctx) → Γ ⊢ (ty 𝓁) → Set

-- induce single substitution
[_] : ∀{Γ 𝓁}{S : Γ ⊢ (ty 𝓁)} → Γ ⊢ (tm S) → (Γ , S) ⟹ Γ

-- a predicative, dependently-typed λ-calculus with natural numbers
data _⊢_ where
  𝑆𝑒𝑡    : ∀{Γ} → (𝓁 : ℒ) → Γ ⊢ (ty (suc 𝓁))
  Nat   : ∀{Γ} → Γ ⊢ (ty 0)
  Π     : ∀{𝓁}{Γ} →
          (S : Γ ⊢ (ty 𝓁)) → (Γ , S) ⊢ (ty 𝓁) →
          --------------------------------------
          Γ ⊢ (ty 𝓁)
  `_    : ∀{Γ 𝓁}{T : Γ ⊢ (ty 𝓁)} →
          Γ ∋ T →
          Γ ⊢ (tm T) -- is it a term or type variable? matter of perspective, see next constructor
  -- Another insight: what is a type at one level, is a term at next level, which we model by the following:
  ↟     : ∀{𝓁}{Γ} → Γ ⊢ (ty 𝓁) → Γ ⊢ (tm (𝑆𝑒𝑡 𝓁))
  ↡     : ∀{𝓁}{Γ} → Γ ⊢ (tm (𝑆𝑒𝑡 𝓁)) → Γ ⊢ (ty 𝓁)
  z     : ∀{Γ} → Γ ⊢ (tm Nat)
  s     : ∀{Γ} → Γ ⊢ (tm Nat) → Γ ⊢ (tm Nat)
  ƛ     : ∀{Γ 𝓁}{S : Γ ⊢ (ty {Γ} 𝓁)}{T} →
         (Γ , S) ⊢ (tm T) →
         -------------------
         Γ ⊢ (tm (Π S T))
  _·ₛₜ_  : ∀{Γ Δ 𝓁} → Γ ⊢ (ty 𝓁) → (σ : Γ ⟹ Δ) → Δ ⊢ (ty 𝓁)                         -- apply subst to type
  _·ₛₜₘ_ : ∀{Γ Δ 𝓁}{T : Γ ⊢ (ty 𝓁)} → Γ ⊢ (tm T) → (σ : Γ ⟹ Δ) → Δ ⊢ (tm (T ·ₛₜ σ)) -- apply subst to term
  _·_   : ∀{Γ 𝓁}{S : Γ ⊢ (ty 𝓁)}{T} → -- apply lambda
         Γ ⊢ (tm (Π S T)) → (e : Γ ⊢ (tm S)) →
         --------------------------------------
         Γ ⊢ (tm (T ·ₛₜ [ e ] ))

data _⟹_ where
  Id   : ∀{Γ} → Γ ⟹ Γ
  ↑    : ∀{Γ 𝓁}{T : Γ ⊢ (ty 𝓁)} → Γ ⟹ (Γ , T)
  _,ₛ_ : ∀{Γ Δ} → (σ : Γ ⟹ Δ) → ∀{𝓁}{T : Γ ⊢ (ty 𝓁)} → Δ ⊢ (tm (T ·ₛₜ σ)) → (Γ , T) ⟹ Δ
  _∘ₛ_ : ∀{Γ Δ Ψ} → Δ ⟹ Γ → Ψ ⟹ Δ → Ψ ⟹ Γ

-- Important insight from studying extrinsic formulations: we should apply the weakening subst ↑
-- to the RHS of the deBruijn variable, which is at the same time the lookup.
-- This makes it also easier to work with types which depend on a proper prefix of Γ.
data _∋_ where
  Z : ∀{Γ 𝓁}{T : Γ ⊢ (ty 𝓁)} → (Γ , T) ∋ (T ·ₛₜ ↑)
  S : ∀{Γ 𝓁 𝓀}{S : Γ ⊢ (ty 𝓁)}{T : Γ ⊢ (ty 𝓀)} → Γ ∋ S → (Γ , T) ∋ (S ·ₛₜ ↑)

-- TODO impl of [_]

-- this won't type check in Agda at the moment, because it doesn't know that Nat = (Nat ·ₛ Id),
-- a drawback of first-order substitutions.
-- σ = Id ,ₛ z
