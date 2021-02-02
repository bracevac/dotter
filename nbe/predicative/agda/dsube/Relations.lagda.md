# Binary Relations

TODO : eventually migrate to the stdlib's rich binary relations module.

```agda
module dsube.Relations where

open import Data.Product using (_,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _≤′_; _<′_)
open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to _⊔ˡ_)
open import dsube.NbE

-- for cumulative definitions, it's simpler to use the ≤′ relation from Data.Nat,
-- which is useful for course-of-values induction over natural numbers.
open import Data.Nat.Properties using (≤′⇒≤; ≤⇒≤′; <-irrefl; ≤-pred; n<1+n; <-asym; <-trans)
open _≤′_

-- some facts about <′/≤′ which oddly are missing from the stdlib
<′-irrefl : ∀{x} → x <′ x → ⊥
<′-irrefl x<x = <-irrefl refl (≤′⇒≤ x<x)

<′-asym : ∀ {a b} → a <′ b → b <′ a → ⊥
<′-asym a<b b<a = <-asym (≤′⇒≤ a<b) (≤′⇒≤ b<a)

<′-trans : ∀ {a b c} → a <′ b → b <′ c → a <′ c
<′-trans a<b b<c = ≤⇒≤′ (<-trans (≤′⇒≤ a<b) (≤′⇒≤ b<c))

≤′-irrelevant : ∀ {x y} (a b : x ≤′ y) → a ≡ b
≤′-irrelevant _≤′_.≤′-refl _≤′_.≤′-refl = refl
≤′-irrelevant _≤′_.≤′-refl (_≤′_.≤′-step b) = ⊥-elim (<′-irrefl b)
≤′-irrelevant (_≤′_.≤′-step a) _≤′_.≤′-refl = ⊥-elim (<′-irrefl a)
≤′-irrelevant (_≤′_.≤′-step a) (_≤′_.≤′-step b) rewrite ≤′-irrelevant a b = refl

≤′-pred : ∀ {m n} → suc m ≤′ suc n → m ≤′ n
≤′-pred m+1≤n+1 = ≤⇒≤′ (≤-pred (≤′⇒≤ m+1≤n+1))

n<′1+n : ∀ n → n <′ suc n
n<′1+n n = ≤⇒≤′ (n<1+n n)

1+n≮′n : ∀ {n} → suc n <′ n → ⊥
1+n≮′n {n} = <′-asym (n<′1+n n)

open import Data.Nat using (_⊔_)
open import Data.Nat.Properties using (≤⇒≤′; ⊔-comm; m≤m⊔n; ≤′-trans)

m,n≤′m⊔n : ∀ m n → m ≤′ m ⊔ n × n ≤′ m ⊔ n
m,n≤′m⊔n m n = left , right
  where
    left : m ≤′ m ⊔ n
    left = ≤⇒≤′ (m≤m⊔n m n)
    right : n ≤′ m ⊔ n
    right rewrite ⊔-comm m n = ≤⇒≤′ (m≤m⊔n n m)

k,m,n≤′k⊔m⊔n : ∀ k m n → k ≤′ k ⊔ m ⊔ n × m ≤′ k ⊔ m ⊔ n × n ≤′ k ⊔ m ⊔ n
k,m,n≤′k⊔m⊔n k m n with m,n≤′m⊔n k m | m,n≤′m⊔n (k ⊔ m) n
... | k≤k⊔m , m≤k⊔m | k⊔m≤k⊔m⊔n , n≤k⊔m⊔n with ≤′-trans k≤k⊔m k⊔m≤k⊔m⊔n | ≤′-trans m≤k⊔m k⊔m≤k⊔m⊔n
... | k≤k⊔m⊔n | m≤k⊔m⊔n = k≤k⊔m⊔n , m≤k⊔m⊔n , n≤k⊔m⊔n

-- TODO it seems worthwhile using the stdlib's rich support for binary relations instead
-- of our own ad-hoc definitions
-- Binary relations over a type
Rel₂ : ∀{ℓ} → Set ℓ → Set (lsuc ℓ)
Rel₂ {ℓ} 𝓐  = 𝓐 → 𝓐 → Set ℓ

-- empty relation
⊥ᴿ : ∀ {T} → Rel₂ T
⊥ᴿ _ _ = ⊥

-- total relation
⊤ᴿ : ∀ {T} → Rel₂ T
⊤ᴿ _ _ = ⊤

-- Membership of an element in the domain of a given relation
data _∈_ {ℓ}{𝓐 : Set ℓ} (a : 𝓐) (R : Rel₂ 𝓐) : Set ℓ where
   memˡ : ∀{b} → R a b → a ∈ R
   memʳ : ∀{b} → R b a → a ∈ R

Refl : ∀{ℓ}{T : Set ℓ} → Rel₂ T → Set ℓ
Refl R = ∀{a} → R a a

Sym : ∀{ℓ}{T : Set ℓ} → Rel₂ T → Set ℓ
Sym R = ∀{a b} → R a b → R b a

Trans : ∀{ℓ}{T : Set ℓ} → Rel₂ T → Set ℓ
Trans R = ∀{a b c} → R a b → R b c → R a c

_∪_ : ∀{𝓐 : Set} → Rel₂ 𝓐 → Rel₂ 𝓐 → Rel₂ 𝓐
_∪_ R₁ R₂ a b = R₁ a b ⊎ R₂ a b

-- fancy notation for semantic equality
_==_∈_ : ∀{ℓ}{𝓐 : Set ℓ} → 𝓐 → 𝓐 → Rel₂ 𝓐 → Set ℓ
a == b ∈ R = R a b

-- entailment and equivalence of relations
_⊆_ :  ∀{ℓ}{𝓐 : Set ℓ} → Rel₂ 𝓐 → Rel₂ 𝓐 → Set ℓ
P ⊆ Q = ∀{a b} → P a b → Q a b

_≡ᴿ_ :  ∀{ℓ}{𝓐 : Set ℓ} → Rel₂ 𝓐 → Rel₂ 𝓐 → Set ℓ
P ≡ᴿ Q = P ⊆ Q × Q ⊆ P

≡→≡ᴿ : ∀{𝓐 : Set}{P Q : Rel₂ 𝓐} → P ≡ Q → P ≡ᴿ Q
≡→≡ᴿ refl = (λ z → z) , λ z → z

≡ᴿ-refl : ∀{𝓐 : Set}{R : Rel₂ 𝓐} → R ≡ᴿ R
≡ᴿ-refl {_} {R} = (λ x → x) , (λ x → x)

≡ᴿ-sym : ∀{𝓐 : Set}{R S : Rel₂ 𝓐} → R ≡ᴿ S → S ≡ᴿ R
≡ᴿ-sym (R⊆S , S⊆R) = S⊆R , R⊆S

≡ᴿ-trans : ∀{𝓐 : Set}{R Q S : Rel₂ 𝓐} → R ≡ᴿ Q → Q ≡ᴿ S → R ≡ᴿ S
≡ᴿ-trans (R⊆Q , Q⊆R) (Q⊆S , S⊆Q) = (λ x → Q⊆S (R⊆Q x)) , (λ x → Q⊆R (S⊆Q x))

≡ᴿ-∈ : ∀{𝓐 : Set}{R S : Rel₂ 𝓐} → R ≡ᴿ S → ∀{a b} → R a b → S a b
≡ᴿ-∈ (fst , _) = fst

-- The types of binary relations on our value domains
Rel = Rel₂ 𝕍
Rel' : ∀{ ℓ} → Set (lsuc ℓ)
Rel' {ℓ} = 𝕍 → 𝕍 → Set ℓ

Relᴺᶠ = Rel₂ 𝕍ᴺᶠ
Relᴺᵉ = Rel₂ 𝕍ᴺᵉ

⊆→∈ : ∀{ℓ}{𝓐 : Set ℓ}{R R' : Rel₂ 𝓐} → R ⊆ R' → ∀{a} → a ∈ R → a ∈ R'
⊆→∈ R⊆R' (memˡ x) = memˡ (R⊆R' x)
⊆→∈ R⊆R' (memʳ x) = memʳ (R⊆R' x)
```
