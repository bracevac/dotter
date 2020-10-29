# Completeness of Normalization by Evaluation for Dᵉ<:>

We prove completeness with a partial equivalence (PER) model.
Completeness means that whatever terms are βη-equal in the Dᵉ<:> system,
so will be their normal forms in the PER model of equality (and their NFs exist!)

It seems sufficient to use this result to conclude termination of NbE,
for the special case of relating a well-typed expression to itself.


```agda
module dsube.Completeness3 where

open import Data.Bool using (true; false)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax; _,_; _×_)
open Σ
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _≤′_; _<′_)
open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to _⊔ˡ_)
open import dsube.NbE

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
data _∈_ {𝓐 : Set} (a : 𝓐) (R : Rel₂ 𝓐) : Set where
   memˡ : ∀{b} → R a b → a ∈ R
   memʳ : ∀{b} → R b a → a ∈ R

_∪_ : ∀{𝓐 : Set} → Rel₂ 𝓐 → Rel₂ 𝓐 → Rel₂ 𝓐
_∪_ R₁ R₂ a b = R₁ a b ⊎ R₂ a b

-- fancy notation for semantic equality
_==_∈_ : ∀{𝓐 : Set} → 𝓐 → 𝓐 → Rel₂ 𝓐 → Set
a == b ∈ R = R a b

-- entailment and equivalence of relations
_⊆_ :  ∀{𝓐 : Set} → Rel₂ 𝓐 → Rel₂ 𝓐 → Set
P ⊆ Q = ∀{a b} → P a b → Q a b

_≡ᴿ_ :  ∀{𝓐 : Set} → Rel₂ 𝓐 → Rel₂ 𝓐 → Set
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
Relᴺᶠ = Rel₂ 𝕍ᴺᶠ
Relᴺᵉ = Rel₂ 𝕍ᴺᵉ

-- a partial equivalence relation (PER) is an equivalence relation on its domain
record Per {𝓐} (R : Rel₂ 𝓐) : Set where
  field -- TODO better add 𝓐 and R as fields and have Per non-parameterized?
    per-sym   : ∀ {a a'} → R a a' → R a' a
    per-trans : ∀ {a b c} → R a b → R b c → R a c
open Per {{...}}

per-refl : ∀{𝓐}{R : Rel₂ 𝓐} → {{Per R}} → ∀ {a} → a ∈ R → R a a
per-refl (memˡ x) = per-trans x (per-sym x)
per-refl (memʳ x) = per-trans (per-sym x) x


-- these are the top and bottom elements of what Abel dubs a "candidate space".
-- our semantics for equality at the various types lives in the space between these sets
-- that is, 𝓑𝓸𝓽 ⊆ ⟦ T ⟧ ⊆ 𝓣𝓸𝓹
-- roughly, we will show that Γ ⊢ e₁ ≈ e₂ ∶ T → ⟦e₁⟧ == ⟦e₂⟧ ∈ ⟦ T ⟧
-- there is a bit more structure needed for dependent types, but that is the high-level intuition
𝓣𝓸𝓹 : Relᴺᶠ
𝓣𝓸𝓹 v₁ v₂ = ∀ n → ∃[ eᴺᶠ ]( ℜᴺᶠ⟨ n ⟩ v₁ ⇓ eᴺᶠ × ℜᴺᶠ⟨ n ⟩ v₂ ⇓ eᴺᶠ )

𝓑𝓸𝓽 : Relᴺᵉ
𝓑𝓸𝓽 nv₁ nv₂ = ∀ n → ∃[ eᴺᵉ ]( ℜᴺᵉ⟨ n ⟩ nv₁ ⇓ eᴺᵉ × ℜᴺᵉ⟨ n ⟩ nv₂ ⇓ eᴺᵉ )

--- Bot and Top are PERs
instance Per-𝓣𝓸𝓹 : Per 𝓣𝓸𝓹
per-sym   {{Per-𝓣𝓸𝓹}} Taa' n with Taa' n
... | eᴺᶠ , fst , snd = eᴺᶠ , snd , fst
per-trans {{Per-𝓣𝓸𝓹}} Tab Tbc n  with Tab n | Tbc n
... | eab , fst , snd | ebc , fst₁ , snd₁ rewrite is-fun-ℜᴺᶠ snd fst₁ = ebc , fst , snd₁

instance Per-𝓑𝓸𝓽 : Per 𝓑𝓸𝓽
per-sym   {{Per-𝓑𝓸𝓽}} Botaa' n with Botaa' n
... | x , fst , snd = x , snd , fst
per-trans {{Per-𝓑𝓸𝓽}} Botab Botbc n with Botab n | Botbc n
... | x , fst , snd | y , fst₁ , snd₁ rewrite is-fun-ℜᴺᵉ snd fst₁ = y , fst , snd₁

-- TODO show that 𝓑𝓸𝓽 ⊆ 𝓣𝓸𝓹 → 𝓑𝓸𝓽, 𝓑𝓸𝓽 → 𝓣𝓸𝓹 ⊆ 𝓣𝓸𝓹 for the semantic function spaces
-- This is a bit hand-wavy, since  𝓑𝓸𝓽 and 𝓣𝓸𝓹 are relations over different kinds of domains
-- (neutral values, normal form values), which in turn are different from the values domain.
-- So it's not clear how to define the notions of ⊆ and → between them.

-- TODO show the various implications analogous to Abel'13, p.32, stemming from the
-- cases of the read-back functions

data 𝓝𝓪𝓽 : Rel where
  𝓝-𝑛 : ∀{n} →
        -------------------------------
        (ᶜ (V𝑛 n)) == (ᶜ (V𝑛 n)) ∈ 𝓝𝓪𝓽

  𝓝-Ne : ∀{nv nv'} →
        nv == nv' ∈ 𝓑𝓸𝓽 →
        -----------------------------------
        ↑⟨ ᶜ V𝑁 ⟩ nv == ↑⟨ ᶜ V𝑁 ⟩ nv' ∈ 𝓝𝓪𝓽

instance Per-𝓝𝓪𝓽 : Per 𝓝𝓪𝓽
per-sym   {{Per-𝓝𝓪𝓽}} 𝓝-𝑛 = 𝓝-𝑛
per-sym   {{Per-𝓝𝓪𝓽}} (𝓝-Ne x) = 𝓝-Ne (per-sym x)
per-trans {{Per-𝓝𝓪𝓽}} 𝓝-𝑛 𝓝-𝑛 = 𝓝-𝑛
per-trans {{Per-𝓝𝓪𝓽}} (𝓝-Ne x) (𝓝-Ne x₁) = 𝓝-Ne (per-trans x x₁)

open import dsube.Syntax using (ℒ)

-- Neutral type interp -- TODO not sure about the definition: this is one of the very hand-wavy places in thesis
data 𝓥Ty-Ne (𝓁 : ℒ) (NE : 𝕍ᴺᵉ) : Rel where
  𝓥Ty-Ne-mem : ∀ {NE₁ ne₁ NE₂ ne₂} →
    NE == NE₁ ∈ 𝓑𝓸𝓽 →
    NE == NE₂ ∈ 𝓑𝓸𝓽 →
    ne₁ == ne₂ ∈ 𝓑𝓸𝓽 →
    -------------------------------------------------------------------------------
    ↑⟨ (↑⟨ (ᶜ (V𝑆𝑒𝑡 𝓁)) ⟩ NE₁) ⟩ ne₁ == ↑⟨ (↑⟨ (ᶜ (V𝑆𝑒𝑡 𝓁)) ⟩ NE₂) ⟩ ne₂ ∈ (𝓥Ty-Ne 𝓁 NE)

instance Per-𝓥Ty-Ne : ∀{𝓁 NE} → Per (𝓥Ty-Ne 𝓁 NE)
per-sym   {{Per-𝓥Ty-Ne}} (𝓥Ty-Ne-mem x x₁ x₂) = 𝓥Ty-Ne-mem x₁ x (per-sym x₂)
per-trans {{Per-𝓥Ty-Ne}} (𝓥Ty-Ne-mem x x₁ x₂) (𝓥Ty-Ne-mem y y₁ y₂) = 𝓥Ty-Ne-mem x y₁ (per-trans x₂ y₂)

-- ⊥ type interp
-- TODO not sure either, but to fulfill the candidate space requirement, V⊥ cannot be empty
-- it appears reasonable to take the total relation, as interpreting a term at type V⊥ logically
-- implies arbitrary things
𝓥⊥ : Rel
𝓥⊥ _ _ = ⊤

instance Per-𝓥⊥ : Per 𝓥⊥
per-sym   {{Per-𝓥⊥}} _   = tt
per-trans {{Per-𝓥⊥}} _ _ = tt

-- ⊤ type interp
data 𝓥⊤ : Rel where
  𝓥⊤-ne :  ∀{nv nv'} →
    nv == nv' ∈ 𝓑𝓸𝓽 →
    -----------------------------------
    ↑⟨ ᶜ V⊤ ⟩ nv == ↑⟨ ᶜ V⊤ ⟩ nv' ∈ 𝓥⊤

  𝓥⊤-val : ∀ {v} →
    ---------------
    v == v ∈ 𝓥⊤

instance Per-𝓥⊤ : Per 𝓥⊤
per-sym   {{Per-𝓥⊤}} (𝓥⊤-ne x) = 𝓥⊤-ne (per-sym x)
per-sym   {{Per-𝓥⊤}} 𝓥⊤-val = 𝓥⊤-val
per-trans {{Per-𝓥⊤}} (𝓥⊤-ne x) (𝓥⊤-ne x₁) = 𝓥⊤-ne (per-trans x x₁)
per-trans {{Per-𝓥⊤}} (𝓥⊤-ne x) 𝓥⊤-val = 𝓥⊤-ne x
per-trans {{Per-𝓥⊤}} 𝓥⊤-val b = b

-- abstract type interp
data 𝓥Type (𝓣₁ : Rel) (𝓣₂ : Rel) : Rel where
  𝓥Type-ne : ∀ {𝑆 𝑆' 𝑇 𝑇' NE NE'} →
          𝑆 == 𝑆' ∈ 𝓣₁ →
          𝑇 == 𝑇' ∈ 𝓣₂ →
          NE == NE' ∈ 𝓑𝓸𝓽 →
          ----------------------------------------------------------------
          ↑⟨ ⟪Type 𝑆 ⋯ 𝑇 ⟫ ⟩ NE == ↑⟨ ⟪Type 𝑆' ⋯ 𝑇' ⟫ ⟩ NE' ∈ 𝓥Type 𝓣₁ 𝓣₂

  𝓥Type-val : ∀ {𝐴 𝐴'} →
          𝐴 == 𝐴' ∈ 𝓣₁ →
          𝐴 == 𝐴' ∈ 𝓣₂ →
          ---------------------------------------
          (VType 𝐴) == (VType 𝐴') ∈ 𝓥Type 𝓣₁ 𝓣₂

instance Per-𝓥Type : ∀{𝓢 𝓣 : Rel} → {{Per 𝓢}} → {{Per 𝓣}} → Per (𝓥Type 𝓢 𝓣)
per-sym   {{Per-𝓥Type}} (𝓥Type-ne x x₁ x₂) = 𝓥Type-ne (per-sym x) (per-sym x₁) (per-sym x₂)
per-sym   {{Per-𝓥Type}} (𝓥Type-val x x₁)   = 𝓥Type-val (per-sym x) (per-sym x₁)
per-trans {{Per-𝓥Type}} (𝓥Type-ne x x₁ x₂) (𝓥Type-ne x₃ x₄ x₅) =
  𝓥Type-ne (per-trans x x₃) (per-trans x₁ x₄) (per-trans x₂ x₅)
per-trans {{Per-𝓥Type}} (𝓥Type-val x x₁) (𝓥Type-val x₂ x₃) =
  𝓥Type-val (per-trans x x₂) (per-trans x₁ x₃)

-- An extension function over a binary relation
-- A function that maps the given relation's elements A==A' pointwise to a relation.
_⟾Rel₂ : {T : Set} → Rel₂ T → Set₁
_⟾Rel₂ {T} R = ∀ {𝐴 : T} → ∀ {𝐴' : T} → R 𝐴 𝐴' → Rel₂ T

-- Dependent function space between relations
𝓟𝓲 : (𝓐 : Rel) → 𝓐 ⟾Rel₂ → Rel
𝓟𝓲 𝓐 𝓕 𝑓 𝑓' =  ∀{𝑎 𝑎'} → (a==a' : 𝑎 == 𝑎' ∈ 𝓐) →
       ∃[ 𝑏 ] ∃[ 𝑏' ] ( (𝑓 · 𝑎 ⇓ 𝑏) × (𝑓' · 𝑎' ⇓ 𝑏') × (𝑏 == 𝑏' ∈ (𝓕 a==a') ) )

-- Non-dependent function space between relations
_⟹_ :  (𝓐 : Rel) → (𝓑 : Rel) → Rel
_⟹_ 𝓐 𝓑 = 𝓟𝓲 𝓐 (λ _ → 𝓑)

infixr 21 _⟹_

data 𝓢𝓮𝓽₀ : Rel
𝓔𝓵₀ : 𝓢𝓮𝓽₀ ⟾Rel₂

data 𝓢𝓮𝓽₀ where
  𝓢𝓮𝓽₀-NE : ∀{NE NE'} →
    NE == NE' ∈ 𝓑𝓸𝓽 →
    -------------------------------------------------
    ↑⟨ (ᶜ (V𝑆𝑒𝑡 0)) ⟩ NE == ↑⟨ (ᶜ (V𝑆𝑒𝑡 0)) ⟩ NE' ∈ 𝓢𝓮𝓽₀

  𝓢𝓮𝓽₀-𝑁 : (ᶜ V𝑁) == (ᶜ V𝑁) ∈ 𝓢𝓮𝓽₀

  𝓢𝓮𝓽₀-⊤ : (ᶜ V⊤) == (ᶜ V⊤) ∈ 𝓢𝓮𝓽₀

  𝓢𝓮𝓽₀-⊥ : (ᶜ V⊥) == (ᶜ V⊥) ∈ 𝓢𝓮𝓽₀

  𝓢𝓮𝓽₀-Π : ∀{𝐴 𝐴' 𝐹 𝐹'} →
    (A==A' : 𝐴 == 𝐴' ∈ 𝓢𝓮𝓽₀) →
    𝐹 == 𝐹' ∈ (𝓔𝓵₀ A==A') ⟹ 𝓢𝓮𝓽₀ →
    -----------------------------------------------------------------------------------
    VΠ 𝐴 𝐹 == VΠ 𝐴' 𝐹' ∈ 𝓢𝓮𝓽₀

-- turns out it is important to index the function by the inductive type, see below
-- not only do we rule out impossible cases, which we beforehand defined by the empty relation
-- but the interpretation if Π types crucially depends on information from the 𝓢𝓮𝓽₀-Π constructor.
𝓔𝓵₀ {↑⟨ ᶜ V𝑆𝑒𝑡 0 ⟩ NE} _ = 𝓥Ty-Ne 0 NE
𝓔𝓵₀ {ᶜ V𝑁} _ = 𝓝𝓪𝓽
𝓔𝓵₀ {ᶜ V⊤} _ = 𝓥⊤
𝓔𝓵₀ {ᶜ V⊥} _ = 𝓥⊥
-- I would like to abstract the nested projections into something more readable, but the types are killing me
𝓔𝓵₀ {VΠ 𝐴 𝐹} (𝓢𝓮𝓽₀-Π 𝐴==𝐴' 𝐹==𝐹') =
  𝓟𝓲 (𝓔𝓵₀ 𝐴==𝐴') λ 𝑎==𝑎' → 𝓔𝓵₀ (proj₂ (proj₂ (proj₂ (proj₂ (𝐹==𝐹' 𝑎==𝑎')))))

data 𝓢𝓮𝓽ₖ₊₁ {𝓀 : ℒ} {𝓢ₖ : Rel} {𝓔𝓵ₖ : 𝓢ₖ ⟾Rel₂} : Rel
𝓔𝓵ₖ₊₁ : {𝓀 : ℒ} → {𝓢ₖ : Rel} → {𝓔𝓵ₖ : 𝓢ₖ ⟾Rel₂} → (𝓢𝓮𝓽ₖ₊₁ {𝓀} {𝓢ₖ} {𝓔𝓵ₖ}) ⟾Rel₂

data 𝓢𝓮𝓽ₖ₊₁ {𝓀} {𝓢ₖ} {𝓔𝓵ₖ} where
  𝓢𝓮𝓽ₖ₊₁-NE : ∀{NE NE'} →
    NE == NE' ∈ 𝓑𝓸𝓽 →
    ------------------------------------------------------------------------
    ↑⟨ (ᶜ (V𝑆𝑒𝑡 (suc 𝓀))) ⟩ NE == ↑⟨ (ᶜ (V𝑆𝑒𝑡 (suc 𝓀))) ⟩ NE' ∈ 𝓢𝓮𝓽ₖ₊₁

  -- TODO via cumulativity, we could get rid of the following three rules in 𝓢𝓮𝓽ₖ₊₁
  𝓢𝓮𝓽ₖ₊₁-𝑁 : (ᶜ V𝑁) == (ᶜ V𝑁) ∈ 𝓢𝓮𝓽ₖ₊₁

  𝓢𝓮𝓽ₖ₊₁-⊤ : (ᶜ V⊤) == (ᶜ V⊤) ∈ 𝓢𝓮𝓽ₖ₊₁

  𝓢𝓮𝓽ₖ₊₁-⊥ : (ᶜ V⊥) == (ᶜ V⊥) ∈ 𝓢𝓮𝓽ₖ₊₁

  𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ : ∀{𝐴 𝐵} →
    𝐴 == 𝐵 ∈ 𝓢ₖ →
    --------------------
    𝐴 == 𝐵 ∈ 𝓢𝓮𝓽ₖ₊₁

  𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ : ∀{𝑆 𝑆' 𝑇 𝑇'} →
    𝑆 == 𝑆' ∈ 𝓢ₖ →
    𝑇 == 𝑇' ∈ 𝓢ₖ →
    ------------------------------------------
    ⟪Type 𝑆 ⋯ 𝑇 ⟫ == ⟪Type 𝑆' ⋯ 𝑇' ⟫ ∈ 𝓢𝓮𝓽ₖ₊₁

  𝓢𝓮𝓽ₖ₊₁-𝓢𝓮𝓽ₖ :
    (ᶜ (V𝑆𝑒𝑡 𝓀)) == (ᶜ (V𝑆𝑒𝑡 𝓀)) ∈ 𝓢𝓮𝓽ₖ₊₁

  𝓢𝓮𝓽ₖ₊₁-Π : ∀{𝐴 𝐴' 𝐹 𝐹'} →
    (A==A' : 𝐴 == 𝐴' ∈ 𝓢𝓮𝓽ₖ₊₁ {𝓀} {𝓢ₖ} {𝓔𝓵ₖ}) →
    𝐹 == 𝐹' ∈ (𝓔𝓵ₖ₊₁ A==A') ⟹ 𝓢𝓮𝓽ₖ₊₁ {𝓀} {𝓢ₖ} {𝓔𝓵ₖ} →
    ----------------------------------------------------------------------------------------------------
    VΠ 𝐴 𝐹 == VΠ 𝐴' 𝐹' ∈ 𝓢𝓮𝓽ₖ₊₁

𝓔𝓵ₖ₊₁ {𝓀} (𝓢𝓮𝓽ₖ₊₁-NE {NE} _) = 𝓥Ty-Ne (suc 𝓀) NE
𝓔𝓵ₖ₊₁ 𝓢𝓮𝓽ₖ₊₁-𝑁 = 𝓝𝓪𝓽
𝓔𝓵ₖ₊₁ 𝓢𝓮𝓽ₖ₊₁-⊤ = 𝓥⊤
𝓔𝓵ₖ₊₁ 𝓢𝓮𝓽ₖ₊₁-⊥ = 𝓥⊥
𝓔𝓵ₖ₊₁ {_} {_} {𝓔𝓵ₖ} (𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ A==A') = 𝓔𝓵ₖ A==A'
𝓔𝓵ₖ₊₁ {_} {_} {𝓔𝓵ₖ} (𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ S==S' T==T') = 𝓥Type (𝓔𝓵ₖ S==S') (𝓔𝓵ₖ T==T')
𝓔𝓵ₖ₊₁ {_} {𝓢ₖ} (𝓢𝓮𝓽ₖ₊₁-𝓢𝓮𝓽ₖ) = 𝓢ₖ
𝓔𝓵ₖ₊₁ {_} {_} {_} {VΠ 𝐴 𝐹} (𝓢𝓮𝓽ₖ₊₁-Π 𝐴==𝐴' 𝐹==𝐹') =
  𝓟𝓲 (𝓔𝓵ₖ₊₁ 𝐴==𝐴') λ 𝑎==𝑎' → 𝓔𝓵ₖ₊₁ (proj₂ (proj₂ (proj₂ (proj₂ (𝐹==𝐹' 𝑎==𝑎') ))))

𝓢𝓮𝓽 : ℒ → Rel
𝓔𝓵 : (𝓀 : ℒ) → (𝓢𝓮𝓽 𝓀) ⟾Rel₂

𝓢𝓮𝓽 0 = 𝓢𝓮𝓽₀
𝓢𝓮𝓽 (suc 𝓀) = 𝓢𝓮𝓽ₖ₊₁ {𝓀} {𝓢𝓮𝓽 𝓀} {𝓔𝓵 𝓀}

𝓔𝓵 0 = 𝓔𝓵₀
𝓔𝓵 (suc 𝓀) = 𝓔𝓵ₖ₊₁ {𝓀} {𝓢𝓮𝓽 𝓀} {𝓔𝓵 𝓀}

-- TODO It might also be beneficial if we had proper inversion lemmas + induction principle for these
𝓢𝓮𝓽-NE : ∀{𝓀 NE NE'} →
  NE == NE' ∈ 𝓑𝓸𝓽 →
  --------------------------------------------------
  ↑⟨ (ᶜ (V𝑆𝑒𝑡 𝓀)) ⟩ NE == ↑⟨ (ᶜ (V𝑆𝑒𝑡 𝓀)) ⟩ NE' ∈ 𝓢𝓮𝓽 𝓀

𝓢𝓮𝓽-NE {zero} = 𝓢𝓮𝓽₀-NE
𝓢𝓮𝓽-NE {suc 𝓀} = 𝓢𝓮𝓽ₖ₊₁-NE

𝓢𝓮𝓽-𝑁 : ∀{𝓀} → (ᶜ V𝑁) == (ᶜ V𝑁) ∈ 𝓢𝓮𝓽 𝓀
𝓢𝓮𝓽-𝑁 {zero} = 𝓢𝓮𝓽₀-𝑁
𝓢𝓮𝓽-𝑁 {suc 𝓀} = 𝓢𝓮𝓽ₖ₊₁-𝑁

𝓢𝓮𝓽-⊤ : ∀{𝓀} → (ᶜ V⊤) == (ᶜ V⊤) ∈ 𝓢𝓮𝓽 𝓀
𝓢𝓮𝓽-⊤ {zero} = 𝓢𝓮𝓽₀-⊤
𝓢𝓮𝓽-⊤ {suc 𝓀} = 𝓢𝓮𝓽ₖ₊₁-⊤

𝓢𝓮𝓽-⊥ : ∀{𝓀} → (ᶜ V⊥) == (ᶜ V⊥) ∈ 𝓢𝓮𝓽 𝓀
𝓢𝓮𝓽-⊥ {zero} = 𝓢𝓮𝓽₀-⊥
𝓢𝓮𝓽-⊥ {suc 𝓀} = 𝓢𝓮𝓽ₖ₊₁-⊥

𝓢𝓮𝓽-⟪Type⋯⟫ : ∀{𝓀 𝑆 𝑆' 𝑇 𝑇'} →
  𝑆 == 𝑆' ∈ 𝓢𝓮𝓽 𝓀 →
  𝑇 == 𝑇' ∈ 𝓢𝓮𝓽 𝓀 →
  -----------------------------------------------
  ⟪Type 𝑆 ⋯ 𝑇 ⟫ == ⟪Type 𝑆' ⋯ 𝑇' ⟫ ∈ 𝓢𝓮𝓽 (suc 𝓀)

𝓢𝓮𝓽-⟪Type⋯⟫ 𝑆==𝑆' 𝑇==𝑇' = 𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ 𝑆==𝑆' 𝑇==𝑇'

open import Data.Nat.Properties using (<-irrefl; ≤′⇒≤)
open _≤′_
𝓢𝓮𝓽ₗ∈𝓢𝓮𝓽ₖ : ∀{𝓁 𝓀} → 𝓁 <′ 𝓀 → (ᶜ (V𝑆𝑒𝑡 𝓁)) == (ᶜ (V𝑆𝑒𝑡 𝓁)) ∈ 𝓢𝓮𝓽 𝓀
𝓢𝓮𝓽ₗ∈𝓢𝓮𝓽ₖ {𝓁} {.(suc 𝓁)} ≤′-refl = 𝓢𝓮𝓽ₖ₊₁-𝓢𝓮𝓽ₖ
𝓢𝓮𝓽ₗ∈𝓢𝓮𝓽ₖ {𝓁} {.(suc _)} (≤′-step 𝓁<𝓀) = 𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ (𝓢𝓮𝓽ₗ∈𝓢𝓮𝓽ₖ 𝓁<𝓀)

𝓢𝓮𝓽-Π : ∀{𝓀 𝐴 𝐴' 𝐹 𝐹'} →
  (A==A' : 𝐴 == 𝐴' ∈ 𝓢𝓮𝓽 𝓀) →
  𝐹 == 𝐹' ∈ (𝓔𝓵 𝓀 A==A') ⟹ 𝓢𝓮𝓽 𝓀 →
  -------------------------------------------------------------------------------------
  VΠ 𝐴 𝐹 == VΠ 𝐴' 𝐹' ∈ 𝓢𝓮𝓽 𝓀

𝓢𝓮𝓽-Π {zero} = 𝓢𝓮𝓽₀-Π
𝓢𝓮𝓽-Π {suc 𝓀} = 𝓢𝓮𝓽ₖ₊₁-Π

-- restricting the domain of the 𝓔𝓵 functions makes the proofs (and formulation) of the equations a bit more involved
𝓔𝓵-𝑁 : ∀ {𝓀 x y} → 𝓔𝓵 𝓀 {ᶜ V𝑁} {x} y ≡ 𝓝𝓪𝓽 -- on the bright side, we can use the stronger notion of prop. eq.
𝓔𝓵-𝑁 {zero} = refl
𝓔𝓵-𝑁 {suc 𝓀} {_} {𝓢𝓮𝓽ₖ₊₁-𝑁} = refl
𝓔𝓵-𝑁 {suc 𝓀} {_} {𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ x} = 𝓔𝓵-𝑁 {𝓀}

𝓔𝓵-⊤ : ∀ {𝓀 x y} → 𝓔𝓵 𝓀 {ᶜ V⊤} {x} y ≡ 𝓥⊤
𝓔𝓵-⊤ {zero} = refl
𝓔𝓵-⊤ {suc 𝓀} {_} {𝓢𝓮𝓽ₖ₊₁-⊤} = refl
𝓔𝓵-⊤ {suc 𝓀} {_} {𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ x} = 𝓔𝓵-⊤ {𝓀}

𝓔𝓵-⊥ : ∀ {𝓀 x y} → 𝓔𝓵 𝓀 {ᶜ V⊥} {x} y ≡ 𝓥⊥
𝓔𝓵-⊥ {zero} = refl
𝓔𝓵-⊥ {suc 𝓀} {_} {𝓢𝓮𝓽ₖ₊₁-⊥} = refl
𝓔𝓵-⊥ {suc 𝓀} {_} {𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ x} = 𝓔𝓵-⊥ {𝓀}

predicativity : ∀{𝓁 x} → (ᶜ (V𝑆𝑒𝑡 𝓁)) == x ∈ 𝓢𝓮𝓽 𝓁 → ⊥

𝓔𝓵-𝑆𝑒𝑡 : ∀ {𝓁 𝓀 x y} → 𝓁 <′ 𝓀 → 𝓔𝓵 𝓀 {ᶜ (V𝑆𝑒𝑡 𝓁)} {x} y ≡ 𝓢𝓮𝓽 𝓁
𝓔𝓵-𝑆𝑒𝑡 {𝓁} {.(suc 𝓁)} {x} {𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ x₁} ≤′-refl = ⊥-elim (predicativity x₁)
𝓔𝓵-𝑆𝑒𝑡 {𝓁} {.(suc 𝓁)} {.(ᶜ V𝑆𝑒𝑡 𝓁)} {𝓢𝓮𝓽ₖ₊₁-𝓢𝓮𝓽ₖ} ≤′-refl = refl
𝓔𝓵-𝑆𝑒𝑡 {𝓁} {suc 𝓀'} {x} {𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ x₁} (≤′-step 𝓁<𝓀') with 𝓔𝓵-𝑆𝑒𝑡 {_} {_} {x} {x₁} 𝓁<𝓀'
... | z = z
𝓔𝓵-𝑆𝑒𝑡 {.𝓀'} {suc 𝓀'} {.(ᶜ V𝑆𝑒𝑡 𝓀')} {𝓢𝓮𝓽ₖ₊₁-𝓢𝓮𝓽ₖ} (≤′-step 𝓁<𝓀') = refl

𝓔𝓵-⟪Type⋯⟫ : ∀ {𝓀 𝑆 𝑆' 𝑇 𝑇' S==S' T==T'} →
  𝓔𝓵 (suc 𝓀) {⟪Type 𝑆 ⋯ 𝑇 ⟫} (𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ {_} {_} {_} {_} {𝑆'} {_} {𝑇'} S==S' T==T') ≡ 𝓥Type (𝓔𝓵 𝓀 S==S') (𝓔𝓵 𝓀 T==T')
𝓔𝓵-⟪Type⋯⟫ = refl

𝓢𝓮𝓽-NE¬suc : ∀ {𝓀 𝓁 NE x} → 𝓀 <′ 𝓁 →  ↑⟨ ᶜ V𝑆𝑒𝑡 𝓁 ⟩ NE == x ∈ 𝓢𝓮𝓽 𝓀 → ⊥ -- TODO better name for thm
𝓢𝓮𝓽-NE¬suc {zero} ≤′-refl = λ ()
𝓢𝓮𝓽-NE¬suc {zero} (≤′-step 0<l) = λ ()
𝓢𝓮𝓽-NE¬suc {suc 𝓀} ≤′-refl (𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ x) = 𝓢𝓮𝓽-NE¬suc (≤′-step ≤′-refl) x
𝓢𝓮𝓽-NE¬suc {suc 𝓀} (≤′-step k+1<l) (𝓢𝓮𝓽ₖ₊₁-NE x) = {!!} -- TODO boring low-level stuff about inequalities
𝓢𝓮𝓽-NE¬suc {suc 𝓀} (≤′-step k+1<l) (𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ x) = {!!}

𝓔𝓵-NE : ∀ {𝓀 NE x y} → 𝓔𝓵 𝓀 {↑⟨ (ᶜ (V𝑆𝑒𝑡 𝓀)) ⟩ NE} {x} y ≡ 𝓥Ty-Ne 𝓀 NE
𝓔𝓵-NE {zero} = refl
𝓔𝓵-NE {suc 𝓀} {_} {.(↑⟨ ᶜ V𝑆𝑒𝑡 (suc 𝓀) ⟩ _)} {𝓢𝓮𝓽ₖ₊₁-NE _} = refl
𝓔𝓵-NE {(suc 𝓀)} {_} {x} {𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ x₁} = ⊥-elim (𝓢𝓮𝓽-NE¬suc ≤′-refl x₁)

-- Another litmus test
open import Data.Nat.Properties using (≤′-trans)
Set𝓁∈Set𝓀→𝓁<𝓀 : ∀{𝓀 𝓁} → (ᶜ (V𝑆𝑒𝑡 𝓁)) == (ᶜ (V𝑆𝑒𝑡 𝓁)) ∈ 𝓢𝓮𝓽 𝓀 → 𝓁 <′ 𝓀
Set𝓁∈Set𝓀→𝓁<𝓀 {suc 𝓀} {𝓁} (𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ x) with Set𝓁∈Set𝓀→𝓁<𝓀 x
... | y = ≤′-trans y (≤′-step ≤′-refl)
Set𝓁∈Set𝓀→𝓁<𝓀 {suc 𝓀} {.𝓀} 𝓢𝓮𝓽ₖ₊₁-𝓢𝓮𝓽ₖ = ≤′-refl

𝓁<𝓀→Set𝓁∈Set𝓀 : ∀{𝓀 𝓁} → 𝓁 <′ 𝓀 → (ᶜ (V𝑆𝑒𝑡 𝓁)) == (ᶜ (V𝑆𝑒𝑡 𝓁)) ∈ 𝓢𝓮𝓽 𝓀
𝓁<𝓀→Set𝓁∈Set𝓀 {.(suc 𝓁)} {𝓁} ≤′-refl = 𝓢𝓮𝓽ₖ₊₁-𝓢𝓮𝓽ₖ
𝓁<𝓀→Set𝓁∈Set𝓀 {.(suc _)} {𝓁} (≤′-step 𝓁<𝓀) = 𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ (𝓁<𝓀→Set𝓁∈Set𝓀 𝓁<𝓀)

predicativity {suc 𝓁} {Vƛ x x₁} (𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ x₂) = {!!}
predicativity {_} {ᶜ x} foo = {!!}
predicativity {_} {VΠ x x₁} foo = {!!}
predicativity {_} {⟪Type x ⋯ x₁ ⟫} foo = {!!}
predicativity {_} {VType x} foo = {!!}
predicativity {_} {↑⟨ x ⟩ x₁} foo = {!!}
--predicativity Set𝓁∈Set𝓁 = ⊥-elim (<-irrefl refl (≤′⇒≤ (Set𝓁∈Set𝓀→𝓁<𝓀 Set𝓁∈Set𝓁)))

cumulativity : ∀{𝓁 𝓀} → 𝓁 ≤′ 𝓀 → 𝓢𝓮𝓽 𝓁 ⊆ 𝓢𝓮𝓽 𝓀
cumulativity {𝓁} {.𝓁} ≤′-refl a==b∈𝓢𝓮𝓽𝓁 = a==b∈𝓢𝓮𝓽𝓁
cumulativity {𝓁} {(suc 𝓀')} (≤′-step 𝓁<𝓀') a==b∈𝓢𝓮𝓽𝓁 with cumulativity 𝓁<𝓀'
... | Set𝓁⊆Set𝓀' = 𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ (Set𝓁⊆Set𝓀' a==b∈𝓢𝓮𝓽𝓁)
-- we make our live easy with the extra constructor 𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ, which is not present in Abel's thesis
-- it also seems mandatory to have

-- -- -- TODO show that all these things are PERs/closed under PER formation
-- -- TODO turn these into instances once proven

𝓔𝓵₀-respect-⊆ : ∀ {A} {B} {C} {D} → A == B ∈ 𝓢𝓮𝓽₀ → (A==C : A == C ∈ 𝓢𝓮𝓽₀) → (B==D : B == D ∈ 𝓢𝓮𝓽₀) → 𝓔𝓵₀ A==C ⊆ 𝓔𝓵₀ B==D
𝓔𝓵₀-respect-⊇ : ∀ {A} {B} {C} {D} → A == B ∈ 𝓢𝓮𝓽₀ → (A==C : A == C ∈ 𝓢𝓮𝓽₀) → (B==D : B == D ∈ 𝓢𝓮𝓽₀) → 𝓔𝓵₀ B==D ⊆ 𝓔𝓵₀ A==C
𝓔𝓵₀-respect-sym : ∀ {A} {B} → (A==B : A == B ∈ 𝓢𝓮𝓽₀) → {B==A : B == A ∈ 𝓢𝓮𝓽₀} → 𝓔𝓵₀ A==B ⊆ 𝓔𝓵₀ B==A
𝓔𝓵₀-respect-trans : ∀ {A} {B} {C} → (A==B : A == B ∈ 𝓢𝓮𝓽₀) → (B==C : B == C ∈ 𝓢𝓮𝓽₀) → 𝓔𝓵₀ A==B ⊆ 𝓔𝓵₀ B==C
Per-𝓔𝓵₀' : ∀{A B} → (eq : A == B ∈ 𝓢𝓮𝓽₀) → Per (𝓔𝓵₀ eq)
Set0-sym   : ∀{𝐴 𝐵} → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽₀ → 𝐵 == 𝐴 ∈ 𝓢𝓮𝓽₀
Set0-trans : ∀{𝐴 𝐵 𝐶} → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽₀ → 𝐵 == 𝐶 ∈ 𝓢𝓮𝓽₀ → 𝐴 == 𝐶 ∈ 𝓢𝓮𝓽₀

Set0-sym (𝓢𝓮𝓽₀-NE x) = 𝓢𝓮𝓽₀-NE (per-sym x)
Set0-sym 𝓢𝓮𝓽₀-𝑁 = 𝓢𝓮𝓽₀-𝑁
Set0-sym 𝓢𝓮𝓽₀-⊤ = 𝓢𝓮𝓽₀-⊤
Set0-sym 𝓢𝓮𝓽₀-⊥ = 𝓢𝓮𝓽₀-⊥
Set0-sym (𝓢𝓮𝓽₀-Π {𝐴} {𝐴'} {𝐹} {𝐹'} A==A' F==F') = 𝓢𝓮𝓽₀-Π A'==A F'==F
       where
         A'==A : 𝐴' == 𝐴 ∈ 𝓢𝓮𝓽₀
         A'==A = (Set0-sym A==A')
         massage : (𝓔𝓵₀ A'==A) ⊆ (𝓔𝓵₀ A==A')
         massage = 𝓔𝓵₀-respect-sym A'==A {A==A'}
         F'==F : ∀{𝑎' 𝑎} → 𝑎' == 𝑎 ∈ 𝓔𝓵₀ A'==A →
                     ∃[ 𝐵' ] ∃[ 𝐵 ] ( (𝐹' · 𝑎' ⇓ 𝐵') × (𝐹 · 𝑎 ⇓ 𝐵) × (𝐵' == 𝐵 ∈ 𝓢𝓮𝓽₀))
         F'==F ElA'Aa'a with massage ElA'Aa'a
         ... | ElAA'a'a with per-sym {{Per-𝓔𝓵₀' A==A'}} ElAA'a'a
         ... | ElAA'aa' with F==F' ElAA'aa'
         ... | B , B' , F·a⇓B , F'·a'⇓B'  , B==B' = B' , (B , ( F'·a'⇓B' , (F·a⇓B , Set0-sym B==B')))

Set0-trans (𝓢𝓮𝓽₀-NE NE==NE'') (𝓢𝓮𝓽₀-NE NE''==NE') = 𝓢𝓮𝓽₀-NE (per-trans NE==NE'' NE''==NE')
Set0-trans 𝓢𝓮𝓽₀-𝑁 𝓢𝓮𝓽₀-𝑁 = 𝓢𝓮𝓽₀-𝑁
Set0-trans 𝓢𝓮𝓽₀-⊤ 𝓢𝓮𝓽₀-⊤ = 𝓢𝓮𝓽₀-⊤
Set0-trans 𝓢𝓮𝓽₀-⊥ 𝓢𝓮𝓽₀-⊥ = 𝓢𝓮𝓽₀-⊥
Set0-trans (𝓢𝓮𝓽₀-Π {𝐴} {𝐴''} {𝐹} {𝐹''} A==A'' F==F'') (𝓢𝓮𝓽₀-Π {𝐴''} {𝐴'} {𝐹''} {𝐹'} A''==A' F''==F') = 𝓢𝓮𝓽₀-Π A==A' F==F'
       where
         A==A' : 𝐴 == 𝐴' ∈ 𝓢𝓮𝓽₀
         A==A' = (Set0-trans A==A'' A''==A')
         -- A==A : 𝐴 == 𝐴 ∈ 𝓢𝓮𝓽₀
         -- A==A = Set0-trans A==A'' (Set0-sym A==A'') -- here, we just inline the reflexivity proof
         massage₁ : (𝓔𝓵₀ A==A') ⊆ (𝓔𝓵₀ A==A'')
         massage₁ = 𝓔𝓵₀-respect-trans A==A' (Set0-sym A''==A')
         massage₂ : (𝓔𝓵₀ A==A') ⊆ (𝓔𝓵₀ A''==A')
         massage₂ = 𝓔𝓵₀-respect-⊆ A==A'' A==A' A''==A'
         F==F' : ∀ {𝑎 𝑎' : 𝕍} → 𝑎 == 𝑎' ∈ 𝓔𝓵₀ A==A'  →
                 ∃[ 𝐵 ] ∃[ 𝐵' ] ( (𝐹 · 𝑎 ⇓ 𝐵) × (𝐹' · 𝑎' ⇓ 𝐵') × (𝐵 == 𝐵' ∈ 𝓢𝓮𝓽₀))
         F==F' ELAA'aa' with F==F'' (massage₁ ELAA'aa') | F''==F' (per-refl {{Per-𝓔𝓵₀' A''==A'}} (memʳ (massage₂ ELAA'aa')))
         ... | B , B'' , F·a⇓B , F''·a'⇓B'' , B==B'' | B₀'' , B' , F''·a'⇓B₀'' , F'·a'⇓B' , B₀''==B'
               rewrite is-fun-· F''·a'⇓B₀''  F''·a'⇓B''
               = B , (B' , (F·a⇓B , ( F'·a'⇓B' , Set0-trans  B==B'' B₀''==B')))

-- importantly, per-reflexivity is a consequence of symmetry and transitivity!
Set0-refl : ∀{𝐴 𝐵} → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽₀ → 𝐴 == 𝐴 ∈ 𝓢𝓮𝓽₀
Set0-refl A==B = Set0-trans A==B (Set0-sym A==B)

𝓔𝓵₀-respect-sym = {!!}

𝓔𝓵₀-respect-trans  = {!!}


𝓔𝓵₀-respect-⊆ (𝓢𝓮𝓽₀-NE NE==NE') (𝓢𝓮𝓽₀-NE NE==NE'') (𝓢𝓮𝓽₀-NE NE'==NE''') (𝓥Ty-Ne-mem NE==NE₁ NE==NE₂ ne₁==ne₂) =
  𝓥Ty-Ne-mem (per-trans (per-sym NE==NE') NE==NE₁) ((per-trans (per-sym NE==NE') NE==NE₂)) ne₁==ne₂
𝓔𝓵₀-respect-⊆ 𝓢𝓮𝓽₀-𝑁 𝓢𝓮𝓽₀-𝑁 𝓢𝓮𝓽₀-𝑁 = λ z → z
𝓔𝓵₀-respect-⊆ 𝓢𝓮𝓽₀-⊤ 𝓢𝓮𝓽₀-⊤ 𝓢𝓮𝓽₀-⊤ = λ z → z
𝓔𝓵₀-respect-⊆ 𝓢𝓮𝓽₀-⊥ 𝓢𝓮𝓽₀-⊥ 𝓢𝓮𝓽₀-⊥ = λ _ → tt
𝓔𝓵₀-respect-⊆ (𝓢𝓮𝓽₀-Π {𝐴}  {𝐴'}   {𝐹}  {𝐹'}   A=A'    F=F')
              (𝓢𝓮𝓽₀-Π {𝐴}  {𝐴''}  {𝐹}  {𝐹''}  A=A''   F=F'')
              (𝓢𝓮𝓽₀-Π {𝐴'} {𝐴'''} {𝐹'} {𝐹'''} A'=A''' F'=F''')
              f==f''∈ΠAA''-FF''
              ELA'=A'''aa' with 𝓔𝓵₀-respect-⊇ A=A' A=A'' A'=A''' ELA'=A'''aa'
-- IMPORTANT: calling f==f''∈ΠAA''-FF'' has to be made as early as possible
--            otherwise, the final call to IH below won't go through
--            The problem is the lambda abstraction in the goal.
... | ELA=A''aa' with f==f''∈ΠAA''-FF'' ELA=A''aa'
... | 𝑏 , 𝑏' ,  𝑓·𝑎⇓𝑏 , 𝑓''·𝑎'⇓𝑏' , 𝑏==𝑏'∈𝓔𝓵₀FA==F''A''
      with 𝓔𝓵₀-respect-⊇ A=A' A=A' A'=A''' ELA'=A'''aa'
... | ELA=A'aa' with (per-refl {{Per-𝓔𝓵₀' A=A'}} (memˡ  ELA=A'aa'))
... | ELA=A'aa  with F=F' ELA=A'aa | F=F'' ELA=A''aa' | F'=F''' ELA'=A'''aa'
... | F·a   , F'·a    , F·a⇓   , F'·a⇓    , FA==F'A'
    | !F·a  , F''·a'  , !F·a⇓  , F''·a'⇓  , FA==F''A''
    | !F'·a , F'''·a' , !F'·a⇓ , F'''·a'⇓ , F'A'==F'''A'''
      rewrite is-fun-· !F·a⇓  F·a⇓ | is-fun-· !F'·a⇓  F'·a⇓
      with  𝓔𝓵₀-respect-⊆ FA==F'A' FA==F''A''  F'A'==F'''A'''
... | IH = 𝑏 , (𝑏' , (𝑓·𝑎⇓𝑏 , (𝑓''·𝑎'⇓𝑏' , IH 𝑏==𝑏'∈𝓔𝓵₀FA==F''A'')))

𝓔𝓵₀-respect-⊇ (𝓢𝓮𝓽₀-NE NE==NE') (𝓢𝓮𝓽₀-NE NE==NE'') (𝓢𝓮𝓽₀-NE NE'==NE''') (𝓥Ty-Ne-mem NE'==NE₁ NE'==NE₂ ne₁==ne₂) =
  𝓥Ty-Ne-mem (per-trans NE==NE' NE'==NE₁) (per-trans NE==NE' NE'==NE₂ ) ne₁==ne₂
𝓔𝓵₀-respect-⊇ 𝓢𝓮𝓽₀-𝑁 𝓢𝓮𝓽₀-𝑁 𝓢𝓮𝓽₀-𝑁 = λ z → z
𝓔𝓵₀-respect-⊇ 𝓢𝓮𝓽₀-⊤ 𝓢𝓮𝓽₀-⊤ 𝓢𝓮𝓽₀-⊤ = λ z → z
𝓔𝓵₀-respect-⊇ 𝓢𝓮𝓽₀-⊥ 𝓢𝓮𝓽₀-⊥ 𝓢𝓮𝓽₀-⊥ = λ _ → tt
𝓔𝓵₀-respect-⊇ (𝓢𝓮𝓽₀-Π {𝐴}  {𝐴'}   {𝐹}  {𝐹'}   A=A'    F=F')
              (𝓢𝓮𝓽₀-Π {𝐴}  {𝐴''}  {𝐹}  {𝐹''}  A=A''   F=F'')
              (𝓢𝓮𝓽₀-Π {𝐴'} {𝐴'''} {𝐹'} {𝐹'''} A'=A''' F'=F''')
              f'==f'''∈ΠA'A'''-F'F'''
              ELA=A''aa' with 𝓔𝓵₀-respect-⊆ A=A' A=A'' A'=A''' ELA=A''aa'
... | ELA'=A'''aa' with  f'==f'''∈ΠA'A'''-F'F''' ELA'=A'''aa'
... | 𝑏 , 𝑏' ,  𝑓'·𝑎⇓𝑏 , 𝑓'''·𝑎'⇓𝑏' , 𝑏==𝑏'∈𝓔𝓵₀F'A'==F'''A''' = {!!}
--       with 𝓔𝓵₀-respect-⊆  A=A' A'=A''' A=A' ELA'=A'''aa'
-- ... | ELA=A'aa'  = {!!}

Per.per-sym   (Per-𝓔𝓵₀' eq) = {!!}
Per.per-trans (Per-𝓔𝓵₀' eq) = {!!}

instance Per-𝓢𝓮𝓽₀ : Per 𝓢𝓮𝓽₀
per-sym   {{Per-𝓢𝓮𝓽₀}} = Set0-sym
per-trans {{Per-𝓢𝓮𝓽₀}} = Set0-trans

instance Per-𝓔𝓵₀ : ∀{A B} → {eq : A == B ∈ 𝓢𝓮𝓽₀} → Per (𝓔𝓵₀ eq)
per-sym   {{Per-𝓔𝓵₀ {_} {_} {eq}}} = per-sym   {{Per-𝓔𝓵₀' eq}}
per-trans {{Per-𝓔𝓵₀ {_} {_} {eq}}} = per-trans {{Per-𝓔𝓵₀' eq}}

-- -- -- Set of all semantic types is the limit 𝓢𝓮𝓽ω
-- -- 𝓢𝓮𝓽ω : Rel
-- -- 𝓢𝓮𝓽ω A B = ∃[ 𝓁 ]( A == B ∈ (𝓢𝓮𝓽 𝓁) )
-- -- 𝒯𝓎𝓅ℯ = 𝓢𝓮𝓽ω

-- -- -- Value interpretation is the limit 𝓔𝓵ω
-- -- 𝓔𝓵ω : 𝕍 → Rel
-- -- 𝓔𝓵ω 𝑇 𝑎 𝑏 = ∃[ 𝓁 ]( 𝑎 == 𝑏 ∈ 𝓔𝓵 𝓁 𝑇 )

-- -- -- Interpretation of syntactic types into semantic types (PERs)
-- -- open import dsube.NbE using (⟦_⟧_⇓_)
-- -- open import dsube.Syntax using (Exp)

-- -- data [_]_⇓_ : Exp → Env → Rel → Set where
-- --   ty-rel : ∀{T ρ 𝑇} →
-- --      ⟦ T ⟧ ρ ⇓ 𝑇 →
-- --      -----------------
-- --      [ T ] ρ ⇓ 𝓔𝓵ω 𝑇

-- -- -- TODO show that all these things live in the candidate space

-- -- -- TODO: semantically well-formed contexts and context extension (p. 46)

-- -- -- TODO: for each of the syntactic judgments, define the semantic jugdements (p. 46)
-- -- -- TODO: esp: how to deal with subtyping?

-- -- -- TODO : typed candidate spaces (p. 47)

-- -- -- TODO : completeness proof (end of 4.5, p. 48)


-- -- ```
