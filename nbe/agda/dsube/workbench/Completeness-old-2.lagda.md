# Completeness of Normalization by Evaluation for Dᵉ<:>

We prove completeness with a partial equivalence (PER) model.
Completeness means that whatever terms are βη-equal in the Dᵉ<:> system,
so will be their normal forms in the PER model of equality (and their NFs exist!)

It seems sufficient to use this result to conclude termination of NbE,
for the special case of relating a well-typed expression to itself.


```agda
module dsube.Completeness where

open import Data.Bool using (true; false)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax; _,_; _×_)
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
-- TODO makes proofs simpler if we just define it to be R a a, since
-- we only care about PERs, which are by definition reflexive on their domain.
-- Right now, we pointlessly have to duplicate proofs.
_∈_ : ∀{𝓐 : Set} → 𝓐 → Rel₂ 𝓐 → Set
a ∈ R = ∃[ a' ]( (R a a') ⊎ (R a' a) )

Dom : ∀{𝓐 : Set} → Rel₂ 𝓐 → Set
Dom R = ∃[ a ]( a ∈ R )

_∪_ : ∀{𝓐 : Set} → Rel₂ 𝓐 → Rel₂ 𝓐 → Rel₂ 𝓐
_∪_ R₁ R₂ a b = R₁ a b ⊎ R₂ a b

-- fancy notation for semantic equality
_==_∈_ : ∀{𝓐 : Set} → 𝓐 → 𝓐 → Rel₂ 𝓐 → Set
a == b ∈ R = R a b

memˡ : ∀ {𝓐}{R : Rel₂ 𝓐}{a b} → R a b → a ∈ R
memˡ {𝓐} {R} {a} {b} Rab = (b , inj₁ Rab)

memʳ : ∀ {𝓐}{R : Rel₂ 𝓐}{a b} → R a b → b ∈ R
memʳ  {𝓐} {R} {a} {b} Rab = (a , inj₂ Rab)

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
    per-refl  : ∀ {a} → a ∈ R → R a a
    per-sym   : ∀ {a a'} → R a a' → R a' a
    per-trans : ∀ {a b c} → R a b → R b c → R a c
open Per {{...}}

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
per-refl  {{Per-𝓣𝓸𝓹}} (_ , inj₁ Taa') n with Taa' n
... | eᴺᶠ , ℜᴺᶠ⟨n⟩a⇓eᴺᶠ , _ = eᴺᶠ , ℜᴺᶠ⟨n⟩a⇓eᴺᶠ , ℜᴺᶠ⟨n⟩a⇓eᴺᶠ
per-refl  {{Per-𝓣𝓸𝓹}} (_ , inj₂ Ta'a) n with Ta'a n
... | eᴺᶠ , _ , ℜᴺᶠ⟨n⟩a⇓eᴺᶠ = eᴺᶠ , ℜᴺᶠ⟨n⟩a⇓eᴺᶠ , ℜᴺᶠ⟨n⟩a⇓eᴺᶠ
per-sym   {{Per-𝓣𝓸𝓹}} Taa' n with Taa' n
... | eᴺᶠ , fst , snd = eᴺᶠ , snd , fst
per-trans {{Per-𝓣𝓸𝓹}} Tab Tbc n  with Tab n | Tbc n
... | eab , fst , snd | ebc , fst₁ , snd₁ rewrite is-fun-ℜᴺᶠ snd fst₁ = ebc , fst , snd₁

instance Per-𝓑𝓸𝓽 : Per 𝓑𝓸𝓽
per-refl  {{Per-𝓑𝓸𝓽}} (_ , inj₁ Botaa') n with Botaa' n
... | x , fst , _ = x , fst , fst
per-refl  {{Per-𝓑𝓸𝓽}} (_ , inj₂ Bota'a) n with Bota'a n
... | x , _ , snd = x , snd , snd
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
per-refl  {{Per-𝓝𝓪𝓽}} (_ , inj₁ 𝓝-𝑛) = 𝓝-𝑛
per-refl  {{Per-𝓝𝓪𝓽}} (_ , inj₁ (𝓝-Ne {nv} {nv'} x)) = 𝓝-Ne (per-refl ( nv' , inj₁ x))
per-refl  {{Per-𝓝𝓪𝓽}} (_ , inj₂ 𝓝-𝑛) = 𝓝-𝑛
per-refl  {{Per-𝓝𝓪𝓽}} (_ , inj₂ (𝓝-Ne {nv} {nv'} x)) = 𝓝-Ne (per-refl ( nv , inj₂ x))
per-sym   {{Per-𝓝𝓪𝓽}} 𝓝-𝑛 = 𝓝-𝑛
per-sym   {{Per-𝓝𝓪𝓽}} (𝓝-Ne x) = 𝓝-Ne (per-sym x)
per-trans {{Per-𝓝𝓪𝓽}} 𝓝-𝑛 𝓝-𝑛 = 𝓝-𝑛
per-trans {{Per-𝓝𝓪𝓽}} (𝓝-Ne x) (𝓝-Ne x₁) = 𝓝-Ne (per-trans x x₁)

-- PERs over a domain indexed by a PER
record _∶_⟹Per {D : Set} (F : D → Rel₂ D) (𝓐 : Rel₂ D) : Set₁ where
  field
    respect : ∀{a a'} → 𝓐 a a' → F a ≡ᴿ F a'
    per-family : ∀{a} → a ∈ 𝓐 → Per (F a)
open _∶_⟹Per

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
per-refl  {{Per-𝓥Ty-Ne}} (.(↑⟨ ↑⟨ ᶜ V𝑆𝑒𝑡 _ ⟩ _ ⟩ _) , inj₁ (𝓥Ty-Ne-mem x x₁ x₂)) =
  𝓥Ty-Ne-mem x x (per-refl (memˡ {_} {𝓑𝓸𝓽} x₂))
per-refl  {{Per-𝓥Ty-Ne}} (.(↑⟨ ↑⟨ ᶜ V𝑆𝑒𝑡 _ ⟩ _ ⟩ _) , inj₂ (𝓥Ty-Ne-mem x x₁ x₂)) =
  𝓥Ty-Ne-mem x₁ x₁ (per-refl (memʳ {_} {𝓑𝓸𝓽} x₂))
per-sym   {{Per-𝓥Ty-Ne}} (𝓥Ty-Ne-mem x x₁ x₂) = 𝓥Ty-Ne-mem x₁ x (per-sym x₂)
per-trans {{Per-𝓥Ty-Ne}} (𝓥Ty-Ne-mem x x₁ x₂) (𝓥Ty-Ne-mem y y₁ y₂) = 𝓥Ty-Ne-mem x y₁ (per-trans x₂ y₂)

-- ⊥ type interp
-- TODO not sure either, but to fulfill the candidate space requirement, V⊥ cannot be empty
-- it appears reasonable to take the total relation, as interpreting a term at type V⊥ logically
-- implies arbitrary things
𝓥⊥ : Rel
𝓥⊥ _ _ = ⊤

instance Per-𝓥⊥ : Per 𝓥⊥
per-refl  {{Per-𝓥⊥}} _   = tt
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
per-refl  {{Per-𝓥⊤}} _ = 𝓥⊤-val
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
per-refl  {{Per-𝓥Type {𝓢} {𝓣} }} (.(↑⟨ ⟪Type _ ⋯ _ ⟫ ⟩ _) , inj₁ (𝓥Type-ne x x₁ x₂)) =
  𝓥Type-ne (per-refl (memˡ {_} {𝓢} x))
            (per-refl (memˡ {_} {𝓣} x₁))
            (per-refl (memˡ {_} {𝓑𝓸𝓽} x₂))
per-refl  {{Per-𝓥Type {𝓢} {𝓣} }} (.(VType _) , inj₁ (𝓥Type-val {𝐴} {𝐴'} x x₁)) =
  𝓥Type-val (per-refl (𝐴' , inj₁ x)) (per-refl (𝐴' , inj₁ x₁))
per-refl  {{Per-𝓥Type {𝓢} {𝓣} }} (.(↑⟨ ⟪Type _ ⋯ _ ⟫ ⟩ _) , inj₂ (𝓥Type-ne x x₁ x₂)) =
  𝓥Type-ne (per-refl (memʳ {_} {𝓢} x))
            (per-refl (memʳ {_} {𝓣} x₁))
            (per-refl (memʳ {_} {𝓑𝓸𝓽} x₂))
per-refl  {{Per-𝓥Type {𝓢} {𝓣} }} (.(VType _) , inj₂ (𝓥Type-val {𝐴} {𝐴'} x x₁)) =
  𝓥Type-val (per-refl (𝐴 , inj₂ x)) (per-refl (𝐴 , inj₂ x₁))
per-sym   {{Per-𝓥Type}} (𝓥Type-ne x x₁ x₂) = 𝓥Type-ne (per-sym x) (per-sym x₁) (per-sym x₂)
per-sym   {{Per-𝓥Type}} (𝓥Type-val x x₁)   = 𝓥Type-val (per-sym x) (per-sym x₁)
per-trans {{Per-𝓥Type}} (𝓥Type-ne x x₁ x₂) (𝓥Type-ne x₃ x₄ x₅) =
  𝓥Type-ne (per-trans x x₃) (per-trans x₁ x₄) (per-trans x₂ x₅)
per-trans {{Per-𝓥Type}} (𝓥Type-val x x₁) (𝓥Type-val x₂ x₃) =
  𝓥Type-val (per-trans x x₂) (per-trans x₁ x₃)


-- First, the universe at level 0
data 𝓢𝓮𝓽₀ : Rel
data 𝓔𝓵₀ : 𝕍 → Rel

data 𝓢𝓮𝓽₀ where
  𝓢𝓮𝓽₀-NE : ∀{NE NE'} →
    NE == NE' ∈ 𝓑𝓸𝓽 →
    -------------------------------------------------
    ↑⟨ (ᶜ (V𝑆𝑒𝑡 0)) ⟩ NE == ↑⟨ (ᶜ (V𝑆𝑒𝑡 0)) ⟩ NE' ∈ 𝓢𝓮𝓽₀

  𝓢𝓮𝓽₀-𝑁 : (ᶜ V𝑁) == (ᶜ V𝑁) ∈ 𝓢𝓮𝓽₀

  𝓢𝓮𝓽₀-⊤ : (ᶜ V⊤) == (ᶜ V⊤) ∈ 𝓢𝓮𝓽₀

  𝓢𝓮𝓽₀-⊥ : (ᶜ V⊥) == (ᶜ V⊥) ∈ 𝓢𝓮𝓽₀

  𝓢𝓮𝓽₀-Π : ∀{𝐴 𝐴' 𝐹 𝐹'} →
    𝐴 == 𝐴' ∈ 𝓢𝓮𝓽₀ →
    (∀{𝑎 𝑎'} → 𝑎 == 𝑎' ∈ (𝓔𝓵₀ 𝐴) →
               (∃[ 𝐵 ] ∃[ 𝐵' ] ( (𝐹 · 𝑎 ⇓ 𝐵) × (𝐹' · 𝑎' ⇓ 𝐵') × (𝐵 == 𝐵' ∈ 𝓢𝓮𝓽₀) ))) →
    -----------------------------------------------------------------------------------
    VΠ 𝐴 𝐹 == VΠ 𝐴' 𝐹' ∈ 𝓢𝓮𝓽₀

data 𝓔𝓵₀ where
   𝓔𝓵₀-𝑁 : ∀{𝑎 𝑏} →
           𝑎 == 𝑏 ∈ 𝓝𝓪𝓽 →
           -------------------
           𝑎 == 𝑏 ∈ 𝓔𝓵₀ (ᶜ V𝑁)

   𝓔𝓵₀-⊤ : ∀{𝑎 𝑏} →
           𝑎 == 𝑏 ∈ 𝓥⊤ →
           -------------------
           𝑎 == 𝑏 ∈ 𝓔𝓵₀ (ᶜ V⊤)

   𝓔𝓵₀-⊥ : ∀{𝑎 𝑏} →
           𝑎 == 𝑏 ∈ 𝓥⊥ →
           -------------------
           𝑎 == 𝑏 ∈ 𝓔𝓵₀ (ᶜ V⊥)

   𝓔𝓵₀-Ty-Ne : ∀ {NE ne ne'} →
           ne == ne' ∈ 𝓥Ty-Ne 0 NE →
           ------------------------------------
           ne == ne' ∈ 𝓔𝓵₀ (↑⟨ (ᶜ (V𝑆𝑒𝑡 0)) ⟩ NE)

   𝓔𝓵₀-Π : ∀{𝐴 𝐹 𝐹·𝑎 𝑓 𝑓' 𝑎 𝑎' 𝑏 𝑏'} →
           𝑎 == 𝑎' ∈ 𝓔𝓵₀ 𝐴 →
           𝐹  · 𝑎  ⇓ 𝐹·𝑎 →
           𝑓  · 𝑎  ⇓ 𝑏 →
           𝑓' · 𝑎' ⇓ 𝑏' →
           𝑏 == 𝑏' ∈ 𝓔𝓵₀ 𝐹·𝑎 →
           ----------------------
           𝑓 == 𝑓' ∈ 𝓔𝓵₀ (VΠ 𝐴 𝐹)

data 𝓢𝓮𝓽ₖ₊₁ {𝓀 : ℒ} {𝓢ₖ : Rel} {𝓔𝓵ₖ : 𝕍 → Rel} : Rel
data 𝓔𝓵ₖ₊₁  {𝓀 : ℒ} {𝓢ₖ : Rel} {𝓔𝓵ₖ : 𝕍 → Rel} : 𝕍 → Rel

data 𝓢𝓮𝓽ₖ₊₁ {𝓀} {𝓢ₖ} {𝓔𝓵ₖ} where
  𝓢𝓮𝓽ₖ₊₁-NE : ∀{NE NE'} →
    NE == NE' ∈ 𝓑𝓸𝓽 →
    ------------------------------------------------------------------------
    ↑⟨ (ᶜ (V𝑆𝑒𝑡 (suc 𝓀))) ⟩ NE == ↑⟨ (ᶜ (V𝑆𝑒𝑡 (suc 𝓀))) ⟩ NE' ∈ 𝓢𝓮𝓽ₖ₊₁

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
    𝐴 == 𝐴' ∈ 𝓢𝓮𝓽ₖ₊₁ {𝓀} {𝓢ₖ} {𝓔𝓵ₖ} →
    (∀{𝑎 𝑎'} → 𝑎 == 𝑎' ∈ (𝓔𝓵ₖ₊₁ {𝓀} {𝓢ₖ} {𝓔𝓵ₖ} 𝐴) →
               (∃[ 𝐵 ] ∃[ 𝐵' ] ( (𝐹 · 𝑎 ⇓ 𝐵) × (𝐹' · 𝑎' ⇓ 𝐵') × (𝐵 == 𝐵' ∈ 𝓢𝓮𝓽ₖ₊₁ {𝓀} {𝓢ₖ} {𝓔𝓵ₖ}) ))) →
    ----------------------------------------------------------------------------------------------------
    VΠ 𝐴 𝐹 == VΠ 𝐴' 𝐹' ∈ 𝓢𝓮𝓽ₖ₊₁

data 𝓔𝓵ₖ₊₁ {𝓀} {𝓢ₖ} {𝓔𝓵ₖ} where
   𝓔𝓵ₖ₊₁-𝑁 : ∀{𝑎 𝑏} →
           𝑎 == 𝑏 ∈ 𝓝𝓪𝓽 →
           --------------------
           𝑎 == 𝑏 ∈ 𝓔𝓵ₖ₊₁ (ᶜ V𝑁)

   𝓔𝓵ₖ₊₁-⊤ : ∀{𝑎 𝑏} →
           𝑎 == 𝑏 ∈ 𝓥⊤ →
           --------------------
           𝑎 == 𝑏 ∈ 𝓔𝓵ₖ₊₁ (ᶜ V⊤)

   𝓔𝓵ₖ₊₁-⊥ : ∀{𝑎 𝑏} →
           𝑎 == 𝑏 ∈ 𝓥⊥ →
           -------------------
           𝑎 == 𝑏 ∈ 𝓔𝓵ₖ₊₁ (ᶜ V⊥)

   𝓔𝓵ₖ₊₁-Ty-Ne : ∀ {NE ne ne'} →
           ne == ne' ∈ 𝓥Ty-Ne (suc 𝓀) NE →
           -------------------------------------------
           ne == ne' ∈ 𝓔𝓵ₖ₊₁ (↑⟨ (ᶜ (V𝑆𝑒𝑡 (suc 𝓀))) ⟩ NE)

   𝓔𝓵ₖ₊₁-𝑆𝑒𝑡-pred : ∀{𝐴 𝐴'} →
           𝐴 == 𝐴' ∈ 𝓢ₖ →
           -------------------------
           𝐴 == 𝐴' ∈ 𝓔𝓵ₖ₊₁ (ᶜ V𝑆𝑒𝑡 𝓀)

   𝓔𝓵ₖ₊₁-𝑆𝑒𝑡-below : ∀{𝐴 𝐴' 𝓁} →
           𝓁 <′ 𝓀 →
           𝐴 == 𝐴' ∈ 𝓔𝓵ₖ (ᶜ V𝑆𝑒𝑡 𝓁) →
           --------------------------
           𝐴 == 𝐴' ∈ 𝓔𝓵ₖ₊₁ (ᶜ V𝑆𝑒𝑡 𝓁)

   𝓔𝓵ₖ₊₁-⟪Type⋯⟫ : ∀{𝑆 𝑇 𝐴 𝐴'} →
           𝐴 == 𝐴' ∈ 𝓥Type (𝓔𝓵ₖ 𝑆) (𝓔𝓵ₖ 𝑇) →
           ----------------------------------
           𝐴 == 𝐴' ∈ 𝓔𝓵ₖ₊₁ ⟪Type 𝑆 ⋯ 𝑇 ⟫

   𝓔𝓵ₖ₊₁-Π : ∀{𝐴 𝐹 𝐹·𝑎 𝑓 𝑓' 𝑎 𝑎' 𝑏 𝑏'} →

           (∀{ 𝑎 𝑎' } →
             𝑎 == 𝑎' ∈ 𝓔𝓵ₖ₊₁ {𝓀} {𝓢ₖ} {𝓔𝓵ₖ} 𝐴 →
             𝐹  · 𝑎  ⇓ 𝐹·𝑎 →
             𝑓  · 𝑎  ⇓ 𝑏 →
             𝑓' · 𝑎' ⇓ 𝑏' →
             𝑏 == 𝑏' ∈ 𝓔𝓵ₖ₊₁ {𝓀} {𝓢ₖ} {𝓔𝓵ₖ} 𝐹·𝑎) →
           ------------------------------------
           𝑓 == 𝑓' ∈ 𝓔𝓵ₖ₊₁ (VΠ 𝐴 𝐹)

𝓢𝓮𝓽 : ℒ → Rel
𝓔𝓵 : ℒ → 𝕍 → Rel

𝓢𝓮𝓽 0 = 𝓢𝓮𝓽₀
𝓢𝓮𝓽 (suc 𝓀) = 𝓢𝓮𝓽ₖ₊₁ {𝓀} {𝓢𝓮𝓽 𝓀} {𝓔𝓵 𝓀}

𝓔𝓵 0 = 𝓔𝓵₀
𝓔𝓵 (suc 𝓀) = 𝓔𝓵ₖ₊₁ {𝓀} {𝓢𝓮𝓽 𝓀} {𝓔𝓵 𝓀}

-- -- TOOD It might also be beneficial if we have proper inversion lemmas for these
𝓢𝓮𝓽-NE : ∀{𝓀 NE NE'} →
  NE == NE' ∈ 𝓑𝓸𝓽 →
  --------------------------------------------------
  ↑⟨ (ᶜ (V𝑆𝑒𝑡 𝓀)) ⟩ NE == ↑⟨ (ᶜ (V𝑆𝑒𝑡 𝓀)) ⟩ NE' ∈ 𝓢𝓮𝓽 𝓀

𝓢𝓮𝓽-𝑁 : ∀{𝓀} → (ᶜ V𝑁) == (ᶜ V𝑁) ∈ 𝓢𝓮𝓽 𝓀

𝓢𝓮𝓽-⊤ : ∀{𝓀} → (ᶜ V⊤) == (ᶜ V⊤) ∈ 𝓢𝓮𝓽 𝓀

𝓢𝓮𝓽-⊥ : ∀{𝓀} → (ᶜ V⊥) == (ᶜ V⊥) ∈ 𝓢𝓮𝓽 𝓀

𝓢𝓮𝓽-⟪Type⋯⟫ : ∀{𝓀 𝑆 𝑆' 𝑇 𝑇'} →
  𝑆 == 𝑆' ∈ 𝓢𝓮𝓽 𝓀 →
  𝑇 == 𝑇' ∈ 𝓢𝓮𝓽 𝓀 →
  -----------------------------------------------
  ⟪Type 𝑆 ⋯ 𝑇 ⟫ == ⟪Type 𝑆' ⋯ 𝑇' ⟫ ∈ 𝓢𝓮𝓽 (suc 𝓀)

open import Data.Nat.Properties using (<-irrefl; ≤′⇒≤)
open _≤′_
𝓢𝓮𝓽ₗ∈𝓢𝓮𝓽ₖ : ∀{𝓁 𝓀} → 𝓁 <′ 𝓀 → (ᶜ (V𝑆𝑒𝑡 𝓁)) == (ᶜ (V𝑆𝑒𝑡 𝓁)) ∈ 𝓢𝓮𝓽 𝓀

𝓢𝓮𝓽-Π : ∀{𝓀 𝐴 𝐴' 𝐹 𝐹'} →
  𝐴 == 𝐴' ∈ 𝓢𝓮𝓽 𝓀 →
  (∀{𝑎 𝑎'} → 𝑎 == 𝑎' ∈ (𝓔𝓵 𝓀 𝐴) →
             (∃[ 𝐵 ] ∃[ 𝐵' ] ( (𝐹 · 𝑎 ⇓ 𝐵) × (𝐹' · 𝑎' ⇓ 𝐵') × (𝐵 == 𝐵' ∈ 𝓢𝓮𝓽 𝓀) ))) →
  -------------------------------------------------------------------------------------
  VΠ 𝐴 𝐹 == VΠ 𝐴' 𝐹' ∈ 𝓢𝓮𝓽 𝓀

𝓔𝓵-𝑁 : ∀ {𝓀} → 𝓔𝓵 𝓀 (ᶜ V𝑁) ≡ᴿ 𝓝𝓪𝓽

𝓔𝓵-⊤ : ∀ {𝓀} → 𝓔𝓵 𝓀 (ᶜ V⊤) ≡ᴿ 𝓥⊤

𝓔𝓵-⊥ : ∀ {𝓀} → 𝓔𝓵 𝓀 (ᶜ V⊥) ≡ᴿ 𝓥⊥

𝓔𝓵-𝑆𝑒𝑡 : ∀ {𝓁 𝓀} → 𝓁 <′ 𝓀 → 𝓔𝓵 𝓀 (ᶜ (V𝑆𝑒𝑡 𝓁)) ≡ᴿ 𝓢𝓮𝓽 𝓁
𝓔𝓵-𝑆𝑒𝑡 {𝓁} {.(suc 𝓁)} ≤′-refl = (λ{ (𝓔𝓵ₖ₊₁-𝑆𝑒𝑡-pred x) → x ;
                                   (𝓔𝓵ₖ₊₁-𝑆𝑒𝑡-below x x₁) → ⊥-elim (<-irrefl refl (≤′⇒≤ x))}) ,
                                𝓔𝓵ₖ₊₁-𝑆𝑒𝑡-pred
𝓔𝓵-𝑆𝑒𝑡 {𝓁} {(suc 𝓀')} (≤′-step 𝓁<𝓀') with 𝓔𝓵-𝑆𝑒𝑡 𝓁<𝓀'
... | fst , snd = left , right
  where
    left : 𝓔𝓵ₖ₊₁ (ᶜ V𝑆𝑒𝑡 𝓁) ⊆ 𝓢𝓮𝓽 𝓁
    left (𝓔𝓵ₖ₊₁-𝑆𝑒𝑡-pred x) = x
    left (𝓔𝓵ₖ₊₁-𝑆𝑒𝑡-below x x₁) = fst x₁
    right : 𝓢𝓮𝓽 𝓁 ⊆ 𝓔𝓵ₖ₊₁ (ᶜ V𝑆𝑒𝑡 𝓁)
    right Set𝓁ab = 𝓔𝓵ₖ₊₁-𝑆𝑒𝑡-below 𝓁<𝓀' (snd Set𝓁ab)

𝓔𝓵-⟪Type⋯⟫ : ∀ {𝓀 𝑆 𝑇} → 𝓔𝓵 (suc 𝓀) ⟪Type 𝑆 ⋯ 𝑇 ⟫ ≡ᴿ 𝓥Type (𝓔𝓵 𝓀 𝑆) (𝓔𝓵 𝓀 𝑇)

𝓔𝓵-NE : ∀ {𝓀 NE} → 𝓔𝓵 𝓀 (↑⟨ (ᶜ (V𝑆𝑒𝑡 𝓀)) ⟩ NE) ≡ᴿ 𝓥Ty-Ne 𝓀 NE

-- proofs are mostly straightforward
𝓔𝓵-𝑁 {zero} = (λ{ (𝓔𝓵₀-𝑁 x) → x}) , (λ{ x → 𝓔𝓵₀-𝑁 x})
𝓔𝓵-𝑁 {suc 𝓀} = (λ{ (𝓔𝓵ₖ₊₁-𝑁 x) → x}) , (λ{ x → 𝓔𝓵ₖ₊₁-𝑁 x})

𝓔𝓵-⊤ {zero} = (λ{ (𝓔𝓵₀-⊤ x) → x}) , (λ{ x → 𝓔𝓵₀-⊤ x})
𝓔𝓵-⊤ {suc 𝓀} = (λ{ (𝓔𝓵ₖ₊₁-⊤ x) → x}) , (λ{ x → 𝓔𝓵ₖ₊₁-⊤ x})

𝓔𝓵-⊥ {zero} = (λ{ (𝓔𝓵₀-⊥ x) → x}) , (λ{ x → 𝓔𝓵₀-⊥ x})
𝓔𝓵-⊥ {suc 𝓀} = (λ{ (𝓔𝓵ₖ₊₁-⊥ x) → x}) , (λ{ x → 𝓔𝓵ₖ₊₁-⊥ x})

𝓔𝓵-⟪Type⋯⟫ = (λ{ (𝓔𝓵ₖ₊₁-⟪Type⋯⟫ x) → x}) ,
               λ{ (𝓥Type-ne x x₁ x₂) → 𝓔𝓵ₖ₊₁-⟪Type⋯⟫ (𝓥Type-ne x x₁ x₂) ;
                  (𝓥Type-val x x₁) → 𝓔𝓵ₖ₊₁-⟪Type⋯⟫ (𝓥Type-val x x₁)}

𝓔𝓵-NE {zero} = (λ{ (𝓔𝓵₀-Ty-Ne x) → x}) , λ{ (𝓥Ty-Ne-mem x x₁ x₂) → 𝓔𝓵₀-Ty-Ne (𝓥Ty-Ne-mem x x₁ x₂)}
𝓔𝓵-NE {suc 𝓀} = (λ{ (𝓔𝓵ₖ₊₁-Ty-Ne x) → x}) , (λ{ (𝓥Ty-Ne-mem x x₁ x₂) → 𝓔𝓵ₖ₊₁-Ty-Ne (𝓥Ty-Ne-mem x x₁ x₂)})

𝓢𝓮𝓽-NE {zero} = 𝓢𝓮𝓽₀-NE
𝓢𝓮𝓽-NE {suc 𝓀} = 𝓢𝓮𝓽ₖ₊₁-NE

𝓢𝓮𝓽-𝑁 {zero} = 𝓢𝓮𝓽₀-𝑁
𝓢𝓮𝓽-𝑁 {suc 𝓀} = 𝓢𝓮𝓽ₖ₊₁-𝑁

𝓢𝓮𝓽-⊤ {zero} = 𝓢𝓮𝓽₀-⊤
𝓢𝓮𝓽-⊤ {suc 𝓀} = 𝓢𝓮𝓽ₖ₊₁-⊤

𝓢𝓮𝓽-⊥ {zero} = 𝓢𝓮𝓽₀-⊥
𝓢𝓮𝓽-⊥ {suc 𝓀} = 𝓢𝓮𝓽ₖ₊₁-⊥

𝓢𝓮𝓽-⟪Type⋯⟫ 𝑆==𝑆' 𝑇==𝑇' = 𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ 𝑆==𝑆' 𝑇==𝑇'

𝓢𝓮𝓽ₗ∈𝓢𝓮𝓽ₖ {𝓁} {.(suc 𝓁)} ≤′-refl = 𝓢𝓮𝓽ₖ₊₁-𝓢𝓮𝓽ₖ
𝓢𝓮𝓽ₗ∈𝓢𝓮𝓽ₖ {𝓁} {.(suc _)} (≤′-step 𝓁<𝓀) = 𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ (𝓢𝓮𝓽ₗ∈𝓢𝓮𝓽ₖ 𝓁<𝓀)

𝓢𝓮𝓽-Π {zero} = 𝓢𝓮𝓽₀-Π
𝓢𝓮𝓽-Π {suc 𝓀} = 𝓢𝓮𝓽ₖ₊₁-Π

-- Another litmus test
open import Data.Nat.Properties using (≤′-trans)
Set𝓁∈Set𝓀→𝓁<𝓀 : ∀{𝓀 𝓁} → (ᶜ (V𝑆𝑒𝑡 𝓁)) == (ᶜ (V𝑆𝑒𝑡 𝓁)) ∈ 𝓢𝓮𝓽 𝓀 → 𝓁 <′ 𝓀
Set𝓁∈Set𝓀→𝓁<𝓀 {suc 𝓀} {𝓁} (𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ x) with Set𝓁∈Set𝓀→𝓁<𝓀 x
... | y = ≤′-trans y (≤′-step ≤′-refl)
Set𝓁∈Set𝓀→𝓁<𝓀 {suc 𝓀} {.𝓀} 𝓢𝓮𝓽ₖ₊₁-𝓢𝓮𝓽ₖ = ≤′-refl

𝓁<𝓀→Set𝓁∈Set𝓀 : ∀{𝓀 𝓁} → 𝓁 <′ 𝓀 → (ᶜ (V𝑆𝑒𝑡 𝓁)) == (ᶜ (V𝑆𝑒𝑡 𝓁)) ∈ 𝓢𝓮𝓽 𝓀
𝓁<𝓀→Set𝓁∈Set𝓀 {.(suc 𝓁)} {𝓁} ≤′-refl = 𝓢𝓮𝓽ₖ₊₁-𝓢𝓮𝓽ₖ
𝓁<𝓀→Set𝓁∈Set𝓀 {.(suc _)} {𝓁} (≤′-step 𝓁<𝓀) = 𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ (𝓁<𝓀→Set𝓁∈Set𝓀 𝓁<𝓀)

predicativity : ∀{𝓁} → (ᶜ (V𝑆𝑒𝑡 𝓁)) == (ᶜ (V𝑆𝑒𝑡 𝓁)) ∈ 𝓢𝓮𝓽 𝓁 → ⊥
predicativity Set𝓁∈Set𝓁 = ⊥-elim (<-irrefl refl (≤′⇒≤ (Set𝓁∈Set𝓀→𝓁<𝓀 Set𝓁∈Set𝓁)))

cumulativity : ∀{𝓁 𝓀} → 𝓁 ≤′ 𝓀 → 𝓢𝓮𝓽 𝓁 ⊆ 𝓢𝓮𝓽 𝓀
cumulativity {𝓁} {.𝓁} ≤′-refl a==b∈𝓢𝓮𝓽𝓁 = a==b∈𝓢𝓮𝓽𝓁
cumulativity {𝓁} {(suc 𝓀')} (≤′-step 𝓁<𝓀') a==b∈𝓢𝓮𝓽𝓁 with cumulativity 𝓁<𝓀'
... | Set𝓁⊆Set𝓀' = 𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ (Set𝓁⊆Set𝓀' a==b∈𝓢𝓮𝓽𝓁)
-- we make our live easy with the extra constructor 𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ, which is not present in Abel's thesis
-- it also seems mandatory to have

-- -- TODO show that all these things are PERs/closed under PER formation
-- TODO turn these into instances once proven
-- TODO prove that element function is a function?
Per-𝓢𝓮𝓽₀ : Per 𝓢𝓮𝓽₀
𝓔𝓵₀∶𝓢𝓮𝓽₀⟹Per :  𝓔𝓵₀ ∶ 𝓢𝓮𝓽₀ ⟹Per

Per.per-refl Per-𝓢𝓮𝓽₀ (.(↑⟨ ᶜ V𝑆𝑒𝑡 0 ⟩ _) , inj₁ (𝓢𝓮𝓽₀-NE x)) = 𝓢𝓮𝓽₀-NE (per-refl (memˡ {_} {𝓑𝓸𝓽} x))
Per.per-refl Per-𝓢𝓮𝓽₀ (.(ᶜ V𝑁) , inj₁ 𝓢𝓮𝓽₀-𝑁) = 𝓢𝓮𝓽₀-𝑁
Per.per-refl Per-𝓢𝓮𝓽₀ (.(ᶜ V⊤) , inj₁ 𝓢𝓮𝓽₀-⊤) = 𝓢𝓮𝓽₀-⊤
Per.per-refl Per-𝓢𝓮𝓽₀ (.(ᶜ V⊥) , inj₁ 𝓢𝓮𝓽₀-⊥) = 𝓢𝓮𝓽₀-⊥
Per.per-refl Per-𝓢𝓮𝓽₀ (.(VΠ _ _) , inj₁ (𝓢𝓮𝓽₀-Π {𝐴} {𝐴'} {𝐹} {𝐹'} x x₁)) = 𝓢𝓮𝓽₀-Π (Per.per-refl Per-𝓢𝓮𝓽₀ (memˡ {_} {𝓢𝓮𝓽₀} x)) {!!}
  -- 𝓢𝓮𝓽₀-Π (Per.per-refl Per-𝓢𝓮𝓽₀ (memˡ {_} {𝓢𝓮𝓽₀} x)) prf
  --   where
  --     prf : ∀ {𝑎 𝑎' : 𝕍} → 𝑎 == 𝑎' ∈ 𝓔𝓵₀ 𝐴 →
  --           ∃[ 𝐵 ] ∃[ 𝐵' ] ( (𝐹 · 𝑎 ⇓ 𝐵) × (𝐹 · 𝑎' ⇓ 𝐵') × (𝐵 == 𝐵' ∈ 𝓢𝓮𝓽₀))
  --     prf ElAaa' with x₁ ElAaa' | x₁ (Per.per-sym (per-family 𝓔𝓵₀∶𝓢𝓮𝓽₀⟹Per (memˡ {_} {𝓢𝓮𝓽₀} x)) ElAaa') | x₁ (Per.per-refl (per-family 𝓔𝓵₀∶𝓢𝓮𝓽₀⟹Per (memˡ {_} {𝓢𝓮𝓽₀} x)) (memˡ {_} {𝓔𝓵₀ 𝐴} ElAaa'))
  --     ... | B₁ , B₂ , F·a⇓B₁ , F'·a'⇓B₂ , B₁==B₂ | B₃ , B₄ , F·a'⇓B₃ , F'·a⇓B₄ , B₃==B₄ | B₁' , B₄' , F·a⇓B₁' , F'·a⇓B₄' , B₁'==B₄' rewrite is-fun-· F·a⇓B₁' F·a⇓B₁ | is-fun-· F'·a⇓B₄' F'·a⇓B₄ =
  --      B₁ , (B₃ , F·a⇓B₁ , ( F·a'⇓B₃ , Per.per-trans Per-𝓢𝓮𝓽₀ B₁'==B₄' (Per.per-sym Per-𝓢𝓮𝓽₀ B₃==B₄)))

Per.per-refl Per-𝓢𝓮𝓽₀ (.(↑⟨ ᶜ V𝑆𝑒𝑡 0 ⟩ _) , inj₂ (𝓢𝓮𝓽₀-NE x)) = 𝓢𝓮𝓽₀-NE (per-refl (memʳ {_} {𝓑𝓸𝓽} x))
Per.per-refl Per-𝓢𝓮𝓽₀ (.(ᶜ V𝑁) , inj₂ 𝓢𝓮𝓽₀-𝑁) = 𝓢𝓮𝓽₀-𝑁
Per.per-refl Per-𝓢𝓮𝓽₀ (.(ᶜ V⊤) , inj₂ 𝓢𝓮𝓽₀-⊤) = 𝓢𝓮𝓽₀-⊤
Per.per-refl Per-𝓢𝓮𝓽₀ (.(ᶜ V⊥) , inj₂ 𝓢𝓮𝓽₀-⊥) = 𝓢𝓮𝓽₀-⊥
Per.per-refl Per-𝓢𝓮𝓽₀ (.(VΠ _ _) , inj₂ (𝓢𝓮𝓽₀-Π {𝐴} {𝐴'} {𝐹} {𝐹'} x x₁)) =
  𝓢𝓮𝓽₀-Π ((Per.per-refl Per-𝓢𝓮𝓽₀ (memʳ {_} {𝓢𝓮𝓽₀} x))) (prf ∘ massage)
    where
      massage : 𝓔𝓵₀ 𝐴' ⊆ 𝓔𝓵₀ 𝐴
      massage = Data.Product.proj₂ (respect 𝓔𝓵₀∶𝓢𝓮𝓽₀⟹Per x)

      prf : ∀ {𝑎 𝑎' : 𝕍} → 𝑎 == 𝑎' ∈ 𝓔𝓵₀ 𝐴 →
             ∃[ 𝐵 ] ∃[ 𝐵' ] ( (𝐹' · 𝑎 ⇓ 𝐵) × (𝐹' · 𝑎' ⇓ 𝐵') × (𝐵 == 𝐵' ∈ 𝓢𝓮𝓽₀))
      prf ElAaa' with x₁ ElAaa' | x₁ (Per.per-sym (per-family 𝓔𝓵₀∶𝓢𝓮𝓽₀⟹Per (memˡ {_} {𝓢𝓮𝓽₀} x)) ElAaa') | x₁ (Per.per-refl (per-family 𝓔𝓵₀∶𝓢𝓮𝓽₀⟹Per (memˡ {_} {𝓢𝓮𝓽₀} x)) (memˡ {_} {𝓔𝓵₀ 𝐴} ElAaa'))
      ... | B₁ , B₂ , F·a⇓B₁ , F'·a'⇓B₂ , B₁==B₂ | B₃ , B₄ , F·a'⇓B₃ , F'·a⇓B₄ , B₃==B₄ | B₁' , B₄' , F·a⇓B₁' , F'·a⇓B₄' , B₁'==B₄' rewrite is-fun-· F·a⇓B₁' F·a⇓B₁ | is-fun-· F'·a⇓B₄' F'·a⇓B₄ =
       B₄ , (B₂ , (F'·a⇓B₄ , (F'·a'⇓B₂ , Per.per-trans Per-𝓢𝓮𝓽₀ (Per.per-sym Per-𝓢𝓮𝓽₀ B₁'==B₄') B₁==B₂)))

Per.per-sym Per-𝓢𝓮𝓽₀ (𝓢𝓮𝓽₀-NE x) = 𝓢𝓮𝓽₀-NE (per-sym x)
Per.per-sym Per-𝓢𝓮𝓽₀ 𝓢𝓮𝓽₀-𝑁 = 𝓢𝓮𝓽₀-𝑁
Per.per-sym Per-𝓢𝓮𝓽₀ 𝓢𝓮𝓽₀-⊤ = 𝓢𝓮𝓽₀-⊤
Per.per-sym Per-𝓢𝓮𝓽₀ 𝓢𝓮𝓽₀-⊥ = 𝓢𝓮𝓽₀-⊥
Per.per-sym Per-𝓢𝓮𝓽₀ (𝓢𝓮𝓽₀-Π {𝐴} {𝐴'} {𝐹} {𝐹'} A==A' F==F') = 𝓢𝓮𝓽₀-Π (Per.per-sym Per-𝓢𝓮𝓽₀ A==A') (prf ∘ massage)
  where
    massage : 𝓔𝓵₀ 𝐴' ⊆ 𝓔𝓵₀ 𝐴
    massage = Data.Product.proj₂ (respect 𝓔𝓵₀∶𝓢𝓮𝓽₀⟹Per A==A')

    prf : ∀ {𝑎} {𝑎'} →
      𝑎' == 𝑎 ∈ 𝓔𝓵₀ 𝐴 →
      ∃-syntax
      (λ 𝐵' →
         ∃-syntax (λ 𝐵 → (𝐹' · 𝑎' ⇓ 𝐵') × (𝐹 · 𝑎 ⇓ 𝐵) × (𝐵' == 𝐵 ∈ 𝓢𝓮𝓽₀)))
    prf ElAa'a with F==F' (Per.per-sym (per-family 𝓔𝓵₀∶𝓢𝓮𝓽₀⟹Per (memˡ {_} {𝓢𝓮𝓽₀} A==A')) ElAa'a)
    ... | B , B' , 𝐹·𝑎⇓B , 𝐹'·𝑎'⇓B' , B==B' = B' , (B , (𝐹'·𝑎'⇓B' , (𝐹·𝑎⇓B , (Per.per-sym Per-𝓢𝓮𝓽₀ B==B')))) -- this'll cause termination check to complain :(
Per.per-trans Per-𝓢𝓮𝓽₀ = {!!}


respect 𝓔𝓵₀∶𝓢𝓮𝓽₀⟹Per = {!!}
Per.per-refl  (per-family 𝓔𝓵₀∶𝓢𝓮𝓽₀⟹Per {𝐴} 𝐴∈𝓢𝓮𝓽₀) = {!!}
Per.per-sym   (per-family 𝓔𝓵₀∶𝓢𝓮𝓽₀⟹Per {𝐴} 𝐴∈𝓢𝓮𝓽₀) = {!!}
Per.per-trans (per-family 𝓔𝓵₀∶𝓢𝓮𝓽₀⟹Per {𝐴} 𝐴∈𝓢𝓮𝓽₀) = {!!}



-- Set of all semantic types is the limit 𝓢𝓮𝓽ω
𝓢𝓮𝓽ω : Rel
𝓢𝓮𝓽ω A B = ∃[ 𝓁 ]( A == B ∈ (𝓢𝓮𝓽 𝓁) )
𝒯𝓎𝓅ℯ = 𝓢𝓮𝓽ω

-- Value interpretation is the limit 𝓔𝓵ω
𝓔𝓵ω : 𝕍 → Rel
𝓔𝓵ω 𝑇 𝑎 𝑏 = ∃[ 𝓁 ]( 𝑎 == 𝑏 ∈ 𝓔𝓵 𝓁 𝑇 )

-- Interpretation of syntactic types into semantic types (PERs)
open import dsube.NbE using (⟦_⟧_⇓_)
open import dsube.Syntax using (Exp)

data [_]_⇓_ : Exp → Env → Rel → Set where
  ty-rel : ∀{T ρ 𝑇} →
     ⟦ T ⟧ ρ ⇓ 𝑇 →
     -----------------
     [ T ] ρ ⇓ 𝓔𝓵ω 𝑇

-- -- TODO show that all these things live in the candidate space

-- -- TODO: semantically well-formed contexts and context extension (p. 46)

-- -- TODO: for each of the syntactic judgments, define the semantic jugdements (p. 46)
-- -- TODO: esp: how to deal with subtyping?

-- -- TODO : typed candidate spaces (p. 47)

-- -- TODO : completeness proof (end of 4.5, p. 48)


-- ```
