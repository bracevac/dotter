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
open import Data.Unit using (⊤)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _≤_; _<_; _≤′_; _<′_; _⊔_; _∸_; _≡ᵇ_)
open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to _⊔ˡ_)
open import dsube.NbE

-- TODO it seems worthwhile using the stdlib's rich support for binary relations instead
-- of our own ad-hoc definitions
-- Binary relations over a type
Rel₂ : ∀{ℓ} → Set ℓ → Set (lsuc ℓ)
Rel₂ {ℓ} 𝓐  = 𝓐 → 𝓐 → Set ℓ

-- empty relation
Rel₂⊥ : ∀ {T} → Rel₂ T
Rel₂⊥ _ _ = ⊥

-- Membership of an element in the domain of a given relation
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

_≡Rel₂_ :  ∀{𝓐 : Set} → Rel₂ 𝓐 → Rel₂ 𝓐 → Set
P ≡Rel₂ Q = P ⊆ Q × Q ⊆ P

≡→≡Rel₂ : ∀{𝓐 : Set}{P Q : Rel₂ 𝓐} → P ≡ Q → P ≡Rel₂ Q
≡→≡Rel₂ refl = (λ z → z) , λ z → z

≡Rel₂-refl : ∀{𝓐 : Set}{R : Rel₂ 𝓐} → R ≡Rel₂ R
≡Rel₂-refl {_} {R} = (λ x → x) , (λ x → x)

≡Rel₂-sym : ∀{𝓐 : Set}{R S : Rel₂ 𝓐} → R ≡Rel₂ S → S ≡Rel₂ R
≡Rel₂-sym (R⊆S , S⊆R) = S⊆R , R⊆S

≡Rel₂-trans : ∀{𝓐 : Set}{R Q S : Rel₂ 𝓐} → R ≡Rel₂ Q → Q ≡Rel₂ S → R ≡Rel₂ S
≡Rel₂-trans (R⊆Q , Q⊆R) (Q⊆S , S⊆Q) = (λ x → Q⊆S (R⊆Q x)) , (λ x → Q⊆R (S⊆Q x))

≡Rel₂-∈ : ∀{𝓐 : Set}{R S : Rel₂ 𝓐} → R ≡Rel₂ S → ∀{a b} → R a b → S a b
≡Rel₂-∈ (fst , _) = fst


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
open Per

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
Per-𝓣𝓸𝓹 : Per 𝓣𝓸𝓹
per-refl  Per-𝓣𝓸𝓹 (_ , inj₁ Taa') n with Taa' n
... | eᴺᶠ , ℜᴺᶠ⟨n⟩a⇓eᴺᶠ , _ = eᴺᶠ , ℜᴺᶠ⟨n⟩a⇓eᴺᶠ , ℜᴺᶠ⟨n⟩a⇓eᴺᶠ
per-refl  Per-𝓣𝓸𝓹 (_ , inj₂ Ta'a) n with Ta'a n
... | eᴺᶠ , _ , ℜᴺᶠ⟨n⟩a⇓eᴺᶠ = eᴺᶠ , ℜᴺᶠ⟨n⟩a⇓eᴺᶠ , ℜᴺᶠ⟨n⟩a⇓eᴺᶠ
per-sym   Per-𝓣𝓸𝓹 Taa' n with Taa' n
... | eᴺᶠ , fst , snd = eᴺᶠ , snd , fst
per-trans Per-𝓣𝓸𝓹 Tab Tbc n  with Tab n | Tbc n
... | eab , fst , snd | ebc , fst₁ , snd₁ rewrite is-fun-ℜᴺᶠ snd fst₁ = ebc , fst , snd₁

Per-𝓑𝓸𝓽 : Per 𝓑𝓸𝓽
per-refl  Per-𝓑𝓸𝓽 (_ , inj₁ Botaa') n with Botaa' n
... | x , fst , _ = x , fst , fst
per-refl  Per-𝓑𝓸𝓽 (_ , inj₂ Bota'a) n with Bota'a n
... | x , _ , snd = x , snd , snd
per-sym   Per-𝓑𝓸𝓽 Botaa' n with Botaa' n
... | x , fst , snd = x , snd , fst
per-trans Per-𝓑𝓸𝓽 Botab Botbc n with Botab n | Botbc n
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

Per-𝓝𝓪𝓽 : Per 𝓝𝓪𝓽
per-refl  Per-𝓝𝓪𝓽 (_ , inj₁ 𝓝-𝑛) = 𝓝-𝑛
per-refl  Per-𝓝𝓪𝓽 (_ , inj₁ (𝓝-Ne {nv} {nv'} x)) = 𝓝-Ne (per-refl Per-𝓑𝓸𝓽 ( nv' , inj₁ x))
per-refl  Per-𝓝𝓪𝓽 (_ , inj₂ 𝓝-𝑛) = 𝓝-𝑛
per-refl  Per-𝓝𝓪𝓽 (_ , inj₂ (𝓝-Ne {nv} {nv'} x)) = 𝓝-Ne (per-refl Per-𝓑𝓸𝓽 ( nv , inj₂ x))
per-sym   Per-𝓝𝓪𝓽 𝓝-𝑛 = 𝓝-𝑛
per-sym   Per-𝓝𝓪𝓽 (𝓝-Ne x) = 𝓝-Ne (per-sym Per-𝓑𝓸𝓽 x)
per-trans Per-𝓝𝓪𝓽 𝓝-𝑛 𝓝-𝑛 = 𝓝-𝑛
per-trans Per-𝓝𝓪𝓽 (𝓝-Ne x) (𝓝-Ne x₁) = 𝓝-Ne (per-trans Per-𝓑𝓸𝓽 x x₁)

-- PERs over a domain indexed by a PER
record _∶_⟹Per {D : Set} (F : D → Rel₂ D) (𝓐 : Rel₂ D) : Set₁ where
  field
    respect : ∀{a a'} → 𝓐 a a' → F a ≡Rel₂ F a'
    per-family : ∀{a} → a ∈ 𝓐 → Per (F a)
open _∶_⟹Per

-- semantic function space
𝓟𝓲 : ∀(𝓐 : Rel) → (𝕍 → Rel) → Rel
𝓟𝓲 𝓐 𝓕 f f' = ∀{a a'} → a == a' ∈ 𝓐 → ∃[ b ] ∃[ b' ] ((f · a ⇓ b) × (f' · a' ⇓ b' ) × (b == b' ∈ (𝓕 a)))

-- 𝓟𝓲 is a PER if its arguments are
Per-𝓟𝓲 : ∀{𝓐 : Rel}{𝓕 : (𝕍 → Rel)} → Per 𝓐 → (𝓕 ∶ 𝓐 ⟹Per) → Per (𝓟𝓲 𝓐 𝓕)
per-refl  (Per-𝓟𝓲 Per-𝓐 𝓕∶𝓐⟹Per) {f} (f' , inj₁ PiAFff') {a} {a'} Aaa' with PiAFff' Aaa' | PiAFff' (per-sym Per-𝓐 Aaa')
... | b , c , fa⇓b , f'a'⇓c , Fabc | b' , c' , fa'⇓b' , f'a⇓c' , Fa'b'c' with per-refl  Per-𝓐 {a'} (memʳ Aaa')
... | Aa'a' with  PiAFff' Aa'a'
... | d , d' , fa'⇓d , f'a'⇓d' , Fa'dd' = b , b' , fa⇓b , fa'⇓b' , {!!}
--  1. show that Fa'dd' implies Facb' from · being a function and respect property of 𝓕
--  2. With Fabc and PER transitivity, conclude Fabb'

per-refl  (Per-𝓟𝓲 Per-𝓐 𝓕∶𝓐⟹Per) {f} (_ , inj₂ y) = {!!}
-- should be entirely symmetric to the first case

per-sym   (Per-𝓟𝓲 Per-𝓐 𝓕∶𝓐⟹Per) = {!!}

per-trans (Per-𝓟𝓲 Per-𝓐 𝓕∶𝓐⟹Per) = {!!}

open import dsube.Syntax using (ℒ)

-- Neutral type interp -- TODO not sure about the definition: this is one of the very hand-wavy places in thesis
data 𝓥Ty-Ne (𝓁 : ℒ) (NE : 𝕍ᴺᵉ) : Rel where
  𝓥Ty-Ne-mem : ∀ {NE₁ ne₁ NE₂ ne₂} →
    NE == NE₁ ∈ 𝓑𝓸𝓽 →
    NE == NE₂ ∈ 𝓑𝓸𝓽 →
    ne₁ == ne₂ ∈ 𝓑𝓸𝓽 →
    --------------------------------------------------------------------------
    ↑⟨ (↑⟨ (ᶜ (V𝑆𝑒𝑡 𝓁)) ⟩ NE₁) ⟩ ne₁ == ↑⟨ (↑⟨ (ᶜ (V𝑆𝑒𝑡 𝓁)) ⟩ NE₂) ⟩ ne₂ ∈ (𝓥Ty-Ne 𝓁 NE)

Per-𝓥Ty-Ne : ∀{𝓁 NE} → Per (𝓥Ty-Ne 𝓁 NE)
per-refl  Per-𝓥Ty-Ne = {!!}
per-sym   Per-𝓥Ty-Ne = {!!}
per-trans Per-𝓥Ty-Ne = {!!}

-- ⊥ type interp
-- TODO not sure either, but to fulfill the candidate space requirement, V⊥ cannot be empty
-- it appears reasonable to take the total relation, as interpreting a term at type V⊥ logically
-- implies arbitrary things
𝓥⊥ : Rel
𝓥⊥ _ _ = ⊤

Per-𝓥⊥ : Per 𝓥⊥
per-refl  Per-𝓥⊥ = {!!}
per-sym   Per-𝓥⊥ = {!!}
per-trans Per-𝓥⊥ = {!!}

-- ⊤ type interp
data 𝓥⊤ : Rel where
  𝓥⊤-ne :  ∀{nv nv'} →
    nv == nv' ∈ 𝓑𝓸𝓽 →
    -----------------------------------
    ↑⟨ ᶜ V⊤ ⟩ nv == ↑⟨ ᶜ V⊤ ⟩ nv' ∈ 𝓥⊤

  𝓥⊤-val : ∀ {v} →
    ---------------
    v == v ∈ 𝓥⊤

Per-𝓥⊤ : Per 𝓥⊤
per-refl  Per-𝓥⊤ = {!!}
per-sym   Per-𝓥⊤ = {!!}
per-trans Per-𝓥⊤ = {!!}

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

Per-𝓥Type : ∀{𝓢 𝓣 : Rel} → Per 𝓢 → Per 𝓣 → Per (𝓥Type 𝓢 𝓣)
per-refl  (Per-𝓥Type Per-𝓢 Per-𝓣) = {!!}
per-sym   (Per-𝓥Type Per-𝓢 Per-𝓣) = {!!}
per-trans (Per-𝓥Type Per-𝓢 Per-𝓣) = {!!}

-- First, the universe at level 0
data 𝓢𝓮𝓽₀ : Rel
𝓔𝓵₀ : 𝕍 → Rel

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

𝓐𝓹𝓹 : (𝐹 : 𝕍) → (𝑎 : 𝕍) → (𝓕 : 𝕍 → Rel) → Rel
𝓐𝓹𝓹 𝐹 𝑎 𝓕 x y = ∃[ 𝐵 ] ( (𝐹 · 𝑎 ⇓ 𝐵) × (x == y ∈ 𝓕 𝐵) )

𝓔𝓵₀ (ᶜ V𝑁) = 𝓝𝓪𝓽
𝓔𝓵₀ (ᶜ V⊤) = 𝓥⊤
𝓔𝓵₀ (ᶜ V⊥) = 𝓥⊥
𝓔𝓵₀ (↑⟨ (ᶜ (V𝑆𝑒𝑡 0)) ⟩ NE) = 𝓥Ty-Ne 0 NE
𝓔𝓵₀ (VΠ 𝐴 𝐹) = 𝓟𝓲 (𝓔𝓵₀ 𝐴) λ 𝑎 → 𝓐𝓹𝓹 𝐹 𝑎 𝓔𝓵₀  -- TODO
𝓔𝓵₀ _ = Rel₂⊥

data 𝓢𝓮𝓽ₖ₊₁ (𝓀 : ℒ) (𝓢ₖ : Rel) (𝓔𝓵ₖ : 𝕍 → Rel) : Rel
𝓔𝓵ₖ₊₁ : ℒ → Rel → (𝕍 → Rel) → 𝕍 → Rel

data 𝓢𝓮𝓽ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ where
  𝓢𝓮𝓽ₖ₊₁-NE : ∀{NE NE'} →
    NE == NE' ∈ 𝓑𝓸𝓽 →
    ------------------------------------------------------------------------
    ↑⟨ (ᶜ (V𝑆𝑒𝑡 (suc 𝓀))) ⟩ NE == ↑⟨ (ᶜ (V𝑆𝑒𝑡 (suc 𝓀))) ⟩ NE' ∈ 𝓢𝓮𝓽ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ

  𝓢𝓮𝓽ₖ₊₁-𝑁 : (ᶜ V𝑁) == (ᶜ V𝑁) ∈ 𝓢𝓮𝓽ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ

  𝓢𝓮𝓽ₖ₊₁-⊤ : (ᶜ V⊤) == (ᶜ V⊤) ∈ 𝓢𝓮𝓽ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ

  𝓢𝓮𝓽ₖ₊₁-⊥ : (ᶜ V⊥) == (ᶜ V⊥) ∈ 𝓢𝓮𝓽ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ

  𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ : ∀{𝐴 𝐵} →
    𝐴 == 𝐵 ∈ 𝓢ₖ →
    --------------------------
    𝐴 == 𝐵 ∈ (𝓢𝓮𝓽ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ)

  𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ : ∀{𝑆 𝑆' 𝑇 𝑇'} →
    𝑆 == 𝑆' ∈ 𝓢ₖ →
    𝑇 == 𝑇' ∈ 𝓢ₖ →
    -----------------------------------------------
    ⟪Type 𝑆 ⋯ 𝑇 ⟫ == ⟪Type 𝑆' ⋯ 𝑇' ⟫ ∈ 𝓢𝓮𝓽ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ

  𝓢𝓮𝓽ₖ₊₁-𝓢𝓮𝓽ₖ :
    (ᶜ (V𝑆𝑒𝑡 𝓀)) == (ᶜ (V𝑆𝑒𝑡 𝓀)) ∈ 𝓢𝓮𝓽ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ

  𝓢𝓮𝓽ₖ₊₁-Π : ∀{𝐴 𝐴' 𝐹 𝐹'} →
    𝐴 == 𝐴' ∈ 𝓢𝓮𝓽ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ →
    (∀{𝑎 𝑎'} → 𝑎 == 𝑎' ∈ (𝓔𝓵ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ 𝐴) →
               (∃[ 𝐵 ] ∃[ 𝐵' ] ( (𝐹 · 𝑎 ⇓ 𝐵) × (𝐹' · 𝑎' ⇓ 𝐵') × (𝐵 == 𝐵' ∈ 𝓢𝓮𝓽ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ) ))) →
    --------------------------------------------------------------------------------------------
    VΠ 𝐴 𝐹 == VΠ 𝐴' 𝐹' ∈ 𝓢𝓮𝓽ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ

-- cumulative interpretation of the V𝑆𝑒𝑡 𝓁 case in 𝓔𝓵ₖ₊₁ below
-- we could have also used combinators on relations instead
data 𝓥𝑆𝑒𝑡≤ (𝓁 𝓀 : ℒ) (𝓢ₖ : Rel) (𝓔𝓵ₖ : 𝕍 → Rel) : Rel where
  -- either 𝓁 is the immediate predecessor universe 𝓀
  𝓥𝑆𝑒𝑡≤-pred : 𝓁 ≡ 𝓀 →
            ∀{𝐴 𝐴'} →
            𝐴 == 𝐴' ∈ 𝓢ₖ → -- in which case we refer to the predecessor universe
            ----------------------------
            𝐴 == 𝐴' ∈ (𝓥𝑆𝑒𝑡≤ 𝓁 𝓀 𝓢ₖ 𝓔𝓵ₖ)

  -- or a lower universe
  𝓥𝑆𝑒𝑡≤-below : 𝓁 < 𝓀 →
            ∀{𝐴 𝐴'} →
             -- in which case we defer to the interpretation of the predecessor universe's elements
            𝐴 == 𝐴' ∈ 𝓔𝓵ₖ (ᶜ V𝑆𝑒𝑡 𝓁) →
            ----------------------------
            𝐴 == 𝐴' ∈ (𝓥𝑆𝑒𝑡≤ 𝓁 𝓀 𝓢ₖ 𝓔𝓵ₖ)

open import Data.Nat using (compare; Ordering)
open Ordering
𝓔𝓵ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ (ᶜ V𝑁) = 𝓝𝓪𝓽
𝓔𝓵ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ (ᶜ V⊤) = 𝓥⊤
𝓔𝓵ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ (ᶜ V⊥) = 𝓥⊥
𝓔𝓵ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ (ᶜ V𝑆𝑒𝑡 𝓀') = 𝓥𝑆𝑒𝑡≤ 𝓀' 𝓀 𝓢ₖ 𝓔𝓵ₖ
𝓔𝓵ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ ⟪Type 𝑆 ⋯ 𝑇 ⟫ = 𝓥Type (𝓔𝓵ₖ 𝑆) (𝓔𝓵ₖ 𝑇)
𝓔𝓵ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ (↑⟨ (ᶜ (V𝑆𝑒𝑡 (suc 𝓀'))) ⟩ NE) with 𝓀 ≡ᵇ 𝓀' -- TODO use similar construction to 𝓥𝑆𝑒𝑡≤
... | true = 𝓥Ty-Ne (suc 𝓀) NE
... | _ = Rel₂⊥
𝓔𝓵ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ (VΠ 𝐴 𝐹) = 𝓟𝓲 (𝓔𝓵ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ 𝐴) λ 𝑎 → 𝓐𝓹𝓹 𝐹 𝑎 (𝓔𝓵ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ)
𝓔𝓵ₖ₊₁ _ _ _ _ = Rel₂⊥

𝓢𝓮𝓽 : ℒ → Rel
𝓔𝓵 : ℒ → 𝕍 → Rel

𝓢𝓮𝓽 0 = 𝓢𝓮𝓽₀
𝓢𝓮𝓽 (suc 𝓀) = 𝓢𝓮𝓽ₖ₊₁ 𝓀 (𝓢𝓮𝓽 𝓀) (𝓔𝓵 𝓀)

𝓔𝓵 0 = 𝓔𝓵₀
𝓔𝓵 (suc 𝓀) = 𝓔𝓵ₖ₊₁ 𝓀 (𝓢𝓮𝓽 𝓀) (𝓔𝓵 𝓀)

-- TODO Using the indexed 𝓢𝓮𝓽 and 𝓔𝓵 definitions, assert that the rules/equations as depicted in Abel p.46 are admissible
-- TOOD It might also be beneficial if we have proper inversion lemmas for these
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

𝓢𝓮𝓽ₗ∈𝓢𝓮𝓽ₖ : ∀{𝓁 𝓀} → 𝓁 < 𝓀 → (ᶜ (V𝑆𝑒𝑡 𝓁)) == (ᶜ (V𝑆𝑒𝑡 𝓁)) ∈ 𝓢𝓮𝓽 𝓀

𝓢𝓮𝓽-Π : ∀{𝓀 𝐴 𝐴' 𝐹 𝐹'} →
  𝐴 == 𝐴' ∈ 𝓢𝓮𝓽 𝓀 →
  (∀{𝑎 𝑎'} → 𝑎 == 𝑎' ∈ (𝓔𝓵 𝓀 𝐴) →
             (∃[ 𝐵 ] ∃[ 𝐵' ] ( (𝐹 · 𝑎 ⇓ 𝐵) × (𝐹' · 𝑎' ⇓ 𝐵') × (𝐵 == 𝐵' ∈ 𝓢𝓮𝓽 𝓀) ))) →
  -------------------------------------------------------------------------------------
  VΠ 𝐴 𝐹 == VΠ 𝐴' 𝐹' ∈ 𝓢𝓮𝓽 𝓀

𝓔𝓵-𝑁 : ∀ {𝓀} → 𝓔𝓵 𝓀 (ᶜ V𝑁) ≡ 𝓝𝓪𝓽

𝓔𝓵-⊤ : ∀ {𝓀} → 𝓔𝓵 𝓀 (ᶜ V⊤) ≡ 𝓥⊤

𝓔𝓵-⊥ : ∀ {𝓀} → 𝓔𝓵 𝓀 (ᶜ V⊥) ≡ 𝓥⊥

open import Data.Nat.Properties using (<-irrefl; ≤′⇒≤)
open _≤′_
𝓔𝓵-𝑆𝑒𝑡 : ∀ {𝓁 𝓀} → suc 𝓁 ≤′ 𝓀 → 𝓔𝓵 𝓀 (ᶜ (V𝑆𝑒𝑡 𝓁)) ≡Rel₂ 𝓢𝓮𝓽 𝓁
𝓔𝓵-𝑆𝑒𝑡 {𝓁} {.(suc 𝓁)} ≤′-refl =
   (λ{ (𝓥𝑆𝑒𝑡≤-pred x x₁) → x₁ ; (𝓥𝑆𝑒𝑡≤-below x x₁) → ⊥-elim (<-irrefl refl x)}) ,
   𝓥𝑆𝑒𝑡≤-pred refl
𝓔𝓵-𝑆𝑒𝑡 {𝓁} {(suc 𝓀')} (≤′-step 𝓁+1≤𝓀') with 𝓔𝓵-𝑆𝑒𝑡 𝓁+1≤𝓀'
... | fst , snd = left , right
  where
    left : 𝓥𝑆𝑒𝑡≤ 𝓁 𝓀' (𝓢𝓮𝓽 𝓀') (𝓔𝓵 𝓀') ⊆ 𝓢𝓮𝓽 𝓁
    left (𝓥𝑆𝑒𝑡≤-pred x x₁) rewrite x = x₁
    left (𝓥𝑆𝑒𝑡≤-below x x₁) = fst x₁
    right : 𝓢𝓮𝓽 𝓁 ⊆  𝓥𝑆𝑒𝑡≤ 𝓁 𝓀' (𝓢𝓮𝓽 𝓀') (𝓔𝓵 𝓀')
    right Set𝓁ab =  𝓥𝑆𝑒𝑡≤-below (≤′⇒≤ 𝓁+1≤𝓀') (snd Set𝓁ab)

𝓔𝓵-⟪Type⋯⟫ : ∀ {𝓀 𝑆 𝑇} → 𝓔𝓵 (suc 𝓀) ⟪Type 𝑆 ⋯ 𝑇 ⟫ ≡ 𝓥Type (𝓔𝓵 𝓀 𝑆) (𝓔𝓵 𝓀 𝑇)


𝓔𝓵-NE : ∀ {𝓀 NE} → 𝓔𝓵 𝓀 (↑⟨ (ᶜ (V𝑆𝑒𝑡 𝓀)) ⟩ NE) ≡ 𝓥Ty-Ne 𝓀 NE
𝓔𝓵-NE = {!!}

-- 𝓔𝓵ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ (VΠ 𝐴 𝐹) = 𝓟𝓲 (𝓔𝓵ₖ₊₁ 𝓀 𝓢ₖ 𝓔𝓵ₖ 𝐴) {!!}  -- TODO

-- proofs are mostly straightforward
𝓔𝓵-𝑁 {zero} = refl
𝓔𝓵-𝑁 {suc 𝓀} = refl

𝓔𝓵-⊤ {zero} = refl
𝓔𝓵-⊤ {suc 𝓀} = refl

𝓔𝓵-⊥ {zero} = refl
𝓔𝓵-⊥ {suc 𝓀} = refl

𝓔𝓵-⟪Type⋯⟫ = refl

𝓢𝓮𝓽-NE {zero} = 𝓢𝓮𝓽₀-NE
𝓢𝓮𝓽-NE {suc 𝓀} = 𝓢𝓮𝓽ₖ₊₁-NE

𝓢𝓮𝓽-𝑁 {zero} = 𝓢𝓮𝓽₀-𝑁
𝓢𝓮𝓽-𝑁 {suc 𝓀} = 𝓢𝓮𝓽ₖ₊₁-𝑁

𝓢𝓮𝓽-⊤ {zero} = 𝓢𝓮𝓽₀-⊤
𝓢𝓮𝓽-⊤ {suc 𝓀} = 𝓢𝓮𝓽ₖ₊₁-⊤

𝓢𝓮𝓽-⊥ {zero} = 𝓢𝓮𝓽₀-⊥
𝓢𝓮𝓽-⊥ {suc 𝓀} = 𝓢𝓮𝓽ₖ₊₁-⊥

𝓢𝓮𝓽-⟪Type⋯⟫ 𝑆==𝑆' 𝑇==𝑇' = 𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ 𝑆==𝑆' 𝑇==𝑇'

𝓢𝓮𝓽ₗ∈𝓢𝓮𝓽ₖ (_≤_.s≤s {_} {zero} _≤_.z≤n) =  𝓢𝓮𝓽ₖ₊₁-𝓢𝓮𝓽ₖ
𝓢𝓮𝓽ₗ∈𝓢𝓮𝓽ₖ (_≤_.s≤s {_} {suc n} _≤_.z≤n) = {!!}
𝓢𝓮𝓽ₗ∈𝓢𝓮𝓽ₖ (_≤_.s≤s (_≤_.s≤s 𝓁≤n)) = {!!}

𝓢𝓮𝓽-Π {𝓀} = {!!}

-- another litmus test
predicativity : ∀{𝓁} → (ᶜ (V𝑆𝑒𝑡 𝓁)) == (ᶜ (V𝑆𝑒𝑡 𝓁)) ∈ 𝓢𝓮𝓽 𝓁 → ⊥
predicativity {suc 𝓁} (𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ x) = {!!}

cumulativity : ∀{𝓁 𝓀} → 𝓁 ≤′ 𝓀 → 𝓢𝓮𝓽 𝓁 ⊆ 𝓢𝓮𝓽 𝓀
cumulativity {𝓁} {.𝓁} ≤′-refl a==b∈𝓢𝓮𝓽𝓁 = a==b∈𝓢𝓮𝓽𝓁
cumulativity {𝓁} {(suc 𝓀')} (≤′-step 𝓁<𝓀') a==b∈𝓢𝓮𝓽𝓁 with cumulativity 𝓁<𝓀'
... | Set𝓁⊆Set𝓀' = 𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ (Set𝓁⊆Set𝓀' a==b∈𝓢𝓮𝓽𝓁)
-- we make our live easy with the extra constructor 𝓢𝓮𝓽ₖ₊₁-⊇𝓢ₖ, which is not present in Abel's thesis
-- it also seems mandatory to have


𝓢𝓮𝓽ω : Rel
𝓢𝓮𝓽ω A B = ∃[ 𝓁 ]( A == B ∈ (𝓢𝓮𝓽 𝓁) )

-- Semantic interp of all types
𝒯𝓎𝓅ℯ = 𝓢𝓮𝓽ω

-- the limit 𝓔𝓵ω
-- first, we define the domain of the 𝓔𝓵-family (which are the semantic types)
data Dom-𝓔𝓵 (𝓁 : ℒ) (v : 𝕍) : Set where
--- todo

data [_]⇓_ : 𝕍 → Rel → Set where
  𝓔𝓵ω : ∀{v 𝓁} →
    {Dom-𝓔𝓵 𝓁 v} → -- this prevents a v that yields the empty relation
    ---------------
    [ v ]⇓ (𝓔𝓵 𝓁 v)

-- type interpretation into PERs
open import dsube.NbE using (⟦_⟧_⇓_)
open import dsube.Syntax using (Exp)

data 【_】_⇓_ : Exp → Env → Rel → Set where
  ty-rel : ∀{T ρ 𝑇 𝓣} →
     ⟦ T ⟧ ρ ⇓ 𝑇 →
     [ 𝑇 ]⇓ 𝓣 →
     -------------
     【 T 】 ρ ⇓ 𝓣

-- TODO show that all these things are PERs/closed under PER formation
-- element function must respect PER equality
-- TODO show that all these things live in the candidate space

-- TODO: semantically well-formed contexts and context extension (p. 46)

-- TODO: for each of the syntactic judgments, define the semantic jugdements (p. 46)
-- TODO: esp: how to deal with subtyping?

-- TODO : typed candidate spaces (p. 47)

-- TODO : completeness proof (end of 4.5, p. 48)


```
