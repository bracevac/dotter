# Partial Equivalence Relations (PERs)

```agda
module dsube.PER where

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
open import dsube.Relations
open import dsube.RelFun
open Rel-family {{...}}

-- a partial equivalence relation (PER) is an equivalence relation on its domain
record Per {𝓐} (R : Rel₂ 𝓐) : Set where
  field
    per-sym   : Sym R
    per-trans : Trans R
open Per {{...}}

per-refl : ∀{𝓐}{R : Rel₂ 𝓐} → {{Per R}} → ∀ {a} → a ∈ R → R a a
per-refl (memˡ x) = per-trans x (per-sym x)
per-refl (memʳ x) = per-trans (per-sym x) x

Per-≡ᴿ : ∀{T}{𝓐 𝓑 : Rel₂ T} → 𝓐 ≡ᴿ 𝓑 → Per 𝓐 → Per 𝓑
Per.per-sym   (Per-≡ᴿ (𝓐⊆𝓑 , 𝓑⊆𝓐) Per-𝓐) = 𝓐⊆𝓑 ∘ (per-sym {{Per-𝓐}}) ∘ 𝓑⊆𝓐
Per.per-trans (Per-≡ᴿ (𝓐⊆𝓑 , 𝓑⊆𝓐) Per-𝓐) a==b b==c = 𝓐⊆𝓑 (per-trans {{Per-𝓐}} (𝓑⊆𝓐 a==b) (𝓑⊆𝓐 b==c))
```
# Elementary PERs for the Types of Dᵉ<:>
```agda
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
... | eab , fst , snd | ebc , fst₁ , snd₁ rewrite det-ℜᴺᶠ snd fst₁ = ebc , fst , snd₁

instance Per-𝓑𝓸𝓽 : Per 𝓑𝓸𝓽
per-sym   {{Per-𝓑𝓸𝓽}} Botaa' n with Botaa' n
... | x , fst , snd = x , snd , fst
per-trans {{Per-𝓑𝓸𝓽}} Botab Botbc n with Botab n | Botbc n
... | x , fst , snd | y , fst₁ , snd₁ rewrite det-ℜᴺᵉ snd fst₁ = y , fst , snd₁

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
𝓥⊥ = ⊤ᴿ

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

-- The dependent product over relations, building on the previous construction
ℿ : (𝓐 : Rel) → (∀{𝑎} → 𝑎 ∈ 𝓐 → Rel) → Rel
ℿ 𝓐 𝓕 𝑓 𝑓' =  ∀{𝑎 𝑎'} → (a==a' : 𝑎 == 𝑎' ∈ 𝓐) → [ 𝑓 == 𝑓' ∙ 𝑎 == 𝑎' ]∈ (𝓕 (memˡ a==a'))

-- ℿ is closed under the PER property, we show this is a slightly less general way than what is possible, to cater to our universe encoding later
ℿ-sym :  ∀{U : 𝕍 → Set}{𝐴 𝐹} → {El : U ⟹ Rel} → {U𝐴 : U 𝐴} →
         Sym (El U𝐴) →
         (U𝐹 : [ 𝐹 ∙ (El U𝐴) ]⟹ U) →
         {{Rel-family El U𝐴 U𝐹}} →
         (∀{𝑎 𝑎'} → (a==a' : 𝑎 == 𝑎' ∈ El U𝐴) → Sym (El ⌜ U𝐹 ∙ˡ a==a' ⌝)) →
         Sym (ℿ (El U𝐴) (λ 𝑎 → El ⌜ U𝐹 𝑎 ⌝))
ℿ-sym dom-sym U𝐹 cod-sym {f} {g} f==g a==a' with (dom-sym a==a')
... | a'==a with f==g a'==a | cod-unif² a'==a
... | [⁈-rel ELFa'-f·a'==g·a ]
    | ELFa'⊆ELFa , _ with cod-sym a'==a
... | sym-ELF·a' with U𝐹 (memˡ a'==a)
... | [⁈ F·a' ] with ELFa'⊆ELFa (sym-ELF·a' ELFa'-f·a'==g·a)
... | ELFa-g·a==f·a' rewrite (cod-unif¹ (memʳ a'==a) (memˡ a==a'))
      = [⁈-rel ELFa-g·a==f·a' ]

ℿ-trans : ∀{U : 𝕍 → Set}{𝐴 𝐹} → {El : U ⟹ Rel} → {U𝐴 : U 𝐴} →
         Sym (El U𝐴) →
         Trans (El U𝐴) →
         (U𝐹 : [ 𝐹 ∙ (El U𝐴) ]⟹ U) →
         {{Rel-family El U𝐴 U𝐹}} →
         (∀{𝑎 𝑎'} → (a==a' : 𝑎 == 𝑎' ∈ El U𝐴) → Trans (El ⌜ U𝐹 ∙ˡ a==a' ⌝)) →
         Trans (ℿ (El U𝐴) (λ 𝑎 → El ⌜ U𝐹 𝑎 ⌝))
ℿ-trans dom-sym dom-trans UF cod-trans {f} {f'} {g} f==f' f'==g a==a' with (dom-trans (dom-sym a==a') a==a')
... | a'==a' with f==f' a==a' | f'==g a'==a' | cod-unif² a==a'
... | record { ⁈-rel = f·a==f'·a'  ; ⁈-r-eval = f'·a'⇓b  }
    | record { ⁈-rel = f'·a'==g·a' ; ⁈-l-eval = f'·a'⇓b' }
    | _ , UFa'⊆UFa rewrite det-· f'·a'⇓b'  f'·a'⇓b | cod-unif¹ (memˡ a'==a') (memʳ a==a')
      = [⁈-rel (cod-trans a==a' f·a==f'·a' (UFa'⊆UFa f'·a'==g·a')) ]

```
