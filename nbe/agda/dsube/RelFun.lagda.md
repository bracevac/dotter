# Partial Functions & Relation Families

Auxiliary definitions and predicates on top of partial functions,
which are encoded either as inductive-recursive definitions (think El
function), or as graphs (think evaluation and quotation functions in
NbE).

```agda
module dsube.RelFun where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to _⊔ˡ_)
open import dsube.NbE
open import dsube.Relations

-- Function space restricted to a subset of the domain
_⟹_ : ∀{ℓ}{T : Set ℓ} → (T → Set ℓ) → ∀{ℓ'} → Set ℓ' → Set (ℓ ⊔ˡ ℓ')
U ⟹ R = ∀{A} → U A → R

-- interpretation El respects a relation, meaning it yields equivalent relations for related pairs
Respect⊆ :  ∀{U : 𝕍 → Set} → (El : U ⟹ Rel) → (𝓐 : Rel) → Set
Respect⊆ {U} El 𝓐 = ∀ {A B} → (A==B : A == B ∈ 𝓐) → ∀{UA : U A}{UB : U B} → El UA ⊆ El UB
Respect⊇ :  ∀{U : 𝕍 → Set} → (El : U ⟹ Rel) → (𝓐 : Rel) → Set
Respect⊇ {U} El 𝓐 = ∀ {A B} → (A==B : A == B ∈ 𝓐) → ∀{UA : U A}{UB : U B} → El UB ⊆ El UA


-- certifies that 𝐹 · 𝑎 is defined and the result satisfies P
-- the point of this is avoiding working with bare existentials in proofs, which tend to be noisy
record [_∙_]∈_ (𝐹 : 𝕍) (𝑎 : 𝕍) (P : 𝕍 → Set) : Set where
  eta-equality
  constructor [⁈_]
  field
    {{⁈-val}} : 𝕍
    {{⁈-eval}} : 𝐹 · 𝑎 ⇓ ⁈-val
    ⁈ : P ⁈-val -- in most cases, this is the interesting bit, thus, the other fields are instances

open [_∙_]∈_

-- analogous construction on pairs, i.e., certify that F·𝑎 and F'·𝑎' are defined and related via R
record [_==_∙_==_]∈_ (𝐹 : 𝕍) (𝐹' : 𝕍) (𝑎 : 𝕍) (𝑎' : 𝕍) (R : Rel) : Set where
  eta-equality
  constructor [⁈-rel_]
  field
    {{⁈-val-l}} : 𝕍
    {{⁈-val-r}} : 𝕍
    {{⁈-l-eval}} : 𝐹 · 𝑎 ⇓ ⁈-val-l
    {{⁈-r-eval}} : 𝐹' · 𝑎' ⇓ ⁈-val-r
    ⁈-rel : R ⁈-val-l ⁈-val-r
open [_==_∙_==_]∈_

-- Certifies that value 𝐹 is models an indexed family over the domain of relation 𝓐:
-- for all 𝑎 ∈ 𝓐 , F·𝑎 is defined and P F·𝑎 holds.
[_∙_]⟹_ : (𝐹 : 𝕍) → (𝓐 : Rel) → (P : 𝕍 → Set) → Set
[ 𝐹 ∙ 𝓐 ]⟹ P = ∀{𝑎} → 𝑎 ∈ 𝓐 → [ 𝐹 ∙ 𝑎 ]∈ P

-- some sugar to lighten the notation
_∙ˡ_ : ∀{𝐹 𝓐 P} → [ 𝐹 ∙ 𝓐 ]⟹ P → ∀{𝑎 𝑎'} → 𝑎 == 𝑎' ∈ 𝓐 → [ 𝐹 ∙ 𝑎 ]∈ P
_∙ˡ_ F a==a' = F (memˡ a==a')
_∙ʳ_ : ∀{𝐹 𝓐 P} → [ 𝐹 ∙ 𝓐 ]⟹ P → ∀{𝑎 𝑎'} → 𝑎 == 𝑎' ∈ 𝓐 → [ 𝐹 ∙ 𝑎' ]∈ P
_∙ʳ_ F a==a' = F (memʳ a==a')

infixr 7 _∙ˡ_
infixr 7 _∙ʳ_

⌜_⌝ : {𝐹 : 𝕍} → {𝑎 : 𝕍} → { P : 𝕍 → Set } → (Fa : [ 𝐹 ∙ 𝑎 ]∈ P) → P (⁈-val Fa)
⌜ Fa ⌝ = ⁈ Fa

[_] : {𝐹 : 𝕍} → {𝑎 : 𝕍} → { P : 𝕍 → Set } → (Fa : [ 𝐹 ∙ 𝑎 ]∈ P) → 𝕍
[ Fa ] = ⁈-val Fa

-- Again, analogous construction to pairs of functions, certifying that 𝐹 and 𝐹'
-- take related things in 𝓐 to related things in 𝓡
[_==_∙_]⟹_ : (𝐹 : 𝕍) → (𝐹 : 𝕍) → (𝓐 : Rel) → (𝓡 : Rel) → Set
[ 𝐹 == 𝐹' ∙ 𝓐 ]⟹ 𝓡 = ∀{𝑎 𝑎'} → 𝑎 == 𝑎' ∈ 𝓐 → [ 𝐹 == 𝐹' ∙ 𝑎 == 𝑎' ]∈ 𝓡

-- what it means to be a proper indexed family of relations
record Rel-family {U : 𝕍 → Set}{𝐴 𝐹} (El : U ⟹ Rel) (U𝐴 : U 𝐴) (U𝐹 : [ 𝐹 ∙ (El U𝐴) ]⟹ U) : Set where
  field
    cod-unif¹ : ∀{𝑎} → (prf prf' : 𝑎 ∈ El U𝐴) → U𝐹 prf ≡ U𝐹 prf'
    cod-unif² :  ∀{𝑎 𝑎'} → (a==a' : 𝑎 == 𝑎' ∈ El U𝐴) → El ⌜ U𝐹 ∙ˡ a==a' ⌝ ≡ᴿ El ⌜ U𝐹 ∙ʳ a==a' ⌝
open Rel-family {{...}}


-- asserts that 𝐴 and 𝐹 form a Π-type in the universe U with interpretation fun El
record Π-⟨_,_⟩ (U : 𝕍 → Set) (El : U ⟹ Rel) (𝐴 𝐹 : 𝕍) : Set where
  eta-equality
  field
    Π-dom : U 𝐴
    Π-cod : [ 𝐹 ∙ (El Π-dom) ]⟹ U
    overlap {{Π-props}} : Rel-family El Π-dom Π-cod
open Π-⟨_,_⟩ {{...}}


-- some more syntactic sugar for Π-type that will make definitions a lot easier to read
-- ᵈ refers to the domain, ᶜ refers to the codomain
⌜_⌝ᵈ : {U : 𝕍 → Set} → {El : U ⟹ Rel} → (𝐴 : 𝕍) → {𝐹 : 𝕍} → {{Pi : Π-⟨ U , El ⟩ 𝐴 𝐹 }} → U 𝐴
⌜ 𝐴 ⌝ᵈ = Π-dom

⌜_⌝ᶜ : {U : 𝕍 → Set} → {El : U ⟹ Rel} → (𝐹 : 𝕍) → {𝐴 : 𝕍} → {{Pi : Π-⟨ U , El ⟩ 𝐴 𝐹 }} → [ 𝐹 ∙ (El (Π-dom {{Pi}})) ]⟹ U
⌜ 𝐹 ⌝ᶜ = Π-cod

-- apply the codomain to a value which is element of the domain interpretation
⌜_·_⌝ᶜ : {U : 𝕍 → Set} → {El : U ⟹ Rel} → (𝐹 : 𝕍) → {𝐴 : 𝕍} → {{Pi : Π-⟨ U , El ⟩ 𝐴 𝐹 }} → ∀{𝑎} → (mem : 𝑎 ∈ (El (Π-dom {{Pi}}))) → U (⁈-val (Π-cod {{Pi}} mem))
⌜ 𝐹 · 𝑎 ⌝ᶜ =  ⌜  ⌜ 𝐹 ⌝ᶜ 𝑎 ⌝

-- apply the codomain to the left of a pair in the domain interpretation
⌜_·ˡ_⌝ᶜ : {U : 𝕍 → Set} → {El : U ⟹ Rel} → (𝐹 : 𝕍) → {𝐴 : 𝕍} → {{Pi : Π-⟨ U , El ⟩ 𝐴 𝐹 }} → ∀{𝑎 𝑏} → (a==b : 𝑎 == 𝑏 ∈ (El (Π-dom {{Pi}}))) → U (⁈-val (Π-cod {{Pi}} (memˡ a==b)))
⌜ 𝐹 ·ˡ a==b ⌝ᶜ =  ⁈ ( Π-cod (memˡ a==b) )

-- apply the codomain to the right of a pair in the domain interpretation
⌜_·ʳ_⌝ᶜ : {U : 𝕍 → Set} → {El : U ⟹ Rel} → (𝐹 : 𝕍) → {𝐴 : 𝕍} → {{Pi : Π-⟨ U , El ⟩ 𝐴 𝐹 }} → ∀{𝑎 𝑏} → (a==b : 𝑎 == 𝑏 ∈ (El (Π-dom {{Pi}}))) → U (⁈-val (Π-cod {{Pi}} (memʳ a==b)))
⌜ 𝐹 ·ʳ a==b ⌝ᶜ =  ⌜  ⌜ 𝐹 ⌝ᶜ (memʳ a==b) ⌝
