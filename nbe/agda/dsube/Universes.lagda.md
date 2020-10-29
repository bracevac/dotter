# Cumulative PER Universe Hierarchy

This file formalizes a cumulative universe hierarchy of partial
equivalence relations (PERs) over the semantic domain `𝕍` (cf. `NbE`
module) à la Abel and collaborators.

We may think of the universe hierarchy as a level-indexed family of
inductive-recursive definitions.  Since Agda offers no linguistic support
for *indexed* inductive-recursive definitions (go ahead and try it!),
we have to emulate them. Concretely, that means

  1. Define the inductive-recursive universe for level 0 and prove PER
     properties.
  2. Define an inductive-recursive universe for level n+1,
     parameterized over the immediate predecessor universe level n, and
     prove PER properties.
  3. From the previous two definitions, define the level-indexed
     universe hierarchy as a large elimination. Prove its PER properties,
     which are an easy consequence of the previous results. Also, prove
     cumulativity properties.
  4. Finally, define the limit of the indexed family of universes,
     yielding a single universe definition that hides the explicit level
     indices.

```agda
module dsube.Universes where

open import Data.Bool using (true; false)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax; _,_; _×_)
open Σ
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _≤′_; _<′_; _⊔_)
open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to _⊔ˡ_)
open import dsube.Syntax using (ℒ)
open import dsube.NbE
open import dsube.Relations
open import dsube.RelFun
open import dsube.PER
open Per {{...}}
open Π-⟨_,_⟩ {{...}}
open [_∙_]∈_
open [_==_∙_==_]∈_
open Rel-family {{...}}
open _≤′_
```
# Universe Level 0

## Single Type Codes `𝓤₀` and Interpretation Function `𝓔𝓵₀`.

`𝓤₀` defines valid type codes, i.e., the subset of the semantic domain `𝕍`
corresponding to normalized type expressions.
We require that `𝓤₀` is closed under the formation of dependent function types,
i.e., we need to refer to the interpretation/denotation of type codes while
defining them. This leads to the induction-recursion definition principle:
We define `𝓤₀` inductively, simultaneously with the interpretation function
`𝓔𝓵₀`, which recurses over `𝓤₀`.
```agda
-- we first define the El function that takes *single* type codes (and not related pairs) to relations, just as on pen and paper
data 𝓤₀ : 𝕍 → Set
𝓔𝓵₀ : {𝐴 : 𝕍} → 𝓤₀ 𝐴 → Rel
```
From another perspective, this corresponds to the Bove&Capretta method of defining
a partial function (`𝓔𝓵₀`) in terms of a total function on the function domain,
which we model by a predicate (`𝓤₀`).
```agda
data 𝓤₀ where
  𝓤₀-NE : ∀{NE} → 𝓤₀ (↑⟨ (ᶜ (V𝑆𝑒𝑡 0)) ⟩ NE)

  𝓤₀-𝑁 : 𝓤₀ (ᶜ V𝑁)

  𝓤₀-⊤ : 𝓤₀ (ᶜ V⊤)

  𝓤₀-⊥ : 𝓤₀ (ᶜ V⊥)

  𝓤₀-Π : ∀ 𝐴 𝐹 →
    {{Π-⟨ 𝓤₀ , 𝓔𝓵₀ ⟩ 𝐴 𝐹}} →
    -------------------------
    𝓤₀ (VΠ 𝐴 𝐹)

𝓔𝓵₀ {ᶜ V𝑁} _              = 𝓝𝓪𝓽
𝓔𝓵₀ {ᶜ V⊥} _              = 𝓥⊥
𝓔𝓵₀ {ᶜ V⊤} _              = 𝓥⊤
𝓔𝓵₀ {↑⟨ ᶜ V𝑆𝑒𝑡 0 ⟩ NE} _  = 𝓥Ty-Ne 0 NE
𝓔𝓵₀ (𝓤₀-Π 𝐴 𝐹)        = ℿ (𝓔𝓵₀ ⌜ 𝐴 ⌝ᵈ) (λ 𝑎 → 𝓔𝓵₀ ⌜ 𝐹 · 𝑎 ⌝ᶜ )
```
### 𝓔𝓵₀ Interprets Type Codes as PERs
```agda
-- -- for each type 𝐴 in the universe 𝓤₀, its interpretation is a PER
𝓔𝓵₀-sym : ∀ {𝐴} → (UA : 𝓤₀ 𝐴) → Sym (𝓔𝓵₀ UA)
𝓔𝓵₀-sym 𝓤₀-NE        = per-sym
𝓔𝓵₀-sym 𝓤₀-𝑁         = per-sym
𝓔𝓵₀-sym 𝓤₀-⊤         = per-sym
𝓔𝓵₀-sym 𝓤₀-⊥ {a} {b} = per-sym {{Per-𝓥⊥}} {a} {b}
𝓔𝓵₀-sym (𝓤₀-Π 𝐴 𝐹) = ℿ-sym (𝓔𝓵₀-sym ⌜ 𝐴 ⌝ᵈ) ⌜ 𝐹 ⌝ᶜ (λ a==a' → 𝓔𝓵₀-sym ⌜ ⌜ 𝐹 ⌝ᶜ ∙ˡ a==a' ⌝)

𝓔𝓵₀-trans : ∀ {𝐴} → (UA : 𝓤₀ 𝐴) → Trans (𝓔𝓵₀ UA)
𝓔𝓵₀-trans 𝓤₀-NE            = per-trans
𝓔𝓵₀-trans 𝓤₀-𝑁             = per-trans
𝓔𝓵₀-trans 𝓤₀-⊤             = per-trans
𝓔𝓵₀-trans 𝓤₀-⊥ {a} {b} {c} = per-trans {{Per-𝓥⊥}} {a} {b} {c}
𝓔𝓵₀-trans (𝓤₀-Π 𝐴 𝐹)     = ℿ-trans (𝓔𝓵₀-sym ⌜ 𝐴 ⌝ᵈ) (𝓔𝓵₀-trans ⌜ 𝐴 ⌝ᵈ) ⌜ 𝐹 ⌝ᶜ (λ a==a' →  𝓔𝓵₀-trans ⌜ ⌜ 𝐹 ⌝ᶜ ∙ˡ a==a' ⌝)

Per-𝓔𝓵₀ : ∀ {𝐴} → (UA : 𝓤₀ 𝐴) → Per (𝓔𝓵₀ UA)
Per.per-sym   (Per-𝓔𝓵₀ UA) = 𝓔𝓵₀-sym UA
Per.per-trans (Per-𝓔𝓵₀ UA) = 𝓔𝓵₀-trans UA
```
### Uniformity of 𝓔𝓵₀

This property asserts that the result of 𝓔𝓵₀ is independent of the
concrete proof structure of a type code 𝓤₀ 𝐴. Others might call it a
form of proof irrelevance.

```agda
𝓔𝓵₀-unif : ∀{𝐴} → (prf prf' : 𝓤₀ 𝐴) → 𝓔𝓵₀ prf ≡ᴿ 𝓔𝓵₀ prf'
𝓔𝓵₀-unif 𝓤₀-NE        𝓤₀-NE          = (λ x → x) , (λ x → x)
𝓔𝓵₀-unif 𝓤₀-𝑁         𝓤₀-𝑁           = (λ x → x) , (λ x → x)
𝓔𝓵₀-unif 𝓤₀-⊤         𝓤₀-⊤           = (λ x → x) , (λ x → x)
𝓔𝓵₀-unif 𝓤₀-⊥         𝓤₀-⊥           = (λ x → tt) , (λ x → tt)
𝓔𝓵₀-unif (𝓤₀-Π 𝐴 𝐹 {{Pi}}) (𝓤₀-Π 𝐴 𝐹 {{Pi'}}) with Π-dom {{Pi}} | Π-dom {{Pi'}} | Π-cod {{Pi}} | Π-cod {{Pi'}}
... | U𝐴 | U𝐴' | U𝐹 | U𝐹' with 𝓔𝓵₀-unif U𝐴 U𝐴'
... | ElUA⊆ElUA' , ElUA'⊆ElUA        = left , right
  where
    left :  ℿ (𝓔𝓵₀ U𝐴) (λ 𝑎 → 𝓔𝓵₀ (⁈ (U𝐹 𝑎))) ⊆ ℿ (𝓔𝓵₀ U𝐴') (λ 𝑎 → 𝓔𝓵₀ (⁈ (U𝐹' 𝑎)))
    left ΠUAUF-f==f' ELUA'a==a' with ΠUAUF-f==f' (ElUA'⊆ElUA  ELUA'a==a')
    ... | [⁈-rel ELUFa-fa==f'a' ] with ((U𝐹 (memˡ (ElUA'⊆ElUA ELUA'a==a')))) | ((U𝐹' (memˡ ELUA'a==a')))
    ... | record { ⁈ = Fa-1 ;  ⁈-eval = Fa⇓-1} | record { ⁈ = Fa-2 ; ⁈-eval = Fa⇓-2}
          rewrite det-· Fa⇓-2 Fa⇓-1
          with 𝓔𝓵₀-unif Fa-2 Fa-1
    ... | _ , conv = [⁈-rel (conv ELUFa-fa==f'a') ]
    right : ℿ (𝓔𝓵₀ U𝐴') (λ 𝑎 → 𝓔𝓵₀ (⁈ (U𝐹' 𝑎))) ⊆ ℿ (𝓔𝓵₀ U𝐴) (λ 𝑎 → 𝓔𝓵₀ (⁈ (U𝐹 𝑎)))
    right  ΠUA'UF'-f==f' ELUAa==a' with ΠUA'UF'-f==f' (ElUA⊆ElUA'  ELUAa==a')
    ... | [⁈-rel ELUF'a-fa==f'a' ] with ((U𝐹' (memˡ (ElUA⊆ElUA' ELUAa==a')))) | ((U𝐹 (memˡ ELUAa==a')))
    ... | record { ⁈ = Fa-1 ;  ⁈-eval = Fa⇓-1} | record { ⁈ = Fa-2 ; ⁈-eval = Fa⇓-2}
          rewrite det-· Fa⇓-2 Fa⇓-1
          with 𝓔𝓵₀-unif Fa-2 Fa-1
    ... | _ , conv = [⁈-rel (conv ELUF'a-fa==f'a') ]
```
## 𝓢𝓮𝓽₀ : The PER Universe of Type Codes at Level 0

Next, we define the universe `𝓢𝓮𝓽₀` for type equalities, which is another
inductive-recursive type.  Again, induction-recursion arises here from
the case for Π-types, similar to the `𝓤₀` definition.  This time,
though, we have to simultaneously define `𝓢𝓮𝓽₀` (induction part) with
the property that the interpretation `𝓔𝓵₀` respects it (recursion part).

```agda
data 𝓢𝓮𝓽₀ : Rel
-- we need to define the respect property of EL simultaneously (cf. 𝓢𝓮𝓽₀-Π)
𝓔𝓵₀-resp-⊆ : Respect⊆ {𝓤₀} 𝓔𝓵₀ 𝓢𝓮𝓽₀
-- due to contraviarance in Pi, we need to simultaneosly prove it with the opposite direction
𝓔𝓵₀-resp-⊇ : Respect⊇ {𝓤₀} 𝓔𝓵₀ 𝓢𝓮𝓽₀

data 𝓢𝓮𝓽₀ where
  𝓢𝓮𝓽₀-NE : ∀{NE NE'} →
    NE == NE' ∈ 𝓑𝓸𝓽 →
    -----------------------------------------------
    ↑⟨ (ᶜ (V𝑆𝑒𝑡 0)) ⟩ NE == ↑⟨ (ᶜ (V𝑆𝑒𝑡 0)) ⟩ NE' ∈ 𝓢𝓮𝓽₀

  𝓢𝓮𝓽₀-𝑁 : (ᶜ V𝑁) == (ᶜ V𝑁) ∈ 𝓢𝓮𝓽₀

  𝓢𝓮𝓽₀-⊤ : (ᶜ V⊤) == (ᶜ V⊤) ∈ 𝓢𝓮𝓽₀

  𝓢𝓮𝓽₀-⊥ : (ᶜ V⊥) == (ᶜ V⊥) ∈ 𝓢𝓮𝓽₀

  𝓢𝓮𝓽₀-Π : ∀{𝐴 𝐹 𝐴' 𝐹'} →
    (A==A' : 𝐴 == 𝐴' ∈ 𝓢𝓮𝓽₀) →
    {Pi  : 𝓤₀ (VΠ 𝐴 𝐹)} →
    {Pi' : 𝓤₀ (VΠ 𝐴' 𝐹')} →
    --it's easier to do some proofs if we universally quantify over Pi and Pi here
    (∀ {{Pi  : Π-⟨ 𝓤₀ , 𝓔𝓵₀ ⟩ 𝐴 𝐹}} →
       {{Pi' : Π-⟨ 𝓤₀ , 𝓔𝓵₀ ⟩ 𝐴' 𝐹'}} →
       (∀{a a'} → (a==a' : a == a' ∈ 𝓔𝓵₀ ⌜ 𝐴 ⌝ᵈ) →
         [ ⌜ 𝐹 ⌝ᶜ ∙ˡ a==a' ] == [ ⌜ 𝐹' ⌝ᶜ ∙ʳ (𝓔𝓵₀-resp-⊆ A==A' a==a') ] ∈ 𝓢𝓮𝓽₀)) →
    ------------------------------------------------------------------------------------------------------
    (VΠ 𝐴 𝐹) == (VΠ 𝐴' 𝐹') ∈ 𝓢𝓮𝓽₀
```
### 𝓔𝓵₀ Respects 𝓢𝓮𝓽₀

This property ensures that the 𝓔𝓵₀ interpretations of two related type codes in 𝓢𝓮𝓽₀ are equivalent relations
(cf. `RelFun` module).

```agda
-- -- TODO: to facilitate reuse , factor out the proofs for the Pi cases in the below properties
𝓔𝓵₀-resp-⊆ (𝓢𝓮𝓽₀-NE NE==NE') (𝓥Ty-Ne-mem x x₁ x₂) =
  𝓥Ty-Ne-mem (per-trans (per-sym NE==NE') x) ((per-trans (per-sym NE==NE') x₁)) x₂
𝓔𝓵₀-resp-⊆ 𝓢𝓮𝓽₀-𝑁 = λ z → z
𝓔𝓵₀-resp-⊆ 𝓢𝓮𝓽₀-⊤ = λ z → z
𝓔𝓵₀-resp-⊆ 𝓢𝓮𝓽₀-⊥ = λ _ → tt
𝓔𝓵₀-resp-⊆ (𝓢𝓮𝓽₀-Π A==A' F==F') {𝓤₀-Π 𝐴 𝐹} {𝓤₀-Π 𝐴' 𝐹'} {f} {f'} ELUPi-f==f' --with F₀==F₀' {{Pi}} {{Pi'}}
--... | F==F'
    = prf
      where
      prf : ∀{ 𝑎 𝑎' } → ∀ (a==a' : 𝓔𝓵₀ ⌜ 𝐴' ⌝ᵈ 𝑎 𝑎') →  [ f == f' ∙ 𝑎 == 𝑎' ]∈ 𝓔𝓵₀ ⌜ ⌜ 𝐹' ⌝ᶜ ∙ˡ a==a' ⌝
      prf ELUA'-a==a' with 𝓔𝓵₀-resp-⊇  A==A' ELUA'-a==a'
      ... | ELUA-a==a' with ELUPi-f==f' ELUA-a==a' | 𝓔𝓵₀-resp-⊆ (F==F' ELUA-a==a') | cod-unif² ELUA'-a==a'
      ... | [⁈-rel ELUFa-b==b' ] | IH-cod | _ , ELUF'a'→a
            rewrite cod-unif¹ (memʳ (𝓔𝓵₀-resp-⊆ A==A' ELUA-a==a')) (memʳ ELUA'-a==a')
            = [⁈-rel ELUF'a'→a (IH-cod ELUFa-b==b') ]

𝓔𝓵₀-resp-⊇ (𝓢𝓮𝓽₀-NE NE==NE') (𝓥Ty-Ne-mem x₁ x₂ x₃) =
  𝓥Ty-Ne-mem (per-trans NE==NE' x₁) (per-trans NE==NE' x₂) x₃
𝓔𝓵₀-resp-⊇ 𝓢𝓮𝓽₀-𝑁 = λ z → z
𝓔𝓵₀-resp-⊇ 𝓢𝓮𝓽₀-⊤ = λ z → z
𝓔𝓵₀-resp-⊇ 𝓢𝓮𝓽₀-⊥ = λ z → z
𝓔𝓵₀-resp-⊇ (𝓢𝓮𝓽₀-Π A==A' F₀==F₀') {𝓤₀-Π 𝐴 𝐹 {{Pi}}} {𝓤₀-Π 𝐴' 𝐹' {{Pi'}}} {f} {f'} ELUPi-f==f' with F₀==F₀' {{Pi}} {{Pi'}}
... | F==F' = prf
      where
      prf : ∀{ 𝑎 𝑎' } → ∀ (a==a' : 𝓔𝓵₀ ⌜ 𝐴 ⌝ᵈ 𝑎 𝑎') →  [ f == f' ∙ 𝑎 == 𝑎' ]∈ 𝓔𝓵₀ ⌜ ⌜ 𝐹 ⌝ᶜ ∙ˡ a==a' ⌝
      prf ELUA-a==a' with 𝓔𝓵₀-resp-⊆  A==A' ELUA-a==a'
      ... | ELUA'-a==a' with ELUPi-f==f' ELUA'-a==a' | 𝓔𝓵₀-resp-⊇ (F==F' ELUA-a==a') | cod-unif² ELUA'-a==a'
      ... | [⁈-rel ELUF'a-b==b' ] | IH-cod | ELUF'a→a' , _
            rewrite cod-unif¹ (memʳ (𝓔𝓵₀-resp-⊆ A==A' ELUA-a==a')) (memʳ ELUA'-a==a')
           = [⁈-rel IH-cod (ELUF'a→a' ELUF'a-b==b') ]
```
### Proof that 𝓢𝓮𝓽₀ is a PER
```agda
Set0-sym : ∀{𝐴 𝐵} → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽₀ → 𝐵 == 𝐴 ∈ 𝓢𝓮𝓽₀
Set0-sym (𝓢𝓮𝓽₀-NE x) = 𝓢𝓮𝓽₀-NE (per-sym x)
Set0-sym 𝓢𝓮𝓽₀-𝑁      = 𝓢𝓮𝓽₀-𝑁
Set0-sym 𝓢𝓮𝓽₀-⊤      = 𝓢𝓮𝓽₀-⊤
Set0-sym 𝓢𝓮𝓽₀-⊥      = 𝓢𝓮𝓽₀-⊥
Set0-sym (𝓢𝓮𝓽₀-Π {𝐴} {𝐹} {𝐴'} {𝐹'} A==A' {UF} {UF'} F==F') = 𝓢𝓮𝓽₀-Π A'==A {UF'} {UF} F'==F
   where
     A'==A : 𝓢𝓮𝓽₀ 𝐴' 𝐴
     A'==A = Set0-sym A==A'
     F'==F : ∀ {{Pi'  : Π-⟨ 𝓤₀ , 𝓔𝓵₀ ⟩ 𝐴' 𝐹'}} → {{Pi : Π-⟨ 𝓤₀ , 𝓔𝓵₀ ⟩ 𝐴 𝐹}} → ∀ {a a' : 𝕍} →
                (a==a' : a == a' ∈ 𝓔𝓵₀ ⌜ 𝐴' ⌝ᵈ) →
                   [ ⌜ 𝐹' ⌝ᶜ ∙ˡ a==a' ] == [ ⌜ 𝐹 ⌝ᶜ ∙ʳ (𝓔𝓵₀-resp-⊆ A'==A a==a') ] ∈ 𝓢𝓮𝓽₀
     F'==F ELUA'-a==a' with 𝓔𝓵₀-resp-⊆ A'==A  ELUA'-a==a'
     ... | ELUA-a==a' with Set0-sym (F==F' (𝓔𝓵₀-sym ⌜ 𝐴 ⌝ᵈ ELUA-a==a'))
     ... | UF'a'==UFa rewrite cod-unif¹ (memʳ (𝓔𝓵₀-resp-⊆ A==A' (𝓔𝓵₀-sym ⌜ 𝐴 ⌝ᵈ ELUA-a==a'))) (memˡ ELUA'-a==a')
                            | cod-unif¹ (memʳ (𝓔𝓵₀-resp-⊆ (Set0-sym A==A') ELUA'-a==a')) (memˡ (𝓔𝓵₀-sym ⌜ 𝐴 ⌝ᵈ ELUA-a==a'))
           = UF'a'==UFa

Set0-trans : ∀{𝐴 𝐵 𝐶} → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽₀ → 𝐵 == 𝐶 ∈ 𝓢𝓮𝓽₀ → 𝐴 == 𝐶 ∈ 𝓢𝓮𝓽₀
Set0-trans (𝓢𝓮𝓽₀-NE NE==NE'') (𝓢𝓮𝓽₀-NE NE''==NE') = 𝓢𝓮𝓽₀-NE (per-trans NE==NE'' NE''==NE')
Set0-trans 𝓢𝓮𝓽₀-𝑁 𝓢𝓮𝓽₀-𝑁 = 𝓢𝓮𝓽₀-𝑁
Set0-trans 𝓢𝓮𝓽₀-⊤ 𝓢𝓮𝓽₀-⊤ = 𝓢𝓮𝓽₀-⊤
Set0-trans 𝓢𝓮𝓽₀-⊥ 𝓢𝓮𝓽₀-⊥ = 𝓢𝓮𝓽₀-⊥
Set0-trans (𝓢𝓮𝓽₀-Π {𝐴} {𝐹} {𝐴''} {𝐹''} A==A'' {PiAF} {𝓤₀-Π 𝐴'' 𝐹''}  F==F'')
           (𝓢𝓮𝓽₀-Π {𝐴''} {𝐹''} {𝐴'} {𝐹'} A''==A' {_} {PiA'F'} F''==F')
         = 𝓢𝓮𝓽₀-Π A==A' {PiAF} {PiA'F'} F==F'
   where
     A==A' : 𝓢𝓮𝓽₀ 𝐴 𝐴'
     A==A' = Set0-trans A==A'' A''==A'
     F==F' : ∀ {{Pi  : Π-⟨ 𝓤₀ , 𝓔𝓵₀ ⟩ 𝐴 𝐹}} → {{Pi' : Π-⟨ 𝓤₀ , 𝓔𝓵₀ ⟩ 𝐴' 𝐹'}} → ∀ {a a' : 𝕍} →
                (a==a' : a == a' ∈ 𝓔𝓵₀ ⌜ 𝐴 ⌝ᵈ) →
                   [ ⌜ 𝐹 ⌝ᶜ ∙ˡ a==a' ] == [ ⌜ 𝐹' ⌝ᶜ ∙ʳ (𝓔𝓵₀-resp-⊆ A==A' a==a') ] ∈ 𝓢𝓮𝓽₀
     F==F' ELUA-a==a'  with (𝓔𝓵₀-resp-⊆ A==A'' (𝓔𝓵₀-trans ⌜ 𝐴 ⌝ᵈ (𝓔𝓵₀-sym  ⌜ 𝐴 ⌝ᵈ ELUA-a==a') ELUA-a==a'))
     ... | ELUA''-a'==a' with  F==F'' ELUA-a==a' | F''==F' ELUA''-a'==a'
     ... | UFa==UF''a' | UF''a'==UF'a' rewrite cod-unif¹ (memʳ (𝓔𝓵₀-resp-⊆ A==A'' ELUA-a==a')) (memˡ ELUA''-a'==a')
           with Set0-trans UFa==UF''a' UF''a'==UF'a'
     ... | UFa==UF'a' rewrite cod-unif¹  (memʳ (𝓔𝓵₀-resp-⊆ A''==A' ELUA''-a'==a'))
                                         (memʳ (𝓔𝓵₀-resp-⊆ (Set0-trans A==A'' A''==A') ELUA-a==a'))
           = UFa==UF'a'

instance Per-𝓢𝓮𝓽₀ : Per 𝓢𝓮𝓽₀
per-sym   {{Per-𝓢𝓮𝓽₀}} = Set0-sym
per-trans {{Per-𝓢𝓮𝓽₀}} = Set0-trans
```
### Relationship between 𝓢𝓮𝓽₀ and 𝓤₀

We prove that type codes related in 𝓢𝓮𝓽₀ are in the domain of 𝓔𝓵₀,
yielding useful projections.
```agda
π₀ˡ : ∀ {A B} → A == B ∈ 𝓢𝓮𝓽₀ → 𝓤₀ A
π₀ˡ (𝓢𝓮𝓽₀-NE x) = 𝓤₀-NE
π₀ˡ 𝓢𝓮𝓽₀-𝑁 = 𝓤₀-𝑁
π₀ˡ 𝓢𝓮𝓽₀-⊤ = 𝓤₀-⊤
π₀ˡ 𝓢𝓮𝓽₀-⊥ = 𝓤₀-⊥
π₀ˡ (𝓢𝓮𝓽₀-Π _ {Pi} _) = Pi

π₀ʳ : ∀ {A B} → A == B ∈ 𝓢𝓮𝓽₀ → 𝓤₀ B
π₀ʳ = π₀ˡ ∘ Set0-sym
```
# Intermezzo: Abstracting over Universe Levels

To define a universe at level 𝓀+1, we need to parameterize it
over the previous level. The following record type bundles the requirements
on the previous level. We will carry these around as implicit instance
arguments.

```agda
-- for sanity, bundles the implicit parameters for the definitions
record ↓𝕌 : Set₁ where
  field
    ↓𝓀           : ℒ -- predecessor level, i.e., our level is suc ↓𝓀
    ↓𝓤           : 𝕍 → Set --type codes at level ↓𝓀
    ↓𝓔𝓵          : ∀ {𝐴 : 𝕍} → ↓𝓤 𝐴 → Rel -- interpretation function at level ↓𝓀
    ↓𝓢𝓮𝓽         : Rel -- PER of type codes at level ↓𝓀
    -- properties at level ↓𝓀
    ↓𝓔𝓵-resp-⊆   : Respect⊆ {↓𝓤} ↓𝓔𝓵 ↓𝓢𝓮𝓽
    ↓𝓔𝓵-resp-⊇   : Respect⊇ {↓𝓤} ↓𝓔𝓵 ↓𝓢𝓮𝓽
    ↓𝓔𝓵-unif     : ∀{𝐴} → (prf prf' : ↓𝓤 𝐴) → ↓𝓔𝓵 prf ≡ᴿ ↓𝓔𝓵 prf'
    ↓𝓤-𝑆𝑒𝑡       : ∀{𝓁} → 𝓁 <′ ↓𝓀 → ↓𝓤 (ᶜ (V𝑆𝑒𝑡 𝓁))
    ↓πˡ          : ∀ {A B} → A == B ∈ ↓𝓢𝓮𝓽 → ↓𝓤 A
    ↓πʳ          : ∀ {A B} → A == B ∈ ↓𝓢𝓮𝓽 → ↓𝓤 B
    ↓𝓤→↓𝓢𝓮𝓽      : ∀ {𝐴} → ↓𝓤 𝐴 → 𝐴 == 𝐴 ∈ ↓𝓢𝓮𝓽 --TODO: prove for all levels
    Per-↓𝓔𝓵      : ∀ {𝐴} → (UA : ↓𝓤 𝐴) → Per (↓𝓔𝓵 UA)
    {{Per-↓𝓢𝓮𝓽}} : Per ↓𝓢𝓮𝓽
    --TODO demand projections from Set to U
open ↓𝕌 {{...}}
```
# PERs at Higher Universe Levels

The PER interpretations for `𝑆𝑒𝑡 𝓁` and abstract types `⟨Type 𝑆 ⋯ 𝑇⟩` only exist
at universe levels `𝓀 > 0`, and thus depend on an immediate predeccesor universe `↓𝕌`,
which is why their definitions are relatively late to the party.

## Interpretation of (V𝑆𝑒𝑡 𝓁), for 𝓁 <′ (suc ↓𝓀)

```agda
𝓥Set : {{𝔘ₖ : ↓𝕌}} → ∀{𝓁} → 𝓁 <′ (suc ↓𝓀) → Rel
𝓥Set ≤′-refl = ↓𝓢𝓮𝓽 -- either the universe immediately below
𝓥Set (≤′-step 𝓁<↓𝓀) = ↓𝓔𝓵 (↓𝓤-𝑆𝑒𝑡 𝓁<↓𝓀) -- or delegate to below's interpretation fun for smaller universes

Per-𝓥Set : {{𝔘ₖ : ↓𝕌}} → ∀{𝓁} → (lt : 𝓁 <′ (suc ↓𝓀)) → Per (𝓥Set lt)
per-sym   {{Per-𝓥Set {_} ≤′-refl}}        = per-sym   {{Per-↓𝓢𝓮𝓽}}
per-sym   {{Per-𝓥Set {_} (≤′-step 𝓁<↓𝓀)}} = per-sym   {{Per-↓𝓔𝓵 (↓𝓤-𝑆𝑒𝑡 𝓁<↓𝓀)}}
per-trans {{Per-𝓥Set {_} ≤′-refl}}        = per-trans {{Per-↓𝓢𝓮𝓽}}
per-trans {{Per-𝓥Set {_} (≤′-step 𝓁<↓𝓀)}} = per-trans {{Per-↓𝓔𝓵 (↓𝓤-𝑆𝑒𝑡 𝓁<↓𝓀)}}

```
## Interpretation of Bounded Abstract Types ⟨Type 𝑆 ⋯ 𝑇 ⟩

By virtue of predicativity, we can encode the meaning of an abstract type
in the "intuitive way", i.e.,

    ⟦ { Type S..T } ⟧ᵏ⁺¹ = { (Type 𝑋 , Type 𝑋') | 𝑋 == 𝑋' ∈ Set k ∧ ⟦ S ⟧ᵏ ⊆ ⟦ 𝑋 ⟧ᵏ ⊆ ⟦ T ⟧ᵏ }

The semantics of abstract types just contains concrete type values,
whose interpretations are "sandwiched" between the interpretations of
the bounds.  Since we work with PERs, our definition accounts for
pairs of type values. The additional condition 𝑋 == 𝑋' ∈ Set k ensures
that ⟦ 𝑋 ⟧ᵏ = ⟦ 𝑋' ⟧ᵏ, implying that both are sandwiched in the same manner.

Notably, we have replaced the weird step-indexing from the ECOOP paper with
reference to the previous universe level, plain and simple.

The following data type models the interpretation of abstract types with bounds `𝑆` and `𝑇`
at some universe level 𝓀+1:

```agda
data 𝓥Type {{𝔘ₖ : ↓𝕌}} (𝑆 𝑇 : 𝕍) : Rel
```
### Sandwiches
We factor out the defining property of an abstract type using the following "sandwich" type,
bon appetit!
```agda
⟦_<:_<:_⟧ : {{𝔘ₖ : ↓𝕌}} → ∀(𝑆 𝑋 𝑇 : 𝕍) → Set
```
Intuitively, `⟦ 𝑆 <: 𝑋 <: 𝑇 ⟧` states that at level 𝓀+1, the 𝓀 interpretation of 𝑋
is between the 𝓀 interpretations of 𝑆 and 𝑇, by set inclusion:
```agda
⟦ 𝑆 <: 𝑋 <: 𝑇 ⟧ =  ∀(US : ↓𝓤 𝑆) → ∀(UX : ↓𝓤 𝑋) → ∀(UT : ↓𝓤 𝑇) → ↓𝓔𝓵 US ⊆ ↓𝓔𝓵 UX × ↓𝓔𝓵 UX ⊆ ↓𝓔𝓵 UT
```
To keep the subsequent definition of 𝓥Type 𝑆 𝑇 simple, and to account
for the uniformity/irrelevance of ↓𝓔𝓵 on ↓𝓤, we quantify over all
valid ↓𝓤 codes for 𝑆 𝑋 𝑇 here, assuming that we are instantiating
𝓥Type in a context where such codes are always recoverable for these
parameters.

The following lemma is useful for replacing a sandwich's components with equivalent ones:
```agda
sandwich-== : {{𝔘ₖ : ↓𝕌}} → ∀{𝑆 𝑋 𝑇} → ⟦ 𝑆 <: 𝑋 <: 𝑇 ⟧ →
              ∀{𝑆' 𝑋' 𝑇'} → 𝑆 == 𝑆' ∈ ↓𝓢𝓮𝓽 → 𝑋 == 𝑋' ∈ ↓𝓢𝓮𝓽 → 𝑇 == 𝑇' ∈ ↓𝓢𝓮𝓽 →
              ⟦ 𝑆' <: 𝑋' <: 𝑇' ⟧
sandwich-== sndwch S==S' X==X' T==T' US' UX' UT' with (↓πˡ S==S') | (↓πˡ X==X') | (↓πˡ T==T')
... | US | UX | UT  with sndwch US UX UT
... | US→UX , UX→UT with ↓𝓔𝓵-resp-⊇ S==S' {US} {US'}
                        | ↓𝓔𝓵-resp-⊆ X==X' {UX} {UX'}
                        | ↓𝓔𝓵-resp-⊇ X==X' {UX} {UX'}
                        | ↓𝓔𝓵-resp-⊆ T==T' {UT} {UT'}
... | US'→US | UX→UX' | UX'→UX | UT→UT'
      = UX→UX' ∘ US→UX ∘ US'→US , UT→UT' ∘ UX→UT ∘ UX'→UX
```
### The PER for Abstract Types

We now have the ingredients to define the interpretation of abstract types
in terms of the following data type:
```agda
-- interpretation of bounded abstract types
data 𝓥Type 𝑆 𝑇  where
  -- the case for neutral terms
  𝓥Type-ne : ∀ {NE NE' 𝑆' 𝑇' 𝑆'' 𝑇''} →
          -- to ensure PER properties, we reflect at type bounds compatible with 𝑆 𝑇
          𝑆 == 𝑆' ∈ ↓𝓢𝓮𝓽 →
          𝑇 == 𝑇' ∈ ↓𝓢𝓮𝓽 →
          𝑆 == 𝑆'' ∈ ↓𝓢𝓮𝓽 →
          𝑇 == 𝑇'' ∈ ↓𝓢𝓮𝓽 →
          NE == NE' ∈ 𝓑𝓸𝓽 →
          ----------------------------------------------------------------
          ↑⟨ ⟪Type 𝑆' ⋯ 𝑇' ⟫ ⟩ NE == ↑⟨ ⟪Type 𝑆'' ⋯ 𝑇'' ⟫ ⟩ NE' ∈ 𝓥Type 𝑆 𝑇

  -- The non-neutral case models the sandwich property
  -- ⟦ { Type S..T } ⟧ᵏ⁺¹ = { (Type 𝐴 , Type 𝐴') | 𝐴 == 𝐴' ∈ Set k ∧ ⟦ S ⟧ᵏ ⊆ ⟦ 𝐴 ⟧ᵏ ⊆ ⟦ T ⟧ᵏ }.
  𝓥Type-val : ∀ {𝑋 𝑋'} →
          𝑋 == 𝑋' ∈ ↓𝓢𝓮𝓽 →
          ⟦ 𝑆 <: 𝑋 <: 𝑇 ⟧ →
          ------------------------------------------------------
          (VType 𝑋) == (VType 𝑋') ∈ 𝓥Type 𝑆 𝑇
```
The interpretation indeed is a family of PERs:
```agda
Per-𝓥Type : {{𝔘ₖ : ↓𝕌}} → ∀{𝑆 𝑇} → ∀(US : ↓𝓤 𝑆) → ∀(UT : ↓𝓤 𝑇) → Per (𝓥Type 𝑆 𝑇)
Per.per-sym   (Per-𝓥Type US UT) (𝓥Type-ne S==S' T==T' S==S'' T==T'' NE==NE') = 𝓥Type-ne S==S'' T==T'' S==S' T==T' (per-sym NE==NE')
Per.per-sym   (Per-𝓥Type US UT) (𝓥Type-val X==X' S<:X<:T) = 𝓥Type-val (per-sym X==X') (sandwich-== S<:X<:T (↓𝓤→↓𝓢𝓮𝓽 US) X==X' (↓𝓤→↓𝓢𝓮𝓽 UT))
Per.per-trans (Per-𝓥Type US UT)  (𝓥Type-ne S==S' T==T' S==S'' T==T'' NE==NE') (𝓥Type-ne _ _ S==S''' T==T''' NE'==NE'') =
    𝓥Type-ne S==S' T==T' S==S''' T==T''' (per-trans NE==NE' NE'==NE'')
Per.per-trans (Per-𝓥Type US UT) (𝓥Type-val X==X' S<:X<:T) (𝓥Type-val X'==X'' S<:X'<:T) = 𝓥Type-val (per-trans X==X' X'==X'') S<:X<:T
```
# Universe Level 𝓀+1

The definitions are similar to universe level 0, with additional cases for abstract types and 𝑆𝑒𝑡 𝓁 where
we need to refer to the predecessor universe at 𝓀.

## Single Type Codes `𝓤ₖ₊₁` and Interpretation Function `𝓔𝓵ₖ₊₁`.

```agda
data 𝓤ₖ₊₁ {{𝔘ₖ : ↓𝕌}} :  𝕍 → Set
𝓔𝓵ₖ₊₁ : {𝐴 : 𝕍} → {{𝔘ₖ : ↓𝕌}} → 𝓤ₖ₊₁ {{𝔘ₖ}} 𝐴 → Rel

data 𝓤ₖ₊₁  where
  𝓤ₖ₊₁-NE : ∀{NE 𝓁} → 𝓁 ≤′ (suc ↓𝓀) →
    ---------------------------------
    𝓤ₖ₊₁ (↑⟨ (ᶜ (V𝑆𝑒𝑡 𝓁)) ⟩ NE)

  𝓤ₖ₊₁-𝑁 : 𝓤ₖ₊₁ (ᶜ V𝑁)

  𝓤ₖ₊₁-⊤ : 𝓤ₖ₊₁ (ᶜ V⊤)

  𝓤ₖ₊₁-⊥ : 𝓤ₖ₊₁ (ᶜ V⊥)

  𝓤ₖ₊₁-⟪Type⋯⟫ : ∀{𝑆 𝑇} →
    ↓𝓤 𝑆 →
    ↓𝓤 𝑇 → -- ↓𝓔𝓵 US ⊆ ↓𝓔𝓵 UT
    -------------------
    𝓤ₖ₊₁ ⟪Type 𝑆 ⋯ 𝑇 ⟫

  𝓤ₖ₊₁-𝑆𝑒𝑡< : ∀{𝓁} → 𝓁 <′ (suc ↓𝓀) →
    𝓤ₖ₊₁ (ᶜ (V𝑆𝑒𝑡 𝓁))

  𝓤ₖ₊₁-Π : ∀ 𝐴 𝐹 →
    {{Pi : Π-⟨ 𝓤ₖ₊₁ , 𝓔𝓵ₖ₊₁ ⟩ 𝐴 𝐹}} →
    ---------------------------------
    𝓤ₖ₊₁ (VΠ 𝐴 𝐹)

𝓔𝓵ₖ₊₁ (𝓤ₖ₊₁-NE {NE} {𝓁} _) = 𝓥Ty-Ne 𝓁 NE
𝓔𝓵ₖ₊₁  𝓤ₖ₊₁-𝑁               = 𝓝𝓪𝓽
𝓔𝓵ₖ₊₁  𝓤ₖ₊₁-⊥               = 𝓥⊥
𝓔𝓵ₖ₊₁  𝓤ₖ₊₁-⊤               = 𝓥⊤
𝓔𝓵ₖ₊₁ (𝓤ₖ₊₁-⟪Type⋯⟫ {𝑆} {𝑇} US UT)  = 𝓥Type 𝑆 𝑇
𝓔𝓵ₖ₊₁ (𝓤ₖ₊₁-𝑆𝑒𝑡< 𝓁≤↓𝓀)      = 𝓥Set 𝓁≤↓𝓀
𝓔𝓵ₖ₊₁ (𝓤ₖ₊₁-Π 𝐴 𝐹)          = ℿ (𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ) (λ 𝑎 → 𝓔𝓵ₖ₊₁ ⌜ 𝐹 · 𝑎 ⌝ᶜ)
```
### 𝓔𝓵ₖ₊₁ Interprets Type Codes as PERs
```agda
-- for each type 𝐴 in the universe 𝓤ₖ₊₁, its interpretation is a PER
𝓔𝓵ₖ₊₁-sym : ∀ {𝐴} → {{𝔘ₖ : ↓𝕌}} → (UA : 𝓤ₖ₊₁ 𝐴) → Sym (𝓔𝓵ₖ₊₁ UA)
𝓔𝓵ₖ₊₁-sym (𝓤ₖ₊₁-NE _)            = per-sym
𝓔𝓵ₖ₊₁-sym  𝓤ₖ₊₁-𝑁                = per-sym
𝓔𝓵ₖ₊₁-sym  𝓤ₖ₊₁-⊤                = per-sym
𝓔𝓵ₖ₊₁-sym  𝓤ₖ₊₁-⊥ {a} {b}        = per-sym {{Per-𝓥⊥}} {a} {b}
𝓔𝓵ₖ₊₁-sym (𝓤ₖ₊₁-⟪Type⋯⟫ UₖS UₖT) = per-sym {{Per-𝓥Type UₖS UₖT}}
𝓔𝓵ₖ₊₁-sym (𝓤ₖ₊₁-𝑆𝑒𝑡< 𝓁≤↓𝓀)       = per-sym {{Per-𝓥Set 𝓁≤↓𝓀}}
𝓔𝓵ₖ₊₁-sym (𝓤ₖ₊₁-Π 𝐴 𝐹)           = ℿ-sym (𝓔𝓵ₖ₊₁-sym  ⌜ 𝐴 ⌝ᵈ) ⌜ 𝐹 ⌝ᶜ (λ a==a' → 𝓔𝓵ₖ₊₁-sym ⌜ ⌜ 𝐹 ⌝ᶜ ∙ˡ a==a' ⌝)

𝓔𝓵ₖ₊₁-trans : ∀ {𝐴} → {{𝔘ₖ : ↓𝕌}} → (UA : 𝓤ₖ₊₁ 𝐴) → Trans (𝓔𝓵ₖ₊₁ UA)
𝓔𝓵ₖ₊₁-trans (𝓤ₖ₊₁-NE _)            = per-trans
𝓔𝓵ₖ₊₁-trans  𝓤ₖ₊₁-𝑁                = per-trans
𝓔𝓵ₖ₊₁-trans  𝓤ₖ₊₁-⊤                = per-trans
𝓔𝓵ₖ₊₁-trans  𝓤ₖ₊₁-⊥ {a} {b} {c}    = per-trans {{Per-𝓥⊥}} {a} {b} {c}
𝓔𝓵ₖ₊₁-trans (𝓤ₖ₊₁-⟪Type⋯⟫ UₖS UₖT) = per-trans {{Per-𝓥Type UₖS UₖT}}
𝓔𝓵ₖ₊₁-trans (𝓤ₖ₊₁-𝑆𝑒𝑡< 𝓁≤↓𝓀)       = per-trans {{Per-𝓥Set 𝓁≤↓𝓀}}
𝓔𝓵ₖ₊₁-trans (𝓤ₖ₊₁-Π 𝐴 𝐹)           = ℿ-trans (𝓔𝓵ₖ₊₁-sym ⌜ 𝐴 ⌝ᵈ) (𝓔𝓵ₖ₊₁-trans ⌜ 𝐴 ⌝ᵈ) ⌜ 𝐹 ⌝ᶜ (λ a==a' → 𝓔𝓵ₖ₊₁-trans ⌜ ⌜ 𝐹 ⌝ᶜ ∙ˡ a==a' ⌝)

Per-𝓔𝓵ₖ₊₁ : ∀ {𝐴} → {{𝔘ₖ : ↓𝕌}} → (UA : 𝓤ₖ₊₁ 𝐴) → Per (𝓔𝓵ₖ₊₁ UA)
Per.per-sym   (Per-𝓔𝓵ₖ₊₁ UA) = 𝓔𝓵ₖ₊₁-sym UA
Per.per-trans (Per-𝓔𝓵ₖ₊₁ UA) = 𝓔𝓵ₖ₊₁-trans UA
```
### Uniformity of 𝓔𝓵ₖ₊₁
```agda
𝓔𝓵ₖ₊₁-unif : {{𝔘ₖ : ↓𝕌}} → ∀{𝐴} → (prf prf' : 𝓤ₖ₊₁ 𝐴) → 𝓔𝓵ₖ₊₁ prf ≡ᴿ 𝓔𝓵ₖ₊₁ prf'
𝓔𝓵ₖ₊₁-unif (𝓤ₖ₊₁-NE x) (𝓤ₖ₊₁-NE x₁) = ≡→≡ᴿ refl
𝓔𝓵ₖ₊₁-unif 𝓤ₖ₊₁-𝑁 𝓤ₖ₊₁-𝑁 = ≡→≡ᴿ refl
𝓔𝓵ₖ₊₁-unif 𝓤ₖ₊₁-⊤ 𝓤ₖ₊₁-⊤ = ≡→≡ᴿ refl
𝓔𝓵ₖ₊₁-unif 𝓤ₖ₊₁-⊥ 𝓤ₖ₊₁-⊥ = ≡→≡ᴿ refl
𝓔𝓵ₖ₊₁-unif (𝓤ₖ₊₁-𝑆𝑒𝑡< x) (𝓤ₖ₊₁-𝑆𝑒𝑡< x₁) rewrite ≤′-irrelevant x x₁ = ≡→≡ᴿ refl
𝓔𝓵ₖ₊₁-unif (𝓤ₖ₊₁-⟪Type⋯⟫ _ _) (𝓤ₖ₊₁-⟪Type⋯⟫ _ _) = ≡→≡ᴿ refl
𝓔𝓵ₖ₊₁-unif (𝓤ₖ₊₁-Π 𝐴 𝐹 {{Pi}}) (𝓤ₖ₊₁-Π 𝐴 𝐹 {{Pi'}}) with Π-dom {{Pi}} | Π-dom {{Pi'}} | Π-cod {{Pi}} | Π-cod {{Pi'}}
... | U𝐴 | U𝐴' | U𝐹 | U𝐹' with 𝓔𝓵ₖ₊₁-unif U𝐴 U𝐴'
... | ElUA⊆ElUA' , ElUA'⊆ElUA        = left , right
  where
    left :  ℿ (𝓔𝓵ₖ₊₁ U𝐴) (λ 𝑎 → 𝓔𝓵ₖ₊₁ (⁈ (U𝐹 𝑎))) ⊆ ℿ (𝓔𝓵ₖ₊₁ U𝐴') (λ 𝑎 → 𝓔𝓵ₖ₊₁ (⁈ (U𝐹' 𝑎)))
    left ΠUAUF-f==f' ELUA'a==a' with ΠUAUF-f==f' (ElUA'⊆ElUA  ELUA'a==a')
    ... | [⁈-rel ELUFa-fa==f'a' ] with ((U𝐹 (memˡ (ElUA'⊆ElUA ELUA'a==a')))) | ((U𝐹' (memˡ ELUA'a==a')))
    ... | record { ⁈ = Fa-1 ;  ⁈-eval = Fa⇓-1} | record { ⁈ = Fa-2 ; ⁈-eval = Fa⇓-2}
          rewrite det-· Fa⇓-2 Fa⇓-1
          with 𝓔𝓵ₖ₊₁-unif Fa-2 Fa-1
    ... | _ , conv = [⁈-rel (conv ELUFa-fa==f'a') ]
    right : ℿ (𝓔𝓵ₖ₊₁ U𝐴') (λ 𝑎 → 𝓔𝓵ₖ₊₁ (⁈ (U𝐹' 𝑎))) ⊆ ℿ (𝓔𝓵ₖ₊₁ U𝐴) (λ 𝑎 → 𝓔𝓵ₖ₊₁ (⁈ (U𝐹 𝑎)))
    right  ΠUA'UF'-f==f' ELUAa==a' with ΠUA'UF'-f==f' (ElUA⊆ElUA'  ELUAa==a')
    ... | [⁈-rel ELUF'a-fa==f'a' ] with ((U𝐹' (memˡ (ElUA⊆ElUA' ELUAa==a')))) | ((U𝐹 (memˡ ELUAa==a')))
    ... | record { ⁈ = Fa-1 ;  ⁈-eval = Fa⇓-1} | record { ⁈ = Fa-2 ; ⁈-eval = Fa⇓-2}
          rewrite det-· Fa⇓-2 Fa⇓-1
          with 𝓔𝓵ₖ₊₁-unif Fa-2 Fa-1
    ... | _ , conv = [⁈-rel (conv ELUF'a-fa==f'a') ]
```
## 𝓢𝓮𝓽ₖ₊₁: The PER Universe of Type Codes at Level 𝓀+1

Again, analogous to level 0, with cases for Set k and abstract types added.
```agda
data 𝓢𝓮𝓽ₖ₊₁ {{𝔘ₖ : ↓𝕌}} : Rel
𝓔𝓵ₖ₊₁-resp-⊆ : {{𝔘ₖ : ↓𝕌}} → Respect⊆ {𝓤ₖ₊₁} 𝓔𝓵ₖ₊₁ 𝓢𝓮𝓽ₖ₊₁
𝓔𝓵ₖ₊₁-resp-⊇ : {{𝔘ₖ : ↓𝕌}} → Respect⊇ {𝓤ₖ₊₁} 𝓔𝓵ₖ₊₁ 𝓢𝓮𝓽ₖ₊₁

data 𝓢𝓮𝓽ₖ₊₁ where
  𝓢𝓮𝓽ₖ₊₁-NE : ∀{NE NE' 𝓁} → 𝓁 ≤′ (suc ↓𝓀) →
    NE == NE' ∈ 𝓑𝓸𝓽 →
    ------------------------------------------------------------------------
    ↑⟨ (ᶜ (V𝑆𝑒𝑡 𝓁)) ⟩ NE == ↑⟨ (ᶜ (V𝑆𝑒𝑡 𝓁)) ⟩ NE' ∈ 𝓢𝓮𝓽ₖ₊₁

  𝓢𝓮𝓽ₖ₊₁-𝑁 : (ᶜ V𝑁) == (ᶜ V𝑁) ∈ 𝓢𝓮𝓽ₖ₊₁

  𝓢𝓮𝓽ₖ₊₁-⊤ : (ᶜ V⊤) == (ᶜ V⊤) ∈ 𝓢𝓮𝓽ₖ₊₁

  𝓢𝓮𝓽ₖ₊₁-⊥ : (ᶜ V⊥) == (ᶜ V⊥) ∈ 𝓢𝓮𝓽ₖ₊₁

  𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ : ∀{𝑆 𝑆' 𝑇 𝑇'} →
    𝑆 == 𝑆' ∈ ↓𝓢𝓮𝓽 →
    𝑇 == 𝑇' ∈ ↓𝓢𝓮𝓽 →
    ------------------------------------------
    ⟪Type 𝑆 ⋯ 𝑇 ⟫ == ⟪Type 𝑆' ⋯ 𝑇' ⟫ ∈ 𝓢𝓮𝓽ₖ₊₁

  𝓢𝓮𝓽ₖ₊₁-𝑆𝑒𝑡< : ∀ {𝓁} → 𝓁 <′ (suc ↓𝓀) →
    (ᶜ (V𝑆𝑒𝑡 𝓁)) == (ᶜ (V𝑆𝑒𝑡 𝓁)) ∈ 𝓢𝓮𝓽ₖ₊₁

  𝓢𝓮𝓽ₖ₊₁-Π : ∀{𝐴 𝐹 𝐴' 𝐹'} →
    (A==A' : 𝐴 == 𝐴' ∈ 𝓢𝓮𝓽ₖ₊₁) →
    {Pi : Π-⟨ 𝓤ₖ₊₁ , 𝓔𝓵ₖ₊₁ ⟩ 𝐴 𝐹} → --todo unify the set0 version like this
    {Pi' : Π-⟨ 𝓤ₖ₊₁ , 𝓔𝓵ₖ₊₁ ⟩ 𝐴' 𝐹'} →
    (∀ {{Pi  : Π-⟨ 𝓤ₖ₊₁ , 𝓔𝓵ₖ₊₁ ⟩ 𝐴 𝐹}} →
       {{Pi' : Π-⟨ 𝓤ₖ₊₁ , 𝓔𝓵ₖ₊₁ ⟩ 𝐴' 𝐹'}} →
       (∀{a a'} → (a==a' : a == a' ∈ 𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ) →
         [ ⌜ 𝐹 ⌝ᶜ ∙ˡ a==a' ] == [ ⌜ 𝐹' ⌝ᶜ ∙ʳ (𝓔𝓵ₖ₊₁-resp-⊆ A==A' {⌜ 𝐴 ⌝ᵈ} {⌜ 𝐴' ⌝ᵈ} a==a') ] ∈ 𝓢𝓮𝓽ₖ₊₁)) →
    ------------------------------------------------------------------------------------------------------
    (VΠ 𝐴 𝐹) == (VΠ 𝐴' 𝐹') ∈ 𝓢𝓮𝓽ₖ₊₁
```
### 𝓔𝓵ₖ₊₁ Respects 𝓢𝓮𝓽ₖ₊₁
```agda
-- again, agda stumbles in places with implicit parameters, compared to the definitions at universe level 0
𝓔𝓵ₖ₊₁-resp-⊆ (𝓢𝓮𝓽ₖ₊₁-NE _ NE==NE') {𝓤ₖ₊₁-NE _} {𝓤ₖ₊₁-NE _} (𝓥Ty-Ne-mem x x₁ x₂) =
  𝓥Ty-Ne-mem (per-trans (per-sym NE==NE') x) ((per-trans (per-sym NE==NE') x₁)) x₂
𝓔𝓵ₖ₊₁-resp-⊆  𝓢𝓮𝓽ₖ₊₁-𝑁 {𝓤ₖ₊₁-𝑁} {𝓤ₖ₊₁-𝑁} = λ z → z
𝓔𝓵ₖ₊₁-resp-⊆  𝓢𝓮𝓽ₖ₊₁-⊤ {𝓤ₖ₊₁-⊤} {𝓤ₖ₊₁-⊤} = λ z → z
𝓔𝓵ₖ₊₁-resp-⊆  𝓢𝓮𝓽ₖ₊₁-⊥ {𝓤ₖ₊₁-⊥} {𝓤ₖ₊₁-⊥} = λ _ → tt

𝓔𝓵ₖ₊₁-resp-⊆ (𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ {S1} {S2} {T1} {T2} S1==S2 T1==T2) {𝓤ₖ₊₁-⟪Type⋯⟫ ↓US1 ↓UT1} {𝓤ₖ₊₁-⟪Type⋯⟫ ↓US2 ↓UT2}
             (𝓥Type-ne S1==S1' T1==T1'  S1==S1'' T1==T1'' NE==NE')
               = 𝓥Type-ne (per-trans (per-sym S1==S2) S1==S1')
                           (per-trans (per-sym T1==T2) T1==T1')
                           (per-trans (per-sym S1==S2) S1==S1'')
                           (per-trans (per-sym T1==T2) T1==T1'')
                           NE==NE'
𝓔𝓵ₖ₊₁-resp-⊆ (𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ {S1} {S2} {T1} {T2} ↓S1==S2 ↓T1==T2) {𝓤ₖ₊₁-⟪Type⋯⟫ ↓US1 ↓UT1} {𝓤ₖ₊₁-⟪Type⋯⟫ ↓US2 ↓UT2}
             (𝓥Type-val X==X' S1<:X<:T1) = 𝓥Type-val X==X' (sandwich-== S1<:X<:T1 ↓S1==S2 (per-refl (memˡ X==X')) ↓T1==T2)
𝓔𝓵ₖ₊₁-resp-⊆ (𝓢𝓮𝓽ₖ₊₁-𝑆𝑒𝑡< _) {𝓤ₖ₊₁-𝑆𝑒𝑡< x} {𝓤ₖ₊₁-𝑆𝑒𝑡< y} rewrite ≤′-irrelevant y x = λ z → z
𝓔𝓵ₖ₊₁-resp-⊆ (𝓢𝓮𝓽ₖ₊₁-Π A==A' F==F') {𝓤ₖ₊₁-Π 𝐴 𝐹} {𝓤ₖ₊₁-Π 𝐴' 𝐹'} {f} {f'} ELUPi-f==f' = prf
      where
      prf : ∀{ 𝑎 𝑎' } → ∀ (a==a' : 𝓔𝓵ₖ₊₁ ⌜ 𝐴' ⌝ᵈ 𝑎 𝑎') →  [ f == f' ∙ 𝑎 == 𝑎' ]∈ 𝓔𝓵ₖ₊₁ ⌜ ⌜ 𝐹' ⌝ᶜ ∙ˡ a==a' ⌝
      prf ELUA'-a==a' with 𝓔𝓵ₖ₊₁-resp-⊇ A==A' {⌜ 𝐴 ⌝ᵈ} {⌜ 𝐴' ⌝ᵈ} ELUA'-a==a'
      ... | ELUA-a==a' with ELUPi-f==f' ELUA-a==a' | 𝓔𝓵ₖ₊₁-resp-⊆ (F==F' ELUA-a==a') | cod-unif² ELUA'-a==a'
      ... | [⁈-rel ELUFa-b==b' ] | IH-cod | _ , ELUF'a'→a
            rewrite cod-unif¹ (memʳ (𝓔𝓵ₖ₊₁-resp-⊆ A==A' {⌜ 𝐴 ⌝ᵈ} {⌜ 𝐴' ⌝ᵈ} ELUA-a==a')) (memʳ ELUA'-a==a')
            = [⁈-rel ELUF'a'→a (IH-cod {⌜ 𝐹 ·ˡ ELUA-a==a' ⌝ᶜ} {⌜ 𝐹' ·ʳ ELUA'-a==a' ⌝ᶜ} ELUFa-b==b') ]

𝓔𝓵ₖ₊₁-resp-⊇  (𝓢𝓮𝓽ₖ₊₁-NE _ NE==NE') {𝓤ₖ₊₁-NE _} {𝓤ₖ₊₁-NE _} (𝓥Ty-Ne-mem x₁ x₂ x₃) =
   𝓥Ty-Ne-mem (per-trans NE==NE' x₁) (per-trans NE==NE' x₂) x₃
𝓔𝓵ₖ₊₁-resp-⊇ 𝓢𝓮𝓽ₖ₊₁-𝑁 {𝓤ₖ₊₁-𝑁} {𝓤ₖ₊₁-𝑁} = λ z → z
𝓔𝓵ₖ₊₁-resp-⊇ 𝓢𝓮𝓽ₖ₊₁-⊤ {𝓤ₖ₊₁-⊤} {𝓤ₖ₊₁-⊤} = λ z → z
𝓔𝓵ₖ₊₁-resp-⊇ 𝓢𝓮𝓽ₖ₊₁-⊥ {𝓤ₖ₊₁-⊥} {𝓤ₖ₊₁-⊥} = λ z → z

𝓔𝓵ₖ₊₁-resp-⊇ (𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ {S1} {S2} {T1} {T2} S1==S2 T1==T2) {𝓤ₖ₊₁-⟪Type⋯⟫ ↓US1 ↓UT1} {𝓤ₖ₊₁-⟪Type⋯⟫ ↓US2 ↓UT2}
             (𝓥Type-ne S2==S2' T2==T2'  S2==S2'' T2==T2'' NE==NE')
               = 𝓥Type-ne (per-trans S1==S2 S2==S2')
                           (per-trans T1==T2 T2==T2')
                           (per-trans S1==S2 S2==S2'')
                           (per-trans T1==T2 T2==T2'')
                           NE==NE'
𝓔𝓵ₖ₊₁-resp-⊇ (𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ {S1} {S2} {T1} {T2} ↓S1==S2 ↓T1==T2) {𝓤ₖ₊₁-⟪Type⋯⟫ ↓US1 ↓UT1} {𝓤ₖ₊₁-⟪Type⋯⟫ ↓US2 ↓UT2}
             (𝓥Type-val X==X' S2<:X<:T2) = 𝓥Type-val X==X' (sandwich-== S2<:X<:T2 (per-sym ↓S1==S2) (per-refl (memˡ X==X')) (per-sym ↓T1==T2))

𝓔𝓵ₖ₊₁-resp-⊇ (𝓢𝓮𝓽ₖ₊₁-𝑆𝑒𝑡< _) {𝓤ₖ₊₁-𝑆𝑒𝑡< x} {𝓤ₖ₊₁-𝑆𝑒𝑡< y} rewrite ≤′-irrelevant y x = λ z → z
𝓔𝓵ₖ₊₁-resp-⊇ (𝓢𝓮𝓽ₖ₊₁-Π A==A' F==F') {𝓤ₖ₊₁-Π 𝐴 𝐹} {𝓤ₖ₊₁-Π 𝐴' 𝐹'} {f} {f'} ELUPi-f==f' = prf
      where
      prf : ∀{ 𝑎 𝑎' } → ∀ (a==a' : 𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ 𝑎 𝑎') →  [ f == f' ∙ 𝑎 == 𝑎' ]∈ 𝓔𝓵ₖ₊₁ ⌜ ⌜ 𝐹 ⌝ᶜ ∙ˡ a==a' ⌝
      prf ELUA-a==a' with 𝓔𝓵ₖ₊₁-resp-⊆  A==A' {⌜ 𝐴 ⌝ᵈ} {⌜ 𝐴' ⌝ᵈ} ELUA-a==a'
      ... | ELUA'-a==a' with ELUPi-f==f' ELUA'-a==a' | 𝓔𝓵ₖ₊₁-resp-⊇ (F==F' ELUA-a==a') | cod-unif² ELUA'-a==a'
      ... | [⁈-rel ELUF'a-b==b' ] | IH-cod | ELUF'a→a' , _
            rewrite cod-unif¹ (memʳ (𝓔𝓵ₖ₊₁-resp-⊆ A==A' {⌜ 𝐴 ⌝ᵈ} {⌜ 𝐴' ⌝ᵈ} ELUA-a==a')) (memʳ ELUA'-a==a')
           = [⁈-rel IH-cod {⌜ 𝐹 ·ˡ ELUA-a==a' ⌝ᶜ} {⌜ 𝐹' ·ʳ ELUA'-a==a' ⌝ᶜ} (ELUF'a→a' ELUF'a-b==b') ]
```
### Proof that 𝓢𝓮𝓽ₖ₊₁ is a PER
```agda
Setₖ₊₁-sym : {{𝔘ₖ : ↓𝕌}} → Sym 𝓢𝓮𝓽ₖ₊₁
Setₖ₊₁-sym (𝓢𝓮𝓽ₖ₊₁-NE lt x) = 𝓢𝓮𝓽ₖ₊₁-NE lt (per-sym x)
Setₖ₊₁-sym 𝓢𝓮𝓽ₖ₊₁-𝑁      = 𝓢𝓮𝓽ₖ₊₁-𝑁
Setₖ₊₁-sym 𝓢𝓮𝓽ₖ₊₁-⊤      = 𝓢𝓮𝓽ₖ₊₁-⊤
Setₖ₊₁-sym 𝓢𝓮𝓽ₖ₊₁-⊥      = 𝓢𝓮𝓽ₖ₊₁-⊥
Setₖ₊₁-sym (𝓢𝓮𝓽ₖ₊₁-Π {𝐴} {𝐹} {𝐴'} {𝐹'} A==A' {UF} {UF'} F==F') = 𝓢𝓮𝓽ₖ₊₁-Π A'==A {UF'} {UF} F'==F
   where
     A'==A : 𝐴' == 𝐴 ∈ 𝓢𝓮𝓽ₖ₊₁
     A'==A = Setₖ₊₁-sym A==A'
     F'==F : ∀ {{Pi'  : Π-⟨ 𝓤ₖ₊₁ , 𝓔𝓵ₖ₊₁ ⟩ 𝐴' 𝐹'}} → {{Pi : Π-⟨ 𝓤ₖ₊₁ , 𝓔𝓵ₖ₊₁ ⟩ 𝐴 𝐹}} → ∀ {a a' : 𝕍} →
                (a==a' : a == a' ∈ 𝓔𝓵ₖ₊₁ ⌜ 𝐴' ⌝ᵈ) →
                   [ ⌜ 𝐹' ⌝ᶜ ∙ˡ a==a' ] == [ ⌜ 𝐹 ⌝ᶜ ∙ʳ (𝓔𝓵ₖ₊₁-resp-⊆ A'==A {⌜ 𝐴' ⌝ᵈ} {⌜ 𝐴 ⌝ᵈ} a==a') ] ∈ 𝓢𝓮𝓽ₖ₊₁
     F'==F ELUA'-a==a' with 𝓔𝓵ₖ₊₁-resp-⊆ A'==A {⌜ 𝐴' ⌝ᵈ} {⌜ 𝐴 ⌝ᵈ} ELUA'-a==a'
     ... | ELUA-a==a' with Setₖ₊₁-sym (F==F' (𝓔𝓵ₖ₊₁-sym ⌜ 𝐴 ⌝ᵈ ELUA-a==a'))
     ... | UF'a'==UFa rewrite cod-unif¹ (memʳ (𝓔𝓵ₖ₊₁-resp-⊆ A==A' {⌜ 𝐴 ⌝ᵈ} {⌜ 𝐴' ⌝ᵈ} (𝓔𝓵ₖ₊₁-sym ⌜ 𝐴 ⌝ᵈ ELUA-a==a'))) (memˡ ELUA'-a==a')
                            | cod-unif¹ (memˡ (𝓔𝓵ₖ₊₁-sym  ⌜ 𝐴 ⌝ᵈ ELUA-a==a')) (memʳ ELUA-a==a')
           = UF'a'==UFa
Setₖ₊₁-sym (𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ ↓S==S' ↓T==T') = 𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ (per-sym ↓S==S') (per-sym ↓T==T')
Setₖ₊₁-sym (𝓢𝓮𝓽ₖ₊₁-𝑆𝑒𝑡< lt) = (𝓢𝓮𝓽ₖ₊₁-𝑆𝑒𝑡< lt)

Setₖ₊₁-trans : {{𝔘ₖ : ↓𝕌}} → Trans 𝓢𝓮𝓽ₖ₊₁
Setₖ₊₁-trans (𝓢𝓮𝓽ₖ₊₁-NE lt NE==NE'') (𝓢𝓮𝓽ₖ₊₁-NE _ NE''==NE') = 𝓢𝓮𝓽ₖ₊₁-NE lt (per-trans NE==NE'' NE''==NE')
Setₖ₊₁-trans 𝓢𝓮𝓽ₖ₊₁-𝑁 𝓢𝓮𝓽ₖ₊₁-𝑁 = 𝓢𝓮𝓽ₖ₊₁-𝑁
Setₖ₊₁-trans 𝓢𝓮𝓽ₖ₊₁-⊤ 𝓢𝓮𝓽ₖ₊₁-⊤ = 𝓢𝓮𝓽ₖ₊₁-⊤
Setₖ₊₁-trans 𝓢𝓮𝓽ₖ₊₁-⊥ 𝓢𝓮𝓽ₖ₊₁-⊥ = 𝓢𝓮𝓽ₖ₊₁-⊥
Setₖ₊₁-trans (𝓢𝓮𝓽ₖ₊₁-Π {𝐴} {𝐹} {𝐴''} {𝐹''} A==A'' {PiAF}  {Pi''}  F==F'')
            (𝓢𝓮𝓽ₖ₊₁-Π {𝐴''} {𝐹''} {𝐴'} {𝐹'} A''==A' {_} {PiA'F'} F''==F')
         = 𝓢𝓮𝓽ₖ₊₁-Π A==A' {PiAF} {PiA'F'} F==F'
   where
     A==A' : 𝐴 == 𝐴' ∈ 𝓢𝓮𝓽ₖ₊₁
     A==A' = Setₖ₊₁-trans A==A'' A''==A'
     F==F' : ∀ {{Pi  : Π-⟨ 𝓤ₖ₊₁ , 𝓔𝓵ₖ₊₁ ⟩ 𝐴 𝐹}} → {{Pi' : Π-⟨ 𝓤ₖ₊₁ , 𝓔𝓵ₖ₊₁ ⟩ 𝐴' 𝐹'}} → ∀ {a a' : 𝕍} →
                (a==a' : a == a' ∈ 𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ) →
                   [ ⌜ 𝐹 ⌝ᶜ ∙ˡ a==a' ] == [ ⌜ 𝐹' ⌝ᶜ ∙ʳ (𝓔𝓵ₖ₊₁-resp-⊆ A==A' {⌜ 𝐴 ⌝ᵈ} {⌜ 𝐴' ⌝ᵈ} a==a') ] ∈ 𝓢𝓮𝓽ₖ₊₁
     F==F' {{Pi}} {{Pi'}} ELUA-a==a'  with (𝓔𝓵ₖ₊₁-resp-⊆ A==A'' {⌜ 𝐴 ⌝ᵈ} {Π-dom {{Pi''}}} (𝓔𝓵ₖ₊₁-trans ⌜ 𝐴 ⌝ᵈ (𝓔𝓵ₖ₊₁-sym  ⌜ 𝐴 ⌝ᵈ ELUA-a==a') ELUA-a==a'))
     ... | ELUA''-a'==a' with  F==F'' {{Pi}} {{Pi''}} ELUA-a==a' | F''==F' {{Pi''}} {{Pi'}} ELUA''-a'==a'
     ... | UFa==UF''a' | UF''a'==UF'a' rewrite cod-unif¹ (memʳ (𝓔𝓵ₖ₊₁-resp-⊆ A==A'' {⌜ 𝐴 ⌝ᵈ} {Π-dom {{Pi''}}} ELUA-a==a')) (memˡ ELUA''-a'==a')
           with Setₖ₊₁-trans UFa==UF''a' UF''a'==UF'a'
     ... | UFa==UF'a' rewrite cod-unif¹  (memʳ (𝓔𝓵ₖ₊₁-resp-⊆ A''==A' {Π-dom {{Pi''}}} {⌜ 𝐴' ⌝ᵈ} ELUA''-a'==a'))
                                         (memʳ (𝓔𝓵ₖ₊₁-resp-⊆ (Setₖ₊₁-trans A==A'' A''==A') {⌜ 𝐴 ⌝ᵈ} {⌜ 𝐴' ⌝ᵈ} ELUA-a==a'))
           = UFa==UF'a'
Setₖ₊₁-trans (𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ ↓S==S'' ↓T==T'') (𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ ↓S''==S' ↓T''==T') = 𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ (per-trans ↓S==S'' ↓S''==S') (per-trans ↓T==T'' ↓T''==T')
Setₖ₊₁-trans (𝓢𝓮𝓽ₖ₊₁-𝑆𝑒𝑡< lt) (𝓢𝓮𝓽ₖ₊₁-𝑆𝑒𝑡< _) = (𝓢𝓮𝓽ₖ₊₁-𝑆𝑒𝑡< lt)

instance Per-𝓢𝓮𝓽ₖ₊₁ : {{𝔘ₖ : ↓𝕌}} → Per 𝓢𝓮𝓽ₖ₊₁
per-sym   {{Per-𝓢𝓮𝓽ₖ₊₁ {{𝔘ₖ}}}} = Setₖ₊₁-sym
per-trans {{Per-𝓢𝓮𝓽ₖ₊₁ {{𝔘ₖ}}}} = Setₖ₊₁-trans
```
### Relationship between 𝓢𝓮𝓽ₖ₊₁ and 𝓤ₖ₊₁
```agda
πₖ₊₁ˡ : {{𝔘ₖ : ↓𝕌}} → ∀ {A B} → A == B ∈ 𝓢𝓮𝓽ₖ₊₁ → 𝓤ₖ₊₁ A
πₖ₊₁ˡ (𝓢𝓮𝓽ₖ₊₁-NE lt _) = 𝓤ₖ₊₁-NE lt
πₖ₊₁ˡ 𝓢𝓮𝓽ₖ₊₁-𝑁 = 𝓤ₖ₊₁-𝑁
πₖ₊₁ˡ 𝓢𝓮𝓽ₖ₊₁-⊤ = 𝓤ₖ₊₁-⊤
πₖ₊₁ˡ 𝓢𝓮𝓽ₖ₊₁-⊥ = 𝓤ₖ₊₁-⊥
πₖ₊₁ˡ (𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ S==S' T==T') = 𝓤ₖ₊₁-⟪Type⋯⟫ (↓πˡ S==S') (↓πˡ T==T')
πₖ₊₁ˡ (𝓢𝓮𝓽ₖ₊₁-𝑆𝑒𝑡< lt) = 𝓤ₖ₊₁-𝑆𝑒𝑡< lt
πₖ₊₁ˡ (𝓢𝓮𝓽ₖ₊₁-Π {𝐴} {𝐹} _ {Pi} _) = 𝓤ₖ₊₁-Π 𝐴 𝐹 {{Pi}}

πₖ₊₁ʳ : {{𝔘ₖ : ↓𝕌}} → ∀ {A B} → A == B ∈ 𝓢𝓮𝓽ₖ₊₁ → 𝓤ₖ₊₁ B
πₖ₊₁ʳ = πₖ₊₁ˡ ∘ per-sym
```
# Indexed Universe Hierarchy

Having defined universe 0 and the successor universe 𝓀+1 for arbitrary 𝓀,
we now combine these to a single level-indexed family of universe definitions.
```agda
𝕌   : ℒ → ↓𝕌
𝕌𝓀↓𝓀≡ : ∀ 𝓀 → (↓𝕌.↓𝓀 (𝕌 𝓀)) ≡ 𝓀 -- this is to help agda accept the ↓𝓤-𝑆𝑒𝑡 field of 𝕌 (suc 𝓀)
𝓤   : ℒ → 𝕍 → Set
𝓔𝓵  : (𝓀 : ℒ) → {𝐴 : 𝕍} → 𝓤 𝓀 𝐴 → Rel
𝓢𝓮𝓽 : ℒ → Rel
```
## Universe Records
```agda
𝕌 0       = record
              { ↓𝓀            = zero
              ; ↓𝓤            = 𝓤₀
              ; ↓𝓔𝓵           = 𝓔𝓵₀
              ; ↓𝓢𝓮𝓽          = 𝓢𝓮𝓽₀
              ; ↓𝓔𝓵-resp-⊆    = 𝓔𝓵₀-resp-⊆
              ; ↓𝓔𝓵-resp-⊇    = 𝓔𝓵₀-resp-⊇
              ; ↓𝓔𝓵-unif      = 𝓔𝓵₀-unif
              ; ↓𝓤-𝑆𝑒𝑡        = λ ()
              ; ↓πˡ           = π₀ˡ
              ; ↓πʳ           = π₀ʳ
              ; ↓𝓤→↓𝓢𝓮𝓽       = {!!}
              ; Per-↓𝓔𝓵       = Per-𝓔𝓵₀
              ; Per-↓𝓢𝓮𝓽      = Per-𝓢𝓮𝓽₀
              }
𝕌 (suc 𝓀) = record
              { ↓𝓀            = suc 𝓀
              ; ↓𝓤            = 𝓤ₖ₊₁ {{𝕌 𝓀}}
              ; ↓𝓔𝓵           = 𝓔𝓵ₖ₊₁ {{𝕌 𝓀}}
              ; ↓𝓢𝓮𝓽          = 𝓢𝓮𝓽ₖ₊₁ {{𝕌 𝓀}}
              ; ↓𝓔𝓵-resp-⊆    = 𝓔𝓵ₖ₊₁-resp-⊆ {{𝕌 𝓀}}
              ; ↓𝓔𝓵-resp-⊇    = 𝓔𝓵ₖ₊₁-resp-⊇ {{𝕌 𝓀}}
              ; ↓𝓔𝓵-unif      = 𝓔𝓵ₖ₊₁-unif {{𝕌 𝓀}}
              ; ↓𝓤-𝑆𝑒𝑡        = 𝓤ₖ₊₁-𝑆𝑒𝑡
              ; ↓πˡ           = πₖ₊₁ˡ {{𝕌 𝓀}}
              ; ↓πʳ           = πₖ₊₁ʳ {{𝕌 𝓀}}
              ; ↓𝓤→↓𝓢𝓮𝓽       = {!!}
              ; Per-↓𝓔𝓵       = Per-𝓔𝓵ₖ₊₁ {{𝕌 𝓀}}
              ; Per-↓𝓢𝓮𝓽      = Per-𝓢𝓮𝓽ₖ₊₁ {{𝕌 𝓀}}
              }
                where
                  𝓤ₖ₊₁-𝑆𝑒𝑡 : ∀ {𝓁} → 𝓁 <′ suc 𝓀 → 𝓤ₖ₊₁ {{𝕌 𝓀}} (ᶜ V𝑆𝑒𝑡 𝓁)
                  𝓤ₖ₊₁-𝑆𝑒𝑡 with 𝓤ₖ₊₁-𝑆𝑒𝑡< {{𝕌 𝓀}}
                  ... | f rewrite (𝕌𝓀↓𝓀≡ 𝓀) = f
𝕌𝓀↓𝓀≡ 0 = refl
𝕌𝓀↓𝓀≡ (suc k) = refl
```
## Type Codes 𝓤, Interpretation Function 𝓔𝓵, and PER type codes 𝓢𝓮𝓽

The definitions and proofs of properties are now straightforward.

```agda
𝓤 0         = 𝓤₀
𝓤 (suc 𝓀)   = 𝓤ₖ₊₁ {{𝕌 𝓀}}
𝓔𝓵 0        = 𝓔𝓵₀
𝓔𝓵 (suc 𝓀)  = 𝓔𝓵ₖ₊₁ {{𝕌 𝓀}}
𝓢𝓮𝓽 0       = 𝓢𝓮𝓽₀
𝓢𝓮𝓽 (suc 𝓀) = 𝓢𝓮𝓽ₖ₊₁ {{𝕌 𝓀}}

𝓢𝓮𝓽-sym : ∀{𝓀} → Sym (𝓢𝓮𝓽 𝓀)
𝓢𝓮𝓽-sym {zero}  A==B = per-sym A==B
𝓢𝓮𝓽-sym {suc 𝓀} A==B = per-sym {{Per-𝓢𝓮𝓽ₖ₊₁ {{𝕌 𝓀}}}} A==B

𝓢𝓮𝓽-trans : ∀{𝓀} → Trans (𝓢𝓮𝓽 𝓀)
𝓢𝓮𝓽-trans {zero}  A==B B==C = per-trans A==B B==C
𝓢𝓮𝓽-trans {suc 𝓀} A==B B==C = per-trans {{Per-𝓢𝓮𝓽ₖ₊₁ {{𝕌 𝓀}}}} A==B B==C

instance Per-𝓢𝓮𝓽 : ∀{𝓀} → Per (𝓢𝓮𝓽 𝓀)
per-sym   {{Per-𝓢𝓮𝓽 {𝓀}}} = 𝓢𝓮𝓽-sym {𝓀}
per-trans {{Per-𝓢𝓮𝓽 {𝓀}}} = 𝓢𝓮𝓽-trans {𝓀}

𝓔𝓵-resp-⊆ : ∀ {𝓀} → Respect⊆ {𝓤 𝓀} (𝓔𝓵 𝓀) (𝓢𝓮𝓽 𝓀)
𝓔𝓵-resp-⊆ {zero}  = 𝓔𝓵₀-resp-⊆
𝓔𝓵-resp-⊆ {suc 𝓀} = ↓𝓔𝓵-resp-⊆ {{𝕌 (suc 𝓀)}}
𝓔𝓵-resp-⊇ : ∀ {𝓀} → Respect⊇ {𝓤 𝓀} (𝓔𝓵 𝓀) (𝓢𝓮𝓽 𝓀)
𝓔𝓵-resp-⊇ {zero}  = 𝓔𝓵₀-resp-⊇
𝓔𝓵-resp-⊇ {suc 𝓀} = ↓𝓔𝓵-resp-⊇ {{𝕌 (suc 𝓀)}}

Per-𝓔𝓵 : ∀{𝓀 𝐴} → (UA : 𝓤 𝓀 𝐴) → Per (𝓔𝓵 𝓀 UA)
Per.per-sym   (Per-𝓔𝓵 {zero} UA)  = Per.per-sym (Per-𝓔𝓵₀ UA)
Per.per-sym   (Per-𝓔𝓵 {suc 𝓀} UA) = Per.per-sym (Per-𝓔𝓵ₖ₊₁ {{𝕌 𝓀}} UA)
Per.per-trans (Per-𝓔𝓵 {zero} UA)  = Per.per-trans (Per-𝓔𝓵₀ UA)
Per.per-trans (Per-𝓔𝓵 {suc 𝓀} UA) = Per.per-trans (Per-𝓔𝓵ₖ₊₁ {{𝕌 𝓀}} UA)

𝓔𝓵-unif : ∀{𝓀} → ∀{𝐴} → (prf prf' : 𝓤 𝓀 𝐴) → 𝓔𝓵 𝓀 prf ≡ᴿ 𝓔𝓵 𝓀 prf'
𝓔𝓵-unif {zero}  = 𝓔𝓵₀-unif
𝓔𝓵-unif {suc 𝓀} = ↓𝓔𝓵-unif {{𝕌 (suc 𝓀)}}
```
# Cumulativity

Here, we prove that our family of universes indeed exhibits cumulativity properties.

## Cumulativity of 𝓤 and 𝓔𝓵

Once we have a type code in universe 𝓀, we keep having one in the successor universe:
```agda
𝓔𝓵₀⊆𝓔𝓵₁ : ∀{𝐴} → (UA : 𝓤 0 𝐴) → (UA' : 𝓤 1 𝐴)  → 𝓔𝓵 0 UA ⊆ 𝓔𝓵 1 UA'
𝓔𝓵₀⊇𝓔𝓵₁ : ∀{𝐴} → (UA : 𝓤 0 𝐴) → (UA' : 𝓤 1 𝐴)  → 𝓔𝓵 1 UA' ⊆ 𝓔𝓵 0 UA

𝓔𝓵₀⊆𝓔𝓵₁ 𝓤₀-NE (𝓤ₖ₊₁-NE x) = λ z → z
𝓔𝓵₀⊆𝓔𝓵₁ 𝓤₀-𝑁 𝓤ₖ₊₁-𝑁 = λ z → z
𝓔𝓵₀⊆𝓔𝓵₁ 𝓤₀-⊤ 𝓤ₖ₊₁-⊤ = λ z → z
𝓔𝓵₀⊆𝓔𝓵₁ 𝓤₀-⊥ 𝓤ₖ₊₁-⊥ = λ z → z
𝓔𝓵₀⊆𝓔𝓵₁ (𝓤₀-Π 𝐴 𝐹 {{Pi}}) (𝓤ₖ₊₁-Π .𝐴 .𝐹 {{Pi'}}) {f} {f'} f==f'∈Π0 a==a'∈El1 with (𝓔𝓵₀⊇𝓔𝓵₁ (Π-dom {{Pi}}) (Π-dom {{Pi'}}) a==a'∈El1)
... | a==a'∈El0 with  f==f'∈Π0 a==a'∈El0
... | [⁈-rel fa==f'a'∈𝐹a ] with Π-cod {{Pi}} (memˡ a==a'∈El0) | Π-cod {{Pi'}} (memˡ a==a'∈El1)
... | record { ⁈-val = Fa; ⁈-eval = 𝐹·𝑎⇓Fa; ⁈ = U0Fa }
    | record { ⁈-val = Fa1; ⁈-eval = 𝐹·𝑎⇓Fa1; ⁈ = U1Fa } rewrite det-· 𝐹·𝑎⇓Fa 𝐹·𝑎⇓Fa1
       = [⁈-rel 𝓔𝓵₀⊆𝓔𝓵₁ U0Fa U1Fa fa==f'a'∈𝐹a ]

𝓔𝓵₀⊇𝓔𝓵₁ 𝓤₀-NE (𝓤ₖ₊₁-NE x) = λ z → z
𝓔𝓵₀⊇𝓔𝓵₁ 𝓤₀-𝑁 𝓤ₖ₊₁-𝑁 = λ z → z
𝓔𝓵₀⊇𝓔𝓵₁ 𝓤₀-⊤ 𝓤ₖ₊₁-⊤ = λ z → z
𝓔𝓵₀⊇𝓔𝓵₁ 𝓤₀-⊥ 𝓤ₖ₊₁-⊥ = λ z → z
𝓔𝓵₀⊇𝓔𝓵₁ (𝓤₀-Π 𝐴 𝐹 {{Pi}}) (𝓤ₖ₊₁-Π .𝐴 .𝐹 {{Pi'}}) f==f'∈Π1 a==a'∈El0 with (𝓔𝓵₀⊆𝓔𝓵₁ (Π-dom {{Pi}}) (Π-dom {{Pi'}}) a==a'∈El0)
... | a==a'∈El1 with  f==f'∈Π1 a==a'∈El1
... | [⁈-rel fa==f'a'∈𝐹a ] with Π-cod {{Pi}} (memˡ a==a'∈El0) | Π-cod {{Pi'}} (memˡ a==a'∈El1)
... | record { ⁈-val = Fa; ⁈-eval = 𝐹·𝑎⇓Fa; ⁈ = U0Fa }
    | record { ⁈-val = Fa1; ⁈-eval = 𝐹·𝑎⇓Fa1; ⁈ = U1Fa } rewrite det-· 𝐹·𝑎⇓Fa 𝐹·𝑎⇓Fa1
       = [⁈-rel 𝓔𝓵₀⊇𝓔𝓵₁ U0Fa U1Fa fa==f'a'∈𝐹a ]

𝓤₀⊆𝓤₁   : ∀{𝐴} → 𝓤 0 𝐴 → 𝓤 1 𝐴
𝓤₀⊆𝓤₁ (𝓤₀-NE {NE}) = 𝓤ₖ₊₁-NE {{𝕌 0}} {NE} (≤′-step ≤′-refl)
𝓤₀⊆𝓤₁ 𝓤₀-𝑁 = 𝓤ₖ₊₁-𝑁
𝓤₀⊆𝓤₁ 𝓤₀-⊤ = 𝓤ₖ₊₁-⊤
𝓤₀⊆𝓤₁ 𝓤₀-⊥ = 𝓤ₖ₊₁-⊥
𝓤₀⊆𝓤₁ (𝓤₀-Π 𝐴 𝐹 {{Pi}}) = 𝓤ₖ₊₁-Π 𝐴 𝐹 {{Pi'}}
  where
     U1𝐴 : 𝓤 1 𝐴
     U1𝐴 = 𝓤₀⊆𝓤₁ ⌜ 𝐴 ⌝ᵈ

     U1𝐹 : ∀ {𝑎} → 𝑎 ∈ 𝓔𝓵 1 U1𝐴 → [ 𝐹 ∙ 𝑎 ]∈ 𝓤 1
     U1𝐹 a∈𝓔𝓵0 with ⌜ 𝐹 ⌝ᶜ (⊆→∈ (𝓔𝓵₀⊇𝓔𝓵₁ ⌜ 𝐴 ⌝ᵈ U1𝐴) a∈𝓔𝓵0)
     ... | U0Fa = [⁈ 𝓤₀⊆𝓤₁ ⌜ U0Fa ⌝ ]

     unif²⊆ : ∀ {𝑎 𝑎'} → (a==a' : 𝑎 == 𝑎' ∈ 𝓔𝓵 1 U1𝐴) →
                 𝓔𝓵 1 ⌜ U1𝐹 ∙ˡ a==a' ⌝ ⊆ 𝓔𝓵 1 ⌜ U1𝐹 ∙ʳ a==a' ⌝
     unif²⊆ a==a' with (𝓔𝓵₀⊇𝓔𝓵₁ ⌜ 𝐴 ⌝ᵈ U1𝐴 a==a') | U1𝐹 ∙ˡ a==a' | U1𝐹 ∙ʳ a==a'
     ... | EL1-a==a' | [⁈ U1Fa ] | [⁈ U1Fa' ] with cod-unif² EL1-a==a'
     ... | El0Fa→Fa' , _ =  (𝓔𝓵₀⊆𝓔𝓵₁ ⌜ 𝐹 ·ʳ EL1-a==a' ⌝ᶜ (𝓤₀⊆𝓤₁ ⌜ 𝐹 ·ʳ EL1-a==a' ⌝ᶜ)) ∘ El0Fa→Fa' ∘ (𝓔𝓵₀⊇𝓔𝓵₁ ⌜ 𝐹 ·ˡ EL1-a==a' ⌝ᶜ (𝓤₀⊆𝓤₁ ⌜ 𝐹 ·ˡ EL1-a==a' ⌝ᶜ))

     unif²⊇ : ∀ {𝑎 𝑎'} → (a==a' : 𝑎 == 𝑎' ∈ 𝓔𝓵 1 U1𝐴) →
                 𝓔𝓵 1 ⌜ U1𝐹 ∙ʳ a==a' ⌝ ⊆ 𝓔𝓵 1 ⌜ U1𝐹 ∙ˡ a==a' ⌝
     unif²⊇ a==a' with (𝓔𝓵₀⊇𝓔𝓵₁ ⌜ 𝐴 ⌝ᵈ U1𝐴 a==a') | U1𝐹 ∙ˡ a==a' | U1𝐹 ∙ʳ a==a'
     ... | EL1-a==a' | [⁈ U1Fa ] | [⁈ U1Fa' ] with cod-unif² EL1-a==a'
     ... | _ , El0Fa'→Fa =  (𝓔𝓵₀⊆𝓔𝓵₁ ⌜ 𝐹 ·ˡ EL1-a==a' ⌝ᶜ (𝓤₀⊆𝓤₁ ⌜ 𝐹 ·ˡ EL1-a==a' ⌝ᶜ) ) ∘ El0Fa'→Fa ∘ (𝓔𝓵₀⊇𝓔𝓵₁ ⌜ 𝐹 ·ʳ EL1-a==a' ⌝ᶜ (𝓤₀⊆𝓤₁ ⌜ 𝐹 ·ʳ EL1-a==a' ⌝ᶜ))

     Pi' : Π-⟨ 𝓤 1 , 𝓔𝓵 1 ⟩ 𝐴 𝐹
     Π-dom {{Pi'}} = U1𝐴
     Π-cod {{Pi'}} = U1𝐹
     cod-unif¹ {{Π-props {{Pi'}}}} prf prf'
       rewrite cod-unif¹ (⊆→∈ (𝓔𝓵₀⊇𝓔𝓵₁ ⌜ 𝐴 ⌝ᵈ U1𝐴) prf) (⊆→∈ (𝓔𝓵₀⊇𝓔𝓵₁ ⌜ 𝐴 ⌝ᵈ U1𝐴) prf') = refl
     cod-unif² {{Π-props {{Pi'}}}} = λ a==a' → (unif²⊆ a==a') , (unif²⊇ a==a')

𝓢𝓮𝓽₀⊆𝓢𝓮𝓽₁ : ∀{𝐴 𝐵} → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽 0 → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽 1
𝓢𝓮𝓽₀⊆𝓢𝓮𝓽₁ (𝓢𝓮𝓽₀-NE NE==NE') = 𝓢𝓮𝓽ₖ₊₁-NE (≤′-step ≤′-refl) NE==NE'
𝓢𝓮𝓽₀⊆𝓢𝓮𝓽₁ 𝓢𝓮𝓽₀-𝑁 = 𝓢𝓮𝓽ₖ₊₁-𝑁
𝓢𝓮𝓽₀⊆𝓢𝓮𝓽₁ 𝓢𝓮𝓽₀-⊤ = 𝓢𝓮𝓽ₖ₊₁-⊤
𝓢𝓮𝓽₀⊆𝓢𝓮𝓽₁ 𝓢𝓮𝓽₀-⊥ = 𝓢𝓮𝓽ₖ₊₁-⊥
𝓢𝓮𝓽₀⊆𝓢𝓮𝓽₁ (𝓢𝓮𝓽₀-Π A==A' {𝓤₀-Π 𝐴 𝐹 {{Pi}}} {𝓤₀-Π 𝐴' 𝐹' {{Pi'}}} F==F') =
  𝓢𝓮𝓽ₖ₊₁-Π {{_}} {𝐴} {𝐹} {𝐴'} {𝐹'} A==A'+ {Pi+} {Pi'+} F==F'+
    where
      A==A'+ : 𝐴 == 𝐴' ∈ 𝓢𝓮𝓽 1
      A==A'+ = 𝓢𝓮𝓽₀⊆𝓢𝓮𝓽₁ A==A'

      Pi+ : Π-⟨ 𝓤 1 , 𝓔𝓵 1 ⟩ 𝐴 𝐹
      Pi+ with 𝓤₀⊆𝓤₁ (𝓤₀-Π 𝐴 𝐹)
      ... | 𝓤ₖ₊₁-Π 𝐴 𝐹 {{x}} = x

      Pi'+ : Π-⟨ 𝓤 1 , 𝓔𝓵 1 ⟩ 𝐴' 𝐹'
      Pi'+ with 𝓤₀⊆𝓤₁ (𝓤₀-Π 𝐴' 𝐹')
      ... | 𝓤ₖ₊₁-Π 𝐴' 𝐹' {{x}} = x

      F==F'+ : ⦃ Pi0 : Π-⟨ 𝓤 1 , 𝓔𝓵 1 ⟩ 𝐴 𝐹 ⦄
               ⦃ Pi0' : Π-⟨ 𝓤 1 , 𝓔𝓵 1 ⟩ 𝐴' 𝐹' ⦄ {a a' : 𝕍}
               (a==a' : a == a' ∈ 𝓔𝓵 1 ⌜ 𝐴 ⌝ᵈ) →
                   [ ⌜ 𝐹 ⌝ᶜ ∙ˡ a==a' ] == [ ⌜ 𝐹' ⌝ᶜ ∙ʳ 𝓔𝓵-resp-⊆ {1} (𝓢𝓮𝓽₀⊆𝓢𝓮𝓽₁ A==A') {⌜ 𝐴 ⌝ᵈ} {⌜ 𝐴' ⌝ᵈ} a==a' ] ∈ 𝓢𝓮𝓽 1
      F==F'+ {{Pi0}} {{Pi0'}} El1A-a==a' with F==F' {{Pi}} {{Pi'}} | 𝓔𝓵₀⊇𝓔𝓵₁ (Π-dom {{Pi}}) (Π-dom {{Pi+}})
      ... | F==F'-PiPi' | El+1Pi→El0Pi with 𝓔𝓵ₖ₊₁-unif {{𝕌 0}} (Π-dom {{Pi0}}) (𝓤₀⊆𝓤₁ (Π-dom {{Pi}}))
      ... | El1Pi0→EL1Pi , _  with El+1Pi→El0Pi (El1Pi0→EL1Pi El1A-a==a')
      ... | El0Pi-a==a' with F==F'-PiPi' El0Pi-a==a'
      ... | Fa==F'a'∈Set0 with 𝓢𝓮𝓽₀⊆𝓢𝓮𝓽₁ Fa==F'a'∈Set0
      ... | Fa==F'a'∈Set1 with (Π-cod {{Pi}}) ∙ˡ El0Pi-a==a'
                             | (Π-cod {{Pi'}}) ∙ʳ (𝓔𝓵₀-resp-⊆ A==A' El0Pi-a==a')
                             | (Π-cod {{Pi0}}) ∙ˡ El1A-a==a'
                             | (Π-cod {{Pi0'}}) ∙ʳ (𝓔𝓵ₖ₊₁-resp-⊆ {{𝕌 0}} A==A'+ {Π-dom {{Pi0}}} {Π-dom {{Pi0'}}} El1A-a==a')
      ... | record { ⁈-eval = F·a⇓x }
          | record { ⁈-eval = F'·a'⇓y }
          | record { ⁈-eval = F·a⇓x' }
          | record { ⁈-eval = F'·a'⇓y' }
            rewrite det-· F·a⇓x' F·a⇓x | det-· F'·a'⇓y' F'·a'⇓y
            = Fa==F'a'∈Set1
```
We also have the _other_ direction in specific circumstances: if
we know that a type code for `𝐴` already exists in the smaller universe, then
every `𝐵` it is related to above must already be related to it below.
That is to say, universe levels do not change existing equivalence classes.
```agda
𝓢𝓮𝓽₀⊇𝓢𝓮𝓽₁ : ∀{𝐴 𝐵} → 𝓤 0 𝐴 → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽 1 → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽 0
𝓢𝓮𝓽₀⊇𝓢𝓮𝓽₁ {.(↑⟨ ᶜ V𝑆𝑒𝑡 0 ⟩ _)} {.(↑⟨ ᶜ V𝑆𝑒𝑡 0 ⟩ _)} 𝓤₀-NE     (𝓢𝓮𝓽ₖ₊₁-NE x x₁) = 𝓢𝓮𝓽₀-NE x₁
𝓢𝓮𝓽₀⊇𝓢𝓮𝓽₁ {.(ᶜ V𝑁)}            {.(ᶜ V𝑁)}            𝓤₀-𝑁       𝓢𝓮𝓽ₖ₊₁-𝑁 = 𝓢𝓮𝓽₀-𝑁
𝓢𝓮𝓽₀⊇𝓢𝓮𝓽₁ {.(ᶜ V⊤)}            {.(ᶜ V⊤)}            𝓤₀-⊤       𝓢𝓮𝓽ₖ₊₁-⊤ = 𝓢𝓮𝓽₀-⊤
𝓢𝓮𝓽₀⊇𝓢𝓮𝓽₁ {.(ᶜ V⊥)}            {.(ᶜ V⊥)}            𝓤₀-⊥       𝓢𝓮𝓽ₖ₊₁-⊥ = 𝓢𝓮𝓽₀-⊥
𝓢𝓮𝓽₀⊇𝓢𝓮𝓽₁ {.(VΠ 𝐴 𝐹)}          {(VΠ 𝐴' 𝐹')}        (𝓤₀-Π 𝐴 𝐹 {{Pi₀}}) (𝓢𝓮𝓽ₖ₊₁-Π A==A'1 {Pi₁} {Pi'₁} F==F'1) with F==F'1 {{Pi₁}} {{Pi'₁}}
... | F==F' =  𝓢𝓮𝓽₀-Π  A==A'0 {(𝓤₀-Π 𝐴 𝐹 {{Pi₀}})} {U0ΠA'F'} F==F'0
    where
      A==A'0 : 𝐴 == 𝐴' ∈ 𝓢𝓮𝓽 0
      A==A'0 = 𝓢𝓮𝓽₀⊇𝓢𝓮𝓽₁ (Π-dom {{Pi₀}}) A==A'1

      U0A' : 𝓤 0 𝐴'
      U0A' =  π₀ʳ A==A'0

      U1A' : 𝓤 1 𝐴'
      U1A' = Π-dom {{Pi'₁}}

      F==F'0 : ∀ ⦃ Pi1 : Π-⟨ 𝓤 0 , 𝓔𝓵 0 ⟩ 𝐴 𝐹 ⦄ ⦃ Pi'1 : Π-⟨ 𝓤 0 , 𝓔𝓵 0 ⟩ 𝐴' 𝐹' ⦄ →
               {a a' : 𝕍} → (a==a' : a == a' ∈ 𝓔𝓵 0 (Π-dom {{Pi1}})) →
                [ (Π-cod {{Pi1}}) ∙ˡ a==a' ] == [ (Π-cod {{Pi'1}}) ∙ʳ 𝓔𝓵-resp-⊆ {0} A==A'0 a==a' ] ∈ 𝓢𝓮𝓽 0
      F==F'0 {{Pi1}} {{Pi'1}} a==a'El0A with (𝓔𝓵₀⊆𝓔𝓵₁ (Π-dom {{Pi1}}) (𝓤₀⊆𝓤₁ (Π-dom {{Pi1}})) a==a'El0A)
      ... | a==a'EL1'A with ((proj₁ (𝓔𝓵-unif {1} (𝓤₀⊆𝓤₁ (Π-dom {{Pi1}})) (Π-dom {{Pi₁}}))) a==a'EL1'A)
      ... | a==a'El1A with F==F' a==a'El1A
      ... | Fa==F'a'1 with Π-cod {{Pi1}} ∙ˡ a==a'El0A
                   | Π-cod {{Pi'1}} ∙ʳ (𝓔𝓵₀-resp-⊆ A==A'0 a==a'El0A)
                   | Π-cod {{Pi₁}} (memˡ a==a'El1A)
                   | Π-cod {{Pi'₁}} (memʳ (𝓔𝓵-resp-⊆ {1} A==A'1 {Π-dom {{Pi₁}}} {Π-dom {{Pi'₁}}} a==a'El1A))
      ... | record { ⁈ = U0Fa   ; ⁈-val = Fa   ; ⁈-eval = F·a⇓Fa }
          | record { ⁈ = U0F'a' ; ⁈-val = F'a' ; ⁈-eval = F'·a'⇓F'a' }
          | record { ⁈ = U1_Fa  ; ⁈-val = _Fa  ; ⁈-eval = F·a⇓_Fa }
          | record { ⁈ = U1_F'a'; ⁈-val = _F'a'; ⁈-eval = F'·a'⇓_F'a' }
            rewrite det-· F·a⇓_Fa F·a⇓Fa | det-· F'·a'⇓_F'a' F'·a'⇓F'a'
            = 𝓢𝓮𝓽₀⊇𝓢𝓮𝓽₁ U0Fa Fa==F'a'1

      --TODO can this be simplified?
      cod : ∀ {𝑎} → 𝑎 ∈ 𝓔𝓵₀ U0A' → [ 𝐹' ∙ 𝑎 ]∈ 𝓤₀
      cod a∈El0Dom with (⊆→∈ (𝓔𝓵-resp-⊇ {0} A==A'0 {Π-dom {{Pi₀}}} {U0A'})) a∈El0Dom
                               | ((⊆→∈ (𝓔𝓵-resp-⊇ {1} A==A'1 {Π-dom {{Pi₁}}} {U1A'})) ∘ (⊆→∈ (𝓔𝓵₀⊆𝓔𝓵₁ U0A' U1A'))) a∈El0Dom
      ... | a∈El0DomA | a∈El1Dom with (per-refl {{Per-𝓔𝓵 {1} (Π-dom {{Pi₁}})}} a∈El1Dom)
      ... | a==aEl1 with F==F' a==aEl1
      ... | Fa==F'a1 with (𝓔𝓵-resp-⊆ {1} A==A'1 {Π-dom {{Pi₁}}} {U1A'} a==aEl1)
      ... | a==aElA'1 with (Π-cod {{Pi₀}} a∈El0DomA) | Π-cod {{Pi₁}} (memˡ a==aEl1) | Π-cod {{Pi'₁}} (memʳ a==aElA'1)
      ... | record { ⁈ = U0Fa; ⁈-val = Fa; ⁈-eval = F·a⇓Fa }
          | record { ⁈ = U1Fa; ⁈-val = Fa_; ⁈-eval = F·a⇓Fa_ }
          | record { ⁈ = U1F'a; ⁈-val = F'a; ⁈-eval = F'·a⇓F'a } rewrite det-· F·a⇓Fa_ F·a⇓Fa with 𝓢𝓮𝓽₀⊇𝓢𝓮𝓽₁ U0Fa Fa==F'a1
      ... | Fa==F'a0 with π₀ʳ Fa==F'a0
      ... | U0F'a = [⁈ U0F'a ]

      Pi'₀ :  Π-⟨ 𝓤 0 , 𝓔𝓵 0 ⟩ 𝐴' 𝐹'
      Π-dom {{Pi'₀}} = U0A'
      Π-cod {{Pi'₀}} = cod

      -- TODO: these seem very tedious, we might need a weaker notion of equality for [ 𝐹' ∙ 𝑎 ]∈ 𝓤₀
      cod-unif¹ {{Π-props {{Pi'₀}}}} prf prf' = {!!}
      cod-unif² {{Π-props {{Pi'₀}}}} a==a'El0A with cod ∙ʳ a==a'El0A | cod ∙ˡ a==a'El0A
      ... | u | v = {!!}

      U0ΠA'F' : 𝓤 0 (VΠ 𝐴' 𝐹')
      U0ΠA'F' = 𝓤₀-Π 𝐴' 𝐹' {{Pi'₀}}


𝓔𝓵₁⊆𝓔𝓵₂ : ∀{𝐴} → (UA : 𝓤 1 𝐴) →(UA' : 𝓤 2 𝐴)  → 𝓔𝓵 1 UA ⊆ 𝓔𝓵 2 UA'
𝓔𝓵₁⊇𝓔𝓵₂ : ∀{𝐴} → (UA : 𝓤 1 𝐴) →(UA' : 𝓤 2 𝐴)  → 𝓔𝓵 2 UA' ⊆ 𝓔𝓵 1 UA

𝓔𝓵₁⊆𝓔𝓵₂ (𝓤ₖ₊₁-NE x) (𝓤ₖ₊₁-NE x₁) = λ z → z
𝓔𝓵₁⊆𝓔𝓵₂ 𝓤ₖ₊₁-𝑁 𝓤ₖ₊₁-𝑁 = λ z → z
𝓔𝓵₁⊆𝓔𝓵₂ 𝓤ₖ₊₁-⊤ 𝓤ₖ₊₁-⊤ = λ z → z
𝓔𝓵₁⊆𝓔𝓵₂ 𝓤ₖ₊₁-⊥ 𝓤ₖ₊₁-⊥ = λ z → z
-- abstract types are straightforward, we just need to massage the components into the next level, using
-- the coercions from the previous level
𝓔𝓵₁⊆𝓔𝓵₂ (𝓤ₖ₊₁-⟪Type⋯⟫ U0S U0T) (𝓤ₖ₊₁-⟪Type⋯⟫ U1S U1T) (𝓥Type-ne S==S'0 T==T'0 S==S''0 T==T''0 NE==NE') =
  𝓥Type-ne (𝓢𝓮𝓽₀⊆𝓢𝓮𝓽₁ S==S'0) (𝓢𝓮𝓽₀⊆𝓢𝓮𝓽₁ T==T'0) (𝓢𝓮𝓽₀⊆𝓢𝓮𝓽₁ S==S''0) (𝓢𝓮𝓽₀⊆𝓢𝓮𝓽₁ T==T''0) NE==NE'
𝓔𝓵₁⊆𝓔𝓵₂ (𝓤ₖ₊₁-⟪Type⋯⟫ {𝑆} {𝑇} U0S U0T) (𝓤ₖ₊₁-⟪Type⋯⟫ U1S U1T) (𝓥Type-val {𝑋} X==X'0 S<:₀X<:₀T) with π₀ˡ X==X'0
... | U0X with S<:₀X<:₀T U0S U0X U0T
... | El0S→El0X , El0X→El0T = 𝓥Type-val (𝓢𝓮𝓽₀⊆𝓢𝓮𝓽₁ X==X'0) S<:₁X<:₁T
  where
     S<:₁X<:₁T : ⟦_<:_<:_⟧ {{𝕌 1}} 𝑆 𝑋 𝑇
     S<:₁X<:₁T U1S' U1X U1T' = ((𝓔𝓵₀⊆𝓔𝓵₁ U0X U1X) ∘ El0S→El0X ∘ (𝓔𝓵₀⊇𝓔𝓵₁ U0S U1S')) , ((𝓔𝓵₀⊆𝓔𝓵₁ U0T U1T') ∘ El0X→El0T ∘ (𝓔𝓵₀⊇𝓔𝓵₁ U0X U1X))
𝓔𝓵₁⊆𝓔𝓵₂ (𝓤ₖ₊₁-𝑆𝑒𝑡< ≤′-refl) (𝓤ₖ₊₁-𝑆𝑒𝑡< (≤′-step ≤′-refl)) = λ z → z
𝓔𝓵₁⊆𝓔𝓵₂ (𝓤ₖ₊₁-Π 𝐴 𝐹 {{Pi}}) (𝓤ₖ₊₁-Π .𝐴 .𝐹 {{Pi'}}) {f} {f'} f==f'∈Π1 a==a'∈El2 with (𝓔𝓵₁⊇𝓔𝓵₂ (Π-dom {{Pi}}) (Π-dom {{Pi'}}) a==a'∈El2)
... | a==a'∈El1 with  f==f'∈Π1 a==a'∈El1
... | [⁈-rel fa==f'a'∈𝐹a ] with Π-cod {{Pi}} (memˡ a==a'∈El1) | Π-cod {{Pi'}} (memˡ a==a'∈El2)
... | record { ⁈-val = Fa; ⁈-eval = 𝐹·𝑎⇓Fa; ⁈ = U1Fa }
    | record { ⁈-val = Fa2; ⁈-eval = 𝐹·𝑎⇓Fa2; ⁈ = U2Fa } rewrite det-· 𝐹·𝑎⇓Fa 𝐹·𝑎⇓Fa2
       = [⁈-rel 𝓔𝓵₁⊆𝓔𝓵₂ U1Fa U2Fa fa==f'a'∈𝐹a ]

𝓔𝓵₁⊇𝓔𝓵₂ (𝓤ₖ₊₁-NE x) (𝓤ₖ₊₁-NE x₁) = λ z → z
𝓔𝓵₁⊇𝓔𝓵₂ 𝓤ₖ₊₁-𝑁 𝓤ₖ₊₁-𝑁 = λ z → z
𝓔𝓵₁⊇𝓔𝓵₂ 𝓤ₖ₊₁-⊤ 𝓤ₖ₊₁-⊤ = λ z → z
𝓔𝓵₁⊇𝓔𝓵₂ 𝓤ₖ₊₁-⊥ 𝓤ₖ₊₁-⊥ = λ z → z
𝓔𝓵₁⊇𝓔𝓵₂ (𝓤ₖ₊₁-⟪Type⋯⟫ U0S U0T) (𝓤ₖ₊₁-⟪Type⋯⟫ U1S U1T) (𝓥Type-ne S==S'1 T==T'1 S==S''1 T==T''1 NE==NE') =
  {!𝓥Type-ne (𝓢𝓮𝓽₀⊇𝓢𝓮𝓽₁ S==S'1) (𝓢𝓮𝓽₀⊇𝓢𝓮𝓽₁ T==T'1) (𝓢𝓮𝓽₀⊇𝓢𝓮𝓽₁ S==S''1) (𝓢𝓮𝓽₀⊇𝓢𝓮𝓽₁ T==T''1) NE==NE'!}
𝓔𝓵₁⊇𝓔𝓵₂ (𝓤ₖ₊₁-⟪Type⋯⟫ U0S U0T) (𝓤ₖ₊₁-⟪Type⋯⟫ U1S U1T) (𝓥Type-val {𝑋} X==X'1 S<:₁X<:₁T) = 𝓥Type-val {!!} {!!}
𝓔𝓵₁⊇𝓔𝓵₂ (𝓤ₖ₊₁-𝑆𝑒𝑡< ≤′-refl) (𝓤ₖ₊₁-𝑆𝑒𝑡< (≤′-step ≤′-refl)) = λ z → z
𝓔𝓵₁⊇𝓔𝓵₂ (𝓤ₖ₊₁-Π 𝐴 𝐹) (𝓤ₖ₊₁-Π .𝐴 .𝐹) = {!!}

𝓤₁⊆𝓤₂ : ∀{𝐴} → 𝓤 1 𝐴 → 𝓤 2 𝐴
𝓤₁⊆𝓤₂ (𝓤ₖ₊₁-NE x) = 𝓤ₖ₊₁-NE (≤′-step x)
𝓤₁⊆𝓤₂ 𝓤ₖ₊₁-𝑁 = 𝓤ₖ₊₁-𝑁
𝓤₁⊆𝓤₂ 𝓤ₖ₊₁-⊤ = 𝓤ₖ₊₁-⊤
𝓤₁⊆𝓤₂ 𝓤ₖ₊₁-⊥ = 𝓤ₖ₊₁-⊥
𝓤₁⊆𝓤₂ (𝓤ₖ₊₁-⟪Type⋯⟫ ↓US ↓UT) = 𝓤ₖ₊₁-⟪Type⋯⟫ (𝓤₀⊆𝓤₁ ↓US) (𝓤₀⊆𝓤₁ ↓UT)
𝓤₁⊆𝓤₂ (𝓤ₖ₊₁-𝑆𝑒𝑡< x) = 𝓤ₖ₊₁-𝑆𝑒𝑡< (≤′-step x)
𝓤₁⊆𝓤₂ (𝓤ₖ₊₁-Π 𝐴 𝐹 {{Pi}}) = 𝓤ₖ₊₁-Π 𝐴 𝐹 {{Pi'}}
  where
     U2𝐴 : 𝓤 2 𝐴
     U2𝐴 = 𝓤₁⊆𝓤₂ ⌜ 𝐴 ⌝ᵈ

     U2𝐹 : ∀ {𝑎} → 𝑎 ∈ 𝓔𝓵 2 U2𝐴 → [ 𝐹 ∙ 𝑎 ]∈ 𝓤 2
     U2𝐹 a∈𝓔𝓵1 with ⌜ 𝐹 ⌝ᶜ (⊆→∈ (𝓔𝓵₁⊇𝓔𝓵₂ ⌜ 𝐴 ⌝ᵈ U2𝐴) a∈𝓔𝓵1)
     ... | U1Fa = [⁈ 𝓤₁⊆𝓤₂ ⌜ U1Fa ⌝ ]

     unif²⊆ : ∀ {𝑎 𝑎'} → (a==a' : 𝑎 == 𝑎' ∈ 𝓔𝓵 2 U2𝐴) →
                 𝓔𝓵 2 ⌜ U2𝐹 ∙ˡ a==a' ⌝ ⊆ 𝓔𝓵 2 ⌜ U2𝐹 ∙ʳ a==a' ⌝
     unif²⊆ a==a' with (𝓔𝓵₁⊇𝓔𝓵₂ ⌜ 𝐴 ⌝ᵈ U2𝐴 a==a') | U2𝐹 ∙ˡ a==a' | U2𝐹 ∙ʳ a==a'
     ... | EL2-a==a' | [⁈ U2Fa ] | [⁈ U2Fa' ] with cod-unif² EL2-a==a'
     ... | El1Fa→Fa' , _ = (𝓔𝓵₁⊆𝓔𝓵₂ ⌜ 𝐹 ·ʳ EL2-a==a' ⌝ᶜ (𝓤₁⊆𝓤₂ ⌜ 𝐹 ·ʳ EL2-a==a' ⌝ᶜ)) ∘ El1Fa→Fa' ∘ (𝓔𝓵₁⊇𝓔𝓵₂ ⌜ 𝐹 ·ˡ EL2-a==a' ⌝ᶜ (𝓤₁⊆𝓤₂ ⌜ 𝐹 ·ˡ EL2-a==a' ⌝ᶜ))

     unif²⊇ : ∀ {𝑎 𝑎'} → (a==a' : 𝑎 == 𝑎' ∈ 𝓔𝓵 2 U2𝐴) →
                 𝓔𝓵 2 ⌜ U2𝐹 ∙ʳ a==a' ⌝ ⊆ 𝓔𝓵 2 ⌜ U2𝐹 ∙ˡ a==a' ⌝
     unif²⊇ a==a' with (𝓔𝓵₁⊇𝓔𝓵₂ ⌜ 𝐴 ⌝ᵈ U2𝐴 a==a') | U2𝐹 ∙ˡ a==a' | U2𝐹 ∙ʳ a==a'
     ... | EL2-a==a' | [⁈ U2Fa ] | [⁈ U2Fa' ] with cod-unif² EL2-a==a'
     ... | _ , El1Fa'→Fa = (𝓔𝓵₁⊆𝓔𝓵₂ ⌜ 𝐹 ·ˡ EL2-a==a' ⌝ᶜ (𝓤₁⊆𝓤₂ ⌜ 𝐹 ·ˡ EL2-a==a' ⌝ᶜ) ) ∘ El1Fa'→Fa ∘ (𝓔𝓵₁⊇𝓔𝓵₂ ⌜ 𝐹 ·ʳ EL2-a==a' ⌝ᶜ (𝓤₁⊆𝓤₂ ⌜ 𝐹 ·ʳ EL2-a==a' ⌝ᶜ))

     Pi' : Π-⟨ 𝓤 2 , 𝓔𝓵 2 ⟩ 𝐴 𝐹
     Π-dom {{Pi'}} = U2𝐴
     Π-cod {{Pi'}} = U2𝐹
     cod-unif¹ {{Π-props {{Pi'}}}} prf prf'
       rewrite cod-unif¹ (⊆→∈ (𝓔𝓵₁⊇𝓔𝓵₂ ⌜ 𝐴 ⌝ᵈ U2𝐴) prf) (⊆→∈ (𝓔𝓵₁⊇𝓔𝓵₂ ⌜ 𝐴 ⌝ᵈ U2𝐴) prf') = refl
     cod-unif² {{Π-props {{Pi'}}}} = λ a==a' → (unif²⊆ a==a') , (unif²⊇ a==a')

𝓢𝓮𝓽₁⊆𝓢𝓮𝓽₂ : ∀{𝐴 𝐵} → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽 1 → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽 2
𝓢𝓮𝓽₁⊆𝓢𝓮𝓽₂ = {!!}



𝓤ₖ⊆𝓤ₖ₊₁   : ∀{𝓀} → ∀{𝐴} → 𝓤 𝓀 𝐴 → 𝓤 (suc 𝓀) 𝐴
𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ : ∀{𝓀} → ∀{𝐴 𝐵} → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽 𝓀 → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽 (suc 𝓀)
```
Furthermore, the interpretation of a type code at a given level is stable, i.e.,
it is preserved by the successor universe:
```agda
-- it should indeed hold that (UA : 𝓤 𝓀 𝐴) → 𝓔𝓵 𝓀 UA ≡ᴿ 𝓔𝓵 (suc 𝓀) (𝓤ₖ⊆𝓤ₖ₊₁ UA)
-- this stronger property allows contravariant use in the Pi type cases
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ : ∀{𝓀} → ∀{𝐴} → (UA : 𝓤 𝓀 𝐴) → 𝓔𝓵 𝓀 UA ⊆ 𝓔𝓵 (suc 𝓀) (𝓤ₖ⊆𝓤ₖ₊₁ UA)
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ : ∀{𝓀} → ∀{𝐴} → (UA : 𝓤 𝓀 𝐴) → 𝓔𝓵 (suc 𝓀) (𝓤ₖ⊆𝓤ₖ₊₁ UA) ⊆ 𝓔𝓵 𝓀 UA
```
We prove these in tandem:
```agda
𝓤ₖ⊆𝓤ₖ₊₁ {zero}        (𝓤₀-NE {NE})                     = 𝓤ₖ₊₁-NE {{𝕌 0}} {NE} (≤′-step ≤′-refl)
𝓤ₖ⊆𝓤ₖ₊₁ {zero}         𝓤₀-𝑁                            = 𝓤ₖ₊₁-𝑁
𝓤ₖ⊆𝓤ₖ₊₁ {zero}         𝓤₀-⊤                            = 𝓤ₖ₊₁-⊤
𝓤ₖ⊆𝓤ₖ₊₁ {zero}         𝓤₀-⊥                            = 𝓤ₖ₊₁-⊥
𝓤ₖ⊆𝓤ₖ₊₁ {zero}        (𝓤₀-Π 𝐴 𝐹 {{Pi}})                = 𝓤ₖ₊₁-Π 𝐴 𝐹 {{Pi'}}
  where
     U1𝐴 : 𝓤 1 𝐴
     U1𝐴 = 𝓤ₖ⊆𝓤ₖ₊₁ ⌜ 𝐴 ⌝ᵈ

     U1𝐹 : ∀ {𝑎} → 𝑎 ∈ 𝓔𝓵 1 U1𝐴 → [ 𝐹 ∙ 𝑎 ]∈ 𝓤 1
     U1𝐹 a∈𝓔𝓵0 with ⌜ 𝐹 ⌝ᶜ (⊆→∈ (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ) a∈𝓔𝓵0)
     ... | U0Fa = [⁈ 𝓤ₖ⊆𝓤ₖ₊₁ ⌜ U0Fa ⌝ ]

     unif²⊆ : ∀ {𝑎 𝑎'} → (a==a' : 𝑎 == 𝑎' ∈ 𝓔𝓵 1 (𝓤ₖ⊆𝓤ₖ₊₁ ⌜ 𝐴 ⌝ᵈ)) →
                 𝓔𝓵 1 ⌜ U1𝐹 ∙ˡ a==a' ⌝ ⊆ 𝓔𝓵 1 ⌜ U1𝐹 ∙ʳ a==a' ⌝
     unif²⊆ a==a' with (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ a==a') | U1𝐹 ∙ˡ a==a' | U1𝐹 ∙ʳ a==a'
     ... | EL1-a==a' | [⁈ U1Fa ] | [⁈ U1Fa' ] with cod-unif² EL1-a==a'
     ... | El0Fa→Fa' , _ =  (𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ ⌜ 𝐹 ·ʳ EL1-a==a' ⌝ᶜ) ∘ El0Fa→Fa' ∘ (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ ⌜ 𝐹 ·ˡ EL1-a==a' ⌝ᶜ)

     unif²⊇ : ∀ {𝑎 𝑎'} → (a==a' : 𝑎 == 𝑎' ∈ 𝓔𝓵 1 (𝓤ₖ⊆𝓤ₖ₊₁ ⌜ 𝐴 ⌝ᵈ)) →
                 𝓔𝓵 1 ⌜ U1𝐹 ∙ʳ a==a' ⌝ ⊆ 𝓔𝓵 1 ⌜ U1𝐹 ∙ˡ a==a' ⌝
     unif²⊇ a==a' with (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ a==a') | U1𝐹 ∙ˡ a==a' | U1𝐹 ∙ʳ a==a'
     ... | EL1-a==a' | [⁈ U1Fa ] | [⁈ U1Fa' ] with cod-unif² EL1-a==a'
     ... | _ , El0Fa'→Fa =  (𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ ⌜ 𝐹 ·ˡ EL1-a==a' ⌝ᶜ) ∘ El0Fa'→Fa ∘ (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ ⌜ 𝐹 ·ʳ EL1-a==a' ⌝ᶜ)

     Pi' : Π-⟨ 𝓤 1 , 𝓔𝓵 1 ⟩ 𝐴 𝐹
     Π-dom {{Pi'}} = U1𝐴
     Π-cod {{Pi'}} = U1𝐹
     cod-unif¹ {{Π-props {{Pi'}}}} prf prf'
       rewrite cod-unif¹ (⊆→∈ (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ) prf) (⊆→∈ (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ) prf') = refl
     cod-unif² {{Π-props {{Pi'}}}} = λ a==a' → (unif²⊆ a==a') , (unif²⊇ a==a')


𝓤ₖ⊆𝓤ₖ₊₁ {suc 𝓀}       (𝓤ₖ₊₁-NE lt) rewrite (𝕌𝓀↓𝓀≡ 𝓀)   = 𝓤ₖ₊₁-NE (≤′-step lt)
𝓤ₖ⊆𝓤ₖ₊₁ {suc 𝓀}        𝓤ₖ₊₁-𝑁                          = 𝓤ₖ₊₁-𝑁
𝓤ₖ⊆𝓤ₖ₊₁ {suc 𝓀}        𝓤ₖ₊₁-⊤                          = 𝓤ₖ₊₁-⊤
𝓤ₖ⊆𝓤ₖ₊₁ {suc 𝓀}        𝓤ₖ₊₁-⊥                          = 𝓤ₖ₊₁-⊥
𝓤ₖ⊆𝓤ₖ₊₁ {suc 0}       (𝓤ₖ₊₁-⟪Type⋯⟫ ↓US ↓UT)           = 𝓤ₖ₊₁-⟪Type⋯⟫ (𝓤ₖ⊆𝓤ₖ₊₁ ↓US) (𝓤ₖ⊆𝓤ₖ₊₁ ↓UT)
𝓤ₖ⊆𝓤ₖ₊₁ {suc (suc 𝓀)} (𝓤ₖ₊₁-⟪Type⋯⟫ ↓US ↓UT)           = 𝓤ₖ₊₁-⟪Type⋯⟫ (𝓤ₖ⊆𝓤ₖ₊₁ ↓US) (𝓤ₖ⊆𝓤ₖ₊₁ ↓UT)
𝓤ₖ⊆𝓤ₖ₊₁ {suc 𝓀}       (𝓤ₖ₊₁-𝑆𝑒𝑡< lt) rewrite (𝕌𝓀↓𝓀≡ 𝓀) = 𝓤ₖ₊₁-𝑆𝑒𝑡< (≤′-step lt)
𝓤ₖ⊆𝓤ₖ₊₁ {suc 𝓀}       (𝓤ₖ₊₁-Π 𝐴 𝐹 {{Pi}})              = 𝓤ₖ₊₁-Π 𝐴 𝐹 {{Pi'}}
  where
     U1𝐴 : 𝓤 (suc (suc 𝓀)) 𝐴
     U1𝐴 = 𝓤ₖ⊆𝓤ₖ₊₁ ⌜ 𝐴 ⌝ᵈ

     U1𝐹 : ∀ {𝑎} → 𝑎 ∈ 𝓔𝓵 (suc (suc 𝓀)) U1𝐴 → [ 𝐹 ∙ 𝑎 ]∈ 𝓤 (suc (suc 𝓀))
     U1𝐹 a∈𝓔𝓵 with ⌜ 𝐹 ⌝ᶜ (⊆→∈ (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ) a∈𝓔𝓵)
     ... | U0Fa = [⁈ 𝓤ₖ⊆𝓤ₖ₊₁ ⌜ U0Fa ⌝ ]

     unif²⊆ : ∀ {𝑎 𝑎'} → (a==a' : 𝑎 == 𝑎' ∈ 𝓔𝓵 (suc (suc 𝓀)) (𝓤ₖ⊆𝓤ₖ₊₁ ⌜ 𝐴 ⌝ᵈ)) →
                 𝓔𝓵 (suc (suc 𝓀)) ⌜ U1𝐹 ∙ˡ a==a' ⌝ ⊆ 𝓔𝓵 (suc (suc 𝓀)) ⌜ U1𝐹 ∙ʳ a==a' ⌝
     unif²⊆ a==a' with (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ a==a') | U1𝐹 ∙ˡ a==a' | U1𝐹 ∙ʳ a==a'
     ... | EL1-a==a' | [⁈ U1Fa ] | [⁈ U1Fa' ] with cod-unif² EL1-a==a'
     ... | El0Fa→Fa' , _ =  (𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ ⌜ 𝐹 ·ʳ EL1-a==a' ⌝ᶜ) ∘ El0Fa→Fa' ∘ (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ ⌜ 𝐹 ·ˡ EL1-a==a' ⌝ᶜ)

     unif²⊇ : ∀ {𝑎 𝑎'} → (a==a' : 𝑎 == 𝑎' ∈ 𝓔𝓵 (suc (suc 𝓀)) (𝓤ₖ⊆𝓤ₖ₊₁ ⌜ 𝐴 ⌝ᵈ)) →
                 𝓔𝓵 (suc (suc 𝓀)) ⌜ U1𝐹 ∙ʳ a==a' ⌝ ⊆ 𝓔𝓵 (suc (suc 𝓀)) ⌜ U1𝐹 ∙ˡ a==a' ⌝
     unif²⊇ a==a' with (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ a==a') | U1𝐹 ∙ˡ a==a' | U1𝐹 ∙ʳ a==a'
     ... | EL1-a==a' | [⁈ U1Fa ] | [⁈ U1Fa' ] with cod-unif² EL1-a==a'
     ... | _ , El0Fa'→Fa = (𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ ⌜ 𝐹 ·ˡ EL1-a==a' ⌝ᶜ) ∘ El0Fa'→Fa ∘ (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ ⌜ 𝐹 ·ʳ EL1-a==a' ⌝ᶜ)

     Pi' : Π-⟨ 𝓤 (suc (suc 𝓀)) , 𝓔𝓵 (suc (suc 𝓀)) ⟩ 𝐴 𝐹
     Π-dom {{Pi'}} = U1𝐴
     Π-cod {{Pi'}} = U1𝐹
     cod-unif¹ {{Π-props {{Pi'}}}} prf prf'
        rewrite cod-unif¹ (⊆→∈ (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ) prf) (⊆→∈ (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ) prf') = refl
     cod-unif² {{Π-props {{Pi'}}}} = λ a==a' → (unif²⊆ a==a') , (unif²⊇ a==a')

𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {zero}         𝓤₀-NE                         = λ z → z
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {zero}         𝓤₀-𝑁                          = λ z → z
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {zero}         𝓤₀-⊤                          = λ z → z
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {zero}         𝓤₀-⊥                          = λ z → z
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {zero}        (𝓤₀-Π 𝐴 𝐹) {f} {f'}   f==f'∈Π0 a==a' with (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ a==a')
... | a==a'∈El0 with ⌜ 𝐹 ·ˡ a==a'∈El0 ⌝ᶜ | f==f'∈Π0 a==a'∈El0
... | U0Fa | [⁈-rel fa==f'a'∈𝐹a ] = [⁈-rel 𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ U0Fa fa==f'a'∈𝐹a ]


𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {suc 𝓀}       (𝓤ₖ₊₁-NE lt) rewrite (𝕌𝓀↓𝓀≡ 𝓀) = λ z → z
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {suc 𝓀}        𝓤ₖ₊₁-𝑁                         = λ z → z
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {suc 𝓀}        𝓤ₖ₊₁-⊤                         = λ z → z
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {suc 𝓀}        𝓤ₖ₊₁-⊥                         = λ z → z
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {suc zero} (𝓤ₖ₊₁-⟪Type⋯⟫ UT US) (𝓥Type-ne x x₁ x₂ x₃ x₄) = {!!}
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {suc zero} (𝓤ₖ₊₁-⟪Type⋯⟫ UT US) (𝓥Type-val x x₁) = {!!}
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {suc (suc 𝓀)} (𝓤ₖ₊₁-⟪Type⋯⟫ UT US) (𝓥Type-ne x x₁ x₂ x₃ x₄) = {!!}
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {suc (suc 𝓀)} (𝓤ₖ₊₁-⟪Type⋯⟫ UT US) (𝓥Type-val x x₁) = {!!}
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {suc zero}    (𝓤ₖ₊₁-𝑆𝑒𝑡< ≤′-refl)            = λ z → z
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {suc (suc 𝓀)} (𝓤ₖ₊₁-𝑆𝑒𝑡< ≤′-refl)            = λ z → z
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {suc (suc 𝓀)} (𝓤ₖ₊₁-𝑆𝑒𝑡< (≤′-step lt))       = λ z → z
𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {suc 𝓀}       (𝓤ₖ₊₁-Π 𝐴 𝐹)  {f} {f'}   f==f'∈Πk+1 a==a' with (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc 𝓀}  ⌜ 𝐴 ⌝ᵈ a==a')
... | a==a'∈Elk+1 with ⌜ 𝐹 ·ˡ a==a'∈Elk+1 ⌝ᶜ | f==f'∈Πk+1 a==a'∈Elk+1
... | Uk+1Fa | [⁈-rel fa==f'a'∈𝐹a ] = [⁈-rel 𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {suc 𝓀} Uk+1Fa fa==f'a'∈𝐹a ]

𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {zero}         𝓤₀-NE                         = λ z → z
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {zero}         𝓤₀-𝑁                          = λ z → z
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {zero}         𝓤₀-⊤                          = λ z → z
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {zero}         𝓤₀-⊥                          = λ z → z
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {zero}        (𝓤₀-Π 𝐴 𝐹) {f} {f'}   f==f'∈Π1 a==a' with (𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ ⌜ 𝐴 ⌝ᵈ a==a')
... | a==a'∈El1 with f==f'∈Π1 a==a'∈El1
... | [⁈-rel fa==f'a'∈𝐹a ]
      rewrite cod-unif¹ (memˡ (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ Π-dom a==a'∈El1))
                        (memˡ a==a')
      with  ⌜ 𝐹 ·ˡ a==a' ⌝ᶜ
... | U0Fa = [⁈-rel 𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ U0Fa fa==f'a'∈𝐹a ]

𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc 𝓀}       (𝓤ₖ₊₁-NE lt) rewrite (𝕌𝓀↓𝓀≡ 𝓀) = λ z → z
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc 𝓀}        𝓤ₖ₊₁-𝑁                        = λ z → z
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc 𝓀}        𝓤ₖ₊₁-⊤                        = λ z → z
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc 𝓀}        𝓤ₖ₊₁-⊥                        = λ z → z
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc zero} (𝓤ₖ₊₁-⟪Type⋯⟫ UT US) (𝓥Type-ne x x₁ x₂ x₃ x₄) = {!!}
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc zero} (𝓤ₖ₊₁-⟪Type⋯⟫ UT US) (𝓥Type-val x x₁) = {!!}
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc (suc 𝓀)} (𝓤ₖ₊₁-⟪Type⋯⟫ UT US) (𝓥Type-ne x x₁ x₂ x₃ x₄) = {!!}
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc (suc 𝓀)} (𝓤ₖ₊₁-⟪Type⋯⟫ UT US) (𝓥Type-val x x₁) = {!!}
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc zero}    (𝓤ₖ₊₁-𝑆𝑒𝑡< ≤′-refl)            = λ z → z
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc (suc 𝓀)} (𝓤ₖ₊₁-𝑆𝑒𝑡< ≤′-refl)            = λ z → z
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc (suc 𝓀)} (𝓤ₖ₊₁-𝑆𝑒𝑡< (≤′-step lt))       = λ z → z
𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc 𝓀}       (𝓤ₖ₊₁-Π 𝐴 𝐹) {f} {f'} f==f'∈Πk+2 a==a' with (𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ {suc 𝓀} ⌜ 𝐴 ⌝ᵈ a==a')
... | a==a'∈Elk+2 with f==f'∈Πk+2 a==a'∈Elk+2
... | [⁈-rel fa==f'a'∈𝐹a ]
      rewrite cod-unif¹ (memˡ (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc 𝓀} Π-dom a==a'∈Elk+2))
                        (memˡ a==a')
      with  ⌜ 𝐹 ·ˡ a==a' ⌝ᶜ
... | Uk+1Fa = [⁈-rel 𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc 𝓀} Uk+1Fa fa==f'a'∈𝐹a ]
```
## Upcast Lemmas for 𝓤 and 𝓔𝓵

Using the previous lemmas, we prove their more general counterparts, which relate
a universe level to arbitrary larger levels. These lemmas provide useful
"upcast" operations:

```agda
𝓤↑ : ∀{𝓁 𝓀} → 𝓁 ≤′ 𝓀 → ∀{𝐴} → 𝓤 𝓁 𝐴 → 𝓤 𝓀 𝐴
𝓤↑ ≤′-refl       = λ u → u
𝓤↑ (≤′-step 𝓁≤𝓀) = 𝓤ₖ⊆𝓤ₖ₊₁ ∘ (𝓤↑ 𝓁≤𝓀)

𝓔𝓵↑ : ∀{𝓁 𝓀} → (𝓁≤𝓀 : 𝓁 ≤′ 𝓀) → ∀{𝐴} → (UA : 𝓤 𝓁 𝐴) → 𝓔𝓵 𝓁 UA ≡ᴿ 𝓔𝓵 𝓀 (𝓤↑ 𝓁≤𝓀 UA)
𝓔𝓵↑ ≤′-refl       _  = ≡→≡ᴿ refl
𝓔𝓵↑ (≤′-step 𝓁≤𝓀) UA = (𝓔𝓵ₖ⊆𝓔𝓵ₖ₊₁ (𝓤↑ 𝓁≤𝓀 UA)) ∘ (proj₁ (𝓔𝓵↑ 𝓁≤𝓀 UA)) ,
                       (proj₂ (𝓔𝓵↑ 𝓁≤𝓀 UA))     ∘ (𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ (𝓤↑ 𝓁≤𝓀 UA))
```
## Cumulativity of 𝓢𝓮𝓽

Similarly, we first prove that two related codes at one universe level remain
related in the immediate successor universe:

```agda
𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ {zero}        (𝓢𝓮𝓽₀-NE NE==NE') = 𝓢𝓮𝓽ₖ₊₁-NE (≤′-step ≤′-refl) NE==NE'
𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ {zero}         𝓢𝓮𝓽₀-𝑁 = 𝓢𝓮𝓽ₖ₊₁-𝑁
𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ {zero}         𝓢𝓮𝓽₀-⊤ = 𝓢𝓮𝓽ₖ₊₁-⊤
𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ {zero}         𝓢𝓮𝓽₀-⊥ = 𝓢𝓮𝓽ₖ₊₁-⊥
𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ {zero}        (𝓢𝓮𝓽₀-Π A==A' {𝓤₀-Π 𝐴 𝐹 {{Pi}}} {𝓤₀-Π 𝐴' 𝐹' {{Pi'}}} F==F') =
  𝓢𝓮𝓽ₖ₊₁-Π {{_}} {𝐴} {𝐹} {𝐴'} {𝐹'} A==A'+ {Pi+} {Pi'+} F==F'+
    where
      A==A'+ : 𝐴 == 𝐴' ∈ 𝓢𝓮𝓽 1
      A==A'+ = 𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ A==A'

      Pi+ : Π-⟨ 𝓤 1 , 𝓔𝓵 1 ⟩ 𝐴 𝐹
      Pi+ with 𝓤ₖ⊆𝓤ₖ₊₁ (𝓤₀-Π 𝐴 𝐹)
      ... | 𝓤ₖ₊₁-Π 𝐴 𝐹 {{x}} = x

      Pi'+ : Π-⟨ 𝓤 1 , 𝓔𝓵 1 ⟩ 𝐴' 𝐹'
      Pi'+ with 𝓤ₖ⊆𝓤ₖ₊₁ (𝓤₀-Π 𝐴' 𝐹')
      ... | 𝓤ₖ₊₁-Π 𝐴' 𝐹' {{x}} = x

      F==F'+ : ⦃ Pi0 : Π-⟨ 𝓤 1 , 𝓔𝓵 1 ⟩ 𝐴 𝐹 ⦄
               ⦃ Pi0' : Π-⟨ 𝓤 1 , 𝓔𝓵 1 ⟩ 𝐴' 𝐹' ⦄ {a a' : 𝕍}
               (a==a' : a == a' ∈ 𝓔𝓵 1 ⌜ 𝐴 ⌝ᵈ) →
                   [ ⌜ 𝐹 ⌝ᶜ ∙ˡ a==a' ] == [ ⌜ 𝐹' ⌝ᶜ ∙ʳ 𝓔𝓵-resp-⊆ {1} (𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ A==A') {⌜ 𝐴 ⌝ᵈ} {⌜ 𝐴' ⌝ᵈ} a==a' ] ∈ 𝓢𝓮𝓽 1
      F==F'+ {{Pi0}} {{Pi0'}} El1A-a==a' with F==F' {{Pi}} {{Pi'}} | 𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ (Π-dom {{Pi}})
      ... | F==F'-PiPi' | El+1Pi→El0Pi with 𝓔𝓵ₖ₊₁-unif {{𝕌 0}} (Π-dom {{Pi0}}) (𝓤ₖ⊆𝓤ₖ₊₁ (Π-dom {{Pi}}))
      ... | El1Pi0→EL1Pi , _  with El+1Pi→El0Pi (El1Pi0→EL1Pi El1A-a==a')
      ... | El0Pi-a==a' with F==F'-PiPi' El0Pi-a==a'
      ... | Fa==F'a'∈Set0 with 𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ Fa==F'a'∈Set0
      ... | Fa==F'a'∈Set1 with (Π-cod {{Pi}}) ∙ˡ El0Pi-a==a'
                             | (Π-cod {{Pi'}}) ∙ʳ (𝓔𝓵₀-resp-⊆ A==A' El0Pi-a==a')
                             | (Π-cod {{Pi0}}) ∙ˡ El1A-a==a'
                             | (Π-cod {{Pi0'}}) ∙ʳ (𝓔𝓵ₖ₊₁-resp-⊆ {{𝕌 0}} A==A'+ {Π-dom {{Pi0}}} {Π-dom {{Pi0'}}} El1A-a==a')
      ... | record { ⁈-eval = F·a⇓x }
          | record { ⁈-eval = F'·a'⇓y }
          | record { ⁈-eval = F·a⇓x' }
          | record { ⁈-eval = F'·a'⇓y' }
            rewrite det-· F·a⇓x' F·a⇓x | det-· F'·a'⇓y' F'·a'⇓y
            = Fa==F'a'∈Set1

𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ {suc 𝓀}       (𝓢𝓮𝓽ₖ₊₁-NE lt NE==NE') rewrite (𝕌𝓀↓𝓀≡ 𝓀) =
  𝓢𝓮𝓽ₖ₊₁-NE (≤′-step lt) NE==NE'
𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ {suc 𝓀}        𝓢𝓮𝓽ₖ₊₁-𝑁 = 𝓢𝓮𝓽ₖ₊₁-𝑁
𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ {suc 𝓀}        𝓢𝓮𝓽ₖ₊₁-⊤ = 𝓢𝓮𝓽ₖ₊₁-⊤
𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ {suc 𝓀}        𝓢𝓮𝓽ₖ₊₁-⊥ = 𝓢𝓮𝓽ₖ₊₁-⊥
𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ {suc zero}    (𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ S==S' T==T') =
  𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ (𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ S==S') (𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ T==T')
𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ {suc (suc 𝓀)} (𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ S==S' T==T') =
  𝓢𝓮𝓽ₖ₊₁-⟪Type⋯⟫ (𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ S==S') (𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ T==T')
𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ {suc 𝓀}       (𝓢𝓮𝓽ₖ₊₁-𝑆𝑒𝑡< lt) rewrite (𝕌𝓀↓𝓀≡ 𝓀) =
  𝓢𝓮𝓽ₖ₊₁-𝑆𝑒𝑡< (≤′-step lt)
𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ {suc 𝓀}       (𝓢𝓮𝓽ₖ₊₁-Π {𝐴} {𝐹} {𝐴'} {𝐹'} A==A' {Pi} {Pi'} F==F') =
  𝓢𝓮𝓽ₖ₊₁-Π {{_}} {𝐴} {𝐹} {𝐴'} {𝐹'} A==A'+ {Pi+} {Pi'+} F==F'+
    where
      A==A'+ : 𝐴 == 𝐴' ∈ 𝓢𝓮𝓽 (suc (suc 𝓀))
      A==A'+ = 𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ A==A'

      Pi+ : Π-⟨ 𝓤 (suc (suc 𝓀)) , 𝓔𝓵 (suc (suc 𝓀)) ⟩ 𝐴 𝐹
      -- we can just reuse the 𝓤ₖ⊆𝓤ₖ₊₁ result here
      Pi+ with 𝓤ₖ⊆𝓤ₖ₊₁ {suc 𝓀} (𝓤ₖ₊₁-Π 𝐴 𝐹 {{Pi}})
      ... | 𝓤ₖ₊₁-Π _ _ {{Pi'}} = Pi'

      Pi'+ : Π-⟨ 𝓤 (suc (suc 𝓀)) , 𝓔𝓵 (suc (suc 𝓀)) ⟩ 𝐴' 𝐹'
      Pi'+ with 𝓤ₖ⊆𝓤ₖ₊₁ {suc 𝓀} (𝓤ₖ₊₁-Π 𝐴' 𝐹' {{Pi'}})
      ... | 𝓤ₖ₊₁-Π _ _ {{Pi''}} = Pi''

      F==F'+ : ⦃ Pi0 : Π-⟨ 𝓤 (suc (suc 𝓀)) , 𝓔𝓵 (suc (suc 𝓀)) ⟩ 𝐴 𝐹 ⦄
               ⦃ Pi0' : Π-⟨ 𝓤 (suc (suc 𝓀)) , 𝓔𝓵 (suc (suc 𝓀)) ⟩ 𝐴' 𝐹' ⦄ {a a' : 𝕍}
               (a==a' : a == a' ∈ 𝓔𝓵 (suc (suc 𝓀)) ⌜ 𝐴 ⌝ᵈ) →
                   [ ⌜ 𝐹 ⌝ᶜ ∙ˡ a==a' ] == [ ⌜ 𝐹' ⌝ᶜ ∙ʳ 𝓔𝓵-resp-⊆ {(suc (suc 𝓀))} (𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ A==A') {⌜ 𝐴 ⌝ᵈ} {⌜ 𝐴' ⌝ᵈ} a==a' ] ∈ 𝓢𝓮𝓽 (suc (suc 𝓀))
      F==F'+ {{Pi0}} {{Pi0'}} El1A-a==a' with F==F' {{Pi}} {{Pi'}} | 𝓔𝓵ₖ⊇𝓔𝓵ₖ₊₁ {suc 𝓀} (Π-dom {{Pi}})
      ... | F==F'-PiPi' | El+1Pi→El0Pi with 𝓔𝓵ₖ₊₁-unif {{𝕌 (suc 𝓀)}} (Π-dom {{Pi0}}) (𝓤ₖ⊆𝓤ₖ₊₁ (Π-dom {{Pi}}))
      ... | El1Pi0→EL1Pi , _  with El+1Pi→El0Pi (El1Pi0→EL1Pi El1A-a==a')
      ... | El0Pi-a==a' with F==F'-PiPi' El0Pi-a==a'
      ... | Fa==F'a'∈Set0 with 𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ {suc 𝓀} Fa==F'a'∈Set0
      ... | Fa==F'a'∈Set1 with (Π-cod {{Pi}}) ∙ˡ El0Pi-a==a'
                             | (Π-cod {{Pi'}}) ∙ʳ (𝓔𝓵ₖ₊₁-resp-⊆ {{𝕌 𝓀}} A==A' {Π-dom {{Pi}}} {Π-dom {{Pi'}}} El0Pi-a==a')
                             | (Π-cod {{Pi0}}) ∙ˡ El1A-a==a'
                             | (Π-cod {{Pi0'}}) ∙ʳ (𝓔𝓵ₖ₊₁-resp-⊆ {{𝕌 (suc 𝓀)}} A==A'+ {Π-dom {{Pi0}}} {Π-dom {{Pi0'}}} El1A-a==a')
      ... | record { ⁈-eval = F·a⇓x }
          | record { ⁈-eval = F'·a'⇓y }
          | record { ⁈-eval = F·a⇓x' }
          | record { ⁈-eval = F'·a'⇓y' }
            rewrite det-· F·a⇓x' F·a⇓x | det-· F'·a'⇓y' F'·a'⇓y
            = Fa==F'a'∈Set1
```
## Upcast Lemma for 𝓢𝓮𝓽

Finally, we generalize to arbitrary higher levels:

```agda
𝓢𝓮𝓽↑ : ∀{𝓁 𝓀} → 𝓁 ≤′ 𝓀 → ∀{𝐴 𝐵} → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽 𝓁 → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽 𝓀
𝓢𝓮𝓽↑ ≤′-refl = λ p → p
𝓢𝓮𝓽↑ (≤′-step 𝓁≤𝓀) = 𝓢𝓮𝓽ₖ⊆𝓢𝓮𝓽ₖ₊₁ ∘ (𝓢𝓮𝓽↑ 𝓁≤𝓀)

-- 𝓢𝓮𝓽→𝓤 : ∀{𝓀 𝐴 𝐵} → 𝐴 == 𝐵 ∈ 𝓢𝓮𝓽 𝓀 → 𝓤 𝓀 𝐴
-- 𝓢𝓮𝓽→𝓤 = {!!}
```
# The Limit Universe

The level-indexed family of cumulative universes permits the definition of a limit, which
hides the explicit universe levels and exhibits comp# Cumulative PER Universe Hierarchy

```agda
𝓤ω   : 𝕍 → Set
𝓔𝓵ω  : 𝓤ω ⟹ Rel
𝓢𝓮𝓽ω : Rel

𝓤ω 𝐴          = Σ[ 𝓀 ∈ ℒ ](𝓤 𝓀 𝐴)
𝓔𝓵ω (𝓀 , UₖA) = 𝓔𝓵 𝓀 UₖA
𝓢𝓮𝓽ω 𝐴 𝐴'     = Σ[ 𝓀 ∈ ℒ ](𝐴 == 𝐴' ∈ 𝓢𝓮𝓽 𝓀)

Per-𝓔𝓵ω : ∀{𝐴} → (UA : 𝓤ω 𝐴) → Per (𝓔𝓵ω UA)
Per.per-sym   (Per-𝓔𝓵ω (𝓀 , UA)) = per-sym {{Per-𝓔𝓵 UA}}
Per.per-trans (Per-𝓔𝓵ω (𝓀 , UA)) = per-trans {{Per-𝓔𝓵 UA}}

𝓢𝓮𝓽ω-sym : Sym 𝓢𝓮𝓽ω
𝓢𝓮𝓽ω-sym (zero , A==B)  = zero , (per-sym A==B)
𝓢𝓮𝓽ω-sym (suc 𝓀 , A==B) = suc 𝓀 , per-sym {{Per-𝓢𝓮𝓽ₖ₊₁ {{𝕌 𝓀}}}} A==B

𝓢𝓮𝓽ω-trans : Trans 𝓢𝓮𝓽ω
𝓢𝓮𝓽ω-trans (𝓀 , A==B) (𝓀' , B==C) = 𝓀 ⊔ 𝓀' , per-trans (𝓢𝓮𝓽↑ (proj₁ (m,n≤′m⊔n 𝓀 𝓀')) A==B) (𝓢𝓮𝓽↑ (proj₂ (m,n≤′m⊔n 𝓀 𝓀')) B==C)

instance Per-𝓢𝓮𝓽ω : Per 𝓢𝓮𝓽ω
per-sym   {{Per-𝓢𝓮𝓽ω}} = 𝓢𝓮𝓽ω-sym
per-trans {{Per-𝓢𝓮𝓽ω}} = 𝓢𝓮𝓽ω-trans

𝓔𝓵ω-resp-⊆ : Respect⊆ {𝓤ω} 𝓔𝓵ω 𝓢𝓮𝓽ω
𝓔𝓵ω-resp-⊆ (𝓀 , A==B) {𝓁 , UA} {𝓂 , UB} with k,m,n≤′k⊔m⊔n 𝓀 𝓁 𝓂
... | 𝓀≤′𝓊 , 𝓁≤′𝓊 , 𝓂≤′𝓊 with 𝓀 ⊔ 𝓁 ⊔ 𝓂
... | 𝓊 with 𝓢𝓮𝓽↑ 𝓀≤′𝓊 A==B | 𝓔𝓵↑ 𝓁≤′𝓊 UA | 𝓔𝓵↑ 𝓂≤′𝓊 UB
... | A==B∈Set𝓊 | EL𝓁UA→EL𝓊↑UA , _ | _ , EL𝓊↑UB→EL𝓂UB with 𝓔𝓵-resp-⊆ A==B∈Set𝓊
... | EL𝓊-resp
      = EL𝓊↑UB→EL𝓂UB ∘ EL𝓊-resp ∘ EL𝓁UA→EL𝓊↑UA

𝓔𝓵ω-resp-⊇ : Respect⊇ {𝓤ω} 𝓔𝓵ω 𝓢𝓮𝓽ω
𝓔𝓵ω-resp-⊇ (𝓀 , A==B) {𝓁 , UA} {𝓂 , UB} with k,m,n≤′k⊔m⊔n 𝓀 𝓁 𝓂
... | 𝓀≤′𝓊 , 𝓁≤′𝓊 , 𝓂≤′𝓊 with 𝓀 ⊔ 𝓁 ⊔ 𝓂
... | 𝓊 with 𝓢𝓮𝓽↑ 𝓀≤′𝓊 A==B | 𝓔𝓵↑ 𝓁≤′𝓊 UA | 𝓔𝓵↑ 𝓂≤′𝓊 UB
... | A==B∈Set𝓊 | _ , EL𝓊↑UA→EL𝓁UA | EL𝓂UB→EL𝓊↑UB , _ with 𝓔𝓵-resp-⊇ A==B∈Set𝓊
... | EL𝓊-resp
      = EL𝓊↑UA→EL𝓁UA ∘ EL𝓊-resp ∘ EL𝓂UB→EL𝓊↑UB

𝓔𝓵ω-unif : ∀{𝐴} → (prf prf' : 𝓤ω 𝐴) → 𝓔𝓵ω prf ≡ᴿ 𝓔𝓵ω prf'
𝓔𝓵ω-unif (𝓀 , UkA) (𝓁 , UlA) with m,n≤′m⊔n 𝓀 𝓁
... | 𝓀≤𝓊 , 𝓁≤𝓊 with 𝓀 ⊔ 𝓁
... | 𝓊 with 𝓔𝓵↑ 𝓀≤𝓊 UkA | 𝓔𝓵↑ 𝓁≤𝓊 UlA | 𝓔𝓵-unif (𝓤↑ 𝓀≤𝓊 UkA) (𝓤↑ 𝓁≤𝓊 UlA)
... | a , b | u , v | El𝓊-unifˡ , El𝓊-unifʳ
      = v ∘ El𝓊-unifˡ ∘ a , b ∘ El𝓊-unifʳ ∘ u
```
Some facts that will come in handy for the logical relations proofs.
```agda
𝓤-𝑆𝑒𝑡 : ∀ 𝓀 → 𝓤 (suc 𝓀) (ᶜ (V𝑆𝑒𝑡 𝓀))
𝓤-𝑆𝑒𝑡 𝓀 with 𝓤ₖ₊₁-𝑆𝑒𝑡< {{𝕌 𝓀}} {𝓀}
... | f rewrite (𝕌𝓀↓𝓀≡ 𝓀) = f ≤′-refl

𝓤ω-𝑆𝑒𝑡 : ∀ 𝓀 → 𝓤ω (ᶜ (V𝑆𝑒𝑡 𝓀))
𝓤ω-𝑆𝑒𝑡 𝓀 = (suc 𝓀) , (𝓤-𝑆𝑒𝑡 𝓀)

𝓤𝓀-Set𝓁 : ∀{𝓀 𝓁} → 𝓤 𝓀 (ᶜ (V𝑆𝑒𝑡 𝓁)) → 𝓁 <′ 𝓀
𝓤𝓀-Set𝓁 {suc 𝓀} {𝓁} (𝓤ₖ₊₁-𝑆𝑒𝑡< 𝓁≤𝓀+1) rewrite 𝕌𝓀↓𝓀≡ 𝓀 = 𝓁≤𝓀+1

𝓔𝓵𝓀+1-𝓢𝓮𝓽𝓀 : ∀{𝓀} → ∀(US : 𝓤 (suc 𝓀) (ᶜ (V𝑆𝑒𝑡 𝓀))) → 𝓔𝓵 (suc 𝓀) US ≡ᴿ 𝓢𝓮𝓽 𝓀
𝓔𝓵𝓀+1-𝓢𝓮𝓽𝓀 {zero} (𝓤ₖ₊₁-𝑆𝑒𝑡< ≤′-refl) = ≡ᴿ-refl
𝓔𝓵𝓀+1-𝓢𝓮𝓽𝓀 {suc 𝓀} (𝓤ₖ₊₁-𝑆𝑒𝑡< ≤′-refl) = ≡ᴿ-refl
𝓔𝓵𝓀+1-𝓢𝓮𝓽𝓀 {suc 𝓀} (𝓤ₖ₊₁-𝑆𝑒𝑡< (≤′-step 𝓀+2≤𝓀+1)) = ⊥-elim (<′-irrefl 𝓀+2≤𝓀+1)

𝓔𝓵ω-𝓢𝓮𝓽 : ∀ {𝓁} → ∀(US : 𝓤ω (ᶜ (V𝑆𝑒𝑡 𝓁))) → 𝓔𝓵ω US ≡ᴿ 𝓢𝓮𝓽 𝓁
𝓔𝓵ω-𝓢𝓮𝓽 {𝓁} ( 𝓀 , U𝓀Set𝓁 ) with 𝓤𝓀-Set𝓁 U𝓀Set𝓁 | 𝓔𝓵𝓀+1-𝓢𝓮𝓽𝓀 (𝓤-𝑆𝑒𝑡 𝓁)
... | 𝓁+1≤𝓀 | EL𝓁+1≡Set𝓁 with 𝓔𝓵↑ 𝓁+1≤𝓀 (𝓤-𝑆𝑒𝑡 𝓁) | 𝓔𝓵-unif (𝓤↑ 𝓁+1≤𝓀 (𝓤-𝑆𝑒𝑡 𝓁)) U𝓀Set𝓁
... | El𝓁USet𝓁≡El𝓀↑USet𝓁 | El𝓀↑USet𝓁≡El𝓀U𝓀Set𝓁
--TODO would be nice to have reasoning combinators analogous to the ones for ≡
      = ≡ᴿ-sym (≡ᴿ-trans (≡ᴿ-trans (≡ᴿ-sym EL𝓁+1≡Set𝓁) El𝓁USet𝓁≡El𝓀↑USet𝓁) El𝓀↑USet𝓁≡El𝓀U𝓀Set𝓁)
```
