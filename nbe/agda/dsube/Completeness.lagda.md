# Completeness of Normalization by Evaluation for Dᵉ<:>

We prove completeness with a partial equivalence (PER) model.
Completeness means that whatever terms are βη-equal in the Dᵉ<:> system,
so will be their normal forms in the PER model of equality (and their NFs exist!)

It is sufficient to use this result to conclude termination of NbE,
for the special case of relating a well-typed expression to itself.


```agda
module dsube.Completeness where

open import Data.Bool using (true; false)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open Σ
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _≤′_; _<′_)
open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to _⊔ˡ_)
open import dsube.Syntax
open import dsube.NbE
open import dsube.Relations
open import dsube.RelFun
open import dsube.PER
open import dsube.Universes
-- TODO should the below things be automatically exported?
open Per {{...}}
open Π-⟨_,_⟩ {{...}}
open [_∙_]∈_
open [_==_∙_==_]∈_
open Rel-family {{...}}
open _≤′_
```
# Type Interpretation

For clarity, we alias the cumulative universe of PERs on our domain:
```agda
𝓣𝔂𝓹𝓮 = 𝓢𝓮𝓽ω
```
Then, we define the partial type interpretation function (again using Bove's graph encoding), which
is the composition of evaluation ⟦_⟧ and interpretation 𝓔𝓵ω into 𝓣𝔂𝓹𝓮:
```agda
data ⟦_⟧ᵗʸ_⇓_ : Exp → Env → Rel → Set where
  ty-interp : ∀ {T ρ 𝑇} →
      ⟦ T ⟧ ρ ⇓ 𝑇 →
      (UT : 𝓤ω 𝑇) →
      -----------------
      ⟦ T ⟧ᵗʸ ρ ⇓ (𝓔𝓵ω UT)
```
The graph encoding is a function:
```agda
det-⟦-⟧ᵗʸ : ∀{T ρ R R'} → ⟦ T ⟧ᵗʸ ρ ⇓ R → ⟦ T ⟧ᵗʸ ρ ⇓ R' → R ≡ᴿ R'
det-⟦-⟧ᵗʸ (ty-interp x UT) (ty-interp x₁ UT₁) rewrite det-⟦-⟧ x x₁ = 𝓔𝓵ω-unif UT UT₁
```
# Logical Relation(s)

For each syntaxtic judgment form, we define its semantic counterpart.

```agda
-- what follows are some aux. record types, to avoid working with bare products and existentials in proofs

-- ⟦ T ⇓ ρ == T ⇓ ρ' ⟧ᵗʸ ↔ ∃[ 𝑇 ] ∃[ 𝑇' ](𝑇 == 𝑇' ∈ 𝓣𝔂𝓹𝓮 × ⟦ T ⟧ ρ ⇓ 𝑇 × ⟦ T ⟧ ρ' ⇓ 𝑇'))
record ⟦_⇓_==_⇓_⟧ᵗʸ (T : Exp) (ρ : Env) (T' : Exp) (ρ' : Env)  : Set where
  eta-equality
  constructor ⟦ty_⟧
  field
    {{ty-l}}  : 𝕍
    {{ty-r}}  : 𝕍
    {{ty-l-eval}} : ⟦ T  ⟧ ρ  ⇓ ty-l
    {{ty-r-eval}} : ⟦ T' ⟧ ρ' ⇓ ty-r
    ty-rel    : 𝓣𝔂𝓹𝓮 ty-l ty-r
open ⟦_⇓_==_⇓_⟧ᵗʸ

-- ⟦ e ⇓ ρ == e' ⇓ ρ' ∈ T ⟧ᵉˣᵖ ↔ ∃[ 𝑒 ] ∃[ 𝑒' ] ∃[ R ](𝑒 == 𝑒' ∈ R × ⟦ e ⟧ ρ ⇓ 𝑒 × ⟦ e' ⟧ ρ' ⇓ 𝑒' × ⟦ T ⟧ᵗʸ ρ ⇓ R)
record ⟦_⇓_==_⇓_∈_⟧ᵉˣᵖ (e : Exp) (ρ : Env) (e' : Exp) (ρ' : Env) (T : Exp) : Set₁ where
  eta-equality
  constructor ⟦exp_,_⟧
  field
    {{exp-l}}  : 𝕍
    {{exp-r}}  : 𝕍
    {exp-R}  : Rel
    {{exp-l-eval}} : ⟦ e  ⟧ ρ  ⇓ exp-l
    {{exp-r-eval}} : ⟦ e' ⟧ ρ' ⇓ exp-r
    exp-R-eval : ⟦ T  ⟧ᵗʸ ρ ⇓ exp-R
    exp-rel    : exp-l == exp-r ∈ exp-R
open ⟦_⇓_==_⇓_∈_⟧ᵉˣᵖ


-- valid contexts and induced environment relation
data ⟦_⟧ᶜᵗˣ : Ctx → Env → Env → Set₁ where -- TODO eventually, make the a == b ∈ R notation work for this kind of binary relation
  ⟦-⟧ᶜᵗˣ-∅ :
    ----------
    ⟦ ∅ ⟧ᶜᵗˣ ε ε

  ⟦-⟧ᶜᵗˣ-, : ∀{Γ T ρ ρ' 𝑎 𝑎' R} →
    ⟦ Γ ⟧ᶜᵗˣ ρ ρ' →
    ⟦ T ⟧ᵗʸ ρ ⇓ R →
    R 𝑎 𝑎' →
    ------------------------------
    ⟦ Γ , T ⟧ᶜᵗˣ (ρ ,, 𝑎) (ρ' ,, 𝑎')

-- ⟦ σ == σ' ∈ Δ ⟧ˢᵘᵇ ↔ ∃[ δ ] ∃[ δ' ] (⟦ Δ ⟧ᶜᵗˣ δ δ' × ⟦ σ ⟧ˢ ρ ⇓ δ × ⟦ σ' ⟧ˢ ρ' ⇓ δ'))
record ⟦_⇓_==_⇓_∈_⟧ˢᵘᵇ (σ : Subst) (ρ : Env) (σ' : Subst) (ρ' : Env) (Δ : Ctx) : Set₁ where
  eta-equality
  constructor ⟦sub_⟧
  field
    {sub-l}  : Env
    {sub-r}  : Env
    {{sub-l-eval}} : ⟦ σ ⟧ˢ ρ ⇓ sub-l
    {{sub-r-eval}} : ⟦ σ' ⟧ˢ ρ' ⇓ sub-r
    sub-rel    : ⟦ Δ ⟧ᶜᵗˣ sub-l sub-r
open ⟦_⇓_==_⇓_∈_⟧ˢᵘᵇ


-- valid contexts
data ⊨ᶜᵗˣ : Ctx → Set₁ where
  ⊨-∅ :
    ---
    ⊨ᶜᵗˣ ∅

  ⊨-, : ∀{Γ T} →
    {{⊨ᶜᵗˣ Γ}} →
    (∀{ρ ρ'} → ⟦ Γ ⟧ᶜᵗˣ ρ ρ' → ⟦ T ⇓ ρ == T ⇓ ρ' ⟧ᵗʸ) →
    ------------------------------------------------------------------
    ⊨ᶜᵗˣ (Γ , T)

-- Valid types, we deviate from the thesis by inlining and simplifying the definition, which is Γ ⊨ᵉˣᵖ T ∶ Set k for some k.
-- Otherwise, we arrive at a non-wellfounded group of definitions which Agda rightfully rejects.
-- It (perhaps unsurprisingly) turns out this is just the extension ⊨-, case for valid contexts  ⊨ᶜᵗˣ above.

-- Γ ⊨ᵗʸ T = ⊨ᶜᵗˣ Γ × (∀{ρ ρ'} → ⟦ Γ ⟧ᶜᵗˣ ρ ρ' → ⟦ T ⇓ ρ == T ⇓ ρ' ⟧ᵗʸ)
data _⊨ᵗʸ_ : Ctx → Exp → Set₁ where
  ⊨ty : ∀ {Γ T} →
    {{⊨ᶜᵗˣ Γ}} →
    (∀{ρ ρ'} → ⟦ Γ ⟧ᶜᵗˣ ρ ρ' → ⟦ T ⇓ ρ == T ⇓ ρ' ⟧ᵗʸ) →
    ------------------------------------------------
    Γ ⊨ᵗʸ T

-- equality
-- Γ ⊨ e ≈ e' ∶ T = Γ ⊨ᵗʸ T × (∀{ρ ρ'} → ⟦ Γ ⟧ᶜᵗˣ ρ ρ' → ⟦ e ⇓ ρ == e' ⇓ ρ' ∈ T ⟧ᵉˣᵖ)
data _⊨_≈_∶_ : Ctx → Exp → Exp → Exp → Set₁ where
 ⊨≈ : ∀{Γ e e' T} →
    Γ ⊨ᵗʸ T →
    (∀{ρ ρ'} → ⟦ Γ ⟧ᶜᵗˣ ρ ρ' → ⟦ e ⇓ ρ == e' ⇓ ρ' ∈ T ⟧ᵉˣᵖ) →
    -------------------------------------------------------
    Γ ⊨ e ≈ e' ∶ T

-- valid expressions
_⊨ᵉˣᵖ_∶_ : Ctx → Exp → Exp → Set₁
Γ ⊨ᵉˣᵖ e ∶ T = Γ ⊨ e ≈ e ∶ T

-- substitution equality
-- Γ ⊨ˢᵘᵇ≈ σ ≈ σ' ∶ Δ = ⊨ᶜᵗˣ Γ × ⊨ᶜᵗˣ Δ × (∀{ρ ρ'} → ⟦ Γ ⟧ᶜᵗˣ ρ ρ' → ⟦ σ ⇓ ρ == σ' ⇓ ρ' ∈ Δ ⟧ˢᵘᵇ)
data _⊨ˢᵘᵇ≈_≈_∶_ : Ctx → Subst → Subst → Ctx → Set₁ where
  ⊨sub≈ : ∀ {Γ σ σ' Δ} →
    {{⊨ᶜᵗˣ Γ}} →
    {{⊨ᶜᵗˣ Δ}} →
    (∀{ρ ρ'} → ⟦ Γ ⟧ᶜᵗˣ ρ ρ' → ⟦ σ ⇓ ρ == σ' ⇓ ρ' ∈ Δ ⟧ˢᵘᵇ) →
    ------------------------------------------------------
    Γ ⊨ˢᵘᵇ≈ σ ≈ σ' ∶ Δ

-- valid substitutions
_⊨ˢᵘᵇ_∶_  : Ctx → Subst → Ctx → Set₁
Γ ⊨ˢᵘᵇ σ ∶ Δ = Γ ⊨ˢᵘᵇ≈ σ ≈ σ ∶ Δ

-- TODO subtyping
_⊨_<∶_ :  Ctx → Exp → Exp → Set₁
Γ ⊨ T <∶ T' = {!!}

infix 3 _⊨ᵗʸ_
infix 4 _⊨ᵉˣᵖ_∶_
infix 5 _⊨_≈_∶_
infix 4 _⊨ˢᵘᵇ_∶_
infix 5 _⊨ˢᵘᵇ≈_≈_∶_
infix 4 _⊨_<∶_
```
# Fundamental Theorem(s)

TODO: put into separate module
```agda
⊢→⊨ᶜᵗˣ    : ∀ {Γ}        → ⊢ᶜᵗˣ Γ            → ⊨ᶜᵗˣ Γ
⊢→⊨ᵗʸ     : ∀ {Γ T}      → Γ ⊢ T             → Γ ⊨ᵗʸ T
⊢→⊨ᵉˣᵖ    : ∀ {Γ e T}    → Γ ⊢ e ∶ T         → Γ ⊨ᵉˣᵖ e ∶ T
⊢→⊨ˢᵘᵇ    : ∀ {Γ σ Δ}    → Γ ⊢ˢᵘᵇ σ ∶ Δ      → Γ ⊨ˢᵘᵇ σ ∶ Δ
⊢→⊨<∶     : ∀ {Γ S T}    → Γ ⊢ S <∶ T        → Γ ⊨ S <∶ T
⊢→⊨≈      : ∀ {Γ e e' T} → Γ ⊢ e ≈ e' ∶ T    → Γ ⊨ e ≈ e' ∶ T
⊢→⊨ˢᵘᵇ≈   : ∀ {Γ σ σ' Δ} → Γ ⊢ˢᵘᵇ σ ≈ σ' ∶ Δ → Γ ⊨ˢᵘᵇ≈ σ ≈ σ' ∶ Δ

⊢→⊨ᶜᵗˣ wf∅ = ⊨-∅
⊢→⊨ᶜᵗˣ (wf-,- wfΓ Γ⊢T) with (⊢→⊨ᵗʸ  Γ⊢T)
... | ⊨ty ⊨T = ⊨-, ⊨T

⊢→⊨ᵗʸ {Γ} {T} (wf-ty {_} {𝓁} Γ⊢T∶Set𝓁) with (⊢→⊨ᵉˣᵖ Γ⊢T∶Set𝓁)
... | ⊨≈ (⊨ty _) Γ⊨T∶Set𝓁 = ⊨ty Γ⊨T
       where
         Γ⊨T : ∀ {ρ ρ'} → ⟦ Γ ⟧ᶜᵗˣ ρ ρ' → ⟦ T ⇓ ρ == T ⇓ ρ' ⟧ᵗʸ
         Γ⊨T ρ==ρ' with Γ⊨T∶Set𝓁 ρ==ρ'
         ... | ⟦exp ty-interp eval-c UωSet𝓁 , 𝑇==𝑇'∈ELωSet𝓁 ⟧
               = ⟦ty ⟨ 𝓁 , (proj₁ (𝓔𝓵ω-𝓢𝓮𝓽 UωSet𝓁)) 𝑇==𝑇'∈ELωSet𝓁  ⟩ ⟧
```
## Expression and Substitutions Interpretation

A simple solution would be delegating directly to the equalities, via the syntactic
reflexivity rules, like so:

    ⊢→⊨ᵉˣᵖ Γ⊢e∶T = ⊢→⊨≈ (≈refl Γ⊢e∶T)

    ⊢→⊨ˢᵘᵇ Γ⊢σ∶Δ = ⊢→⊨ˢᵘᵇ≈ (sub≈refl Γ⊢σ∶Δ)

but that will cause the termination checker to complain, once we proceed
proving `⊢→⊨≈`, respectively `⊢→⊨ˢᵘᵇ≈`, since derivations of `Γ ⊢ e ≈ e' ∶ T`
may contain expression/substitution typing derivations  `Γ ⊢ e' ∶ T'`. We
try the naive solution first, which is proving these by induction on the
respective derivations. Alternative, we could try a proper induction measure
to keep the simple solution above.
```agda
⊢→⊨ᵉˣᵖ (TCst {Γ} {c} {T} ⊢Γ c⊢T) with ⊢→⊨ᶜᵗˣ ⊢Γ
... | ⊨Γ with c
... | 𝑁     = {!!}
... | 𝑧     = {!!}
... | 𝑠     = {!!}
... | 𝑆𝑒𝑡 𝓁 = {!!}
... | ⊤'    = {!!}
... | ⊥'    = {!!}
⊢→⊨ᵉˣᵖ (TVar x x₁) = {!!}
⊢→⊨ᵉˣᵖ (T·ₛ x Γ⊢e∶T) = {!!}
⊢→⊨ᵉˣᵖ (TΠ Γ⊢e∶T Γ⊢e∶T₁) = {!!}
⊢→⊨ᵉˣᵖ (Tƛ x Γ⊢e∶T) = {!!}
⊢→⊨ᵉˣᵖ (T· Γ⊢e∶T Γ⊢e∶T₁) = {!!}
⊢→⊨ᵉˣᵖ (T⟨Type⋯⟩ Γ⊢e∶T Γ⊢e∶T₁) = {!!}
⊢→⊨ᵉˣᵖ (TType x) = {!!}
⊢→⊨ᵉˣᵖ (T∙Type Γ⊢e∶T Γ⊢e∶T₁) = {!!}
⊢→⊨ᵉˣᵖ (T<∶ Γ⊢e∶T x) = {!!}

⊢→⊨ˢᵘᵇ (TId ⊢Γ) = {!!}
⊢→⊨ˢᵘᵇ (T↑ Δ⊢T) = {!!}
⊢→⊨ˢᵘᵇ (T∘ˢ Γ⊢τ∶Δ₁ Δ₁⊢σ∶Δ) = {!!}
⊢→⊨ˢᵘᵇ (T,ˢ Γ⊢σ∶Δ Δ⊢T Γ⊢e∶Tσ) = {!!}


⊢→⊨<∶ (<∶Refl x) = {!!}
⊢→⊨<∶ (<∶Lvl x) = {!!}
⊢→⊨<∶ (<∶Trans Γ⊢S<∶T Γ⊢S<∶T₁) = {!!}
⊢→⊨<∶ (<∶⊤ x) = {!!}
⊢→⊨<∶ (<∶⊥ x) = {!!}
⊢→⊨<∶ (<∶Sel₁ x) = {!!}
⊢→⊨<∶ (<∶Sel₂ x) = {!!}
⊢→⊨<∶ (<∶⟨Type⋯⟩ Γ⊢S<∶T Γ⊢S<∶T₁) = {!!}
⊢→⊨<∶ (<∶Π Γ⊢S<∶T Γ⊢S<∶T₁) = {!!}

{-
 Γ ⊨ᵗʸ T × (∀{ρ ρ'} → ⟦ Γ ⟧ᶜᵗˣ ρ ρ' →
           ∃[ 𝑒 ] ∃[ 𝑒' ] ∃[ R ](𝑒 == 𝑒' ∈ R × ⟦ e ⟧ ρ ⇓ 𝑒 × ⟦ e' ⟧ ρ' ⇓ 𝑒' × ⟦ T ⟧ᵗʸ ρ ⇓ R)) -}

postulate --TODO move and prove
  ⊢ᵗʸ→⊢ᶜᵗˣ : ∀ {Γ T} → Γ ⊢ T → ⊢ᶜᵗˣ Γ
  ⊢ᵉˣᵖ→⊢ᵗʸ : ∀ {Γ e T} → Γ ⊢ e ∶ T → Γ ⊢ T
  ⊢ᵉˣᵖ→⊢ᶜᵗˣ : ∀ {Γ e T} → Γ ⊢ e ∶ T → ⊢ᶜᵗˣ Γ

⊢→⊨≈ (≈β· {Γ} {S} {T} {s} {t} Γ,S⊢t∶T Γ⊢s∶S) with ⊢→⊨ᵉˣᵖ Γ,S⊢t∶T | ⊢→⊨ᵉˣᵖ Γ⊢s∶S
... | ⊨≈ (⊨ty ⦃ ⊨-, Γ⊨S ⦄ Γ,S⊨T) Γ,S⊨t∶T
    | ⊨≈ _ Γ⊨s∶S = ⊨≈ (⊨ty Γ⊨T[s]) Γ⊨ƛt·s≈t[s]∶T[s]
        where
          Γ⊨T[s] : ∀ {ρ ρ'} → ⟦ Γ ⟧ᶜᵗˣ ρ ρ' → ⟦ T ·ₛ (Id ,ₛ s) ⇓ ρ == T ·ₛ (Id ,ₛ s) ⇓ ρ' ⟧ᵗʸ
          Γ⊨T[s] ρ==ρ' with Γ⊨s∶S ρ==ρ'
          ... | ⟦exp S⇓𝓢 , 𝑠==𝑠'∈𝓢 ⟧ = {!!}
          -- need to show that [[ Γ , S ]] (ρ ,, 𝑠) (ρ' ,, 𝑠')
          -- apply to Γ,S⊨T
          -- this should yield all evidence for ⟦ T [ s ] ⇓ ρ == T [ s ] ⇓ ρ' ⟧ᵗʸ
          Γ⊨ƛt·s≈t[s]∶T[s] : ∀{ρ ρ'} → ⟦ Γ ⟧ᶜᵗˣ ρ ρ' → ⟦ ƛ t · s ⇓ ρ == t ·ₛ (Id ,ₛ s) ⇓ ρ' ∈ T ·ₛ (Id ,ₛ s) ⟧ᵉˣᵖ
          Γ⊨ƛt·s≈t[s]∶T[s] ρ==ρ' with Γ⊨s∶S ρ==ρ'
          ... | ⟦exp S⇓𝓢 , 𝑠==𝑠'∈𝓢 ⟧  = {!!}
          -- similarly, show that [[ Γ , S ]] (ρ ,, 𝑠) (ρ' ,, 𝑠')
          -- apply to Γ,S⊨t∶T and  Γ,S⊨T
          -- this should yield all evidence for ⟦ ƛ t · s ⇓ ρ == t [ s ] ⇓ ρ' ∈ T [ s ] ⟧ᵉˣᵖ
          -- as both ƛ t · s ⇓ ρ and  t [ s ] ⇓ ρ' stem from t ⇓ (ρ ,, 𝑠) and t ⇓ (ρ' ,, 𝑠'), respectively
          -- and the relation R w. ⟦ T [ s ] ⟧ ρ ⇓ R stems from ⟦ T ⟧ (ρ ,, 𝑠) ⇓ R

--⊨Γ,S , ρ==ρ'→t⇓ρ==t⇓ρ'∈⟦T⟧ ⟩ , ρ==ρ'→T⇓ρ==T⇓ρ' ⟩ = ⟨ {!!} , {!!} ⟩
⊢→⊨≈ (≈β∙Type x) = {!!}
⊢→⊨≈ (≈ξƛ Γ⊢e≈e'∶T) = {!!}
⊢→⊨≈ (≈ηƛ x) = {!!}
⊢→⊨≈ (≈η∙Type x) = {!!}
⊢→⊨≈ (≈♯ x x₁) = {!!}
⊢→⊨≈ (≈ᶜ x) = {!!}
⊢→⊨≈ (≈∶[ℒ≤] x Γ⊢e≈e'∶T) = {!!}
⊢→⊨≈ (≈∶[≈] Γ⊢e≈e'∶T Γ⊢e≈e'∶T₁) = {!!}
⊢→⊨≈ (≈[Π] Γ⊢e≈e'∶T Γ⊢e≈e'∶T₁) = {!!}
⊢→⊨≈ (≈[·] Γ⊢e≈e'∶T Γ⊢e≈e'∶T₁) = {!!}
⊢→⊨≈ (≈[ˢᵘᵇ] x Γ⊢e≈e'∶T) = {!!}
⊢→⊨≈ (≈[⟨Type⋯⟩] Γ⊢e≈e'∶T Γ⊢e≈e'∶T₁) = {!!}
⊢→⊨≈ (≈[Type] Γ⊢e≈e'∶T) = {!!}
⊢→⊨≈ (≈[∙Type] x Γ⊢e≈e'∶T) = {!!}
⊢→⊨≈ (≈ˢᵘᵇ↑ x) = {!!}
⊢→⊨≈ (≈ˢᵘᵇId x) = {!!}
⊢→⊨≈ (≈ˢᵘᵇ,ₛ-0 x) = {!!}
⊢→⊨≈ (≈ˢᵘᵇ,ₛ-suc x x₁) = {!!}
⊢→⊨≈ (≈ˢᵘᵇ∘ₛ x x₁ x₂) = {!!}
⊢→⊨≈ (≈ˢᵘᵇᶜ x x₁) = {!!}
⊢→⊨≈ (≈ˢᵘᵇΠ x x₁ x₂) = {!!}
⊢→⊨≈ (≈ˢᵘᵇƛ x x₁) = {!!}
⊢→⊨≈ (≈ˢᵘᵇ· x x₁ x₂) = {!!}
⊢→⊨≈ (≈ˢᵘᵇ⟨Type⋯⟩ x x₁ x₂) = {!!}
⊢→⊨≈ (≈ˢᵘᵇType x x₁) = {!!}
⊢→⊨≈ (≈ˢᵘᵇ∙Type x x₁ x₂) = {!!}
⊢→⊨≈ (≈refl x) = {!!}
⊢→⊨≈ (≈sym Γ⊢e≈e'∶T) = {!!}
⊢→⊨≈ (≈trans Γ⊢e≈e'∶T Γ⊢e≈e'∶T₁) = {!!}

⊢→⊨ˢᵘᵇ≈ (sub≈refl x) = {!!}
⊢→⊨ˢᵘᵇ≈ (sub≈sym Γ⊢σ≈σ'∶Δ) = {!!}
⊢→⊨ˢᵘᵇ≈ (sub≈trans Γ⊢σ≈σ'∶Δ Γ⊢σ≈σ'∶Δ₁) = {!!}
⊢→⊨ˢᵘᵇ≈ (sub≈↑ x x₁ x₂) = {!!}
⊢→⊨ˢᵘᵇ≈ (sub≈Idₗ x) = {!!}
⊢→⊨ˢᵘᵇ≈ (sub≈Idᵣ x) = {!!}
⊢→⊨ˢᵘᵇ≈ (sub≈∘ₛassoc x x₁ x₂) = {!!}
⊢→⊨ˢᵘᵇ≈ (sub≈η x) = {!!}
⊢→⊨ˢᵘᵇ≈ (sub≈β x x₁ x₂) = {!!}
⊢→⊨ˢᵘᵇ≈ (sub≈[,ₛ] Γ⊢σ≈σ'∶Δ x x₁) = {!!}
⊢→⊨ˢᵘᵇ≈ (sub≈[∘ˢ] Γ⊢σ≈σ'∶Δ Γ⊢σ≈σ'∶Δ₁) = {!!}
```
# Typed Candidate Spaces
```agda
-- TODO probably separate module
```
# Escape Lemma
```agda
-- TODO
```
# Completeness
```agda
-- TODO: this'll require proving the Set -> U lemmas in Universes, which are commented out
⟦-⟧ᶜᵗˣ-refl : ∀ {Γ ρ} → ⊢ᶜᵗˣ Γ → ↑ Γ ⇓ ρ → ⟦ Γ ⟧ᶜᵗˣ ρ ρ
⟦-⟧ᶜᵗˣ-refl = {!!}
-- ⟦-⟧ᶜᵗˣ-refl _ lift-∅ = ⟦-⟧ᶜᵗˣ-∅
-- ⟦-⟧ᶜᵗˣ-refl (wf-,- wfG Γ⊢T) (lift-, liftG x) with ⊢→⊨ᵗʸ Γ⊢T
-- ... | ⟨ fst , rel ⟩ with ⟦-⟧ᶜᵗˣ-refl wfG liftG
-- ... | IH with rel IH
-- ... | ⟨ 𝑇 , ⟨ 𝑇' , ⟨ ⟨ 𝓀 , snd ⟩ , ⟨ fst₄ , snd₁ ⟩ ⟩ ⟩ ⟩ = ⟦-⟧ᶜᵗˣ-, IH {!!} {!!}


completeness : ∀ {Γ e e' T} → Γ ⊢ e ≈ e' ∶ T → ∃[ n ] (nf e ⇓⟨ Γ , T ⟩ n × nf e' ⇓⟨ Γ , T ⟩ n)
completeness = {!!}
```
# Corollary: Strong Normalization (SN)

SN is a special case of completeness:

```agda
strong-normalization : ∀ {Γ e T} → Γ ⊢ e ∶ T → ∃[ n ] (nf e ⇓⟨ Γ , T ⟩ n)
strong-normalization Γ⊢e∶T with completeness (≈refl Γ⊢e∶T)
... | ⟨ n , ⟨ eval , _ ⟩ ⟩ = ⟨ n , eval ⟩
```

# TODOs
* determinize the nbe functions, prove their irrelevance and determinism properties
* subtyping interp cf. Abel'17
* prove the cases of fundamental lemma
* typed candidate spaces
* prove escape lemma
* make the syntax well-scoped?
