open import Lib.Algebra.Reals
open import DPPL.Denotations.Regularity

module DPPL.Denotations.Domain (R : Reals₀) (Ax : RegAssumptions R) where

open import DPPL.Regularity hiding (A)
open import DPPL.Denotations.Site R Ax

open import Lib.Prelude using (swizzle-equiv)
open import Lib.Cat.Concrete
open import Lib.Cat.Functor
open import Lib.Cat.Product
open import Lib.Data.Vector

open import Cat.Prelude
open import Cat.Cartesian
open import Cat.Diagram.Exponential
open import Cat.Diagram.Product.Finite
open import Cat.Diagram.Product.Indexed
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Base
open import Cat.Functor.Coherence
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Hom
open import Cat.Functor.Naturality
open import Cat.Instances.Sets
open import Data.Fin.Base hiding (_≤_)
open import Data.Fin.Properties
open import Data.Power hiding (_∪_ ; _∩_)
open import Order.Base
open import Order.Lattice
import Cat.Reasoning as Cr
import Cat.Functor.Reasoning as Fr

open Reals R using (ℝ ; 0r)
open RegAssumptions Ax

open Reg↓≤ using (_≤_)
open is-lattice Reg↓-lattice hiding (top)

open Functor
open _=>_ renaming (op to opⁿ)
open Cr._≅_
open Cr.Inverses

private
  variable
    m n : Nat
    c c' : Reg↓

π'[_] : Fin m → ℝ ^ m → ℝ ^ 1
π'[ i ] = make ⊙ π[ i ]

π'1 : (f : ℝ ^ m → ℝ ^ 1) → π'[ fzero ] ⊙ f ≡ f
π'1 _ = ext λ _ → Fin-cases refl λ ()

𝔇 : Precategory _ _
𝔇 = ConcPSh lzero ℛ-conc

module 𝔇 = Cr 𝔇

𝔇-cartesian : Cartesian-category 𝔇
𝔇-cartesian = ConcPSh-cartesian ℛ-conc

𝔇-closed : Cartesian-closed 𝔇 𝔇-cartesian
𝔇-closed = ConcPSh-closed ℛ-conc

open Cartesian-category 𝔇-cartesian
open Cartesian-closed 𝔇-closed renaming ([_,_] to _⇒_)

module 𝔇-ip {n} (F : 𝔇.Ob ^ n) =
  Indexed-product (Cartesian→standard-finite-products terminal products F)
open ProdIso 𝔇-cartesian

□⟨_⟩ : Reg↓ → Functor 𝔇 𝔇
□⟨ c ⟩ = conc-dir-image ℛ-conc ℛ-conc μ⟨ c ⟩ μ-pres-top μ-onto-points

𝔇≤ : Reg↓ → Precategory _ _
𝔇≤ c = ConcPSh lzero (ℛ≤-conc c)

ι≤' : ∀ c → Functor 𝔇 (𝔇≤ c)
ι≤' c = conc-dir-image ℛ-conc (ℛ≤-conc c) (ι≤ c)
  (ι≤-pres-top {c}) (λ {U} → ι≤-onto-points {c} {U})

□-counit : □⟨ c ⟩ => Id
□-counit = λ where
  .η X              → nat-idr-op-to (X .fst ▸ opⁿ μ-unit)
  .is-natural _ _ f → Nat-path λ _ → sym $ f .is-natural _ _ _

□-comult : □⟨ c ⟩ F∘ □⟨ c' ⟩ ≅ⁿ □⟨ c ∩ c' ⟩
□-comult .to = λ where
  .η X              → nat-assoc-from (X .fst ▸ op-compose-from (opⁿ (μ-mult .from)))
  .is-natural _ _ f → Nat-path λ _ → sym $ f .is-natural _ _ _
□-comult .from = λ where
  .η X              → nat-assoc-to (X .fst ▸ op-compose-into (opⁿ (μ-mult .to)))
  .is-natural _ _ f → Nat-path λ _ → sym $ f .is-natural _ _ _
□-comult .inverses = λ where
  .invl → ext λ F _ _ → Fr.annihilate (F .fst) (μ-mult .inverses .invl ηₚ _) $ₚ _
  .invr → ext λ F _ _ → Fr.annihilate (F .fst) (μ-mult .inverses .invr ηₚ _) $ₚ _

□-≤ : c ≤ c' → □⟨ c ⟩ => □⟨ c' ⟩
□-≤ {c} {c'} H≤ = λ where
  .η X              → X .fst ▸ opⁿ (μ-≤ H≤)
  .is-natural _ _ f → Nat-path λ _ → sym $ f .is-natural _ _ _

□⟨A⟩-Id : □⟨ A↓ ⟩ ≅ⁿ Id
□⟨A⟩-Id .to = λ where
  .η X              → nat-idr-op-to (X .fst ▸ opⁿ (μ⟨A⟩-Id .from))
  .is-natural _ _ f → Nat-path λ _ → sym $ f .is-natural _ _ _
□⟨A⟩-Id .from = λ where
  .η X              → nat-idr-op-from (X .fst ▸ opⁿ (μ⟨A⟩-Id .to))
  .is-natural _ _ f → Nat-path λ _ → sym $ f .is-natural _ _ _
□⟨A⟩-Id .inverses = λ where
  .invl → ext λ F _ _ → Fr.annihilate (F .fst) (μ⟨A⟩-Id .inverses .invl ηₚ _) $ₚ _
  .invr → ext λ F _ _ → Fr.annihilate (F .fst) (μ⟨A⟩-Id .inverses .invr ηₚ _) $ₚ _

□-pres-lt : ι≤' c F∘ □⟨ c ⟩ ≅ⁿ ι≤' c
□-pres-lt {c} .to = λ where
  .η X → nat-assoc-from (X .fst ▸ op-compose-from (opⁿ (μ-pres-lt {c} .from)))
  .is-natural _ _ f → Nat-path λ _ → sym $ f .is-natural _ _ _
□-pres-lt {c} .from = λ where
  .η X → nat-assoc-to (X .fst ▸ op-compose-into (opⁿ (μ-pres-lt {c} .to)))
  .is-natural _ _ f → Nat-path λ _ → sym $ f .is-natural _ _ _
□-pres-lt .inverses = λ where
  .invl → ext λ F _ _ → Fr.annihilate (F .fst) (μ-pres-lt .inverses .invl ηₚ _) $ₚ _
  .invr → ext λ F _ _ → Fr.annihilate (F .fst) (μ-pres-lt .inverses .invr ηₚ _) $ₚ _

□-pres-top : □⟨ c ⟩ .F₀ top ≅ top
□-pres-top = super-iso→sub-iso _
  $ F-map-iso (よ ℛ) ν-pres-top ∘ni adjunct-hom-iso-into μ⊣ν _

□-pres-prod : ∀ X Y → □⟨ c ⟩ .F₀ (X ⊗₀ Y) ≅ (□⟨ c ⟩ .F₀ X ⊗₀ □⟨ c ⟩ .F₀ Y)
□-pres-prod X Y = super-iso→sub-iso _ (to-natural-iso ni) where
  ni : make-natural-iso _ _
  ni .make-natural-iso.eta _ u       = u
  ni .make-natural-iso.inv _ u       = u
  ni .make-natural-iso.eta∘inv _     = refl
  ni .make-natural-iso.inv∘eta _     = refl
  ni .make-natural-iso.natural _ _ _ = refl


𝔇ℝ[_] : ℛ.Ob → 𝔇.Ob
𝔇ℝ[_] = Conc-よ₀ ℛ-conc

𝔇ℝ'[_] : Reg↓ ^ n → 𝔇.Ob
𝔇ℝ'[ cs ] = 𝔇-ip.ΠF λ i → 𝔇ℝ[ 1 , cs i ]

𝔇ℝ-underlying : ∀ {U} → 𝔇ℝ[ U ] ʻ ⋆ ≃ ℝ ^ U .fst
𝔇ℝ-underlying = ℛ-underlying

𝔇ℝ-sec-equiv : ∀ {U} →
  is-conc-section ℛ-conc 𝔇ℝ[ n , c ] {U} ≃[ →-ap ℛ-underlying 𝔇ℝ-underlying ]
  (_∈ ⟨ U .snd ∣ c ⟩-reg)
𝔇ℝ-sec-equiv = over-left→over (→-ap ℛ-underlying 𝔇ℝ-underlying) λ f →
  ℛ-conc-hom-equiv _ _ refl

𝔇ℝ'-underlying : (cs : Reg↓ ^ n) → 𝔇ℝ'[ cs ] ʻ ⋆ ≃ ℝ ^ n
𝔇ℝ'-underlying cs =
  Π-underlying ℛ-conc (λ i → 𝔇ℝ[ 1 , cs i ]) ∙e
  Π-ap-cod λ _ →
    ℛ-underlying ∙e Fin-suc-Π ∙e Σ-contr-snd (λ _ → Π-dom-empty-is-contr λ ())

⟨_⟩-sec : Reg↓ ^ n → (U : Nat × Reg↓) → (ℝ ^ (U .fst) → ℝ ^ n) → Type _
⟨ cs ⟩-sec U g = ∀ i → π'[ i ] ⊙ g ∈ ⟨ U .snd ∣ cs i ⟩-reg

𝔇ℝ'-sec-equiv
  : ∀ {U} {cs : Reg↓ ^ n}
  → is-conc-section ℛ-conc 𝔇ℝ'[ cs ] {U} ≃[ →-ap 𝔇ℝ-underlying (𝔇ℝ'-underlying cs) ]
    ⟨ cs ⟩-sec U
𝔇ℝ'-sec-equiv {cs = cs} = over-left→over (→-ap 𝔇ℝ-underlying (𝔇ℝ'-underlying cs)) λ f →
  Π-sec-equiv ℛ-conc (λ i → 𝔇ℝ[ 1 , cs i ]) _ _ refl ∙e
  Π-ap-cod λ _ → 𝔇ℝ-sec-equiv _ _ $ ext λ _ → Fin-cases refl λ ()

⟨_∥_⟩-reg : Reg↓ ^ m → Reg↓ ^ n → (ℝ ^ m → ℝ ^ n) → Type _
⟨_∥_⟩-reg cs cs' = is-cpsh-hom' ℛ-conc ⟨ cs ⟩-sec ⟨ cs' ⟩-sec

𝔇ℝ'-hom≃⟨∥⟩-reg
  : {cs : Reg↓ ^ m} {cs' : Reg↓ ^ n}
  → Hom 𝔇ℝ'[ cs ] 𝔇ℝ'[ cs' ] ≃ ∫ₚ ⟨ cs ∥ cs' ⟩-reg
𝔇ℝ'-hom≃⟨∥⟩-reg {cs = cs} {cs'} =
  Hom≃Cpsh-hom ℛ-conc ∙e
  Cpsh-hom≃Cpsh-hom' ℛ-conc ℛ-underlying {𝔇ℝ'[ cs ]} {𝔇ℝ'[ cs' ]}
    (𝔇ℝ'-underlying cs) (𝔇ℝ'-underlying cs')
    𝔇ℝ'-sec-equiv 𝔇ℝ'-sec-equiv

□-underlying : {A : 𝔇.Ob} → (□⟨ c ⟩ .F₀ A) ʻ ⋆ ≃ A ʻ ⋆
□-underlying {c} {A} = iso→equiv $ F-map-iso (A .fst) λ where
  .to             → μ-pres-top .from
  .from           → μ-pres-top .to
  .inverses .invl → μ-pres-top .inverses .invl
  .inverses .invr → μ-pres-top .inverses .invr

□-sec-equiv≤
  : ∀ {U} (A : 𝔇.Ob)
  → U .snd ≤ c
  → is-conc-section ℛ-conc (□⟨ c ⟩ .F₀ A) {U} ≃[ →-ap id≃ (□-underlying {A = A}) ]
    is-conc-section ℛ-conc A {U}
□-sec-equiv≤ {c} {U} A H≤ = prop-over-ext (→-ap id≃ (□-underlying {A = A}))
  (λ {b} → is-conc-section-prop ℛ-conc (□⟨ c ⟩ .F₀ A) b)
  (λ {b} → is-conc-section-prop ℛ-conc A b)
  (λ f (au , Hf) → □-pres-lt {c} .to .η A .η (U , H≤) au ,
    ap (Equiv.to (→-ap id≃ (□-underlying {A = A}))) Hf ∙
    ext λ g Hg → □-pres-lt {c} .to .η A .is-natural (U , H≤) (⋆ , ¡) (g , Hg) $ₚ au)
  (λ f (au , Hf) → □-pres-lt {c} .from .η A .η (U , H≤) au ,
    ap (Equiv.from (→-ap id≃ (□-underlying {A = A}))) Hf ∙
    ext λ g Hg → □-pres-lt {c} .from .η A .is-natural _ _ (g , Hg) $ₚ au)

-- □-sec-equiv≰
--   : ∀ {U} (A : 𝔇.Ob)
--   → ¬ U .snd ≤ c
--   → is-conc-section ℛ-conc (□⟨ c ⟩ .F₀ A) {U} ≃[ →-ap id≃ (□-underlying {A = A}) ]
--     λ f → Σ[ x ∈ A ʻ ⋆ ] f ≡ λ _ → x
-- □-sec-equiv≰ = {!!}
