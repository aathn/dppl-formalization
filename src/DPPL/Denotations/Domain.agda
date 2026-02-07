open import Lib.Algebra.Reals
import DPPL.Denotations.Site as Site

module DPPL.Denotations.Domain (R : Reals₀) (Ax : Site.SiteAssumptions R) where

open import DPPL.Regularity

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
open import Data.Fin.Base hiding (_≤_)
open import Data.Power hiding (_∪_ ; _∩_)
open import Order.Base
open import Order.Lattice
import Cat.Reasoning as Cr
import Cat.Functor.Reasoning as Fr

open Reals R using (ℝ ; 0r)

open Site.Site R Ax
open Site.SiteAssumptions Ax

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

module 𝔇-ip {n} (F : Fin n → 𝔇.Ob) =
  Indexed-product (Cartesian→standard-finite-products terminal products F)
open ProdIso 𝔇-cartesian

□⟨_⟩ : Reg↓ → Functor 𝔇 𝔇
□⟨ c ⟩ = conc-dir-image ℛ-conc ℛ-conc μ⟨ c ⟩ (path→iso μ-pres-top) μ-onto-points

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

□-pres-top : □⟨ c ⟩ .F₀ top ≅ top
□-pres-top = super-iso→sub-iso _
  $ F-map-iso (よ ℛ) (path→iso ν-pres-top) ∘ni adjunct-hom-iso-into μ⊣ν _

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

𝔇ℝ'-underlying : (cs : Reg↓ ^ n) → 𝔇ℝ'[ cs ] ʻ ⋆ ≃ ℝ ^ n
𝔇ℝ'-underlying {n = zero}        cs = ℛ-underlying
𝔇ℝ'-underlying {n = suc zero}    cs = ℛ-underlying
𝔇ℝ'-underlying {n = suc (suc n)} cs =
  Σ-ap ℛ-underlying (λ _ → 𝔇ℝ'-underlying (cs ⊙ fsuc)) ∙e
  vec-prod-sum

𝔇ℝ→𝔇ℝ'-underlying
  : ∀ U (cs : Reg↓ ^ n) → (𝔇ℝ[ U ] ʻ ⋆ → 𝔇ℝ'[ cs ] ʻ ⋆) ≃ (ℝ ^ (U .fst) → ℝ ^ n)
𝔇ℝ→𝔇ℝ'-underlying U cs = →-ap ℛ-underlying (𝔇ℝ'-underlying cs)


⟨_⟩-sec : Reg↓ ^ n → (U : Nat × Reg↓) → (ℝ ^ (U .fst) → ℝ ^ n) → Type _
⟨ cs ⟩-sec U g = ∀ i → π'[ i ] ⊙ g ∈ ⟨ U .snd ∣ cs i ⟩-reg

⟨_∥_⟩-reg : Reg↓ ^ m → Reg↓ ^ n → (ℝ ^ m → ℝ ^ n) → Type _
⟨_∥_⟩-reg {m} {n} cs cs' f =
  {U : Nat × Reg↓} (g : ℝ ^ (U .fst) → ℝ ^ m)
  → g ∈ ⟨ cs ⟩-sec U → f ⊙ g ∈ ⟨ cs' ⟩-sec U

∈-sec→conc-section
  : ∀ {U} {cs : Reg↓ ^ n} (f : ℝ ^ U .fst → ℝ ^ n)
  → f ∈ ⟨ cs ⟩-sec U
  → is-conc-section ℛ-conc 𝔇ℝ'[ cs ] (Equiv.from (𝔇ℝ→𝔇ℝ'-underlying U cs) f)
∈-sec→conc-section {zero} f Hf = ℛ⊤.! , ext λ _ _ → ℛ-hom-path (ext λ _ ())
∈-sec→conc-section {suc zero} {U} {cs} f Hf =
  (π'[ fzero ] ⊙ f , Hf fzero) , ext λ g _ →
    ℛ-hom-path (ext λ _ → Fin-cases (ap (λ z → f (g z) _) (ext λ ())) (λ ()))
∈-sec→conc-section {suc (suc n)} {U} {cs} f Hf =
  let f' , Hf' = ∈-sec→conc-section (λ x → f x ⊙ fsuc) (Hf ⊙ fsuc)
  in  ((π'[ fzero ] ⊙ f , Hf fzero) , f') , ext λ g Hg →
    ℛ-hom-path (ext λ _ → Fin-cases (ap (λ z → f (g z) _) (ext λ ())) (λ ())) ,ₚ
    ap (Equiv.from (𝔇ℝ'-underlying (tail cs))) (transport-refl _) ∙ Hf' $ₚ (g , Hg)

conc-section→∈-sec
  : ∀ {U} {cs : Reg↓ ^ n} (f : 𝔇ℝ[ U ] ʻ ⋆ → 𝔇ℝ'[ cs ] ʻ ⋆)
  → is-conc-section ℛ-conc 𝔇ℝ'[ cs ] f
  → Equiv.to (𝔇ℝ→𝔇ℝ'-underlying U cs) f ∈ ⟨ cs ⟩-sec U
conc-section→∈-sec {zero} f _                            = λ ()
conc-section→∈-sec {suc zero} {U} {cs} f ((g , Hg) , Hf) =
  let Hf'  = ap ((π'[ fzero ] ⊙_) ⊙ Equiv.to (𝔇ℝ→𝔇ℝ'-underlying U cs)) Hf ∙
             ext λ _ → Fin-cases refl λ ()
      Hsec = subst (_∈ ⟨ U .snd ∣ cs fzero ⟩-reg) (sym Hf') Hg
  in Fin-cases Hsec λ ()
conc-section→∈-sec {suc (suc n)} {U} {cs} f (((g₁ , Hg₁) , g₂) , Hf) =
  let Hf' = ap (λ z → π'[ fzero ] ⊙ Equiv.to (𝔇ℝ→𝔇ℝ'-underlying U cs) z) Hf ∙
            ext λ _ → Fin-cases refl λ () 
      Hsec₁ = subst (λ x → ∣ ⟨ U .snd ∣ cs fzero ⟩-reg x ∣) (sym Hf') Hg₁
      Hsec₂ = conc-section→∈-sec (snd ⊙ f) (g₂ , ap (snd ⊙_) Hf)
  in
  Fin-cases Hsec₁ Hsec₂

∈-sec≃conc-section
  : ∀ {U} {cs : Reg↓ ^ n}
  → (_∈ ⟨ cs ⟩-sec U) ≃[ 𝔇ℝ→𝔇ℝ'-underlying U cs e⁻¹ ] is-conc-section ℛ-conc 𝔇ℝ'[ cs ]
∈-sec≃conc-section {U = U} {cs = cs} =
  prop-over-ext (𝔇ℝ→𝔇ℝ'-underlying _ cs e⁻¹)
    (hlevel 1) (λ {b} → is-conc-section-prop ℛ-conc 𝔇ℝ'[ cs ] b)
    ∈-sec→conc-section
    conc-section→∈-sec

⟨⟩-sec≃𝔇ℝ'-section
  : ∀ {U} {cs : Reg↓ ^ n}
  → ∫ₚ (⟨ cs ⟩-sec U) ≃ ∫ₚ (is-conc-section ℛ-conc {U = U} 𝔇ℝ'[ cs ])
⟨⟩-sec≃𝔇ℝ'-section {U = U} {cs} =
  Σ-ap (𝔇ℝ→𝔇ℝ'-underlying U cs e⁻¹) λ _ → ∈-sec≃conc-section _ _ refl

⟨∥⟩-reg≃Hom
  : {cs : Reg↓ ^ m} {cs' : Reg↓ ^ n}
  → ∫ₚ ⟨ cs ∥ cs' ⟩-reg ≃ Hom 𝔇ℝ'[ cs ] 𝔇ℝ'[ cs' ]
⟨∥⟩-reg≃Hom {cs = cs} {cs'} =
  eqv'' ∙e Iso→Equiv (eqv {A = 𝔇ℝ'[ cs ]} {𝔇ℝ'[ cs' ]}) e⁻¹ ∙e Conc-hom≃Hom ℛ-conc
  where
    unquoteDecl eqv = declare-record-iso eqv (quote Conc-hom)
    eqv'  = →-ap (𝔇ℝ'-underlying _ e⁻¹) (𝔇ℝ'-underlying _ e⁻¹)
    eqv'' = Σ-ap eqv' λ f → Π'-ap-cod λ U → curry≃ e⁻¹ ∙e
      Π-ap-dom ((⟨⟩-sec≃𝔇ℝ'-section ∙e conc-section≃section ℛ-conc (𝔇ℝ'[ cs ])) e⁻¹) ∙e
      Π-ap-cod λ g → ∈-sec≃conc-section _ _ $ funext λ z →
        ap (Equiv.to eqv' f ⊙ conc-section ℛ-conc (𝔇ℝ'[ cs ] .fst) g)
           (ℛ-hom-path (ext λ _ i → ap (λ y → z .fst y i) (ext λ ())))
