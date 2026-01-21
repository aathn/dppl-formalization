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
open import Cat.Diagram.Terminal
open import Cat.Monoidal.Base
open import Cat.Monoidal.Instances.Cartesian
open import Cat.Functor.Base
open import Cat.Functor.Coherence
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Naturality
open import Data.Fin.Base hiding (_≤_)
open import Data.Power hiding (_∪_ ; _∩_)
open import Order.Base
open import Order.Lattice
import Cat.Reasoning as Cr
import Cat.Functor.Bifunctor as Bifunctor
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
open Monoidal-category (Cartesian-monoidal 𝔇-cartesian)

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
□-pres-top = super-iso→sub-iso _ (to-natural-iso ni) where
  ni : make-natural-iso _ _
  ni .make-natural-iso.eta _ u       = u
  ni .make-natural-iso.inv _ u       = u
  ni .make-natural-iso.eta∘inv _     = refl
  ni .make-natural-iso.inv∘eta _     = refl
  ni .make-natural-iso.natural _ _ _ = refl

□-pres-prod : ∀ X Y → □⟨ c ⟩ .F₀ (X ⊗ Y) ≅ (□⟨ c ⟩ .F₀ X ⊗ □⟨ c ⟩ .F₀ Y)
□-pres-prod X Y = super-iso→sub-iso _ (to-natural-iso ni) where
  ni : make-natural-iso _ _
  ni .make-natural-iso.eta _ u       = u
  ni .make-natural-iso.inv _ u       = u
  ni .make-natural-iso.eta∘inv _     = refl
  ni .make-natural-iso.inv∘eta _     = refl
  ni .make-natural-iso.natural _ _ _ = refl


⟨_⟩-sec : Reg↓ ^ n → (U : Nat × Reg↓) → ℙ (ℝ ^ (U .fst) → ℝ ^ n)
⟨ cs ⟩-sec U g = elΩ $ ∀ i → π'[ i ] ⊙ g ∈ ⟨ U .snd ∣ cs i ⟩-reg

⟨_∥_⟩-reg : Reg↓ ^ m → Reg↓ ^ n → (ℝ ^ m → ℝ ^ n) → Type _
⟨_∥_⟩-reg {m} {n} cs cs' f =
  ∀ {U : Nat × Reg↓} (g : ℝ ^ (U .fst) → ℝ ^ m)
  → g ∈ ⟨ cs ⟩-sec U → f ⊙ g ∈ ⟨ cs' ⟩-sec U

𝔇ℝ[_] : ℛ.Ob → 𝔇.Ob
𝔇ℝ[_] = Conc-よ₀ ℛ-conc

𝔇ℝ'[_] : Reg↓ ^ n → 𝔇.Ob
𝔇ℝ'[ cs ] = 𝔇-ip.ΠF λ i → 𝔇ℝ[ 1 , cs i ]

𝔇ℝ'-cons : (cs : Reg↓ ^ suc m) → 𝔇ℝ'[ cs ] ≅ (𝔇ℝ[ 1 , head cs ] ⊗ 𝔇ℝ'[ tail cs ])
𝔇ℝ'-cons = {!!}

𝔇ℝ'-⊗
  : (cs : Reg↓ ^ m) (cs' : Reg↓ ^ n)
  → (𝔇ℝ'[ cs ] ⊗ 𝔇ℝ'[ cs' ]) ≅ 𝔇ℝ'[ cs ++ cs' ]
𝔇ℝ'-⊗ {m = zero} cs cs' =
  λ≅ {𝔇ℝ'[ cs' ]} Iso⁻¹ ∙Iso path→iso (ap 𝔇ℝ'[_] (++-split 0 (cs ++ cs')))
𝔇ℝ'-⊗ {m = suc m} cs cs' =
  F-map-iso (Bifunctor.Left -⊗- 𝔇ℝ'[ cs' ]) (𝔇ℝ'-cons cs) ∙Iso
  -- α≅ {A = 𝔇ℝ[ 1 , head cs ]} {𝔇ℝ'[ tail cs ]} {𝔇ℝ'[ cs' ]} ∙Iso
  foo ∙Iso
  {!!}
  where foo : ((𝔇ℝ[ 1 , head cs ] ⊗ 𝔇ℝ'[ tail cs ]) ⊗ 𝔇ℝ'[ cs' ]) ≅ (𝔇ℝ[ 1 , head cs ] ⊗ (𝔇ℝ'[ tail cs ] ⊗ 𝔇ℝ'[ cs' ]))
        foo = α≅ {A = 𝔇ℝ[ 1 , head cs ]} {𝔇ℝ'[ tail cs ]} {𝔇ℝ'[ cs' ]}
-- (cs : Reg↓ ^ (1 + m)) → 𝔇ℝ'[ cs ] ≅ 𝔇ℝ[ head cs ] ⊗ 𝔇ℝ'[ tail cs ]

top-underlying : top ʻ ⋆ ≃ ℝ ^ 0
top-underlying = Iso→Equiv
  $ (λ _ ()) , iso (λ _ → lift tt) (λ _ → ext λ ()) (λ _ → refl)

𝔇ℝ-underlying : ∀ U → 𝔇ℝ[ U ] ʻ ⋆ ≃ ℝ ^ (U .fst)
𝔇ℝ-underlying U = Iso→Equiv
  $ (λ (f , _) → f (make 0r))
  , iso (λ x → ℛ-const x)
    (λ _ → refl)
    (λ f → ℛ-hom-path (ext λ _ x → ap (λ y → f .fst y x) (ext λ ())))

𝔇ℝ'-underlying : (cs : Reg↓ ^ n) → 𝔇ℝ'[ cs ] ʻ ⋆ ≃ ℝ ^ n
𝔇ℝ'-underlying {n = zero}        cs = top-underlying
𝔇ℝ'-underlying {n = suc zero}    cs = 𝔇ℝ-underlying (1 , cs fzero)
𝔇ℝ'-underlying {n = suc (suc n)} cs =
  Σ-ap (𝔇ℝ-underlying (1 , cs fzero)) (λ _ → 𝔇ℝ'-underlying (cs ⊙ fsuc)) ∙e
  vec-prod-sum

𝔇ℝ→𝔇ℝ'-underlying
  : ∀ U (cs : Reg↓ ^ n) → (𝔇ℝ[ U ] ʻ ⋆ → 𝔇ℝ'[ cs ] ʻ ⋆) ≃ (ℝ ^ (U .fst) → ℝ ^ n)
𝔇ℝ→𝔇ℝ'-underlying U cs = →-ap (𝔇ℝ-underlying U) (𝔇ℝ'-underlying cs)

⟨⟩-sec→𝔇ℝ'-section : ∀ {U} {cs : Reg↓ ^ n} → ∫ₚ (⟨ cs ⟩-sec U) → 𝔇ℝ'[ cs ] ʻ U
⟨⟩-sec→𝔇ℝ'-section {n = zero} (f , Hf)     = lift tt
⟨⟩-sec→𝔇ℝ'-section {n = suc zero} (f , Hf) =
  π'[ fzero ] ⊙ f , case Hf of λ Hf' → Hf' fzero
⟨⟩-sec→𝔇ℝ'-section {n = suc (suc n)} (f , Hf) =
  (π'[ fzero ] ⊙ f , case Hf of λ Hf' → Hf' fzero) ,
  ⟨⟩-sec→𝔇ℝ'-section {n = suc n}
    ((λ x → f x ⊙ fsuc) , case Hf of λ Hf' → inc (Hf' ⊙ fsuc))

𝔇ℝ'-section→⟨⟩-sec : ∀ {U} {cs : Reg↓ ^ n} → 𝔇ℝ'[ cs ] ʻ U → ∫ₚ (⟨ cs ⟩-sec U)
𝔇ℝ'-section→⟨⟩-sec {n = zero} f                         = (λ _ ()) , inc λ ()
𝔇ℝ'-section→⟨⟩-sec {n = suc zero} {_ , c} {cs} (f , Hf) =
  f , inc (Fin-cases (subst (_∈ ⟨ c ∣ cs fzero ⟩-reg) (sym (π'1 f)) Hf) λ ())
𝔇ℝ'-section→⟨⟩-sec {n = suc (suc n)} {_ , c} {cs} ((f , Hf) , Hfs) =
  let f' , Hf' = 𝔇ℝ'-section→⟨⟩-sec {n = suc n} Hfs in
  (λ x → f x ++ f' x) , case Hf' of λ Hreg →
    inc (Fin-cases (subst (_∈ ⟨ c ∣ cs fzero ⟩-reg) (sym (π'1 f)) Hf) Hreg)

⟨⟩-sec≃𝔇ℝ'-section : ∀ {U} {cs : Reg↓ ^ n} → ∫ₚ (⟨ cs ⟩-sec U) ≃ 𝔇ℝ'[ cs ] ʻ U
⟨⟩-sec≃𝔇ℝ'-section =
  Iso→Equiv $ ⟨⟩-sec→𝔇ℝ'-section , iso 𝔇ℝ'-section→⟨⟩-sec rinv linv where
  rinv : ∀ {n} {cs : Reg↓ ^ n} → is-right-inverse (𝔇ℝ'-section→⟨⟩-sec {cs = cs}) ⟨⟩-sec→𝔇ℝ'-section
  rinv {zero} (lift tt)       = refl
  rinv {suc zero} f           = ℛ-hom-path (π'1 (f .fst))
  rinv {suc (suc n)} (f , fs) = ℛ-hom-path (π'1 (f .fst)) ,ₚ
    ap ⟨⟩-sec→𝔇ℝ'-section (ext λ _ _ → refl) ∙ rinv {suc n} fs
  linv : ∀ {n} {cs : Reg↓ ^ n} → is-left-inverse (𝔇ℝ'-section→⟨⟩-sec {cs = cs}) ⟨⟩-sec→𝔇ℝ'-section
  linv {zero} _                    = ext λ _ ()
  linv {suc zero} (f , Hf)         = ext λ _ _ → π'1 f $ₚ _ $ₚ _
  linv {suc (suc n)} {cs} (f , Hf) = ext λ x i →
    let p = linv {suc n} {cs ⊙ fsuc}
          $ (λ x → f x ⊙ fsuc) , case Hf of λ Hf' → inc (Hf' ⊙ fsuc)
    in
    ap (λ l → (π'[ fzero ] ⊙ f) x ++ l x $ i) (ap fst p) ∙
    ++-singleton $ₚ i ∙ ∷-head-tail (f x) $ₚ i

⟨⟩-sec≃𝔇ℝ'-conc-section
  : ∀ {U} {cs : Reg↓ ^ n}
  → ∫ₚ (⟨ cs ⟩-sec U) ≃ ∫ₚ (is-conc-section ℛ-conc {U = U} 𝔇ℝ'[ cs ])
⟨⟩-sec≃𝔇ℝ'-conc-section {cs = cs} =
  ⟨⟩-sec≃𝔇ℝ'-section ∙e conc-section≃section ℛ-conc {A = 𝔇ℝ'[ cs ]} e⁻¹

sec≃𝔇ℝ'-pres-dom
  : ∀ {U} {cs : Reg↓ ^ n}
  → Equiv.from (𝔇ℝ→𝔇ℝ'-underlying U cs) ⊙ fst ≡ fst ⊙ Equiv.to ⟨⟩-sec≃𝔇ℝ'-conc-section
sec≃𝔇ℝ'-pres-dom {zero}     = refl
sec≃𝔇ℝ'-pres-dom {suc zero} = ext λ f _ g _ → ℛ-hom-path
  $ ext λ _ → Fin-cases (ap (λ x → f (g x) _) (ext λ ())) λ ()
sec≃𝔇ℝ'-pres-dom {suc (suc n)} {U} {cs} = ext λ f Hf g Hg →
  ℛ-hom-path (ext λ _ → Fin-cases (ap (λ x → f (g x) _) (ext λ ())) λ ()) ,ₚ
  ap (λ z → 𝔇ℝ'-underlying (cs ⊙ fsuc) .snd .is-eqv z .centre .fst) (transport-refl _)
  ∙ sec≃𝔇ℝ'-pres-dom {suc n} {U} {cs ⊙ fsuc}
    $ₚ ((λ x → f x ⊙ fsuc) , case Hf of λ Hf' → inc (Hf' ⊙ fsuc)) $ₚ (g , Hg)

∈-sec≃conc-section
  : ∀ {U} {cs : Reg↓ ^ n}
  → (_∈ ⟨ cs ⟩-sec U) ≃[ 𝔇ℝ→𝔇ℝ'-underlying U cs e⁻¹ ] is-conc-section ℛ-conc 𝔇ℝ'[ cs ]
∈-sec≃conc-section {U = U} {cs = cs} =
  prop-over-ext (𝔇ℝ→𝔇ℝ'-underlying _ cs e⁻¹)
    (hlevel 1) (λ {b} → is-conc-section-prop ℛ-conc 𝔇ℝ'[ cs ] b)
    (λ f Hf →
      subst (is-conc-section ℛ-conc 𝔇ℝ'[ cs ]) (sym sec≃𝔇ℝ'-pres-dom $ₚ (f , Hf))
      $ Equiv.to ⟨⟩-sec≃𝔇ℝ'-conc-section (f , Hf) .snd)
    (λ f Hf →
      let pres-dom' = swizzle-equiv (𝔇ℝ→𝔇ℝ'-underlying U cs)
            ⟨⟩-sec≃𝔇ℝ'-conc-section fst fst sec≃𝔇ℝ'-pres-dom
      in
      subst (_∈ ⟨ cs ⟩-sec _) (sym pres-dom' $ₚ (f , Hf))
      $ Equiv.from ⟨⟩-sec≃𝔇ℝ'-conc-section (f , Hf) .snd)

⟨∥⟩-reg≃Hom
  : {cs : Reg↓ ^ m} {cs' : Reg↓ ^ n}
  → ∫ₚ ⟨ cs ∥ cs' ⟩-reg ≃ Hom 𝔇ℝ'[ cs ] 𝔇ℝ'[ cs' ]
⟨∥⟩-reg≃Hom {cs = cs} {cs'} =
  eqv'' ∙e Iso→Equiv (eqv {A = 𝔇ℝ'[ cs ]} {𝔇ℝ'[ cs' ]}) e⁻¹ ∙e Conc-hom≃Hom ℛ-conc
  where
    unquoteDecl eqv = declare-record-iso eqv (quote Conc-hom)
    eqv' = →-ap (𝔇ℝ'-underlying _ e⁻¹) (𝔇ℝ'-underlying _ e⁻¹)
    eqv'' = Σ-ap eqv' λ f → Π'-ap-cod λ x →
      Π-ap-dom (𝔇ℝ→𝔇ℝ'-underlying x cs) ∙e
      Π-ap-cod λ g → →-ap
        (∈-sec≃conc-section _ _ (Equiv.η (𝔇ℝ→𝔇ℝ'-underlying x cs) _))
        (∈-sec≃conc-section _ _
          (funext λ z → ap (Equiv.to eqv' f ⊙ g)
            (ℛ-hom-path (ext λ _ i → ap (λ y → z .fst y i) (ext λ ())))))
