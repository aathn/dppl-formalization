open import Lib.Algebra.Reals
open import DPPL.Denotations.Regularity

module DPPL.Denotations.Denotations (R : Reals₀) (Ax : RegAssumptions R) where

open import DPPL.Regularity
open import DPPL.Syntax R
open import DPPL.Typing R
open import DPPL.Denotations.Model R
open import DPPL.Denotations.Domain R Ax
open import DPPL.Denotations.Site R Ax

open import Lib.Cat.Concrete
open import Lib.Data.Vector

open import Cat.Prelude
open import Cat.Cartesian
open import Cat.Diagram.Exponential
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Hom
open import Data.Sum using (_⊎_)
open import Order.Lattice

open Reals R using (ℝ)
open RegAssumptions Ax

open SyntaxVars

open Reg↓≤ using (_≤_)
open is-lattice Reg↓-lattice hiding (top)

open VectorSyntax

open Functor

open Cartesian-category 𝔇-cartesian
open Cartesian-closed 𝔇-closed renaming ([_,_] to infixr 4 _⇒_)

record DenotAssumptions : Type where
  field
    Prim-denot : (ϕ : Prim) → ℝ ^ PrimAr ϕ → ℝ ^ 1
    Prim-reg
      : {cs : Coeff ^ PrimAr ϕ} → PrimTy ϕ ≡ (cs , c)
      → Prim-denot ϕ ∈ ⟨ cs ∥ make c ⟩-reg

    cond-denot : ℝ ^ (1 + (n + n)) → ℝ ^ n
    cond-reg
      : (cs : Coeff ^ n) (_ : ∀ i → P↓ ≤ cs i)
      → cond-denot ∈ ⟨ make {n = 1} P↓ ++ (cs ++ cs) ∥ cs ⟩-reg

    diff-denot
      : ∀ m n → c ≡ A↓ ⊎ c ≡ P↓
      → ∫ₚ ⟨ make {n = m} c ∥ make {n = n} c ⟩-reg × ℝ ^ m × ℝ ^ m
      → ℝ ^ n

    diff-reg
      : ∀ m n (Hc : c ≡ A↓ ⊎ c ≡ P↓) {U}
      → (g : ℝ ^ U .fst → ∫ₚ ⟨ make c ∥ make {n = n} c ⟩-reg × ℝ ^ m × ℝ ^ m)
      → (fst ⊙ g ∈ bound-sec P↓ ⟨ make c ∥ make c ⟩-hom-sec U ×
         fst ⊙ snd ⊙ g ∈ ⟨ make c ⟩-sec U ×
         snd ⊙ snd ⊙ g ∈ ⟨ make A↓ ⟩-sec U)
      → diff-denot m n Hc ⊙ g ∈ ⟨ make A↓ ⟩-sec U

    solve-denot
      : ∀ n → c ≡ A↓ ⊎ c ≡ C↓
      → ∫ₚ ⟨ c ∷ make {n = n} A↓ ∥ make {n = n} A↓ ⟩-reg × ℝ ^ (1 + n) × ℝ ^ 1
      → ℝ ^ (1 + n)

    solve-reg
      : ∀ n (Hc : c ≡ A↓ ⊎ c ≡ C↓) {U}
      → (g : ℝ ^ U .fst → ∫ₚ ⟨ c ∷ make A↓ ∥ make A↓ ⟩-reg × ℝ ^ (1 + n) × ℝ ^ 1)
      → (fst ⊙ g ∈ bound-sec C↓ ⟨ c ∷ make A↓ ∥ make A↓ ⟩-hom-sec U ×
         fst ⊙ snd ⊙ g ∈ ⟨ c ∷ make A↓ ⟩-sec U ×
         snd ⊙ snd ⊙ g ∈ ⟨ U .snd ∣ c ∩ PC↓ ⟩-reg)
      → solve-denot n Hc ⊙ g ∈ ⟨ make A↓ ⟩-sec U

module _ (Ax : DenotAssumptions) where
  open DenotAssumptions Ax

  diff-hom
    : ∀ m n → c ≡ A↓ ⊎ c ≡ P↓ → Hom
      (□⟨ P↓ ⟩ .F₀ (𝔇ℝ'[ make {n = m} c ] ⇒ 𝔇ℝ'[ make {n = n} c ]) ⊗₀
        𝔇ℝ'[ make {n = m} c ] ⊗₀ 𝔇ℝ'[ make {n = m} A↓ ])
      𝔇ℝ'[ make {n = n} A↓ ]
  diff-hom {c} m n Hc = Equiv.from
    (Hom≃Cpsh-hom ℛ-conc
      {A = □⟨ P↓ ⟩ .F₀ (𝔇ℝ'[ make {n = m} c ] ⇒ 𝔇ℝ'[ make {n = n} c ]) ⊗₀
             𝔇ℝ'[ make {n = m} c ] ⊗₀ 𝔇ℝ'[ make {n = m} A↓ ]}
      {𝔇ℝ'[ make {n = n} A↓ ]} ∙e
    Cpsh-hom≃Cpsh-hom' ℛ-conc ℛ-underlying
      (Σ-ap (□-underlying {A = 𝔇ℝ'[ make {n = m} c ] ⇒ 𝔇ℝ'[ make {n = n} c ]} ∙e
              (⇒-underlying ℛ-conc ∙e 𝔇ℝ'-hom≃⟨∥⟩-reg)) λ _ →
       Σ-ap (𝔇ℝ'-underlying (make c)) λ _ → 𝔇ℝ'-underlying (make A↓))
      (𝔇ℝ'-underlying (make A↓))
      (over-left→over
        (→-ap ℛ-underlying
          (Σ-ap (□-underlying {A = 𝔇ℝ'[ make {n = m} c ] ⇒ 𝔇ℝ'[ make {n = n} c ]} ∙e
                  (⇒-underlying ℛ-conc ∙e 𝔇ℝ'-hom≃⟨∥⟩-reg)) λ _ →
           Σ-ap (𝔇ℝ'-underlying (make c)) λ _ → 𝔇ℝ'-underlying (make A↓))) λ f →
        ⊗-sec-equiv ℛ-conc
          {A = □⟨ P↓ ⟩ .F₀ (𝔇ℝ'[ make {n = m} c ] ⇒ 𝔇ℝ'[ make {n = n} c ])}
          {𝔇ℝ'[ make {n = m} c ] ⊗₀ 𝔇ℝ'[ make {n = m} A↓ ]} f ∙e
        Σ-ap (□-sec-equiv {A = 𝔇ℝ'[ make {n = m} c ] ⇒ 𝔇ℝ'[ make {n = n} c ]}
               ℛ-underlying (⇒-underlying ℛ-conc ∙e 𝔇ℝ'-hom≃⟨∥⟩-reg) 𝔇ℝ'⇒𝔇ℝ'-sec-equiv _ _ refl) λ _ →
        ⊗-sec-equiv ℛ-conc {A = 𝔇ℝ'[ make {n = m} c ]} {𝔇ℝ'[ make {n = m} A↓ ]} (snd ⊙ f) ∙e
        Σ-ap (𝔇ℝ'-sec-equiv _ _ refl) λ _ → 𝔇ℝ'-sec-equiv _ _ refl)
      𝔇ℝ'-sec-equiv)
    (diff-denot {c} m n Hc , diff-reg m n Hc)

  solve-hom
    : ∀ n → c ≡ A↓ ⊎ c ≡ C↓ → Hom
      (□⟨ C↓ ⟩ .F₀ (𝔇ℝ'[ c ∷ make {n = n} A↓ ] ⇒ 𝔇ℝ'[ make {n = n} A↓ ])
       ⊗₀ 𝔇ℝ'[ c ∷ make {n = n} A↓ ]
       ⊗₀ 𝔇ℝ[ 1 , c ∩ PC↓ ])
      (𝔇ℝ'[ make {n = 1 + n} A↓ ])
  solve-hom {c} n Hc = Equiv.from
    (Hom≃Cpsh-hom ℛ-conc
      {A = □⟨ C↓ ⟩ .F₀ (𝔇ℝ'[ c ∷ make {n = n} A↓ ] ⇒ 𝔇ℝ'[ make {n = n} A↓ ]) ⊗₀
             𝔇ℝ'[ c ∷ make {n = n} A↓ ] ⊗₀ 𝔇ℝ[ 1 , c ∩ PC↓ ]}
      {𝔇ℝ'[ make {n = 1 + n} A↓ ]} ∙e
    Cpsh-hom≃Cpsh-hom' ℛ-conc ℛ-underlying
      (Σ-ap (□-underlying {A = 𝔇ℝ'[ c ∷ make {n = n} A↓ ] ⇒ 𝔇ℝ'[ make {n = n} A↓ ]} ∙e
              (⇒-underlying ℛ-conc ∙e 𝔇ℝ'-hom≃⟨∥⟩-reg)) λ _ →
       Σ-ap (𝔇ℝ'-underlying (c ∷ make A↓)) λ _ → 𝔇ℝ-underlying)
      (𝔇ℝ'-underlying (make A↓))
      (over-left→over
        (→-ap ℛ-underlying
          (Σ-ap (□-underlying {A = 𝔇ℝ'[ c ∷ make {n = n} A↓ ] ⇒ 𝔇ℝ'[ make {n = n} A↓ ]} ∙e
              (⇒-underlying ℛ-conc ∙e 𝔇ℝ'-hom≃⟨∥⟩-reg)) λ _ →
           Σ-ap (𝔇ℝ'-underlying (c ∷ make A↓)) λ _ → 𝔇ℝ-underlying)) λ f →
        ⊗-sec-equiv ℛ-conc
          {A = □⟨ C↓ ⟩ .F₀ (𝔇ℝ'[ c ∷ make {n = n} A↓ ] ⇒ 𝔇ℝ'[ make {n = n} A↓ ])}
          {𝔇ℝ'[ c ∷ make {n = n} A↓ ] ⊗₀ 𝔇ℝ[ 1 , c ∩ PC↓ ]} f ∙e
        Σ-ap (□-sec-equiv {A = 𝔇ℝ'[ c ∷ make {n = n} A↓ ] ⇒ 𝔇ℝ'[ make {n = n} A↓ ]}
               ℛ-underlying (⇒-underlying ℛ-conc ∙e 𝔇ℝ'-hom≃⟨∥⟩-reg) 𝔇ℝ'⇒𝔇ℝ'-sec-equiv _ _ refl) λ _ →
        ⊗-sec-equiv ℛ-conc {A = 𝔇ℝ'[ c ∷ make {n = n} A↓ ]} {𝔇ℝ[ 1 , c ∩ PC↓ ]} (snd ⊙ f) ∙e
        Σ-ap (𝔇ℝ'-sec-equiv _ _ refl) λ _ → 𝔇ℝ-sec-equiv _ _ refl)
      𝔇ℝ'-sec-equiv)
    (solve-denot {c} n Hc , solve-reg n Hc)

  model : DPPL-model _ _
  model .fst = 𝔇
  model .snd = record
    { 𝔇-cartesian = 𝔇-cartesian
    ; 𝔇-closed    = 𝔇-closed
    ; □⟨_⟩        = □⟨_⟩
    ; □-pres-top  = □-pres-top
    ; □-pres-prod = □-pres-prod
    ; □-≤         = □-≤
    ; □-comult    = □-comult
    ; □⟨A⟩-Id     = □⟨A⟩-Id
    ; 𝔇ℝ[_]       = 𝔇ℝ[_]
    ; □-𝔇ℝ        = super-iso→sub-iso _ (adjunct-hom-iso-into μ⊣ν _)
    ; 𝔇-real      = λ r → よ ℛ .F₁ (ℛ-const (make r))
    ; 𝔇-prim      = λ Hϕ → Equiv.from (Hom≃Cpsh-hom ℛ-conc ∙e 𝔇ℝ'-hom≃⟨∥⟩-reg) (Prim-denot _ , Prim-reg Hϕ)
    ; 𝔇-cond      = λ cs H≤ → Equiv.from (Hom≃Cpsh-hom ℛ-conc ∙e 𝔇ℝ'-hom≃⟨∥⟩-reg) (cond-denot , cond-reg cs H≤)
    ; 𝔇-sub       = λ H≤ → よ ℛ .F₁ (ℛ-id≤ H≤)
    ; 𝔇-diff      = diff-hom
    ; 𝔇-solve     = solve-hom
    }

  open Denotations model public
