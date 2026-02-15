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
      : {c : Coeff} {m n : Nat} → c ≡ A↓ ⊎ c ≡ P↓
      → (f : ℝ ^ m → ℝ ^ n) (Hf : f ∈ ⟨ make c ∥ make c ⟩-reg)
      → ℝ ^ m → ℝ ^ m → ℝ ^ n

    diff-reg
      : ∀ {c : Coeff} {m n : Nat} (Hc : c ≡ A↓ ⊎ c ≡ P↓) c' k
      → (g₁ : ℝ ^ (k + m) → ℝ ^ n) (g₂ g₃ : ℝ ^ k → ℝ ^ m)
      → (Hg₁ : ∀ (x : ℝ ^ k) → (λ y → g₁ (x ++ y)) ∈ ⟨ make c ∥ make c ⟩-reg)
      → (c' ≤ P↓ → g₁ ∈ ⟨ make {n = k} c' ++ make c ∥ make c ⟩-reg)
      → (¬ c' ≤ P↓ → Σ[ g₁' ∈ (ℝ ^ m → ℝ ^ n) ] (λ (x : ℝ ^ k) y → g₁ (x ++ y)) ≡ λ _ → g₁')
      → g₂ ∈ ⟨ make c ⟩-sec (k , c') → g₃ ∈ ⟨ make A↓ ⟩-sec (k , c')
      → (λ x → diff-denot Hc (λ y → g₁ (x ++ y)) (Hg₁ x) (g₂ x) (g₃ x)) ∈ ⟨ make A↓ ⟩-sec (k , c')

    solve-denot
      : {c : Coeff} {n : Nat} → c ≡ A↓ ⊎ c ≡ C↓
      → (f : ℝ ^ (1 + n) → ℝ ^ n) (Hf : f ∈ ⟨ c ∷ make A↓ ∥ make A↓ ⟩-reg)
      → ℝ ^ (1 + n) → ℝ ^ 1 → ℝ ^ (1 + n)

    solve-reg 
      : ∀ {c : Coeff} {n : Nat} (Hc : c ≡ A↓ ⊎ c ≡ C↓) c' k
      → (g₁ : ℝ ^ (k + (1 + n)) → ℝ ^ n) (g₂ : ℝ ^ k → ℝ ^ (1 + n)) (g₃ : ℝ ^ k → ℝ ^ 1)
      → (Hg₁ : ∀ (x : ℝ ^ k) → (λ y → g₁ (x ++ y)) ∈ ⟨ c ∷ make A↓ ∥ make A↓ ⟩-reg)
      → (c' ≤ C↓ → g₁ ∈ ⟨ make {n = k} c' ++ (c ∷ make {n = n} A↓) ∥ make A↓ ⟩-reg)
      → (¬ c' ≤ C↓ → Σ[ g₁' ∈ (ℝ ^ (1 + n) → ℝ ^ n) ] (λ (x : ℝ ^ k) y → g₁ (x ++ y)) ≡ λ _ → g₁')
      → g₂ ∈ ⟨ c ∷ make {n = n} A↓ ⟩-sec (k , c') → g₃ ∈ ⟨ make (c ∩ PC↓) ⟩-sec (k , c') 
      → (λ x → solve-denot Hc (λ y → g₁ (x ++ y)) (Hg₁ x) (g₂ x) (g₃ x)) ∈ ⟨ c ∷ make A↓ ⟩-sec (k , c')

-- module _ (Ax : DenotAssumptions) where
--   open DenotAssumptions Ax

    -- diff-hom
    --   : {c : Coeff} (m n : Nat) → c ≡ A↓ ⊎ c ≡ P↓ → Hom
    --     (□⟨ P↓ ⟩ .F₀ (𝔇ℝ'[ make {n = m} c ] ⇒ 𝔇ℝ'[ make {n = n} c ]) ⊗₀ 𝔇ℝ'[ make {n = m} c ] ⊗₀ 𝔇ℝ'[ make {n = m} A↓ ])
    --     𝔇ℝ'[ make {n = n} A↓ ]
    -- diff-hom = ?

    -- solve-hom
    --   : {c : Coeff} (n : Nat) → c ≡ A↓ ⊎ c ≡ C↓ → Hom
    --     (□⟨ C↓ ⟩ .F₀ (𝔇ℝ[ 1 , c ] ⊗₀ 𝔇ℝ'[ make {n = n} A↓ ] ⇒ 𝔇ℝ'[ make {n = n} A↓ ])
    --      ⊗₀ (𝔇ℝ[ 1 , c ] ⊗₀ 𝔇ℝ'[ make {n = n} A↓ ])
    --      ⊗₀ 𝔇ℝ[ 1 , c ∩ PC↓ ])
    --     (𝔇ℝ[ 1 , A↓ ] ⊗₀ 𝔇ℝ'[ make {n = n} A↓ ])
    -- solve-hom = ?

--   model : DPPL-model _ _
--   model .fst = 𝔇
--   model .snd = record
--     { 𝔇-cartesian = 𝔇-cartesian
--     ; 𝔇-closed    = 𝔇-closed
--     ; □⟨_⟩        = □⟨_⟩
--     ; □-pres-top  = □-pres-top
--     ; □-pres-prod = □-pres-prod
--     ; □-≤         = □-≤
--     ; □-comult    = □-comult
--     ; □⟨A⟩-Id     = □⟨A⟩-Id
--     ; 𝔇ℝ[_]       = 𝔇ℝ[_]
--     ; □-𝔇ℝ        = super-iso→sub-iso _ (adjunct-hom-iso-into μ⊣ν _)
--     ; 𝔇-real      = λ r → よ₁ ℛ (ℛ-const (make r))
--     ; 𝔇-prim      = λ Hϕ → Equiv.from 𝔇ℝ'-hom≃⟨∥⟩-reg (Prim-denot _ , Prim-reg Hϕ)
--     ; 𝔇-cond      = λ cs H≤ → Equiv.from 𝔇ℝ'-hom≃⟨∥⟩-reg (cond-denot , cond-reg cs H≤)
--     ; 𝔇-sub       = λ H≤ → よ₁ ℛ (ℛ-id≤ H≤)
--     ; 𝔇-diff      = diff-denot
--     ; 𝔇-solve     = solve-denot
--     }

--   open Denotations model public
