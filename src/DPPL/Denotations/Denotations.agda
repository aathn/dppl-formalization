open import Lib.Algebra.Reals
import DPPL.Denotations.Site as Site

module DPPL.Denotations.Denotations (R : Reals₀) (Ax : Site.SiteAssumptions R) where

open import DPPL.Regularity
open import DPPL.Syntax R
open import DPPL.Typing R
open import DPPL.Denotations.Model R
open import DPPL.Denotations.Domain R Ax
open Site.Site R Ax

open import Lib.Cat.Concrete
open import Lib.Cat.Subcategory
open import Lib.Data.Vector

open import Cat.Prelude
open import Cat.Cartesian
open import Cat.Diagram.Exponential
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Hom
open import Data.Sum using (_⊎_)
open import Order.Lattice

open Reals R using (ℝ)
open SyntaxVars

open Reg↓≤ using (_≤_)
open is-lattice Reg↓-lattice hiding (top)

open Functor

open Cartesian-category 𝔇-cartesian
open Cartesian-closed 𝔇-closed renaming ([_,_] to _⇒_)

open import Data.Fin.Base

bug : (n : Nat) → Type
bug n =
  Hom
    (top ⊗₀ (Conc-よ₀ ℛ-conc ⋆ ⊗₀ 𝔇-ip.ΠF (λ (_ : Fin n) → top)) ⊗₀ top)
    top

record MyRecord : Type where
  field
    my-field : (n : Nat) → bug n
--     Prim-denot : (ϕ : Prim) → ℝ ^ PrimAr ϕ → ℝ ^ 1
--     Prim-reg
--       : {cs : Coeff ^ PrimAr ϕ} → PrimTy ϕ ≡ (cs , c)
--       → Prim-denot ϕ ∈ ⟨ cs ∥ make c ⟩-reg

--     cond-denot : ℝ ^ (1 + (n + n)) → ℝ ^ n
--     cond-reg
--       : (cs : Coeff ^ n) (_ : ∀ i → P↓ ≤ cs i)
--       → cond-denot ∈ ⟨ make {n = 1} P↓ ++ (cs ++ cs) ∥ cs ⟩-reg

--     diff-denot
--       : {c : Coeff} (n m : Nat) → c ≡ A↓ ⊎ c ≡ P↓ → Hom
--         (□⟨ P↓ ⟩ .F₀ (𝔇ℝ'[ make {n = n} c ] ⇒ 𝔇ℝ'[ make {n = m} c ]) ⊗₀ 𝔇ℝ'[ make {n = n} c ])
--         (𝔇ℝ'[ make {n = n} A↓ ] ⇒ 𝔇ℝ'[ make {n = m} A↓ ])

--     -- solve-denot
--     --   : {c : Coeff} (n : Nat) → c ≡ A↓ ⊎ c ≡ C↓ → foo c n

-- module _ (Ax : DenotAssumptions) where
--   open DenotAssumptions Ax

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
--     ; □-𝔇ℝ        = iso→sub-iso (adjunct-hom-iso-into μ⊣ν _)
--     ; 𝔇ℝ'-⊗       = {!!}
--     ; 𝔇-real      = λ r →
--       full-hom (よ₁ ℛ (ℛ-const (make r))) ∘ よ⋆-is-terminal ℛ-conc _ .centre
--     ; 𝔇-prim  = λ Hϕ → Equiv.to ⟨∥⟩-reg≃Hom (Prim-denot _ , Prim-reg Hϕ)
--     ; 𝔇-cond  = λ cs H≤ → Equiv.to ⟨∥⟩-reg≃Hom (cond-denot , cond-reg cs H≤)
--     ; 𝔇-sub   = λ H≤ → full-hom (よ₁ ℛ (ℛ-id≤ H≤))
--     ; 𝔇-diff  = diff-denot
--     ; 𝔇-solve = {!!}
--     }
