open import 1Lab.Prelude

open import DPPL.Regularity

open import Lib.Algebra.Reals

open import Order.Lattice
open import Order.Base

import DPPL.Syntax as Syntax

module DPPL.Properties.Syntax (R : Reals₀) where

open is-lattice Reg⊆-lat
open Reg≤
open Syntax R
open SyntaxVars

≤ᵗ→∩ᵗ : T ≤ᵗ X → X ∩ᵗ T ≡ T
≤ᵗ→∩ᵗ {T = treal c} H≤ = ap treal $ ext λ x → Ω-ua
  (λ Hx → case Hx of λ y x≤y Hy Hy' → c .pres-≤ x≤y Hy')
  (λ Hx → case H≤ (x , Hx) of λ y Hy Hy' x≤y → inc (y , x≤y , Hy , Hy'))
≤ᵗ→∩ᵗ {T = T ⇒[ _ ] T'} H≤ = ap (T ⇒[_] T') (∩-comm ∙ order→∩ H≤)
≤ᵗ→∩ᵗ {T = ttup n _} H≤    = ap (ttup n) (ext λ i → ≤ᵗ→∩ᵗ (H≤ i))

≤ᵗ→~ᵗ : T ≤ᵗ X → X ~ᵗ T
≤ᵗ→~ᵗ {T = treal c} H≤             = tt
≤ᵗ→~ᵗ {T = T ⇒[ _ ] T₁} H≤ x y x≤y =
  inc ((y .fst , H≤ _ (y .snd) , y .snd) , x≤y , ≤-refl)
≤ᵗ→~ᵗ {T = ttup n Ts} H≤ i         = ≤ᵗ→~ᵗ (H≤ i)
