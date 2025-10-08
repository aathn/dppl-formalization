open import Lib.Algebra.Reals

module DPPL.Properties.Syntax (R : Reals₀) where

open import DPPL.Regularity
open import DPPL.Syntax R

open import 1Lab.Prelude
open import Order.Lattice

open SyntaxVars
open is-lattice Reg↓-lattice

∩ᵗ-action : (T : Ty) → (c ∩ c') ∩ᵗ T ≡ c ∩ᵗ (c' ∩ᵗ T)
∩ᵗ-action (treal _)         = ap treal (sym ∩-assoc)
∩ᵗ-action (T ⇒[ _ , e ] T') = ap (T ⇒[_, e ] T') (sym ∩-assoc)
∩ᵗ-action (ttup n Ts)       = ap (ttup n) (ext λ i → ∩ᵗ-action (Ts i))
∩ᵗ-action (tdist T)         = refl

≤ᵗ→∩ᵗ : T ≤ᵗ c → c ∩ᵗ T ≡ T
≤ᵗ→∩ᵗ {T = treal d}        H≤ = ap treal (∩-comm ∙ order→∩ H≤)
≤ᵗ→∩ᵗ {T = _ ⇒[ _ , _ ] _} H≤ = ap (_ ⇒[_, _ ] _) (∩-comm ∙ order→∩ H≤)
≤ᵗ→∩ᵗ {T = ttup n Ts}      H≤ = ap (ttup n) (ext λ i → ≤ᵗ→∩ᵗ (H≤ i))
≤ᵗ→∩ᵗ {T = tdist T}        _  = refl
