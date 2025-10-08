open import Lib.Algebra.Reals

module DPPL.Properties.Typing (R : Reals₀) where

open import 1Lab.Prelude

open import DPPL.Regularity
open import DPPL.Syntax R
open import DPPL.Typing R

open import Lib.Syntax.Env

open import Order.Lattice

open SyntaxVars
open TypingVars
open is-lattice Reg↓-lattice

∩ᵗ-<:-pres : T <: T' → c ∩ᵗ T <: c ∩ᵗ T'
∩ᵗ-<:-pres {c = c} (sreal {c = d} {c' = d'} H≤) = sreal (∩≤∩r {c} {d} {d'} H≤)
∩ᵗ-<:-pres (stup H<:)                           = stup λ i → ∩ᵗ-<:-pres (H<: i)
∩ᵗ-<:-pres {c = c} (sarr {c = d} {c' = d'} H<: H<:' H≤c H≤e) =
  sarr H<: H<:' (∩≤∩r {c} {d} {d'} H≤c) H≤e
∩ᵗ-<:-pres (sdist H<:) = sdist H<:
