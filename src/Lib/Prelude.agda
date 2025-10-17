module Lib.Prelude where

open import 1Lab.Prelude public
  hiding (_≠_; _∉_)

open import Lib.Data.Dec public using (is-no ; _≠_ ; _∉_)
open import Lib.Data.Finset public using (module FinsetSyntax)
open import Lib.Data.List public using (module ListSyntax)
open import Lib.Data.Nat public using (module NatOrd)
open import Lib.Data.Vector public using (Vector ; Array ; module VectorSyntax)

open import Data.Bool.Base public using (if_then_else_)
open import Data.Dec.Base public using (Dec ; yes ; no ; _≡?_ ; Discrete ; is-yes ; ifᵈ_then_else_)
open import Data.Fin.Base public using (Fin ; fin ; fzero ; fsuc ; fin-view ; zero ; suc)
open import Data.Finset.Base public using (Finset ; Membership-Finset ; Dec-∈ᶠˢ)
open import Data.Irr public using (make-irr)
open import Data.List.Base public using (List)
open import Data.Nat.Base public using (Discrete-Nat)
open import Data.Sum.Base public using (_⊎_ ; inl ; inr)
open import Data.Sum.Properties public using (Discrete-⊎)
open import Data.Vec.Base public using (Vec ; lookup)

module VecSyntax where
  open import Data.Vec.Base public using ([] ; _∷_)
