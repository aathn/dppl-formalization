module Lib.Vector where

open import 1Lab.Prelude

open import Data.Fin.Base using (Fin)

Vector : {l : Level} → Type l → Nat → Type l
Vector A n = Fin n → A

----------------------------------------------------------------------
-- Arrays
----------------------------------------------------------------------
record Array {l : Level}(A : Type l) : Type l where
  constructor mkArray
  field
    length : Nat
    index  : Vector A length

open Array public
