open import Lib.Reals

module Properties.Syntax (R : Reals₀) where

open import Syntax R

open import Lib.Prelude
open import Lib.FunExt
open import Lib.Util

open import Data.Fin.Instances using (Fin-≡-isDecEquivalence)

deceqType : (T₁ T₂ : Type) → Dec (T₁ ≡ T₂)
deceqType (treal c) (treal d) with c ≐ d
... | equ   = equ
... | neq p = neq λ {refl → p refl}
deceqType (T₁ ⇒[ e ] T₃) (T₂ ⇒[ f ] T₄)
  with deceqType T₁ T₂ | e ≐ f | deceqType T₃ T₄
... | equ | equ | equ = equ
... | neq p | _ | _ = neq λ {refl → p refl}
... | _ | neq p | _ = neq λ {refl → p refl}
... | _ | _ | neq p = neq λ {refl → p refl}
deceqType (ttup n₁ Ts₁) (ttup n₂ Ts₂) with n₁ ≐ n₂
... | neq p = neq λ {refl → p refl}
... | equ = case (all-⊎ Heq) λ where
             (ι₁ p) → yes (ap (ttup _) $ funext p)
             (ι₂ (_ , q , _)) → no λ {refl → q refl}
  where Heq : ∀ i → Ts₁ i ≡ Ts₂ i ⊎ ¬ Ts₁ i ≡ Ts₂ i
        Heq i with deceqType (Ts₁ i) (Ts₂ i)
        ... | yes p = ι₁ p
        ... | no  q = ι₂ q
deceqType (tdist T₁) (tdist T₂) with deceqType T₁ T₂
... | equ = equ
... | neq p = neq λ {refl → p refl}

deceqType (treal _) (_ ⇒[ _ ] _)   = neq λ()
deceqType (treal _) (ttup _ _)     = neq λ()
deceqType (treal _) (tdist _)      = neq λ()
deceqType (_ ⇒[ _ ] _) (treal _)   = neq λ()
deceqType (_ ⇒[ _ ] _) (ttup _ _)  = neq λ()
deceqType (_ ⇒[ _ ] _) (tdist _)   = neq λ()
deceqType (ttup _ _) (treal _)     = neq λ()
deceqType (ttup _ _) (_ ⇒[ _ ] _)  = neq λ()
deceqType (ttup _ _) (tdist _)     = neq λ()
deceqType (tdist _) (treal _)      = neq λ()
deceqType (tdist _) (_ ⇒[ _ ] _)   = neq λ()
deceqType (tdist _) (ttup _ _)     = neq λ()

import Relation.Binary.PropositionalEquality.Properties as ≡

instance
  hasDecEqType : hasDecEq Type
  isEquivalence {{hasDecEqType}} = ≡.isEquivalence
  _≐_ {{hasDecEqType}} = deceqType
