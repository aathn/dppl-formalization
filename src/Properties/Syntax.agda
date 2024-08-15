open import Lib.Reals
module Properties.Syntax (R : Reals₀) where

open import Syntax R
open import Lib.Prelude
open import Lib.FunExt
import Relation.Binary.PropositionalEquality.Properties as ≡
open import Data.Vec.Functional.Properties
open import Data.Product
-- open import Relation.Binary

typeHasDecEq : hasDecEq Type
isEquivalence ⦃ typeHasDecEq ⦄ = ≡.isEquivalence
_≐_ ⦃ typeHasDecEq ⦄ (treal c₁) (treal c₂) with  c₁ ≐ c₂
... | equ = yes refl
... | neq p = no λ { refl → p refl}
_≐_ ⦃ typeHasDecEq ⦄ (treal x) (T₂ ⇒[ x₁ ] T₃) = no λ ()
_≐_ ⦃ typeHasDecEq ⦄ (treal x) (ttup x₁) = no λ ()
_≐_ ⦃ typeHasDecEq ⦄ (treal x) (tdist T₂) = no λ ()
_≐_ ⦃ typeHasDecEq ⦄ (_ ⇒[ _ ] T₃) (treal x₁) = no λ ()
_≐_ ⦃ typeHasDecEq ⦄ (T₁ ⇒[ e₁ ] T₃) (T₂ ⇒[ e₂ ] T₄) with e₁ ≐ e₂ | _≐_ ⦃ typeHasDecEq ⦄ T₁ T₂ | _≐_ ⦃ typeHasDecEq ⦄ T₃ T₄
... | equ | equ | equ = yes refl
... | neq p | _ | _ = no λ { refl → p refl }
... | _ | neq p | _ = no λ { refl → p refl }
... | _ | _ | neq p = no λ { refl → p refl }
_≐_ ⦃ typeHasDecEq ⦄ (T₁ ⇒[ x ] T₃) (ttup x₁) = {!!}
_≐_ ⦃ typeHasDecEq ⦄ (T₁ ⇒[ x ] T₃) (tdist T₂) = {!!}
_≐_ ⦃ typeHasDecEq ⦄ (ttup x) (treal x₁) = {!!}
_≐_ ⦃ typeHasDecEq ⦄ (ttup x) (T₂ ⇒[ x₁ ] T₃) = {!!}
_≐_ ⦃ typeHasDecEq ⦄ (ttup {₀} Ts₁) (ttup {₀} Ts₂) = yes (ap ttup (funext λ ()))
_≐_ ⦃ typeHasDecEq ⦄ (ttup {₀} Ts₁) (ttup {_+1 n₂} Ts₂) = no λ ()
_≐_ ⦃ typeHasDecEq ⦄ (ttup {_+1 n₁} Ts₁) (ttup {₀} Ts₂) = no λ ()
_≐_ ⦃ typeHasDecEq ⦄ (ttup {_+1 n₁} Ts₁) (ttup {_+1 n₂} Ts₂) with _≐_ ⦃ typeHasDecEq ⦄ (Ts₁ ₀) (Ts₂ ₀)
... | yes p = {!!}
... | no p = {!!}
_≐_ ⦃ typeHasDecEq ⦄ (ttup x) (tdist T₂) = {!!}
_≐_ ⦃ typeHasDecEq ⦄ (tdist T₁) T₂ = {!!}
