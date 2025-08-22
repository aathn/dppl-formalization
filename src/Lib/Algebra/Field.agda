module Lib.Algebra.Field where

open import 1Lab.Prelude hiding (_*_ ; _+_)

open import Algebra.Ring
open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
import Algebra.Ring.Reasoning as RR

record is-field {ℓ} {A : Type ℓ} (1f : A) (_*_ _+_ : A → A → A) : Type ℓ where
  field
    has-is-ring : is-ring 1f _*_ _+_

  open is-ring has-is-ring public renaming (0r to 0f)

  field
    *-commutes : ∀ {x y} → x * y ≡ y * x
    0≠1        : 0f ≠ 1f
    _[_]⁻¹     : ∀ x → ¬ x ≠ 0f → Σ[ x' ∈ A ] x * x' ≡ 1f

  ring : Σ (Set ℓ) λ X → Ring-on ∣ X ∣
  ring = el A has-is-set , record
    { 1r = 1f
    ; _*_ = _*_
    ; _+_ = _+_
    ; has-is-ring = has-is-ring
    }

  commutative-ring : Σ (Set ℓ) λ X → CRing-on ∣ X ∣
  commutative-ring = ring .fst , record
    { has-ring-on = ring .snd
    ; *-commutes = *-commutes
    }

record Field-on {ℓ} (A : Type ℓ) : Type ℓ where
  field
    1f : A
    _*_ _+_ : A → A → A
    has-is-field : is-field 1f _*_ _+_

  open is-field has-is-field public
  infixl 25 _*_
  infixl 20 _+_

module Properties {ℓ} {A : Type ℓ} (F : Field-on A) where
  open Field-on F
  module R = RR ring
  -- open import Algebra.Properties.Ring ring
  -- open import Algebra.Solver.CommutativeMonoid *-commutativeMonoid
  -- open import Relation.Binary.Reasoning.Setoid setoid

  [-1]²≡1 : (- 1f) * (- 1f) ≡ 1f
  [-1]²≡1 =
    (- 1f) * (- 1f) ≡⟨ R.*-negatel ⟩
    - (1f * (- 1f)) ≡⟨ ap -_ *-idl ⟩
    - (- 1f)        ≡⟨ inv-inv ⟩
    1f              ∎

  [-a]²≡a² : ∀ a → (- a) * (- a) ≡ a * a
  [-a]²≡a² a =
    (- a) * (- a)               ≡⟨ {!!} ⟩ -- *-cong (sym $ -1*x≈-x _) (sym $ -1*x≈-x _) ⟩
    ((- 1f) * a) * ((- 1f) * a) ≡⟨ {!!} ⟩ -- solve 2 (λ x y → (x ⊕ y) ⊕ (x ⊕ y) ⊜ (x ⊕ x) ⊕ (y ⊕ y)) refl _ _ ⟩
--     (- 1# * - 1#) * (a * a) ≈⟨ *-congʳ [-1]²≈1 ⟩
--     1# * (a * a)            ≈⟨ *-identityˡ _ ⟩
    a * a                   ∎

--   a≲0→0≲-a : ∀ a → a ≲ 0# → 0# ≲ (- a)
--   a≲0→0≲-a a H≲ =
--     ≲-respˡ-≈ (-‿inverseʳ a) $
--     ≲-respʳ-≈ (+-identityˡ (- a)) $
--     ≲+-compat a 0# (- a) H≲

--   0≲a² : ∀ a → 0# ≲ a * a
--   0≲a² a with total 0# a
--   ... | ι₁ H≲ = ≲*-compat _ _ H≲ H≲
--   ... | ι₂ H≲ = ≲-respʳ-≈ ([-a]²≈a² _) $ ≲*-compat _ _ H≲′ H≲′
--     where H≲′ = a≲0→0≲-a _ H≲

--   0≲1 : 0# ≲ 1#
--   0≲1 = ≲-respʳ-≈ (*-identityʳ _) $ 0≲a² _
