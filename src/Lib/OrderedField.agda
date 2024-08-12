module Lib.OrderedField where

open import Lib.Prelude hiding (_+_ ; refl ; trans ; sym)

open import Algebra using (Op₁ ; Op₂ ; CommutativeRing)
open import Level using (suc ; _⊔_)
open import Relation.Binary using (Rel)

module _ {a ℓ ℓ′} {A : Set a} (_≈_ : Rel A ℓ) where
  open import Algebra.Definitions _≈_ using (RightInvertible)
  open import Algebra.Structures _≈_ using (IsCommutativeRing)
  open import Relation.Binary.Structures _≈_ using (IsTotalOrder)
  record IsField (+ * : Op₂ A) (- : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
    field
      isCommutativeRing : IsCommutativeRing + * - 0# 1#
      0≉1    : ¬ 0# ≈ 1#
      _[_]⁻¹ : ∀ (x : A) → ¬ x ≈ 0# → RightInvertible 1# * x

    open IsCommutativeRing isCommutativeRing public

  record IsOrderedField
    (_≲_ : Rel A ℓ′) (_+_ _*_ : Op₂ A) (- : Op₁ A) (0# 1# : A)
    : Set (a ⊔ ℓ ⊔ ℓ′)
    where
    field
      isField : IsField _+_ _*_ - 0# 1#
      isTotalOrder : IsTotalOrder _≲_
      ≲+-compat : ∀ (a b c : A) → a ≲ b → (a + c) ≲ (b + c)
      ≲*-compat : ∀ (a b : A) → 0# ≲ a → 0# ≲ b → 0# ≲ (a * b)

    open IsField isField public
    open IsTotalOrder isTotalOrder public
      renaming (refl to ≲-refl ; reflexive to ≲-reflexive
               ; trans to ≲-trans)

record OrderedField c ℓ ℓ′ : Set (suc (c ⊔ ℓ ⊔ ℓ′)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  infix  4 _≲_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ
    _≲_            : Rel Carrier ℓ′
    _+_            : Op₂ Carrier
    _*_            : Op₂ Carrier
    -_             : Op₁ Carrier
    0#             : Carrier
    1#             : Carrier
    isOrderedField : IsOrderedField _≈_ _≲_ _+_ _*_ -_ 0# 1#

  open IsOrderedField isOrderedField public

  commutativeRing : CommutativeRing _ _
  commutativeRing = record { isCommutativeRing = isCommutativeRing }

  open CommutativeRing commutativeRing public
    using (_≉_; rawRing; +-invertibleMagma
    ; +-invertibleUnitalMagma ; +-group; +-abelianGroup ; +-rawMagma; +-magma
    ; +-unitalMagma ; +-commutativeMagma ; +-semigroup; +-commutativeSemigroup
    ; *-rawMagma; *-magma; *-commutativeMagma; *-semigroup
    ; *-commutativeSemigroup ; +-rawMonoid; +-monoid
    ; +-commutativeMonoid ; *-rawMonoid; *-monoid
    ; *-commutativeMonoid ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero; semiring
    ; commutativeSemiringWithoutOne; ring ; commutativeSemiring
    )

module Properties {c ℓ ℓ′} (F : OrderedField c ℓ ℓ′) where
  open OrderedField F
  open import Algebra.Properties.Ring
  open import Algebra.Solver.CommutativeMonoid *-commutativeMonoid
  open import Relation.Binary.Reasoning.Setoid setoid

  a≲0→0≲-a : ∀ a → a ≲ 0# → 0# ≲ (- a)
  a≲0→0≲-a a H≲ =
    ≲-respˡ-≈ (-‿inverseʳ a) $
    ≲-respʳ-≈ (+-identityˡ (- a)) $
    ≲+-compat a 0# (- a) H≲

  [-1]²≈1 : - 1# * - 1# ≈ 1#
  [-1]²≈1 = begin
    - 1# * - 1#   ≈⟨ sym $ -‿distribˡ-* ring _ _ ⟩
    - (1# * - 1#) ≈⟨ -‿cong (*-identityˡ _) ⟩
    - (- 1#)      ≈⟨ -‿involutive ring _ ⟩
    1#            ∎

  [-a]²≈a² : ∀ a → - a * - a ≈ a * a
  [-a]²≈a² a = begin
    - a * - a               ≈⟨ *-cong (sym $ -1*x≈-x ring _) (sym $ -1*x≈-x ring _) ⟩
    (- 1# * a) * (- 1# * a) ≈⟨ solve 2 (λ x y → (x ⊕ y) ⊕ (x ⊕ y) ⊜ (x ⊕ x) ⊕ (y ⊕ y)) refl _ _ ⟩
    (- 1# * - 1#) * (a * a) ≈⟨ *-congʳ [-1]²≈1 ⟩
    1# * (a * a)            ≈⟨ *-identityˡ _ ⟩
    a * a                   ∎

  0≲a² : ∀ a → 0# ≲ a * a
  0≲a² a with total 0# a
  ... | ι₁ H≲ = ≲*-compat _ _ H≲ H≲
  ... | ι₂ H≲ = ≲-respʳ-≈ ([-a]²≈a² _) $ ≲*-compat _ _ H≲′ H≲′
    where H≲′ = a≲0→0≲-a _ H≲

  0≲1 : 0# ≲ 1#
  0≲1 = ≲-respʳ-≈ (*-identityʳ _) $ 0≲a² _
