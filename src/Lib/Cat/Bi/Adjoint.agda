open import Cat.Bi.Base
open import Cat.Prelude

module Lib.Cat.Bi.Adjoint {o h ℓ} (C : Prebicategory o h ℓ) where

open Prebicategory C

record _⊣_ {A B} (l : A ↦ B) (r : B ↦ A) : Type ℓ where
  no-eta-equality
  field
    η : id ⇒ r ⊗ l
    ε : l ⊗ r ⇒ id

    zig : λ← _ ∘ ε ◀ l ∘ α← _ ∘ l ▶ η ∘ ρ→ _ ≡ Hom.id
    zag : ρ← _ ∘ r ▶ ε ∘ α→ _ ∘ η ◀ r ∘ λ→ _ ≡ Hom.id

infixr 15 _⊣_
