module Lib.Concrete.Properties where

open import Lib.Prelude renaming (_∘_ to _∘ᶠ_) hiding (id)
open import Lib.Concrete.Concrete

open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
-- open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.CartesianClosed.Canonical
  using (module Equivalence) renaming (CartesianClosed to CCartesianClosed)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Complete.Finitely using (FinitelyComplete)
open import Categories.Category.Construction.Properties.Presheaves.Complete using (Presheaves-FinitelyComplete)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Object.Exponential using (Exponential)
open import Categories.Object.Terminal using (Terminal)

import Categories.Category.Construction.Properties.Presheaves.Cartesian as PreCart
import Categories.Category.Construction.Properties.Presheaves.CartesianClosed as PreCCC
import Categories.Morphism.Reasoning as MR

open import Function using (Func)

open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

open Func


module _ {o ℓ e i p : Level} {𝒞 : CCat o ℓ e} (S : CSite 𝒞 i p) (o′ e′ : Level) where
  open CCat 𝒞
  open CSite S
  open CSheaf

  -- CSheaves is complete, cocomplete, and (cartesian) closed, just
  -- like Presheaves.  Here, we only show what we need for our
  -- semantics: (co)cartesian structure, finite completeness, and
  -- cartesian closure.

  open PreCart.IsCartesian Cat o′ e′
  private
    module PreTerm = Terminal Presheaves-Cartesian.terminal
    module PreProd = BinaryProducts Presheaves-Cartesian.products

  CSheaves-Cartesian : Cartesian (CSheaves S o′ e′)
  CSheaves-Cartesian = record
    { terminal = record
      { ⊤ = record
        { Psh = PreTerm.⊤
        ; is-sheaf = λ _ p₁ _ → mkUnique tt (λ {V} Hf → tt) (λ x _ → tt)
        ; is-concrete = λ _ → tt
        }
      ; ⊤-is-terminal = record
        { ! = PreTerm.!
        ; !-unique = λ _ → tt
        }
      }
    ; products = record
      { product = λ {A B} →
        let module A = CSheaf A
            module B = CSheaf B
        in record
        { A×B = record
          { Psh = A.Psh PreProd.× B.Psh
          ; is-sheaf = λ {U R} HR p matching →
            let p₁ : A.Parts R
                p₁ = record { to = π₁ ∘ᶠ p .to ; cong = π₁ ∘ᶠ p .cong }
                s₁ : ∃! (A.₀ U) (A.is-section R p₁)
                s₁ = A.is-sheaf HR p₁ λ Hf Hgf → matching Hf Hgf .π₁
                p₂ : B.Parts R
                p₂ = record { to = π₂ ∘ᶠ p .to ; cong = π₂ ∘ᶠ p .cong }
                s₂ : ∃! (B.₀ U) (B.is-section R p₂)
                s₂ = B.is-sheaf HR p₂ λ Hf Hgf → matching Hf Hgf .π₂
            in
            mkUnique (s₁ .witness , s₂ .witness)
                     (λ Hf → s₁ .has-prop Hf , s₂ .has-prop Hf)
                     (λ (x₁ , x₂) Hx → s₁ .unique x₁ (π₁ ∘ᶠ Hx) ,
                                       s₂ .unique x₂ (π₂ ∘ᶠ Hx))
          ; is-concrete = λ z →
            A.is-concrete (λ {_} → z .π₁) , B.is-concrete (λ {_} → z .π₂)
          }
        ; π₁ = PreProd.π₁
        ; π₂ = PreProd.π₂
        ; ⟨_,_⟩ = PreProd.⟨_,_⟩
        ; project₁ = λ {_ h g} → PreProd.project₁ {h = h} {g}
        ; project₂ = λ {_ h g} → PreProd.project₂ {h = h} {g}
        ; unique = λ {_ h i j} → PreProd.unique {h = h} {i} {j}
        }
      }
    }

  CSheaves-Cocartesian : Cocartesian (CSheaves S o′ e′)
  CSheaves-Cocartesian = record
    { initial = record
      { ⊥ = record
        { Psh = {!!}
        ; is-sheaf = {!!}
        ; is-concrete = {!!}
        }
      ; ⊥-is-initial = {!!}
      }
    ; coproducts = {!!}
    }

module _ {o ℓ e i p : Level} {𝒞 : CCat o ℓ e} (S : CSite 𝒞 i p) (o′ e′ : Level) where
  open CCat 𝒞
  open CSite S

  private
    module PFC = FinitelyComplete (Presheaves-FinitelyComplete Cat ℓ₀ ℓ₀ ℓ₀ o′ e′)

  CSheaves-FinitelyComplete : FinitelyComplete (CSheaves S (o′ ⊔ e′) e′)
  CSheaves-FinitelyComplete = record
    { cartesian = CSheaves-Cartesian S _ _
    ; equalizer = λ f g → record
      { obj = record
        { Psh = PFC.equalizer.obj f g
        ; is-sheaf = {!!}
        ; is-concrete = {!!}
        }
      ; arr = PFC.equalizer.arr f g
      ; isEqualizer = {!!} -- PFC.equalizer.isEqualizer f g
      }
    }

module _ {o : Level} {𝒞 : CCat o o o} (S : CSite 𝒞 o o) where
  open CCat 𝒞
  open CSite S
  open CSheaf

  open PreCCC.IsCartesianClosed Cat

  private
    module PCC = CCartesianClosed CanonicalCCC
    module Term = Terminal (Cartesian.terminal (CSheaves-Cartesian S o o))
    module Prod = BinaryProducts (Cartesian.products (CSheaves-Cartesian S o o))

  open NaturalTransformation
  open Setoid

  CSheaves-CCartesianClosed : CCartesianClosed (CSheaves S o o)
  CSheaves-CCartesianClosed = record
      { ⊤ = Term.⊤
      ; _×_ = Prod._×_
      ; ! = PCC.!
      ; π₁ = PCC.π₁
      ; π₂ = PCC.π₂
      ; ⟨_,_⟩ = PCC.⟨_,_⟩
      ; !-unique = PCC.!-unique
      ; π₁-comp = λ {_ _ f} {_ g} → PCC.π₁-comp {f = f} {g = g}
      ; π₂-comp = λ {_ _ f} {_ g} → PCC.π₂-comp {f = f} {g = g}
      ; ⟨,⟩-unique = λ {_ _ _ f g h} → PCC.⟨,⟩-unique {f = f} {g} {h}
      ; _^_ = λ B A →
      let module A = CSheaf A
          module B = CSheaf B
          module BA = Functor (B.Psh PCC.^ A.Psh)
      in record
        { Psh = B.Psh PCC.^ A.Psh
        ; is-sheaf = λ {U} {R} HR p matching →
          let p′ : ∀ {V} → A.F₀.Carrier V → (f : V ⇒ U) → Parts B (pullback f R)
              p′ e f = record
                { to = λ {_ g} Hg → p .to Hg .η _ .to (id , A.₁ g .to e)
                ; cong = λ {V} H≈ →
                  let module BV = B.F₀ V in
                  BV.trans (p .cong (∘-resp-≈ʳ H≈))
                           (p .to _ .η _ .cong (Equiv.refl , A.F-resp-≈ H≈))
                }
              matching′ : ∀ {V} (e : A.F₀.Carrier V) (f : V ⇒ U) → B.is-matching (pullback f R) (p′ e f)
              matching′ = {!!}

              sections : ∀ {V} (e : A.F₀.Carrier V) (f : V ⇒ U) → ∃! (B.₀ V) (B.is-section (pullback f R) (p′ e f))
              sections e f = B.is-sheaf (is-stable f HR) (p′ e f) (matching′ e f)

              s : BA.₀ U .Carrier
              s = record
                { η = λ V → record
                  { to = λ (f , e) → sections e f .witness
                  ; cong = λ {(f , e)} {(f′ , e′)} (H≈f , H≈e) →
                    sections e f .unique (sections e′ f′ .witness) λ {W g} Hg →
                      let Hg′ = R .resp-≈ (∘-resp-≈ˡ H≈f) Hg
                          open SetoidR (B.₀ W)
                      in begin
                        B.₁ g .to (sections e′ f′ .witness)    ≈⟨ sections e′ f′ .has-prop Hg′ ⟩
                        p .to Hg′ .η _ .to (id , A.₁ g .to e′) ≈⟨ p .to Hg′ .η _ .cong (Equiv.refl , A.₁ g .cong (A.F₀.sym V H≈e)) ⟩
                        p .to Hg′ .η _ .to (id , A.₁ g .to e)  ≈⟨ p .cong (Equiv.sym (∘-resp-≈ˡ H≈f)) ⟩
                        p .to Hg .η _ .to (id , A.₁ g .to e)   ∎
                  }
                ; commute = {!!}
                ; sym-commute = {!!}
                }
          in
          {!!}
        ; is-concrete = λ H≈ → {!!}
        }
      ; eval = PCC.eval
      ; curry = PCC.curry
      ; eval-comp = λ {_ _ _} {α} → PCC.eval-comp {f = α}
      ; curry-unique = λ {_ _ _} {α β} → PCC.curry-unique {f = α} {β}
      }
