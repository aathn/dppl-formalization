module Lib.Cat.Yoneda where

open import Cat.Prelude
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Adjoint
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Base
open import Cat.Functor.Coherence
open import Cat.Functor.Hom
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Kan.Base
open import Cat.Functor.Kan.Duality
open import Cat.Functor.Kan.Pointwise
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Naturality
import Cat.Reasoning as Cr
import Cat.Functor.Hom.Cocompletion as Cocompletion

open Functor
open make-natural-iso
open _=>_ renaming (op to opⁿ)
open Cr._≅_

module YonedaLemma {κ o ℓ} (C : Precategory κ κ) (D : Precategory o ℓ) where

  yoneda-lemma : (F : ⌞ PSh κ C ⌟) → Hom-into (PSh κ C) F F∘ op (よ C) ≅ⁿ F
  yoneda-lemma P = to-natural-iso ni where
    ni : make-natural-iso (よ₀ (PSh κ C) P F∘ op (よ C)) P
    ni .eta _ = unyo P
    ni .inv _ = yo P
    ni .eta∘inv _ = funext $ equiv→unit (yo-is-equiv {C = C} P)
    ni .inv∘eta _ = funext $ equiv→counit (yo-is-equiv {C = C} P)
    ni .natural _ _ f = funext λ α →
      sym (α .is-natural _ _ f $ₚ id) ∙ ap (α .η _) id-comm-sym
      where open Cr C

  is-ran-hom-into : (F : ⌞ PSh κ C ⌟) → is-ran (op (よ C)) F (Hom-into (PSh κ C) F) (yoneda-lemma F .to)
  is-ran-hom-into F = ran where
    open is-ran
    open Cr C
    ran : is-ran (op (よ C)) F (Hom-into (PSh κ C) F) (yoneda-lemma F .to)
    ran .σ {M} α = yo-σ module ran where
      yo-σ : M => Hom-into (PSh κ C) F
      yo-σ .η X x = α ∘nt (yo M x ◂ op (よ C)) ∘nt yoneda-lemma X .from
      yo-σ .is-natural _ _ f = ext λ x U _ → ap (α .η U) $
        sym (M .F-∘ _ _ $ₚ _) ∙ ap (λ z → M .F₁ z x) yo-naturall
    ran .σ-comm {M} {β} = ext λ U x → ap (β .η U) $
      ap (λ z → M .F₁ z x) (ext λ _ → idl) ∙ M .F-id $ₚ x
    ran .σ-uniq {σ' = σ'} p = ap ran.yo-σ p ∙ ext λ X x U y →
      σ' .is-natural _ _ (yo {C = C} X y) $ₚ x ηₚ U $ₚ id ∙
      ap (σ' .η X x .η U) (X .F-id $ₚ y)


module Tensor {κ o}
  {C : Precategory κ κ}
  {D : Precategory o κ}
  (D-cocomp : is-cocomplete κ κ D)
  where

  module CC = Cocompletion C D D-cocomp

  -⊗⟨_⟩ : Functor C D → Functor (PSh κ C) D
  -⊗⟨ F ⟩ = Lan.Ext (CC.よ-extension F)

  Hom⟨_,-⟩ : Functor C D → Functor D (PSh κ C)
  Hom⟨ F ,-⟩ = precompose (op F) F∘ よ D

  module _ (F : Functor C D) where

    extend-is-ran-hom-into
      : (x : ⌞ D ⌟) → is-ran (op (よ C)) (Hom⟨ F ,-⟩ .F₀ x) (Hom-into D x F∘ op -⊗⟨ F ⟩) _
    extend-is-ran-hom-into x = ran where
      -- The core of this proof is just the fact that the Yoneda
      -- extension is a pointwise left Kan extension, which means it's
      -- reversed by the hom functor.  However, we need to fiddle a bit
      -- to get the "op"s to distribute like they should.
      co-ran : is-ran (op (よ C)) (op (op (Hom-into D x) F∘ F)) (op (op (Hom-into D x) F∘ -⊗⟨ F ⟩)) _
      co-ran =
        is-lan→is-co-ran (よ C) (op (Hom-into D x) F∘ F) $
          cocomplete→pointwise-lan (よ C) F D-cocomp x

      p : op (op (Hom-into D x) F∘ F) ≅ⁿ Hom⟨ F ,-⟩ .F₀ x
      p = to-natural-iso ni where
        ni : make-natural-iso _ _
        ni .eta _ x = x
        ni .inv _ x = x
        ni .eta∘inv _ = refl
        ni .inv∘eta _ = refl
        ni .natural _ _ _ = refl

      q : op (op (Hom-into D x) F∘ -⊗⟨ F ⟩) ≅ⁿ Hom-into D x F∘ op -⊗⟨ F ⟩
      q = to-natural-iso ni where
        ni : make-natural-iso _ _
        ni .eta _ x = x
        ni .inv _ x = x
        ni .eta∘inv _ = refl
        ni .inv∘eta _ = refl
        ni .natural _ _ _ = refl

      ran : is-ran (op (よ C)) (Hom⟨ F ,-⟩ .F₀ x) (Hom-into D x F∘ op -⊗⟨ F ⟩) _
      ran = natural-iso-ext→is-ran (natural-iso-of→is-ran co-ran p) q

    opaque
      extend-hom-iso-into
        : (x : ⌞ D ⌟) → Hom-into D x F∘ op -⊗⟨ F ⟩ ≅ⁿ Hom-into (PSh κ C) (Hom⟨ F ,-⟩ .F₀ x)
      extend-hom-iso-into x =
        Ran-unique.unique (extend-is-ran-hom-into x) (is-ran-hom-into (Hom⟨ F ,-⟩ .F₀ x))
        where open YonedaLemma C D

    private
      module PSh[C] = Cr (PSh κ C)
      module D = Cr D

      L-adj : ∀ {x y} → D.Hom (op -⊗⟨ F ⟩ .F₀ x) y → PSh[C].Hom x (Hom⟨ F ,-⟩ .F₀ y)
      L-adj {x} {y} = extend-hom-iso-into y .to .η x

    opaque
      unfolding extend-hom-iso-into

      extend-hom-iso-natural : hom-iso-natural {L = -⊗⟨ F ⟩} {Hom⟨ F ,-⟩} L-adj
      extend-hom-iso-natural g h a = ext λ U b →
        L-adj (g ∘ a ∘ -⊗⟨ F ⟩ .F₁ h) .η U b   ≡⟨ ap (λ f → L-adj f .η U b) (assoc _ _ _) ⟩
        L-adj ((g ∘ a) ∘ -⊗⟨ F ⟩ .F₁ h) .η U b ≡⟨ extend-hom-iso-into _ .to .is-natural _ _ h $ₚ (g ∘ a) ηₚ _ $ₚ _ ⟩
        L-adj (g ∘ a) .η U (h .η U b)          ≡⟨ pullr3 (assoc _ _ _) ⟩
        g ∘ L-adj a .η U (h .η U b)            ∎
        where open D

    Tensor⊣Hom : -⊗⟨ F ⟩ ⊣ Hom⟨ F ,-⟩
    Tensor⊣Hom =
      hom-iso→adjoints L-adj
        (λ {x} {y} → is-iso→is-equiv $ iso
          (extend-hom-iso-into y .from .η x)
          (extend-hom-iso-into y .inverses .invl ηₚ x $ₚ_)
          (extend-hom-iso-into y .inverses .invr ηₚ x $ₚ_))
        extend-hom-iso-natural
      where open Cr.Inverses
