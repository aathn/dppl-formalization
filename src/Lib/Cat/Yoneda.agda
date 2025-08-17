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
open import Cat.Instances.Comma
open import Cat.Instances.Shape.Terminal

import Cat.Reasoning as Cr
import Cat.Functor.Hom.Cocompletion as Cocompletion

open Functor
open _=>_ hiding (op)
open Cr._≅_

module YonedaLemma {κ o ℓ} (C : Precategory κ κ) (D : Precategory o ℓ) where

  yoneda-lemma : (F : ⌞ PSh κ C ⌟) → Hom-into (PSh κ C) F F∘ op (よ C) ≅ⁿ F
  yoneda-lemma P = to-natural-iso record
    { eta = λ _ → unyo P
    ; inv = λ _ → yo P
    ; eta∘inv = λ _ → funext $ equiv→unit (yo-is-equiv {C = C} P)
    ; inv∘eta = λ _ → funext $ equiv→counit (yo-is-equiv {C = C} P)
    ; natural = λ _ _ f → funext λ α →
      sym (α .is-natural _ _ f $ₚ id) ∙ ap (α .η _) id-comm-sym
    }
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

  private
    module C = Cr C
    module D = Cr D
    module PSh[C] = Cr (PSh κ C)

  module CC = Cocompletion C D D-cocomp

  -⊗⟨_⟩ : Functor C D → Functor (PSh κ C) D
  -⊗⟨ F ⟩ = Lan.Ext (CC.よ-extension F)

  Hom⟨_,-⟩ : Functor C D → Functor D (PSh κ C)
  Hom⟨ F ,-⟩ = precompose (op F) F∘ よ D

  module _ (F : Functor C D) where
    private
      T = -⊗⟨ F ⟩
      H = Hom⟨ F ,-⟩

      module F = Functor F
      module T = Functor T
      module H = Functor H

    -- We show the tensor-hom adjunction --- the main idea of the
    -- proof is that since the Yoneda extension is pointwise, it is
    -- reversed by the Yoneda embedding, which gives that for all x,
    -- Hom[ -⊗⟨ F ⟩ , x ] is a right extension to Hom⟨ F , x ⟩ along
    -- Yoneda.  But we already established above that right extension
    -- along Yoneda is given by the Yoneda embedding itself, and hence
    -- we get an isomorphism Hom[ -⊗⟨ F ⟩ , x ] ≅ Hom[ - , Hom⟨ F , x ⟩ ],
    -- which establishes the adjunction, provided we show naturality
    -- in x.

    tensor-is-ran-hom-into : (x : ⌞ D ⌟) → is-ran (op (よ C)) (H.₀ x) (Hom-into D x F∘ T.op) _
    tensor-is-ran-hom-into x = ran where
      eps = _

      -- This is the core part of the proof: since the tensor is a
      -- pointwise extension, it is reversed into a right extension by
      -- Hom-into.  However, we need to fiddle a bunch to work around
      -- the fact that C ^op ^op ≡ C is not a definitional equality.
      co-ran : is-ran (op (よ C)) (op (opFʳ (Hom-into D x) F∘ F)) (op (opFʳ (Hom-into D x) F∘ T)) eps
      co-ran =
        is-lan→is-co-ran (よ C) (opFʳ (Hom-into D x) F∘ F) $
          cocomplete→pointwise-lan (よ C) F D-cocomp x

      p : Sets κ ^op ^op ≡ Sets κ
      p = C^op^op≡C

      q : PathP (λ i → Functor (C ^op) (p i)) (op (opFʳ (Hom-into D x) F∘ F)) (H.₀ x)
      q = Functor-pathp
        (λ r i → (opFʳ (Hom-into D x) F∘ F) .F₀ (r i))
        (λ r i → (opFʳ (Hom-into D x) F∘ F) .F₁ (r i))

      r : PathP (λ i → Functor (PSh κ C ^op) (p i)) (op (opFʳ (Hom-into D x) F∘ T)) (Hom-into D x F∘ T.op)
      r = Functor-pathp
        (λ r i → (opFʳ (Hom-into D x) F∘ T) .F₀ (r i))
        (λ r i → (opFʳ (Hom-into D x) F∘ T) .F₁ (r i))

      z : I → Type _
      z i = r i F∘ op (よ C) => q i

      ran : is-ran (op (よ C)) (H.₀ x) (Hom-into D x F∘ T.op) _
      ran = transport (λ i → is-ran (op (よ C)) (q i) (r i) (coe0→i z i eps)) co-ran

    opaque
      tensor-hom-iso-into
        : (x : ⌞ D ⌟) → Hom-into D x F∘ T.op ≅ⁿ Hom-into (PSh κ C) (H.₀ x)
      tensor-hom-iso-into x =
        Ran-unique.unique (tensor-is-ran-hom-into x) (is-ran-hom-into (H.₀ x))
        where open YonedaLemma C D

    private
      L-adj : ∀ {x y} → D.Hom (T.op .F₀ x) y → PSh[C].Hom x (H.₀ y)
      L-adj {x} {y} = tensor-hom-iso-into y .to .η x

    module _ where opaque
      unfolding tensor-hom-iso-into
      open D

      -- Showing that the established equivalence is natural in x is
      -- in principle a straightforward unrolling of the definitions,
      -- but we need to wrestle with type inference and transports to
      -- make the proof go through.

      private
        ↓Dia : (A : PSh[C].Ob) → Functor (よ C ↘ A) D
        ↓Dia A = F F∘ Dom (よ C) (!Const A)

        module ↓colim (A : PSh[C].Ob) = Colimit (D-cocomp (↓Dia A))

        p0 : ∀ {ℓ} {A : Type ℓ} → A → I → A
        p0 {A = A} x i = transp (λ _ → A) i x

        p1 : ∀ {ℓ} {A : Type ℓ} → A → I → A
        p1 {A = A} x i = transp (λ _ → A) (∂ i) x

        p2 : C.Ob → I → Ob
        p2 U i = F.₀ (p1 (p0 U i) i)

        p3 : C.Ob → I → Ob
        p3 U i = ↓colim.coapex (p1 (よ₀ C (p0 U (~ i))) (~ i))

      tensor-hom-iso-natural : hom-iso-natural {L = T} {H} L-adj
      tensor-hom-iso-natural {a = a} {b} {c} {d} g h s = ext λ U t →
        L-adj (g ∘ s ∘ T.₁ h) .η U t   ≡⟨ ap (λ f → L-adj f .η U t) (assoc _ _ _) ⟩
        L-adj ((g ∘ s) ∘ T.₁ h) .η U t ≡⟨ tensor-hom-iso-into _ .to .is-natural _ _ h $ₚ (g ∘ s) ηₚ _ $ₚ _ ⟩
        L-adj (g ∘ s) .η U (h .η U t)  ≡⟨ lemma (g ∘ s) U t ⟩
        _                              ≡⟨ sym (pulll (pulll (assoc _ _ _))) ⟩∘⟨refl ⟩
        _                              ≡⟨ pullr (sym (lemma s U t)) ⟩
        g ∘ L-adj s .η U (h .η U t)    ∎
        where
        lemma
          : ∀ {z} (s : Hom (T.₀ d) z) U t
          → L-adj s .η U (h .η U t) ≡
             (((s ∘ unmake-colimit.hom (↓colim.has-colimit (よ₀ C U))
                      (λ j → is-colimit.ψ (↓colim.has-colimit d)
                               (↓obj (yo d (h .η U t) ∘nt ↓Obj.map j)))
                      (λ f → is-colimit.commutes (↓colim.has-colimit d)
                               (↓hom (PSh[C].pullr (↓Hom.com f) ∙∙
                                      PSh[C].elim-inner refl ∙∙
                                      sym (ext λ _ _ → refl))))) ∘
               path→iso {C = D} (λ i → p3 U i) .from) ∘
               ↓colim.cocone (よ₀ C (p0 U i0)) .η (↓obj idnt)) ∘
             path→iso {C = D} (λ i → p2 U i) .from
        lemma _ _ _ =
          Hom-transport D _ refl _ ∙ eliml (transport-refl id) ∙
          (Hom-transport D _ refl _ ∙ eliml (transport-refl id) ⟩∘⟨refl ⟩∘⟨refl)

    Tensor⊣Hom : -⊗⟨ F ⟩ ⊣ Hom⟨ F ,-⟩
    Tensor⊣Hom =
      hom-iso→adjoints L-adj
        (λ {x} {y} → is-iso→is-equiv $ iso
          (tensor-hom-iso-into y .from .η x)
          (tensor-hom-iso-into y .inverses .invl ηₚ x $ₚ_)
          (tensor-hom-iso-into y .inverses .invr ηₚ x $ₚ_))
        tensor-hom-iso-natural
      where open Cr.Inverses
