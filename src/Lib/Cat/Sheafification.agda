module Lib.Cat.Sheafification where

open import Cat.Prelude
open import Cat.Site.Base
open import Cat.Site.Sheafification

module _ {o ℓ ℓc ℓs} {C : Precategory o ℓ} {J : Coverage C ℓc} {A : Functor (C ^op) (Sets ℓs)} where
  open Precategory C
  open Coverage J
  open Sheafification J A

  private
    module A = Functor A
    -- variable
    --   U V W : ⌞ C ⌟
    --   f g h : Hom U V

    -- → (pmap-id : ∀ {U} (z : Sheafify₀ U) → P (map id z) z (map-id z))
    -- → (pmap-∘
    --     : ∀ {U V W} (f : Hom W V) (g : Hom V U) (z : Sheafify₀ U)
    --     → P (map (g ∘ f) z) (map f (map g z)) (map-∘ z))
    -- → (pinc-natural
    --     : ∀ {U V} (f : Hom V U) (z : A ʻ U)
    --     → P (inc (A ⟪ f ⟫ z)) (map f (inc z)) (inc-natural z))
    -- → (pglues
    --     : {U : ⌞ C ⌟} (c : J ʻ U) (p : pre.Parts C map (J .cover c))
    --     → (patch : pre.is-patch C map ⟦ c ⟧ p)
    --     → (Hpatch : ∀ {V W} (f : Hom V U) (hf : f ∈ c) (g : Hom W V) (hgf : f ∘ g ∈ c)
    --               → P (map g (p f hf)) (p (f ∘ g) hgf) (patch f hf g hgf))
    --     → ∀ {V} (f : Hom V U) (hf : f ∈ c)
    --     → P (map f (glue c p patch)) (p f hf) (Sheafification.glues c p patch f hf))

  Sheafify-elim-inc-path
    : ∀ {ℓp} (P : {U : ⌞ C ⌟} (z w : A ʻ U) → Sheafification.inc z ≡ inc w → Type ℓp)
    → (prefl : {U : ⌞ C ⌟} (z : A ʻ U) → P z z refl)
    → (psep
        : ∀ {U V} {f : Hom U V} (z w : A ʻ U) (c : J ʻ U)
        → (l : ∀ {V} (f : Hom V U) (hf : f ∈ c) → map f (inc z) ≡ map f (inc w))
        → (Hl : ∀ {V} (f : Hom V U) (hf : f ∈ c) → P (A ⟪ f ⟫ z) (A ⟪ f ⟫ w) (inc-natural z ∙ l f hf ∙ sym (inc-natural w)))
        → P z w (sep c l))
    → (psquash : {U : ⌞ C ⌟} (z w : A ʻ U) (p q : inc z ≡ inc w) → P z w p ≡ P z w q)
    → {U : ⌞ C ⌟} (z w : A ʻ U) (p : inc z ≡ inc w) → P z w p
  Sheafify-elim-inc-path P prefl psep psquash z w p = {!!}

  -- For separated presheaves, the unit of the sheafification
  -- adjunction is componentwise monic.  This appears as part of Lemma
  -- 7.49.3 in the Stacks project.
  -- https://stacks.math.columbia.edu/tag/00ZG.
  inc-inj : {U : ⌞ C ⌟} {x y : A ʻ U} → is-separated J A → Sheafification.inc x ≡ inc y → x ≡ y
  inc-inj {U} {x} {y} Hsep p = {!!}
    -- Sheafify-elim-inc-path (λ z w _ → z ≡ w)
    --   (λ z → refl)
    --   (λ z w c l Hl → Hsep c Hl)
    --   (λ _ _ _ _ → refl)
    --   x y p

   -- ap f p where
   --  f : Sheafify₀ U → A ʻ U
   --  f (inc x) = x
   --  f (map _ _) = x
   --  f (glue _ _ _) = x
   --  f (map-id z i) = {!!}
   --  f (map-∘ z i) = x
   --  f (inc-natural z i) = {!!}
   --  f (sep c l i) = {!!} -- ap f ? i
   --  f (glues c p g f₁ hf i) = {!!}
   --  f (squash x x₁ x₂ y i i₁) = {!!}
