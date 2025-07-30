module Lib.Cat.Sites where

open import Lib.Cat.Concrete

open import Cat.Prelude
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Sieve
open import Cat.Finite
open import Cat.Functor.Base
open import Cat.Functor.Compose
open import Cat.Functor.Constant
open import Cat.Instances.Elements
open import Cat.Instances.Shape.Initial
open import Cat.Site.Base
open import Cat.Site.Instances.Canonical
import Cat.Reasoning as Reasoning

open import Data.Fin.Finite

open _=>_
open Functor

-- We define the notion of a site morphism and the bicategory of
-- sites.

-- First, we must define the notion of flatness which forms a
-- principal part of the definition.
--
-- golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html
-- https://ncatlab.org/nlab/show/flat+functor#SiteValuedFunctors
-- https://arxiv.org/pdf/1203.4318


module _ {oc ℓc oe ℓe}
  {C : Precategory oc ℓc}
  {E : Precategory oe ℓe}
  (F : Functor C E)
  where
  module C = Precategory C
  module E = Precategory E
  module F = Functor F

  open is-lex

  cone-sieve
    : ∀ {oj} {ℓj} {I : Precategory oj ℓj} (D : Functor I C) {U : ⌞ E ⌟}
    → (T : Const U => F F∘ D) → Sieve E U
  cone-sieve D T .arrows {V} h =
    elΩ $ Σ[ w ∈ C ] Σ[ S ∈ Const w => D ] Σ[ g ∈ E.Hom V (F.₀ w) ]
          T ∘nt constⁿ h ≡ (F ▸ S) ∘nt const' g
    where
    open Reasoning E
    const' : {w : ⌞ C ⌟} {V : ⌞ E ⌟} → E.Hom V (F.₀ w) → Const V => F F∘ Const w
    const' g .η _ = g
    const' g .is-natural _ _ _ = E.idr g ∙ introl F.F-id
  cone-sieve D T .closed hh g = do
    w , S , g' , p ← hh
    pure (w , S , g' ∘ g , ext λ i → extendl (p ηₚ i))
    where open Reasoning E

  is-flat : ∀ {ℓE} (oj ℓj : Level) (J : Coverage E ℓE) → Type _
  is-flat oj ℓj J =
    ∀ {I : Precategory oj ℓj} (D : Functor I C) (D-fin : is-finite-precategory I) {U : ⌞ E ⌟}
    → (T : Const U => F F∘ D) → ∃[ S ∈ J ʻ U ] ⟦ S ⟧ ⊆ cone-sieve D T
    where open Coverage J

  map-sieve : {u : ⌞ C ⌟} → Sieve C u → Sieve E (F.₀ u)
  map-sieve {u} c .arrows {V} g =
    elΩ $ Σ[ w ∈ C ] Σ[ f ∈ C.Hom w u ] Σ[ h ∈ E.Hom V (F.₀ w) ] F.₁ f E.∘ h ≡ g
  map-sieve c .closed hf g = do
    w , f' , h , p ← hf
    pure (w , f' , h E.∘ g , pulll p)
    where open Reasoning E

  preserves-covers : ∀ {ℓC ℓE} (JC : Coverage C ℓC) (JE : Coverage E ℓE) → Type _
  preserves-covers JC JE =
    ∀ {u} (c : JC ʻ u) → ∃[ S ∈ JE ʻ F.₀ u ] ⟦ S ⟧ ⊆ map-sieve ⟦ c ⟧ where
    open Coverage JC
    open Coverage JE

  is-site-morphism : ∀ {ℓC ℓE} (oj ℓj : Level) (JC : Coverage C ℓC) (JE : Coverage E ℓE) → Type _
  is-site-morphism oj ℓj JC JE = is-flat oj ℓj JE × preserves-covers JC JE

  -- A theorem about flatness is that when the codomain site E is
  -- subcanonical, flat functors preserve finite limits: this appears
  -- as Proposition 4.13 in Shulman (2012) and also in a comment to
  -- the blog post above.  In Shulman's paper the requirement is that
  -- the covering families of E are strong-epic, which is slightly
  -- weaker than subcanonicity.  In particular, subcanonicity is
  -- equivalent to covering families being *effective-epic* (see
  -- Cat.Site.Instances.Canonical), which implies being strong epic
  -- (definition 2.22 in Shulman).
  --
  -- This means that if we restrict our attention to subcanonical
  -- sites, the standard notion of site morphism automatically
  -- preserves concrete structure, namely terminal objects.
  postulate
    -- TODO: We postulate this result for now, as showing the
    -- uniqueness part of the limit will require some additional
    -- lemmas on monicity-preservation (Lemma 4.12 in Shulman).
    subcanonical+flat→lex
      : ∀ {ℓE} (J : Coverage E ℓE) → is-subcanonical E J → is-flat lzero lzero J → is-lex F
  -- subcanonical+is-flat→is-lex J J-sub F-flat .pres-⊤ {⊤} ⊤-is-terminal U =
  --   let cone : Const {D = E} U => F F∘ ¡F
  --       cone = ¡nt
  --       flat-sieve = F-flat ¡F finite-cat cone
  --   in
  --   case flat-sieve of λ S H⊆ →
  --     let module colim = is-colimit (J-sub S E.id)
  --         open Element
  --         open Coverage J
  --         univ = colim.universal {F.₀ ⊤} λ j →
  --           let f , Hf = j .section
  --               Hflat = H⊆ f (subst (_∈ ⟦ S ⟧) (E.idl f) Hf)
  --           in
  --           {!!}
  --     in
  --     contr (univ {!!}) {!!}
  -- subcanonical+is-flat→is-lex J J-sub F-flat .pres-pullback = {!!}
