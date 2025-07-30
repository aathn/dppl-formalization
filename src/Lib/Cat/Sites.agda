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

-- The notion of flatness which forms a principal part of the
-- definition is somewhat subtle, see references below.
--
-- golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html
-- https://ncatlab.org/nlab/show/flat+functor#SiteValuedFunctors
-- https://arxiv.org/pdf/1203.4318


module _ {oc ℓc oe ℓe}
  {C : Precategory oc ℓc}
  {E : Precategory oe ℓe}
  (F : Functor C E)
  where
  private
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

  is-flat : ∀ {ℓE} (J : Coverage E ℓE) (oj ℓj : Level) → Type _
  is-flat J oj ℓj =
    ∀ {I : Precategory oj ℓj} (D : Functor I C) (D-fin : is-finite-precategory I) {U : ⌞ E ⌟}
    → (T : Const U => F F∘ D) → ∃[ S ∈ J ʻ U ] ⟦ S ⟧ ⊆ cone-sieve D T
    where open Coverage J

  map-sieve : {u : ⌞ C ⌟} → Sieve C u → Sieve E (F.₀ u)
  map-sieve {u} c .arrows {V} g =
    elΩ $ Σ[ w ∈ C ] Σ[ f ∈ C.Hom w u ] Σ[ h ∈ E.Hom V (F.₀ w) ] f ∈ c × F.₁ f E.∘ h ≡ g
  map-sieve c .closed hf g = do
    w , f' , h , hf , p ← hf
    pure (w , f' , h E.∘ g , hf , pulll p)
    where open Reasoning E

  preserves-covers : ∀ {ℓC ℓE} (JC : Coverage C ℓC) (JE : Coverage E ℓE) → Type _
  preserves-covers JC JE =
    ∀ {u} (c : JC ʻ u) → ∃[ S ∈ JE ʻ F.₀ u ] ⟦ S ⟧ ⊆ map-sieve ⟦ c ⟧ where
    open Coverage JC
    open Coverage JE

  is-site-morphism : ∀ {ℓC ℓE} (JC : Coverage C ℓC) (JE : Coverage E ℓE) (oj ℓj : Level) → Type _
  is-site-morphism JC JE oj ℓj = is-flat JE oj ℓj × preserves-covers JC JE

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
      : ∀ {ℓE} (J : Coverage E ℓE) → is-subcanonical E J → is-flat J lzero lzero → is-lex F
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

module _ {oc ℓc od ℓd oe ℓe}
  {C : Precategory oc ℓc}
  {D : Precategory od ℓd}
  {E : Precategory oe ℓe}
  (F : Functor C D)
  (G : Functor D E)
  where
  private
    module D = Precategory D
    module E = Precategory E
    module F = Functor F
    module G = Functor G

  is-flat-compose
    : ∀ {ℓD ℓE oj ℓj} {JD : Coverage D ℓD} {JE : Coverage E ℓE}
    → is-flat F JD oj ℓj → is-flat G JE oj ℓj
    → is-flat (G F∘ F) JE oj ℓj
  is-flat-compose F-flat G-flat Diagram fin T = do
    (c , Hc) ← G-flat (F F∘ Diagram) fin (assoc ∘nt T)
    pure (c , λ h hh → do
      (w , S , g , p) ← Hc h hh
      case F-flat Diagram fin S of λ c' Hc' →
        pure {!!})
    where
    assoc = NT (λ _ → E.id) (λ _ _ _ → E.idl _ ∙ sym (E.idr _))

  preserves-covers-compose
    : ∀ {ℓC ℓD ℓE} {JC : Coverage C ℓC} {JD : Coverage D ℓD} {JE : Coverage E ℓE}
    → preserves-covers F JC JD → preserves-covers G JD JE
    → preserves-covers (G F∘ F) JC JE
  preserves-covers-compose F-pres G-pres c = do
    (F-cov , HF⊆) ← F-pres c
    (G-cov , HG⊆) ← G-pres F-cov
    pure (G-cov , λ g hg → do
      (w , f , h  , hf , p) ← HG⊆ g hg
      (w' , f' , h' , hf' , q) ← HF⊆ f hf
      let s = G.F₁ (F.₁ f') ∘ G.F₁ h' ∘ h ≡⟨ pulll $ sym (G.F-∘ (F.₁ f') h') ∙ ap G.₁ q ⟩
              G.F₁ f ∘ h                  ≡⟨ p ⟩
              g                           ∎
      pure (w' , f' , G.₁ h' E.∘ h , hf' , s))
   where open Reasoning E
