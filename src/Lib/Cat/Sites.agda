module Lib.Cat.Sites where

open import Lib.Cat.Concrete
open import Lib.Cat.Bi

open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Diagram.Exponential
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Sieve
open import Cat.Finite
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Functor.Coherence
open import Cat.Functor.Compose
open import Cat.Functor.Constant
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Hom
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Kan.Base
open import Cat.Functor.Kan.Pointwise
open import Cat.Functor.Naturality
open import Cat.Instances.Functor.Limits
open import Cat.Instances.Product
open import Cat.Instances.Sets.Cocomplete
open import Cat.Instances.Sheaves
open import Cat.Instances.Elements
-- open import Cat.Instances.Shape.Initial
open import Cat.Site.Base
open import Cat.Site.Closure
open import Cat.Site.Instances.Canonical
open import Cat.Site.Sheafification
import Cat.Reasoning as Cr
import Cat.Functor.Reasoning.Presheaf as Pr
import Cat.Functor.Hom.Cocompletion as Cocompletion
import Cat.Instances.Presheaf.Limits as PL
import Cat.Instances.Presheaf.Exponentials as PE

open import Data.Fin.Finite

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
    module F = Functor F
    open Cr E

  -- open is-lex

  cone-sieve
    : ∀ {oj} {ℓj} {I : Precategory oj ℓj} (D : Functor I C) {U : ⌞ E ⌟}
    → (T : Const U => F F∘ D) → Sieve E U
  cone-sieve D T .arrows {V} h = elΩ $
    Σ[ w ∈ C ] Σ[ S ∈ Const w => D ] Σ[ g ∈ Hom V (F.₀ w) ]
      T ∘nt constⁿ h ≡ to-coneⁿ (nat-assoc-from (F ▸ S)) ∘nt constⁿ g
  cone-sieve D T .closed hh g = do
    w , S , g' , p ← hh
    pure (w , S , g' ∘ g , ext λ i → extendl (p ηₚ i))

  is-flat : ∀ {ℓE} (J : Coverage E ℓE) (oj ℓj : Level) → Type _
  is-flat J oj ℓj =
    ∀ {I : Precategory oj ℓj} (D : Functor I C) (D-fin : is-finite-precategory I) {U : ⌞ E ⌟}
    → (T : Const U => F F∘ D) → J ∋ cone-sieve D T

  map-sieve : {u : ⌞ C ⌟} → Sieve C u → Sieve E (F.₀ u)
  map-sieve {u} c .arrows {V} g = elΩ $
    Σ[ w ∈ C ] Σ[ f ∈ C.Hom w u ] Σ[ h ∈ Hom V (F.₀ w) ] f ∈ c × F.₁ f ∘ h ≡ g
  map-sieve c .closed hf g = do
    w , f' , h , hf , p ← hf
    pure (w , f' , h ∘ g , hf , pulll p)

  preserves-covers : ∀ {ℓC ℓE} (JC : Coverage C ℓC) (JE : Coverage E ℓE) → Type _
  preserves-covers JC JE =
    ∀ {u} {c : Sieve C u} → JC ∋ c → JE ∋ map-sieve c

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
  -- TODO: It's still not guaranteed that this is a sufficiently good
  -- definition of morphisms of concrete sites, since concretization
  -- generally does not preserve finite limits so that the usual
  -- recipe of left Kan extension + sheafification may not work;
  -- this requires further investigation.
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

module _ {oc ℓc ℓC} {C : Precategory oc ℓc} {J : Coverage C ℓC} where
  open Cr C
  Id-is-flat : ∀ {oj ℓj} → is-flat Id J oj ℓj
  Id-is-flat D fin {U} T =
    max (inc (U , nat-idl-to T , id , trivial!))

  Id-preserves-covers : preserves-covers Id J J
  Id-preserves-covers Hc =
    flip incl Hc λ {V} h hh → inc (V , h , id , hh , idr h)

  Id-is-site-morphism : ∀ {oj ℓj} → is-site-morphism Id J J oj ℓj
  Id-is-site-morphism = Id-is-flat , Id-preserves-covers

module _ {oc ℓc od ℓd oe ℓe}
  {C : Precategory oc ℓc}
  {D : Precategory od ℓd}
  {E : Precategory oe ℓe}
  (F : Functor C D)
  (G : Functor D E)
  where
  private
    module D = Precategory D
    module F = Functor F
    module G = Functor G
    open Cr E

  is-flat-compose
    : ∀ {ℓD ℓE oj ℓj} {JD : Coverage D ℓD} {JE : Coverage E ℓE}
    → is-flat F JD oj ℓj → is-site-morphism G JD JE oj ℓj
    → is-flat (G F∘ F) JE oj ℓj
  is-flat-compose {JE = JE} F-flat (G-flat , G-pres) Diagram fin T =
    local (G-flat (F F∘ Diagram) fin (nat-unassoc-to T)) λ f hf →
      case hf of λ w S g p →
        flip incl (pull g (G-pres (F-flat Diagram fin S))) λ j hj →
          case hj of λ z j' h w' S' g' p' q →
            pure (w' , S' , G.₁ g' ∘ h , ext λ i →
              T .η i ∘ f ∘ j                   ≡⟨ extendl $ p ηₚ i ⟩
              G.₁ (S .η i) ∘ g ∘ j             ≡⟨ refl⟩∘⟨ sym q ⟩
              G.₁ (S .η i) ∘ G.₁ j' ∘ h        ≡⟨ pulll $ sym (G.F-∘ _ _) ⟩
              G.₁ (S .η i D.∘ j') ∘ h          ≡⟨ ap G.₁ (p' ηₚ i) ⟩∘⟨refl ⟩
              G.₁ (F.₁ (S' .η i) D.∘ g') ∘ h   ≡⟨ ap (_∘ _) (G.F-∘ _ _) ∙ sym (assoc _ _ _) ⟩
              G.₁ (F.₁ (S' .η i)) ∘ G.₁ g' ∘ h ∎)
    where open _=>_

  preserves-covers-compose
    : ∀ {ℓC ℓD ℓE} {JC : Coverage C ℓC} {JD : Coverage D ℓD} {JE : Coverage E ℓE}
    → preserves-covers F JC JD → preserves-covers G JD JE
    → preserves-covers (G F∘ F) JC JE
  preserves-covers-compose F-pres G-pres Hc =
    flip incl (G-pres (F-pres Hc)) λ g hg →
      case hg of λ w f h w' f' h' hf p q →
        pure (w' , f' , G.₁ h' ∘ h , hf ,
          (G.₁ (F.₁ f') ∘ G.₁ h' ∘ h ≡⟨ pulll $ sym (G.F-∘ _ _) ∙ ap G.₁ p ⟩
           G.₁ f ∘ h                 ≡⟨ q ⟩
           g                         ∎))

  is-site-morphism-compose
    : ∀ {ℓC ℓD ℓE oj ℓj} {JC : Coverage C ℓC} {JD : Coverage D ℓD} {JE : Coverage E ℓE}
    → is-site-morphism F JC JD oj ℓj → is-site-morphism G JD JE oj ℓj
    → is-site-morphism (G F∘ F) JC JE oj ℓj
  is-site-morphism-compose F-mor G-mor =
    is-flat-compose (F-mor .fst) G-mor ,
    preserves-covers-compose (F-mor .snd) (G-mor .snd)

Sites : ∀ o ℓ ℓc oj ℓj → Prebicategory (lsuc o ⊔ lsuc ℓ ⊔ lsuc ℓc) (lsuc (oj ⊔ ℓj) ⊔ o ⊔ ℓ ⊔ ℓc) (o ⊔ ℓ)
Sites o ℓ ℓc oj ℓj =
  Birestrict (Cat o ℓ)
    (λ C → Coverage C ℓc)
    (λ (_ , JC) (_ , JD) F → is-site-morphism F JC JD oj ℓj)
    Id-is-site-morphism
    (λ F G → is-site-morphism-compose F G)


--   -- A main result is that morphisms of sites induce geometric
--   -- morphisms of corresponding sheaf toposes.  We proceed to define
--   -- the components of these geometric morphisms, known as the direct
--   -- and inverse image functors.  We do so using tensor and hom
--   -- functors as in Mac Lane and Moerdijk, Chapter VII.

  -- -- The induced direct and inverse image functors are given by this
  -- -- adjunction together with composition with Yoneda.

  -- direct-image-presheaf : Functor C D → Functor (PSh κ D) (PSh κ C)
  -- direct-image-presheaf F = Hom⟨ よ D F∘ F ,-⟩

  -- inverse-image-presheaf : Functor C D → Functor (PSh κ C) (PSh κ D)
  -- inverse-image-presheaf F = -⊗⟨ よ D F∘ F ⟩

  -- inverse-image-map-sieve
  --   : {F : Functor C D} {U : ⌞ C ⌟} {S : Sieve C U}
  --   → inverse-image-presheaf F .F₀ (to-presheaf S) ≅ⁿ to-presheaf (map-sieve F S)
  -- inverse-image-map-sieve {F} {U} {S} = to-natural-iso ni where
  --   ni : make-natural-iso (inverse-image-presheaf F .F₀ (to-presheaf S)) (to-presheaf (map-sieve F S))
  --   ni .eta V x = {!!} , {!!}
  --   ni .inv V (f , hf) = {!!}
  --   ni .eta∘inv = {!!}
  --   ni .inv∘eta = {!!}
  --   ni .natural = {!!}

  -- -- module _
  -- --   (JC : Coverage C κ)
  -- --   (JD : Coverage D κ)
  -- --   where
  -- --   open Coverage JC using (Sem-covers)

  -- --   is-cont : Functor C (PSh κ D) → Type (lsuc κ)
  -- --   is-cont F = ∀ {U} (S : JC ʻ U) →
  -- --     is-colimit _ (F .F₀ U) (to-coconeⁿ (nat-assoc-to (F ▸ sieve→cocone C ⟦ S ⟧)))

  -- --   nat-eq-is-sheaf
  -- --     : (F : Functor (C ^op) (Sets κ))
  -- --     → ∀ {U} (S : Sieve C U) → (to-presheaf S => F) ≃ (よ₀ C U => F) → is-sheaf₁ F S
  -- --   nat-eq-is-sheaf = {!!}

  -- --   is-cont-sheaf
  -- --     : {F : Functor C (PSh κ D)} {A : Functor (D ^op) (Sets κ)}
  -- --     → is-cont F → is-sheaf JC (Hom⟨ F ,-⟩ .F₀ A)
  -- --   is-cont-sheaf {F} {A} F-cont = from-is-sheaf₁ λ S →
  -- --     nat-eq-is-sheaf (Hom⟨ F ,-⟩ .F₀ A) ⟦ S ⟧ (nat-eq S)
  -- --     where
  -- --     module F-colim {U : ⌞ C ⌟} (S : JC ʻ U) = is-colimit (F-cont S)
  -- --     -- to-presheaf ⟦ S ⟧ => Hom⟨ F ,-⟩ .F₀ A        ≈
  -- --     -- -⊗⟨ よ D F∘ F ⟩ .F₀ (to-presheaf ⟦ S ⟧) => A ≈
  -- --     -- to-presheaf (map-sieve F ⟦ S ⟧) => A         ≈
  -- --     -- よ D (F U) => A                              ≈
  -- --     -- -⊗⟨ よ D F∘ F ⟩ .F₀ (よ C U) => A            ≈
  -- --     -- よ C U => Hom⟨ F ,-⟩ .F₀ A
  -- --     nat-eq : ∀ {U} (S : JC ʻ U) → (to-presheaf ⟦ S ⟧ => F₀ Hom⟨ F ,-⟩ A) ≃ (よ₀ C U => Hom⟨ F ,-⟩ .F₀ A)
  -- --     nat-eq S = {!!}

  -- -- module _
  -- --   (JC : Coverage C κ)
  -- --   (JD : Coverage D κ)
  -- --   (F-pres : preserves-covers F JC JD)
  -- --   where

  -- --   direct-image-sheaf : Functor (Sheaves JD κ) (Sheaves JC κ)
  -- --   direct-image-sheaf .F₀ (A , shf) = direct-image-presheaf .F₀ A , {!!} where
  -- --     module shf = sat shf
  -- --     module A = Pr A
  -- --     open Coverage JC
  -- --     sep' : is-separated JC (A F∘ F.op)
  -- --     sep' S {x} {y} p = shf.separate (F-pres (inc S)) λ g hg →
  -- --       case hg of λ w f h hf q →
  -- --         A ⟪ g ⟫ x               ≡⟨ A.expand (sym q) ⟩
  -- --         A ⟪ h ⟫ (A ⟪ F.₁ f ⟫ x) ≡⟨ A.ap (p f hf) ⟩
  -- --         A ⟪ h ⟫ (A ⟪ F.₁ f ⟫ y) ≡⟨ A.collapse q ⟩
  -- --         A ⟪ g ⟫ y               ∎
  -- --   direct-image-sheaf .F₁   = direct-image-presheaf .F₁
  -- --   direct-image-sheaf .F-id = direct-image-presheaf .F-id
  -- --   direct-image-sheaf .F-∘  = direct-image-presheaf .F-∘
