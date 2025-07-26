module Lib.Cat.Concrete where

-- Our definitions of concrete categories, sites, and sheaves.

open import Cat.Prelude
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Terminal
open import Cat.Functor.Adjoint
open import Cat.Functor.Adjoint.Continuous
open import Cat.Functor.Adjoint.Monadic
open import Cat.Functor.Adjoint.Reflective
open import Cat.Functor.Equivalence
open import Cat.Functor.Equivalence.Properties
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Properties
open import Cat.Instances.Algebras.Limits
open import Cat.Instances.Functor
open import Cat.Instances.Sheaves
open import Cat.Site.Base
import Cat.Functor.Hom as Hom

record Conc-category {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  no-eta-equality
  open Precategory C
  open Hom C

  -- We use a more restrictive definition of concrete category than
  -- the standard presentation in that we require the forgetful
  -- functor to be representable by a terminal object (following
  -- Matache et al.).

  field
    terminal : Terminal C

  open Terminal terminal public renaming (top to ⋆ ; has⊤ to ⋆-is-terminal)

  field
    ⋆-hom-faithful : is-faithful Hom[ ⋆ ,-]

  open Functor

  ob∣_∣ : Ob → Type ℓ
  ob∣ c ∣ = Hom[ ⋆ ,-] ʻ c

  hom∣_∣ : {o₁ o₂ : ⌞ C ⌟} → Hom o₁ o₂ → ob∣ o₁ ∣ → ob∣ o₂ ∣
  hom∣_∣ = Hom[ ⋆ ,-] .F₁

module _ {o ℓ} {C : Precategory o ℓ} (Conc : Conc-category C) where
  record Conc-coverage {ℓc} (J : Coverage C ℓc) : Type (o ⊔ ℓ ⊔ ℓc) where
    no-eta-equality
    open Precategory C
    open Conc-category Conc
    open Coverage J

    field
      is-concrete :
        ∀ {U} {S : J ʻ U} (x : ob∣ U ∣)
        → ------------------------------------------
        ∃[ V ∈ C ] Σ[ f ∈ Hom V U ] Σ[ a ∈ ob∣ V ∣ ]
        f ∈ S × hom∣ f ∣ a ≡ x

module _ {o ℓ ℓc}
  {C : Precategory o ℓ}
  {Conc : Conc-category C}
  {J : Coverage C ℓc}
  (Conc-J : Conc-coverage Conc J)
  where

  open Precategory C
  open Conc-category Conc
  open Functor
  module JC = Conc-coverage Conc-J

  module _ {ℓs} (A : Functor (C ^op) (Sets ℓs)) where
    -- We take the "concrete sections" of A at U to be the maps
    -- g : ob∣ U ∣ → A ʻ ⋆
    -- given by the contravariant action of A on a morphism
    -- h : ob∣ U ∣ = Hom ⋆ U.
    -- In other words, given h which selects a point in U, we obtain a
    -- point in A ʻ ⋆ by restricting along h.
    conc-sections : (U : ⌞ C ⌟) → A ʻ U → ob∣ U ∣ → A ʻ ⋆
    conc-sections U AU f = A ⟪ f ⟫ AU

    -- A presheaf is *concrete* if the concrete sections are a
    -- faithful representation of the functor's action.
    is-concrete : Type (o ⊔ ℓ ⊔ ℓs)
    is-concrete = ∀ {U} → injective (conc-sections U)

  module _ ℓs where
    -- The category of concrete sheaves is the subcategory of sheaves
    -- which are concrete.
    ConcSheaves : Precategory (o ⊔ ℓ ⊔ ℓc ⊔ lsuc ℓs) (o ⊔ ℓ ⊔ ℓs)
    ConcSheaves = Restrict {C = Sheaves J ℓs} (is-concrete ⊙ fst)

    -- The evident forgetful functor from ConcSheaves to Sheaves
    forget-conc : Functor ConcSheaves (Sheaves J ℓs)
    forget-conc .F₀ = fst
    forget-conc .F₁ x = x
    forget-conc .F-id = refl
    forget-conc .F-∘ f g = refl

  module _ {ℓs} (A : Functor (C ^op) (Sets ℓs)) where
    -- Interestingly, the concrete sections can be used to define a
    -- concretized version of any presheaf.  The idea is to take the
    -- sections of the original presheaf A and identify any two
    -- sections giving rise to distinct concrete sections.
    -- Due to reasons explained in Data.Image, the resulting universe
    -- level is potentially raised by this construction.  This could
    -- be resolved using the Image type of that module, but for now
    -- this will work for us.
    concretize-presheaf : Functor (C ^op) (Sets (ℓ ⊔ ℓs))
    concretize-presheaf .F₀ U = el (image (conc-sections A U)) (hlevel 2)
    concretize-presheaf .F₁ f (fr , ∥r∥) =
      fr ⊙ hom∣ f ∣ ,
      ∥-∥-rec (hlevel 1)
        (λ (r , Hr) → inc (A ⟪ f ⟫ r , funext λ g → happly (sym (F-∘ A g f)) r ∙ happly Hr (f ∘ g)))
        ∥r∥
    concretize-presheaf .F-id =
      funext λ (fr , ∥r∥) → Σ-pathp.to
        (ap (fr ⊙_) (funext idl) , is-prop→pathp (λ i → hlevel 1) _ _)
    concretize-presheaf .F-∘ f g =
      funext λ (fr , ∥r∥) → Σ-pathp.to
        (ap (fr ⊙_) (funext (sym ⊙ assoc g f)) , is-prop→pathp (λ i → hlevel 1) _ _)

    -- We check that this indeed gives a concrete presheaf.  Let A' be
    -- the concretization of A. The statement to prove is that if x, y
    -- are two sections of A' (in other words, two concrete sections
    -- of A), and they map to the same concrete section under
    -- conc-sections, then they must be identical.  But note that the
    -- functorial action of A' on a morphism f : V → U takes a section
    -- x : ob∣ U ∣ → A ʻ ⋆ to λ h → x (f ∘ h), so that conc-sections
    -- on x is just the map f ↦ h ↦ x (f ∘ h).  Thus, the premise says
    -- that for any f and h, we have x (f ∘ h) ≡ y (f ∘ h).  To
    -- conclude that x ≡ y, we just instantiate h with id.
    concretize-is-concrete : is-concrete concretize-presheaf
    concretize-is-concrete {x = x , _} {y , _} p = Σ-pathp.to
      ( funext (λ g → ap x (sym (idr g)) ∙ happly (ap fst (happly p g)) id ∙ ap y (idr g))
      , is-prop→pathp (λ i → hlevel 1) _ _
      )

    -- The construction also lifts to the level of sheaves.  We begin
    -- by showing separation.  Note that this holds even if the
    -- original presheaf was not separated.  We need to show that two
    -- concrete sections x, y are equal if they agree on all
    -- restrictions of a cover.  This holds iff they map points
    -- g : Hom ⋆ U to equal elements of A ʻ ⋆.  The crucial
    -- observation is that the concreteness of J lets us find a map
    -- f : Hom V U in the cover and a point h of V, such that
    -- g ≡ f ∘ h.  In other words, g is a restriction of h, and
    -- x and y must agree on it.
    concretize-is-separated : is-separated J concretize-presheaf
    concretize-is-separated S {x , _} {y , _} p = Σ-pathp.to
      ( funext (λ g → ∥-∥-rec (A .F₀ ⋆ .is-tr _ _)
          (λ (V , f , h , Hf , Hg) →
            ap x (sym Hg) ∙ happly (ap fst (p f Hf)) h ∙ ap y Hg)
          (JC.is-concrete g))
      , is-prop→pathp (λ i → hlevel 1) _ _
      )

    concretize-is-sheaf : is-sheaf J A → is-sheaf J concretize-presheaf
    concretize-is-sheaf shf .whole S p =
      let foo = p .part
          -- bar = p .patch
      in {!!}
    concretize-is-sheaf shf .glues S p = {!!}
    concretize-is-sheaf shf .separate = concretize-is-separated

  -- Concretization provides a left adjoint to forget-conc.
  open Free-object

  make-free-conc : ∀ F → Free-object (forget-conc ℓ) F
  make-free-conc F = {!!}
  -- make-free-conc (F , shf) .free =
  --   (concretize-presheaf F , concretize-is-sheaf F shf) , concretize-is-concrete F
  -- make-free-conc F .unit = {!!}
  -- make-free-conc F .fold = {!!}
  -- make-free-conc F .commute = {!!}
  -- make-free-conc F .unique = {!!}

-- Next, we show the main properties of the category of concrete
-- sheaves.  We follow the conventions in Cat.Instances.Sheaves, using
-- homogeneous levels; the properties and proofs are the same as in
-- that module.

CSh[_,_]
  : ∀ {ℓ} {C : Precategory ℓ ℓ} (CC : Conc-category C)
    {J : Coverage C ℓ} (JC : Conc-coverage CC J) → Precategory (lsuc ℓ) ℓ
CSh[ CC , JC ] = ConcSheaves JC _

module _
  {ℓ} {C : Precategory ℓ ℓ} {CC : Conc-category C}
  {J : Coverage C ℓ} {JC : Conc-coverage CC J}
  where

  Concretization : Functor Sh[ C , J ] CSh[ CC , JC ]
  Concretization = free-objects→functor (make-free-conc JC)

  Concretization⊣ι : Concretization ⊣ forget-conc JC _
  Concretization⊣ι = free-objects→left-adjoint (make-free-conc JC)

  Concretization-is-reflective : is-reflective Concretization⊣ι
  Concretization-is-reflective = id-equiv

  Concretization-is-monadic : is-monadic Concretization⊣ι
  Concretization-is-monadic = is-reflective→is-monadic _ id-equiv

  CSh[]-is-complete : is-complete ℓ ℓ CSh[ CC , JC ]
  CSh[]-is-complete = equivalence→complete
    (is-equivalence.inverse-equivalence Concretization-is-monadic)
    (Eilenberg-Moore-is-complete _ Sh[]-is-complete)

  -- Todo: check if concretization is needed, or if the colimit of
  -- concrete sheaves in Sh is already guaranteed to be concrete.
  CSh[]-is-cocomplete : is-cocomplete ℓ ℓ CSh[ CC , JC ]
  CSh[]-is-cocomplete F = done where
    sh-colim : Colimit (forget-conc JC _ F∘ F)
    sh-colim = Sh[]-is-cocomplete _

    concretized : Colimit ((Concretization F∘ forget-conc JC _) F∘ F)
    concretized = subst Colimit F∘-assoc $
      left-adjoint-colimit Concretization⊣ι sh-colim

    done = natural-iso→colimit
      (F∘-iso-id-l (is-reflective→counit-iso Concretization⊣ι id-equiv))
      concretized

