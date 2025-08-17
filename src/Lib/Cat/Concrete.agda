module Lib.Cat.Concrete where

-- Our definitions of concrete sites and sheaves.

open import Lib.Cat.Sheafification

open import Cat.Prelude
open import Cat.Cartesian
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Exponential
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Limit.Product
open import Cat.Diagram.Product
open import Cat.Diagram.Sieve
open import Cat.Diagram.Terminal
open import Cat.Functor.Adjoint
open import Cat.Functor.Adjoint.Compose
open import Cat.Functor.Adjoint.Continuous
open import Cat.Functor.Adjoint.Monadic
open import Cat.Functor.Adjoint.Reflective
open import Cat.Functor.Equivalence
open import Cat.Functor.Equivalence.Properties
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Properties
open import Cat.Instances.Algebras.Limits
open import Cat.Instances.Functor
open import Cat.Instances.Functor.Limits
open import Cat.Instances.Presheaf.Limits
open import Cat.Instances.Presheaf.Exponentials
open import Cat.Instances.Sets.Complete
open import Cat.Instances.Sets.Cocomplete
open import Cat.Instances.Shape.Two
open import Cat.Instances.Sheaf.Exponentials
open import Cat.Instances.Sheaf.Limits
open import Cat.Site.Base
open import Cat.Site.Sheafification
import Cat.Functor.Hom as Hom
import Cat.Functor.Reasoning.Presheaf as PSh

open _=>_
open Functor

record Conc-coverage {o ℓ ℓc} {C : Precategory o ℓ} (J : Coverage C ℓc) : Type (o ⊔ ℓ ⊔ ℓc) where
  no-eta-equality
  open Precategory C
  open Hom C
  open Coverage J

  field
    terminal : Terminal C

  open Terminal terminal public renaming (top to ⋆ ; has⊤ to ⋆-is-terminal)

  field
    ⋆-hom-faithful : is-faithful Hom[ ⋆ ,-]

  ob∣_∣ : Ob → Type ℓ
  ob∣ c ∣ = Hom[ ⋆ ,-] ʻ c

  hom∣_∣ : {o₁ o₂ : ⌞ C ⌟} → Hom o₁ o₂ → ob∣ o₁ ∣ → ob∣ o₂ ∣
  hom∣_∣ = Hom[ ⋆ ,-] .F₁

  field
    -- We reformulate the usual joint surjectivity condition as
    -- below, stating that any covering sieve must contain all the
    -- points of U.
    covers-points : ∀ {U} (S : J ʻ U) (x : ob∣ U ∣) → x ∈ S

module _ {o ℓ ℓc}
  {C : Precategory o ℓ}
  {J : Coverage C ℓc}
  (JC : Conc-coverage J)
  where

  open Precategory C
  open Conc-coverage JC
  open Coverage J using (Sem-covers)

  private variable
    ℓs : Level
    A : Functor (C ^op) (Sets ℓs)

  module _ {ℓs} (A : Functor (C ^op) (Sets ℓs)) where
    -- We take the "concrete sections" of A at U to be the maps
    -- g : ob∣ U ∣ → A ʻ ⋆
    -- given by the contravariant action of A on a point
    -- h : ob∣ U ∣ = Hom ⋆ U.
    -- In other words, given h which selects a point in U, we obtain a
    -- point in A ʻ ⋆ by restricting along h.
    conc-sections : (U : ⌞ C ⌟) → A ʻ U → ob∣ U ∣ → A ʻ ⋆
    conc-sections U AU f = A ⟪ f ⟫ AU

    -- A presheaf is *concrete* if the concrete sections are a
    -- faithful representation of the functor's action.
    is-concrete : Type (o ⊔ ℓ ⊔ ℓs)
    is-concrete = ∀ {U} → injective (conc-sections U)

    -- A concrete presheaf is always separated.  This means that two
    -- concrete sections x , y which agree on all restrictions of a
    -- cover must be equal.  They are equal iff they map points
    -- g : ob∣ U ∣ to equal elements of A ʻ ⋆, but as noted, any cover
    -- can be restricted to its points.  Hence, x and y must agree.
    is-concrete→is-separated : is-concrete → is-separated J A
    is-concrete→is-separated conc S p =
      conc $ ext λ g → p g (covers-points S g)

  module Concretize {ℓs} (A : Functor (C ^op) (Sets ℓs)) where
    -- Interestingly, the concrete sections can be used to define a
    -- concretized version of any presheaf.  The idea is to take the
    -- sections of the original presheaf A and identify any two
    -- sections giving rise to distinct concrete sections.
    -- Due to reasons explained in Data.Image, the resulting universe
    -- level is potentially raised by this construction.  This could
    -- be resolved using the Image type of that module, but for now
    -- this will work for us.
    Concretize : Functor (C ^op) (Sets (ℓ ⊔ ℓs))
    Concretize .F₀ U = el (image (conc-sections A U)) (hlevel 2)
    Concretize .F₁ f (fr , ∥r∥) =
      fr ⊙ hom∣ f ∣ ,
      case ∥r∥ of λ r Hr →
        inc (A ⟪ f ⟫ r , ext λ g → sym (F-∘ A g f) $ₚ r ∙ Hr $ₚ (f ∘ g))
    Concretize .F-id = ext λ fr _ _ g → ap fr (idl g)
    Concretize .F-∘ f g = ext λ fr _ _ h → ap fr (sym (assoc g f h))

    -- If A is already concrete, concretization has no effect.
    is-concrete→Concretize-equiv : is-concrete A → ∀ {U} → A ʻ U ≃ image (conc-sections A U)
    is-concrete→Concretize-equiv conc {U} =
      image-inc (conc-sections A U) ,
      is-embedding→image-inc-is-equiv λ ca (x , p) (y , q) →
        Σ-pathp.to (conc (p ∙ sym q) , is-prop→pathp (λ i → hlevel 1) _ _)

  module _ {ℓs} (A : Functor (C ^op) (Sets ℓs)) where
    open Concretize

    -- We check that concretization indeed gives a concrete presheaf.
    -- Let A' be the concretization of A. The statement to prove is that
    -- if x , y are two sections of A' (in other words, two concrete
    -- sections of A), and they map to the same concrete section under
    -- conc-sections, then they must be identical.  But note that the
    -- functorial action of A' on a morphism f : V → U takes a section
    -- x : ob∣ U ∣ → A ʻ ⋆ to λ h → x (f ∘ h), so that conc-sections on
    -- x is just the map f ↦ h ↦ x (f ∘ h).  Thus, the premise says that
    -- for any f and h, we have x (f ∘ h) ≡ y (f ∘ h).  To conclude that
    -- x ≡ y, we just instantiate h with id.
    Concretize-is-concrete : is-concrete (Concretize A)
    Concretize-is-concrete {x = x , _} {y , _} p = ext λ g →
      ap x (sym (idr g)) ∙ ap fst (p $ₚ g) $ₚ id ∙ ap y (idr g)

    -- Sheafification also preserves concreteness.  This follows by a
    -- fairly direct argument, noting that equality on sheaves is a
    -- local property by definition (by separatedness), and using the
    -- fact that the unit map from a presheaf into its sheafification is
    -- injective if the presheaf is separated (or indeed concrete).
    -- This result appears as Lemma 5.22 in Baez and Hoffnung (2011).
    Sheafify-is-concrete : is-concrete A → is-concrete (Sheafification.Sheafify J A)
    Sheafify-is-concrete conc {x = x} {y} =
      Sheafify-elim-prop A (λ {U} x → ∀ y → cs U x ≡ cs U y → x ≡ y)
        (λ _ → hlevel 1)
        (λ x₀ y →
          Sheafify-elim-prop A (λ {U} y → ∀ x₀ → cs U (inc x₀) ≡ cs U y → inc x₀ ≡ y)
            (λ _ → hlevel 1)
            (λ y₀ x₀ p → ap inc $ conc $ ext λ g →
              inc-inj (is-concrete→is-separated A conc) (inc-natural x₀ ∙ p $ₚ g ∙ sym (inc-natural y₀)))
            (λ {U} S x p x₀ q → sep S λ f Hf →
              sym (inc-natural x₀) ∙ p f Hf (A ⟪ f ⟫ x₀) (ext λ g →
                ap (map g) (inc-natural x₀) ∙ sym (map-∘ _) ∙ q $ₚ (f ∘ g) ∙ map-∘ _))
            y x₀)
        (λ {U} S x p x₀ q → sep S λ f Hf →
          p f Hf (map f x₀) (funext λ g → sym (map-∘ _) ∙ q $ₚ (f ∘ g) ∙ map-∘ _))
        x y
      where
      open Sheafification J
      cs = conc-sections (Sheafify A)
      instance
        _ : ∀ {U} → H-Level (Sheafify₀ A U) 2
        _ = hlevel-instance squash

  -- The converse, that concretization preserves the sheaf property,
  -- appears impossible to prove.  Given a patch of concrete sections,
  -- each induced by some av : A ʻ V, we must make a global concrete
  -- section induced by some au : A ʻ U.  The obvious idea would be to
  -- glue the avs to obtain au, but the first issue is that we do not
  -- have a concrete choice of av for each section, only mere
  -- existence.  If we assume the axiom of choice, we can say that a
  -- choice of av : A ʻ V is given, but we get no guarantee that they
  -- agree on arbitrary restrictions.  The patch condition for the
  -- concretization only ensures that the induced concrete sections
  -- are compatible with restrictions, not that the av themselves are.
  -- Making that implication go through requires A to have been a
  -- concrete sheaf to begin with.
  --
  -- Luckily, we do not really need this property, since we can always
  -- apply sheafification as an extra step, preserving concreteness.
  --
  -- Concretize-is-sheaf : is-sheaf J A → is-sheaf J (Concretize A)

  module _ ℓs where
    -- The concrete presheaves as a full subcategory of presheaves
    ConcPSh : Precategory (o ⊔ ℓ ⊔ lsuc ℓs) (o ⊔ ℓ ⊔ ℓs)
    ConcPSh = Restrict {C = PSh ℓs C} is-concrete

    -- The forgetful functor from ConcPSh to PSh
    Forget-conc : Functor ConcPSh (PSh ℓs C)
    Forget-conc .F₀ = fst
    Forget-conc .F₁ x = x
    Forget-conc .F-id = refl
    Forget-conc .F-∘ f g = refl

    -- The concrete sheaves as a full subcategory of concrete presheaves
    ConcSh : Precategory (o ⊔ ℓ ⊔ ℓc ⊔ lsuc ℓs) (o ⊔ ℓ ⊔ ℓs)
    ConcSh = Restrict {C = ConcPSh} (is-sheaf J ⊙ fst)

    -- The forgetful functor from ConcSh to ConcPSh
    Forget-sheaf-to-conc : Functor ConcSh ConcPSh
    Forget-sheaf-to-conc .F₀ = fst
    Forget-sheaf-to-conc .F₁ x = x
    Forget-sheaf-to-conc .F-id = refl
    Forget-sheaf-to-conc .F-∘ f g = refl

    -- And their composite
    Forget-conc-sheaf : Functor ConcSh (PSh ℓs C)
    Forget-conc-sheaf = Forget-conc F∘ Forget-sheaf-to-conc


module Free {ℓ} {C : Precategory ℓ ℓ} {J : Coverage C ℓ} (JC : Conc-coverage J) where
  -- Concretization provides a left adjoint to the forget-conc functors.
  -- Regarding the universe level ℓ here, see the comment in
  -- Cat.Site.Sheafification.

  open Concretize JC
  open Sheafification J
  module FreeSheaf = Small J

  private variable A : Functor (C ^op) (Sets ℓ)

  unit : A => Concretize A
  unit {A = A} .η U au = image-inc (conc-sections JC A U) au
  unit {A = A} .is-natural x y f = ext λ au g → sym (F-∘ A g f) $ₚ au

  univ : (B : Functor (C ^op) (Sets ℓ)) → is-concrete JC B → A => B → Concretize A => B
  univ {A = A} B conc eta .η U (ca , im) =
    equiv→inverse (is-concrete→Concretize-equiv B conc .snd) im' where
    im' : image (conc-sections JC B U)
    im' = eta .η _ ⊙ ca , flip ∥-∥-map im λ (au , p) →
      eta .η _ au ,
      (conc-sections JC B U (eta .η _ au) ≡⟨ ext (λ g → sym (eta .is-natural _ _ g $ₚ au)) ⟩
       eta .η _ ⊙ conc-sections JC A U au ≡⟨ ap (eta .η _ ⊙_) p ⟩
       eta .η _ ⊙ ca                      ∎)
  univ {A = A} B conc eta .is-natural U V f = ext λ _ au _ →
    eta .is-natural _ _ f $ₚ au

  unique
    : (B : Functor (C ^op) (Sets ℓ)) (conc : is-concrete JC B) (eta : A => B) (eps : Concretize A => B)
    → (∀ U (au : A ʻ U) → eps .η U (image-inc (conc-sections JC A U) au) ≡ eta .η U au)
    → univ B conc eta ≡ eps
  unique {A = A} B conc eta eps comm = ext λ U ca au p →
    eta .η U au                            ≡˘⟨ comm U au ⟩
    eps .η U (conc-sections JC A U au , _) ≡⟨ ap (eps .η _) (Σ-pathp.to (p , is-prop→pathp (λ i → hlevel 1) _ _)) ⟩
    eps .η U (ca , inc (au , p))           ∎

  private module fo = Free-object

  make-free-conc-psh : ∀ A → Free-object (Forget-conc JC ℓ) A
  make-free-conc-psh A .fo.free = Concretize A , Concretize-is-concrete JC A
  make-free-conc-psh A .fo.unit = unit
  make-free-conc-psh A .fo.fold {B , conc} = univ B conc
  make-free-conc-psh A .fo.commute = ext λ _ _ → refl
  make-free-conc-psh A .fo.unique {B , conc} {f} g p = sym $
    unique B conc _ _ λ U x → p ηₚ _ $ₚ _

  make-free-conc-sh : ∀ A → Free-object (Forget-sheaf-to-conc JC ℓ) A
  make-free-conc-sh (A , conc) .fo.free =
    (Sheafify A , Sheafify-is-concrete JC A conc) , Sheafify-is-sheaf _
  make-free-conc-sh A .fo.unit = FreeSheaf.unit
  make-free-conc-sh A .fo.fold {(B , _) , shf} = FreeSheaf.univ B shf
  make-free-conc-sh A .fo.commute = ext λ _ _ → refl
  make-free-conc-sh (A , _) .fo.unique {(B , _) , shf} =
    FreeSheaf.make-free-sheaf A .fo.unique {B , shf}


-- We turn to the computation of limits and exponentials of concrete
-- presheaves.

-- Limits of concrete sheaves can be computed pointwise.
is-concrete-limit
  : ∀ {o ℓ o' ℓ' ℓj} {C : Precategory o ℓ} {J : Coverage C ℓj} (JC : Conc-coverage J)
      {D : Precategory o' ℓ'} {F : Functor D (PSh ℓ C)} {L} {ψ}
  → is-limit F L ψ
  → ((d : ⌞ D ⌟) → is-concrete JC (F · d))
  → is-concrete JC L
is-concrete-limit {C = C} _ {F = F} {L} {ψ} lim dconc {U} {x} {y} p =
  -- Mimicking Yoneda voodoo from Cat.Instances.Sheaf.Limits
  unyo-path $ lim.unique₂ {x = よ₀ U} _
    (λ f → yo-natl (sym (ψ .is-natural _ _ _ ηₚ _ $ₚ _))) (λ j → yo-natl refl)
    (λ j → yo-natl (dconc j $ funext λ g →
      F.₁ j g (ψ .η j .η U y) ≡˘⟨ ψ .η j .is-natural _ _ _ $ₚ _ ⟩
      ψ .η j .η _ (L.₁ g y)   ≡˘⟨ ap (ψ .η j .η _) (p $ₚ g) ⟩
      ψ .η j .η _ (L.₁ g x)   ≡⟨ ψ .η j .is-natural _ _ _ $ₚ _ ⟩
      F.₁ j g (ψ .η j .η U x) ∎))
  where
  module lim = is-limit lim
  module F x = PSh (F .F₀ x)
  module L = PSh L
  open Hom C

-- Concrete presheaves form an exponential ideal, just like sheaves.
-- Morally, this is because if we can distinguish points of B, then we
-- can also distinguish maps into B.
is-concrete-exponential
  : ∀ {ℓ ℓc} {C : Precategory ℓ ℓ} {J : Coverage C ℓc} (JC : Conc-coverage J)
  → (A B : Functor (C ^op) (Sets ℓ))
  → is-concrete JC B
  → is-concrete JC (PSh[_,_] C A B)
is-concrete-exponential {C = C} JC A B bconc {x = x} {y} p = ext λ V f au →
  bconc $ ext λ g →
    B ⟪ g ⟫ x .η V (f , au)            ≡˘⟨ x .is-natural V _ g $ₚ (f , au) ⟩
    _                                  ≡˘⟨ ap (λ fg → x .η _ (fg , _)) (idr _) ⟩
    x .η _ ((f ∘ g) ∘ id , A ⟪ g ⟫ au) ≡⟨ (p $ₚ (f ∘ g) ηₚ _) $ₚ (id , A ⟪ g ⟫ au) ⟩
    y .η _ ((f ∘ g) ∘ id , A ⟪ g ⟫ au) ≡⟨ ap (λ fg → y .η _ (fg , _)) (idr _) ⟩
    _                                  ≡⟨ y .is-natural V _ g $ₚ (f , au) ⟩
    B ⟪ g ⟫ y .η V (f , au)            ∎
  where open Precategory C


-- Next, we show the main properties of the category of concrete
-- sheaves.  We follow the conventions in Cat.Instances.Sheaves, using
-- homogeneous levels; the properties and proofs are the same as in
-- that module.

CSh[_,_]
  : ∀ {ℓ} (C : Precategory ℓ ℓ) {J : Coverage C ℓ} (JC : Conc-coverage J)
  → Precategory (lsuc ℓ) ℓ
CSh[ C , JC ] = ConcSh JC _

module _ {ℓ} {C : Precategory ℓ ℓ} {J : Coverage C ℓ} {JC : Conc-coverage J} where

  open Concretize JC
  open Cartesian-closed
  open Cartesian-category
  open Exponential
  open is-exponential
  open is-product
  open Product
  open Terminal


  ConcShfication : Functor (PSh ℓ C) CSh[ C , JC ]
  ConcShfication = Sheafification F∘ Concretization where
    Concretization = free-objects→functor (Free.make-free-conc-psh JC)
    Sheafification = free-objects→functor (Free.make-free-conc-sh JC)

  ConcShfication⊣ι : ConcShfication ⊣ Forget-conc-sheaf JC _
  ConcShfication⊣ι = LF⊣GR Concretization⊣ι Sheafification⊣ι where
    Concretization⊣ι = free-objects→left-adjoint (Free.make-free-conc-psh JC)
    Sheafification⊣ι = free-objects→left-adjoint (Free.make-free-conc-sh JC)

  ConcShfication-is-reflective : is-reflective ConcShfication⊣ι
  ConcShfication-is-reflective = id-equiv

  ConcShfication-is-monadic : is-monadic ConcShfication⊣ι
  ConcShfication-is-monadic = is-reflective→is-monadic _ id-equiv

  CSh[]-is-complete : is-complete ℓ ℓ CSh[ C , JC ]
  CSh[]-is-complete = equivalence→complete
    (is-equivalence.inverse-equivalence ConcShfication-is-monadic)
    (Eilenberg-Moore-is-complete _ (Functor-cat-is-complete (Sets-is-complete {ι = ℓ} {ℓ} {ℓ})))

  CSh[]-is-cocomplete : is-cocomplete ℓ ℓ CSh[ C , JC ]
  CSh[]-is-cocomplete F = done where
    psh-colim : Colimit (Forget-conc-sheaf JC _ F∘ F)
    psh-colim = Functor-cat-is-cocomplete (Sets-is-cocomplete {ι = ℓ} {ℓ} {ℓ}) _

    concretized : Colimit ((ConcShfication F∘ Forget-conc-sheaf JC _) F∘ F)
    concretized = subst Colimit F∘-assoc $
      left-adjoint-colimit ConcShfication⊣ι psh-colim

    done = natural-iso→colimit
      (F∘-iso-id-l (is-reflective→counit-iso ConcShfication⊣ι id-equiv))
      concretized


  CSh[]-products : has-products CSh[ C , JC ]
  CSh[]-products ((A , aconc) , ashf) ((B , bconc) , bshf) = prod where
    prod' = PSh-products _ C A B

    prod : Product CSh[ C , JC ] _ _
    prod .apex .fst .fst = prod' .apex
    prod .apex .fst .snd = is-concrete-limit JC
      {F = 2-object-diagram _ _} {ψ = 2-object-nat-trans _ _}
      (is-product→is-limit (PSh ℓ C) (prod' .has-is-product))
      (λ { true → aconc ; false → bconc })
    prod .π₁ = prod' .π₁
    prod .π₂ = prod' .π₂
    prod .has-is-product .⟨_,_⟩  = prod' .⟨_,_⟩
    prod .has-is-product .π₁∘⟨⟩  = prod' .π₁∘⟨⟩
    prod .has-is-product .π₂∘⟨⟩  = prod' .π₂∘⟨⟩
    prod .has-is-product .unique = prod' .unique

    prod .apex .snd =
      is-sheaf-limit
      {F = 2-object-diagram _ _} {ψ = 2-object-nat-trans _ _}
      (is-product→is-limit (PSh ℓ C) (prod' .has-is-product))
      (λ { true → ashf ; false → bshf })

  CSh[]-terminal : Terminal CSh[ C , JC ]
  CSh[]-terminal .top .fst .fst = PSh-terminal _ C .top
  CSh[]-terminal .top .fst .snd _ = refl
  CSh[]-terminal .top .snd .whole _ _     = lift tt
  CSh[]-terminal .top .snd .glues _ _ _ _ = refl
  CSh[]-terminal .top .snd .separate _ _  = refl
  CSh[]-terminal .has⊤ ((A , _) , _) = PSh-terminal _ C .has⊤ A

  CSh[]-cartesian : Cartesian-category CSh[ C , JC ]
  CSh[]-cartesian .products = CSh[]-products
  CSh[]-cartesian .terminal = CSh[]-terminal

  CSh[]-cc : Cartesian-closed CSh[ C , JC ] CSh[]-cartesian
  CSh[]-cc .has-exp ((A , _) , _) ((B , bconc) , bshf) = exp where
    exp' = PSh-closed C .has-exp A B

    exp : Exponential CSh[ C , JC ] _ _ _
    exp .B^A .fst .fst = exp' .B^A
    exp .B^A .fst .snd = is-concrete-exponential JC A B bconc
    exp .B^A      .snd = is-sheaf-exponential J A B bshf
    exp .ev = exp' .ev
    exp .has-is-exp .ƛ        = exp' .ƛ
    exp .has-is-exp .commutes = exp' .commutes
    exp .has-is-exp .unique   = exp' .unique
