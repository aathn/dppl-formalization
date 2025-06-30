module Lib.Concrete.Concrete where

-- Our definitions of concrete categories, sites, and sheaves.

open import Lib.Prelude hiding (id ; _∘_ ; _∈_ ; [_])

open import Categories.Category using (Category)
open import Categories.Category.Construction.Presheaves using (Presheaves)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.SubCategory using (FullSubCategory)
open import Categories.Functor using (Functor)
open import Categories.Functor.Hom using (module Hom)
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.Functor.Properties using (Faithful)
open import Categories.Object.Terminal using (Terminal)

open import Function using (Func)
import Function.Construct.Setoid as FnS

open import Relation.Unary using (_∈_ ; _⊆_)
open import Relation.Binary.Bundles using (Setoid)

open Func

module _ {a₁ a₂ b₁ b₂ : Level} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} where
  open Setoid B
  Im : Func A B → ℙ Carrier _
  Im f y = ∃ λ x → y ≈ f .to x

  _≗_ : Rel (Func A B) _
  _≗_ = F._≈_
    where module F = Setoid (FnS.setoid A B)

module _ {c ℓ ℓ′ : Level} (A : Setoid c ℓ) where
  open Setoid A
  record ∃! (P : ℙ Carrier ℓ′) : Set (c ⊔ ℓ ⊔ ℓ′) where
    constructor mkUnique
    field
      witness  : Carrier
      has-prop : P witness
      unique   : (x : Carrier) → P x → witness ≈ x

  open ∃! public

record CCat (o ℓ e : Level) : Set (lsuc (o ⊔ ℓ ⊔ e)) where
  -- Here, we use a more restrictive definition of concrete category
  -- than the standard presentation in that we require the forgetful
  -- functor to be representable by a terminal object
  -- (following Matache et al.).
  field
    Cat : Category o ℓ e

  open Category Cat public
  open Hom Cat public

  field
    terminal : Terminal Cat

  open Terminal terminal public renaming (⊤ to ⋆ ; ⊤-is-terminal to ⋆-is-terminal)

  field
    ⋆-hom-faithful : Faithful Hom[ ⋆ ,-]

  obj∣_∣ : Obj → Setoid ℓ e
  obj∣ c ∣ = Hom[ ⋆ , c ]

  hom∣_∣ : {o₁ o₂ : Obj} → o₁ ⇒ o₂ → Func obj∣ o₁ ∣ obj∣ o₂ ∣
  hom∣ f ∣ = record {
      to = λ g → f ∘ g
    ; cong = ∘-resp-≈ʳ
    }

  module obj-set (c : Obj) = Setoid Hom[ ⋆ , c ]


module _ {o ℓ e : Level} where

  module Sieve (C : Category o ℓ e) where
    -- In contrast to Matache et al. (2022), we choose to work primarily
    -- with covering *sieves* (and Grothendieck Topologies), which
    -- simplifies definitions.  For coverage-based sites satisfying
    -- axioms (L) and (M) (as presented in Matache et al.), there is
    -- always a corresponding Grothendieck topology which gives rise
    -- to the same sheaves.

    -- We adapt definitions from the 1lab (which we unfortunately cannot
    -- use as-is since we cannot easily switch to Cubical Agda).
    -- https://1lab.dev/Cat.Diagram.Sieve.html

    open Category C

    record Sieve (U : Obj) (i : Level) : Set (o ⊔ ℓ ⊔ e ⊔ lsuc i) where
      field
        arrows : ∀ {V} → ℙ (V ⇒ U) i
        closed : ∀ {V W f} (Hf : f ∈ arrows) (g : V ⇒ W) → f ∘ g ∈ arrows
        resp-≈ : ∀ {V} {f g} → f ≈ g → f ∈ arrows {V} → g ∈ arrows

    open Sieve public

    private
      variable
        i ℓ′ : Level

    infix 4 _∈ˢ_ _⊆ˢ_
    _∈ˢ_ : ∀ {U} {V} → V ⇒ U → Sieve U i → Set i
    f ∈ˢ S = f ∈ S .arrows

    _⊆ˢ_ : ∀ {U} → Rel (Sieve U i) (o ⊔ ℓ ⊔ i)
    S ⊆ˢ R = ∀ {V} → S .arrows {V} ⊆ R .arrows

    maximal : ∀ {U} → Sieve U i
    maximal .arrows x = 𝟙
    maximal .closed g x = tt
    maximal .resp-≈ H≈ Hf = tt

    intersect : ∀ {U} {I : Set ℓ′} (F : I → Sieve U i) → Sieve U (i ⊔ ℓ′)
    intersect {I = I} F .arrows h = (x : I) → h ∈ˢ F x
    intersect {I = I} F .closed Hx g i = F i .closed (Hx i) g
    intersect {I = I} F .resp-≈ H≈ Hf i = F i .resp-≈ H≈ (Hf i)

    pullback : ∀ {U V} → V ⇒ U → Sieve U i → Sieve V i
    pullback f S .arrows h = f ∘ h ∈ˢ S
    pullback f S .closed Hf g = S .resp-≈ assoc (S .closed Hf g)
    pullback f S .resp-≈ H≈ Hf = S .resp-≈ (∘-resp-≈ʳ H≈) Hf

  module Matching
    {o′ e′ : Level}
    {C : Category o ℓ e}
    (A : Presheaf C (Setoids o′ e′))
    where
    -- We define matching families over sieves, adapting the definitions at
    -- https://1lab.dev/Cat.Site.Base.html

    open Category C
    open Sieve C

    private
      module A = Functor A
      module A₀ (U : Obj) = Setoid (A.₀ U)

      variable
        i : Level

    -- Maybe this could be made into a Func from a setoid of pairs f , Hf
    -- where equality only applies to f...
    record Parts {U : Obj} (S : Sieve U i) : Set (o ⊔ ℓ ⊔ e ⊔ i ⊔ o′ ⊔ e′) where
      field
        to : ∀ {V} {f : V ⇒ U} → f ∈ˢ S → A₀.Carrier V
        cong :
          ∀ {V} {f g : V ⇒ U} {Hf : f ∈ˢ S} {Hg : g ∈ˢ S}
          → f ≈ g → A₀._≈_ V (to Hf) (to Hg)

    open Parts public

    is-matching : {U : Obj} (S : Sieve U i) → Parts S → Set _
    is-matching {U = U} S p =
      ∀ {V W} {f : V ⇒ U} (Hf : f ∈ˢ S) {g : W ⇒ V} (Hgf : f ∘ g ∈ˢ S)
      → [ W ] A.₁ g .to (p .to Hf) ≈ p .to Hgf
      where [_]_≈_ = A₀._≈_

    is-section : {U : Obj} (S : Sieve U i) → Parts S → A₀.Carrier U → Set _
    is-section {U = U} S p s =
      ∀ {V} {f : V ⇒ U} (Hf : f ∈ˢ S) → [ V ] A.₁ f .to s ≈ p .to Hf
      where [_]_≈_ = A₀._≈_


  record CSite (𝒞 : CCat o ℓ e) (i p : Level) : Set (o ⊔ ℓ ⊔ e ⊔ lsuc (i ⊔ p)) where
    -- Grothendieck sites (in a concrete rendering), adapted from
    -- https://1lab.dev/Cat.Site.Grothendieck.html
    open CCat 𝒞
    open Sieve Cat public

    field
      covering : (U : Obj) → ℙ (Sieve U i) p

    _◀_ : (U : Obj) (R : Sieve U i) → Set p
    _◀_ = covering

    field
      is-stable :
        ∀ {U V} (g : V ⇒ U) {R : Sieve U i} (_ : U ◀ R)
        → ---------------------------------------------
        V ◀ pullback g R

      is-concrete :
        ∀ {U} {R : Sieve U i} (_ : U ◀ R) (x : obj-set.Carrier U)
        → -------------------------------------------------------
        ∃₂ λ V (f : V ⇒ U) → f ∈ˢ R × x ∈ Im hom∣ f ∣

      is-maximal : ∀ {U} {R : Sieve U i} → id ∈ˢ R → U ◀ R

      is-local :
        ∀ {U} {R S : Sieve U i} (_ : U ◀ R)
        → (∀ {V} {f : V ⇒ U} → f ∈ˢ R → V ◀ pullback f S)
        → -----------------------------------------------
        U ◀ S

    upward-closed :
      ∀ {U} {R S : Sieve U i} (_ : U ◀ R)
      → ---------------------------------
      R ⊆ˢ S → U ◀ S
    upward-closed {S = S} HR H⊆ =
      is-local HR λ Hf → is-maximal (S .closed (H⊆ Hf) id)


  record CSheaf
    {i p : Level}
    {𝒞 : CCat o ℓ e}
    (S : CSite 𝒞 i p)
    (o′ e′ : Level)
    : -------------------------------------------
    Set (o ⊔ ℓ ⊔ e ⊔ lsuc i ⊔ p ⊔ lsuc (o′ ⊔ e′))
    where
    -- Concrete sheaves over concrete sites, with inspiration from
    -- https://1lab.dev/Cat.Site.Base.html
    open CCat 𝒞
    open CSite S

    field
      Psh : Presheaf Cat (Setoids o′ e′)

    open Functor Psh public
    open Matching Psh public

    module F₀ (U : Obj) = Setoid (F₀ U)
    module X = F₀ ⋆

    ∣_∣ : Setoid o′ e′
    ∣_∣ = F₀ ⋆

    F-maps : (U : Obj) → F₀.Carrier U → Func obj∣ U ∣ ∣_∣
    F-maps U FU = record
      { to = λ f → F₁ f .to FU
      ; cong = λ H≈ → F-resp-≈ H≈
      }

    R[_,_] : (U : Obj) → ℙ (Func obj∣ U ∣ ∣_∣) _
    R[_,_] U f = ∃ λ FU → f ≗ F-maps U FU

    field
      is-sheaf :
        ∀ {U} {R : Sieve U i} (_ : U ◀ R)
        (p : Parts R) (_ : is-matching R p)
        → ---------------------------------
        ∃! (F₀ U) (is-section R p)

      is-concrete :
        ∀ {U} → injection (F₀._≈_ U) _≗_ (F-maps U)


module _ {o ℓ e i p : Level} {𝒞 : CCat o ℓ e} (S : CSite 𝒞 i p) (o′ e′ : Level) where
  open CCat 𝒞

  -- Finally, we define the category of concrete sheaves over a fixed
  -- site.  This is just the subcategory of presheaves whose objects
  -- are concrete sheaves.
  
  CSheaves : Category _ _ _
  CSheaves = FullSubCategory (Presheaves Cat) (CSheaf.Psh {S = S} {o′} {e′})
