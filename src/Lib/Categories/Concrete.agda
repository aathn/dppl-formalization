module Lib.Categories.Concrete where

-- Our definitions of concrete categories, sites, and sheaves.

open import Lib.Prelude renaming (id to idᶠ ; _∘_ to _∘ᶠ_) hiding (⋃ ; _∈_ ; [_])

open import Categories.Adjoint using (Adjoint ; _⊣_)
open import Categories.Adjoint.RAPL using (rapl)
open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Diagram.Empty using (empty)
open import Categories.Diagram.Pullback using (IsPullback)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Hom using (module Hom)
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.Functor.Properties using (Faithful)
open import Categories.Object.Terminal using (Terminal ; IsTerminal)
open import Categories.Object.Terminal.Limit using (limit⇒⊤ ; ⊤⇒limit)

import Categories.Morphism.Reasoning as MR

open import Function using (Func)
import Function.Construct.Setoid as FnS

open import Relation.Unary using (_∈_ ; _⊆_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

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

    record Parts {U : Obj} (S : Sieve U i) : Set (o ⊔ ℓ ⊔ e ⊔ i ⊔ o′ ⊔ e′) where
      field
        to : ∀ {V} (f : V ⇒ U) → f ∈ˢ S → A₀.Carrier V
        cong :
          ∀ {V} {f g : V ⇒ U} {Hf : f ∈ˢ S} {Hg : g ∈ˢ S}
          → f ≈ g → A₀._≈_ V (to f Hf) (to g Hg)

    open Parts public

    is-matching : {U : Obj} (S : Sieve U i) → Parts S → Set _
    is-matching {U = U} S p =
      ∀ {V W} (f : V ⇒ U) (Hf : f ∈ˢ S) (g : W ⇒ V) (Hgf : f ∘ g ∈ˢ S)
      → [ W ] A.₁ g .to (p .to f Hf) ≈ p .to (f ∘ g) Hgf
      where [_]_≈_ = A₀._≈_

    is-section : {U : Obj} (S : Sieve U i) → Parts S → A₀.Carrier U → Set _
    is-section {U = U} S p s =
      ∀ {V} (f : V ⇒ U) → (Hf : f ∈ˢ S) → [ V ] A.₁ f .to s ≈ p .to f Hf
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
      ; cong = λ {x} {y} H≈ → F-resp-≈ H≈
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


  -- Left-exactness and geometric morphisms, defined following
  -- https://1lab.dev/Cat.Diagram.Limit.Finite.html
  -- https://1lab.dev/Topoi.Base.html

  record is-lex {C D : Category o ℓ e} (F : Functor C D) : Set (o ⊔ ℓ ⊔ e) where
    open Category C
    open Functor F
    field
      pres-⊤ : ∀ {T} → IsTerminal C T → IsTerminal D (F₀ T)
      pres-pullback
        : ∀ {P X Y Z} {p₁ : P ⇒ X} {p₂ : P ⇒ Y}
            {f : X ⇒ Z} {g : Y ⇒ Z}
        → IsPullback C p₁ p₂ f g
        → IsPullback D (F₁ p₁) (F₁ p₂) (F₁ f) (F₁ g)

  record Geom[_,_] (C D : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
    field
      Inv[_]  : Functor D C
      Dir[_]  : Functor C D
      Inv-lex : is-lex Inv[_]
      Inv⊣Dir : Inv[_] ⊣ Dir[_]


module Pull {o ℓ e i p : Level} {𝒞 𝒟 : CCat o ℓ e} (S : CSite 𝒞 i p) where
  -- We now define a notion of induced topology, where a topology on 𝒞 is pulled
  -- back to form a topology on 𝒟 given a geometric morphism from 𝒟 to 𝒞.
  -- Sheaves on 𝒞 are also pulled back to form sheaves on 𝒟.
  --
  -- In particular, the induced topology makes a sieve S on U open in 𝒟
  -- if and only if the sieve R* S on R U is open in 𝒞, where we have
  -- g ∈ R* S  ⟺  Radjunct g ∈ S.
  --
  -- Note that the above definition is equivalent to
  -- g ∈ R* S  ⟺  g ∈ ⟨ R f ∣ f ∈ S ⟩, where ⟨ X ⟩ denotes
  -- the sieve generated by the maps in X.  Hence, it may not be necessary to
  -- require a geometric morphism, it may suffice if R is continuous (in the
  -- limit-preserving sense), for example.  An additional observation in this
  -- vein is that the Stacks project (https://stacks.math.columbia.edu/tag/00X0)
  -- defines a morphism of sites 𝒞 → 𝒟 to be a continuous functor f : 𝒟 → 𝒞
  -- (notice the order-reversal of 𝒟 and 𝒞).  Thus, it may be more correct to
  -- think of this construction as a pushforward along a candidate morphism
  -- 𝒞 → D inducing the coarsest topology making the functor continuous.
  -- The pullback sheaf construction is then just the functor of sheaves
  -- induced by our newly formed morphism of sites.
  --
  -- In any case, assuming that we have an adjunction streamlines the
  -- definitions, and is general enough for our application.

  open CSite using (covering ; is-stable ; is-concrete ; is-maximal ; is-local)
  module C = CCat 𝒞
  module D = CCat 𝒟
  module S = CSite S

  open Sieve D.Cat

  module _ (G : Geom[ D.Cat , C.Cat ]) where
    open is-lex
    open Geom[_,_]

    private
      module L = Functor Inv[ G ]
      module R = Functor Dir[ G ]
      module LR = Functor (Inv[ G ] ∘F Dir[ G ])
      module RL = Functor (Dir[ G ] ∘F Inv[ G ])
      open Adjoint (Inv⊣Dir G)

      module DR = D.HomReasoning
      module CR = C.HomReasoning

      LH = L.homomorphism
      RH = R.homomorphism

      abstract
        R⋆-is-terminal : IsTerminal C.Cat (R.₀ D.⋆)
        R⋆-is-terminal = ⊤-is-terminal R⋆-terminal
          where
            open Terminal
            R⋆-terminal : Terminal C.Cat
            R⋆-terminal =
              limit⇒⊤ C.Cat $
              rapl (Inv⊣Dir G) (empty _ o ℓ e) $
              ⊤⇒limit D.Cat D.terminal

      L⋆-is-terminal = Inv-lex G .pres-⊤ C.⋆-is-terminal
      L⋆-terminal = record { ⊤ = _ ; ⊤-is-terminal = L⋆-is-terminal }

      module R⋆ = IsTerminal R⋆-is-terminal
      module L⋆ = IsTerminal L⋆-is-terminal

      R* : ∀ {U} → Sieve U i → S.Sieve (R.₀ U) i
      R* S .arrows g = Radjunct g ∈ˢ S
      R* S .closed Hf g = resp-≈ S (D.assoc DR.○ D.∘-resp-≈ʳ (DR.⟺ LH))
                                        (closed S Hf (L.₁ g))
      R* S .resp-≈ H≈ Hf = resp-≈ S (D.∘-resp-≈ʳ (L.F-resp-≈ H≈)) Hf

    PullSite : CSite 𝒟 i p
    PullSite .covering U R = R.₀ U S.◀ R* R
    PullSite .is-stable g {R} HR =
      S.upward-closed (S.is-stable (R.₁ g) HR) λ H∈ →
        R .resp-≈ (D.∘-resp-≈ʳ LH DR.○ extendʳ (counit.commute _)) H∈
      where open MR D.Cat
    PullSite .is-concrete {R = R} HR x =
      let V , f , Hf , y , H≈ = S.is-concrete HR (R.₁ x C.∘ R⋆.!)
          H≈′ = begin
            x                                             ≈⟨ introʳ D.!-unique₂ ⟩
            x D.∘ Radjunct R⋆.! D.∘ L⋆.!                  ≈⟨ extendʳ (extendʳ (counit.sym-commute _)) ⟩
            counit.η _ D.∘ (LR.₁ x D.∘ L.₁ R⋆.!) D.∘ L⋆.! ≈⟨ refl⟩∘⟨ (⟺ LH ○ L.F-resp-≈ H≈) ⟩∘⟨refl ⟩
            counit.η _ D.∘ L.F₁ (f C.∘ y) D.∘ L⋆.!        ≈⟨ D.sym-assoc ⟩
            Radjunct (f C.∘ y) D.∘ L⋆.!                   ∎
      in L.₀ C.⋆
       , Radjunct (f C.∘ y)
       , R .resp-≈ (D.assoc ○ D.∘-resp-≈ʳ (⟺ LH)) (R .closed Hf _)
       , L⋆.!
       , H≈′
     where open D.HomReasoning
           open MR D.Cat
    PullSite .is-maximal {R = R} Hid =
      S.is-maximal (R .resp-≈ D.identityˡ (R .closed Hid _))
    PullSite .is-local {U} {R} {S} HR HS =
      let HS′ : ∀ {V} {f : V C.⇒ R.₀ U}
              → f S.∈ˢ R* R → V S.◀ S.pullback f (R* S)
          HS′ = λ {_} {f} Hf →
            S.upward-closed (S.is-stable (unit.η _) (HS Hf)) λ {_} {x} H∈ →
              let H≈ = begin
                    Radjunct f D.∘ Radjunct (unit.η _ C.∘ x) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ LH ⟩
                    Radjunct f D.∘ _ D.∘ _ D.∘ L.₁ x         ≈⟨ refl⟩∘⟨ (D.sym-assoc ○ elimˡ zig) ⟩
                    Radjunct f D.∘ L.₁ x                     ≈⟨ D.assoc ○ D.∘-resp-≈ʳ (⟺ LH) ⟩
                    Radjunct (f C.∘ x)                       ∎
              in
              S .resp-≈ H≈ H∈
      in
      S.is-local HR HS′
      where open D.HomReasoning
            open MR D.Cat

    module _
      {o′ ℓ′ : Level}
      (F : CSheaf S o′ ℓ′)
      where

      private
        module F = CSheaf F
        open CSheaf using (Psh ; is-sheaf ; is-concrete)
        open F.Parts

        FH = F.homomorphism

        RL⋆-!-unique : ∀ {U} {f : U C.⇒ RL.₀ C.⋆} → R.₁ L⋆.! C.∘ R⋆.! C.≈ f
        RL⋆-!-unique {f = f} = begin
          R.₁ L⋆.! C.∘ R⋆.!          ≈⟨ refl⟩∘⟨ R⋆.!-unique₂ ⟩
          R.₁ L⋆.! C.∘ R.₁ D.! C.∘ f ≈⟨ pullˡ (⟺ RH) ⟩
          R.₁ (L⋆.! D.∘ D.!) C.∘ f   ≈⟨ R.F-resp-≈ L⋆.!-unique₂ ⟩∘⟨refl ⟩
          R.₁ D.id C.∘ f             ≈⟨ elimˡ R.identity ⟩
          f                          ∎
          where open C.HomReasoning
                open MR C.Cat

        Radjunct-lemma : ∀ {X} {z : C.⋆ C.⇒ R.₀ X} → R.₁ (Radjunct z D.∘ L⋆.!) C.∘ R⋆.! C.≈ z
        Radjunct-lemma {z = z} = begin
          R.₁ (Radjunct z D.∘ L⋆.!) C.∘ R⋆.!     ≈⟨ C.∘-resp-≈ˡ RH ○ C.assoc ⟩
          R.₁ (Radjunct z) C.∘ R.₁ L⋆.! C.∘ R⋆.! ≈⟨ refl⟩∘⟨ RL⋆-!-unique ⟩
          Ladjunct (Radjunct z)                  ≈⟨ LRadjunct≈id ⟩
          z                                      ∎
          where open C.HomReasoning

      PullSheaf : CSheaf PullSite o′ ℓ′
      PullSheaf .Psh = F.Psh ∘F R.op
      PullSheaf .is-sheaf {U} {R} HR p matching =
        mkUnique (uniq-section .witness) section′ unique′
        where
          p′ : F.Parts (R* R)
          p′ = record
            { to = λ {V} f Hf → F.₁ (unit.η V) .to (p .to (Radjunct f) Hf)
            ; cong = λ H≈ →
              F.₁ (unit.η _) .cong $ p .cong $ D.∘-resp-≈ʳ $ L.F-resp-≈ H≈
            }
          matching′ : F.is-matching (R* R) p′
          matching′ {W = W} f Hf g Hgf = begin
            F.₁ g .to (F.₁ (unit.η _) .to (p .to (Radjunct f) Hf))    ≈⟨ FW.sym FH ○ (F.F-resp-≈ (unit.commute _) ○ FH) ⟩
            F.₁ _ .to (F.₁ (RL.₁ g) .to (p .to (Radjunct f) Hf))      ≈⟨ F.F₁ (unit.η _) .cong $ matching _ _ _ _ ⟩
            F.₁ _ .to (p .to (Radjunct f D.∘ L.₁ g) (R .closed Hf _)) ≈⟨ F.F₁ (unit.η _) .cong $ p .cong H≈′ ⟩
            F.₁ (unit.η _) .to (p .to (Radjunct (f C.∘ g)) Hgf)       ∎
            where open SetoidR (F.₀ W)
                  module FW = Setoid (F.₀ W)
                  _○_ = FW.trans
                  H≈′ = D.assoc DR.○ D.∘-resp-≈ʳ (DR.⟺ LH)
          uniq-section : ∃! (F.₀ (R.₀ U)) (F.is-section (R* R) p′)
          uniq-section = F.is-sheaf HR p′ matching′
          open Matching (F.Psh ∘F R.op)
          section′ : is-section _ p (uniq-section .witness)
          section′ {V} f Hf = begin
            F.₁ (R.₁ f) .to (uniq-section .witness)                      ≈⟨ uniq-section .has-prop _ Hf₂ ⟩
            F.₁ (unit.η _) .to (p .to (Radjunct (R.₁ f)) Hf₂)            ≈⟨ F.₁ (unit.η _) .cong $ p .cong (counit.commute f) ⟩
            F.₁ (unit.η _) .to (p .to (f D.∘ counit.η _) Hf₁)            ≈⟨ F.₁ (unit.η _) .cong $ FV′.sym $ matching _ _ _ _ ⟩
            F.₁ (unit.η _) .to (F.₁ (R.₁ (counit.η _)) .to (p .to f Hf)) ≈⟨ FV.sym FH ○ (F.F-resp-≈ zag ○ F.identity) ⟩
            p .to f Hf                                                   ∎
            where open SetoidR (F.₀ (R.₀ V))
                  module FV  = Setoid (F.₀ (R.₀ V))
                  module FV′ = Setoid (F.₀ (R.₀ (LR.₀ V)))
                  _○_ = FV.trans
                  Hf₁ = R .closed Hf (counit.η _)
                  Hf₂ = R .resp-≈ (counit.sym-commute f) Hf₁
          module FU = Setoid (F.₀ (R.₀ U))
          unique′ : ∀ s → is-section _ p s → uniq-section .witness FU.≈ s
          unique′ s Hs = uniq-section .unique s λ {V} f Hf →
            let module FD = Setoid (F.₀ V)
                _○_ = FD.trans
            in F.F-resp-≈ (CR.⟺ LRadjunct≈id) ○ (FH ○ F.F₁ (unit.η _) .cong (Hs _ Hf))
      PullSheaf .is-concrete {x = x} {y} H≈ =
        F.is-concrete λ {z} → begin
          F.₁ z .to x                      ≈⟨ F.F-resp-≈ (CR.⟺ Radjunct-lemma) ○ FH ⟩
          F.₁ R⋆.! .to (F.₁ (R.₁ _) .to x) ≈⟨ F.₁ R⋆.! .cong H≈ ⟩
          F.₁ R⋆.! .to (F.₁ (R.₁ _) .to y) ≈⟨ F.X.sym FH ○ F.F-resp-≈ Radjunct-lemma ⟩
          F.₁ z .to y                      ∎
        where open SetoidR (F.₀ C.⋆)
              _○_ = F.X.trans


module Meet {o ℓ e i p : Level}
  {𝒞 : CCat o ℓ e}
  (S₁ : CSite 𝒞 i p)
  (S₂ : CSite 𝒞 i p)
  where

  open CSite using (covering ; is-stable ; is-concrete ; is-maximal ; is-local)
  open CCat 𝒞
  open HomReasoning
  open MR Cat

  private
    module S₁ = CSite S₁
    module S₂ = CSite S₂

  MeetSite : CSite 𝒞 i p
  MeetSite .covering U R = U S₁.◀ R × U S₂.◀ R
  MeetSite .is-stable g (HR₁ , HR₂) = S₁.is-stable g HR₁ , S₂.is-stable g HR₂
  MeetSite .is-concrete = λ HR → S₁.is-concrete (HR .π₁)
  MeetSite .is-maximal = λ Hid → S₁.is-maximal Hid , S₂.is-maximal Hid
  MeetSite .is-local (HR₁ , HR₂) HS =
    S₁.is-local HR₁ (π₁ ∘ᶠ HS) , S₂.is-local HR₂ (π₂ ∘ᶠ HS)

  open CSheaf using (Psh ; is-sheaf ; is-concrete)

  module _
    {o′ ℓ′ : Level}
    (F : CSheaf S₁ o′ ℓ′)
    where
    private
      module F = CSheaf F

    MeetSheaf₁ : CSheaf MeetSite o′ ℓ′
    MeetSheaf₁ .Psh = F.Psh
    MeetSheaf₁ .is-sheaf (HR₁ , _) p matching = F.is-sheaf HR₁ p matching
    MeetSheaf₁ .is-concrete = F.is-concrete

  module _
    {o′ ℓ′ : Level}
    (F : CSheaf S₂ o′ ℓ′)
    where
    private
      module F = CSheaf F

    MeetSheaf₂ : CSheaf MeetSite o′ ℓ′
    MeetSheaf₂ .Psh = F.Psh
    MeetSheaf₂ .is-sheaf (_ , HR₂) p matching = F.is-sheaf HR₂ p matching
    MeetSheaf₂ .is-concrete = F.is-concrete
