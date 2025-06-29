module Lib.Categories.Concrete where

-- Our definitions of concrete categories, sites, and sheaves.

open import Lib.Prelude renaming (id to idᶠ ; _∘_ to _∘ᶠ_) hiding (⋃ ; _∈_ ; [_])

open import Categories.Adjoint using (Adjoint ; _⊣_)
open import Categories.Adjoint.RAPL using (rapl)
open import Categories.Category using (Category)
open import Categories.Category.Complete.Finitely using (FinitelyComplete)
open import Categories.Category.Construction.Presheaves using (Presheaves′ ; Presheaves)
open import Categories.Category.Construction.Properties.Presheaves.Complete using (Presheaves-FinitelyComplete)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Diagram.Empty using (empty)
open import Categories.Diagram.Pullback using (Pullback ; IsPullback)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Hom
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.Functor.Properties using (Faithful)
open import Categories.NaturalTransformation using (NaturalTransformation)
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


module Sieve {o ℓ e : Level} (C : Category o ℓ e) where
  open Category C

  -- In contrast to Matache et al. (2022), we choose to work primarily
  -- with covering *sieves* (and Grothendieck Topologies), which
  -- simplifies definitions.  For coverage-based sites satisfying
  -- axioms (L) and (M) (as presented in Matache et al.), there is
  -- always a corresponding Grothendieck topology which gives rise
  -- to the same sheaves.

  -- We adapt definitions from the 1lab (which we unfortunately cannot
  -- use as-is since we cannot easily switch to Cubical Agda).
  -- https://1lab.dev/Cat.Site.Base.html
  -- https://1lab.dev/Cat.Diagram.Sieve.html

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

module _ {o ℓ e : Level} (𝒞 : CCat o ℓ e) where
  open CCat 𝒞
  open Sieve Cat

  record CSite (p i : Level) : Set (o ⊔ ℓ ⊔ e ⊔ lsuc (p ⊔ i)) where
    field
      covers : Obj → Set p
      cover  : ∀ {U} → covers U → Sieve U i

      is-stable :
        ∀ {U V} (g : V ⇒ U) (R : covers U)
        → -------------------------------------
        ∃ λ S → cover S ⊆ˢ pullback g (cover R)

      is-concrete :
        ∀ {U} (S : covers U) (x : obj-set.Carrier U)
        → --------------------------------------------------
        ∃₂ λ V (f : V ⇒ U) → f ∈ˢ cover S × x ∈ Im hom∣ f ∣

      is-maximal : ∀ {U} → ∃ λ (S : covers U) → id ∈ˢ cover S

      is-local :
        ∀ {U} (R : covers U) (S : Sieve U i)
        → (∀ {V} {f : V ⇒ U} → f ∈ˢ cover R → ∃ λ T → cover T ⊆ˢ pullback f S)
        → --------------------------------------------------------------------
        ∃ λ S′ → cover S′ ⊆ˢ S

module _ {o ℓ e : Level} {𝒞 : CCat o ℓ e} where
  open CCat 𝒞

  module Matching {o′ e′ : Level} (A : Presheaf Cat (Setoids o′ e′)) where
    -- We define the property of being a sheaf, adapting the definitions at
    -- https://1lab.dev/Cat.Site.Base.html

    open Sieve Cat

    private
      module A = Functor A
      module A₀ (U : Obj) = Setoid (A.₀ U)

      variable
        i : Level

    Parts : {U : Obj} → Sieve U i → Set _
    Parts {U = U} S = ∀ {V} (f : V ⇒ U) → f ∈ˢ S → A₀.Carrier V

    is-matching : {U : Obj} (S : Sieve U i) → Parts S → Set _
    is-matching {U = U} S p =
      ∀ {V W} (f : V ⇒ U) (Hf : f ∈ˢ S) (g : W ⇒ V) (Hgf : f ∘ g ∈ˢ S)
      → [ W ] A.₁ g .to (p f Hf) ≈ p (f ∘ g) Hgf
      where [_]_≈_ = A₀._≈_

    is-section : {U : Obj} (S : Sieve U i) → Parts S → A₀.Carrier U → Set _
    is-section {U = U} S p s =
      ∀ {V} (f : V ⇒ U) → (Hf : f ∈ˢ S) → [ V ] A.₁ f .to s ≈ p f Hf
      where [_]_≈_ = A₀._≈_

  record CSheaf
    {i p : Level}
    (S : CSite 𝒞 i p)
    (o′ e′ : Level)
    : --------------------------------------
    Set (o ⊔ ℓ ⊔ e ⊔ i ⊔ p ⊔ lsuc (o′ ⊔ e′))
    where
    open CSite S

    field
      Psh : Presheaf Cat (Setoids o′ e′)

    open Matching Psh public
    open Functor Psh public

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
        ∀ {U} (S : covers U) (p : Parts (S .cover))
        (_ : is-matching (S .cover) p)
        → -------------------------------------------
        ∃! (F₀ U) (is-section (S .cover) p)

      is-concrete :
        ∀ {U} → injection (F₀._≈_ U) _≗_ (F-maps U)

module _ {o ℓ e : Level} where
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


module Lift {o ℓ e p i : Level} {𝒞 𝒟 : CCat o ℓ e} (S : CSite 𝒞 p i) where

  open CSite
  module C = CCat 𝒞
  module D = CCat 𝒟
  module S = CSite S
  module DS = Sieve D.Cat
  open Sieve C.Cat

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

      L⋆-is-terminal = Inv-lex G .pres-⊤ C.⋆-is-terminal
      L⋆-terminal = record { ⊤ = _ ; ⊤-is-terminal = L⋆-is-terminal }

      module L⋆ = IsTerminal L⋆-is-terminal

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

        RL⋆-is-terminal : IsTerminal C.Cat (RL.₀ C.⋆)
        RL⋆-is-terminal = ⊤-is-terminal RL⋆-terminal
          where
            open Terminal
            RL⋆-terminal : Terminal C.Cat
            RL⋆-terminal =
              limit⇒⊤ C.Cat $
              rapl (Inv⊣Dir G) (empty _ o ℓ e) $
              ⊤⇒limit D.Cat L⋆-terminal

      module R⋆ = IsTerminal R⋆-is-terminal
      module RL⋆ = IsTerminal RL⋆-is-terminal

      Radjunct-lemma : ∀ {X} {z : C.⋆ C.⇒ R.₀ X} → R.₁ (Radjunct z) C.≈ z C.∘ C.!
      Radjunct-lemma {z = z} = begin
        R.₁ (Radjunct z)              ≈⟨ introʳ RL⋆.!-unique₂ ○ C.sym-assoc ⟩
        Ladjunct (Radjunct z) C.∘ C.! ≈⟨ LRadjunct≈id ⟩∘⟨refl ⟩
        z C.∘ C.!                     ∎
        where open C.HomReasoning
              open MR C.Cat

      R⁺ : ∀ {U} → Sieve (R.₀ U) i → DS.Sieve U i
      R⁺ S .arrows g = R.₁ g ∈ˢ S
      R⁺ S .closed Hf g = S .resp-≈ (CR.⟺ RH) (S .closed Hf (R.₁ g))
      R⁺ S .resp-≈ H≈ = S .resp-≈ (R.F-resp-≈ H≈)

      R₊ : ∀ {U} → DS.Sieve U i → Sieve (R.₀ U) i
      R₊ S .arrows g = Radjunct g DS.∈ˢ S
      R₊ S .closed Hf g = DS.resp-≈ S (D.assoc DR.○ D.∘-resp-≈ʳ (DR.⟺ LH))
                                      (DS.closed S Hf (L.₁ g))
      R₊ S .resp-≈ H≈ Hf = DS.resp-≈ S (D.∘-resp-≈ʳ (L.F-resp-≈ H≈)) Hf


    LiftSite : CSite 𝒟 (o ⊔ ℓ ⊔ e ⊔ p ⊔ lsuc i) i
    LiftSite .covers U =
      ∃₂ λ (R : DS.Sieve U i) (Sᵣ : S.covers (R.₀ U)) → S.cover Sᵣ ⊆ˢ R₊ R
    LiftSite .cover (R , _) = R
    LiftSite .is-stable g (R , Sᵣ , H⊆) =
      let S′ , H⊆′ = S.is-stable (R.₁ g) Sᵣ
          S′⊆R′ : S.cover S′ ⊆ˢ R₊ (DS.pullback g R)
          S′⊆R′ H∈ =
            DS.resp-≈ R
              (D.∘-resp-≈ʳ LH DR.○ extendʳ (counit.commute _)) (H⊆ $ H⊆′ H∈)
      in
      (DS.pullback g R , S′ , S′⊆R′) , idᶠ
      where open MR D.Cat
    LiftSite .is-concrete (R ,  Sᵣ , H⊆) x =
      let V , f , Hf , y , H≈ = S.is-concrete Sᵣ (R.₁ x C.∘ R⋆.!)
          H≈′ = begin
            x                                             ≈⟨ introʳ D.!-unique₂ ⟩
            x D.∘ Radjunct R⋆.! D.∘ L⋆.!                  ≈⟨ extendʳ (extendʳ (counit.sym-commute _)) ⟩
            counit.η _ D.∘ (LR.₁ x D.∘ L.₁ R⋆.!) D.∘ L⋆.! ≈⟨ refl⟩∘⟨ (⟺ LH ○ L.F-resp-≈ H≈) ⟩∘⟨refl ⟩
            counit.η _ D.∘ L.F₁ (f C.∘ y) D.∘ L⋆.!        ≈⟨ D.sym-assoc ⟩
            Radjunct (f C.∘ y) D.∘ L⋆.!                   ∎
      in L.₀ C.⋆
       , Radjunct (f C.∘ y)
       , H⊆ (closed (S.cover Sᵣ) Hf y)
       , L⋆.!
       , H≈′
     where open D.HomReasoning
           open MR D.Cat
    LiftSite .is-maximal = (DS.maximal , S.is-maximal .π₁ , λ _ → tt) , tt
    LiftSite .is-local {U} (R , Sᵣ , H⊆) S HS =
      let HS′ : ∀ {V} {f : V C.⇒ R.₀ U}
              → f ∈ˢ S.cover Sᵣ → ∃ λ T → S.cover T ⊆ˢ pullback f (R₊ S)
          HS′ = λ {_} {f} H∈ →
            let (T , Sₜ , H⊆T₁) , H⊆T₂ = HS (H⊆ H∈)
                Sₜ′ , H⊆Sₜ = S.is-stable (unit.η _) Sₜ
            in Sₜ′ , λ {_} {x} H∈ →
              let H≈ = begin
                    Radjunct f D.∘ Radjunct (unit.η _ C.∘ x) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ LH ⟩
                    Radjunct f D.∘ _ D.∘ _ D.∘ L.₁ x         ≈⟨ refl⟩∘⟨ (D.sym-assoc ○ elimˡ zig) ⟩
                    Radjunct f D.∘ L.₁ x                     ≈⟨ D.assoc ○ D.∘-resp-≈ʳ (⟺ LH) ⟩
                    Radjunct (f C.∘ x)                       ∎
              in
              DS.resp-≈ S H≈ (H⊆T₂ $ H⊆T₁ $ H⊆Sₜ H∈)
      in
      (S , S.is-local Sᵣ (R₊ S) HS′) , idᶠ
      where open D.HomReasoning
            open MR D.Cat

--     module _
--       {o′ ℓ′ : Level}
--       (F : CSheaf S o′ ℓ′)
--       where

--       private
--         module F = CSheaf F
--         open CSheaf
--         open Setoid

--         FH = F.homomorphism

--         RL⋆≈η : R.₁ L⋆.! C.∘ R⋆.! C.≈ unit.η _
--         RL⋆≈η = begin
--           R.₁ L⋆.! C.∘ R⋆.!                 ≈⟨ refl⟩∘⟨ R⋆.!-unique₂ ⟩
--           R.₁ L⋆.! C.∘ R.₁ D.! C.∘ unit.η _ ≈⟨ pullˡ (⟺ R.homomorphism) ⟩
--           R.₁ (L⋆.! D.∘ D.!) C.∘ unit.η _   ≈⟨ R.F-resp-≈ L⋆.!-unique₂ ⟩∘⟨refl ⟩
--           R.₁ D.id C.∘ unit.η _             ≈⟨ elimˡ R.identity ⟩
--           unit.η _                          ∎
--           where open C.HomReasoning
--                 open MR C.Cat

--         Radjunct-lemma : ∀ {X} {z : C.⋆ C.⇒ R.₀ X} → R.₁ (Radjunct z D.∘ L⋆.!) C.∘ R⋆.! C.≈ z
--         Radjunct-lemma {z = z} = begin
--           R.₁ (Radjunct z D.∘ L⋆.!) C.∘ R⋆.!     ≈⟨ C.∘-resp-≈ˡ RH ○ C.assoc ⟩
--           R.₁ (Radjunct z) C.∘ R.₁ L⋆.! C.∘ R⋆.! ≈⟨ refl⟩∘⟨ RL⋆≈η ⟩
--           Ladjunct (Radjunct z)                  ≈⟨ LRadjunct≈id ⟩
--           z                                      ∎
--           where open C.HomReasoning

--       LiftSheaf : CSheaf LiftSite o′ ℓ′
--       LiftSheaf .Psh = F.Psh ∘F R.op
--       LiftSheaf .is-sheaf {U} fs p matching =
--         mkUnique (uniq-section .witness) section′ unique′
--         where
--           p′ = λ i → F.₁ (unit.η _) .to (p i)
--           matching′ : F.is-matching (S.cover fs) p′
--           matching′ {K = K} {i = i} {j} f g H≈ = begin
--             F.₁ f .to (F.₁ (unit.η _) .to (p i))        ≈⟨ FK.sym FH ○ (F.F-resp-≈ (unit.commute f) ○ FH) ⟩
--             F.₁ (unit.η _) .to (F.₁ (RL.₁ f) .to (p i)) ≈⟨ F.₁ (unit.η _) .cong (matching (L.₁ f) (L.₁ g) H≈′) ⟩
--             F.₁ (unit.η _) .to (F.₁ (RL.₁ g) .to (p j)) ≈⟨ FK.sym FH ○ (F.F-resp-≈ (unit.sym-commute g) ○ FH) ⟩
--             F.₁ g .to (F.₁ (unit.η _) .to (p j))        ∎
--             where open SetoidR (F.₀ K)
--                   module FK = Setoid (F.₀ K)
--                   _○_ = FK.trans
--                   H≈′ = D.assoc DR.○ D.∘-resp-≈ʳ (DR.⟺ LH DR.○ L.F-resp-≈ H≈ DR.○ LH) DR.○ D.sym-assoc
--           uniq-section : ∃! (F.₀ (R.₀ U)) (F.is-section (S.cover fs) p′)
--           uniq-section = F.is-sheaf fs p′ matching′
--           section′ : F.is-section _ p (uniq-section .witness)
--           section′ i = F.is-concrete λ {x} →
--             let j , u , H≈u = S.is-concrete fs (R.₁ (Radjunct (S.cov fs i)) C.∘ x)
--                 H≈u′ = DR.begin
--                   Radjunct (S.cov fs j) D.∘ L.₁ u              DR.≈⟨ D.assoc DR.○ D.∘-resp-≈ʳ (DR.⟺ LH) ⟩
--                   Radjunct (S.cov fs j C.∘ u)                  DR.≈⟨ DR.refl⟩∘⟨ L.F-resp-≈ (CR.⟺ H≈u) ⟩
--                   Radjunct (R.₁ (Radjunct (S.cov fs i)) C.∘ x) DR.≈⟨ D.∘-resp-≈ʳ LH DR.○ DM.extendʳ (counit.commute _) ⟩
--                   Radjunct (S.cov fs i) D.∘ Radjunct x         DR.∎
--             in begin
--               F.₁ x .to (F.₁ (R.₁ (Radjunct (S.cov fs i))) .to _)   ≈⟨ F.X.sym FH ○ (F.F-resp-≈ H≈u ○ FH) ⟩
--               F.₁ u .to (F.₁ (S.cov fs j) .to _)                    ≈⟨ F.F₁ u .cong (uniq-section .has-prop j) ⟩
--               F.₁ u .to (F.₁ (unit.η _) .to (p j))                  ≈⟨ F.X.sym FH ○ (F.F-resp-≈ (unit.commute u) ○ FH) ⟩
--               F.₁ (unit.η _) .to (F.₁ (RL.₁ u) .to (p j))           ≈⟨ F.₁ (unit.η _) .cong (matching _ _ H≈u′) ⟩
--               F.₁ (unit.η _) .to (F.₁ (R.₁ (Radjunct x)) .to (p i)) ≈⟨ F.X.sym FH ○ F.F-resp-≈ LRadjunct≈id ⟩
--               F.₁ x .to (p i) ∎
--             where open SetoidR (F.₀ C.⋆)
--                   module DM = MR D.Cat
--                   _○_ = F.X.trans
--           module FU = Setoid (F.₀ (R.₀ U))
--           unique′ : ∀ s → F.is-section _ p s → uniq-section .witness FU.≈ s
--           unique′ s Hs = uniq-section .unique s λ i →
--             let module FD = Setoid (F.₀ (S.dom fs i))
--                 _○_ = FD.trans
--             in F.F-resp-≈ (CR.⟺ LRadjunct≈id) ○ (FH ○ F.F₁ (unit.η _) .cong (Hs i))
--       LiftSheaf .is-concrete {x = x} {y} H≈ =
--         F.is-concrete λ {z} → begin
--           F.₁ z .to x                      ≈⟨ F.F-resp-≈ (CR.⟺ Radjunct-lemma) ○ FH ⟩
--           F.₁ R⋆.! .to (F.₁ (R.₁ _) .to x) ≈⟨ F.₁ R⋆.! .cong H≈ ⟩
--           F.₁ R⋆.! .to (F.₁ (R.₁ _) .to y) ≈⟨ F.X.sym FH ○ F.F-resp-≈ Radjunct-lemma ⟩
--           F.₁ z .to y                      ∎
--         where open SetoidR (F.₀ C.⋆)
--               _○_ = F.X.trans

-- module Pull {o ℓ e p i : Level}
--   {𝒞 : CCat o ℓ e}
--   (S₁ : CSite 𝒞 p i)
--   (S₂ : CSite 𝒞 p i)
--   where

--   private
--     open CSite
--     open CCat 𝒞
--     module S₁ = CSite S₁
--     module S₂ = CSite S₂

--     open HomReasoning
--     open MR Cat
--     open Pullback

--   module _
--     (pullback : {U : Obj} (fs : S₁.covers U) (gs : S₂.covers U) →
--                 ∀ i j → Pullback Cat (S₁.cov fs i) (S₂.cov gs j))
--     where

--     PullSite : CSite 𝒞 p i
--     PullSite .covers U = S₁.covers U × S₂.covers U
--     PullSite .cover (fs , gs) = record
--       { index = S₁.cover fs .index × S₂.cover gs .index
--       ; arr = λ (i , j) → S₁.cov fs i ∘ pullback fs gs i j .p₁
--       }
--     PullSite .is-stable g (fs , gs) =
--       let fs′ , pb-prop₁ = S₁.is-stable g fs
--           gs′ , pb-prop₂ = S₂.is-stable g gs
--       in (fs′ , gs′) , λ (j₁ , j₂) →
--         let i₁ , k₁ , comm₁ = pb-prop₁ j₁
--             i₂ , k₂ , comm₂ = pb-prop₂ j₂
--             pb₁ = pullback fs gs i₁ i₂
--             pb₂ = pullback fs′ gs′ j₁ j₂
--             uni = pb₁ .universal $ begin
--               S₁.cov fs i₁ ∘ k₁ ∘ p₁ pb₂ ≈⟨ extendʳ (⟺ comm₁) ⟩
--               g ∘ S₁.cov fs′ j₁ ∘ p₁ pb₂ ≈⟨ refl⟩∘⟨ commute pb₂ ⟩
--               g ∘ S₂.cov gs′ j₂ ∘ p₂ pb₂ ≈⟨ extendʳ comm₂ ⟩
--               S₂.cov gs i₂ ∘ k₂ ∘ p₂ pb₂ ∎
--             H≈ = begin
--               g ∘ S₁.cov fs′ j₁ ∘ p₁ pb₂    ≈⟨ extendʳ comm₁ ⟩
--               S₁.cov fs i₁ ∘ k₁ ∘ p₁ pb₂    ≈⟨ refl⟩∘⟨ ⟺ (p₁∘universal≈h₁ pb₁) ⟩
--               S₁.cov fs i₁ ∘ p₁ pb₁ ∘ uni   ≈⟨ sym-assoc ⟩
--               (S₁.cov fs i₁ ∘ p₁ pb₁) ∘ uni ∎
--         in
--         (i₁ , i₂) , uni , H≈
--     PullSite .is-concrete (fs , gs) x =
--       let n₁ , y₁ , H≈₁ = S₁.is-concrete fs x
--           n₂ , y₂ , H≈₂ = S₂.is-concrete gs x
--           pb = pullback fs gs n₁ n₂
--           y = pb .universal (⟺ H≈₁ ○ H≈₂)
--           H≈ = begin
--             x                          ≈⟨ H≈₁ ⟩
--             S₁.cov fs n₁ ∘ y₁          ≈⟨ refl⟩∘⟨ ⟺ (p₁∘universal≈h₁ pb) ⟩
--             S₁.cov fs n₁ ∘ p₁ pb ∘ y   ≈⟨ sym-assoc ⟩
--             (S₁.cov fs n₁ ∘ p₁ pb) ∘ y ∎
--       in
--       (n₁ , n₂) , y , H≈

--     module _
--       {o′ ℓ′ : Level}
--       (F : CSheaf S₁ (o′ ⊔ ℓ′) ℓ′)
--       -- (G : CSheaf S₂ (o′ ⊔ ℓ′) ℓ′)
--       -- (H : Presheaf Cat (Setoids (o′ ⊔ ℓ′) ℓ′))
--       where

--       private
--         open CSheaf
--         module F = CSheaf F
--         -- module G = CSheaf G
--         -- module H = Functor H
--         -- module FC = FinitelyComplete (Presheaves-FinitelyComplete Cat ℓ₀ ℓ₀ ℓ₀ o′ ℓ′)

--       -- module _
--       --   (nt₁ : NaturalTransformation (F.Psh) H)
--       --   (nt₂ : NaturalTransformation (G.Psh) H)
--       --   where

--       --   module nt₁ = NaturalTransformation nt₁
--       --   module nt₂ = NaturalTransformation nt₂

--       --   abstract
--       --     PB : Pullback (Presheaves Cat) nt₁ nt₂
--       --     PB = FC.pullback nt₁ nt₂

--       --   module PB = Pullback PB
--       --   module FG = Functor PB.P

--       --   module PB₂ = NaturalTransformation PB.p₂

--       PullSheaf : CSheaf PullSite (o′ ⊔ ℓ′) ℓ′
--       PullSheaf .Psh = F.Psh
--       PullSheaf .is-sheaf (fs , gs) p matching =
--         let p′ : F.Parts (S₁.cover fs)
--             p′ = λ i → {!!}
--         --     foo : F.is-matching (S₁.cover fs) p1
--         --     foo = ?
--         in
--         {!!}
--       PullSheaf .is-concrete = {!!}
