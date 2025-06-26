module Lib.Categories.Concrete where

-- Our definitions of concrete categories, sites, and sheaves.

open import Lib.Prelude renaming (_∘_ to _∘ᶠ_) hiding (⋃ ; _∈_ ; refl ; sym ; [_])

open import Categories.Adjoint using (Adjoint ; _⊣_)
open import Categories.Adjoint.RAPL using (rapl)
open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Diagram.Empty using (empty)
open import Categories.Diagram.Pullback using (Pullback ; IsPullback)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Hom
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.Functor.Properties using (Faithful)
open import Categories.Object.Terminal using (Terminal ; IsTerminal)
open import Categories.Object.Terminal.Limit using (limit⇒⊤ ; ⊤⇒limit)

import Categories.Morphism.Reasoning as MR

open import Function using (Func)
open import Function.Construct.Setoid as FnS using (_∙_)
open import Function.Properties.Inverse using (Inverse⇒Injection)

open import Relation.Unary using (_∈_ ; _⊆_ ; ⋃)
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
  -- Our definition of concrete categories differs from the agda-categories library
  -- in that we require a terminal object (following Matache et al.).
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


module _ {o ℓ e : Level} (𝒞 : CCat o ℓ e) where
  open CCat 𝒞

  record Cover (U : Obj) (i : Level) : Set (o ⊔ ℓ ⊔ lsuc i) where
    field
      {index} : Set i
      {domain} : index → Obj
      arr : ∀ i → domain i ⇒ U

  open Cover

  record CSite (p i : Level) : Set (o ⊔ ℓ ⊔ e ⊔ lsuc (p ⊔ i)) where
    field
      covers : Obj → Set p
      cover  : ∀ {U} → covers U → Cover U i

    dom : {U : Obj} (fs : covers U) → index (cover fs) → Obj
    dom fs i = domain (cover fs) i
    
    cov : {U : Obj} (fs : covers U) → ∀ i → dom fs i ⇒ U
    cov fs = cover fs .arr

    field
      is-stable :
        ∀ {Y Z} (g : Y ⇒ Z) (fs : covers Z)
        → ---------------------------------
        ∃ λ hs → ∀ j → ∃₂ λ i k →
        g ∘ cov hs j ≈ cov fs i ∘ k
  
      is-concrete :
        ∀ {U} (fs : covers U) (x : obj-set.Carrier U)
        → -------------------------------------------
        x ∈ ⋃ _ λ i → Im hom∣ cov fs i ∣

open Cover

module _ {o ℓ e : Level} {𝒞 : CCat o ℓ e} where
  open CCat 𝒞

  module Matching {o′ e′ : Level} (A : Presheaf Cat (Setoids o′ e′)) where 
    -- We define the property of being a sheaf, inspired by the definitions at
    -- https://1lab.dev/Cat.Site.Base.html

    private
      module A = Functor A
      module A₀ (U : Obj) = Setoid (A.₀ U)
  
    Parts : {i : Level} {U : Obj} (fs : Cover 𝒞 U i) → Set _
    Parts fs = ∀ i → A₀.Carrier (domain fs i)
  
    is-matching : {i : Level} {U : Obj} (fs : Cover 𝒞 U i) → Parts fs → Set _
    is-matching {U} fs p =
      ∀ {K} {i j} (f : K ⇒ domain fs i) (g : K ⇒ domain fs j)
      → fs .arr i ∘ f ≈ fs .arr j ∘ g
      → [ K ] A.₁ f .to (p i) ≈ A.₁ g .to (p j)
      where [_]_≈_ = A₀._≈_
  
    is-section : {i : Level} {U : Obj} (fs : Cover 𝒞 U i) → Parts fs → A₀.Carrier U → Set _
    is-section fs p s = ∀ i → [ _ ] A.₁ (fs .arr i) .to s ≈ p i
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
        ∀ {U} (fs : covers U) (p : Parts (fs .cover))
        (_ : is-matching (fs .cover) p)
        → -----------------------------------------
        ∃! (F₀ U) (is-section (fs .cover) p)
  
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

  module _ (G : Geom[ D.Cat , C.Cat ]) where
    open is-lex
    open Geom[_,_]

    private
      module L = Functor Inv[ G ]
      module R = Functor Dir[ G ]
      module LR = Functor (Inv[ G ] ∘F Dir[ G ])
      module RL = Functor (Dir[ G ] ∘F Inv[ G ])
      open Adjoint (Inv⊣Dir G)

      LH = L.homomorphism
      RH = R.homomorphism

      abstract
        R⋆-is-terminal : IsTerminal C.Cat (R.₀ D.⋆)
        R⋆-is-terminal = ⊤-is-terminal R⋆-terminal
          where
            open Terminal
            R⋆-terminal : Terminal C.Cat
            R⋆-terminal = limit⇒⊤ C.Cat $ rapl (Inv⊣Dir G) (empty _ o ℓ e) $ ⊤⇒limit D.Cat D.terminal

      R⋆-terminal = record { ⊤ = _ ; ⊤-is-terminal = R⋆-is-terminal}

      module R⋆ = IsTerminal (R⋆-is-terminal)
      module L⋆ = IsTerminal (Inv-lex G .pres-⊤ C.⋆-is-terminal)

    LiftSite : CSite 𝒟 p i
    LiftSite .covers c = S.covers $ R.₀ c
    LiftSite .cover fs = record { arr = Radjunct ∘ᶠ S.cov fs }
    LiftSite .is-stable g fs =
      let hs , pb-prop = S.is-stable (R.₁ g) fs
      in hs , λ j →
        let i , k , H≈ = pb-prop j
            H≈′ = begin
              g D.∘ Radjunct (S.cov hs j)                ≈⟨ extendʳ (counit.sym-commute g) ⟩
              counit.η _ D.∘ LR.₁ g D.∘ L.₁ (S.cov hs j) ≈⟨ refl⟩∘⟨ (⟺ LH ○ L.F-resp-≈ H≈ ○ LH) ⟩
              counit.η _ D.∘ L.₁ (S.cov fs i) D.∘ L.₁ k  ≈⟨ D.sym-assoc ⟩
              Radjunct (S.cov fs i) D.∘ L.₁ k            ∎
        in
        i , L.₁ k , H≈′
      where open D.HomReasoning
            open MR D.Cat
    LiftSite .is-concrete {U} T x =
      let n , y , H≈ = S.is-concrete T $ C.hom∣ R.₁ x ∣ .to R⋆.!
          y′ = D.hom∣ L.₁ y ∣ .to L⋆.! ; STn = S.cov T n
          H≈′ = begin
            x                                             ≈⟨ introʳ D.!-unique₂ ⟩
            x D.∘ Radjunct R⋆.! D.∘ L⋆.!                  ≈⟨ extendʳ (extendʳ (counit.sym-commute _)) ⟩
            counit.η _ D.∘ (LR.₁ x D.∘ L.₁ R⋆.!) D.∘ L⋆.! ≈⟨ refl⟩∘⟨ (⟺ LH ○ L.F-resp-≈ H≈ ○ LH) ⟩∘⟨refl ⟩
            counit.η _ D.∘ (L.₁ STn D.∘ L.₁ y) D.∘ L⋆.!   ≈⟨ assoc²δγ ⟩
            D.hom∣ Radjunct STn ∣ .to y′                  ∎
      in
      n , y′ , H≈′
      where open D.HomReasoning
            open MR D.Cat

    module _
      {o′ ℓ′ : Level}
      (F : CSheaf S o′ ℓ′)
      where

      private
        module F = CSheaf F
        open CSheaf
        open Setoid

        FH = F.homomorphism

        RL⋆≈η : R.₁ L⋆.! C.∘ R⋆.! C.≈ unit.η _
        RL⋆≈η = begin
          R.₁ L⋆.! C.∘ R⋆.!                 ≈⟨ refl⟩∘⟨ R⋆.!-unique₂ ⟩
          R.₁ L⋆.! C.∘ R.₁ D.! C.∘ unit.η _ ≈⟨ pullˡ (⟺ R.homomorphism) ⟩
          R.₁ (L⋆.! D.∘ D.!) C.∘ unit.η _   ≈⟨ R.F-resp-≈ L⋆.!-unique₂ ⟩∘⟨refl ⟩
          R.₁ D.id C.∘ unit.η _             ≈⟨ elimˡ R.identity ⟩
          unit.η _                          ∎
          where open C.HomReasoning
                open MR C.Cat

        module _ {U : C.Obj} where
          private
            module F1 = Setoid (F.₀ U)
            module F2 = Setoid (F.₀ (RL.₀ U))
          Fη-injective : ∀ {s t} → F.₁ (unit.η U) .to s F1.≈ F.₁ (unit.η U) .to t → s F2.≈ t
          Fη-injective {s} {t} H≈ =
            let step1 : (∀ {z} → F.₁ (unit.η _ C.∘ z) .to s F.X.≈ F.₁ (unit.η _ C.∘ z) .to t) → ∀ {z} → F.₁ z .to s F.X.≈ F.₁ z .to t
                step1 = {!!}
                step2 : ∀ {z} → F.₁ (unit.η _ C.∘ z) .to s F.X.≈ F.₁ z .to (F.₁ (unit.η _) .to t)
                step2 = {!!}
            in
            F.is-concrete $ step1 λ {z} → {!!}
              -- F.X.trans (F.F-resp-≈ H≈′) $
              -- F.X.trans FH $
              -- {!!}

        Radjunct-lemma₁ : ∀ {X} {z : C.⋆ C.⇒ R.₀ X} → R.₁ (Radjunct z D.∘ L⋆.!) C.∘ R⋆.! C.≈ z
        Radjunct-lemma₁ {z = z} = begin
          R.₁ (Radjunct z D.∘ L⋆.!) C.∘ R⋆.!     ≈⟨ C.∘-resp-≈ˡ RH ○ C.assoc ⟩ 
          R.₁ (Radjunct z) C.∘ R.₁ L⋆.! C.∘ R⋆.! ≈⟨ refl⟩∘⟨ RL⋆≈η ⟩
          Ladjunct (Radjunct z)                  ≈⟨ LRadjunct≈id ⟩
          z                                      ∎
          where open C.HomReasoning

        Radjunct-lemma₂ : ∀ {X} {z : D.⋆ D.⇒ X} → Radjunct (R.F₁ z C.∘ R⋆.!) D.∘ L⋆.! D.≈ z
        Radjunct-lemma₂ {z = z} = begin
          Radjunct (R.F₁ z C.∘ R⋆.!) D.∘ L⋆.!      ≈⟨ D.∘-resp-≈ʳ (L.F-resp-≈ H≈) ⟩∘⟨refl ⟩
          Radjunct (Ladjunct (z D.∘ D.!)) D.∘ L⋆.! ≈⟨ RLadjunct≈id ⟩∘⟨refl ⟩ 
          (z D.∘ D.!) D.∘ L⋆.!                     ≈⟨ D.assoc ○ elimʳ D.!-unique₂ ⟩
          z                                        ∎
          where
            open D.HomReasoning
            open MR D.Cat
            module CR = C.HomReasoning
            H≈ = C.∘-resp-≈ʳ R⋆.!-unique₂ CR.○ C.sym-assoc CR.○ C.∘-resp-≈ˡ (CR.⟺ RH)

      LiftSheaf : CSheaf LiftSite o′ ℓ′
      LiftSheaf .Psh = F.Psh ∘F R.op
      LiftSheaf .is-sheaf {U} fs p matching = mkUnique witness′ section′ unique′
        where
          p′ = λ i → F.₁ (unit.η _) .to (p i)
          matching′ : F.is-matching (S.cover fs) p′
          matching′ {K = K} {i = i} {j} f g H≈ = begin
            F.₁ f .to (F.₁ (unit.η _) .to (p i))        ≈⟨ FK.sym FH ○ F.F-resp-≈ (unit.commute f) ○ FH ⟩
            F.₁ (unit.η _) .to (F.₁ (RL.₁ f) .to (p i)) ≈⟨ F.₁ (unit.η _) .cong (matching (L.₁ f) (L.₁ g) H≈′) ⟩
            F.₁ (unit.η _) .to (F.₁ (RL.₁ g) .to (p j)) ≈⟨ FK.sym FH ○ F.F-resp-≈ (unit.sym-commute g) ○ FH ⟩
            F.₁ g .to (F.₁ (unit.η _) .to (p j))        ∎
            where
              open SetoidR (F.₀ K)
              module FK = Setoid (F.₀ K)
              module DR = D.HomReasoning
              infixr 5 _○_
              _○_ = FK.trans
              H≈′ = D.assoc DR.○ D.∘-resp-≈ʳ (DR.⟺ LH DR.○ L.F-resp-≈ H≈ DR.○ LH) DR.○ D.sym-assoc
          abstract
            uniq-section : ∃! (F.₀ (R.₀ U)) (F.is-section (S.cover fs) p′)
            uniq-section = F.is-sheaf fs p′ matching′
          module FU = Setoid (F.₀ (R.₀ U))
          witness′ = uniq-section .witness
          section′ : F.is-section _ p witness′
          section′ i =
            let H≈ = uniq-section .has-prop i
                w′ = witness′
                foo = begin
                  F.₁ (unit.η _) .to (F.₁ (R.₁ (Radjunct (S.cov fs i))) .to witness′) ≈⟨ {!!} ⟩
                  F.₁ (Ladjunct (Radjunct (S.cov fs i))) .to witness′                 ≈⟨ {!!} ⟩
                  F.₁ (S.cov fs i) .to witness′                                       ≈⟨ {!!} ⟩
                  F.₁ (unit.η _) .to (p i)                                            ∎
            in {!!}
              -- begin
              -- F.₁ (R.₁ (Radjunct (S.cov fs i))) .to witness′ ≈⟨ {!!} ⟩
              -- -- F.₁ (unit.η _ C.∘ R.₁ (LR.₁ (counit.η _))) .to (p i)  ≈⟨ ? ⟩
              -- F.₁ (R.₁ (counit.η _) C.∘ unit.η _) .to (p i)  ≈⟨ {!!} ⟩
              -- F.₁ C.id .to (p i)                             ≈⟨ {!!} ⟩
              -- p i                                            ∎
            where open SetoidR (F.₀ (S.dom fs i))
          unique′ : ∀ s → F.is-section _ p s → witness′ FU.≈ s
          unique′ s Hs = uniq-section .unique s λ i → {!!}
            -- uniq uniq-section λ i → {!!} -- Define at-most-one part of ∃! and separate out?
      LiftSheaf .is-concrete {x = x} {y} H≈ =
        F.is-concrete λ {z} → begin
          F.₁ z .to x                      ≈⟨ F.F-resp-≈ (CR.⟺ Radjunct-lemma₁) ○ FH ⟩
          F.₁ R⋆.! .to (F.₁ (R.₁ _) .to x) ≈⟨ F.₁ R⋆.! .cong H≈ ⟩
          F.₁ R⋆.! .to (F.₁ (R.₁ _) .to y) ≈⟨ F.X.sym FH ○ F.F-resp-≈ Radjunct-lemma₁ ⟩
          F.₁ z .to y                      ∎
        where open SetoidR (F.₀ C.⋆)
              module CR = C.HomReasoning
              _○_ = F.X.trans
