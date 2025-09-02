open import Lib.Algebra.Reals

module DPPL.Denotations (R : Reals₀) where

open import DPPL.Regularity
open import DPPL.Syntax R
open import DPPL.Typing R
open import DPPL.Properties.Syntax R

open import Lib.Cat.Concrete
open import Lib.Data.Dec
open import Lib.Data.Finset
open import Lib.Data.Vector
open import Lib.LocallyNameless.Unfinite
open import Lib.Syntax.Env

open import Cat.Prelude
open import Cat.Cartesian
open import Cat.Diagram.Exponential
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Product.Finite
open import Cat.Diagram.Product.Indexed
open import Cat.Site.Base

open import Data.Fin.Base hiding (_≤_)
open import Data.List.Base

open import Order.Lattice

open Reals R using (ℝ)

open SyntaxVars
open Reg↓≤ hiding (Ob)
open is-lattice Reg↓-lattice hiding (_∪_ ; ! ; top)

record is-DPPL-model {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  field
    has-cartesian : Cartesian-category C
    has-is-closed : Cartesian-closed C has-cartesian
    has-coprods   : has-coproducts C

  open Cartesian-category has-cartesian public
  open Cartesian-closed   has-is-closed public renaming ([_,_] to _⇒_)
  open Binary-coproducts C has-coprods  public hiding (unique₂)

  module ip {n} (F : Fin n → Ob) =
    Indexed-product (Cartesian→standard-finite-products terminal products F)

  𝔇 : Type o
  𝔇 = Ob

  field
    𝔇ℝ[_] : Reg↓ → 𝔇
    𝔇-real : ℝ → ∀ {c} → Hom top 𝔇ℝ[ c ]
    𝔇-prim
      : {cs : Reg↓ ^ PrimAr ϕ} → PrimTy ϕ ≡ (cs , c)
      → Hom (ip.ΠF λ i → 𝔇ℝ[ cs i ]) 𝔇ℝ[ c ]
    𝔇-if  : Hom 𝔇ℝ[ P↓ ] (top ⊕₀ top)
    -- 𝔇-diff :
    𝔇-promote
      : {cs : Reg↓ ^ n}
      → Hom (ip.ΠF λ i → 𝔇ℝ[ cs i ]) 𝔇ℝ[ c ]
      → Hom (ip.ΠF λ i → 𝔇ℝ[ c' ∩ cs i ]) 𝔇ℝ[ c' ∩ c ]
    𝔇-sub : c ≤ c' → Hom 𝔇ℝ[ c ] 𝔇ℝ[ c' ]

DPPL-model : ∀ o ℓ → Type (lsuc (o ⊔ ℓ))
DPPL-model o ℓ = Σ (Precategory o ℓ) is-DPPL-model 

module Denotations {o ℓ} (model : DPPL-model o ℓ) where
  open is-DPPL-model (model .snd)

  Ty-denot : Ty → 𝔇
  Ty-denot (treal c)        = 𝔇ℝ[ c ]
  Ty-denot (T₁ ⇒[ det ] T₂) = Ty-denot T₁ ⇒ Ty-denot T₂
  Ty-denot (ttup n Ts)      = ip.ΠF λ i → Ty-denot (Ts i)
  -- Distributions are interpreted trivially for the time being.
  Ty-denot (tdist _)        = top
  Ty-denot (_ ⇒[ rnd ] _)   = top

  instance
    ⟦⟧-Ty : ⟦⟧-notation Ty
    ⟦⟧-Ty = brackets _ Ty-denot

  open EnvDenot has-cartesian Ty-denot

  open TypingVars
  open FinsetSyntax hiding ([_])

  Sub-denot : T <: T' → Hom ⟦ T ⟧ ⟦ T' ⟧
  Sub-denot (sreal H≤)             = 𝔇-sub H≤
  Sub-denot (stup {Ts' = Ts'} H<:) = ip.tuple _ λ i → Sub-denot (H<: i) ∘ ip.π _ i
  Sub-denot (sarr {e' = rnd} H<: H<:' H≤)      = !
  Sub-denot (sarr {e = det} {det} H<: H<:' H≤) =
    [-,-]₁ _ _ has-is-closed (Sub-denot H<:') (Sub-denot H<:)
  Sub-denot (sdist H<:) = !

  Tm-denot : Γ ⊢ t :[ c , det ] T → Hom ⟦ Γ ⟧ ⟦ c ∩ᵗ T ⟧
  Tm-denot {Γ = Γ} (tvar {T = T} H∈ H≤) =
    subst (λ T → Hom ⟦ Γ ⟧ ⟦ T ⟧) (sym $ ≤ᵗ→∩ᵗ {T = T} H≤) (env-lookup {Γ = Γ} H∈)
  Tm-denot (tlam {e = rnd} Hlam) = !
  Tm-denot {Γ = Γ} {c = c} (tlam {T = T} {det} {T'} (Иi As Hty))
    with (a , H∉) ← fresh{𝔸} (As ∪ env-dom Γ) =
    ƛ $ subst (λ Γ → Hom ⟦ Γ ⟧ ⟦ c ∩ᵗ T' ⟧)
        (env-nub-cons Γ (∉∪₂ As H∉)) (Tm-denot (Hty a ⦃ ∉∪₁ H∉ ⦄))
  Tm-denot (tapp Hty Hty₁)          = ev ∘ ⟨ Tm-denot Hty , Tm-denot Hty₁ ⟩
  Tm-denot (tprim {cs = cs} Hϕ Hty) = 𝔇-promote {cs = cs} (𝔇-prim Hϕ) ∘ Tm-denot Hty
  Tm-denot (treal {r = r})          = 𝔇-real r ∘ !
  Tm-denot (ttup {Ts = Ts} Htys)    = ip.tuple _ λ i → Tm-denot (Htys i)
  Tm-denot (tproj {Ts = Ts} i Hty)  = ip.π _ i ∘ Tm-denot Hty
  Tm-denot (tif Hty Hty₁ Hty₂)      =
    [ Tm-denot Hty₁ , Tm-denot Hty₂ ] ∘ distr ∘ ⟨ 𝔇-if ∘ {!!} , id ⟩ -- Tm-denot Hty
    where
      distr : ∀ {X} → Hom ((top ⊕₀ top) ⊗₀ X) (X ⊕₀ X)
      distr = unlambda [ ƛ (ι₁ ∘ π₂) , ƛ (ι₂ ∘ π₂) ]
  Tm-denot (tdiff Hc Hty Hty₁)               = {!!}
  Tm-denot (tsolve Hty Hty₁ Hty₂)            = {!!}
  Tm-denot (tinfer Hty)                      = !
  Tm-denot (tsub {e = det} Hty _ H<:)        = {!!} ∘ Tm-denot Hty
  Tm-denot {Γ = Γ} (tpromote {T = T} Hty H≤) =
    subst (λ T → Hom ⟦ Γ ⟧ ⟦ T ⟧)
      (sym (ap (_∩ᵗ T) (∩-comm ∙ order→∩ H≤)) ∙ ∩ᵗ-action T)
      (Tm-denot Hty)
  Tm-denot {Γ = Γ} (tdemote {T = T} Hty H≤) =
    subst (λ T → Hom ⟦ Γ ⟧ ⟦ T ⟧)
      (sym (∩ᵗ-action T) ∙ ap (_∩ᵗ T) (∩-comm ∙ order→∩ H≤))
      (Tm-denot Hty)


--   -- ⟦_⟧ : Γ ⊢ t :[ e ] T → 𝔇-hom ⟦ Γ ⟧ᴱ ⟦ T ⟧ᵀ
--   -- ⟦ tvar {T = T} ⟧ = 𝔇π₂ {D₁ = 𝔇𝟙} {D₂ = ⟦ T ⟧ᵀ}
--   -- ⟦ tabs (Иi As Habs) ⟧ = 𝔇-curry ⟦ Habs (new As) {{unfinite As}} ⟧
--   -- ⟦ tapp Htype Htype₁ ⟧ = 𝔇-eval 𝔇∘ 𝔇⟨ ⟦ Htype ⟧ , ⟦ Htype₁ ⟧ ⟩
--   -- ⟦ tprim {ϕ = ϕ} {cs = cs} Hϕ _ Htypes ⟧ = 𝔇-prim Hϕ 𝔇∘ 𝔇∏⟨ ⟦_⟧ ∘ Htypes ⟩
--   -- ⟦ treal {r = r} ⟧ = 𝔇-const r
--   -- ⟦ ttup _ Htypes ⟧ = 𝔇∏⟨ ⟦_⟧ ∘ Htypes ⟩
--   -- ⟦ tproj {Ts = Ts} i Htype ⟧ = 𝔇π[_] {Ds = ⟦_⟧ᵀ ∘ Ts} i 𝔇∘ ⟦ Htype ⟧
--   -- ⟦ tif {T = T} Htype Htype₁ Htype₂ ⟧ =
--   --   if-denot {T = T} ⟦ Htype₁ ⟧ ⟦ Htype₂ ⟧ 𝔇∘ 𝔇⟨ ⟦ Htype ⟧ , 𝔇-id ⟩
--   -- ⟦ tdiff {cs = cs} H≤ Htype Htype₁ ⟧ =
--   --   𝔇-eval {D₁ = 𝔇ℝ′ cs} 𝔇∘
--   --   𝔇-map {D₂ = 𝔇ℝ′ cs} (𝔇-curry-hom 𝔇∘ 𝔇-diff H≤) 𝔇-id 𝔇∘
--   --   𝔇⟨ ⟦ Htype ⟧ , ⟦ Htype₁ ⟧ ⟩
--   -- ⟦ tsolve Htype Htype₁ Htype₂ x ⟧ = {!!}
--   -- ⟦ tdist x x₁ x₂ ⟧ = {!!}
--   -- ⟦ tassume Htype ⟧ = {!!}
--   -- ⟦ tweight Htype ⟧ = {!!}
--   -- ⟦ tinfer Htype x ⟧ = {!!}
--   -- ⟦ tweaken Htype x x₁ ⟧ = {!!}
--   -- ⟦ tsub Htype x x₁ ⟧ = {!!}
--   -- ⟦ tpromote Htype x ⟧ = {!!}

--     field
--       𝔉-const : (r : ℝ) → const r ∈ 𝔉 []
  
--       𝔉-proj : id ∈ 𝔉′ Θ Θ
  
--       𝔉-cond :
--         (λ θ → if (θ ₀ ≲? 0ᴿ) then θ ₁ else θ ₂)
--           ∈ 𝔉 (P ∷ c ∷ c ∷ [])
  
--       𝔉-sub :
--         {f : ℝ ^ n → ℝ}
--         (_ : ∀ i → π[ i ] Θ ≤′ π[ i ] Θ′)
--         (_ : c′ ≤′ c)
--         → -------------------------------
--         f ∈ 𝔉 Θ → f ∈ 𝔉 Θ′
  
      -- 𝔉-promote :
      --   {f : ℝ ^ n → ℝ}
      --   (_ : ∀ i → c′ ≤′ π[ i ] Θ)
      --   → ------------------------
      --   f ∈ 𝔉 Θ c → f ∈ 𝔉 Θ c′


-- open import Syntax R hiding (n; m; D)
-- open import Typing R

-- open import Lib.Prelude hiding (_∈_ ; _∷_ ; [])

-- open import Lib.Concrete.Concrete
-- open import Lib.Concrete.Construction
-- open import Lib.Concrete.Properties

-- open import Categories.Category using (Category)

-- open import Relation.Unary using (_∈_)

-- open import Lib.LocallyNameless.Unfinite
-- open import Lib.Env
-- open import Lib.Subvec
-- open import Lib.FunExt

-- open import Data.Fin using (splitAt)
-- open import Data.Fin.Properties using (toℕ<n)
-- open import Data.List.Relation.Unary.All as All using (All)
-- open import Data.Sum using ([_,_])
-- open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
-- open import Data.Vec.Functional
-- open import Relation.Unary using (_∈_; Pred; ⋃)
-- open import Relation.Binary using (Rel)

-- open import Function using (Func ; Injection ; Inverse)
-- open import Function.Properties.Inverse using (Inverse⇒Injection)
-- open import Relation.Binary.Bundles using (Setoid)
-- open import Function.Construct.Setoid as FuncS using (_∙_)
-- import Relation.Binary.Reasoning.Setoid as SetoidR

-- private
--   variable
--     n m : ℕ
--     Θ : Coeff ^ n
--     Θ′ : Coeff ^ m

-- record c-assumptions : Set₁ where
--   field
--     c-cat   : Coeff → CCat ℓ₀ ℓ₀ ℓ₀
--     c-site  : (c : Coeff) → CSite (c-cat c) ℓ₀ ℓ₀
--     c-sheaf : (c : Coeff) → CSheaf (c-site c) ℓ₀ ℓ₀

--     Θ-cat : CCat ℓ₀ ℓ₀ ℓ₀

--   module c-cat (c : Coeff) = CCat (c-cat c)
--   module Θ-cat = CCat Θ-cat

--   field
--     Θ-obj : Coeff ^ n → Θ-cat.Obj

--     c-proj : (c : Coeff) → Geom[ Θ-cat.Cat , c-cat.Cat c ]

-- module _ (c-ass : c-assumptions) where
--   open c-assumptions c-ass
--   open Pull
--   open Meet

--   Θc-site : (c : Coeff) → CSite Θ-cat ℓ₀ ℓ₀
--   Θc-site c = PullSite (c-site c) (c-proj c)

--   Θc-sheaf : (c : Coeff) → CSheaf (Θc-site c) ℓ₀ ℓ₀
--   Θc-sheaf c = PullSheaf (c-site c) (c-proj c) (c-sheaf c)

--   Θ-site : CSite Θ-cat ℓ₀ ℓ₀
--   Θ-site =
--     MeetSite (Θc-site A) $
--     MeetSite (Θc-site P)
--              (Θc-site N)

--   Θ-sheaf : CSheaf Θ-site ℓ₀ ℓ₀
--   Θ-sheaf = {!!}

--   𝔉 : (Θ : Coeff ^ n) → ℙ (ℝ ^ n → ℝ) ℓ₀
--   𝔉 Θ f = {!!} -- f ∈ R[ Θ-sheaf , Θ-obj Θ ]

--   𝔉′ : (Θ : Coeff ^ n) (Θ′ : Coeff ^ m) → ℙ (ℝ ^ n → ℝ ^ m) ℓ₀
--   𝔉′ Θ Θ′ f = {!!}

--   record 𝔉-assumptions : Set₁ where

--     field
--       𝔉-const : (r : ℝ) → const r ∈ 𝔉 []
  
--       𝔉-proj : id ∈ 𝔉′ Θ Θ
  
--       𝔉-cond :
--         (λ θ → if (θ ₀ ≲? 0ᴿ) then θ ₁ else θ ₂)
--           ∈ 𝔉 (P ∷ c ∷ c ∷ [])
  
--       𝔉-sub :
--         {f : ℝ ^ n → ℝ}
--         (_ : ∀ i → π[ i ] Θ ≤′ π[ i ] Θ′)
--         (_ : c′ ≤′ c)
--         → -------------------------------
--         f ∈ 𝔉 Θ → f ∈ 𝔉 Θ′
  
      -- 𝔉-promote :
      --   {f : ℝ ^ n → ℝ}
      --   (_ : ∀ i → c′ ≤′ π[ i ] Θ)
      --   → ------------------------
      --   f ∈ 𝔉 Θ c → f ∈ 𝔉 Θ c′


-- module 𝔉-lemmas (Ass : 𝔉-assumptions) where
--   open 𝔉-assumptions Ass

--   𝔉-const′ : (θ : ℝ ^ n) → const θ ∈ 𝔉′ Θ Θ′
--   𝔉-const′ θ i =
--     𝔉-compose {Θ′ = λ ()} {g = λ _ ()} (λ ()) $
--     𝔉-sub (λ ()) (≤-1 $ toℕ<n _) $
--     𝔉-const _

--   𝔉-compose′ :
--     {g : ℝ ^ n → ℝ ^ m}
--     {f : ℝ ^ m → ℝ ^ k}
--     (_ : g ∈ 𝔉′ Θ Θ′)
--     (_ : f ∈ 𝔉′ Θ′ Θ″)
--     → -----------------
--      f ∘ g ∈ 𝔉′ Θ Θ″
--   𝔉-compose′ Hg Hf = 𝔉-compose Hg ∘ Hf

--   𝔉-++ :
--     {f : ℝ ^ n → ℝ ^ m}
--     {g : ℝ ^ n → ℝ ^ k}
--     (_ : f ∈ 𝔉′ Θ Θ′)
--     (_ : g ∈ 𝔉′ Θ Θ″)
--     → ----------------------------------
--     (λ θ → f θ ++ g θ) ∈ 𝔉′ Θ (Θ′ ++ Θ″)
--   𝔉-++ {m = m} Hf Hg i with splitAt m i
--   ... | ι₁ i = Hf i
--   ... | ι₂ i = Hg i

--   𝔉-∷ :
--     {f : ℝ ^ n → ℝ}
--     {g : ℝ ^ n → ℝ ^ m}
--     (_ : f ∈ 𝔉 Θ c)
--     (_ : g ∈ 𝔉′ Θ Θ′)
--     → -------------------------------
--     (λ θ → f θ ∷ g θ) ∈ 𝔉′ Θ (c ∷ Θ′)
--   𝔉-∷ Hf Hg zero = Hf
--   𝔉-∷ Hf Hg (succ i) = Hg i

--   𝔉-papply :
--     {f : ℝ ^ (n + m) → ℝ}
--     (_ : f ∈ 𝔉 (Θ ++ Θ′) c)
--     (θ′ : ℝ ^ m)
--     → -------------------------
--     (λ θ → f (θ ++ θ′)) ∈ 𝔉 Θ c
--   𝔉-papply Hf θ =
--     𝔉-compose (𝔉-++ 𝔉-proj (𝔉-const′ _)) Hf

--   𝔉-proj′ : (H⊆ : Θ ⊆ Θ′) → proj-⊆ (H⊆ .π₁) ∈ 𝔉′ Θ′ Θ
--   𝔉-proj′ {Θ′ = Θ′} H⊆ i rewrite H⊆ .π₂ i = 𝔉-proj _

--   𝔉-weaken :
--     {f : ℝ ^ n → ℝ}
--     (H⊆ : Θ ⊆ Θ′)
--     → ---------------------------------------
--     f ∈ 𝔉 Θ c → f ∘ proj-⊆ (H⊆ .π₁) ∈ 𝔉 Θ′ c
--   𝔉-weaken H⊆ Hf = 𝔉-compose (𝔉-proj′ H⊆) Hf


-- record DenotAssumptions : Set₁ where
--   field
--     𝔉-ass : 𝔉-assumptions

--   open 𝔉-assumptions 𝔉-ass public
--   open 𝔉-lemmas 𝔉-ass public

--   field
--     ⟦_⟧ᴾ : (ϕ : Prim) → ℝ ^ PrimAr ϕ → ℝ

--     𝔉-prim :
--       {Θ : Coeff ^ PrimAr ϕ}
--       (_ : PrimTy ϕ ≡ (Θ , c))
--       → ----------------------
--       ⟦ ϕ ⟧ᴾ ∈ 𝔉 Θ c

--     𝐷 :
--       (f : ℝ ^ n → ℝ)
--       (_ : ∀ i → π[ i ] Θ ≤′ P)
--       (_ : f ∈ 𝔉 Θ c)
--       → -----------------------
--       ℝ ^ (n + n) → ℝ

--     𝔉-diff :
--       (f : ℝ ^ m → ℝ ^ n → ℝ)
--       (H≤ : ∀ i → π[ i ] Θ ≤′ P)
--       (Hf₀ : (λ θ → f (take _ θ) (drop _ θ)) ∈ 𝔉 (Θ′ ++ Θ) c)
--       (Hf₁ : (θ : ℝ ^ m) → f θ ∈ 𝔉 Θ c)
--       -- Note: Hf₀ actually implies Hf₁, but this formulation is easier to work with
--       -- than the one deriving Hf₁ inside the proposition statement.
--       → -------------------------------------------------------------------------------
--       (λ θxv → 𝐷 _ H≤ (Hf₁ (take m θxv)) (drop m θxv)) ∈ 𝔉 (Θ′ ++ Θ ++ replicate n A) c

--     𝔉-diff′ :
--       (f : ℝ ^ n → ℝ)
--       (H≤ : ∀ i → π[ i ] Θ ≤′ P)
--       (Hf : f ∈ 𝔉 Θ c)
--       → ---------------------------------
--       𝐷 _ H≤ Hf ∈ 𝔉 (Θ ++ replicate n A) c


-- module Denotations (Ass : DenotAssumptions) where
--   open DenotAssumptions Ass

--   record S : Set₁ where
--     field
--       dim : ℕ
--       Θ⟨_⟩ : Coeff ^ dim
--       elems : Pred (ℝ ^ dim) ℓ₀

--     ∣_∣ₛ : Set
--     ∣_∣ₛ = ∃ elems

--   open S

--   S-is-hom : (s₁ s₂ : S) → Pred (∣ s₁ ∣ₛ → ∣ s₂ ∣ₛ) ℓ₀
--   S-is-hom s₁ s₂ f =
--     {n : ℕ} {Θ : Coeff ^ n}
--     {g : ℝ ^ n → ∣ s₁ ∣ₛ}
--     → -----------------------------------------------
--     π₁ ∘ g ∈ 𝔉′ Θ Θ⟨ s₁ ⟩ → π₁ ∘ f ∘ g ∈ 𝔉′ Θ Θ⟨ s₂ ⟩

--   S-is-hom : (s₁ s₂ : S) → Pred (∣ s₁ ∣ₛ → ∣ s₂ ∣ₛ) ℓ₀
--   S-is-hom s₁ s₂ f =
--     {n : ℕ} {Θ : Coeff ^ n}
--     {g : ∣ s₁ ∣ₛ → ℝ ^ n}
--     → -----------------------------------------------
--     π₁ ∘ g ∈ 𝔉′ Θ⟨ s₁ ⟩ Θ → π₁ ∘ f ∘ g ∈ 𝔉′ Θ⟨ s₂ ⟩ Θ

--   record S-hom (s₁ s₂ : S) : Set where
--     constructor mkS-hom
--     field
--       to : ∣ s₁ ∣ₛ → ∣ s₂ ∣ₛ
--       is-hom : to ∈ S-is-hom s₁ s₂

--   open S-hom

--   private
--     variable
--       s s₁ s₂ s₃ : S

--   S-id : S-hom s s
--   S-id .to = id
--   S-id .is-hom = id

--   _S∘_ : S-hom s₂ s₃ → S-hom s₁ s₂ → S-hom s₁ s₃
--   (f S∘ g) .to = f .to ∘ g .to
--   (f S∘ g) .is-hom = f .is-hom ∘ g .is-hom

--   record S-covering (s : S) : Set₁ where
--     field
--       count : ℕ
--       parts : (i : Fin count) → Pred (ℝ ^ s .dim) ℓ₀
--       is-cover : (x : ∣ s ∣ₛ) → ∃ λ i → π₁ x ∈ parts i

--   open S-covering

--   S-restrict : (s : S) → Pred (ℝ ^ s .dim) ℓ₀ → S
--   S-restrict s p .dim = s .dim
--   Θ⟨ S-restrict s p ⟩ = Θ⟨ s ⟩
--   S-restrict s p .elems x = x ∈ s .elems × x ∈ p

--   S-inject : (s : S) {p : Pred (ℝ ^ s .dim) ℓ₀} → ∣ S-restrict s p ∣ₛ → ∣ s ∣ₛ
--   S-inject s (x , H∈ , _) = x , H∈

--   S𝟙 : S
--   S𝟙 .dim = 0
--   Θ⟨ S𝟙 ⟩ ()
--   S𝟙 .elems _ = 𝟙

--   S𝟙-terminal : S-hom s S𝟙
--   S𝟙-terminal = {!!}

--   Sℝ : (c : Coeff) → S
--   Sℝ c .dim = 1
--   Θ⟨ Sℝ c ⟩ = const c
--   Sℝ c .elems _ = 𝟙

--   S-const : ℝ → S-hom S𝟙 (Sℝ c)
--   S-const r = {!!}

--   -- Our semantic domain, inspired by the paper
--   -- Concrete Categories for Higher-order Recursion (Matache et al.).
--   --
--   -- In terms of that paper, the idea is that our domains are concrete
--   -- sheaves over a site S whose objects are vectors of coeffects, and
--   -- whose morphisms Θ → Θ′ are functions (f : ℝ ^ n → ℝ ^ m) ∈ 𝔉′ Θ Θ′.
--   -- TODO: What is the coverage on the site?  Can it simply be trivial?
--   -- Should the objects be _subsets_ of ℝ ^ n tagged with vectors of
--   -- coeffects instead, and the coverage be the inclusion functions?
--   --
--   -- The semantics is also closely related to our previous logical
--   -- relations arguments, in that we can view each domain as a set
--   -- equipped with a parameterized predicate describing the
--   -- well-behaved maps into that domain.

--   record 𝔇 : Set₁ where
--     constructor mk𝔇
--     field
--       ∣_∣ : Set
--       R[_,_] : (s : S) → Pred (∣ s ∣ₛ → ∣_∣) ℓ₀

--       R[,]-const : (x : ∣_∣) → const x ∈ R[_,_] s

--       R[,]-compose :
--         {ϕ : ∣ s₂ ∣ₛ → ∣_∣}
--         (f : S-hom s₁ s₂)
--         → -----------------------------------
--         ϕ ∈ R[_,_] s₂ → ϕ ∘ f .to ∈ R[_,_] s₁

--       R[,]-cover :
--         {g : ∣ s ∣ₛ → ∣_∣}
--         (c : S-covering s)
--         (_ : ∀ i → g ∘ S-inject s ∈ R[_,_] (S-restrict s (c .parts i)))
--         → -------------------------------------------------------------
--         g ∈ R[_,_] s

--   open 𝔇

--   -- Conjecture: the previous semantics and this one are equivalent
--   -- under the following correspondence:

--   -- module Correspondence where
--   --   fwd :
--   --     (p : {n : ℕ} → Pred (Coeff ^ n) ℓ₀)
--   --     (pr : {m : ℕ} {Θ : Coeff ^ m} → p Θ → ℝ ^ m → p [])
--   --     → ---------------------------------------------------
--   --     ∃ λ X → {m : ℕ} → Coeff ^ m → Pred (ℝ ^ m → X) ℓ₀
--   --   fwd p pr = p [] , λ Θ f → ∑ f′ ∶ p Θ , pr f′ ≗ f

--   --   bwd :
--   --     {X : Set}
--   --     (_ : {m : ℕ} → Coeff ^ m → Pred (ℝ ^ m → X) ℓ₀)
--   --     → -----------------------------------------------
--   --     {n : ℕ} → Pred (Coeff ^ n) ℓ₀
--   --   bwd Hx = λ Θ → ∃ (Hx Θ)

--     -- Note that this is not a proper equivalence as the forward
--     -- direction requires a projection function from p Θ
--     -- to ℝ ^ m → p [].  Attempting to take this into account in the
--     -- reverse direction requires adding more hypotheses stating that
--     -- constant functions are plots, and furthermore that they are the
--     -- only plots of Hx [].  This gets a bit intricate, but I believe
--     -- the required hypotheses should hold for our case.


--   𝔇-is-hom : (D₁ D₂ : 𝔇) → Pred (∣ D₁ ∣ → ∣ D₂ ∣) ℓ₁
--   𝔇-is-hom D₁ D₂ f =
--     {s : S}
--     → ------------------------------------------
--     ∀ ϕ → ϕ ∈ R[ D₁ , s ] → f ∘ ϕ ∈ R[ D₂ , s ]

--   record 𝔇-hom (D₁ D₂ : 𝔇) : Set₁ where
--     field
--       to : ∣ D₁ ∣ → ∣ D₂ ∣
--       is-hom : 𝔇-is-hom D₁ D₂ to

--   open 𝔇-hom

--   private
--     variable
--       D D₁ D₂ D₃ D₄ : 𝔇

--   𝔇-id : 𝔇-hom D D
--   𝔇-id .to z = z
--   𝔇-id .is-hom _ Hϕ = Hϕ

--   infixr 4 _𝔇∘_
--   _𝔇∘_ : 𝔇-hom D₂ D₃ → 𝔇-hom D₁ D₂ → 𝔇-hom D₁ D₃
--   (f 𝔇∘ g) .to = f .to ∘ g .to
--   (f 𝔇∘ g) .is-hom _ = f .is-hom _ ∘ g .is-hom _

--   𝔇𝟙 : 𝔇
--   𝔇𝟙 = mk𝔇 𝟙 (λ _ _ → 𝟙) (λ _ → tt) (λ _ _ → tt) λ _ _ → tt

--   𝔇𝟙-terminal : 𝔇-hom D 𝔇𝟙
--   𝔇𝟙-terminal .to _ = tt
--   𝔇𝟙-terminal .is-hom _ _ = tt

--   𝔇ℝ : Coeff → 𝔇
--   𝔇ℝ c =
--     mk𝔇 ℝ
--       (λ s → {!!})
--       {!!} -- 𝔉-const′ {Θ′ = c ∷ []} (r ∷ []) ₀)
--       {!!} -- (λ Hf Hg → 𝔉-compose (Hf .is-hom) Hg)
--       {!!}

--   -- 𝔇-const : ℝ → 𝔇-hom 𝔇𝟙 (𝔇ℝ c)
--   -- 𝔇-const r .to _ = r
--   -- 𝔇-const r .is-hom _ _ = R[,]-const (𝔇ℝ _) r

--   -- 𝔇ℝ′ : Coeff ^ n → 𝔇
--   -- 𝔇ℝ′ Θ′ =
--   --   mk𝔇 (ℝ ^ _)
--   --     (λ s → 𝔉′ Θ⟨ s ⟩ Θ′)
--   --     𝔉-const′
--   --     (λ Hf Hg → 𝔉-compose′ (Hf .is-hom) Hg)

--   -- _𝔇×_ : 𝔇 → 𝔇 → 𝔇
--   -- ∣ D₁ 𝔇× D₂ ∣ = ∣ D₁ ∣ × ∣ D₂ ∣
--   -- R[ D₁ 𝔇× D₂ , s ] f = π₁ ∘ f ∈ R[ D₁ , s ] × π₂ ∘ f ∈ R[ D₂ , s ]
--   -- R[,]-const (D₁ 𝔇× D₂) (x₁ , x₂) = R[,]-const D₁ x₁ , R[,]-const D₂ x₂
--   -- R[,]-compose (D₁ 𝔇× D₂) Hf (Hϕ₁ , Hϕ₂) =
--   --   R[,]-compose D₁ Hf Hϕ₁ , R[,]-compose D₂ Hf Hϕ₂

--   -- 𝔇π₁ : 𝔇-hom (D₁ 𝔇× D₂) D₁
--   -- 𝔇π₁ .to = π₁
--   -- 𝔇π₁ .is-hom _ Hϕ = Hϕ .π₁

--   -- 𝔇π₂ : 𝔇-hom (D₁ 𝔇× D₂) D₂
--   -- 𝔇π₂ .to = π₂
--   -- 𝔇π₂ .is-hom _ Hϕ = Hϕ .π₂

--   -- 𝔇⟨_,_⟩ : 𝔇-hom D D₁ → 𝔇-hom D D₂ → 𝔇-hom D (D₁ 𝔇× D₂)
--   -- 𝔇⟨ d₁ , d₂ ⟩ .to z = d₁ .to z , d₂ .to z
--   -- 𝔇⟨ d₁ , d₂ ⟩ .is-hom ϕ Hϕ = d₁ .is-hom ϕ Hϕ , d₂ .is-hom ϕ Hϕ

--   -- 𝔇-map : 𝔇-hom D₁ D₃ → 𝔇-hom D₂ D₄ → 𝔇-hom (D₁ 𝔇× D₂) (D₃ 𝔇× D₄)
--   -- 𝔇-map f g .to (x , y) = f .to x , g .to y
--   -- 𝔇-map f g .is-hom ϕ (Hϕ₁ , Hϕ₂) = f .is-hom (π₁ ∘ ϕ) Hϕ₁ , g .is-hom (π₂ ∘ ϕ) Hϕ₂

--   -- 𝔇-assoc : (D₁ D₂ D₃ : 𝔇) → 𝔇-hom ((D₁ 𝔇× D₂) 𝔇× D₃) (D₁ 𝔇× (D₂ 𝔇× D₃))
--   -- 𝔇-assoc D₁ D₂ D₃ .to ((x , y) , z) = x , y , z
--   -- 𝔇-assoc D₁ D₂ D₃ .is-hom ϕ ((Hϕ₁ , Hϕ₂) , Hϕ₃) = Hϕ₁ , Hϕ₂ , Hϕ₃

--   -- 𝔇∏ : Vector 𝔇 n → 𝔇
--   -- ∣ 𝔇∏ Ds ∣ = (i : Fin _) → ∣ Ds i ∣
--   -- R[ 𝔇∏ Ds , s ] f = (i : Fin _) → (λ θ → f θ i) ∈ R[ Ds i , s ]
--   -- R[,]-const (𝔇∏ Ds) x i = R[,]-const (Ds i) (x i)
--   -- R[,]-compose (𝔇∏ Ds) Hf Hϕs i = R[,]-compose (Ds i) Hf (Hϕs i)

--   -- -- Note: ℝ ^ n ≡ ∏ᵢⁿ ℝ holds definitionally.
--   -- _ : 𝔇∏ (𝔇ℝ ∘ Θ) ≡ 𝔇ℝ′ Θ
--   -- _ = refl

--   -- 𝔇π[_] : {Ds : Vector 𝔇 n} → (i : Fin n) → 𝔇-hom (𝔇∏ Ds) (π[ i ] Ds)
--   -- 𝔇π[ i ] .to ds = ds i
--   -- 𝔇π[ i ] .is-hom _ Hϕ = Hϕ i

--   -- 𝔇∏⟨_⟩ : {Ds : Vector 𝔇 n} → ((i : Fin n) → 𝔇-hom D (Ds i)) → 𝔇-hom D (𝔇∏ Ds)
--   -- 𝔇∏⟨ ds ⟩ .to z i = ds i .to z
--   -- 𝔇∏⟨ ds ⟩ .is-hom ϕ Hϕ i = ds i .is-hom ϕ Hϕ

--   -- infixr 4 _𝔇⇒_
--   -- _𝔇⇒_ : 𝔇 → 𝔇 → 𝔇
--   -- ∣ D₁ 𝔇⇒ D₂ ∣ = 𝔇-hom D₁ D₂
--   -- R[ D₁ 𝔇⇒ D₂ , s ] f =
--   --   (λ (θ , d) → f θ .to d) ∈ 𝔇-is-hom (𝔇ℝ′ Θ⟨ s ⟩ 𝔇× D₁) D₂
--   -- R[,]-const (D₁ 𝔇⇒ D₂) f ϕ Hϕ = f .is-hom (π₂ ∘ ϕ) (Hϕ .π₂)
--   -- R[,]-compose (D₁ 𝔇⇒ D₂) Hf Hϕ₀ ϕ Hϕ =
--   --   Hϕ₀ _ (𝔉-compose′ (Hϕ .π₁) (Hf .is-hom) , Hϕ .π₂)

--   -- 𝔇-eval : 𝔇-hom ((D₁ 𝔇⇒ D₂) 𝔇× D₁) D₂
--   -- 𝔇-eval .to (f , x) = f .to x
--   -- 𝔇-eval .is-hom ϕ (Hϕ₁ , Hϕ₂) = Hϕ₁ _ (𝔉-proj , Hϕ₂)

--   -- 𝔇-curry : 𝔇-hom (D 𝔇× D₁) D₂ → 𝔇-hom D (D₁ 𝔇⇒ D₂)
--   -- 𝔇-curry f .to x .to y = f .to (x , y)
--   -- 𝔇-curry {D = D} f .to x .is-hom ϕ Hϕ =
--   --   f .is-hom _ (R[,]-const D x , Hϕ)
--   -- 𝔇-curry {D = D} f .is-hom ϕ Hϕ ϕ′ (Hϕ′₁ , Hϕ′₂) =
--   --   f .is-hom _ (R[,]-compose D (mkS-hom _ Hϕ′₁) Hϕ , Hϕ′₂)

--   -- 𝔇-curry-hom : 𝔇-hom ((D 𝔇× D₁) 𝔇⇒ D₂) (D 𝔇⇒ D₁ 𝔇⇒ D₂)
--   -- 𝔇-curry-hom {D = D} {D₁} {D₂} =
--   --   𝔇-curry (𝔇-curry (𝔇-eval 𝔇∘ 𝔇-assoc (D 𝔇× D₁ 𝔇⇒ D₂) D D₁))

--   -- 𝔇-uncurry : 𝔇-hom D (D₁ 𝔇⇒ D₂) → 𝔇-hom (D 𝔇× D₁) D₂
--   -- 𝔇-uncurry {D₁ = D₁} f = 𝔇-eval 𝔇∘ 𝔇-map {D₂ = D₁} f 𝔇-id

--   -- _𝔇⊎_ : 𝔇 → 𝔇 → 𝔇
--   -- ∣ D₁ 𝔇⊎ D₂ ∣ = ∣ D₁ ∣ ⊎ ∣ D₂ ∣
--   -- R[_,_] (D₁ 𝔇⊎ D₂) s f =
--   --   ({s′ : S} (f₁ : S-hom s′ s) (g : ∣ s′ ∣ₛ → ∣ D₁ ∣)
--   --    (_ : f ∘ f₁ .to ≗ ι₁ ∘ g)
--   --    → -----------------------------------------------
--   --    g ∈ R[ D₁ , s′ ])
--   --   ×
--   --   ({s′ : S} (f₂ : S-hom s′ s) (g : ∣ s′ ∣ₛ → ∣ D₂ ∣)
--   --    (_ : f ∘ f₂ .to ≗ ι₂ ∘ g)
--   --    → -----------------------------------------------
--   --    g ∈ R[ D₂ , s′ ])
--   -- R[,]-const (D₁ 𝔇⊎ D₂) x = Hl , Hr
--   --   where
--   --     Hl :
--   --       {s′ : S} (f₁ : S-hom s′ s) (g : ∣ s′ ∣ₛ → ∣ D₁ ∣)
--   --       (_ : const x ∘ f₁ .to ≗ ι₁ ∘ g)
--   --       → ------------------------------------------------
--   --       g ∈ R[ D₁ , s′ ]
--   --     Hl f₁ g Heq with refl ← Heq (const 0ᴿ) =
--   --       subst R[ D₁ , _ ] (funext $ inj₁-injective ∘ Heq) $ R[,]-const D₁ _
--   --     Hr :
--   --       {s′ : S} (f₂ : S-hom s′ s) (g : ∣ s′ ∣ₛ → ∣ D₂ ∣)
--   --       (_ : const x ∘ f₂ .to ≗ ι₂ ∘ g)
--   --       → ------------------------------------------------
--   --       g ∈ R[ D₂ , s′ ]
--   --     Hr f₂ g Heq with refl ← Heq (const 0ᴿ) =
--   --       subst R[ D₂ , _ ] (funext $ inj₂-injective ∘ Heq) $ R[,]-const D₂ _
--   -- R[,]-compose (D₁ 𝔇⊎ D₂) {ϕ = ϕ} f (Hϕ₁ , Hϕ₂) =
--   --   λ where
--   --     .π₁ f₁ → Hϕ₁ (f S∘ f₁)
--   --     .π₂ f₂ → Hϕ₂ (f S∘ f₂)

--   -- 𝔇-ι₁ : 𝔇-hom D D₁ → 𝔇-hom D (D₁ 𝔇⊎ D₂)
--   -- 𝔇-ι₁ f .to = ι₁ ∘ f .to
--   -- 𝔇-ι₁ {D = D} {D₁} {D₂} f .is-hom ϕ Hϕ = λ where
--   --   .π₁ f₁ g Heq →
--   --     subst R[ D₁ , _ ] (funext $ inj₁-injective ∘ Heq) $
--   --       f .is-hom _ (R[,]-compose D f₁ Hϕ)
--   --   .π₂ f₂ g Heq → case (Heq (const 0ᴿ)) λ ()

--   -- 𝔇-ι₂ : 𝔇-hom D D₂ → 𝔇-hom D (D₁ 𝔇⊎ D₂)
--   -- 𝔇-ι₂ f .to = ι₂ ∘ f .to
--   -- 𝔇-ι₂ {D = D} {D₁} {D₂} f .is-hom ϕ Hϕ = λ where
--   --   .π₁ f₁ g Heq → case (Heq (const 0ᴿ)) λ ()
--   --   .π₂ f₂ g Heq →
--   --     subst R[ D₁ , _ ] (funext $ inj₂-injective ∘ Heq) $
--   --       f .is-hom _ (R[,]-compose D f₂ Hϕ)

--   -- -- This map seems somewhat tricky to define: we might need the
--   -- -- coverage assumption here.
--   -- 𝔇[_,_] : 𝔇-hom D₁ D → 𝔇-hom D₂ D → 𝔇-hom (D₁ 𝔇⊎ D₂) D
--   -- 𝔇[ f , g ] .to = [ f .to , g .to ]
--   -- 𝔇[ f , g ] .is-hom ϕ (Hϕ₁ , Hϕ₂) = {!!}

--   -- 𝔇-prim :
--   --   {Θ : Coeff ^ PrimAr ϕ}
--   --   (_ : PrimTy ϕ ≡ (Θ , c))
--   --   → ---------------------
--   --   𝔇-hom (𝔇ℝ′ Θ) (𝔇ℝ c)
--   -- 𝔇-prim {ϕ = ϕ} Hϕ .to = ⟦ ϕ ⟧ᴾ
--   -- 𝔇-prim Hϕ .is-hom ϕ′ Hϕ′ = 𝔉-compose Hϕ′ (𝔉-prim Hϕ)

--   -- 𝔇-diff :
--   --   {cs : Coeff ^ n}
--   --   {ds : Coeff ^ m}
--   --   (_ : ∀ i → π[ i ] cs ≤′ P)
--   --   → -----------------------------------------------------------------
--   --   𝔇-hom (𝔇ℝ′ cs 𝔇⇒ 𝔇ℝ′ ds) (𝔇ℝ′ cs 𝔇× 𝔇ℝ′ (replicate n A) 𝔇⇒ 𝔇ℝ′ ds)
--   -- 𝔇-diff H≤ .to f .to (x , v) i = 𝐷 _ H≤ (f .is-hom _ 𝔉-proj i) (x ++ v)
--   -- 𝔇-diff H≤ .to f .is-hom ϕ (Hϕ₁ , Hϕ₂) i =
--   --   𝔉-compose (𝔉-++ Hϕ₁ Hϕ₂) (𝔉-diff′ _ H≤ (f .is-hom _ 𝔉-proj i))
--   -- 𝔇-diff {n = n} {cs = cs} {ds} H≤ .is-hom {s₁} ϕ Hϕ {s} ϕ′ (Hϕ′₁ , Hϕ′₂ , Hϕ′₃) i =
--   --   let foo :
--   --        (λ x →
--   --          𝐷 (λ x₁ → ϕ (take _ x) .to x₁ i) H≤
--   --          (ϕ (take _ x) .is-hom _ 𝔉-proj i)
--   --          (drop (s₁ .dim) x)) ∈ 𝔉 (Θ⟨ s₁ ⟩ ++ cs ++ replicate n A) (ds i)
--   --       foo =
--   --         𝔉-diff (λ x y → ϕ x .to y i) H≤
--   --           {!!}
--   --           λ θ → ϕ θ .is-hom _ 𝔉-proj i
--   --   in
--   --   -- 𝔉-compose
--   --   --   -- {f = λ x →
--   --   --   --    𝐷 (λ x₁ → ϕ (take _ x) .to x₁ i) H≤
--   --   --   --    (ϕ (take _ x) .is-hom (λ z → z) 𝔉-proj i)
--   --   --   --    (drop _ x)}
--   --   --   (𝔉-++ Hϕ′₁ (𝔉-++ Hϕ′₂ Hϕ′₃))
--   --     {!!}
--   -- -- 𝔇-diff H≤ .to f .to x .is-hom ϕ Hϕ i =
--   -- --   𝔉-compose
--   -- --     (𝔉-++ (𝔉-const′ _) Hϕ)
--   -- --     (𝔉-diff′ _ H≤ (f .is-hom _ 𝔉-proj i))
--   -- -- 𝔇-diff H≤ .to f .is-hom ϕ Hϕ ϕ′ (Hϕ′₁ , Hϕ′₂) i =
--   -- --   𝔉-compose
--   -- --     (𝔉-++ (𝔉-compose′ Hϕ′₁ Hϕ) Hϕ′₂)
--   -- --     (𝔉-diff′ _ H≤ (f .is-hom _ 𝔉-proj i))
--   -- -- 𝔇-diff H≤ .is-hom ϕ Hϕ ϕ′ (Hϕ′₁ , Hϕ′₂) ϕ″ (Hϕ″₁ , Hϕ″₂) i = {!!}


--   -- ⟦_⟧ᵀ : Type → 𝔇
--   -- ⟦ treal c ⟧ᵀ = 𝔇ℝ c
--   -- ⟦ T₁ ⇒[ _ ] T₂ ⟧ᵀ = ⟦ T₁ ⟧ᵀ 𝔇⇒ ⟦ T₂ ⟧ᵀ
--   -- ⟦ ttup n Ts ⟧ᵀ = 𝔇∏ (⟦_⟧ᵀ ∘ Ts)
--   -- -- Distributions are interpreted trivially for the time being.
--   -- ⟦ tdist T ⟧ᵀ = ⟦ T ⟧ᵀ

--   -- ⟦_⟧ᴱ : TyEnv → 𝔇
--   -- ⟦ ε ⟧ᴱ = 𝔇𝟙
--   -- ⟦ Γ , _ ∶ T ⟧ᴱ = ⟦ Γ ⟧ᴱ 𝔇× ⟦ T ⟧ᵀ


--   -- -- Since we don't have general coproducts currently, it seems
--   -- -- that the denotation of if must be defined for the interpretation
--   -- -- of some type T instead of a general domain, so that we can
--   -- -- proceed by induction.
--   -- if-denot :
--   --   (_ : 𝔇-hom D ⟦ T ⟧ᵀ)
--   --   (_ : 𝔇-hom D ⟦ T ⟧ᵀ)
--   --   → ---------------------
--   --   𝔇-hom (𝔇ℝ P 𝔇× D) ⟦ T ⟧ᵀ
--   -- if-denot {T = treal c} d₁ d₂ .to (x , γ) = if x ≲? 0ᴿ then d₁ .to γ else d₂ .to γ
--   -- if-denot {T = treal c} d₁ d₂ .is-hom ϕ (Hϕ₁ , Hϕ₂) =
--   --   𝔉-compose
--   --     (𝔉-∷ Hϕ₁ (𝔉-∷ (d₁ .is-hom _ Hϕ₂) (𝔉-∷ {g = const λ()} (d₂ .is-hom _ Hϕ₂) λ())))
--   --     𝔉-cond
--   -- if-denot {D = D} {T = T₁ ⇒[ _ ] T₂} d₁ d₂ =
--   --   𝔇-curry $
--   --     if-denot {T = T₂} (𝔇-uncurry d₁) (𝔇-uncurry d₂) 𝔇∘ 𝔇-assoc (𝔇ℝ P) D ⟦ T₁ ⟧ᵀ
--   -- if-denot {T = ttup n Ts} d₁ d₂ =
--   --   let 𝔇π[_] = 𝔇π[_] {Ds = ⟦_⟧ᵀ ∘ Ts} in
--   --   𝔇∏⟨ (λ i → if-denot {T = Ts i} (𝔇π[ i ] 𝔇∘ d₁) (𝔇π[ i ] 𝔇∘ d₂)) ⟩
--   -- if-denot {T = tdist T} d₁ d₂ = if-denot {T = T} d₁ d₂


--   -- ⟦_⟧ : Γ ⊢ t :[ e ] T → 𝔇-hom ⟦ Γ ⟧ᴱ ⟦ T ⟧ᵀ
--   -- ⟦ tvar {T = T} ⟧ = 𝔇π₂ {D₁ = 𝔇𝟙} {D₂ = ⟦ T ⟧ᵀ}
--   -- ⟦ tabs (Иi As Habs) ⟧ = 𝔇-curry ⟦ Habs (new As) {{unfinite As}} ⟧
--   -- ⟦ tapp Htype Htype₁ ⟧ = 𝔇-eval 𝔇∘ 𝔇⟨ ⟦ Htype ⟧ , ⟦ Htype₁ ⟧ ⟩
--   -- ⟦ tprim {ϕ = ϕ} {cs = cs} Hϕ _ Htypes ⟧ = 𝔇-prim Hϕ 𝔇∘ 𝔇∏⟨ ⟦_⟧ ∘ Htypes ⟩
--   -- ⟦ treal {r = r} ⟧ = 𝔇-const r
--   -- ⟦ ttup _ Htypes ⟧ = 𝔇∏⟨ ⟦_⟧ ∘ Htypes ⟩
--   -- ⟦ tproj {Ts = Ts} i Htype ⟧ = 𝔇π[_] {Ds = ⟦_⟧ᵀ ∘ Ts} i 𝔇∘ ⟦ Htype ⟧
--   -- ⟦ tif {T = T} Htype Htype₁ Htype₂ ⟧ =
--   --   if-denot {T = T} ⟦ Htype₁ ⟧ ⟦ Htype₂ ⟧ 𝔇∘ 𝔇⟨ ⟦ Htype ⟧ , 𝔇-id ⟩
--   -- ⟦ tdiff {cs = cs} H≤ Htype Htype₁ ⟧ =
--   --   𝔇-eval {D₁ = 𝔇ℝ′ cs} 𝔇∘
--   --   𝔇-map {D₂ = 𝔇ℝ′ cs} (𝔇-curry-hom 𝔇∘ 𝔇-diff H≤) 𝔇-id 𝔇∘
--   --   𝔇⟨ ⟦ Htype ⟧ , ⟦ Htype₁ ⟧ ⟩
--   -- ⟦ tsolve Htype Htype₁ Htype₂ x ⟧ = {!!}
--   -- ⟦ tdist x x₁ x₂ ⟧ = {!!}
--   -- ⟦ tassume Htype ⟧ = {!!}
--   -- ⟦ tweight Htype ⟧ = {!!}
--   -- ⟦ tinfer Htype x ⟧ = {!!}
--   -- ⟦ tweaken Htype x x₁ ⟧ = {!!}
--   -- ⟦ tsub Htype x x₁ ⟧ = {!!}
--   -- ⟦ tpromote Htype x ⟧ = {!!}
