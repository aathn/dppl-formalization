open import Lib.Reals

module Denotations (R : Reals₀) where

open Reals R using (ℝ; 0ᴿ; _≲?_)

open import Syntax R hiding (n; m; D)
open import Typing R

open import Lib.Prelude hiding ([]; [_]; _∷_; _∈_; ⋃)
open import Lib.Unfinite
open import Lib.Env hiding ([]; _∷_)
open import Lib.Subvec
open import Lib.FunExt

open import Data.Fin using (splitAt)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Sum using ([_,_])
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import Data.Vec.Functional
open import Relation.Unary using (_∈_; Pred; ⋃)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≗_)

open import Function using (Injection ; _↣_ ; mk↣)
open import Function.Bundles using (Func)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category using (Category)
open import Categories.Category.Concrete using (Concrete)
open import Categories.Category.Slice using (SliceObj ; sliceobj)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.Functor.Hom
open import Categories.Functor.Properties using (Faithful)
open import Categories.Object.Terminal using (IsTerminal)

open import Level using (_⊔_) renaming (suc to lsuc)

open Functor
open Func
open Injection
open SliceObj using (arr)

private
  variable
    n m k : ℕ
--     Θ : Coeff ^ n
--     Θ′ : Coeff ^ m
--     Θ″ : Coeff ^ k

Im : {ℓ ℓ′ : Level} {A B : Set ℓ} → Rel B ℓ′ → (A → B) → Pred B (ℓ ⊔ ℓ′)
Im _≈_ f y = ∃ λ x → y ≈ f x

Pointwise : {ℓA ℓB ℓ : Level} {A : Set ℓA} {B : Set ℓB} → Rel B ℓ → Rel (A → B) (ℓA ⊔ ℓ)
Pointwise _≈_ f g = ∀ z → f z ≈ g z

∣_∣ₚ : {ℓ ℓ′ : Level}{X : Set ℓ} → Pred X ℓ′ → Set _
∣_∣ₚ = ∃

record CCat (o ℓ e : Level) : Set (lsuc (o ⊔ ℓ ⊔ e)) where
  -- Our definition of concrete categories differs from the agda-categories library
  -- in that we require a terminal object (following Matache et al.).
  field
    𝒞 : Category o ℓ e

  open Category 𝒞 public renaming (_∘_ to _∘′_)
  open Hom 𝒞 public

  field
    ⋆ : Obj
    ⋆-is-terminal  : IsTerminal 𝒞 ⋆
    ⋆-hom-faithful : Faithful Hom[ ⋆ ,-]

  open Setoid

  obj∣_∣ : Obj → Set ℓ
  obj∣ c ∣ = ⋆ ⇒ c

  hom∣_∣ : {o₁ o₂ : Obj} → o₁ ⇒ o₂ → obj∣ o₁ ∣ → obj∣ o₂ ∣
  hom∣ f ∣ g = f ∘′ g

module _ {o ℓ e : Level} (p : Level) (Cat : CCat o ℓ e) where
  private
    variable
      Y Z : CCat.Obj Cat

  -- The definition of concrete sites uses a predicate-based approach
  -- instead of explicit indexing as in the agda-categories library,
  -- to simplify the definition of the pullback site.  We also work
  -- exclusively with countable covers.
  record CSite : Set (o ⊔ ℓ ⊔ e ⊔ lsuc p) where
    open CCat Cat
    field
      cover : (c : Obj) → Pred ((n : ℕ) → SliceObj 𝒞 c) p

      coverage-pullback :
        (g : Y ⇒ Z)
        (fs : (n : ℕ) → SliceObj 𝒞 Z)
        (_ : fs ∈ cover Z)
        → ----------------------------------------------
        ∃ λ hs → hs ∈ cover Y × ∀ (j : ℕ) → ∃₂ λ i k →
        g ∘′ hs j .arr ≈ fs i .arr ∘′ k

      coverage-covers :
        (c : Obj)
        (fs : (n : ℕ) → SliceObj 𝒞 c)
        (_ : fs ∈ cover c)
        {x : obj∣ c ∣}
        → ------------------------------------
        x ∈ ⋃ ℕ λ n → Im _≈_ hom∣ fs n .arr ∣

record CSheaf
  {o ℓ e c : Level}
  (o′ ℓ′ : Level)
  {Cat : CCat o ℓ e}
  (S : CSite c Cat)
  : ----------------------------------
  Set (o ⊔ ℓ ⊔ e ⊔ c ⊔ lsuc (o′ ⊔ ℓ′))
  where
  open CSite S
  open CCat Cat
  open Setoid

  field
    ℱ : Presheaf 𝒞 (Setoids o′ ℓ′)

  ∣_∣ : Set o′
  ∣_∣ = ℱ .F₀ ⋆ .Carrier

  ℱ-maps : (c : Obj) → ℱ .F₀ c .Carrier → obj∣ c ∣ → ∣_∣
  ℱ-maps c ℱc f = ℱ .F₁ f .to ℱc

  R[_,_] : (c : Obj) → Pred (obj∣ c ∣ → ∣_∣) _
  R[_,_] c f = ∃ λ ℱc → Pointwise (ℱ .F₀ ⋆ ._≈_) f (ℱ-maps c ℱc)

  field
    ℱ-is-concrete :
      {c : Obj} → injection (ℱ .F₀ c ._≈_) (Pointwise (ℱ .F₀ ⋆ ._≈_)) (ℱ-maps c)

    ℱ-is-sheaf :
      {c : Obj}
      (g : obj∣ c ∣ → ∣_∣)
      (fs : (n : ℕ) → SliceObj 𝒞 c)
      (_ : fs ∈ cover c)
      (_ : ∀ i → g ∘ hom∣ fs i .arr ∣ ∈ R[_,_] _)
      → -----------------------------------------
      g ∈ R[_,_] c

module Pushforward {o ℓ e p : Level}
  {C D : CCat o ℓ e}
  (S : CSite p D)
  (F : Functor (D .CCat.𝒞) (C .CCat.𝒞))
  where

  open CSite
  -- open Sheaf

  PushSite : CSite _ C
  PushSite .cover c fam =
    ∃₂ λ d fam′ →
      S .cover d fam′ ×
      F .F₀ d ≡ c ×
      ∀ n → F .F₁ (fam′ n .arr) ≈ fam n .arr
    where open CCat C
  PushSite .coverage-pullback = {!!}
  PushSite .coverage-covers = {!!}
  -- PushSite .cover c fam =
  --   S .cover (F .F₀ c) λ n → sliceobj $ F .F₁ (fam n .arr)
  -- PushSite .coverage-pullback g fam cov =
  --   let foo = S .coverage-pullback (F .F₁ g) (λ n → sliceobj $ F .F₁ (fam n .arr)) cov
  --   in
  --   {!!}
  -- PushSite .coverage-covers = {!!}
  -- PullSite .cover-fam c = S .cover-fam (F .F₀ c)
  -- PullSite .cover = {!!}
  -- PullSite .coverage-pullback = {!!}
  -- PullSite .coverage-covers = {!!}
  -- PullSite .cover-fam c =
  --   ∑ cov ∶ S .cover-fam (F .F₀ c) ,
  --   ∀ (n : ℕ) → ∃₂ λ c′ f →
  --     ∃ λ (Heq : F .F₀ c′ ≡ S .cover-dom cov n) →
  --     subst (_⇒ F .F₀ c) Heq (F .F₁ f) ≈ S .cover cov n
  --   where open CCat D
  -- PullSite .cover-dom (_ , fam) n = fam n .π₁
  -- PullSite .cover (cov , fam) n = fam n .π₂ .π₁
  -- PullSite .coverage-pullback g (cov , fam) =
  --   let (cov′ , pb-prop) = S .coverage-pullback (F .F₁ g) cov
  --   in
  --   (cov′ ,
  --     λ n →
  --     let c′ , f , Heq , H≈ = fam n in         
  --     {!!}) ,
  --     {!!}
  --   where open CCat D
  -- PullSite .coverage-covers c (cov , f) {x} =
  --   let foo = F .F₁ x in {!!}
--     where open CCat C

module ℝ⊆ where

  open Category renaming (_∘_ to _∘′_; id to id′)

  ℝ⊆ : CCat ℓ₁ ℓ₀ ℓ₀
  ℝ⊆ = {!!}
  -- ℝ⊆ .Obj = ∃₂ λ n o → o ↣ ℝ ^ n
  -- ℝ⊆ ._⇒_ (_ , o₁ , _) (_ , o₂ , _) = o₁ ↣ o₂
  -- ℝ⊆ ._≈_ = {!!}
  -- ℝ⊆ .id′ = {!!}
  -- ℝ⊆ ._∘′_ = {!!}
  -- ℝ⊆ .assoc = {!!}
  -- ℝ⊆ .sym-assoc = {!!}
  -- ℝ⊆ .identityˡ = {!!}
  -- ℝ⊆ .identityʳ = {!!}
  -- ℝ⊆ .identity² = {!!}
  -- ℝ⊆ .equiv = {!!}
  -- ℝ⊆ .∘-resp-≈ = {!!}

open ℝ⊆

record c-assumptions : Set₁ where
  field
    c-site : Coeff → CSite ℓ₀ ℝ⊆
    c-sheaf : (c : Coeff) → CSheaf ℓ₀ ℓ₀ (c-site c)

  -- c-opens : Category ℓ₀ ℓ₀ ℓ₀
  -- c-opens .Obj = ∃₂ c-open
  -- c-opens ._⇒_ (c₁ , n₁ , U) (c₂ , n₂ , V) = c-open-points U ↣ c-open-points V
  -- c-opens ._≈_ = {!!}
  -- c-opens .id′ = {!!}
  -- c-opens ._∘′_ = {!!}
  -- c-opens .assoc = {!!}
  -- c-opens .sym-assoc = {!!}
  -- c-opens .identityˡ = {!!}
  -- c-opens .identityʳ = {!!}
  -- c-opens .identity² = {!!}
  -- c-opens .equiv = {!!}
  -- c-opens .∘-resp-≈ = {!!}

--   𝔉′ : (Θ : Coeff ^ n) (Θ′ : Coeff ^ m) → Pred (ℝ ^ n → ℝ ^ m) ℓ₀
--   𝔉′ Θ Θ′ f = (i : Fin _) → π[ i ] ∘ f ∈ 𝔉 Θ (π[ i ] Θ′)

--   field
--     𝔉-const : (r : ℝ) → const r ∈ 𝔉 [] N

--     𝔉-proj : id ∈ 𝔉′ Θ Θ

--     𝔉-cond :
--       (λ θ → if (θ ₀ ≲? 0ᴿ) then θ ₁ else θ ₂)
--         ∈ 𝔉 (P ∷ c ∷ c ∷ []) c

--     𝔉-compose :
--       {g : ℝ ^ n → ℝ ^ m}
--       {f : ℝ ^ m → ℝ}
--       (_ : g ∈ 𝔉′ Θ Θ′)
--       (_ : f ∈ 𝔉 Θ′ c)
--       → -----------------
--        f ∘ g ∈ 𝔉 Θ c

--     𝔉-sub :
--       {f : ℝ ^ n → ℝ}
--       (_ : ∀ i → π[ i ] Θ ≤′ π[ i ] Θ′)
--       (_ : c′ ≤′ c)
--       → -------------------------------
--       f ∈ 𝔉 Θ c → f ∈ 𝔉 Θ′ c′

--     𝔉-promote :
--       {f : ℝ ^ n → ℝ}
--       (_ : ∀ i → c′ ≤′ π[ i ] Θ)
--       → ------------------------
--       f ∈ 𝔉 Θ c → f ∈ 𝔉 Θ c′


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
