open import Lib.Reals

module Denotations (R : Reals₀) where

open Reals R using (ℝ; 0ᴿ; _≲?_)

open import Syntax R hiding (n; m; D)
open import Typing R

open import Lib.Prelude hiding ([]; _∷_; _∈_)
open import Lib.Unfinite
open import Lib.Env hiding ([]; _∷_)
open import Lib.Subvec

open import Data.Fin using (splitAt)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Vec.Functional
open import Relation.Unary using (_∈_; Pred)
open import Relation.Binary.PropositionalEquality using (_≗_)

private
  variable
    n m k : ℕ
    Θ : Coeff ^ n
    Θ′ : Coeff ^ m
    Θ″ : Coeff ^ k

record 𝔉-assumptions : Set₁ where
  field
    𝔉 : (Θ : Coeff ^ n) → Coeff → Pred (ℝ ^ n → ℝ) ℓ₀

  𝔉′ : (Θ : Coeff ^ n) (Θ′ : Coeff ^ m) → Pred (ℝ ^ n → ℝ ^ m) ℓ₀
  𝔉′ Θ Θ′ f = (i : Fin _) → π[ i ] ∘ f ∈ 𝔉 Θ (π[ i ] Θ′)

  field
    𝔉-const : (r : ℝ) → const r ∈ 𝔉 [] N

    𝔉-proj : id ∈ 𝔉′ Θ Θ

    𝔉-cond :
      (λ θ → if (θ ₀ ≲? 0ᴿ) then θ ₁ else θ ₂)
        ∈ 𝔉 (P ∷ c ∷ c ∷ []) c

    𝔉-compose :
      {g : ℝ ^ n → ℝ ^ m}
      {f : ℝ ^ m → ℝ}
      (_ : g ∈ 𝔉′ Θ Θ′)
      (_ : f ∈ 𝔉 Θ′ c)
      → -----------------
       f ∘ g ∈ 𝔉 Θ c

    𝔉-sub :
      {f : ℝ ^ n → ℝ}
      (_ : ∀ i → π[ i ] Θ ≤′ π[ i ] Θ′)
      (_ : c′ ≤′ c)
      → -------------------------------
      f ∈ 𝔉 Θ c → f ∈ 𝔉 Θ′ c′

    𝔉-promote :
      {f : ℝ ^ n → ℝ}
      (_ : ∀ i → c′ ≤′ π[ i ] Θ)
      → ------------------------
      f ∈ 𝔉 Θ c → f ∈ 𝔉 Θ c′


module 𝔉-lemmas (Ass : 𝔉-assumptions) where
  open 𝔉-assumptions Ass

  𝔉-const′ : (θ : ℝ ^ n) → const θ ∈ 𝔉′ Θ Θ′
  𝔉-const′ θ i =
    𝔉-compose {Θ′ = λ ()} {g = λ _ ()} (λ ()) $
    𝔉-sub (λ ()) (≤-1 $ toℕ<n _) $
    𝔉-const _

  𝔉-compose′ :
    {g : ℝ ^ n → ℝ ^ m}
    {f : ℝ ^ m → ℝ ^ k}
    (_ : g ∈ 𝔉′ Θ Θ′)
    (_ : f ∈ 𝔉′ Θ′ Θ″)
    → -----------------
     f ∘ g ∈ 𝔉′ Θ Θ″
  𝔉-compose′ Hg Hf = 𝔉-compose Hg ∘ Hf

  𝔉-++ :
    {f : ℝ ^ n → ℝ ^ m}
    {g : ℝ ^ n → ℝ ^ k}
    (_ : f ∈ 𝔉′ Θ Θ′)
    (_ : g ∈ 𝔉′ Θ Θ″)
    → ----------------------------------
    (λ θ → f θ ++ g θ) ∈ 𝔉′ Θ (Θ′ ++ Θ″)
  𝔉-++ {m = m} Hf Hg i with splitAt m i
  ... | ι₁ i = Hf i
  ... | ι₂ i = Hg i

  𝔉-papply :
    {f : ℝ ^ (n + m) → ℝ}
    (_ : f ∈ 𝔉 (Θ ++ Θ′) c)
    (θ′ : ℝ ^ m)
    → -------------------------
    (λ θ → f (θ ++ θ′)) ∈ 𝔉 Θ c
  𝔉-papply Hf θ =
    𝔉-compose (𝔉-++ 𝔉-proj (𝔉-const′ _)) Hf

  𝔉-proj′ : (H⊆ : Θ ⊆ Θ′) → proj-⊆ (H⊆ .π₁) ∈ 𝔉′ Θ′ Θ
  𝔉-proj′ {Θ′ = Θ′} H⊆ i rewrite H⊆ .π₂ i = 𝔉-proj _

  𝔉-weaken :
    {f : ℝ ^ n → ℝ}
    (H⊆ : Θ ⊆ Θ′)
    → ---------------------------------------
    f ∈ 𝔉 Θ c → f ∘ proj-⊆ (H⊆ .π₁) ∈ 𝔉 Θ′ c
  𝔉-weaken H⊆ Hf = 𝔉-compose (𝔉-proj′ H⊆) Hf


record DenotAssumptions : Set₁ where
  field
    𝔉-ass : 𝔉-assumptions

  open 𝔉-assumptions 𝔉-ass public
  open 𝔉-lemmas 𝔉-ass public

  field
    ⟦_⟧ᴾ : (ϕ : Prim) → ℝ ^ PrimAr ϕ → ℝ

    𝔉-prim :
      {Θ : Coeff ^ PrimAr ϕ}
      (_ : PrimTy ϕ ≡ (Θ , c))
      → ----------------------
      ⟦ ϕ ⟧ᴾ ∈ 𝔉 Θ c

    𝐷 :
      (f : ℝ ^ n → ℝ)
      (_ : ∀ i → π[ i ] Θ ≤′ P)
      (_ : f ∈ 𝔉 Θ c)
      → -----------------------
      ℝ ^ (n + n) → ℝ

    𝔉-diff :
      {Θ′ : Coeff ^ m}
      (f : ℝ ^ (n + m) → ℝ)
      (H≤ : ∀ i → π[ i ] Θ ≤′ P)
      (Hf : f ∈ 𝔉 (Θ ++ Θ′) c)
      → ------------------------------------------------------
      (λ xvθ → 𝐷 _ H≤ (𝔉-papply Hf (drop _ xvθ)) (take _ xvθ))
        ∈ 𝔉 ((Θ ++ replicate n A) ++ Θ′) c


module Denotations (Ass : DenotAssumptions) where
  open DenotAssumptions Ass

  -- Our semantic domain, inspired by the paper
  -- Concrete Categories for Higher-order Recursion (Matache et al.).
  --
  -- In terms of that paper, the idea is that our domains are concrete
  -- sheaves over a site S whose objects are vectors of coeffects, and
  -- whose morphisms Θ → Θ′ are functions (f : ℝ ^ n → ℝ ^ m) ∈ 𝔉′ Θ Θ′.
  -- TODO: What is the coverage on the site?  Can it simply be trivial?
  -- Should the objects be _subsets_ of ℝ ^ n tagged with vectors of
  -- coeffects instead, and the coverage be the inclusion functions?
  --
  -- The semantics is also closely related to our previous logical
  -- relations arguments, in that we can view each domain as a set
  -- equipped with a parameterized predicate describing the
  -- well-behaved maps into that domain.
  record 𝔇 : Set₁ where
    constructor mk𝔇
    field
      ∣_∣ : Set
      R[_,_] : {n : ℕ} → Coeff ^ n → Pred (ℝ ^ n → ∣_∣) ℓ₀

      R[,]-const :
        (x : ∣_∣)
        → ---------------
        const x ∈ R[_,_] Θ

      R[,]-compose :
        {f : ℝ ^ n → ℝ ^ m}
        {ϕ : ℝ ^ m → ∣_∣}
        (_ : f ∈ 𝔉′ Θ Θ′)
        → ------------------------------
        ϕ ∈ R[_,_] Θ′ → ϕ ∘ f ∈ R[_,_] Θ

  open 𝔇

  -- Conjecture: the previous semantics and this one are equivalent
  -- under the following correspondence:

  module Correspondence where
    fwd :
      (p : {n : ℕ} → Pred (Coeff ^ n) ℓ₀)
      (pr : {m : ℕ} {Θ : Coeff ^ m} → p Θ → ℝ ^ m → p [])
      → ---------------------------------------------------
      ∃ λ X → {m : ℕ} → Coeff ^ m → Pred (ℝ ^ m → X) ℓ₀
    fwd p pr = p [] , λ Θ f → ∑ f′ ∶ p Θ , pr f′ ≗ f

    bwd :
      {X : Set}
      (_ : {m : ℕ} → Coeff ^ m → Pred (ℝ ^ m → X) ℓ₀)
      → -----------------------------------------------
      {n : ℕ} → Pred (Coeff ^ n) ℓ₀
    bwd Hx = λ Θ → ∃ (Hx Θ)

    -- Note that this is not a proper equivalence as the forward
    -- direction requires a projection function from p Θ
    -- to ℝ ^ m → p [].  Attempting to take this into account in the
    -- reverse direction requires adding more hypotheses stating that
    -- constant functions are plots, and furthermore that they are the
    -- only plots of Hx [].  This gets a bit intricate, but I believe
    -- the required hypotheses should hold for our case.


  𝔇-is-hom : (D₁ D₂ : 𝔇) → Pred (∣ D₁ ∣ → ∣ D₂ ∣) ℓ₀
  𝔇-is-hom D₁ D₂ f =
    {m : ℕ} {Θ : Coeff ^ m}
    → -----------------------------------------
    ∀ ϕ → ϕ ∈ R[ D₁ , Θ ] → f ∘ ϕ ∈ R[ D₂ , Θ ]

  record 𝔇-hom (D₁ D₂ : 𝔇) : Set where
    field
      to : ∣ D₁ ∣ → ∣ D₂ ∣
      is-hom : 𝔇-is-hom D₁ D₂ to

  open 𝔇-hom

  private
    variable
      D D₁ D₂ D₃ : 𝔇

  𝔇-id : 𝔇-hom D D
  𝔇-id .to z = z
  𝔇-id .is-hom _ Hϕ = Hϕ

  _𝔇∘_ : 𝔇-hom D₂ D₃ → 𝔇-hom D₁ D₂ → 𝔇-hom D₁ D₃
  (f 𝔇∘ g) .to = f .to ∘ g .to
  (f 𝔇∘ g) .is-hom _ = f .is-hom _ ∘ g .is-hom _

  𝔇𝟙 : 𝔇
  𝔇𝟙 = mk𝔇 𝟙 (λ _ _ → 𝟙) (λ _ → tt) λ _ _ → tt

  𝔇𝟙-terminal : 𝔇-hom D 𝔇𝟙
  𝔇𝟙-terminal .to _ = tt
  𝔇𝟙-terminal .is-hom _ _ = tt

  𝔇ℝ : Coeff → 𝔇
  𝔇ℝ c =
    mk𝔇 ℝ (λ Θ → 𝔉 Θ c) (λ r → 𝔉-const′ {Θ′ = c ∷ []} (r ∷ []) ₀) 𝔉-compose

  𝔇-const : ℝ → 𝔇-hom 𝔇𝟙 (𝔇ℝ c)
  𝔇-const r .to _ = r
  𝔇-const r .is-hom _ _ = R[,]-const (𝔇ℝ _) r

  𝔇ℝ′ : Coeff ^ n → 𝔇
  𝔇ℝ′ Θ′ = mk𝔇 (ℝ ^ _) (λ Θ → 𝔉′ Θ Θ′) 𝔉-const′ 𝔉-compose′

  _𝔇×_ : 𝔇 → 𝔇 → 𝔇
  ∣ D₁ 𝔇× D₂ ∣ = ∣ D₁ ∣ × ∣ D₂ ∣
  R[ D₁ 𝔇× D₂ , Θ ] f = π₁ ∘ f ∈ R[ D₁ , Θ ] × π₂ ∘ f ∈ R[ D₂ , Θ ]
  R[,]-const (D₁ 𝔇× D₂) (x₁ , x₂) = R[,]-const D₁ x₁ , R[,]-const D₂ x₂
  R[,]-compose (D₁ 𝔇× D₂) Hf (Hϕ₁ , Hϕ₂) =
    R[,]-compose D₁ Hf Hϕ₁ , R[,]-compose D₂ Hf Hϕ₂

  𝔇π₁ : 𝔇-hom (D₁ 𝔇× D₂) D₁
  𝔇π₁ .to = π₁
  𝔇π₁ .is-hom _ Hϕ = Hϕ .π₁

  𝔇π₂ : 𝔇-hom (D₁ 𝔇× D₂) D₂
  𝔇π₂ .to = π₂
  𝔇π₂ .is-hom _ Hϕ = Hϕ .π₂

  𝔇⟨_,_⟩ : 𝔇-hom D D₁ → 𝔇-hom D D₂ → 𝔇-hom D (D₁ 𝔇× D₂)
  𝔇⟨ d₁ , d₂ ⟩ .to z = d₁ .to z , d₂ .to z
  𝔇⟨ d₁ , d₂ ⟩ .is-hom ϕ Hϕ = d₁ .is-hom ϕ Hϕ , d₂ .is-hom ϕ Hϕ

  𝔇∏ : Vector 𝔇 n → 𝔇
  ∣ 𝔇∏ Ds ∣ = (i : Fin _) → ∣ Ds i ∣
  R[ 𝔇∏ Ds , Θ ] f = (i : Fin _) → (λ θ → f θ i) ∈ R[ Ds i , Θ ]
  R[,]-const (𝔇∏ Ds) x i = R[,]-const (Ds i) (x i)
  R[,]-compose (𝔇∏ Ds) Hf Hϕs i = R[,]-compose (Ds i) Hf (Hϕs i)

  -- Note: ℝ ^ n ≡ ∏ᵢⁿ ℝ holds definitionally.
  _ : 𝔇∏ (𝔇ℝ ∘ Θ) ≡ 𝔇ℝ′ Θ
  _ = refl

  𝔇π[_] : {Ds : Vector 𝔇 n} → (i : Fin n) → 𝔇-hom (𝔇∏ Ds) (π[ i ] Ds)
  𝔇π[ i ] .to ds = ds i
  𝔇π[ i ] .is-hom _ Hϕ = Hϕ i

  𝔇∏⟨_⟩ : {Ds : Vector 𝔇 n} → ((i : Fin n) → 𝔇-hom D (Ds i)) → 𝔇-hom D (𝔇∏ Ds)
  𝔇∏⟨ ds ⟩ .to z i = ds i .to z
  𝔇∏⟨ ds ⟩ .is-hom ϕ Hϕ i = ds i .is-hom ϕ Hϕ

  _𝔇⇒_ : 𝔇 → 𝔇 → 𝔇
  ∣ D₁ 𝔇⇒ D₂ ∣ = 𝔇-hom D₁ D₂
  R[ D₁ 𝔇⇒ D₂ , Θ ] f =
    (λ (θ , d) → f θ .to d) ∈ 𝔇-is-hom (𝔇ℝ′ Θ 𝔇× D₁) D₂
  R[,]-const (D₁ 𝔇⇒ D₂) f ϕ Hϕ = f .is-hom (π₂ ∘ ϕ) (Hϕ .π₂)
  R[,]-compose (D₁ 𝔇⇒ D₂) Hf Hϕ₀ ϕ Hϕ =
    Hϕ₀ _ (𝔉-compose′ (Hϕ .π₁) Hf , Hϕ .π₂)

  𝔇-eval : 𝔇-hom ((D₁ 𝔇⇒ D₂) 𝔇× D₁) D₂
  𝔇-eval .to (f , x) = f .to x
  𝔇-eval .is-hom ϕ (Hϕ₁ , Hϕ₂) = Hϕ₁ _ (𝔉-proj , Hϕ₂)

  𝔇-curry : 𝔇-hom (D 𝔇× D₁) D₂ → 𝔇-hom D (D₁ 𝔇⇒ D₂)
  𝔇-curry f .to x .to y = f .to (x , y)
  𝔇-curry {D = D} f .to x .is-hom ϕ Hϕ =
    f .is-hom _ (R[,]-const D x , Hϕ)
  𝔇-curry {D = D} f .is-hom ϕ Hϕ ϕ′ (Hϕ′₁ , Hϕ′₂) =
    f .is-hom _ (R[,]-compose D Hϕ′₁ Hϕ , Hϕ′₂)

  -- Coproduct seems somewhat tricky to define: we need to be able to
  -- partition the objects of our site, i.e., ℝ ^ n tagged with vectors
  -- of coeffects.  Probably we would need to have a more fine-grained
  -- site which has objects not just ℝ ^ n but also well-behaved subsets.
  -- Question is how that would interact with the coeffect vectors.
  --
  -- _𝔇⊎_ : 𝔇 → 𝔇 → 𝔇
  -- ∣ D₁ 𝔇⊎ D₂ ∣ = ∣ D₁ ∣ ⊎ ∣ D₂ ∣
  -- R[_,_] (D₁ 𝔇⊎ D₂) {n} Θ f =
  --   ∃ λ ((m , m′) : ℕ × ℕ) →
  --   ∃ λ (Heq : ℝ ^ n ≡ ℝ ^ m ⊎ ℝ ^ m′) →
  --   ∃ λ ((f₁ , f₂) : (ℝ ^ m → ∣ D₁ ∣) × (ℝ ^ m′ → ∣ D₂ ∣)) →
  --   f₁ ∈ R[ D₁ , take m (subst (Coeff ^_) Heq Θ) ] ×
  --   f₂ ∈ R[ D₂ , drop m (subst (Coeff ^_) Heq Θ) ] ×
  --   f ≗ {!!}
  -- R[,]-const (D₁ 𝔇⊎ D₂) = {!!}
  -- R[,]-compose (D₁ 𝔇⊎ D₂) = {!!}

  𝔇-prim :
    {Θ : Coeff ^ PrimAr ϕ}
    (_ : PrimTy ϕ ≡ (Θ , c))
    → ---------------------
    𝔇-hom (𝔇ℝ′ Θ) (𝔇ℝ c)
  𝔇-prim {ϕ = ϕ} Hϕ .to = ⟦ ϕ ⟧ᴾ
  𝔇-prim Hϕ .is-hom ϕ′ Hϕ′ = 𝔉-compose Hϕ′ (𝔉-prim Hϕ)

  -- Doesn't work straight off unless we know what D₁ is...
  -- One way is to define this for the case D₁ ≡ ⟦ T ⟧ᵀ for some
  -- T, so that we can induct over T; the other would be to figure
  -- out general coproducts.
  --
  -- 𝔇-if :
  --   (_ : 𝔇-hom D D₁)
  --   (_ : 𝔇-hom D D₁)
  --   → -----------------
  --   𝔇-hom (𝔇ℝ P 𝔇× D) D₁
  -- 𝔇-if d₁ d₂ .to (x , γ) = if (x ≲? 0ᴿ) then d₁ .to γ else d₂ .to γ
  -- 𝔇-if d₁ d₂ .is-hom ϕ (Hϕ₁ , Hϕ₂) =
  --   let foo = d₁ .is-hom _ Hϕ₂
  --       bar = d₂ .is-hom _ Hϕ₂
  --   in
  --   {!!}


  ⟦_⟧ᵀ : Type → 𝔇
  ⟦ treal c ⟧ᵀ = 𝔇ℝ c
  ⟦ T₁ ⇒[ _ ] T₂ ⟧ᵀ = ⟦ T₁ ⟧ᵀ 𝔇⇒ ⟦ T₂ ⟧ᵀ
  ⟦ ttup n Ts ⟧ᵀ = 𝔇∏ (⟦_⟧ᵀ ∘ Ts)
  -- Distributions are interpreted trivially for the time being.
  ⟦ tdist T ⟧ᵀ = ⟦ T ⟧ᵀ

  ⟦_⟧ᴱ : TyEnv → 𝔇
  ⟦ ε ⟧ᴱ = 𝔇𝟙
  ⟦ Γ , _ ∶ T ⟧ᴱ = ⟦ Γ ⟧ᴱ 𝔇× ⟦ T ⟧ᵀ

  -- weaken : Θ ⊆ Θ′ → ⟦ T ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ′
  -- weaken {T = treal c} H⊆ (_ , Hf) = _ , 𝔉-weaken H⊆ Hf
  -- weaken {T = T₁ ⇒[ _ ] T₂} H⊆ Hf {Θ′ = Θ′} H⊆′ =
  --   Hf (⊆-trans {zs = Θ′} H⊆ H⊆′)
  -- weaken {T = ttup n Ts} H⊆ Hsem i = weaken H⊆ (Hsem i)
  -- weaken {T = tdist T} H⊆ Hsem ₀ = weaken H⊆ (Hsem ₀)

  -- weaken-env : Θ ⊆ Θ′ → ⟦ Γ ⟧ᴱ Θ → ⟦ Γ ⟧ᴱ Θ′
  -- weaken-env H⊆ = All.map (weaken H⊆)

  -- abs-real-denot : {cs : Coeff ^ n} → ⟦ T ⟧ᵀ (cs ++ Θ) → ⟦ treals n cs ⇒[ e ] T ⟧ᵀ Θ
  -- abs-real-denot {n = n} {T = treal c′} {cs = cs} f {Θ′ = Θ′} H⊆ xs
  --   with f , Hf ← weaken (⊆-++⁺ ⊆-refl H⊆) f = _ , 𝔉-compose Hg Hf
  --   where
  --     Hg : (λ θ → (λ i → xs i .π₁ θ) ++ θ) ∈ 𝔉′ Θ′ (cs ++ Θ′)
  --     Hg i with splitAt n i
  --     ... | ι₁ i = xs i .π₂
  --     ... | ι₂ i = 𝔉-proj i
  -- abs-real-denot {T = T₁ ⇒[ _ ] T₂} {cs = cs} Hf H⊆ xs {Θ′ = Θ′} H⊆′ s =
  --   abs-real-denot {e = det} fs ⊆-refl λ i → _ , 𝔉-weaken H⊆′ (xs i .π₂)
  --   where
  --     fs : ⟦ T₂ ⟧ᵀ (cs ++ Θ′)
  --     fs = Hf (⊆-++⁺ ⊆-refl (⊆-trans {zs = Θ′} H⊆ H⊆′)) (weaken (⊆-++⁺ˡ _ ⊆-refl) s)
  -- abs-real-denot {T = ttup n Ts} Hsem H⊆ f i = abs-real-denot {e = det} (Hsem i) H⊆ f
  -- abs-real-denot {T = tdist T} Hsem H⊆ f _ =
  --   abs-real-denot {e = det} (Hsem ₀) H⊆ f

  -- app-real-denot : {cs : Coeff ^ n} → ⟦ treals n cs ⇒[ e ] T ⟧ᵀ Θ → ⟦ T ⟧ᵀ (cs ++ Θ)
  -- app-real-denot f =
  --   f (⊆-++⁺ˡ _ ⊆-refl) λ i → _ , 𝔉-proj′ (⊆-++⁺ʳ _ ⊆-refl) i

  -- if-denot : ⟦ treal P ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ
  -- if-denot {T = treal c} (s , Hs) (s₁ , Hs₁) (s₂ , Hs₂) =
  --   let g θ = λ {₀ → s θ ; ₁ → s₁ θ ; ₂ → s₂ θ }
  --       Hg = λ {₀ → Hs ; ₁ → Hs₁ ; ₂ → Hs₂ }
  --   in
  --   _ , 𝔉-compose {g = g} Hg 𝔉-cond
  -- if-denot {T = T₁ ⇒[ _ ] T₂} s s₁ s₂ H⊆ x =
  --   if-denot (weaken H⊆ s) (s₁ H⊆ x) (s₂ H⊆ x)
  -- if-denot {T = ttup n Ts} s s₁ s₂ i = if-denot s (s₁ i) (s₂ i)
  -- if-denot {T = tdist T} s s₁ s₂ _ = if-denot s (s₁ ₀) (s₂ ₀)


  ⟦_⟧ : Γ ⊢ t :[ e ] T → 𝔇-hom ⟦ Γ ⟧ᴱ ⟦ T ⟧ᵀ
  ⟦ tvar ⟧ = 𝔇π₂ {D₁ = 𝔇𝟙}
  ⟦ tabs (Иi As Habs) ⟧ = 𝔇-curry ⟦ Habs (new As) {{unfinite As}} ⟧
  ⟦ tapp Htype Htype₁ ⟧ = 𝔇-eval 𝔇∘ 𝔇⟨ ⟦ Htype ⟧ , ⟦ Htype₁ ⟧ ⟩
  ⟦ tprim {ϕ = ϕ} {cs = cs} Hϕ _ Htypes ⟧ = 𝔇-prim Hϕ 𝔇∘ 𝔇∏⟨ ⟦_⟧ ∘ Htypes ⟩
  ⟦ treal {r = r} ⟧ = 𝔇-const r
  ⟦ ttup _ Htypes ⟧ = 𝔇∏⟨ ⟦_⟧ ∘ Htypes ⟩
  ⟦ tproj {Ts = Ts} i Htype ⟧ = 𝔇π[_] {Ds = ⟦_⟧ᵀ ∘ Ts} i 𝔇∘ ⟦ Htype ⟧
  ⟦ tif Htype Htype₁ Htype₂ ⟧ = {!!}
  ⟦ tdiff x Htype Htype₁ ⟧ = {!!}
  ⟦ tsolve Htype Htype₁ Htype₂ x ⟧ = {!!}
  ⟦ tdist x x₁ x₂ ⟧ = {!!}
  ⟦ tassume Htype ⟧ = {!!}
  ⟦ tweight Htype ⟧ = {!!}
  ⟦ tinfer Htype x ⟧ = {!!}
  ⟦ tweaken Htype x x₁ ⟧ = {!!}
  ⟦ tsub Htype x x₁ ⟧ = {!!}
  ⟦ tpromote Htype x ⟧ = {!!}
  -- ⟦ tvar ⟧ (x All.∷ _) = x
  -- ⟦ tabs (Иi As Habs) ⟧ γ H⊆ s =
  --   ⟦ Habs (new As) {{unfinite As}} ⟧ (s All.∷ weaken-env H⊆ γ)
  -- ⟦ tapp Hf Ht ⟧ γ = ⟦ Hf ⟧ γ ⊆-refl (⟦ Ht ⟧ γ)
  -- ⟦ tprim {ϕ = ϕ} {cs = cs} Hϕ _ Htypes ⟧ {Θ} γ =
  --   _ , 𝔉-compose (λ i → ⟦ Htypes i ⟧ γ .π₂) (𝔉-prim Hϕ)
  -- ⟦ treal {r = r} ⟧ _ = _ , 𝔉-compose {g = λ _ ()} (λ ()) (𝔉-const r)
  -- ⟦ ttup _ Htypes ⟧ γ i = ⟦ Htypes i ⟧ γ
  -- ⟦ tproj i Htype ⟧ γ = ⟦ Htype ⟧ γ i
  -- ⟦ tif Htype Htype₁ Htype₂ ⟧ γ =
  --   if-denot (⟦ Htype ⟧ γ) (⟦ Htype₁ ⟧ γ) (⟦ Htype₂ ⟧ γ)
  -- ⟦ tdiff {n = n} {m} {cs = cs} {ds} H≤ Htype Htype₁ ⟧ {Θ} γ =
  --   abs-real-denot {T = treals m ds} {e = det} λ j →
  --   _ , 𝔉-compose
  --        ((𝔉-compose′ getΘ (λ i → ⟦ Htype₁ ⟧ γ i .π₂) <++> getAs) <++> getΘ)
  --        (𝔉-diff _ H≤ (fapp _ .π₂))
  --   where
  --     fapp = app-real-denot {e = det} {T = treals m ds} (⟦ Htype ⟧ γ)
  --     _<++>_ = 𝔉-++
  --     getAs = 𝔉-proj′ (⊆-++⁺ʳ _ ⊆-refl)
  --     getΘ = 𝔉-proj′ (⊆-++⁺ˡ _ ⊆-refl)
  -- ⟦ tsolve Htype Htype₁ Htype₂ H≤ ⟧ = {!!}
  -- ⟦ tdist _ _ _ ⟧ = {!!}
  -- ⟦ tassume Htype ⟧ γ = ⟦ Htype ⟧ γ ₀
  -- ⟦ tweight Htype ⟧ γ ()
  -- ⟦ tinfer Htype _ ⟧ γ _ = ⟦ Htype ⟧ γ ⊆-refl λ ()
  -- ⟦ tweaken Htype x x₁ ⟧ = {!!}
  -- ⟦ tsub Htype x x₁ ⟧ = {!!}
  -- ⟦ tpromote Htype x ⟧ = {!!}
