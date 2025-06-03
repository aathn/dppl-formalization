open import Lib.Reals

module Denotations (R : Reals₀) where

open Reals R using (ℝ; 0ᴿ; _≲?_)

open import Syntax R hiding (n; m)
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

  ⟦_⟧ᵀ : Type → Coeff ^ n → Set
  ⟦ treal c ⟧ᵀ Θ = ∃ (𝔉 Θ c)
  ⟦ T₁ ⇒[ _ ] T₂ ⟧ᵀ Θ = {m : ℕ} {Θ′ : Coeff ^ m} → Θ ⊆ Θ′ → ⟦ T₁ ⟧ᵀ Θ′ → ⟦ T₂ ⟧ᵀ Θ′
  ⟦ ttup n Ts ⟧ᵀ Θ = (i : Fin n) → ⟦ Ts i ⟧ᵀ Θ
  -- Distributions are interpreted trivially for the time being.
  -- For some reason, wrapping the result in a 1-vector seems
  -- to help the type inference...
  ⟦ tdist T ⟧ᵀ Θ = (i : Fin 1) → ⟦ T ⟧ᵀ Θ

  ⟦_⟧ᴱ : TyEnv → Coeff ^ n → Set
  ⟦ Γ ⟧ᴱ Θ = All (λ (_ , T) → ⟦ T ⟧ᵀ Θ) Γ


  weaken : Θ ⊆ Θ′ → ⟦ T ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ′
  weaken {T = treal c} H⊆ (_ , Hf) = _ , 𝔉-weaken H⊆ Hf
  weaken {T = T₁ ⇒[ _ ] T₂} H⊆ Hf {Θ′ = Θ′} H⊆′ =
    Hf (⊆-trans {zs = Θ′} H⊆ H⊆′)
  weaken {T = ttup n Ts} H⊆ Hsem i = weaken H⊆ (Hsem i)
  weaken {T = tdist T} H⊆ Hsem ₀ = weaken H⊆ (Hsem ₀)

  weaken-env : Θ ⊆ Θ′ → ⟦ Γ ⟧ᴱ Θ → ⟦ Γ ⟧ᴱ Θ′
  weaken-env H⊆ = All.map (weaken H⊆)

  abs-real-denot : {cs : Coeff ^ n} → ⟦ T ⟧ᵀ (cs ++ Θ) → ⟦ treals n cs ⇒[ e ] T ⟧ᵀ Θ
  abs-real-denot {n = n} {T = treal c′} {cs = cs} f {Θ′ = Θ′} H⊆ xs
    with f , Hf ← weaken (⊆-++⁺ ⊆-refl H⊆) f = _ , 𝔉-compose Hg Hf
    where
      Hg : (λ θ → (λ i → xs i .π₁ θ) ++ θ) ∈ 𝔉′ Θ′ (cs ++ Θ′)
      Hg i with splitAt n i
      ... | ι₁ i = xs i .π₂
      ... | ι₂ i = 𝔉-proj i
  abs-real-denot {T = T₁ ⇒[ _ ] T₂} {cs = cs} Hf H⊆ xs {Θ′ = Θ′} H⊆′ s =
    abs-real-denot {e = det} fs ⊆-refl λ i → _ , 𝔉-weaken H⊆′ (xs i .π₂)
    where
      fs : ⟦ T₂ ⟧ᵀ (cs ++ Θ′)
      fs = Hf (⊆-++⁺ ⊆-refl (⊆-trans {zs = Θ′} H⊆ H⊆′)) (weaken (⊆-++⁺ˡ _ ⊆-refl) s)
  abs-real-denot {T = ttup n Ts} Hsem H⊆ f i = abs-real-denot {e = det} (Hsem i) H⊆ f
  abs-real-denot {T = tdist T} Hsem H⊆ f _ =
    abs-real-denot {e = det} (Hsem ₀) H⊆ f

  app-real-denot : {cs : Coeff ^ n} → ⟦ treals n cs ⇒[ e ] T ⟧ᵀ Θ → ⟦ T ⟧ᵀ (cs ++ Θ)
  app-real-denot f =
    f (⊆-++⁺ˡ _ ⊆-refl) λ i → _ , 𝔉-proj′ (⊆-++⁺ʳ _ ⊆-refl) i

  if-denot : ⟦ treal P ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ
  if-denot {T = treal c} (s , Hs) (s₁ , Hs₁) (s₂ , Hs₂) =
    let g θ = λ {₀ → s θ ; ₁ → s₁ θ ; ₂ → s₂ θ }
        Hg = λ {₀ → Hs ; ₁ → Hs₁ ; ₂ → Hs₂ }
    in
    _ , 𝔉-compose {g = g} Hg 𝔉-cond
  if-denot {T = T₁ ⇒[ _ ] T₂} s s₁ s₂ H⊆ x =
    if-denot (weaken H⊆ s) (s₁ H⊆ x) (s₂ H⊆ x)
  if-denot {T = ttup n Ts} s s₁ s₂ i = if-denot s (s₁ i) (s₂ i)
  if-denot {T = tdist T} s s₁ s₂ _ = if-denot s (s₁ ₀) (s₂ ₀)


  ⟦_⟧ : Γ ⊢ t :[ e ] T → {Θ : Coeff ^ n} → ⟦ Γ ⟧ᴱ Θ → ⟦ T ⟧ᵀ Θ
  ⟦ tvar ⟧ (x All.∷ _) = x
  ⟦ tabs (Иi As Habs) ⟧ γ H⊆ s =
    ⟦ Habs (new As) {{unfinite As}} ⟧ (s All.∷ weaken-env H⊆ γ)
  ⟦ tapp Hf Ht ⟧ γ = ⟦ Hf ⟧ γ ⊆-refl (⟦ Ht ⟧ γ)
  ⟦ tprim {ϕ = ϕ} {cs = cs} Hϕ _ Htypes ⟧ {Θ} γ =
    _ , 𝔉-compose (λ i → ⟦ Htypes i ⟧ γ .π₂) (𝔉-prim Hϕ)
  ⟦ treal {r = r} ⟧ _ = _ , 𝔉-compose {g = λ _ ()} (λ ()) (𝔉-const r)
  ⟦ ttup _ Htypes ⟧ γ i = ⟦ Htypes i ⟧ γ
  ⟦ tproj i Htype ⟧ γ = ⟦ Htype ⟧ γ i
  ⟦ tif Htype Htype₁ Htype₂ ⟧ γ =
    if-denot (⟦ Htype ⟧ γ) (⟦ Htype₁ ⟧ γ) (⟦ Htype₂ ⟧ γ)
  ⟦ tdiff {n = n} {m} {cs = cs} {ds} H≤ Htype Htype₁ ⟧ {Θ} γ =
    abs-real-denot {T = treals m ds} {e = det} λ j →
    _ , 𝔉-compose
         ((𝔉-compose′ getΘ (λ i → ⟦ Htype₁ ⟧ γ i .π₂) <++> getAs) <++> getΘ)
         (𝔉-diff _ H≤ (fapp _ .π₂))
    where
      fapp = app-real-denot {e = det} {T = treals m ds} (⟦ Htype ⟧ γ)
      _<++>_ = 𝔉-++
      getAs = 𝔉-proj′ (⊆-++⁺ʳ _ ⊆-refl)
      getΘ = 𝔉-proj′ (⊆-++⁺ˡ _ ⊆-refl)
  ⟦ tsolve Htype Htype₁ Htype₂ H≤ ⟧ = {!!}
  ⟦ tdist _ _ _ ⟧ = {!!}
  ⟦ tassume Htype ⟧ γ = ⟦ Htype ⟧ γ ₀
  ⟦ tweight Htype ⟧ γ ()
  ⟦ tinfer Htype _ ⟧ γ _ = ⟦ Htype ⟧ γ ⊆-refl λ ()
  ⟦ tweaken Htype x x₁ ⟧ = {!!}
  ⟦ tsub Htype x x₁ ⟧ = {!!}
  ⟦ tpromote Htype x ⟧ = {!!}
