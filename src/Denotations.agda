open import Lib.Reals

module Denotations (R : Reals₀) where

open Reals R using (ℝ; 0ᴿ; _≲?_)

open import Syntax R hiding (n; m)
open import Typing R

open import Properties.Typing R

open import Lib.Prelude hiding ([]; _∷_; _∈_)
open import Lib.LocallyNameless.Unfinite
open import Lib.Env hiding ([]; _∷_)
open import Lib.Subvec
open import Lib.Util

open import Data.Fin using (splitAt)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Vec.Functional
open import Relation.Unary using (_∈_; Pred)
import Data.List.Relation.Binary.Sublist.Propositional as Sub

private
  variable
    n m k : ℕ
    Θ : Coeff ^ n
    Θ′ : Coeff ^ m
    Θ″ : Coeff ^ k

record DenotAssumptions : Set₁ where
  field
    𝔉 : (Θ : Coeff ^ n) → Coeff → Pred (ℝ ^ n → ℝ) ℓ₀

    ⟦_⟧ᴾ : (ϕ : Prim) → ℝ ^ PrimAr ϕ → ℝ

    𝐷 :
      (f : ℝ ^ n → ℝ)
      (_ : ∀ i → π[ i ] Θ ≤′ P)
      (_ : f ∈ 𝔉 Θ c)
      → -----------------------
      ℝ ^ (n + n) → ℝ

  𝔉′ : (Θ : Coeff ^ n) (Θ′ : Coeff ^ m) → Pred (ℝ ^ n → ℝ ^ m) ℓ₀
  𝔉′ Θ Θ′ f = (i : Fin _) → π[ i ] ∘ f ∈ 𝔉 Θ (π[ i ] Θ′)

  field
    𝔉-const : (r : ℝ) → const r ∈ 𝔉 [] N

    𝔉-proj : id ∈ 𝔉′ Θ Θ

    𝔉-cond :
      (λ θ → if θ ₀ ≲? 0ᴿ then θ ₁ else θ ₂)
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

    𝔉-prim :
      {Θ : Coeff ^ PrimAr ϕ}
      (_ : PrimTy ϕ ≡ (Θ , c))
      → ----------------------
      ⟦ ϕ ⟧ᴾ ∈ 𝔉 Θ c

    𝔉-diff :
      {Θ′ : Coeff ^ m}
      (f : ℝ ^ (n + m) → ℝ)
      (H≤ : ∀ i → π[ i ] Θ ≤′ P)
      (Hf : f ∈ 𝔉 (Θ ++ Θ′) c)
      (Hf′ : ∀ θ′ → (λ θ → f (θ ++ θ′)) ∈ 𝔉 Θ c)
      → ----------------------------------------------
      (λ xvθ → 𝐷 _ H≤ (Hf′ (drop _ xvθ)) (take _ xvθ))
        ∈ 𝔉 ((Θ ++ replicate n A) ++ Θ′) c


module 𝔉-lemmas (Ass : DenotAssumptions) where
  open DenotAssumptions Ass

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


module Denotations (Ass : DenotAssumptions) where
  open 𝔉-lemmas Ass
  open DenotAssumptions Ass

  ⟦_⟧ᵀ : Type → Coeff ^ n → Set
  ⟦ treal c ⟧ᵀ Θ = ∃ (𝔉 Θ c)
  ⟦ T₁ ⇒[ det ] T₂ ⟧ᵀ Θ = {m : ℕ} {Θ′ : Coeff ^ m} → Θ ⊆ Θ′ → ⟦ T₁ ⟧ᵀ Θ′ → ⟦ T₂ ⟧ᵀ Θ′
  ⟦ ttup n Ts ⟧ᵀ Θ = (i : Fin n) → ⟦ Ts i ⟧ᵀ Θ
  -- Probabilistic subterms are interpreted trivially for the time being.
  ⟦ T₁ ⇒[ rnd ] T₂ ⟧ᵀ Θ = 𝟙
  ⟦ tdist T ⟧ᵀ Θ = 𝟙

  ⟦_⟧ᴱ : TyEnv → Coeff ^ n → Set
  ⟦ Γ ⟧ᴱ Θ = All (λ (_ , T) → ⟦ T ⟧ᵀ Θ) Γ


  weaken : Θ ⊆ Θ′ → ⟦ T ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ′
  weaken {T = treal c} H⊆ (_ , Hf) = _ , 𝔉-weaken H⊆ Hf
  weaken {T = T₁ ⇒[ det ] T₂} H⊆ Hf {Θ′ = Θ′} H⊆′ =
    Hf (⊆-trans {zs = Θ′} H⊆ H⊆′)
  weaken {T = T₁ ⇒[ rnd ] T₂} _ _ = tt
  weaken {T = ttup n Ts} H⊆ Hsem i = weaken H⊆ (Hsem i)
  weaken {T = tdist T} H⊆ Hsem = tt

  weaken-env : Θ ⊆ Θ′ → ⟦ Γ ⟧ᴱ Θ → ⟦ Γ ⟧ᴱ Θ′
  weaken-env H⊆ = All.map (weaken H⊆)

  weaken-Γ : Γ Sub.⊆ Γ′ → ⟦ Γ′ ⟧ᴱ Θ → ⟦ Γ ⟧ᴱ Θ
  weaken-Γ Sub.[] HΓ′ = HΓ′
  weaken-Γ (y Sub.∷ʳ H⊆) (_ All.∷ HΓ′) = weaken-Γ H⊆ HΓ′
  weaken-Γ (refl Sub.∷ H⊆) (px All.∷ HΓ′) = px All.∷ weaken-Γ H⊆ HΓ′

  sub-compat : T <: T′ → ⟦ T ⟧ᵀ Θ → ⟦ T′ ⟧ᵀ Θ
  sub-compat (sreal H≤) (f , Hf) = f , 𝔉-sub (λ _ → ≤refl) H≤ Hf
  sub-compat (stup Hsub) HT i = sub-compat (Hsub i) (HT i)
  sub-compat (sarr {e = det} {e′ = det} Hsub Hsub₁ H≤) HT H⊆ HT₁ =
    sub-compat Hsub₁ (HT H⊆ (sub-compat Hsub HT₁))
  sub-compat (sarr {e′ = rnd} Hsub Hsub₁ H≤) HT = tt
  sub-compat (sdist _) _ = tt

  abs-real-denot : {cs : Coeff ^ n} → ⟦ T ⟧ᵀ (cs ++ Θ) → ⟦ treals n cs ⇒[ det ] T ⟧ᵀ Θ
  abs-real-denot {n = n} {T = treal c′} {cs = cs} f {Θ′ = Θ′} H⊆ xs
    with f , Hf ← weaken (⊆-++⁺ ⊆-refl H⊆) f = _ , 𝔉-compose Hg Hf
    where
      Hg : (λ θ → (λ i → xs i .π₁ θ) ++ θ) ∈ 𝔉′ Θ′ (cs ++ Θ′)
      Hg i with splitAt n i
      ... | ι₁ i = xs i .π₂
      ... | ι₂ i = 𝔉-proj i
  abs-real-denot {T = T₁ ⇒[ det ] T₂} {cs = cs} Hf H⊆ xs {Θ′ = Θ′} H⊆′ s =
    abs-real-denot fs ⊆-refl λ i → _ , 𝔉-weaken H⊆′ (xs i .π₂)
    where
      fs : ⟦ T₂ ⟧ᵀ (cs ++ Θ′)
      fs = Hf (⊆-++⁺ ⊆-refl (⊆-trans {zs = Θ′} H⊆ H⊆′)) (weaken (⊆-++⁺ˡ _ ⊆-refl) s)
  abs-real-denot {T = T₁ ⇒[ rnd ] T₂} {cs = cs} _ _ _ = tt
  abs-real-denot {T = ttup n Ts} Hsem H⊆ f i = abs-real-denot (Hsem i) H⊆ f
  abs-real-denot {T = tdist T} Hsem H⊆ f = tt

  app-real-denot : {cs : Coeff ^ n} → ⟦ treals n cs ⇒[ det ] T ⟧ᵀ Θ → ⟦ T ⟧ᵀ (cs ++ Θ)
  app-real-denot f =
    f (⊆-++⁺ˡ _ ⊆-refl) λ i → _ , 𝔉-proj′ (⊆-++⁺ʳ _ ⊆-refl) i

  if-denot : ⟦ treal P ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ
  if-denot {T = treal c} (s , Hs) (s₁ , Hs₁) (s₂ , Hs₂) =
    let g θ = λ {₀ → s θ ; ₁ → s₁ θ ; ₂ → s₂ θ }
        Hg = λ {₀ → Hs ; ₁ → Hs₁ ; ₂ → Hs₂ }
    in
    _ , 𝔉-compose {g = g} Hg 𝔉-cond
  if-denot {T = T₁ ⇒[ det ] T₂} s s₁ s₂ H⊆ x =
    if-denot (weaken H⊆ s) (s₁ H⊆ x) (s₂ H⊆ x)
  if-denot {T = T₁ ⇒[ rnd ] T₂} s s₁ s₂ = tt
  if-denot {T = ttup n Ts} s s₁ s₂ i = if-denot s (s₁ i) (s₂ i)
  if-denot {T = tdist T} s s₁ s₂ = tt

  term-denot : Γ ⊢ t :[ det ] T → c ≤ᴱ Γ → {Θ : Coeff ^ n} → ⟦ Γ ⟧ᴱ Θ → ⟦ c ⊙ T ⟧ᵀ Θ
  term-denot tvar (H≤ All.∷ _) {Θ} (x All.∷ _) =
    subst (λ T → ⟦ T ⟧ᵀ Θ) (symm $ ≤ᶜ⇒⊙ H≤) x
  term-denot (tabs {e = det} (Иi As Habs)) H≤ γ {Θ′ = Θ′} H⊆ s =
    subst (λ T → ⟦ T ⟧ᵀ Θ′) (≤ᶜ⇒⊙ A≤ᶜ) $
      term-denot
        (Habs (new As) {{unfinite As}}) A≤ᴱ
        (s All.∷ weaken-env H⊆ γ)
  term-denot (tabs {e = rnd} _) H≤ γ = tt
  term-denot (tapp Hf Ht) H≤ γ = {!!}
    -- term-denot Hf ? γ ⊆-refl ? -- (term-denot Ht ? γ)
  term-denot (tprim x x₁ x₂) H≤ γ = {!!}
  term-denot treal H≤ γ = {!!}
  term-denot (ttup _ Htypes) H≤ γ i = term-denot (Htypes i) H≤ γ
  term-denot (tproj i Htype) H≤ γ = term-denot Htype H≤ γ i
  term-denot (tif Htype Htype₁ Htype₂) H≤ γ = {!!}
  term-denot (tdiff x Htype Htype₁) H≤ γ = {!!}
  term-denot (tsolve Htype Htype₁ Htype₂ x) H≤ γ = {!!}
  term-denot (tdist _ _ _) H≤ γ = tt
  term-denot (tinfer _ _) H≤ γ = tt
  term-denot (tweaken Htype H⊆ _) H≤ γ =
    term-denot Htype (all-weaken H⊆ H≤) (weaken-Γ H⊆ γ)
  term-denot (tsub {e = det} Htype _ Hsub) H≤ γ =
    sub-compat (sub-⊙-mono Hsub) (term-denot Htype H≤ γ)
  term-denot (tpromote {T = T} Htype H≤′) H≤ {Θ} γ =
    subst (λ T → ⟦ T ⟧ᵀ Θ) (⊙-action T) $ term-denot Htype (≤ᴱ-lub H≤ H≤′) γ

  ⟦_⟧ : Γ ⊢ t :[ det ] T → {Θ : Coeff ^ n} → ⟦ Γ ⟧ᴱ Θ → ⟦ T ⟧ᵀ Θ
  ⟦ t ⟧ {Θ} γ =
    subst (λ T → ⟦ T ⟧ᵀ Θ) (≤ᶜ⇒⊙ A≤ᶜ) $ term-denot t A≤ᴱ γ

  -- ⟦ tvar ⟧ (x All.∷ _) = x
  -- ⟦ tabs {e = det} (Иi As Habs) ⟧ γ H⊆ s =
  --   ⟦ Habs (new As) {{unfinite As}} ⟧ (s All.∷ weaken-env H⊆ γ)
  -- ⟦ tabs {e = rnd} (Иi As Habs) ⟧ γ = tt
  -- ⟦ tapp Hf Ht ⟧ γ = ⟦ Hf ⟧ γ ⊆-refl (⟦ Ht ⟧ γ)
  -- ⟦ tprim {ϕ = ϕ} {cs = cs} Hϕ _ Htypes ⟧ {Θ} γ =
  --   _ , 𝔉-compose (λ i → ⟦ Htypes i ⟧ γ .π₂) (𝔉-prim Hϕ)
  -- ⟦ treal {r = r} ⟧ _ = _ , 𝔉-compose {g = λ _ ()} (λ ()) (𝔉-const r)
  -- ⟦ ttup _ Htypes ⟧ γ i = ⟦ Htypes i ⟧ γ
  -- ⟦ tproj i Htype ⟧ γ = ⟦ Htype ⟧ γ i
  -- ⟦ tif Htype Htype₁ Htype₂ ⟧ γ =
  --   if-denot (⟦ Htype ⟧ γ) (⟦ Htype₁ ⟧ γ) (⟦ Htype₂ ⟧ γ)
  -- ⟦ tdiff {n = n} {m} {cs = cs} {ds} H≤ Htype Htype₁ ⟧ {Θ} γ =
  --   abs-real-denot {T = treals m ds} λ j →
  --   _ , 𝔉-compose
  --        ((𝔉-compose′ getΘ (λ i → ⟦ Htype₁ ⟧ γ i .π₂) <++> getAs) <++> getΘ)
  --        (𝔉-diff _ H≤ (fapp _ .π₂))
  --   where
  --     fapp = app-real-denot {T = treals m ds} (⟦ Htype ⟧ γ)
  --     _<++>_ = 𝔉-++
  --     getAs = 𝔉-proj′ (⊆-++⁺ʳ _ ⊆-refl)
  --     getΘ = 𝔉-proj′ (⊆-++⁺ˡ _ ⊆-refl)
  -- ⟦ tsolve Htype Htype₁ Htype₂ H≤ ⟧ = {!!}
  -- ⟦ tdist _ _ _ ⟧ γ = tt
  -- ⟦ tinfer Htype _ ⟧ γ = tt
  -- ⟦ tweaken Htype H⊆ Hd ⟧ γ = ⟦ Htype ⟧ (weaken-Γ H⊆ γ)
  -- ⟦ tsub {e = det} Htype _ Hsub ⟧ γ = sub-compat Hsub (⟦ Htype ⟧ γ)
  -- ⟦ tpromote Htype H≤ ⟧ = {!!}
