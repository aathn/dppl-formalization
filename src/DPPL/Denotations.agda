open import Lib.Algebra.Reals

module DPPL.Denotations (R : Reals₀) where

open Reals R using (ℝ)

open import DPPL.Regularity
open import DPPL.Syntax R
open import DPPL.Typing R

open import Lib.Data.Vector
open import Lib.Data.Dec
open import Lib.LocallyNameless.Unfinite
open import Lib.Syntax.Env

open import Cat.Prelude
open import Cat.Functor.Base
open import Cat.Functor.Compose
open import Data.Dec.Base
open import Data.Power
open import Order.Base

open SyntaxVars

-- open import Data.Fin using (splitAt)
-- open import Data.Fin.Properties using (toℕ<n)
-- open import Data.List.Relation.Unary.All as All using (All)
-- open import Data.Vec.Functional
-- open import Relation.Unary using (_∈_; Pred)
-- open import Relation.Binary.PropositionalEquality using (subst₂)
-- import Data.List.Relation.Binary.Sublist.Propositional as Sub

-- private
--   variable
--     n m k : ℕ
--     Θ : Coeff ^ n
--     Θ′ : Coeff ^ m
--     Θ″ : Coeff ^ k

open Reg↓≤ using (_≤_ ; ≤-refl ; ≤-trans)

is-const : ℙ (ℝ ^ m → ℝ ^ n)
is-const {n = n} f = elΩ (Σ[ x ∈ ℝ ^ n ] f ≡ λ _ → x) 

record DenotAssumptions : Type₁ where
  field
    ⟨_⟩-reg : Coeff → ∀ {m n} → ℙ (ℝ ^ m → ℝ ^ n)
    ⊆-reg : c ≤ c' → ⟨ c' ⟩-reg {m} {n} ⊆ ⟨ c ⟩-reg

    id-reg : (λ x → x) ∈ ⟨ c ⟩-reg {m}
    const-reg : (x : ℝ ^ n) → (λ _ → x) ∈ ⟨ c ⟩-reg {m}
    ∘-reg
      : {m n k : Nat} {f : ℝ ^ n → ℝ ^ k} {g : ℝ ^ m → ℝ ^ n}
      → f ∈ ⟨ c ⟩-reg → g ∈ ⟨ c ⟩-reg → f ⊙ g ∈ ⟨ c ⟩-reg

  [_,_]-reg : Coeff → Coeff → ∀ {m n} → ℙ (ℝ ^ m → ℝ ^ n)
  [_,_]-reg c d =
    ifᵈ DecOrd-Reg↓ {c} {d} then
      ⟨ c ⟩-reg
    else
      is-const

--     ⟦_⟧ᴾ : (ϕ : Prim) → ℝ ^ PrimAr ϕ → ℝ

--     𝐷 :
--       (f : ℝ ^ n → ℝ)
--       (_ : ∀ i → π[ i ] Θ ≤′ P)
--       (_ : f ∈ 𝔉 Θ c)
--       → -----------------------
--       ℝ ^ (n + n) → ℝ

--   𝔉′ : (Θ : Coeff ^ n) (Θ′ : Coeff ^ m) → Pred (ℝ ^ n → ℝ ^ m) ℓ₀
--   𝔉′ Θ Θ′ f = (i : Fin _) → π[ i ] ∘ f ∈ 𝔉 Θ (π[ i ] Θ′)

--   field
--     𝔉-const : (r : ℝ) → const r ∈ 𝔉 [] A

--     𝔉-proj : id ∈ 𝔉′ Θ Θ

--     𝔉-cond :
--       (λ θ → if θ ₀ ≲? 0ᴿ then θ ₁ else θ ₂)
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
--       → ------------------------------------------
--       f ∈ 𝔉 Θ c → f ∈ 𝔉 (map (c′ ⊔′_) Θ) (c′ ⊔′ c)

--     𝔉-prim :
--       {Θ : Coeff ^ PrimAr ϕ}
--       (_ : PrimTy ϕ ≡ (Θ , c))
--       → ----------------------
--       ⟦ ϕ ⟧ᴾ ∈ 𝔉 Θ c

--     𝔉-diff :
--       {Θ′ : Coeff ^ m}
--       (f : ℝ ^ (n + m) → ℝ)
--       (H≤ : ∀ i → π[ i ] Θ ≤′ P)
--       (Hf : f ∈ 𝔉 (Θ ++ Θ′) c)
--       (Hf′ : ∀ θ′ → (λ θ → f (θ ++ θ′)) ∈ 𝔉 Θ c)
--       → ----------------------------------------------
--       (λ xvθ → 𝐷 _ H≤ (Hf′ (drop _ xvθ)) (take _ xvθ))
--         ∈ 𝔉 ((Θ ++ replicate n A) ++ Θ′) c


-- module 𝔉-lemmas (Ass : DenotAssumptions) where
--   open DenotAssumptions Ass

--   𝔉-const′ : (θ : ℝ ^ n) → const θ ∈ 𝔉′ Θ Θ′
--   𝔉-const′ {Θ = Θ} θ i =
--     𝔉-compose {Θ′ = λ ()} {g = λ _ ()} (λ ()) $
--     subst₂ (λ Θ Θ′ → const (θ i) ∈ 𝔉 Θ Θ′)
--       (funext λ ()) (i≥j⇒i⊔′j≡i 0≤)
--       (𝔉-promote (𝔉-const _))

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


module Denotations (Ax : DenotAssumptions) where
  open DenotAssumptions Ax

  [,]-reg-≤ : c ≤ c' → [ c , c' ]-reg {m} {n} ≡ ⟨ c ⟩-reg
  [,]-reg-≤ {c = c} {c'} H≤ = ifᵈ-yes (DecOrd-Reg↓ {c} {c'}) (true-is-yes H≤)

  [,]-reg-≰ : ¬ c ≤ c' → [ c , c' ]-reg {m} {n} ≡ is-const
  [,]-reg-≰ {c = c} {c'} H≰ = ifᵈ-no (DecOrd-Reg↓ {c} {c'}) (false-is-no H≰)

  id-reg' : (λ x → x) ∈ [ c , c ]-reg {m}
  id-reg' {c = c} =
    subst ((λ x → x) ∈_) (sym $ [,]-reg-≤ {c} {c} (≤-refl {c})) id-reg

  const-reg' : (x : ℝ ^ n) → (λ _ → x) ∈ [ c , c' ]-reg {m}
  const-reg' {c = c} {c'} x with DecOrd-Reg↓ {c} {c'}
  ... | yes _ = const-reg x
  ... | no  _ = inc (_ , refl)

  ∘-reg'
    : {c d e : Coeff} {m n k : Nat} {f : ℝ ^ n → ℝ ^ k} {g : ℝ ^ m → ℝ ^ n}
    → f ∈ [ d , e ]-reg → g ∈ [ c , d ]-reg → f ⊙ g ∈ [ c , e ]-reg
  ∘-reg' {c} {d} {e} {f = f} {g} Hf Hg with DecOrd-Reg↓ {c} {d}
  ... | no c≰d =
    □-rec ([ c , e ]-reg _ .is-tr)
      (λ (x , Hg') →
        subst (λ g → f ⊙ g ∈ [ c , e ]-reg) (sym Hg') (const-reg' {c = c} {e} (f x)))
      Hg
  ... | yes c≤d with DecOrd-Reg↓ {d} {e}
  ... | no d≰e =
    □-rec ([ c , e ]-reg _ .is-tr)
      (λ (x , Hf') →
        subst (λ f → f ⊙ g ∈ [ c , e ]-reg) (sym Hf') (const-reg' {c = c} {e} x))
      Hf
  ... | yes d≤e = 
    subst (_ ∈_) (sym $ [,]-reg-≤ {c} {e} (≤-trans {c} {d} {e} c≤d d≤e))
      (∘-reg (⊆-reg c≤d _ Hf) Hg)

  module _ where
    open Precategory
  
    ℛ : Precategory lzero lzero
    ℛ .Ob = Nat × Coeff
    ℛ .Hom (m , c) (n , d) = Σ[ f ∈ (ℝ ^ m → ℝ ^ n) ] f ∈ [ c , d ]-reg
    ℛ .Hom-set _ _ _ _ = hlevel 1
    ℛ .id {m , c} = (λ x → x) , id-reg' {c}
    ℛ ._∘_ {_ , c} {_ , d} {_ , e} (f , Hf) (g , Hg) =
      f ⊙ g , ∘-reg' {c} {d} {e} Hf Hg
    ℛ .idr f = refl ,ₚ prop!
    ℛ .idl g = refl ,ₚ prop!
    ℛ .assoc f g h = refl ,ₚ prop!

  𝔇 : Precategory _ _
  𝔇 = PSh lzero ℛ

  open Functor

  μ⟨_⟩ : Coeff → Functor ℛ ℛ
  μ⟨ c ⟩ .F₀ (m , d) =
    ifᵈ DecOrd-Reg↓ {d} {c} then
      (m , d)
    else
      (0 , A↓)
  μ⟨ c ⟩ .F₁ {m , d} {n , e} f = {!!}
  μ⟨ c ⟩ .F-id = {!!}
  μ⟨ c ⟩ .F-∘ = {!!}

  □⟨_⟩ : Coeff → Functor 𝔇 𝔇
  □⟨ c ⟩ = precompose (op μ⟨ c ⟩)

  -- 𝔇𝟙 : 𝔇
  -- 𝔇𝟙 _ = ⊤

  -- 𝔇ℝ[_] : Ob → 𝔇
  -- 𝔇ℝ[ n , c ] (m , d) = Σ[ f ∈ (ℝ ^ m → ℝ ^ n) ] f ∈ [ d , c ]-reg

  -- 𝔇Π : 𝔇 ^ n → 𝔇
  -- 𝔇Π Xs (m , d) = ∀ i → Xs i (m , d)

  -- _𝔇⇒_ : 𝔇 → 𝔇 → 𝔇
  -- (X 𝔇⇒ Y) (n , c) = 𝔇-hom (𝔇Π (pair 𝔇ℝ[ n , c ] X)) Y

  -- Ty-denot : Ty → 𝔇
  -- Ty-denot (treal c)           = 𝔇ℝ[ 1 , c ]
  -- Ty-denot (T ⇒[ c , det ] T') = □⟨ c ⟩ (Ty-denot T 𝔇⇒ Ty-denot T')
  -- Ty-denot (ttup n Ts)         = 𝔇Π (λ i → Ty-denot (Ts i))
  -- Ty-denot (_ ⇒[ _ , rnd ] _)  = 𝔇𝟙
  -- Ty-denot (tdist _)           = 𝔇𝟙

  -- instance
  --   ⟦⟧-Ty : ⟦⟧-notation Ty
  --   ⟦⟧-Ty = brackets _ Ty-denot
  -- ⟦ treal c ⟧ᵀ Θ = ∃ (𝔉 Θ c)
  -- ⟦ T₁ ⇒[ det ] T₂ ⟧ᵀ Θ = {m : ℕ} {Θ′ : Coeff ^ m} → Θ ⊆ Θ′ → ⟦ T₁ ⟧ᵀ Θ′ → ⟦ T₂ ⟧ᵀ Θ′
  -- ⟦ ttup n Ts ⟧ᵀ Θ = (i : Fin n) → ⟦ Ts i ⟧ᵀ Θ
  -- -- Probabilistic subterms are interpreted trivially for the time being.
  -- ⟦ T₁ ⇒[ rnd ] T₂ ⟧ᵀ Θ = 𝟙
  -- ⟦ tdist T ⟧ᵀ Θ = 𝟙

--   ⟦_⟧ᴱ : TyEnv → Coeff ^ n → Set
--   ⟦ Γ ⟧ᴱ Θ = All (λ (_ , T) → ⟦ T ⟧ᵀ Θ) Γ


--   weaken : Θ ⊆ Θ′ → ⟦ T ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ′
--   weaken {T = treal c} H⊆ (_ , Hf) = _ , 𝔉-weaken H⊆ Hf
--   weaken {T = T₁ ⇒[ det ] T₂} H⊆ Hf {Θ′ = Θ′} H⊆′ =
--     Hf (⊆-trans {zs = Θ′} H⊆ H⊆′)
--   weaken {T = T₁ ⇒[ rnd ] T₂} _ _ = tt
--   weaken {T = ttup n Ts} H⊆ Hsem i = weaken H⊆ (Hsem i)
--   weaken {T = tdist T} H⊆ Hsem = tt

--   weaken-env : Θ ⊆ Θ′ → ⟦ Γ ⟧ᴱ Θ → ⟦ Γ ⟧ᴱ Θ′
--   weaken-env H⊆ = All.map (weaken H⊆)

--   weaken-Γ : Γ Sub.⊆ Γ′ → ⟦ Γ′ ⟧ᴱ Θ → ⟦ Γ ⟧ᴱ Θ
--   weaken-Γ Sub.[] HΓ′ = HΓ′
--   weaken-Γ (y Sub.∷ʳ H⊆) (_ All.∷ HΓ′) = weaken-Γ H⊆ HΓ′
--   weaken-Γ (refl Sub.∷ H⊆) (px All.∷ HΓ′) = px All.∷ weaken-Γ H⊆ HΓ′

--   sub-compat : T <: T′ → ⟦ T ⟧ᵀ Θ → ⟦ T′ ⟧ᵀ Θ
--   sub-compat (sreal H≤) (f , Hf) = f , 𝔉-sub (λ _ → ≤refl) H≤ Hf
--   sub-compat (stup Hsub) HT i = sub-compat (Hsub i) (HT i)
--   sub-compat (sarr {e = det} {e′ = det} Hsub Hsub₁ H≤) HT H⊆ HT₁ =
--     sub-compat Hsub₁ (HT H⊆ (sub-compat Hsub HT₁))
--   sub-compat (sarr {e′ = rnd} Hsub Hsub₁ H≤) HT = tt
--   sub-compat (sdist _) _ = tt

--   abs-real-denot : {cs : Coeff ^ n} → ⟦ T ⟧ᵀ (cs ++ Θ) → ⟦ treals n cs ⇒[ det ] T ⟧ᵀ Θ
--   abs-real-denot {n = n} {T = treal c′} {cs = cs} f {Θ′ = Θ′} H⊆ xs
--     with f , Hf ← weaken (⊆-++⁺ ⊆-refl H⊆) f = _ , 𝔉-compose Hg Hf
--     where
--       Hg : (λ θ → (λ i → xs i .π₁ θ) ++ θ) ∈ 𝔉′ Θ′ (cs ++ Θ′)
--       Hg i with splitAt n i
--       ... | ι₁ i = xs i .π₂
--       ... | ι₂ i = 𝔉-proj i
--   abs-real-denot {T = T₁ ⇒[ det ] T₂} {cs = cs} Hf H⊆ xs {Θ′ = Θ′} H⊆′ s =
--     abs-real-denot fs ⊆-refl λ i → _ , 𝔉-weaken H⊆′ (xs i .π₂)
--     where
--       fs : ⟦ T₂ ⟧ᵀ (cs ++ Θ′)
--       fs = Hf (⊆-++⁺ ⊆-refl (⊆-trans {zs = Θ′} H⊆ H⊆′)) (weaken (⊆-++⁺ˡ _ ⊆-refl) s)
--   abs-real-denot {T = T₁ ⇒[ rnd ] T₂} {cs = cs} _ _ _ = tt
--   abs-real-denot {T = ttup n Ts} Hsem H⊆ f i = abs-real-denot (Hsem i) H⊆ f
--   abs-real-denot {T = tdist T} Hsem H⊆ f = tt

--   app-real-denot : {cs : Coeff ^ n} → ⟦ treals n cs ⇒[ det ] T ⟧ᵀ Θ → ⟦ T ⟧ᵀ (cs ++ Θ)
--   app-real-denot f =
--     f (⊆-++⁺ˡ _ ⊆-refl) λ i → _ , 𝔉-proj′ (⊆-++⁺ʳ _ ⊆-refl) i

--   if-denot : ⟦ treal P ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ
--   if-denot {T = treal c} (s , Hs) (s₁ , Hs₁) (s₂ , Hs₂) =
--     let g θ = λ {₀ → s θ ; ₁ → s₁ θ ; ₂ → s₂ θ }
--         Hg = λ {₀ → Hs ; ₁ → Hs₁ ; ₂ → Hs₂ }
--     in
--     _ , 𝔉-compose {g = g} Hg 𝔉-cond
--   if-denot {T = T₁ ⇒[ det ] T₂} s s₁ s₂ H⊆ x =
--     if-denot (weaken H⊆ s) (s₁ H⊆ x) (s₂ H⊆ x)
--   if-denot {T = T₁ ⇒[ rnd ] T₂} s s₁ s₂ = tt
--   if-denot {T = ttup n Ts} s s₁ s₂ i = if-denot s (s₁ i) (s₂ i)
--   if-denot {T = tdist T} s s₁ s₂ = tt

--   ⟦_⟧ : Γ ⊢ t :[ c , det ] T → {Θ : Coeff ^ n} → ⟦ Γ ⟧ᴱ Θ → ⟦ c ⊙ T ⟧ᵀ Θ
--   ⟦ tvar H∈ H≤ _ ⟧ {Θ} γ =
--     subst (λ T → ⟦ T ⟧ᵀ Θ) (symm $ ≤ᶜ⇒⊙ H≤) $ All.lookup γ (Sub.to∈ H∈)
--   ⟦ tabs {e = det} (Иi As Habs) ⟧ {Θ} γ H⊆ s =
--     ⟦ Habs (new As) {{unfinite As}} ⟧ (s All.∷ weaken-env H⊆ γ)
--   ⟦ tabs {e = rnd} Habs ⟧ _ = tt
--   ⟦ tapp Hf Ht ⟧ {Θ} γ = ⟦ Hf ⟧ γ ⊆-refl (⟦ Ht ⟧ γ)
--   ⟦ tprim Hϕ _ Hts ⟧ {Θ} γ =
--     _ , 𝔉-compose (λ i → ⟦ Hts i ⟧ γ .π₂) (𝔉-promote (𝔉-prim Hϕ))
--   ⟦ treal {r = r} _ ⟧ {Θ} γ =
--     _ , 𝔉-compose {g = λ _ ()} (λ ()) (𝔉-promote (𝔉-const r))
--   ⟦ ttup _ Hts ⟧ {Θ} γ i = ⟦ Hts i ⟧ γ
--   ⟦ tproj i Ht ⟧ {Θ} γ = ⟦ Ht ⟧ γ i
--   ⟦ tif Ht Ht₁ Ht₂ ⟧ {Θ} γ =
--     if-denot (⟦ Ht ⟧ γ) (⟦ Ht₁ ⟧ γ) (⟦ Ht₂ ⟧ γ)
--   ⟦ tdiff {n = n} {m} {c} {cs = cs} {cs′} H≤₁ H≤₂ Hf Ht ⟧ {Θ} γ =
--     abs-real-denot {T = c ⊙ treals m cs′} λ j →
--       let fapp = app-real-denot {T = c ⊙ treals m cs′} (⟦ Hf ⟧ γ)
--           fdiff = 𝔉-diff _ (λ i → ⊔′.⊔-lub H≤₂ (H≤₁ i))
--                          (fapp j .π₂) (λ θ → 𝔉-papply (fapp j .π₂) θ)
--       in
--       _ , 𝔉-compose
--            ((𝔉-compose′ getΘ (λ i → ⟦ Ht ⟧ γ i .π₂) <++> getAs) <++> getΘ)
--            (𝔉-sub sig-≤ ≤refl fdiff)
--     where
--       _<++>_ = 𝔉-++
--       getAs = 𝔉-proj′ (⊆-++⁺ʳ _ ⊆-refl)
--       getΘ = 𝔉-proj′ (⊆-++⁺ˡ _ ⊆-refl)
--       sig-≤ : ∀ i →
--         π[ i ] ((map (c ⊔′_) cs ++ replicate n A) ++ Θ) ≤′
--         π[ i ] ((map (c ⊔′_) cs ++ replicate n (c ⊔′ A)) ++ Θ)
--       sig-≤ i with splitAt (n + n) i
--       ... | ι₂ j = ≤refl
--       ... | ι₁ i′ with splitAt n i′
--       ...   | ι₁ k = ≤refl
--       ...   | ι₂ l = ⊔′.x≤y⊔x _ _
--   ⟦ tsolve Hf Ht₁ Ht₂ ⟧ {Θ} γ = {!!}
--   ⟦ tdist HD _ Hts ⟧ {Θ} γ = tt
--   ⟦ tinfer Ht ⟧ {Θ} γ = tt
--   ⟦ tsub {e = det} Ht _ Hsub ⟧ {Θ} γ =
--     sub-compat (sub-⊙-mono Hsub) $ ⟦ Ht ⟧ γ
--   ⟦ tpromote Ht H≤ ⟧ {Θ} γ =
--     subst (λ T → ⟦ T ⟧ᵀ Θ) H≡ $ ⟦ Ht ⟧ γ
--     where H≡ = ap (_⊙ _) (symm $ i≤j⇒i⊔′j≡j H≤) ； ⊙-action _
--   ⟦ tdemote Ht H≤ ⟧ {Θ} γ =
--     subst (λ T → ⟦ T ⟧ᵀ Θ) H≡ $ ⟦ Ht ⟧ γ
--     where H≡ = symm (⊙-action _) ； ap (_⊙ _) (i≤j⇒i⊔′j≡j H≤)
