open import Lib.Reals

module Properties.Preservation (R : Reals₀) where

open Reals R hiding (refl)
open Interval R

open import Lib.Prelude
open import Lib.LocallyNameless.Unfinite
open import Lib.FunExt
open import Lib.LocallyNameless.BindingSignature
open import Lib.EvalCtx
open import Lib.Env
open import Lib.Substitution

open import Data.Fin.Instances using (Fin-≡-isDecEquivalence)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List.Relation.Unary.AllPairs using ([])
open import Data.List.Relation.Binary.Sublist.Propositional using ([])
open import Data.Vec.Functional using (map ; updateAt)
open import Data.Vec.Functional.Properties using (updateAt-updates ; updateAt-minimal ; updateAt-updateAt)

open import Syntax R
open import Typing R
open import SmallStep R
open import Properties.Typing R
open import Properties.SmallStep R
open import Properties.Util

ctx-type-inv :
  {E : Term → Term}
  (_ : DetCtx E)
  (_ : Γ ⊢ E t :[ e ] T)
  → -----------------------------------------
  ∑ (e′ , T′) ∶ Eff × Type , Γ ⊢ t :[ e′ ] T′

ctx-type-inv (ectx {o} {j = j} _) Htype =
  let (e , T) , Htype′ = go j Htype
  in  _ ,
        subst (λ t → _ ⊢ t :[ e ] T)
              (updateAt-updates (ord {o = o} j) _) Htype′
  where
  go :
    {o : TermOp}
    {ts : Vector Term (length (TermAr o))}
    (j : Fin (len {o = o}))
    (_ : Γ ⊢ op (o , ts) :[ e ] T)
    → ----------------------------------------------------------
    ∑ (e′ , T′) ∶ Eff × Type , Γ ⊢ ts (ord {o = o} j) :[ e′ ] T′

  go ₀ (tapp Htype Htype₁) = _ , Htype
  go ₁ (tapp Htype Htype₁) = _ , Htype₁
  go j (tprim _ _ Htypes) = _ , Htypes j
  go j (ttup _ Htypes) = _ , Htypes j
  go ₀ (tproj i Htype) = _ , Htype
  go ₀ (tif Htype _ _) = _ , Htype
  go ₀ (tdiff _ Htype Htype₁) = _ , Htype
  go ₁ (tdiff _ Htype Htype₁) = _ , Htype₁
  go ₀ (tsolve Htype Htype₁ Htype₂ _) = _ , Htype
  go ₁ (tsolve Htype Htype₁ Htype₂ _) = _ , Htype₁
  go ₂ (tsolve Htype Htype₁ Htype₂ _) = _ , Htype₂
  go j (tdist _ _ Htypes) = _ , Htypes j
  go ₀ (tassume Htype) = _ , Htype
  go ₀ (tweight Htype) = _ , Htype
  go ₀ (tinfer Htype _) = _ , Htype
  go j (tweaken Htype H⊆ Hd) = _ , tweaken (go j Htype .π₂) H⊆ Hd
  go j (tsub Htype _ _) = _ , go j Htype .π₂
  go j (tpromote Htype H≤) = _ , tpromote (go j Htype .π₂) H≤

updateAt-type :
  {Γs : Vector TyEnv n}
  {es : Vector Eff n}
  {Ts : Vector Type n}
  {ts : Vector Term n}
  (j : Fin n)
  (_ : ∀ i → Γs i ⊢ ts i :[ es i ] Ts i)
  (_ : Γs j ⊢ t :[ es j ] Ts j)
  → ---------------------------------------------------
  (∀ i → Γs i ⊢ updateAt ts j (const t) i :[ es i ] Ts i)
updateAt-type {t = t} {ts = ts} j Htypes Htype i with (i ≐ j)
... | equ rewrite updateAt-updates j {const t} ts = Htype
... | neq H≢ rewrite updateAt-minimal _ _ {const t} ts H≢ = Htypes i

preservation-ctx :
  {E : Term → Term}
  {t₁ t₂ : Term}
  (_ : DetCtx E)
  (_ : ∀ {e T} → [] ⊢ t₁ :[ e ] T → [] ⊢ t₂ :[ e ] T)
  (_ : [] ⊢ E t₁ :[ e ] T)
  → ------------------
  [] ⊢ E t₂ :[ e ] T

preservation-ctx
  {t₁ = t₁} {t₂} (ectx {o} {j = j} {ts} _) Ht₁₂ Htype =
    let i = ord {o = o} j

        H₁ : ∀ {e T}
           → [] ⊢ updateAt ts i (const t₁) i :[ e ] T
           → [] ⊢ t₂ :[ e ] T
        H₁ = Ht₁₂ ∘ subst (λ t → _ ⊢ t :[ _ ] _) (updateAt-updates i ts)
    
        H₂ : [] ⊢ op (o , updateAt (updateAt ts i (const t₁)) i (const t₂)) :[ _ ] _
        H₂ = go j Htype H₁

        H₃ : [] ⊢ op (o , updateAt ts i (const t₂)) :[ _ ] _
        H₃ = subst (λ ts → _ ⊢ op (o , ts) :[ _ ] _) (funext $ updateAt-updateAt i ts) H₂

    in H₃
  where
  go : 
    {o : TermOp}
    {ts : Vector Term (length (TermAr o))}
    (j : Fin (len {o = o}))
    (_ : [] ⊢ op (o , ts) :[ e ] T)
    (_ : ∀ {e T} → [] ⊢ ts (ord {o = o} j) :[ e ] T → [] ⊢ t :[ e ] T)
    → ----------------------------------------------------------------
    [] ⊢ op (o , updateAt ts (ord {o = o} j) (const t)) :[ e ] T

  go ₀ (tapp Htype Htype₁) Ht = tapp (Ht Htype) Htype₁
  go ₁ (tapp Htype Htype₁) Ht = tapp Htype (Ht Htype₁)
  go j (tprim Hϕ Hd Htypes) Ht =
    tprim Hϕ Hd (updateAt-type j Htypes (Ht (Htypes j)))
  go j (ttup Hd Htypes) Ht =
    ttup Hd (updateAt-type j Htypes (Ht (Htypes j)))
  go ₀ (tproj i Htype) Ht = tproj i (Ht Htype)
  go ₀ (tif Htype Htype₁ Htype₂) Ht = tif (Ht Htype) Htype₁ Htype₂
  go ₀ (tdiff Hcs Htype Htype₁) Ht = tdiff Hcs (Ht Htype) Htype₁
  go ₁ (tdiff Hcs Htype Htype₁) Ht = tdiff Hcs Htype (Ht Htype₁)
  go ₀ (tsolve Htype Htype₁ Htype₂ H≤) Ht = tsolve (Ht Htype) Htype₁ Htype₂ H≤
  go ₁ (tsolve Htype Htype₁ Htype₂ H≤) Ht = tsolve Htype (Ht Htype₁) Htype₂ H≤
  go ₂ (tsolve Htype Htype₁ Htype₂ H≤) Ht = tsolve Htype Htype₁ (Ht Htype₂) H≤
  go j (tdist HD Hd Htypes) Ht =
    tdist HD Hd (updateAt-type j Htypes (Ht (Htypes j)))
  go ₀ (tassume Htype) Ht = tassume (Ht Htype)
  go ₀ (tweight Htype) Ht = tweight (Ht Htype)
  go ₀ (tinfer Htype H≤) Ht = tinfer (Ht Htype) H≤
  go j (tweaken Htype [] Hd) Ht = tweaken (go j Htype Ht) [] Hd
  go j (tsub Htype H≤ Hsub) Ht = tsub (go j Htype Ht) H≤ Hsub
  go j (tpromote Htype H≤) Ht = tpromote (go j Htype Ht) H≤


module _ (Ass : EvalAssumptions) where
  open Eval Ass
  open EvalAssumptions Ass

  record PresAssumptions : Set where
    field
      DiffPres :
        {t₀ t₁ : Term}
        {cs : Vector Coeff n}
        {ds : Vector Coeff m}
        (_ : ∀ i → cs i ≤′ P)
        (_ : Γ ⊢ t₀ :[ e ] treals n cs ⇒[ det ] treals m ds)
        (_ : Γ ⊢ t₁ :[ e ] treals n cs)
        (v₀ : IsValue t₀) (v₁ : IsValue t₁)
        → -----------------------------------------------------------------------
        Γ ⊢ Diff (_ , v₀) (_ , v₁) :[ e ] treals n (const A) ⇒[ det ] treals m ds

      SolvePres :
        {t₀ t₁ t₂ : Term}
        {Ts : Vector Type 2}
        {cs : Vector Coeff n}
        (_ : Γ ⊢ t₀ :[ e ] ttup 2 Ts ⇒[ det ] treals n cs)
        (_ : Ts ₀ ≡ treal c)
        (_ : Ts ₁ ≡ treals n cs)
        (_ : Γ ⊢ t₁ :[ e ] treals n cs)
        (_ : Γ ⊢ t₂ :[ e ] treal c)
        (v₀ : IsValue t₀) (v₁ : IsValue t₁) (v₂ : IsValue t₂)
        → -----------------------------------------------------
        Γ ⊢ Solve (_ , v₀) (_ , v₁) (_ , v₂) :[ e ] treals n cs

      SamplePres :
        {cs : Vector Coeff (DistAr D)}
        {rs : Vector ℝ (DistAr D)}
        (_ : DistTy D ≡ (cs , T))
        → -------------------------------
        [] ⊢ Sample D rs p .π₁ :[ det ] T

      InferPres :
        (_ : Γ ⊢ t :[ e ] tunit ⇒[ rnd ] T)
        (v : IsValue t)
        → ---------------------------------
        Γ ⊢ Infer (_ , v) p .π₁ :[ e ] T


  module Preservation (PAss : PresAssumptions) where
    open PresAssumptions PAss

    preservation-det-step :
      (_ : [] ⊢ t :[ e ] T)
      (_ : t →ᵈ t′)
      → -------------------
      [] ⊢ t′ :[ e ] T

    preservation-det-step (tapp {ts = ts} Htype Htype₁) (eapp {t = t} Heq Hv)
      rewrite Heq with Иi As Hcof ← tabs-inv Htype refl
      with x , ∉∪ ← fresh {𝔸} (As ∪ fv (t ₀))
      rewrite subst-intro {x = x} {0} {ts ₁} (t ₀) it =
      substitution-pres-typing (Hcof x) (val-type-det Htype₁ Hv)
    preservation-det-step (tprim Hϕ Htypes Hd) (eprim Heq) =
      tsub treal 0≤ (sreal (≤-1 (toℕ<n _)))
    preservation-det-step (tproj i Htype) (eproj .i Heq Hvs) rewrite Heq =
      ttup-inv Htype refl i
    preservation-det-step (tif Htype Htype₁ Htype₂) (eif {r} _) with r ≲? 0ᴿ
    ... | false = Htype₁
    ... | true  = Htype₂
    preservation-det-step (tdiff Hcs Htype Htype₁) (ediff Hv Hv₁) =
      DiffPres Hcs Htype Htype₁ Hv Hv₁
    preservation-det-step (tsolve Htype Htype₁ Htype₂ _) (esolve Hv Hv₁ Hv₂) =
      SolvePres Htype refl refl Htype₁ Htype₂ Hv Hv₁ Hv₂
    preservation-det-step (tweaken Htype [] Hd) Hstep =
      preservation-det-step Htype Hstep
    preservation-det-step (tsub Htype H≤ Hsub) Hstep =
      tsub (preservation-det-step Htype Hstep) H≤ Hsub
    preservation-det-step (tpromote Htype Heq) Hstep =
      tpromote (preservation-det-step Htype Hstep) Heq

    preservation-det : 
      (_ : [] ⊢ t :[ e ] T)
      (_ : t →det t′)
      → -------------------
      [] ⊢ t′ :[ e ] T

    preservation-det Htype (estep Hstep) = preservation-det-step Htype Hstep
    preservation-det Htype (econg Hctx Hstep) =
      let _ , Htype′ = ctx-type-inv Hctx Htype in
      preservation-ctx Hctx (λ Ht₁ → preservation-det Ht₁ Hstep) Htype


    preservation-rnd-step :
      {w w′ : ℝ}
      {s s′ : List 𝕀}
      (_ : [] ⊢ t :[ e ] T)
      (_ : (t , w , s) →ʳ (t′ , w′ , s′))
      → ---------------------------------
      [] ⊢ t′ :[ e ] T
    preservation-rnd-step Htype (edet Hstep) = preservation-det-step Htype Hstep
    preservation-rnd-step (tassume Htype) (eassumedist Heq) rewrite Heq
      with tassume-inv Htype refl
    ... | _ , _ , Heq , Hsub =
      tsub (SamplePres Heq) 0≤ Hsub
    preservation-rnd-step (tassume Htype) (eassumeinfer Heq Hv) rewrite Heq =
      InferPres (tinfer-inv Htype refl) Hv
    preservation-rnd-step (tweight Htype) (eweight Heq) =
      ttup [] (λ())
    preservation-rnd-step (tweaken Htype [] Hd) Hstep =
      preservation-rnd-step Htype Hstep
    preservation-rnd-step (tsub Htype H≤ Hsub) Hstep =
      tsub (preservation-rnd-step Htype Hstep) H≤ Hsub
    preservation-rnd-step (tpromote Htype Heq) Hstep =
      tpromote (preservation-rnd-step Htype Hstep) Heq

    preservation-rnd :
      {w w′ : ℝ}
      {s s′ : List 𝕀}
      (_ : [] ⊢ t :[ e ] T)
      (_ : (t , w , s) →rnd (t′ , w′ , s′))
      → -----------------------------------
      [] ⊢ t′ :[ e ] T

    preservation-rnd Htype (estep Hstep) = preservation-rnd-step Htype Hstep
    preservation-rnd Htype (econg (E , Hctx , refl) Hstep) =
      let _ , Htype′ = ctx-type-inv Hctx Htype in
      preservation-ctx Hctx (λ Ht₁ → preservation-rnd Ht₁ Hstep) Htype
