open import Lib.Algebra.Reals

module DPPL.Properties.SmallStep (R : Reals₀) where

open Reals R using (ℝ)
open Interval R

open import DPPL.Syntax R
open import DPPL.Typing R
open import DPPL.SmallStep R

-- Minor lemmas about the step relations (and typing)

open import Lib.Prelude
open import Lib.Data.Vector
open import Lib.LocallyNameless.BindingSignature
open import Lib.Syntax.EvalCtx

open SyntaxVars
open TypingVars
open EvalVars

-- IsValue is a proposition

IsValue-is-prop : is-prop (IsValue t)
IsValue-is-prop vabs vabs            = refl
IsValue-is-prop vreal vreal          = refl
IsValue-is-prop (vtup vs) (vtup vs') =
  ap vtup (funext λ i → IsValue-is-prop (vs i) (vs' i))
IsValue-is-prop (vinfer v) (vinfer v') =
  ap vinfer (IsValue-is-prop v v')

instance
  H-Level-IsValue : ∀ {n} → H-Level (IsValue t) (1 + n)
  H-Level-IsValue = basic-instance 1 IsValue-is-prop

-- Canonical forms

canonical-⇒ :
  {T₁ T₂ : Ty}
  (_ : Γ ⊢ t :[ e ] T)
  (_ : IsValue t)
  (_ : T ≡ᵢ T₁ ⇒[ c , e' ] T₂)
  → -------------------------------------------
  Σ[ T' ∈ Ty ] Σ[ t' ∈ Tm ^ 1 ] t ≡ lam T' ▸ t'

canonical-⇒ (tlam _) _ reflᵢ                   = _ , _ , refl
canonical-⇒ (tsub Hty _ (sarr _ _ _ _)) Hval _ = canonical-⇒ Hty Hval reflᵢ
canonical-⇒ (tpromote {T = _ ⇒[ _ , _ ] _} Hty _ _) Hval _ =
  canonical-⇒ Hty Hval reflᵢ

canonical-real :
  (_ : Γ ⊢ t :[ e ] T)
  (_ : IsValue t)
  (_ : T ≡ᵢ treal c)
  → -------------------
  Σ[ r ∈ ℝ ] t ≡ real r

canonical-real treal _ _                     = _ , refl
canonical-real (tsub Hty _ (sreal _)) Hval _ = canonical-real Hty Hval reflᵢ
canonical-real (tpromote {T = treal _} Hty _ _) Hval _ =
  canonical-real Hty Hval reflᵢ

canonical-tup :
  {Ts : Ty ^ n}
  (_ : Γ ⊢ t :[ e ] T)
  (_ : IsValue t)
  (_ : T ≡ᵢ ttup n Ts)
  → ----------------------------------------------------
  Σ[ ts ∈ Tm ^ n ] t ≡ tup n ▸ ts × ∀ i → IsValue (ts i)

canonical-tup (ttup Htys) (vtup Hvs) reflᵢ     = _ , refl , Hvs
canonical-tup (tsub Hty _ (stup _)) Hval reflᵢ = canonical-tup Hty Hval reflᵢ
canonical-tup (tpromote {T = ttup _ _} Hty _ _) Hval reflᵢ =
  canonical-tup Hty Hval reflᵢ

canonical-dist :
  (_ : Γ ⊢ t :[ e ] T)
  (_ : IsValue t)
  (_ : T ≡ᵢ tdist T')
  → -------------------------------------------
  Σ[ v ∈ Tm ^ 1 ] t ≡ infer ▸ v × IsValue (v ₀)

canonical-dist (tinfer Hty) (vinfer Hv) _    = _ , refl , Hv
canonical-dist (tsub Hty _ (sdist _)) Hval _ = canonical-dist Hty Hval reflᵢ
canonical-dist (tpromote {T = tdist _} Hty _ _) Hval _ =
  canonical-dist Hty Hval reflᵢ

val-type-det :
  (_ : Γ ⊢ t :[ e ] T)
  (_ : IsValue t)
  → ------------------
  Γ ⊢ t :[ det ] T
val-type-det (tsub Hty _ H<:) Hval = tsub (val-type-det Hty Hval) ≤-refl H<: where
  open Eff≤
val-type-det (tpromote Hty H≤ H⊆) Hval = tpromote (val-type-det Hty Hval) H≤ H⊆
val-type-det (tlam Hlam) _             = tlam Hlam
val-type-det treal _                   = treal
val-type-det (ttup Htys) (vtup Hvs)    = ttup λ i → val-type-det (Htys i) (Hvs i)
val-type-det (tinfer Hty) (vinfer Hv)  = tinfer (val-type-det Hty Hv)

module Step (Ax : EvalAssumptions) where
  open Eval Ax

  →det⊆→rnd : t →det t' → (t , w , s) →rnd (t' , w , s)

  →det⊆→rnd (estep Hstep)     = estep (edet Hstep)
  →det⊆→rnd (econg ctx Hstep) = econg (_ , ctx , refl) (→det⊆→rnd Hstep)

  private
    module C1 = CongStep _→ᵈ_ DetCtx id refl id
    module C2 = CongStep _→ʳ_ RndCtx ×-map₁ refl (λ ctx → _ , ctx , refl)

  cong-stepᵈ = C1.cong-step {unit} {unit}

  cong-stepʳ = λ {ws ws' o ts t' n} →
    C2.cong-step {unit , ws} {unit , ws'} {o} {ts} {t'} {n}

  ctx-value-inv :
    {E : Tm → Tm}
    (_ : DetCtx E)
    → -----------------------
    IsValue (E t) → IsValue t

  ctx-value-inv (ectx _) Hv = go Hv where
    go
      : {o : TmOp} {ts : Tm ^ length (ar TmSig o)}
      → {j : Fin (len ⦃ eval-order {o} ⦄)}
      → IsValue (o ▸ updateAt ts (ord ⦃ eval-order {o} ⦄ j) t)
      → ------------------------------------------------------
        IsValue t
    go {ts = ts} {j = j} (vtup Hvs) = subst IsValue (updateAt-updates ts j _) (Hvs j)
    go {j = j} (vinfer Hv) with zero ← fin-view j = Hv

  value-cannot-step-det : IsValue t → ¬ t →det t'
  value-cannot-step-det Hv (estep Hstep) with vabs ← Hv | () ← Hstep
  value-cannot-step-det Hv (econg Hctx Hstep) =
    value-cannot-step-det (ctx-value-inv Hctx Hv) Hstep

  value-cannot-step-rnd :
    {t t' : Tm × ℝ × List 𝕀}
    (_ : IsValue (t .fst))
    → ------------------------
    ¬ t →rnd t'

  value-cannot-step-rnd Hv (estep Hstep) with vabs ← Hv | edet () ← Hstep
  value-cannot-step-rnd Hv (econg (_ , Hctx , HE) Hstep) = value-cannot-step-rnd
    (ctx-value-inv Hctx (subst IsValue (ap fst (HE $ₚ _)) Hv)) Hstep
