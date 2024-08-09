module Properties.SmallStep (ℝ 𝕀 : Set) where

-- Minor lemmas about the step relations (and typing)

open import Lib.Prelude
open import Lib.FunExt
open import Lib.BindingSignature
open import Lib.EvalCtx

open import Data.Product using (∃-syntax ; map₁)
open import Data.Vec.Functional using (map ; updateAt)
open import Data.Vec.Functional.Properties using (updateAt-updates)
open import Relation.Nullary using (Irrelevant)

open import Syntax ℝ
open import Typing ℝ
open import SmallStep ℝ 𝕀

-- Value t is irrelevant

value-irrelevant
  : ∀ {t}
  → --------------------
    Irrelevant (Value t)

value-irrelevant vabs vabs = refl
value-irrelevant vreal vreal = refl
value-irrelevant (vtup vs) (vtup vs′) =
  ap vtup (funext λ i → value-irrelevant (vs i) (vs′ i))
value-irrelevant (vdist vs) (vdist vs′) =
  ap vdist (funext λ i → value-irrelevant (vs i) (vs′ i))
value-irrelevant (vinfer v) (vinfer v′) =
  ap vinfer (value-irrelevant v v′)

-- Canonical forms

canonical-⇒
  : ∀ {Γ t e e′ T T₁ T₂}
  → Γ ⊢ t :[ e ] T
  → Value t
  → T ≡ T₁ ⇒[ e′ ] T₂
  → -----------------------------
    ∃[ T′ ] ∃[ t′ ] t ≡ abs T′ t′

canonical-⇒ (tabs _) _ refl = _ , _ , refl
canonical-⇒ (tweaken Htype _ _) Hval Heq =
  canonical-⇒ Htype Hval Heq
canonical-⇒ (tsub Htype _ (sarr _ _ _)) Hval refl =
  canonical-⇒ Htype Hval refl
canonical-⇒ (tpromote {T = _ ⇒[ _ ] _} Htype H≤) Hval Heq =
  canonical-⇒ Htype Hval Heq

canonical-real
  : ∀ {Γ t e T c}
  → Γ ⊢ t :[ e ] T
  → Value t
  → T ≡ treal c
  → -----------------
    ∃[ r ] t ≡ real r

canonical-real treal _ _ = _ , refl
canonical-real (tweaken Htype _ _) Hval Heq =
  canonical-real Htype Hval Heq
canonical-real (tsub Htype _ (sreal _)) Hval refl =
  canonical-real Htype Hval refl
canonical-real (tpromote {T = treal _} Htype H≤) Hval refl =
  canonical-real Htype Hval refl

canonical-tup
  : ∀ {Γ t e T n Ts}
  → Γ ⊢ t :[ e ] T
  → Value t
  → T ≡ ttup {n} Ts
  → -------------------------------------------
    ∃[ ts ] t ≡ tup {n} ts × ∀ i → Value (ts i)

canonical-tup (ttup _ _) (vtup Hvs) refl = _ , refl , Hvs
canonical-tup (tweaken Htype _ _) Hval Heq =
  canonical-tup Htype Hval Heq
canonical-tup (tsub Htype _ (stup _)) Hval refl =
  canonical-tup Htype Hval refl
canonical-tup (tpromote {T = ttup _} Htype H≤) Hval refl =
  canonical-tup Htype Hval refl

canonical-dist
  : ∀ {Γ t e T T′}
  → Γ ⊢ t :[ e ] T
  → Value t
  → T ≡ tdist T′
  → -----------------------------------------
    (∃[ D ] ∃[ rs ] t ≡ dist D (map real rs))
  ⊎ (∃[ v ] t ≡ infer v × Value (v ₀))

canonical-dist (tdist {ts = ts} _ Htypes _) (vdist Hvs) _ =
  let Hreals : ∃[ rs ] ts ≡ map real rs
      Hreals = _ , funext λ i → π₂ $ canonical-real (Htypes i) (Hvs i) refl
  in
  case Hreals λ { (_ , refl) → ι₁ $ _ , _ , refl }
canonical-dist (tinfer _) (vinfer Hv) refl = ι₂ $ _ , refl , Hv
canonical-dist (tweaken Htype _ _) Hval Heq =
  canonical-dist Htype Hval Heq
canonical-dist (tsub Htype _ (sdist _)) Hval refl =
  canonical-dist Htype Hval refl
canonical-dist (tpromote {T = tdist _} Htype H≤) Hval Heq =
  canonical-dist Htype Hval Heq

val-type-det
  : ∀ {Γ t e T}
  → Γ ⊢ t :[ e ] T
  → Value t
  → ----------------
    Γ ⊢ t :[ det ] T
val-type-det (tabs Htype) _ = tabs Htype
val-type-det treal _ = treal
val-type-det (ttup Htypes Hd) (vtup Hvs) =
  ttup (λ i → val-type-det (Htypes i) (Hvs i)) Hd
val-type-det (tdist HD Htypes Hd) (vdist Hvs) =
  tdist HD (λ i → val-type-det (Htypes i) (Hvs i)) Hd
val-type-det (tinfer Htype) (vinfer Hval) = tinfer (val-type-det Htype Hval)
val-type-det (tweaken Htype H⊆ Hd) Hval = tweaken (val-type-det Htype Hval) H⊆ Hd
val-type-det (tsub Htype He Hsub) Hval = tsub (val-type-det Htype Hval) 0≤ Hsub
val-type-det (tpromote Htype H≤) Hval = tpromote (val-type-det Htype Hval) H≤


module Step (Ass : EvalAssumptions) where
  open Eval Ass

  →det⊆→rnd
    : ∀ {t t′ w s}
    → t →det t′
    → -----------------------------
      (t , w , s) →rnd (t′ , w , s)

  →det⊆→rnd (estep Hstep) = estep (edet Hstep)
  →det⊆→rnd (econg ctx Hstep) = econg (_ , ctx , refl) (→det⊆→rnd Hstep)

  private
    module C1 = CongStep _→ᵈ_ DetCtx id refl id
    module C2 = CongStep _→ʳ_ RndCtx map₁ refl (λ ctx → _ , ctx , refl)

  cong-stepᵈ = C1.cong-step {unit} {unit}

  cong-stepʳ = λ {ws ws′ o ts t′ n} →
    C2.cong-step {unit , ws} {unit , ws′} {o} {ts} {t′} {n}

  ctx-value-inv
    : ∀ {E t}
    → DetCtx E
    → Value (E t)
    → -----------
      Value t

  ctx-value-inv {E} {t} (ectx {o} {j} {ts} _) Hv
    with ts' ← updateAt ts (ord {{eval-order {o}}} j) (const t) in HEt | Hv | HEt
  ... | vtup  Hvs | refl = subst Value (updateAt-updates j ts) (Hvs j)
  ... | vdist Hvs | refl = subst Value (updateAt-updates j ts) (Hvs j)
  ... | vinfer Hv₀ | refl with ₀ ← j = Hv₀

  value-cannot-step-det
    : ∀ {t t′}
    → Value t
    → ------------
      ¬ t →det t′

  value-cannot-step-det Hv (estep Hstep) with vabs ← Hv | () ← Hstep
  value-cannot-step-det Hv (econg Hctx Hstep) =
    value-cannot-step-det (ctx-value-inv Hctx Hv) Hstep
