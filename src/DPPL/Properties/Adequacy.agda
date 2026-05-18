open import 1Lab.Prelude

open import Cat.Displayed.Total

-- open import Data.Finset.Base hiding (_∷_)
-- open import Data.Fin.Base hiding (_≤_)
open import Data.Nat.Base using (Nat-is-set)
-- open import Data.Power using (singleton)

open import DPPL.Denotations.Regularity
-- open import DPPL.Regularity

-- open import Lib.LocallyNameless.BindingSignature
-- open import Lib.LocallyNameless.Unfinite
open import Lib.Syntax.Substitution
-- open import Lib.Syntax.EvalCtx
open import Lib.Algebra.Reals
-- open import Lib.Data.Finset
open import Lib.Data.Vector
open import Lib.Syntax.Env

module DPPL.Properties.Adequacy (R : Reals₀) (RAx : RegAssumptions R) where

open import DPPL.Denotations.Denotations R RAx
open import DPPL.Properties.SmallStep R
open import DPPL.Properties.Syntax R
open import DPPL.Properties.Typing R
open import DPPL.SmallStep R
open import DPPL.Syntax R
open import DPPL.Typing R

-- open FinsetSyntax
-- open VectorSyntax
open SyntaxVars
-- open TypingVars
open Reals R using (ℝ)

module _ (EAx : EvalAssumptions) (DAx : DenotAssumptions) where
  open Eval EAx
  open Denotations DAx

  _⊢_◃_ : (T : Ty) → ⌞ ⟦ T ⟧ ⌟ → Value → Type
  treal c ⊢ r ◃ v = v ≡ (real r , vreal)
  (T ⇒[ X ] T₁) ⊢ f ◃ v =
    Σ[ T' ∈ Ty ] Σ[ ts ∈ Tm ^ 1 ] v ≡ (_ , vlam {T'} {ts})
    × ∀ {x v' v''} → T ⊢ x ◃ v' → (0 ≈> v' .fst) (ts ₀) ⇓ v'' → T₁ ⊢ f · x ◃ v''
  ttup n Ts ⊢ x ◃ v =
    Σ[ vs ∈ Value ^ n ] v ≡ (_ , vtup (snd ∘ vs)) × ∀ i → Ts i ⊢ x i ◃ vs i

  adequacy :
    {v : Value}
    (Hty : ε ⊢ t ∶ T)
    (He : t ⇓ v)
    → -----------------
    T ⊢ ⟦ Hty ⟧ · _ ◃ v
  adequacy (tsub Hty H<:) He = {!!}
  adequacy (tpromote Hty H≤ H~ H⊆) He = {!!}
  adequacy (tlam Hlam) He = {!!}
  adequacy (tapp Hty Hty₁) He = {!!}
  adequacy (tprim Hϕ Hty) He = {!!}
  adequacy treal ereal = refl
  adequacy (ttup Htys) (etup He) = {!!}
  adequacy (tproj i Hty) (eproj _ He) =
    let vs , p , Hrel = adequacy Hty He in
    subst (_ ⊢ _ ◃_)
      ( sym (is-set→cast-pathp (Tm ^_) Nat-is-set (ap snd $ tup-inj (ap fst p)) $ₚ i)
      ,ₚ prop!
      )
      (Hrel i)
  adequacy (tif Hty Hty₁ Hty₂ H≤) He = {!!}
  adequacy (tdiff Hty Hty₁ Hty₂ Hc) He = {!!}
  adequacy (tsolve Hty Hty₁ Hty₂ Hc) He = {!!}

  -- adequacy :
  --   {v : Value}
  --   (Hty : ε ⊢ t ∶ T)
  --   (He : t ⇓ v)
  --   → -----------------
  --   T ⊢ ⟦ Hty ⟧ · _ ◃ v
  -- adequacy (tsub Hty H<:) He = let foo = adequacy Hty He in {!!}
  -- adequacy (tpromote Hty H≤ H~ H⊆) He = {!!}
  -- adequacy (tlam Hlam) = {!!}
  -- adequacy (tapp Hty Hty₁) = {!!}
  -- adequacy (tprim Hϕ Hty) (eprim He) p =
  --   let q = real-inj (ap fst p) in {!!}
  -- adequacy treal ereal p = real-inj (ap fst p)
  -- adequacy (ttup Htys) (etup He) p i =
  --   subst (_ ⊢ _ ◃_)
  --     (  is-set→cast-pathp (Tm ^_) Nat-is-set (ap snd $ tup-inj (ap fst p)) $ₚ i
  --     ,ₚ prop!
  --     )
  --     (adequacy (Htys i) (He i))
  -- adequacy (tproj i Hty) (eproj i He) = adequacy Hty He refl i
  -- adequacy (tif Hty Hty₁ Hty₂ H≤) (eif1 p He He₁) q i q' =
  --   let
  --     foo = adequacy Hty He refl
  --     bar = adequacy Hty₁ He₁ q i q'
  --   in
  --   {!!}
  -- adequacy (tif Hty Hty₁ Hty₂ H≤) (eif2 p He He₁) q i q' =
  --   let
  --     foo = adequacy Hty He refl
  --     bar = adequacy Hty₂ He₁ q i q'
  --   in
  --   {!!}
  -- adequacy (tdiff Hty Hty₁ Hty₂ Hc) = {!!}
  -- adequacy (tsolve Hty Hty₁ Hty₂ Hc) = {!!}
