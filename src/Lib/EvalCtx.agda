module Lib.EvalCtx where

open import Lib.Prelude
open import Lib.FunExt
open import Lib.BindingSignature

open import Function using (_$_ ; const)
open import Data.Fin using () renaming (_<_ to _<ꟳ_)
open import Data.Product using (∃ ; ∃-syntax)
open import Data.Vec.Functional using (updateAt)
open import Data.Vec.Functional.Properties using (updateAt-id-local)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (subst₂)

-- Evaluation orders, evaluation contexts and congruence closure

EvalOrder : Sig → Set
EvalOrder Σ = (o : Op Σ) → ∃ (Vector $ Fin $ length (ar Σ o))

data EvalCtx
  {Σ : Sig} (ord : EvalOrder Σ) (Val : Pred (Trm Σ) _)
  : Pred (Trm Σ → Trm Σ) ℓ₀
  where

  ectx
    : ∀ {o f j ts}
    → ord o .π₂ ≡ f
    → (∀ i → i <ꟳ j → Val (ts (f i)))
    → ----------------------------------------------------------
      EvalCtx ord Val λ t → op (o , updateAt ts (f j) (const t))


data CongCls {A : Set} (_↝_ : Rel A _) (Ctx : Pred (A → A) _) : Rel A ℓ₀ where

  estep
    : ∀ {a b}
    → a ↝ b
    → -------------------
      CongCls _↝_ Ctx a b

  econg
    : ∀ {E t t′}
    → Ctx E
    → CongCls _↝_ Ctx t t′
    → ----------------------------
      CongCls _↝_ Ctx (E t) (E t′)


-- Congruence with respect to evaluation contexts

module CongStep
  {Σ : Sig} {A : Set} {ord : EvalOrder Σ} {Val : Pred (Trm Σ) _}
  (_↝_ : Rel A _) (Ctx : Pred (A → A) _) (Lift : (Trm Σ → Trm Σ) → (A → A))
  (HLift : ∀ {E E′} → Lift E ∘ Lift E′ ≗ Lift (E ∘ E′))
  (HCtx : ∀ {E} → EvalCtx ord Val E → Ctx (Lift E))
  where

  private
    put = Lift ∘ const
    _↝ᶜ_ = CongCls _↝_ Ctx

  cong-step
    : ∀ {a b o ts t′ f n}
    → ord o .π₂ ≡ f
    → (∀ i → i <ꟳ n → Val (ts (f i)))
    → put (ts (f n)) a ↝ᶜ put t′ b
    → ----------------------------
      put (op (o , ts)) a ↝ᶜ
        put (op (o , updateAt ts (f n) (const t′))) b

  cong-step {a} {b} {o} {ts} {t′} {f} {n} Heq Hvs Hstep = subst₂ _↝ᶜ_ it it it
    where instance
    _ : Lift _ (put (ts (f n)) a) ↝ᶜ Lift _ (put t′ b)
    _ = econg (HCtx (ectx Heq Hvs)) Hstep

    _ : Lift _ (put (ts (f n)) a) ≡ put (op (o , ts)) a
    _ =
      HLift _ ；
        ap (λ ts → put (op (o , ts)) a)
           (funext $ updateAt-id-local (f n) ts refl)

    _ : Lift _ (put t′ b) ≡ put (op (o , updateAt ts (f n) (const t′))) b
    _ = HLift _
    
