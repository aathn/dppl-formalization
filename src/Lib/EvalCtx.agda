module Lib.EvalCtx where

open import Lib.Prelude
open import Lib.FunExt
open import Lib.BindingSignature

open import Data.Vec.Functional using (updateAt)
open import Data.Vec.Functional.Properties using (updateAt-id-local)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (subst₂)
open import Relation.Binary.Rewriting using (Deterministic)

-- Evaluation orders, evaluation contexts and congruence closure

record OpEvalOrder (Σ : Sig) (o : Op Σ) : Set where
  field
    len : ℕ
    ord : Vector (Fin $ length (ar Σ o)) len
    inj : injection _≡_ _≡_ ord

open OpEvalOrder {{...}} public

EvalOrder : Sig → Set
EvalOrder Σ = {o : Op Σ} → OpEvalOrder Σ o

data EvalCtx
  {Σ : Sig} {{_ : EvalOrder Σ}} (Val : Pred (Trm Σ) _)
  : Pred (Trm Σ → Trm Σ) ℓ₀
  where

  ectx :
    {o : Op Σ}
    {j : Fin len}
    {ts : Vector (Trm Σ) (length (ar Σ o))}
    (_ : ∀ i → i <′ j → Val (ts (ord i)))
    → ------------------------------------------------------
    EvalCtx Val λ t → op (o , updateAt ts (ord j) (const t))


data CongCls {A : Set} (_↝_ : Rel A _) (Ctx : Pred (A → A) _) : Rel A ℓ₀ where

  estep :
    {a b : A}
    (_ : a ↝ b)
    → -----------------
    CongCls _↝_ Ctx a b

  econg :
    {E : A → A}
    {a b : A}
    (_ : Ctx E)
    (_ : CongCls _↝_ Ctx a b)
    → -------------------------
    CongCls _↝_ Ctx (E a) (E b)


-- Congruence with respect to evaluation contexts

module CongStep
  {Σ : Sig} {A : Set} {{_ : EvalOrder Σ}} {Val : Pred (Trm Σ) _}
  (_↝_ : Rel A _) (Ctx : Pred (A → A) _) (Lift : (Trm Σ → Trm Σ) → (A → A))
  (HLift : ∀ {E E′} → Lift E ∘ Lift E′ ≡ Lift (E ∘ E′))
  (HCtx : ∀ {E} → EvalCtx Val E → Ctx (Lift E))
  where

  private
    put = Lift ∘ const
    _↝ᶜ_ = CongCls _↝_ Ctx

  cong-step :
    {a b : A}
    {o : Op Σ}
    {ts : Vector (Trm Σ) (length (ar Σ o))}
    {t′ : Trm Σ}
    {n : Fin len}
    (_ : ∀ i → i <′ n → Val (ts (ord i)))
    (_ : put (ts (ord n)) a ↝ᶜ put t′ b)
    → -------------------------------------
    put (op (o , ts)) a ↝ᶜ
      put (op (o , updateAt ts (ord n) (const t′))) b

  cong-step {a} {b} {o} {ts} {t′} {n} Hvs Hstep = subst₂ _↝ᶜ_ it it it
    where instance
    _ : Lift _ (put (ts (ord n)) a) ↝ᶜ Lift _ (put t′ b)
    _ = econg (HCtx (ectx Hvs)) Hstep
  
    _ : Lift _ (put (ts (ord n)) a) ≡ put (op (o , ts)) a
    _ =
      ap (_$ _) HLift ；
        ap (λ ts → put (op (o , ts)) a)
           (funext $ updateAt-id-local (ord n) ts refl)
  
    _ : Lift _ (put t′ b) ≡ put (op (o , updateAt ts (ord n) (const t′))) b
    _ = ap (_$ _) HLift
    
CongCls-deterministic :
  {A : Set}
  {_↝_ : Rel A _}
  {Ctx : Pred (A → A) _}
  → let _↝ᶜ_ = CongCls _↝_ Ctx in
    Deterministic _≡_ _↝_
  → (∀ {E E′ a a′ b b′} → Ctx E → Ctx E′ → a ↝ᶜ a′ → b ↝ᶜ b′ → E a ≡ E′ b → E ≡ E′ × a ≡ b)
  → (∀ {E a a′ b} → Ctx E → a ↝ᶜ a′ → ¬ E a ↝ b)
  → --------------------------------------------
  Deterministic _≡_ _↝ᶜ_

CongCls-deterministic Hdet Huniq Hnstep (estep Hstep₁) (estep Hstep₂) =
  Hdet Hstep₁ Hstep₂
CongCls-deterministic Hdet Huniq Hnstep (estep Hstep₁) (econg Hctx Hstep₂)
  with () ← Hnstep Hctx Hstep₂ Hstep₁
CongCls-deterministic Hdet Huniq Hnstep (econg {E} {a} {b} Hctx Hstep₁) Hstep₂
  with Ea ← E a in HEa | Hstep₂
... | estep Hstep₂′ with refl ← HEa with () ← Hnstep Hctx Hstep₁ Hstep₂′
... | econg {E′} Hctx′ Hstep₂′ with refl , refl ← Huniq Hctx Hctx′ Hstep₁ Hstep₂′ HEa =
  ap E $ CongCls-deterministic Hdet Huniq Hnstep Hstep₁ Hstep₂′
