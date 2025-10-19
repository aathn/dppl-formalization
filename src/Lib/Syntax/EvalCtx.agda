module Lib.Syntax.EvalCtx where

open import Lib.Prelude
open import Lib.Data.Vector
open import Lib.LocallyNameless.BindingSignature

open import Data.Fin.Base
open import Data.Nat.Order

-- Evaluation orders, evaluation contexts and congruence closure

record OpEvalOrder (Σ : Sig) (o : Op Σ) : Type where
  field
    len : Nat
    ord : Fin (length (ar Σ o)) ^ len
    inj : injective ord

open OpEvalOrder ⦃...⦄ public

EvalOrder : Sig → Type
EvalOrder Σ = {o : Op Σ} → OpEvalOrder Σ o

data EvalCtx {Σ : Sig} ⦃ _ : EvalOrder Σ ⦄ (Val : (Trm Σ) → Type _)
  : (Trm Σ → Trm Σ) → Type
  where

  ectx :
    {o : Op Σ}
    {j : Fin len}
    {ts : Vector (Trm Σ) (length (ar Σ o))}
    (_ : ∀ i → i < j → Val (ts (ord i)))
    → ------------------------------------------------------
    EvalCtx Val λ t → op (o , updateAt ts (ord j) t)

EvalCtx-unique :
  {Σ : Sig} ⦃ _ : EvalOrder Σ ⦄ (Val : (Trm Σ) → Type _)
  {E E' : Trm Σ → Trm Σ}
  {t u : Trm Σ}
  (_ : EvalCtx Val E)
  (_ : EvalCtx Val E')
  (_ : ¬ Val t)
  (_ : ¬ Val u)
  → -------------------------
  E t ≡ E' u → E ≡ E' × t ≡ u

EvalCtx-unique Val {t = t} {u = u}
  (ectx {o} {i} {ts} Hvs) (ectx {j = j} {ts'} Hvs') Ht Hu Heq
  with reflᵢ ← Id≃path.from (ap fst (op-inj Heq)) | ≤-split (i .lower) (j .lower)
... | inl H< = absurd (Ht (subst Val Heqt (Hvs' i H<))) where
  Heqt =
    ts' (ord i)        ≡˘⟨ updateAt-minimal ts' _ _ _ (<-not-equal H< ∘ sym ∘ ap lower ∘ inj) ⟩
    updateAt ts' _ u _ ≡˘⟨ op-inj' Heq $ₚ _ ⟩
    updateAt ts  _ t _ ≡⟨ updateAt-updates ts _ _ ⟩
    t                  ∎
... | inr (inl H>) = absurd (Hu (subst Val Hequ (Hvs j H>))) where
  Hequ =
    ts (ord j)         ≡˘⟨ updateAt-minimal ts _ _ _ (<-not-equal H> ∘ sym ∘ ap lower ∘ inj) ⟩
    updateAt ts  _ t _ ≡⟨ op-inj' Heq $ₚ _ ⟩
    updateAt ts' _ u _ ≡⟨ updateAt-updates ts' _ _ ⟩
    u                  ∎
... | inr (inr H≡) with reflᵢ ← Id≃path.from H≡ = Heq₁ , Heq₂ where
  Heq₁ = funext λ s → ap (op ∘ (o ,_)) $
    updateAt ts (ord i) s           ≡˘⟨ funext $ updateAt-updateAt ts _ _ _ ⟩
    updateAt (updateAt ts  _ t) _ s ≡⟨ ap (λ xs → updateAt xs _ _ ) (op-inj' Heq) ⟩
    updateAt (updateAt ts' _ u) _ s ≡⟨ funext $ updateAt-updateAt ts' _ _ _ ⟩
    updateAt ts' _ s                ∎
  Heq₂ =
    t                  ≡˘⟨ updateAt-updates ts _ _ ⟩
    updateAt ts  _ t _ ≡⟨ op-inj' Heq $ₚ _ ⟩
    updateAt ts' _ u _ ≡⟨ updateAt-updates ts' _ _ ⟩
    u                  ∎


data CongCls
  {A : Type} (_↝_ : A → A → Type _) (Ctx : (A → A) → Type _)
  : A → A → Type where

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
  {Σ : Sig} {A : Type} ⦃ _ : EvalOrder Σ ⦄ {Val : (Trm Σ) → Type _}
  (_↝_ : A → A → Type _) (Ctx : (A → A) → Type _) (Lift : (Trm Σ → Trm Σ) → (A → A))
  (HLift : ∀ {E E'} → Lift E ∘ Lift E' ≡ Lift (E ∘ E'))
  (HCtx : ∀ {E} → EvalCtx Val E → Ctx (Lift E))
  where

  private
    put = Lift ∘ (λ x _ → x)
    _↝ᶜ_ = CongCls _↝_ Ctx

  cong-step :
    {a b : A}
    {o : Op Σ}
    {ts : Vector (Trm Σ) (length (ar Σ o))}
    {t' : Trm Σ}
    {n : Fin len}
    (_ : ∀ i → i < n → Val (ts (ord i)))
    (_ : put (ts (ord n)) a ↝ᶜ put t' b)
    → -------------------------------------
    put (op (o , ts)) a ↝ᶜ
      put (op (o , updateAt ts (ord n) t')) b
  cong-step {a} {b} {o} {ts} {t'} {n} Hvs Hstep = subst₂ _↝ᶜ_ auto auto auto
    where instance
    _ : Lift _ (put (ts (ord n)) a) ↝ᶜ Lift _ (put t' b)
    _ = econg (HCtx (ectx {j = n} {ts} Hvs)) Hstep

    _ : Lift _ (put (ts (ord n)) a) ≡ put (op (o , ts)) a
    _ = ap (_$ _) HLift ∙
        ap (λ ts → put (op (o , ts)) a)
           (ext λ j → updateAt-id-local ts (ord n) _ refl j)

    _ : Lift _ (put t' b) ≡ put (op (o , updateAt ts (ord n) t')) b
    _ = ap (_$ _) HLift

Deterministic : {A : Type} (_↝_ : A → A → Type) → Type
Deterministic _↝_ = ∀ {x y z} → x ↝ y → x ↝ z → y ≡ z

CongCls-deterministic :
  {A : Type}
  {_↝_ : A → A → Type _}
  {Ctx : (A → A) → Type _}
  → let _↝ᶜ_ = CongCls _↝_ Ctx in
    Deterministic _↝_
  → (∀ {E E' a a' b b'} → Ctx E → Ctx E' → a ↝ᶜ a' → b ↝ᶜ b' → E a ≡ E' b → E ≡ E' × a ≡ b)
  → (∀ {E a a' b} → Ctx E → a ↝ᶜ a' → ¬ E a ↝ b)
  → --------------------------------------------
  Deterministic _↝ᶜ_

CongCls-deterministic Hdet Huniq Hnstep (estep Hstep₁) (estep Hstep₂) =
  Hdet Hstep₁ Hstep₂
CongCls-deterministic Hdet Huniq Hnstep (estep Hstep₁) (econg Hctx Hstep₂)
  with () ← Hnstep Hctx Hstep₂ Hstep₁
CongCls-deterministic {_↝_ = _↝_} {Ctx} Hdet Huniq Hnstep (econg {E} {a} {b} Hctx Hstep₁) Hstep₂
  with Ea ← E a in HEa | Hstep₂
... | estep Hstep₂' with reflᵢ ← HEa with () ← Hnstep Hctx Hstep₁ Hstep₂'
... | econg {E'} {a'} {b'} Hctx' Hstep₂' =
  let H≡₁ , H≡₂ = Huniq Hctx Hctx' Hstep₁ Hstep₂' (Id≃path.to HEa)
      Hstep₂ = subst (λ a → CongCls _↝_ Ctx a _) (sym $ H≡₂) Hstep₂'
  in
  E b   ≡⟨ ap E (CongCls-deterministic Hdet Huniq Hnstep Hstep₁ Hstep₂) ⟩
  E b'  ≡⟨ H≡₁ $ₚ b' ⟩
  E' b' ∎
