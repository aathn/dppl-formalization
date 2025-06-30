module Lib.Env where

open import Lib.Prelude
open import Lib.LocallyNameless.Unfinite
open import Data.List using (_++_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_ ; [] ; _∷_ ; _∷ʳ_; lookup)

Env : Set → Set
Env X = List (𝔸 × X)

private
  variable
    X : Set
    Γ Γ′ : Env X
    T : X

infixl 5 _,_∶_
pattern ε           = []
pattern [_∶_]   x T = (x , T) ∷ []
pattern _,_∶_ Γ x T = (x , T) ∷ Γ

infixl 5 _&_
_&_ : Env X → Env X → Env X
Γ & Γ′ = Γ′ ++ Γ

dom : {X : Set} → Env X → Fset 𝔸
dom [] = Ø
dom (Γ , x ∶ _) = [ x ] ∪ dom Γ

data Distinct {X : Set} : Env X → Set where
  []  : Distinct []
  _∷_ : {x : 𝔸} → x ∉ dom Γ → Distinct Γ → Distinct (Γ , x ∶ T)


dom-distinct :
  {Γ₁ Γ₂ : Env X}
  (_ : dom Γ₁ ≡ dom Γ₂)
  → -----------------------
  Distinct Γ₁ → Distinct Γ₂
dom-distinct {Γ₂ = []} Hdom [] = []
dom-distinct {Γ₂ = (y , T) ∷ Γ₂} Hdom (H∉ ∷ Hd) with refl ← ∪inj₁ Hdom =
  subst (y ∉_) (∪inj₂ Hdom) H∉ ∷ dom-distinct (∪inj₂ Hdom) Hd


dom-∈ : {x : 𝔸} → x ∈ dom Γ → ∃ λ T → (x , T) ∈ˡ Γ
dom-∈ {Γ = x ∷ Γ} (∈∪₁ ∈[]) = _ , here refl
dom-∈ {Γ = x ∷ Γ} (∈∪₂ x∈Γ) with T , H∈ ← dom-∈ x∈Γ = T , there H∈

∈-dom : {x : 𝔸} → (x , T) ∈ˡ Γ → x ∈ dom Γ
∈-dom {Γ = x ∷ Γ} (here refl) = ∈∪₁ ∈[]
∈-dom {Γ = x ∷ Γ} (there H∈)  = ∈∪₂ (∈-dom H∈)

∉-dom-⊆ :
  {Δ Γ : Env X}
  {x : 𝔸}
  (_ : Δ ⊆ Γ)
  → -------------------
  x ∉ dom Γ → x ∉ dom Δ
∉-dom-⊆ {Δ = []} H⊆ H∉ = ∉Ø
∉-dom-⊆ {Δ = _ ∷ Δ} (_ ∷ʳ H⊆) ∉∪ = ∉-dom-⊆ H⊆ it
∉-dom-⊆ {Δ = y ∷ Δ} (refl ∷ H⊆) (∉∪ {{p}}) = ∉∪ {{p = p}} {{∉-dom-⊆ H⊆ it}}

++-dom : {x : 𝔸}(Γ′ : Env X) → x ∉ dom (Γ′ ++ Γ) → x ∉ dom Γ′ ∪ dom Γ
++-dom [] H∉ = ∉∪ {{q = H∉}}
++-dom ((y , T) ∷ Γ′) (∉∪ {{p = H∉₁}} {{H∉₂}}) with ∉∪ ← ++-dom Γ′ H∉₂ =
  ∉∪ {{p = ∉∪ {{p = H∉₁}}}}

dom-++ : {x : 𝔸} → x ∉ dom Γ′ ∪ dom Γ → x ∉ dom (Γ′ ++ Γ)
dom-++ {Γ′ = []} ∉∪ = it
dom-++ {Γ′ = _ ∷ Γ′} (∉∪ {{∉∪ {{p = H∉}}}}) = ∉∪ {{p = H∉}} {{dom-++ it}}

distinct-weaken : {x : 𝔸} → Distinct (Γ , x ∶ T & Γ′) → Distinct (Γ & Γ′)
distinct-weaken {Γ′ = []} (x ∷ Hd) = Hd
distinct-weaken {Γ′ = Γ′ , x′ ∶ T′} (H∉ ∷ Hd)
  with ∉∪ {{q = ∉∪}} ← ++-dom Γ′ H∉ =
  dom-++ it ∷ distinct-weaken Hd

distinct-∉ :
  {Γ₂ Γ₁ : Env X}
  {x : 𝔸}
  (_ : Distinct (Γ₁ , x ∶ T & Γ₂))
  → ------------------------------
  x ∉ dom Γ₁ ∪ dom Γ₂
distinct-∉ {Γ₂ = []} {Γ₁} {x} (H∉ ∷ _) = ∉∪ {{p = H∉}}
distinct-∉ {Γ₂ = (y , _) ∷ Γ₂} {x = x} (H∉ ∷ Hd)
  with ∉∪ {{q = ∉∪ {{∉[]}}}} ← ++-dom Γ₂ H∉ | ∉∪ ← distinct-∉ Hd = it
  where instance
  _ : x ≠ y
  _ = symm≠ y x it

⊆-strengthen :
  {Γ₂ Γ₁ Γ : Env X}
  {x : 𝔸}
  (_ : x ∉ dom Γ)
  (_ : Γ ⊆ Γ₁ , x ∶ T & Γ₂)
  → -----------------------
  Γ ⊆ Γ₁ & Γ₂
⊆-strengthen {Γ₂ = []} H∉ (.(_ , _) ∷ʳ H⊆) = H⊆
⊆-strengthen {Γ₂ = []} {x = x} (∉∪ {{∉[]}}) (refl ∷ H⊆) with () ← ¬≠ x it
⊆-strengthen {Γ₂ = x ∷ Γ₂} H∉ (.x ∷ʳ H⊆) = x ∷ʳ (⊆-strengthen H∉ H⊆)
⊆-strengthen {Γ₂ = x ∷ Γ₂} ∉∪ (x₁ ∷ H⊆) = x₁ ∷ (⊆-strengthen it H⊆)

⊆-split :
  {Γ₂ Γ₁ Δ : Env X}
  {x : 𝔸}
  (_ : x ∉ dom Γ₁ ∪ dom Γ₂)
  (_ : x ∈ dom Δ)
  (_ : Δ ⊆ Γ₁ , x ∶ T & Γ₂)
  → -------------------------------------------------------
  ∃ λ Δ₁ → ∃ λ Δ₂ → Δ₁ ⊆ Γ₁ × Δ₂ ⊆ Γ₂ × Δ ≡ Δ₁ , x ∶ T & Δ₂

⊆-split {Γ₂ = []} ∉∪ H∈ (.(_ , _) ∷ʳ Hsub) with _ , H∈′ ← dom-∈ H∈
  with () ← ∉→¬∈ (∈-dom $ lookup Hsub H∈′)
⊆-split {Γ₂ = []} ∉∪ H∈ (refl ∷ Hsub) = _ , _ , Hsub , [] , refl
⊆-split {Γ₂ = x ∷ Γ₂} (∉∪ {{q = ∉∪}}) H∈ (.x ∷ʳ Hsub)
  with  Δ₁ , Δ₂ , Hsub1 , Hsub2 , Heq ← ⊆-split ∉∪ H∈ Hsub =
  Δ₁ , Δ₂ , Hsub1 , x ∷ʳ Hsub2 , Heq
⊆-split {Γ₂ = x ∷ Γ₂} (∉∪ {{ q = ∉∪ }}) (∈∪₂ H∈) (refl ∷ Hsub)
  with Δ₁ , Δ₂ , Hsub1 , Hsub2 , refl ← ⊆-split ∉∪ H∈ Hsub =
  Δ₁ , x ∷ Δ₂ , Hsub1 , refl ∷ Hsub2 , refl
⊆-split {Γ₂ = Γ₂ , x ∶ _} (∉∪ {{ q = ∉∪ {{ p = ∉[] }} }}) (∈∪₁ ∈[]) (refl ∷ Hsub)
  with () ← ¬≠ x it
