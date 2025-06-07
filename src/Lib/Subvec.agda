module Lib.Subvec where

open import Lib.Prelude hiding ([]; _∷_)

open import Function using (Injection ; _↣_ ; mk↣)
open Injection using (to ; injective)
import Function.Properties.Injection as Inj
import Function.Properties.Inverse as Inv
open import Data.Fin using (splitAt)
open import Data.Fin.Properties
  using (suc-injective ; +↔⊎ ; ↑ʳ-injective ; ↑ˡ-injective
        ; splitAt-↑ˡ ; splitAt-↑ʳ
        )
open import Data.Sum using () renaming (map to ⊎-map)
open import Data.Sum.Properties using (inj₁-injective ; inj₂-injective)
open import Data.Vec.Functional
open import Relation.Binary.PropositionalEquality using (_≗_)

private
  variable
    n m k : ℕ

⊎-map-injective :
  {A B C D : Set}
  {f : A → C}
  {g : B → D}
  (_ : injection _≡_ _≡_ f)
  (_ : injection _≡_ _≡_ g)
  → ---------------------------
  injection _≡_ _≡_ (⊎-map f g)
⊎-map-injective Hf Hg {x = ι₁ x} {ι₁ y} H≡ = ap ι₁ (Hf (inj₁-injective H≡))
⊎-map-injective Hf Hg {x = ι₂ x} {ι₂ y} H≡ = ap ι₂ (Hg (inj₂-injective H≡))

infix 4 _⊆_

-- The preorder induced by the action of reindexing mappings
-- on vectors.  The restriction to injective mappings makes it a
-- partial order.
_⊆_ : {X : Set} → X ^ n → X ^ m → Set
_⊆_ {n} {m} xs ys = ∑ f ∶ Fin n ↣ Fin m , xs ≗ ys ∘ f .to

⊆-refl :
  {X : Set}
  {xs : X ^ n}
  → ----------
  xs ⊆ xs
⊆-refl = Inj.refl , λ _ → refl

⊆-trans :
  {X : Set}
  {n m k : ℕ}
  {xs : X ^ n} {ys : X ^ m} {zs : X ^ k}
  → ------------------------------------
  xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans {n = n} {k = k} (f , Hf) (g , Hg) =
  Inj.trans f g , λ i → Hf i ； Hg (f .to i)

⊆-[] :
  {X : Set}
  {xs : X ^ n}
  → ----------
  [] ⊆ xs
⊆-[] .π₁ .to ()

⊆-∷ :
  {X : Set}
  {xs : X ^ n} {ys : X ^ m}
  {a b : X}
  → ---------------------------------------
  a ≡ b → xs ⊆ ys → (a ∷ xs) ⊆ (b ∷ ys)
⊆-∷ {n = n} {m} refl (f , Hf) =
  let g = Inj.trans (Inv.Inverse⇒Injection +↔⊎) $
          Inj.trans (mk↣ (⊎-map-injective id (f .injective))) $
          Inv.Inverse⇒Injection (Inv.sym +↔⊎)
  in g , λ where
           zero     → refl
           (succ n) → Hf n

⊆-∷ʳ :
  {X : Set}
  {xs : X ^ n} {ys : X ^ m}
  → ---------------------------------
  (a : X) → xs ⊆ ys → xs ⊆ (a ∷ ys)
⊆-∷ʳ {n = n} {m} a (f , Hf) =
  Inj.trans f (mk↣ suc-injective) , Hf

proj-⊆ : {X : Set} → (Fin n ↣ Fin m) → X ^ m → X ^ n
proj-⊆ f xs = xs ∘ f .to

⊆-++⁺ˡ : {X : Set} {Θ : X ^ n} {Θ′ : X ^ m} (Θ″ : X ^ k) → Θ ⊆ Θ′ → Θ ⊆ Θ″ ++ Θ′
⊆-++⁺ˡ {n = n} {m} {k} {Θ = Θ} {Θ′} Θ″ (f , Hf) = g , Hg
  where
    g : Fin n ↣ Fin (k + m)
    g = Inj.trans f $ mk↣ λ {i} {j} → ↑ʳ-injective k i j
    Hg : (i : Fin n) → π[ i ] Θ ≡ π[ g .to i ] (Θ″ ++ Θ′)
    Hg i rewrite splitAt-↑ʳ k m (f .to i) = Hf i

⊆-++⁺ʳ : {X : Set} {Θ : X ^ n} {Θ′ : X ^ m} (Θ″ : X ^ k) → Θ ⊆ Θ′ → Θ ⊆ Θ′ ++ Θ″
⊆-++⁺ʳ {n = n} {m} {k} {Θ = Θ} {Θ′} Θ″ (f , Hf) = g , Hg
  where
    g : Fin n ↣ Fin (m + k)
    g = Inj.trans f $ mk↣ λ {i} {j} → ↑ˡ-injective k i j
    Hg : (i : Fin n) → π[ i ] Θ ≡ π[ g .to i ] (Θ′ ++ Θ″)
    Hg i rewrite splitAt-↑ˡ m (f .to i) k = Hf i

⊆-++⁺ :
  {X : Set} {n n′ m m′ : ℕ}
  {Θ : X ^ n} {Θ′ : X ^ n′} {Δ : X ^ m} {Δ′ : X ^ m′}
  → -------------------------------------------------
  Θ ⊆ Θ′ → Δ ⊆ Δ′ → Θ ++ Δ ⊆ Θ′ ++ Δ′
⊆-++⁺ {n = n} {n′} {m} {m′} {Θ} {Θ′} {Δ} {Δ′} (f , Hf) (g , Hg) = h , Hh
  where
    h : Fin (n + m) ↣ Fin (n′ + m′)
    h = Inj.trans (Inv.Inverse⇒Injection +↔⊎) $
        Inj.trans (mk↣ (⊎-map-injective (f .injective) (g .injective))) $
        Inv.Inverse⇒Injection (Inv.sym +↔⊎)
    Hh : (i : Fin (n + m)) → π[ i ] (Θ ++ Δ) ≡ π[ h .to i ] (Θ′ ++ Δ′)
    Hh i with splitAt n i
    ... | ι₁ i rewrite splitAt-↑ˡ n′ (f .to i) m′ = Hf i
    ... | ι₂ i rewrite splitAt-↑ʳ n′ m′ (g .to i) = Hg i
