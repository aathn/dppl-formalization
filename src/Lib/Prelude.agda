module Lib.Prelude where

open import 1Lab.Prelude public
  hiding (_≠_; _∉_)

open import Lib.Dec public
open import Lib.Finset public

open import Data.Dec.Base public using (Dec ; yes ; no ; ifᵈ_then_else_ ; _≡?_ ; Discrete)
open import Data.Finset.Base public
  using (Finset ; Membership-Finset ; Dec-∈ᶠˢ)
open import Data.Nat.Base public using (Discrete-Nat)
open import Data.Sum.Base public using (_⊎_ ; inl ; inr)
open import Data.Sum.Properties public using (Discrete-⊎)

module NatOrd where
  open import Data.Nat.Base public
    using (_≤_ ; s≤s ; ≤-trans ; _<_ ; max)
  open import Data.Nat.Properties public
    using (max-≤l ; max-≤r ; max-univ)
  open import Data.Nat.Order public using (≤-refl)

  _≥_ = flip _≤_

----------------------------------------------------------------------
-- Empty type
----------------------------------------------------------------------

-- open import Data.Empty public
--   renaming (⊥ to 𝟘 ; ⊥-elim to 𝟘e)

-- open import Relation.Nullary public using (¬_)

-- ----------------------------------------------------------------------
-- -- Unit type
-- ----------------------------------------------------------------------

-- open import Data.Unit public using (tt)
--   renaming (⊤ to 𝟙)

-- ----------------------------------------------------------------------
-- -- Booleans
-- ----------------------------------------------------------------------
-- open import Data.Bool public using (true ; false ; if_then_else_ ; not)
--   renaming (Bool to 𝔹 ; _∧_ to _and_)

-- ----------------------------------------------------------------------
-- -- Relations and predicates
-- ----------------------------------------------------------------------

-- open import Relation.Unary public using () renaming (Pred to ℙ)
-- open import Relation.Binary public using (Rel)

-- ----------------------------------------------------------------------
-- -- Homogeneous propositional equality
-- -- Properties of equality
-- ----------------------------------------------------------------------

-- open import Relation.Binary.PropositionalEquality public
--   using (_≡_ ; refl ; subst)
--   renaming ( cong to ap ; cong₂ to ap₂ ; trans to _；_ ; sym to symm
--            ; ≢-sym to symm¬≡)

-- infix  1 proof_
-- proof_ :
--   {l : Level}
--   {A : Set l}
--   {x y : A}
--   → -----------
--   x ≡ y → x ≡ y
-- proof p = p

-- infixr 2 _≡[_]_
-- _≡[_]_ :
--   {l : Level}
--   {A : Set l}
--   (x : A)
--   {y z : A}
--   → -------------------
--   x ≡ y → y ≡ z → x ≡ z
-- _ ≡[ refl ] q = q

-- infixr 2 _[_]≡_
-- _[_]≡_ :
--   {l : Level}
--   {A : Set l}
--   (x : A)
--   {y z : A}
--   → -------------------
--   y ≡ x → y ≡ z → x ≡ z
-- _ [ refl ]≡ q = q

-- infixr 2 _≡[]_
-- _≡[]_ :
--   {l : Level}
--   {A : Set l}
--   (x : A)
--   {y : A}
--   → -----------
--   x ≡ y → x ≡ y
-- _ ≡[] q = q

-- infix  3 _qed
-- _qed :
--   {l : Level}
--   {A : Set l}
--   (x : A)
--   → ---------
--   x ≡ x
-- _ qed = refl

-- coe : {l : Level}{P Q : Set l} → P ≡ Q → P → Q
-- coe refl x = x

-- open import Axiom.UniquenessOfIdentityProofs.WithK public using (uip)

-- ----------------------------------------------------------------------
-- -- Injective functions
-- ----------------------------------------------------------------------
-- open import Function public using ()
--   renaming (Injective to injection ; Surjective to surjection)

-- ----------------------------------------------------------------------
-- -- Disjoint union
-- ----------------------------------------------------------------------
-- open import Data.Sum public using (_⊎_)
--   renaming (inj₁ to ι₁ ; inj₂ to ι₂)

-- open import Data.Sum.Properties public using ()
--   renaming (inj₁-injective to injectionι₁ ; inj₂-injective to injectionι₂)

-- ----------------------------------------------------------------------
-- -- Recursion over well-founded relations
-- ----------------------------------------------------------------------

-- module wf {l m : Level}{A : Set l}(R : A → A → Set m) where
--   open import Induction.WellFounded public using (acc)
--   open Induction.WellFounded using (WellFounded ; wf⇒irrefl)
--   open import Relation.Binary.PropositionalEquality using (resp₂)

--   Acc : A → Set (l ⊔ m)
--   Acc = Induction.WellFounded.Acc R

--   -- Well-founded relation
--   iswf : Set (l ⊔ m)
--   iswf = WellFounded R

--   -- Well-founded recursion
--   module _
--     (w : iswf)
--     {n : Level}
--     (B : A → Set n)
--     (b : ∀ x → (∀ {y} → R y x → B y) → B x)
--     where
--     open Induction.WellFounded.All w n

--     rec : ∀ x → B x
--     rec = wfRec B b

--   -- Irreflexivity
--   irrefl :
--     (_ : iswf)
--     → ------------------
--     ∀ x → R x x → 𝟘
--   irrefl w x = wf⇒irrefl (resp₂ R) symm w refl

-- ----------------------------------------------------------------------
-- -- Decidable properties
-- ----------------------------------------------------------------------

-- open import Relation.Nullary public
--   using (Reflects ; invert ; Dec ; does ; _because_ ; yes ; no ; map′)
--   renaming (ofʸ to of-y ; ofⁿ to of-n ; proof to bcos)
-- open import Relation.Nullary.Decidable using (dec-true ; dec-false)

-- ----------------------------------------------------------------------
-- -- Decidable homogeneous equality
-- ----------------------------------------------------------------------

-- module _ {l : Level} (A : Set l) where
--   open import Relation.Binary.Structures {A = A} _≡_ using ()
--     renaming (IsDecEquivalence to hasDecEq)
--     public

-- open hasDecEq {{...}} public hiding (refl) renaming (_≟_ to _≐_)

-- pattern equ    = yes refl
-- pattern neq ¬p = no ¬p

-- dec-equ :
--   {ℓ : Level}
--   {A : Set ℓ}
--   {{_ : hasDecEq A}}
--   (x : A)
--   → ----------------
--   does (x ≐ x) ≡ true
-- dec-equ x = dec-true (x ≐ x) refl

-- dec-neq :
--   {ℓ : Level}
--   {A : Set ℓ}
--   {{_ : hasDecEq A}}
--   (x y : A)
--   (_ : ¬ x ≡ y)
--   → ------------------
--   does (x ≐ y) ≡ false
-- dec-neq x y = dec-false (x ≐ y)

-- infix 4 _≠_
-- _≠_ : {l : Level}{A : Set l}{{_ : hasDecEq A}}(x x' : A) → Set
-- x ≠ x' = does (x ≐ x') ≡ false

-- symm≠ :
--   {l : Level}
--   {A : Set l}
--   {{_ : hasDecEq A}}
--   (x x' : A)
--   → ----------------
--   x ≠ x' → x' ≠ x
-- symm≠ x x' _ with  x ≐ x'
-- symm≠  _ _ p    | equ with () ← p
-- symm≠  _ _ refl | neq q = dec-neq _ _ (q ∘ symm)

-- ¬≡→≠  :
--   {ℓ : Level}
--   {A : Set ℓ}
--   {{_ : hasDecEq A}}
--   {x y : A}
--   → ----------------
--   ¬ x ≡ y → x ≠ y
-- ¬≡→≠ {x = x} {y} = dec-neq x y

-- ¬≠ :
--   {l : Level}
--   {A : Set l}
--   {{_ : hasDecEq A}}
--   (x : A)
--   → ----------------
--   ¬ x ≠ x
-- ¬≠ x ¬p rewrite dec-equ x with () ← ¬p

-- ≠→¬≡ :
--   {ℓ : Level}
--   {A : Set ℓ}
--   {{_ : hasDecEq A}}
--   {x y : A}
--   → ----------------
--   x ≠ y → ¬ x ≡ y
-- ≠→¬≡ p refl with () ← ¬≠ _ p

-- inj≠ :
--   {ℓ : Level}
--   {A B : Set ℓ}
--   {{_ : hasDecEq A}}
--   {{_ : hasDecEq B}}
--   {f : A → B}
--   (injf : injection _≡_ _≡_ f)
--   {x x' : A}
--   → -----------------
--   x ≠ x' → f x ≠ f x'
-- inj≠ injf p = ¬≡→≠ λ q → ≠→¬≡ p (injf q)

-- ap≠ :
--   {ℓ : Level}
--   {A B : Set ℓ}
--   {{_ : hasDecEq A}}
--   {{_ : hasDecEq B}}
--   {f : A → B}
--   {x x' : A}
--   → -----------------
--   f x ≠ f x' → x ≠ x'
-- ap≠ {A = A} {B} p = ¬≡→≠ {A = A} λ{refl → ≠→¬≡ {A = B} p refl}

-- import Relation.Binary.PropositionalEquality.Properties as ≡

-- instance
--   hasDecEq⊎ :
--     {l : Level}
--     {A B : Set l}
--     {{_ : hasDecEq A}}
--     {{_ : hasDecEq B}}
--     → ----------------
--     hasDecEq (A ⊎ B)
--   isEquivalence {{hasDecEq⊎}} = ≡.isEquivalence
--   _≐_ {{hasDecEq⊎}} (ι₁ x) (ι₁ x') with  x ≐ x'
--   ... | equ   = yes refl
--   ... | neq f = no λ{refl → f refl}
--   _≐_ {{hasDecEq⊎}} (ι₁ _) (ι₂ _) = no λ()
--   _≐_ {{hasDecEq⊎}} (ι₂ _) (ι₁ _) = no λ()
--   _≐_ {{hasDecEq⊎}} (ι₂ y) (ι₂ y') with y ≐ y'
--   ... | equ   = yes refl
--   ... | neq f = no λ{refl → f refl}

-- ----------------------------------------------------------------------
-- -- Natural number type
-- ----------------------------------------------------------------------
-- open import Data.Nat public
--   using (ℕ ; zero ; _+_ ; pred ; _∸_ ; _≤_ ; _<_ ; _≥_ ; _>_)
--   renaming ( _≡ᵇ_ to _≡ᴮ_ ; suc to _+1 ; z≤n to 0≤ ; s≤s to +1≤
--            ; _⊔_ to max)

-- open import Data.Nat.Properties public using ()
--   renaming ( +-identityʳ to 0+ ; +-suc to +1+ ; +-comm to +comm
--            ; n∸n≡0 to ∸-refl ; 0∸n≡0 to 0∸ ; ≤-refl to ≤refl
--            ; m≤n⇒m≤1+n to ≤+1 ; ≤-trans to ≤trans
--            ; m≤n⇒m≤n+o to ≤+ ; m≤n⇒m≤o+n to ≤+' ; +-monoˡ-≤ to +≤
--            ; <-≤-trans to <≤ ; ≤-<-trans to ≤< ; <-trans to <<
--            ; 1+n≰n to ¬x+1≤x ; <-asym to ¬<> ; ≤∧≢⇒< to trich
--            ; ≤-total to ≤∨≥ ; ≤-pred to ≤-1 ; <⇒≤pred to predadj
--            ; m∸n+n≡m to ∸≤' ; m≤n⇒m⊔n≡n to max≤ ; m≥n⇒m⊔n≡m to max≥
--            )

-- pattern _+2 x = (x +1) +1

-- -- Decidable equality
-- instance
--   hasDecEqℕ : hasDecEq ℕ
--   isEquivalence {{hasDecEqℕ}} = ≡.isEquivalence
--   _≐_ {{hasDecEqℕ}} zero zero = yes refl
--   _≐_ {{hasDecEqℕ}} zero (y +1) = no λ()
--   _≐_ {{hasDecEqℕ}} (x +1) zero = no λ()
--   _≐_ {{hasDecEqℕ}} (x +1) (y +1) with  x ≐ y
--   ... | equ   = yes refl
--   ... | neq f = no λ{refl → f refl}

-- +1≠ : ∀{x y} → x ≠ y → x +1 ≠ y +1
-- +1≠ {x} {y} p = dec-neq (x +1) (y +1) λ{refl → ¬≠ x p}

-- +≠ : ∀ {x y} z → x ≠ y → x + z ≠ y + z
-- +≠ {x} {y} 0       p rewrite 0+ x | 0+ y = p
-- +≠ {x} {y} (z +1)  p rewrite +1+ x z | +1+ y z = +1≠ {x + z} {y + z} (+≠ {x} {y} z p)

-- ≠+1 : ∀ x → x ≠ x +1
-- ≠+1 0      = dec-neq 0 1 λ ()
-- ≠+1 (x +1) = +1≠ {x} (≠+1 x)

-- 1≤+1 : ∀{x} → 1 ≤ x +1
-- 1≤+1 = +1≤ 0≤

-- +1< : ∀{x y} → x < y → x +1 < y +1
-- +1< = +1≤

-- <→+1≤ : ∀ x y → x < y → x +1 ≤ y
-- <→+1≤ _ _ p = p

-- +1≤→< : ∀ x y → x +1 ≤ y → x < y
-- +1≤→< _ _ p = p

-- ≤≠ : ∀{x y} → x ≤ y → x ≠ y → x +1 ≤ y
-- ≤≠ {x} p q with Data.Nat.Properties.≤⇒≤′ p
-- ... | Data.Nat.≤′-refl with () ← ¬≠ x q
-- ... | Data.Nat.≤′-step p = +1≤ (Data.Nat.Properties.≤′⇒≤ p)
--   where open Data.Nat.Properties 

-- trich' : ∀{x y} → ¬(y ≤ x) → x < y
-- trich' {x} {y} _ with ≤∨≥ x y
-- trich' {x} {y} _  | ι₁ _ with  x ≐ y
-- trich'         _  | ι₁ q | neq f = trich q λ{refl → f refl}
-- trich'         p  | ι₁ q | equ with () ← p q
-- trich'         p  | ι₂ q with () ← p q

-- +1≤→≠ : ∀ x y → x +1 ≤ y → y ≠ x
-- +1≤→≠ x y p = dec-neq y x λ{refl → ¬x+1≤x p}

-- <→≠ : ∀ x y → x < y → y ≠ x
-- <→≠ x (y +1) p = dec-neq (y +1) x λ{refl → ¬x+1≤x p}

-- pred+1≤ : ∀ x → x ≤ (pred x) +1
-- pred+1≤ 0      = 0≤
-- pred+1≤ (_ +1) = ≤refl

-- ∸≤ : ∀{x} y → x ≤ (x ∸ y) + y
-- ∸≤ {x} y rewrite +comm (x ∸ y) y = Data.Nat.Properties.m≤n+m∸n x y

-- ∸adj : ∀{x y z} → x + y ≤ z → x ≤ z ∸ y
-- ∸adj {x} = Data.Nat.Properties.m+n≤o⇒m≤o∸n x

-- pred+1 : ∀{x} → 1 ≤ x → (pred x) +1 ≡ x
-- pred+1 {x +1} p = refl

-- ¬x<x : ∀ x → ¬(x < x)
-- ¬x<x _ = Data.Nat.Properties.<-irrefl refl

-- ≤max₁ : ∀{x y} → x ≤ max x y
-- ≤max₁ {x} {y} = Data.Nat.Properties.m≤m⊔n x y

-- ≤max₂ : ∀{x y} → y ≤ max x y
-- ≤max₂ {x} {y} = Data.Nat.Properties.m≤n⊔m x y

-- ≤lub : ∀ x y z → x ≤ z → y ≤ z → max x y ≤ z
-- ≤lub x y z = Data.Nat.Properties.⊔-lub

-- open import Data.Nat.Induction using (<-wellFounded)

-- -- < is well founded
-- wf< : wf.iswf _<_
-- wf< = <-wellFounded

-- ----------------------------------------------------------------------
-- -- Finite enumerated sets
-- ----------------------------------------------------------------------
-- open import Data.Vec.Functional as Vec public using (Vector)

-- open import Data.Fin public using (Fin ; zero) renaming (suc to succ ; _≤_ to _≤′_ ; _<_ to _<′_)
-- open import Data.Fin using (fromℕ<)
-- open import Data.Fin.Properties using (toℕ<n)

-- -- Maximum on finite enumerated sets
-- _⊔′_ : ∀ {n : ℕ} → Fin n → Fin n → Fin n
-- n ⊔′ m = fromℕ< (≤lub _ _ _ (toℕ<n n) (toℕ<n m))

-- -- Maximum of finitely many numbers
-- Max : {n : ℕ} → Vector ℕ n → ℕ
-- Max = Vec.foldr max 0

-- ≤Max :
--   {n : ℕ}
--   (f : Vector ℕ n)
--   (k : Fin n)
--   → -------------
--   f k ≤ Max f
-- ≤Max {n +1} f zero     = ≤max₁
-- ≤Max {n +1} f (succ k) = ≤trans (≤Max (f ∘ succ) k) ≤max₂

-- ----------------------------------------------------------------------
-- -- Arrays
-- ----------------------------------------------------------------------
-- record Array {l : Level}(A : Set l) : Set l where
--   constructor mkArray
--   field
--     length : ℕ
--     index  : Vector A length

-- open Array public

-- ----------------------------------------------------------------------
-- -- Lists
-- ----------------------------------------------------------------------
-- open import Data.List using (List ; [] ; _∷_) public

-- ----------------------------------------------------------------------
-- --  Finite sets represented by trees
-- ----------------------------------------------------------------------
-- infix 1 [_]
-- infixr 6 _∪_
-- data Fset {l : Level}(A : Set l) : Set l where
--   Ø   : Fset A
--   [_] : A → Fset A
--   _∪_ : Fset A → Fset A → Fset A

-- ∪inj₁ :
--   {l : Level}
--   {A : Set l}
--   {xs xs' ys ys' : Fset A}
--   → -----------------------------
--   (xs ∪ xs' ≡ ys ∪ ys') → xs ≡ ys
-- ∪inj₁ refl = refl

-- ∪inj₂ :
--   {l : Level}
--   {A : Set l}
--   {xs xs' ys ys' : Fset A}
--   → -------------------------------
--   (xs ∪ xs' ≡ ys ∪ ys') → xs' ≡ ys'
-- ∪inj₂ refl = refl

-- -- Functorial action
-- Fset′ :
--   {l : Level}
--   {A B : Set l}
--   (f : A → B)
--   → -------------
--   Fset A → Fset B
-- Fset′ f Ø          = Ø
-- Fset′ f [ x ]      = [ f x ]
-- Fset′ f (xs ∪ xs') = Fset′ f xs ∪ Fset′ f xs'

-- -- Membership
-- infix 4 _∈_
-- data _∈_
--   {l : Level}
--   {A : Set l}
--   (x : A)
--   : ------------
--   Fset A → Set l
--   where
--   ∈[] : x ∈ [ x ]
--   ∈∪₁ : ∀{xs xs'} → x ∈ xs  → x ∈ xs ∪ xs'
--   ∈∪₂ : ∀{xs xs'} → x ∈ xs' → x ∈ xs ∪ xs'

-- Fset′∈ :
--   {l : Level}
--   {A B : Set l}
--   {f : A → B}
--   {x : A}
--   {xs : Fset A}
--   (_ : x ∈ xs)
--   → --------------
--   f x ∈ Fset′ f xs
-- Fset′∈ ∈[]     = ∈[]
-- Fset′∈ (∈∪₁ p) = ∈∪₁ (Fset′∈ p)
-- Fset′∈ (∈∪₂ p) = ∈∪₂ (Fset′∈ p)

-- -- Non-membership
-- module _ {l : Level}{A : Set l}{{α : hasDecEq A}} where
--   infix 4 _∉_
--   data _∉_ (x : A) : Fset A → Set l
--     where
--     instance
--       ∉Ø  : x ∉ Ø
--       ∉[] : ∀{x'}{{p : x ≠ x'}} → x ∉ [ x' ]
--       ∉∪  : ∀{xs xs'}{{p : x ∉ xs}}{{q : x ∉ xs'}} → x ∉ xs ∪ xs'

--   ∉∪₁ :
--     {x : A}
--     {xs xs' : Fset A}
--     → -------------------
--     x ∉ xs ∪ xs' → x ∉ xs
--   ∉∪₁ ∉∪ = it

--   ∉∪₂ :
--     {x : A}
--     {xs xs' : Fset A}
--     → --------------------
--     x ∉ xs ∪ xs' → x ∉ xs'
--   ∉∪₂ ∉∪ = it

--   ∉[]₁ :
--     {x x' : A}
--     → -----------------
--     x ∉ [ x' ] → x ≠ x'
--   ∉[]₁ ∉[] = it

-- Fset′∉ :
--   {l : Level}
--   {A B : Set l}
--   {{_ : hasDecEq A}}
--   {{_ : hasDecEq B}}
--   {f : A → B}
--   {x : A}
--   {xs : Fset A}
--   {{p : f x ∉ Fset′ f xs}}
--   → ----------------------
--   x ∉ xs
-- Fset′∉ = ¬∈→∉ λ q → ∉→¬∈ (Fset′∈ q)

-- -- Finite union of finite subsets
-- ⋃ : {l : Level}{A : Set l}{n : ℕ} → Vector (Fset A) n → Fset A
-- ⋃ = Vec.foldr _∪_ Ø

-- ∉⋃ :
--   {l : Level}
--   {A : Set l}
--   {{_ : hasDecEq A}}
--   {n : ℕ}
--   (f : Vector (Fset A) n)
--   {x : A}
--   (k : Fin n)
--   {{p : x ∉ ⋃ f}}
--   → ------------------
--   x ∉ f k
-- ∉⋃ {n = n +1} f zero     {{p}} = ∉∪₁ p
-- ∉⋃ {n = n +1} f (succ k) {{p}} = ∉⋃ {n = n} (f ∘ succ) k {{∉∪₂ p}}

-- ∉⋃′ :
--   {l : Level}
--   {A : Set l}
--   {{_ : hasDecEq A}}
--   {n : ℕ}
--   (f : Vector (Fset A) n)
--   {x : A}
--   (g : (k : Fin n)→ x ∉ f k)
--   → ------------------------
--   x ∉ ⋃ f
-- ∉⋃′ {n = 0}    _ _ = ∉Ø
-- ∉⋃′ {n = n +1} f g =
--   ∉∪{{p = g zero}}{{∉⋃′{n = n} (f ∘ succ) (g ∘ succ)}}

-- -- Subtract an element
-- infix 6 _-[_]
-- _-[_] :
--   {l : Level}
--   {A : Set l}
--   {{α : hasDecEq A}}
--   (xs : Fset A)
--   (x : A)
--   → ----------------
--   Fset A
-- Ø         -[ x ] = Ø
-- [ y ]     -[ x ] = if does(x ≐ y) then Ø else [ y ]
-- (ys ∪ zs) -[ x ] = (ys -[ x ]) ∪ (zs -[ x ])

-- x∉xs-[x] :
--   {l : Level}
--   {A : Set l}
--   {{α : hasDecEq A}}
--   (xs : Fset A)
--   {x : A}
--   → ----------------
--   x ∉ xs -[ x ]
-- x∉xs-[x] Ø = ∉Ø
-- x∉xs-[x] [ y ] {x} with x ≐ y
-- ... | neq f        = ∉[]{{p = ¬≡→≠ f}}
-- ... | equ          = ∉Ø
-- x∉xs-[x] (ys ∪ zs) = ∉∪{{p = x∉xs-[x] ys}}{{x∉xs-[x] zs}}

-- y∉zs→y∉zs-[x] :
--   {l : Level}
--   {A : Set l}
--   {{α : hasDecEq A}}
--   {x y : A}
--   (zs : Fset A)
--   → --------------------
--   y ∉ zs → y ∉ zs -[ x ]
-- y∉zs→y∉zs-[x] Ø ∉Ø = ∉Ø
-- y∉zs→y∉zs-[x] {x = x} {y} [ z ] ∉[] with x ≐ z
-- ... | equ                   = ∉Ø
-- ... | neq f                 = ∉[]
-- y∉zs→y∉zs-[x] (zs ∪ zs') ∉∪ =
--   ∉∪{{p = y∉zs→y∉zs-[x] zs it}}{{y∉zs→y∉zs-[x] zs' it}}

-- ∉-[] :
--   {l : Level}
--   {A : Set l}
--   {{α : hasDecEq A}}
--   {xs : Fset A}
--   {x y : A}
--   (_ : y ∉ xs -[ x ])
--   (_ : y ≠ x)
--   → -----------------
--   y ∉ xs
-- ∉-[] {xs = Ø      } ∉Ø _              = ∉Ø
-- ∉-[] {xs = [ z ]  } {x} p   q with x ≐ z
-- ∉-[] {xs = [ _ ]  }     ∉[] _ | neq _ = ∉[]
-- ∉-[] {xs = [ _ ]  }     _   q | equ   = ∉[]{{p = q}}
-- ∉-[] {xs = ys ∪ zs}     ∉∪  q         =
--   ∉∪{{p = ∉-[] it q}}{{∉-[] it q}}

-- -- Intersection
-- ι₂⁻¹ :
--   {l : Level}
--   {A B : Set l}
--   → ------------------
--   Fset(A ⊎ B) → Fset B
-- ι₂⁻¹ Ø         = Ø
-- ι₂⁻¹ [ ι₁ _ ]  = Ø
-- ι₂⁻¹ [ ι₂ y ]  = [ y ]
-- ι₂⁻¹ (xs ∪ ys) = ι₂⁻¹ xs ∪ ι₂⁻¹ ys

-- ∉ι₂⁻¹→ι₂∉ :
--   {l : Level}
--   {A B : Set l}
--   {{_ : hasDecEq A}}
--   {{_ : hasDecEq B}}
--   (zs : Fset(A ⊎ B))
--   (y : B)
--   → ---------------------
--   y ∉ ι₂⁻¹ zs → ι₂ y ∉ zs
-- ∉ι₂⁻¹→ι₂∉ Ø _ _ = ∉Ø
-- ∉ι₂⁻¹→ι₂∉ [ ι₁ x ] y ∉Ø = ¬∈→∉ λ{()}
-- ∉ι₂⁻¹→ι₂∉ {A = A} {B} [ ι₂ y' ] y (∉[]{{p = p}}) =
--   ∉[]{{p = inj≠ {f = ι₂ {A = A}{B}}(injectionι₂) p}}
-- ∉ι₂⁻¹→ι₂∉ (zs ∪ zs') y ∉∪ =
--   ∉∪ {{p = ∉ι₂⁻¹→ι₂∉ zs y it}}{{∉ι₂⁻¹→ι₂∉ zs' y it}}

-- -- Maximum of a finite set of numbers
-- maxfs : Fset ℕ → ℕ
-- maxfs Ø         = 0
-- maxfs [ x ]     = x
-- maxfs (xs ∪ ys) = max (maxfs xs) (maxfs ys)

-- ≤maxfs : ∀{xs x} → x ∈ xs → x ≤ maxfs xs
-- ≤maxfs ∈[] = ≤refl
-- ≤maxfs (∈∪₁ p) = ≤trans (≤maxfs p) ≤max₁
-- ≤maxfs (∈∪₂ p) = ≤trans (≤maxfs p) ≤max₂

-- maxfs+1∉ : ∀ xs → (maxfs xs +1) ∉ xs
-- maxfs+1∉ xs =
--   ¬∈→∉ λ p → ¬x<x _ (≤maxfs p)

-- -- Finite ordinals
-- ordinal : ℕ → Fset ℕ
-- ordinal 0      = Ø
-- ordinal (n +1) = ordinal n ∪ [ n ]

-- ∉ordinal→≥ : ∀ m n → m ∉ ordinal n → m ≥ n
-- ∉ordinal→≥ _ 0 _ = 0≤
-- ∉ordinal→≥ m (n +1) (∉∪{{q = ∉[]}}) =
--   trich (∉ordinal→≥ m n it) (≠→¬≡ (symm≠ m n it))

-- ----------------------------------------------------------------------
-- -- Dependent product
-- -- Cartesian product
-- ----------------------------------------------------------------------
-- open import Data.Product using (_,_ ; _×_ ; ∃; ∃₂)
--   renaming (Σ to ∑ ; proj₁ to π₁ ; proj₂ to π₂)
--   public

-- infix 2 ∑-syntax
-- ∑-syntax : {l m : Level}(A : Set l) → (A → Set m) → Set (l ⊔ m)
-- ∑-syntax = ∑
-- syntax ∑-syntax A (λ x → B) = ∑ x ∶ A , B

-- pair :
--   {l m : Level}
--   {A : Set l}
--   (B : A → Set m)
--   (x : A)
--   (_ : B x)
--   → -------------
--   ∑ A B
-- pair _ x y = (x , y)

-- _^_ : {l : Level} → Set l → ℕ → Set l
-- X ^ n = Vector X n

-- π[_] : {l : Level}{X : Set l}{n : ℕ} (i : Fin n) → X ^ n → X
-- π[ i ] = _$ i
