-- open import Cat.Functor.FullSubcategory
-- open import Cat.Functor.Naturality
-- open import Cat.Functor.Properties
-- open import Cat.Diagram.Terminal
-- open import Cat.Functor.Constant
-- open import Cat.Functor.Adjoint
-- open import Cat.Functor.Base
open import Cat.Prelude

-- open import Data.Dec.Base
-- open import Data.Dec.Base
-- open import Data.Fin.Base hiding (_≤_)
-- open import Data.Sum.Base

open import DPPL.Denotations.Regularity
open import DPPL.Regularity

-- open import Lib.Cat.Concrete
-- open import Lib.Data.Vector
-- open import Lib.Data.Dec

open import Lib.Algebra.Reals

-- open import Order.Lattice
-- open import Order.Base

-- import Cat.Functor.Hom as Hom
-- import Cat.Reasoning as Cr

module DPPL.Denotations.Site (R : Reals₀) (Ax : RegAssumptions R) where

-- open Reals R using (ℝ ; 0r)
open RegAssumptions Ax
open RegProperties R Ax

open Reg≤ using (_≤_ ; ≤-refl ; ≤-trans)
-- open is-lattice Reg↓-lattice

-- private
--   variable
--     m n : Nat
--     c c' : Reg↓

--   ≤→is-yes : c ≤ c' → is-yes (holds? (c ≤ c'))
--   ≤→is-yes = true→is-yes

--   ≰→is-no : ¬ c ≤ c' → is-no (holds? (c ≤ c'))
--   ≰→is-no = false→is-no

-- open Functor
-- open _=>_
-- open Cr._≅_
-- open Cr.Inverses

module _ where
  open Precategory

  ℛ : Precategory lzero lzero
  ℛ .Ob = Nat × Reg
  ℛ .Hom (m , c) (n , d) = ∫ₚ (⟨ c ∣ d ⟩-reg {m} {n})
  ℛ .Hom-set _ _ _ _ = {!!} -- hlevel 1
  ℛ .id {m , c} = (λ x → x) , id-reg' ≤-refl
  ℛ ._∘_ (f , Hf) (g , Hg) = f ⊙ g , ∘-reg' Hf Hg
  ℛ .idr f = refl ,ₚ {!!}
  ℛ .idl g = refl ,ₚ {!!}
  ℛ .assoc f g h = refl ,ₚ {!!}

-- module ℛ = Cr ℛ

-- ℛ-hom-path : {x y : ℛ.Ob} {f g : ℛ.Hom x y} → f .fst ≡ g .fst → f ≡ g
-- ℛ-hom-path p = p ,ₚ prop!

-- ℛ-terminal : Terminal ℛ
-- ℛ-terminal = record
--   { top  = (0 , bot)
--   ; has⊤ = λ (m , c) → contr
--     ((λ _ ()) , const-reg' λ ())
--     (λ (x , _) → ℛ-hom-path (ext λ _ ()))
--   }

-- module ℛ⊤ = Terminal ℛ-terminal
-- open ℛ⊤ public using () renaming (top to ⋆)

-- ℛ-id≤ : c ≤ c' → ℛ.Hom (m , c) (m , c')
-- ℛ-id≤ H≤ = (λ x → x) , id-reg' H≤

-- ℛ-const : ℝ ^ m → ℛ.Hom ⋆ (m , c)
-- ℛ-const x = (λ _ → x) , const-reg' x

-- ℛ-conc : Conc-category ℛ
-- ℛ-conc .Conc-category.terminal       = ℛ-terminal
-- ℛ-conc .Conc-category.⋆-hom-faithful = ⋆-hom-faithful where
--   open Hom ℛ
--   opaque
--     ⋆-hom-faithful : is-faithful (Hom-from ⋆)
--     ⋆-hom-faithful H≡ =
--       ℛ-hom-path $ funext (λ z → ap fst (H≡ $ₚ ℛ-const z) $ₚ make 0r)

-- open Conc-category ℛ-conc
--   using (ob∣_∣ ; is-conc-hom ; is-conc-hom-prop ; ⋆-hom-faithful)

-- ℛ-underlying : ∀ {U} → ob∣ U ∣ ≃ ℝ ^ (U .fst)
-- ℛ-underlying .fst = λ (f , _) → f (make 0r)
-- ℛ-underlying .snd = is-iso→is-equiv $ iso ℛ-const
--   (λ _ → refl)
--   (λ f → ℛ-hom-path (ext λ _ x → ap (λ y → f .fst y x) (ext λ ())))

-- ℛ-conc-hom-equiv
--   : ∀ {U V}
--   → is-conc-hom U V ≃[ →-ap ℛ-underlying ℛ-underlying ] (_∈ ⟨ U .snd ∣ V .snd ⟩-reg)
-- ℛ-conc-hom-equiv {U} {V} =
--   prop-over-ext (→-ap ℛ-underlying ℛ-underlying)
--     (λ {b} → is-conc-hom-prop _ _ b) (hlevel 1)
--     (λ f ((f' , Hf) , p) →
--       subst (_∈ ⟨ U .snd ∣ V .snd ⟩-reg)
--         (ap (Equiv.to (→-ap ℛ-underlying ℛ-underlying)) (sym p)) Hf)
--     (λ g Hg → (g , Hg) , funext λ x → Equiv.η ℛ-underlying ((g , Hg) ℛ.∘ x))

-- μ⟨_⟩ : Reg↓ → Functor ℛ ℛ
-- μ⟨ c ⟩ .F₀ (m , d) =
--   ifᵈ holds? (d ≤ c) then
--     m , d
--   else
--     ⋆
-- μ⟨ c ⟩ .F₁ {_ , z} {_ , y} (f , Hf) with holds? (y ≤ c) | holds? (z ≤ c)
-- ... | yes _ | yes _ = f , Hf
-- ... | yes _ | no _  = ℛ-const (f (make 0r))
-- ... | no _  | _     = ℛ⊤.!
-- μ⟨ c ⟩ .F-id {_ , z} with holds? (z ≤ c)
-- ... | yes _ = refl
-- ... | no  _ = ℛ⊤.!-unique _
-- μ⟨ c ⟩ .F-∘ {_ , z} {_ , y} {_ , x} (f , Hf) (g , Hg)
--   with holds? (x ≤ c) | holds? (y ≤ c) | holds? (z ≤ c)
-- ... | no _    | _      | _     = ℛ⊤.!-unique _
-- ... | yes _   | yes _  | yes _ = refl
-- ... | yes _   | yes _  | no  _ = ℛ-hom-path refl
-- ... | yes x≤c | no y≰c | z≤?c
--   with f-const ← subst (_ ∈_) (⟨∣⟩-reg-≰ λ y≤x → y≰c (≤-trans y≤x x≤c)) Hf | z≤?c
-- ... | yes _ =
--   case f-const of λ x Hf' → ℛ-hom-path $ funext (λ _ → Hf' $ₚ _ ∙ sym (Hf' $ₚ _))
-- ... | no  _ =
--   case f-const of λ x Hf' → ℛ-hom-path $ funext (λ _ → Hf' $ₚ _ ∙ sym (Hf' $ₚ _))

-- μ-unit : Id => μ⟨ c ⟩
-- μ-unit {c} .η (m , x) with holds? (x ≤ c)
-- ... | yes _ = ℛ.id
-- ... | no  _ = ℛ⊤.!
-- μ-unit {c} .is-natural (m , z) (n , y) (f , Hf) with holds? (z ≤ c) | holds? (y ≤ c)
-- ... | _      | no  _   = ℛ-hom-path refl
-- ... | yes _  | yes _   = ℛ-hom-path refl
-- ... | no z≰c | yes y≤c =
--   case f-const of λ x Hf' → ℛ-hom-path $ funext λ _ → Hf' $ₚ _ ∙ sym (Hf' $ₚ _)
--   where f-const = subst (_ ∈_) (⟨∣⟩-reg-≰ λ z≤y → z≰c (≤-trans z≤y y≤c)) Hf

-- μ-mult : μ⟨ c ⟩ F∘ μ⟨ c' ⟩ ≅ⁿ μ⟨ c' ∩ c ⟩
-- μ-mult {c} {c'} = to-natural-iso ni where
--   -- This proof is... A hundred case splits followed by id or refl :)
--   ni : make-natural-iso (μ⟨ c ⟩ F∘ μ⟨ c' ⟩) μ⟨ c' ∩ c ⟩
--   ni .make-natural-iso.eta (m , z) with holds? (z ≤ c' ∩ c)
--   ... | yes z≤∩ with yes _ ← holds? (z ≤ c') | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤l)
--                 with yes _ ← holds? (z ≤ c)  | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤r) =
--          ℛ.id
--   ... | no z≰∩ with holds? (z ≤ c')
--   ... | yes z≤c' with no _ ← holds? (z ≤ c)
--     | _ ← ≰→is-no (λ z≤c → z≰∩ (∩-universal _ z≤c' z≤c))          = ℛ.id
--   ... | no _ with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c}) = ℛ.id
--   ni .make-natural-iso.inv (m , z) with holds? (z ≤ c' ∩ c)
--   ... | yes z≤∩ with yes _ ← holds? (z ≤ c') | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤l)
--                 with yes _ ← holds? (z ≤ c)  | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤r) =
--          ℛ.id
--   ... | no z≰∩ with holds? (z ≤ c')
--   ... | yes z≤c' with no _ ← holds? (z ≤ c)
--     | _ ← ≰→is-no (λ z≤c → z≰∩ (∩-universal _ z≤c' z≤c))          = ℛ.id
--   ... | no _ with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c}) = ℛ.id
--   ni .make-natural-iso.eta∘inv (m , z) with holds? (z ≤ c' ∩ c)
--   ... | yes z≤∩ with yes _ ← holds? (z ≤ c') | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤l)
--                 with yes _ ← holds? (z ≤ c)  | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤r) =
--          ℛ-hom-path refl
--   ... | no z≰∩ with holds? (z ≤ c')
--   ... | yes z≤c' with no _ ← holds? (z ≤ c)
--     | _ ← ≰→is-no (λ z≤c → z≰∩ (∩-universal _ z≤c' z≤c))          = ℛ-hom-path refl
--   ... | no _ with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c}) = ℛ-hom-path refl
--   ni .make-natural-iso.inv∘eta (m , z) with holds? (z ≤ c' ∩ c)
--   ... | yes z≤∩ with yes _ ← holds? (z ≤ c') | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤l)
--                 with yes _ ← holds? (z ≤ c)  | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤r) =
--          ℛ-hom-path refl
--   ... | no z≰∩ with holds? (z ≤ c')
--   ... | yes z≤c' with no _ ← holds? (z ≤ c)
--     | _ ← ≰→is-no (λ z≤c → z≰∩ (∩-universal _ z≤c' z≤c))          = ℛ-hom-path refl
--   ... | no _ with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c}) = ℛ-hom-path refl
--   ni .make-natural-iso.natural (m , z) _ _ with holds? (z ≤ c' ∩ c)
--   ni .make-natural-iso.natural (m , z) _ _ | no z≰∩ with holds? (z ≤ c')
--   ni .make-natural-iso.natural (m , z) (n , y) _ | no z≰∩ | yes z≤c'
--     with no _ ← holds? (z ≤ c) | _ ← ≰→is-no (λ z≤c → z≰∩ (∩-universal _ z≤c' z≤c))
--     with holds? (y ≤ c' ∩ c)
--   ... | yes y≤∩ with yes _ ← holds? (y ≤ c') | _ ← ≤→is-yes (≤-trans y≤∩ ∩≤l)
--                 with yes _ ← holds? (y ≤ c)  | _ ← ≤→is-yes (≤-trans y≤∩ ∩≤r) =
--     ℛ-hom-path refl
--   ... | no y≰∩ with holds? (y ≤ c')
--   ... | yes y≤c' with no _ ← holds? (y ≤ c)
--     | _ ← ≰→is-no (λ y≤c → y≰∩ (∩-universal _ y≤c' y≤c))          = ℛ-hom-path refl
--   ... | no _ with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c}) = ℛ-hom-path refl
--   ni .make-natural-iso.natural (m , z) (n , y) _ | no z≰∩ | no _
--     with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c})
--     with holds? (y ≤ c' ∩ c)
--   ... | yes y≤∩ with yes _ ← holds? (y ≤ c') | _ ← ≤→is-yes (≤-trans y≤∩ ∩≤l)
--                 with yes _ ← holds? (y ≤ c)  | _ ← ≤→is-yes (≤-trans y≤∩ ∩≤r) =
--     ℛ-hom-path refl
--   ... | no y≰∩ with holds? (y ≤ c')
--   ... | yes y≤c' with no _ ← holds? (y ≤ c)
--     | _ ← ≰→is-no (λ y≤c → y≰∩ (∩-universal _ y≤c' y≤c))          = ℛ-hom-path refl
--   ... | no _ with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c}) = ℛ-hom-path refl
--   ni .make-natural-iso.natural (m , z) (n , y) _ | yes z≤∩
--     with yes _ ← holds? (z ≤ c') | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤l)
--     with yes _ ← holds? (z ≤ c)  | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤r)
--     with holds? (y ≤ c' ∩ c)
--   ... | yes y≤∩ with yes _ ← holds? (y ≤ c') | _ ← ≤→is-yes (≤-trans y≤∩ ∩≤l)
--                 with yes _ ← holds? (y ≤ c)  | _ ← ≤→is-yes (≤-trans y≤∩ ∩≤r) =
--     ℛ-hom-path refl
--   ... | no y≰∩ with holds? (y ≤ c')
--   ... | yes y≤c' with no _ ← holds? (y ≤ c)
--     | _ ← ≰→is-no (λ y≤c → y≰∩ (∩-universal _ y≤c' y≤c))          = ℛ-hom-path refl
--   ... | no _ with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c}) = ℛ-hom-path refl

-- μ-≤ : c' ≤ c → μ⟨ c ⟩ => μ⟨ c' ⟩
-- μ-≤ {c'} {c} H≤ .η (m , x) with holds? (x ≤ c)
-- ... | yes _ = μ-unit .η (m , x)
-- ... | no x≰c
--   with no _ ← holds? (x ≤ c') | _ ← ≰→is-no (λ x≤c' → x≰c (≤-trans x≤c' H≤)) = ℛ⊤.!
-- μ-≤ {c'} {c} H≤ .is-natural (m , z) (n , y) (f , Hf)
--   with holds? (z ≤ c) | holds? (y ≤ c)
-- ... | yes _    | yes _ = μ-unit .is-natural _ _ (f , Hf)
-- ... | no z≰c   | yes _ with no _ ← holds? (z ≤ c')
--   | _ ← ≰→is-no (λ z≤c' → z≰c (≤-trans z≤c' H≤)) | holds? (y ≤ c')
-- ... | no _  = ℛ⊤.!-unique₂ _ _
-- ... | yes _ = ℛ.idl _ ∙ ℛ.intror (ℛ⊤.!-unique _)
-- μ-≤ {c'} {c} H≤ .is-natural _ (n , y) _ | _ | no y≰c
--   with no _ ← holds? (y ≤ c') | _ ← ≰→is-no (λ y≤c' → y≰c (≤-trans y≤c' H≤)) =
--   ℛ⊤.!-unique₂ _ _

-- μ⟨A⟩-Id : μ⟨ A↓ ⟩ ≅ⁿ Id
-- μ⟨A⟩-Id = to-natural-iso ni where
--   ni : make-natural-iso μ⟨ A↓ ⟩ Id
--   ni .make-natural-iso.eta (m , c)
--     with yes _ ← holds? (c ≤ A↓) | _ ← ≤→is-yes {c} A! = ℛ.id
--   ni .make-natural-iso.inv (m , c)
--     with yes _ ← holds? (c ≤ A↓) | _ ← ≤→is-yes {c} A! = ℛ.id
--   ni .make-natural-iso.eta∘inv (m , c)
--     with yes _ ← holds? (c ≤ A↓) | _ ← ≤→is-yes {c} A! = ℛ.idl _
--   ni .make-natural-iso.inv∘eta (m , c)
--     with yes _ ← holds? (c ≤ A↓) | _ ← ≤→is-yes {c} A! = ℛ.idl _
--   ni .make-natural-iso.natural (m , c) (n , c') f
--     with yes _ ← holds? (c ≤ A↓)  | _ ← ≤→is-yes {c} A!
--        | yes _ ← holds? (c' ≤ A↓) | _ ← ≤→is-yes {c'} A! =
--     ℛ.id-comm

-- ℛ≤ : Reg↓ → Precategory lzero lzero
-- ℛ≤ c = Restrict {C = ℛ} ((_≤ c) ⊙ snd)

-- ℛ≤-conc : ∀ c → Conc-category (ℛ≤ c)
-- ℛ≤-conc c .Conc-category.terminal .Terminal.top  = (⋆ , ¡)
-- ℛ≤-conc c .Conc-category.terminal .Terminal.has⊤ = ℛ⊤.has⊤ ⊙ fst
-- ℛ≤-conc c .Conc-category.⋆-hom-faithful          = ⋆-hom-faithful

-- ι≤ : ∀ c → Functor (ℛ≤ c) ℛ
-- ι≤ c = Forget-full-subcat

-- ι≤-pres-top : ι≤ c .F₀ (⋆ , ¡) ℛ.≅ ⋆
-- ι≤-pres-top = ℛ.id-iso

-- ι≤-onto-points : ∀ {U} → is-surjective (ι≤ c .F₁ {⋆ , ¡} {U})
-- ι≤-onto-points b = inc (b , refl)

-- μ-pres-ι≤ : μ⟨ c ⟩ F∘ ι≤ c ≅ⁿ ι≤ c
-- μ-pres-ι≤ {c} = to-natural-iso ni where
--   ni : make-natural-iso (μ⟨ c ⟩ F∘ ι≤ c) (ι≤ c)
--   ni .make-natural-iso.eta (U , H≤)
--     with yes _ ← holds? (U .snd ≤ c) | _ ← ≤→is-yes H≤ = ℛ.id
--   ni .make-natural-iso.inv (U , H≤) = μ-unit .η _
--   ni .make-natural-iso.eta∘inv (U , H≤)
--     with yes _ ← holds? (U .snd ≤ c) | _ ← ≤→is-yes H≤ = ℛ-hom-path refl
--   ni .make-natural-iso.inv∘eta (U , H≤)
--     with yes _ ← holds? (U .snd ≤ c) | _ ← ≤→is-yes H≤ = ℛ-hom-path refl
--   ni .make-natural-iso.natural (U , HU) (V , HV) f
--     with yes _ ← holds? (U .snd ≤ c) | _ ← ≤→is-yes HU
--        | yes _ ← holds? (V .snd ≤ c) | _ ← ≤→is-yes HV = ℛ-hom-path refl

-- μ-pres-top : μ⟨ c ⟩ .F₀ ⋆ ℛ.≅ ⋆
-- μ-pres-top = isoⁿ→iso μ-pres-ι≤ (⋆ , ¡)

-- μ-onto-points : ∀ {U} → is-surjective (μ⟨ c ⟩ .F₁ {⋆} {U})
-- μ-onto-points {c = c} {n , c'} (f , Hf) with holds? (c' ≤ c)
-- ... | no  _ = inc (ℛ-const (make 0r) , ℛ⊤.!-unique _)
-- ... | yes _ with yes _ ← holds? (bot ≤ c)  | _ ← ≤→is-yes (¡ {c})
--             with yes _ ← holds? (bot ≤ c') | _ ← ≤→is-yes (¡ {c'}) =
--   inc ((f , Hf) , refl)

-- ℛ≰ : Reg↓ → Precategory lzero lzero
-- ℛ≰ c = Restrict {C = ℛ} λ U → U ℛ.≅ ⋆ ⊎ ¬ U .snd ≤ c

-- -- TODO : Extract these proofs to someplace more general
-- ℛ≰-conc : ∀ c → Conc-category (ℛ≰ c)
-- ℛ≰-conc c .Conc-category.terminal .Terminal.top  = (⋆ , inl ℛ.id-iso)
-- ℛ≰-conc c .Conc-category.terminal .Terminal.has⊤ = ℛ⊤.has⊤ ⊙ fst
-- ℛ≰-conc c .Conc-category.⋆-hom-faithful          = ⋆-hom-faithful

-- ι≰ : ∀ c → Functor (ℛ≰ c) ℛ
-- ι≰ c = Forget-full-subcat

-- ι≰-pres-top : ι≰ c .F₀ (⋆ , inl ℛ.id-iso) ℛ.≅ ⋆
-- ι≰-pres-top = ℛ.id-iso

-- ι≰-onto-points : ∀ {U} → is-surjective (ι≰ c .F₁ {⋆ , inl ℛ.id-iso} {U})
-- ι≰-onto-points b = inc (b , refl)

-- Const⋆-onto-points : ∀ {U} → is-surjective (Const {C = ℛ≰ c} {ℛ} ⋆ .F₁ {⋆ , inl ℛ.id-iso} {U})
-- Const⋆-onto-points b = inc (ℛ-const (make 0r) , ℛ-hom-path (ext λ _ ()))

-- μ-erases-ι≰ : μ⟨ c ⟩ F∘ ι≰ c ≅ⁿ Const ⋆
-- μ-erases-ι≰ {c} = to-natural-iso ni where
--   ni : make-natural-iso (μ⟨ c ⟩ F∘ ι≰ c) (Const ⋆)
--   ni .make-natural-iso.eta _           = ℛ⊤.!
--   ni .make-natural-iso.inv (U , inl p) = μ-unit .η U ℛ.∘ p .from
--   ni .make-natural-iso.inv (U , inr H≰)
--     with no _ ← holds? (U .snd ≤ c) | _ ← ≰→is-no H≰ = ℛ.id
--   ni .make-natural-iso.eta∘inv _                     = ℛ⊤.!-unique₂ _ _
--   ni .make-natural-iso.inv∘eta (U , inl p) =
--     is-contr→is-prop (is-terminal-iso ℛ ⋆≅μU ℛ⊤.has⊤ _) _ _
--     where ⋆≅μU = (F-map-iso μ⟨ c ⟩ p ℛ.∙Iso μ-pres-top {c}) ℛ.Iso⁻¹
--   ni .make-natural-iso.inv∘eta (U , inr H≰)
--     with no _ ← holds? (U .snd ≤ c) | _ ← ≰→is-no H≰ = ℛ⊤.!-unique₂ _ _
--   ni .make-natural-iso.natural (U , HU) (V , HV) _   = ℛ⊤.!-unique₂ _ _

-- ν⟨_⟩ : Reg↓ → Functor ℛ ℛ
-- ν⟨ c ⟩ .F₀ (n , x)                  = n , c ∩ x
-- ν⟨ c ⟩ .F₁ {m , z} {n , y} (f , Hf) = f , Hf' where
--   Hf' : f ∈ ⟨ c ∩ z ∣ c ∩ y ⟩-reg
--   Hf' with holds? (z ≤ y)
--   ... | yes z≤y = subst (_ ∈_) (sym $ ⟨∣⟩-reg-≤ (∩≤∩r z≤y)) (⊆-reg ∩≤r _ Hf)
--   ... | no _    = case Hf of λ x p → subst (_∈ ⟨ _ ∣ _ ⟩-reg) (sym p) (const-reg' x)
-- ν⟨ c ⟩ .F-id    = ℛ-hom-path refl
-- ν⟨ c ⟩ .F-∘ _ _ = ℛ-hom-path refl

-- ν-counit : ν⟨ c ⟩ => Id
-- ν-counit .η X              = ℛ-id≤ ∩≤r
-- ν-counit .is-natural _ _ f = ℛ-hom-path refl

-- ν-pres-top : ν⟨ c ⟩ .F₀ ⋆ ℛ.≅ ⋆
-- ν-pres-top .to             = ℛ⊤.!
-- ν-pres-top .from           = ℛ-id≤ ¡
-- ν-pres-top .inverses .invl = ℛ⊤.!-unique₂ _ _
-- ν-pres-top .inverses .invr = ℛ-hom-path (ext λ _ ())

-- μ-dominates-ν : ν⟨ c ⟩ F∘ μ⟨ c ⟩ ≅ⁿ μ⟨ c ⟩
-- μ-dominates-ν {c} = to-natural-iso ni where
--   ni : make-natural-iso (ν⟨ c ⟩ F∘ μ⟨ c ⟩) μ⟨ c ⟩
--   ni .make-natural-iso.eta _ = ν-counit .η _
--   ni .make-natural-iso.inv (m , z) with holds? (z ≤ c)
--   ... | yes z≤c = ℛ-id≤ (∩-universal _ z≤c ≤-refl)
--   ... | no _    = ℛ-const (make 0r)
--   ni .make-natural-iso.eta∘inv (m , z) with holds? (z ≤ c)
--   ... | yes z≤c = ℛ-hom-path refl
--   ... | no _    = ℛ-hom-path $ ext λ _ ()
--   ni .make-natural-iso.inv∘eta (m , z) with holds? (z ≤ c)
--   ... | yes z≤c = ℛ-hom-path refl
--   ... | no _    = ℛ-hom-path $ ext λ _ ()
--   ni .make-natural-iso.natural _ _ _ = ℛ-hom-path refl

-- ν-dominates-μ : μ⟨ c ⟩ F∘ ν⟨ c ⟩ ≅ⁿ ν⟨ c ⟩
-- ν-dominates-μ {c} = to-natural-iso ni where
--   ni : make-natural-iso (μ⟨ c ⟩ F∘ ν⟨ c ⟩) ν⟨ c ⟩
--   ni .make-natural-iso.eta (m , z)
--     with yes _ ← holds? (c ∩ z ≤ c) | _ ← ≤→is-yes (∩≤l {c} {z}) = ℛ.id
--   ni .make-natural-iso.inv (m , z)
--     with yes _ ← holds? (c ∩ z ≤ c) | _ ← ≤→is-yes (∩≤l {c} {z}) = ℛ.id
--   ni .make-natural-iso.eta∘inv (m , z)
--     with yes _ ← holds? (c ∩ z ≤ c) | _ ← ≤→is-yes (∩≤l {c} {z}) = ℛ-hom-path refl
--   ni .make-natural-iso.inv∘eta (m , z)
--     with yes _ ← holds? (c ∩ z ≤ c) | _ ← ≤→is-yes (∩≤l {c} {z}) = ℛ-hom-path refl
--   ni .make-natural-iso.natural (m , z) (n , y) _
--     with yes _ ← holds? (c ∩ z ≤ c) | _ ← ≤→is-yes (∩≤l {c} {z})
--        | yes _ ← holds? (c ∩ y ≤ c) | _ ← ≤→is-yes (∩≤l {c} {y}) = ℛ-hom-path refl

-- μ⊣ν : μ⟨ c ⟩ ⊣ ν⟨ c ⟩
-- μ⊣ν {c} ._⊣_.unit   = μ-dominates-ν .from ∘nt μ-unit {c}
-- μ⊣ν {c} ._⊣_.counit = ν-counit {c} ∘nt ν-dominates-μ .to
-- μ⊣ν {c} ._⊣_.zig {m , z} with holds? (z ≤ c)
-- ... | yes _ with yes _ ← holds? (c ∩ z ≤ c) | _ ← ≤→is-yes (∩≤l {c} {z}) =
--   ℛ-hom-path refl
-- ... | no _ with yes _ ← holds? (c ∩ bot ≤ c) | _ ← ≤→is-yes (∩≤l {c} {bot}) =
--   ℛ-hom-path $ ext λ _ ()
-- μ⊣ν {c} ._⊣_.zag {m , z}
--   with yes _ ← holds? (c ∩ z ≤ c) | _ ← ≤→is-yes (∩≤l {c} {z}) = ℛ-hom-path refl
