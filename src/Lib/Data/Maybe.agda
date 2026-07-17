open import 1Lab.Prelude

open import Data.Maybe.Base

module Lib.Data.Maybe where

private variable
  ℓ : Level
  A B : Type ℓ

map-just : {x : Maybe A} {y : A} {f : A → B} → x ≡ just y → map f x ≡ just (f y)
map-just {x = nothing} p = absurd (just≠nothing (sym p))
map-just {x = just x}  p = ap (just ∘ _) (just-inj p)

map-just'
  : {A : Type ℓ} {x : Maybe A} {y : B} {f : A → B}
  → map f x ≡ just y → Σ[ y' ∈ A ] x ≡ just y' × f y' ≡ y
map-just' {x = nothing} p = absurd (just≠nothing (sym p))
map-just' {x = just x}  p = x , refl , just-inj p

maybe-join : Maybe (Maybe A) → Maybe A
maybe-join = _>>= λ z → z

join-nothing
  : {x : Maybe (Maybe A)} → (∀ {y} → just y ≡ x → y ≡ nothing)
  → maybe-join x ≡ nothing
join-nothing {x = nothing} p = refl
join-nothing {x = just x}  p = p refl

join-just-inv
  : {x : Maybe (Maybe A)} {y : A} → maybe-join x ≡ just y → x ≡ just (just y)
join-just-inv {x = nothing} p       = absurd (just≠nothing (sym p))
join-just-inv {x = just nothing} p  = absurd (just≠nothing (sym p))
join-just-inv {x = just (just x)} p = ap just p

join-nat : {f : A → B} → maybe-join ∘ map (map f) ≡ map f ∘ maybe-join
join-nat = ext λ where
  nothing   → refl
  (just _)  → refl

join-unitr : maybe-join ∘ map (just {A = A}) ≡ id
join-unitr = ext λ where
  nothing  → refl
  (just _) → refl

join-unitl : maybe-join ∘ just {A = Maybe A} ≡ id
join-unitl = refl

join-assoc : maybe-join ∘ map (maybe-join {A = A}) ≡ maybe-join ∘ maybe-join
join-assoc = ext λ where
  nothing  → refl
  (just _) → refl
