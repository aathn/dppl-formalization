module Lib.Order.Monotone where

open import 1Lab.Prelude
open import Order.Base
open import Order.Diagram.Top
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Instances.Pointwise
import Order.Reasoning as Pr

module _ {o o' ℓ ℓ'} {P : Poset o ℓ} {S : Poset o' ℓ'} where
  private
    module P = Pr P
    module S = Pr S

  Monotone-has-top : Top S → Top Poset[ P , S ]
  Monotone-has-top s-top .Top.top .hom _    = Top.top s-top
  Monotone-has-top s-top .Top.top .pres-≤ _ = S.≤-refl
  Monotone-has-top s-top .Top.has-top _ _   = Top.has-top s-top _

  Monotone-has-bot : Bottom S → Bottom Poset[ P , S ]
  Monotone-has-bot s-bot .Bottom.bot .hom _     = Bottom.bot s-bot
  Monotone-has-bot s-bot .Bottom.bot .pres-≤ _  = S.≤-refl
  Monotone-has-bot s-bot .Bottom.has-bottom _ _ = Bottom.has-bottom s-bot _

  module _ where
    open is-meet
    open is-join
  
    Monotone-meets : (a b : Monotone P S) → ((x : P.Ob) → Meet S (a · x) (b · x)) → Meet Poset[ P , S ] a b
    Monotone-meets a b s-meet .Meet.glb .hom x = Meet.glb (s-meet x)
    Monotone-meets a b s-meet .Meet.glb .pres-≤ {x} {y} x≤y =
      Meet.has-meet (s-meet y) .greatest _
        (S.≤-trans x-meet.meet≤l (a .pres-≤ x≤y))
        (S.≤-trans x-meet.meet≤r (b .pres-≤ x≤y))
      where module x-meet = is-meet (Meet.has-meet (s-meet x))
    Monotone-meets a b s-meet .Meet.has-meet .meet≤l x = Meet.has-meet (s-meet x) .meet≤l
    Monotone-meets a b s-meet .Meet.has-meet .meet≤r x = Meet.has-meet (s-meet x) .meet≤r
    Monotone-meets a b s-meet .Meet.has-meet .greatest c c≤a c≤b x =
      Meet.has-meet (s-meet x) .greatest (c · x) (c≤a x) (c≤b x)
  
    Monotone-joins : (a b : Monotone P S) → ((x : P.Ob) → Join S (a · x) (b · x)) → Join Poset[ P , S ] a b
    Monotone-joins a b s-join .Join.lub .hom x = Join.lub (s-join x)
    Monotone-joins a b s-join .Join.lub .pres-≤ {x} {y} x≤y =
      Join.has-join (s-join x) .least _
        (S.≤-trans (a .pres-≤ x≤y) y-join.l≤join)
        (S.≤-trans (b .pres-≤ x≤y) y-join.r≤join)
      where module y-join = is-join (Join.has-join (s-join y))
    Monotone-joins a b s-join .Join.has-join .l≤join x = Join.has-join (s-join x) .l≤join
    Monotone-joins a b s-join .Join.has-join .r≤join x = Join.has-join (s-join x) .r≤join
    Monotone-joins a b s-join .Join.has-join .least c c≤a c≤b x =
      Join.has-join (s-join x) .least (c · x) (c≤a x) (c≤b x)

  module _ where
    open is-glb
    open is-lub
  
    Monotone-complete
      : ∀ {ℓ'} {I : Type ℓ'} (F : I → Monotone P S)
      → ((x : P.Ob) → Glb S (λ i → F i · x))
      → Glb Poset[ P , S ] F
    Monotone-complete F s-glb .Glb.glb .hom x = Glb.glb (s-glb x)
    Monotone-complete F s-glb .Glb.glb .pres-≤ {x} {y} x≤y =
      Glb.has-glb (s-glb y) .greatest _ λ i →
        (S.≤-trans (x-glb.glb≤fam i) (F i .pres-≤ x≤y))
      where module x-glb = is-glb (Glb.has-glb (s-glb x))
    Monotone-complete F s-glb .Glb.has-glb .glb≤fam i x = Glb.has-glb (s-glb x) .glb≤fam i
    Monotone-complete F s-glb .Glb.has-glb .greatest c c≤ x =
      Glb.has-glb (s-glb x) .greatest (c · x) λ i → c≤ i x

    Monotone-cocomplete
      : ∀ {ℓ'} {I : Type ℓ'} (F : I → Monotone P S)
      → ((x : P.Ob) → Lub S (λ i → F i · x))
      → Lub Poset[ P , S ] F
    Monotone-cocomplete F s-lub .Lub.lub .hom x = Lub.lub (s-lub x)
    Monotone-cocomplete F s-lub .Lub.lub .pres-≤ {x} {y} x≤y =
      Lub.has-lub (s-lub x) .least _ λ i →
        (S.≤-trans (F i .pres-≤ x≤y) (y-lub.fam≤lub i))
      where module y-lub = is-lub (Lub.has-lub (s-lub y))
    Monotone-cocomplete F s-lub .Lub.has-lub .fam≤lub i x = Lub.has-lub (s-lub x) .fam≤lub i
    Monotone-cocomplete F s-lub .Lub.has-lub .least c c≤ x =
      Lub.has-lub (s-lub x) .least (c · x) λ i → c≤ i x
