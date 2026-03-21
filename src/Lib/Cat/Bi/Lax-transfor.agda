open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Bi.Solver
open import Cat.Functor.Base
open import Cat.Functor.Coherence hiding (_◆_)

import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr

module Lib.Cat.Bi.Lax-transfor
  {o h l o' h' l'} {B : Prebicategory o h l} {C : Prebicategory o' h' l'}
  where

private
  module B  = Prebicategory B
  module C  = Br C
  module CH = C.Hom

open Prebicategory C
open Pseudonatural
open Lax-transfor
open Cr.Inverses
open Cr._≅_
open _=>_

module _ {F : Lax-functor B C} where

  idlx : F =>ₗ F
  idlx .σ a              = id
  idlx .naturator        = (unitor-l .to ∘nt unitor-r .from) ◂ _
  idlx .ν-compositor f g = bicat! C
  idlx .ν-unitor         = bicat! C

  idpx : F =>ₚ F
  idpx .lax             = idlx
  idpx .naturator-inv f = CH.invertible-∘ (CH.inverses→invertible (C.λ≅ .inverses))
    (CH.is-invertible.op (CH.inverses→invertible (C.ρ≅ .inverses)))

module _ {F G H : Lax-functor B C} where
  private
    module F = Lax-functor F
    module G = Lax-functor G
    module H = Lax-functor H

  _∘lx_ : G =>ₗ H → F =>ₗ G → F =>ₗ H
  _∘lx_ α β = lx module ∘lx where
    private
      module α = Lax-transfor α
      module β = Lax-transfor β

    ν : ∀ {a b} → preaction C (α.σ b ⊗ β.σ b) F∘ H.P₁ => postaction C (α.σ a ⊗ β.σ a) F∘ F.P₁
    ν {a} {b} =
      (C.▶-assoc .from ◂ F.P₁) ∘nt
      nat-assoc-to (postaction C (α.σ a) ▸ β.naturator) ∘nt
      (nat-unassoc-to ⊙ nat-unassoc-from) (C.◀-▶-comm .to ◂ G.P₁) ∘nt
      nat-assoc-from (preaction C (β.σ b) ▸ α.naturator) ∘nt
      (C.◀-assoc .to ◂ H.P₁)
  
    lx : _ =>ₗ _
    lx .σ x                              = α.σ x ⊗ β.σ x
    lx .naturator                        = ν
    lx .ν-compositor {a = a} {b} {c} f g =
      ν .η (f B.⊗ g) ∘ H.γ→ _ ◀ (α.σ a ⊗ β.σ a)
        ≡⟨ bicat! C ⟩
        α← _ ∘ α.σ c ▶ β.ν→ (f B.⊗ g) ∘ α→ _
      ∘ ⌜ α.ν→ (f B.⊗ g) ∘ H.γ→ _ ◀ α.σ a ⌝ ◀ β.σ a ∘ α← _
        ≡⟨ ap! (α.ν-compositor f g) ⟩
        α← _ ∘ α.σ c ▶ β.ν→ (f B.⊗ g) ∘ α→ _ ∘ (α.σ c ▶ G.γ→ _ ∘ α→ _
      ∘ α.ν→ f ◀ G.₁ g ∘ α← _ ∘ H.₁ f ▶ α.ν→ g ∘ α→ _) ◀ β.σ a ∘ α← _
        ≡⟨ bicat! C ⟩
        α← _ ∘ α.σ c ▶ ⌜ β.ν→ (f B.⊗ g) ∘ G.γ→ _ ◀ β.σ a ⌝ ∘ α→ _ ∘ α→ _ ◀ β.σ a
      ∘ (α.ν→ f ◀ G.₁ g) ◀ β.σ a ∘ α← _ ◀ β.σ a ∘ (H.₁ f ▶ α.ν→ g) ◀ β.σ a
      ∘ α→ _ ◀ β.σ a ∘ α← _
        ≡⟨ ap! (β.ν-compositor f g) ⟩
      α← _ ∘ α.σ c ▶ (β.σ c ▶ F.γ→ _ ∘ α→ _ ∘ β.ν→ f ◀ F.₁ g ∘ α← _ ∘ G.₁ f ▶ β.ν→ g ∘ α→ _)
      ∘ α→ _ ∘ α→ _ ◀ β.σ a ∘ (α.ν→ f ◀ G.₁ g) ◀ β.σ a ∘ α← _ ◀ β.σ a
      ∘ (H.₁ f ▶ α.ν→ g) ◀ β.σ a ∘ α→ _ ◀ β.σ a ∘ α← _
        ≡⟨ bicat! C ⟩
      (α.σ c ⊗ β.σ c) ▶ F.γ→ _ ∘ α→ _ ∘ ν .η f ◀ F.₁ g ∘ α← _ ∘ H.₁ f ▶ ν .η g ∘ α→ _
        ∎
    lx .ν-unitor {a} =
      ν .η B.id ∘ H.υ→ ◀ _
        ≡⟨ bicat! C ⟩
      α← _ ∘ α.σ a ▶ β.ν→ _ ∘ α→ _ ∘ ⌜ α.ν→ _ ∘ H.υ→ ◀ α.σ a ⌝ ◀ β.σ a ∘ α← _
        ≡⟨ ap! α.ν-unitor ⟩
      α← _ ∘ α.σ a ▶ β.ν→ _ ∘ α→ _ ∘ (α.σ a ▶ G.υ→ ∘ ρ→ _ ∘ λ← _) ◀ β.σ a ∘ α← _
        ≡⟨ bicat! C ⟩
      α← _ ∘ α.σ a ▶ ⌜ β.ν→ _ ∘ G.υ→ ◀ β.σ a ⌝ ∘ α→ _ ∘ ρ→ _ ◀ β.σ a ∘ λ← _ ◀ β.σ a ∘ α← _
        ≡⟨ ap! β.ν-unitor ⟩
      α← _ ∘ α.σ a ▶ (β.σ a ▶ F.υ→ ∘ ρ→ _ ∘ λ← _) ∘ α→ _ ∘ ρ→ _ ◀ β.σ a ∘ λ← _ ◀ β.σ a ∘ α← _
        ≡⟨ bicat! C ⟩
      (α.σ a ⊗ β.σ a) ▶ F.υ→ ∘ ρ→ (α.σ a ⊗ β.σ a) ∘ λ← (α.σ a ⊗ β.σ a)
        ∎

  {-# DISPLAY ∘lx.lx f g = f ∘lx g #-}

  _∘px_ : G =>ₚ H → F =>ₚ G → F =>ₚ H
  _∘px_ α β .lax             = α .lax ∘lx β .lax
  _∘px_ α β .naturator-inv f = CH.invertible-∘
    (CH.is-invertible.op (CH.inverses→invertible (C.α≅ .inverses)))
    $ CH.invertible-∘ (C.▶.F-map-invertible (β .naturator-inv f))
    $ CH.invertible-∘ (CH.inverses→invertible (C.α≅ .inverses))
    $ CH.invertible-∘ (C.◀.F-map-invertible (α .naturator-inv f))
    $ CH.is-invertible.op (CH.inverses→invertible (C.α≅ .inverses))
