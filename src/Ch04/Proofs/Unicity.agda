module Proofs.Unicity where

open import Syntax
open import Inference
open import Util.Membership
open Util.Membership.Proofs

open import Relation.Binary.PropositionalEquality

unicity : ∀ {Γ : Cxt} {e τ₁ τ₂}
          → (ε₁ : Γ ⊢ e ∷ τ₁) → (ε₂ : Γ ⊢ e ∷ τ₂)
          → τ₁ ≡ τ₂
unicity {e = var x} (var x₁) (var x₂)
  = ∈at-same x₁ x₂
unicity {e = num[ .n ]} num[ n ] num[ .n ]
  = refl
unicity {e = str[ .s ]} str[ s ] str[ .s ]
  = refl
unicity {e = plus e₂ e₁} (plus ε₂ ε₁) (plus ε₃ ε₄)
  = refl
unicity {e = mult e₂ e₁} (mult ε₂ ε₁) (mult ε₃ ε₄)
  = refl
unicity {e = ccat e₂ e₁} (ccat ε₂ ε₁) (ccat ε₃ ε₄)
  = refl
unicity {e = len e} (len ε₁) (len ε₂)
  = refl
unicity {e = lett e₂ e₁} (lett ε₁ ε₂) (lett ε₁' ε₂')
  with unicity ε₁ ε₁'
unicity {e = lett e₂ e₁} (lett ε₁ ε₂) (lett ε₁' ε₂')
  | refl
  = unicity ε₂ ε₂'
