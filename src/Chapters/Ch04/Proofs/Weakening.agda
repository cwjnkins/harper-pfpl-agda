module Chapters.Ch04.Proofs.Weakening where

open import Chapters.Ch04.Language

open import Util.Membership
open import Chapters.Ch04.Proofs.Swapping

open import Data.Nat
open import Data.List

weaken : Exp → Exp
weaken (var x)
  = var (suc x)
weaken num[ n ]
  = num[ n ]
weaken str[ s ]
  = str[ s ]
weaken (plus e₁ e₂)
  = plus (weaken e₁) (weaken e₂)
weaken (mult e₁ e₂)
  = mult (weaken e₁) (weaken e₂)
weaken (ccat e₁ e₂)
  = ccat (weaken e₁) (weaken e₂)
weaken (len e)
  = len (weaken e)
weaken (lett e₁ e₂) = lett (weaken e₁) (swap 0 (weaken e₂))

weakening : ∀ {Γ e τ τ'}
            → (ε : Γ ⊢ e ∷ τ)
            → (τ' ∷ Γ) ⊢ weaken e ∷ τ
weakening (var x₁)
  = var (there x₁)
weakening num[ n ]
  = num[ n ]
weakening str[ s ]
  = str[ s ]
weakening (plus ε₁ ε₂)
  = plus (weakening ε₁) (weakening ε₂)
weakening (mult ε₁ ε₂)
  = mult (weakening ε₁) (weakening ε₂)
weakening (ccat ε₁ ε₂)
  = ccat (weakening ε₁) (weakening ε₂)
weakening (len ε)
  = len (weakening ε)
weakening {τ' = τ'} (lett ε₁ ε₂)
  with weakening {τ' = τ'} ε₁
  |    weakening {τ' = τ'} ε₂
...
  | ε₁' | ε₂'
  = lett ε₁' (swapping ε₂' (there here))
