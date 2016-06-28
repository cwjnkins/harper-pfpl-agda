module Chapters.Ch05.Dynamics.Val where

open import Chapters.Ch04.Language

data Val : (e : Exp) → Set where
  num[_] : ∀ n → Val (num[ n ])
  str[_] : ∀ s → Val (str[ s ])

module Proofs where
  open import Data.Product
  Γ⊢val : ∀ {Γ e}
          → Val e
          → Σ[ τ ∈ Typ ] Γ ⊢ e ∷ τ
  Γ⊢val num[ n ] = num , num[ n ]
  Γ⊢val str[ s ] = str , str[ s ]

