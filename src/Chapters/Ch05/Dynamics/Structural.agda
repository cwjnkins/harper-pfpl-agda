module Chapters.Ch05.Dynamics.Structural where

open import Chapters.Ch04.Language
open import Chapters.Ch04.Proofs.Substituting
open import Chapters.Ch05.Dynamics.Val

open import Data.Nat
open import Data.String
open import Data.List
  hiding (_++_)

open import Function

data _↦ₛ_ : (e₁ e₂ : Exp) → Set where
  plusᵥ : ∀ {n₁ n₂}
          → plus num[ n₁ ] num[ n₂ ] ↦ₛ num[ n₁ + n₂ ]
  plusₗ : ∀ {e₁ e₁' e₂}
          → e₁ ↦ₛ e₁'
          → plus e₁ e₂ ↦ₛ plus e₁' e₂
  plusᵣ : ∀ {e₁ e₂ e₂'}
          → Val e₁
          → e₂ ↦ₛ e₂'
          → plus e₁ e₂ ↦ₛ plus e₁ e₂'

  multᵥ : ∀ {n₁ n₂}
          → mult num[ n₁ ] num[ n₂ ] ↦ₛ num[ n₁ * n₂ ]
  multₗ : ∀ {e₁ e₁' e₂}
          → e₁ ↦ₛ e₁'
          → mult e₁ e₂ ↦ₛ mult e₁' e₂
  multᵣ : ∀ {e₁ e₂ e₂'}
          → Val e₁
          → e₂ ↦ₛ e₂'
          → mult e₁ e₂ ↦ₛ mult e₁ e₂'

  ccatᵥ : ∀ {s₁ s₂}
          → ccat str[ s₁ ] str[ s₂ ] ↦ₛ str[ s₁ ++ s₂ ]
  ccatₗ : ∀ {e₁ e₁' e₂}
          → e₁ ↦ₛ e₁'
          → ccat e₁ e₂ ↦ₛ ccat e₁' e₂
  ccatᵣ : ∀ {e₁ e₂ e₂'}
          → Val e₁
          → e₂ ↦ₛ e₂'
          → ccat e₁ e₂ ↦ₛ ccat e₁ e₂'

  lenᵥ : ∀ {s}
         → len str[ s ] ↦ₛ num[ length ∘ toList $ s ]
  lenₑ : ∀ {e e'}
         → e ↦ₛ e'
         → len e ↦ₛ len e'

  lettₑ : ∀ {e₁ e₂}
          → lett e₁ e₂ ↦ₛ ([ e₁ / 0 ] e₂)

private
  -- example differs from the one in the book,
  -- as there call by value was used, and here call by name
  example₁ : lett (plus num[ 1 ] num[ 2 ])
                 (plus (plus (var 0) num[ 3 ]) num[ 4 ])
            ↦ₛ
            plus (plus (plus num[ 1 ] num[ 2 ]) num[ 3 ]) num[ 4 ]
  example₁ = lettₑ

  example₂ : plus (plus (plus num[ 1 ] num[ 2 ]) num[ 3 ]) num[ 4 ]
             ↦ₛ
             plus (plus num[ 3 ] num[ 3 ]) num[ 4 ]
  example₂ = plusₗ (plusₗ plusᵥ)

  example₃ : plus (plus num[ 3 ] num[ 3 ]) num[ 4 ]
             ↦ₛ
             plus num[ 6 ] num[ 4 ]
  example₃ = plusₗ plusᵥ

  example₄ : plus num[ 6 ] num[ 4 ]
             ↦ₛ
             num[ 10 ]
  example₄ = plusᵥ
  
module Transition where
  open import Chapters.Ch05.TransitionSystem
  open TransitionSystem _↦ₛ_ public
