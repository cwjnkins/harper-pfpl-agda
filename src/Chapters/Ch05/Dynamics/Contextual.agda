module Chapters.Ch05.Dynamics.Contextual where

open import Chapters.Ch04.Language
open import Chapters.Ch04.Proofs.Substituting
open import Chapters.Ch05.Dynamics.Val

open import Data.List
  hiding (_++_)
open import Data.Nat
open import Data.String

open import Function

data _→ₑ_ : (e₁ e₂ : Exp) → Set where
  plus : ∀ {m n}
         → plus num[ m ] num[ n ] →ₑ num[ m + n ]
  mult : ∀ {m n}
         → mult num[ m ] num[ n ] →ₑ num[ m * n ]
  ccat : ∀ {s t}
         → ccat str[ s ] str[ t ] →ₑ str[ s ++ t ]
  len : ∀ {s}
        → len str[ s ] →ₑ num[ length ∘ toList $ s ]

  lett : ∀ {e₁ e₂}
         → lett e₁ e₂ →ₑ ([ e₁ / 0 ] e₂)

data Ectxt : Set where
  ∘ : Ectxt
  plusₗ plusᵣ multₗ multᵣ ccatₗ ccatᵣ :
    ∀ (e : Exp)
    → (E : Ectxt)
    → Ectxt
  len : (E : Ectxt) → Ectxt

data _≔_[_] : (e' : Exp) → (E : Ectxt) → (e : Exp) → Set where
  e-self : ∀ {e} → e ≔ ∘ [ e ]
  plusₗ  : ∀ {e₁ e₁' e₂ E}
           → e₁' ≔ E [ e₁ ]
           → plus e₁' e₂ ≔ plusₗ e₂ E [ e₁ ]
  plusᵣ  : ∀ {e₁ e₂ e₂' E}
           → Val e₁
           → e₂' ≔ E [ e₂ ]
           → plus e₁ e₂' ≔ plusᵣ e₁ E [ e₂ ]
  multₗ  : ∀ {e₁ e₁' e₂ E}
           → e₁' ≔ E [ e₁ ]
           → mult e₁' e₂ ≔ multₗ e₂ E [ e₁ ]
  multᵣ  : ∀ {e₁ e₂ e₂' E}
           → Val e₁
           → e₂' ≔ E [ e₂ ]
           → mult e₁ e₂' ≔ multᵣ e₁ E [ e₂ ]
  ccatₗ  : ∀ {e₁ e₁' e₂ E}
           → e₁' ≔ E [ e₁ ]
           → ccat e₁' e₂ ≔ ccatₗ e₂ E [ e₁ ]
  ccatᵣ  : ∀ {e₁ e₂ e₂' E}
           → Val e₁
           → e₂' ≔ E [ e₂ ]
           → ccat e₁ e₂' ≔ ccatᵣ e₁ E [ e₂ ]
  len : ∀ {e e' E}
        → e' ≔ E [ e ]
        → len e' ≔ len E [ e ]

-- ... finally
data _↦ₑ_ : (e₁ e₂ : Exp) → Set where
  intro↦ₑ : ∀ {e e' e₀ e₀' E}
            → e ≔ E [ e₀ ]
            → e₀ →ₑ e₀'
            → e' ≔ E [ e₀' ]
            -----------------
            → e ↦ₑ e'
  
