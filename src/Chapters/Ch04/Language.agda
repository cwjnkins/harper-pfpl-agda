module Chapters.Ch04.Language where

open import Util.Membership

open import Data.Nat
open import Data.String
open import Data.List

data Typ : Set where
  num str : Typ

data Exp : Set where
  var    : (x : ℕ) → Exp
  num[_] : (n : ℕ) → Exp
  str[_] : (s : String) → Exp
  plus mult ccat
         : (e₁ e₂ : Exp) → Exp
  len    : (e : Exp) → Exp
  lett   : (e₁ e₂ : Exp) → Exp

Cxt = List Typ

data _⊢_∷_ (Γ : Cxt) : (e : Exp) → (τ : Typ) → Set where
  var    : ∀ {x τ} → τ ∈ Γ at x → Γ ⊢ (var x) ∷ τ
  num[_] : ∀ n → Γ ⊢ num[ n ] ∷ num
  str[_] : ∀ s → Γ ⊢ str[ s ] ∷ str

  plus : ∀ {e₁ e₂}
         → (ε₁ : Γ ⊢ e₁ ∷ num) → (ε₂ : Γ ⊢ e₂ ∷ num)
         → Γ ⊢ plus e₁ e₂ ∷ num

  mult : ∀ {e₁ e₂}
         → (ε₁ : Γ ⊢ e₁ ∷ num) → (ε₂ : Γ ⊢ e₂ ∷ num)
         → Γ ⊢ mult e₁ e₂ ∷ num

  ccat : ∀ {e₁ e₂}
         → (ε₁ : Γ ⊢ e₁ ∷ str) → (ε₂ : Γ ⊢ e₂ ∷ str)
         → Γ ⊢ ccat e₁ e₂ ∷ str

  len : ∀ {e}
        → (ε : Γ ⊢ e ∷ str)
        → Γ ⊢ len e ∷ num

  lett : ∀ {e₁ e₂ : Exp} {τ₁ τ₂ : Typ}
         → (ε₁ : Γ ⊢ e₁ ∷ τ₁) → (ε₂ : (τ₁ ∷ Γ) ⊢ e₂ ∷ τ₂)
         → Γ ⊢ (lett e₁ e₂) ∷ τ₂
