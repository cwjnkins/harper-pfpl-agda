module Chapters.Ch04.Proofs.Swapping where

open import Chapters.Ch04.Language
open import Util.Membership
open Util.Membership.Proofs
open Util.Membership.Proofs.Swap

open import Data.Nat

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

swap : (i : ℕ) → (e : Exp) → Exp
swap i (var x)
  with i ≟ x
...
  | yes _ = var (suc i)
...
  | no  _
  with (suc i) ≟ x
...
  | yes _
  = var i
...
  | no  _
  = var x
swap i num[ n ]
  = num[ n ]
swap i str[ s ]
  = str[ s ]
swap i (plus e e₁)
  = plus (swap i e) (swap i e₁)
swap i (mult e e₁)
  = mult (swap i e) (swap i e₁)
swap i (ccat e e₁)
  = ccat (swap i e) (swap i e₁)
swap i (len e)
  = len (swap i e)
swap i (lett e e₁)
  = lett (swap i e) (swap (suc i) e₁)

swapping : ∀ {Γ i τ τ' e}
           → Γ ⊢ e ∷ τ
           → (τ'∈Γ : τ' ∈ Γ at (suc i))
           → (∈at-swap Γ τ'∈Γ) ⊢ swap i e ∷ τ
swapping {i = i} (var {x = x} x₁) τ'∈Γ
  with i ≟ x
swapping {i = i} (var x₁) τ'∈Γ
  | yes refl
  = var (∈at-swap-i x₁ τ'∈Γ)
swapping {i = i} (var {x = x} x₁) τ'∈Γ
  | no _
  with (suc i) ≟ x
swapping (var x₁) τ'∈Γ
  | no _  | yes refl
  with ∈at-same x₁ τ'∈Γ
swapping (var x₁) τ'∈Γ
  | no _  | yes refl | refl
  = var (∈at-swap-si τ'∈Γ)
swapping (var x₁) τ'∈Γ
  | no ¬p₁ | no ¬p₂
  = var (∈at-swap-preserve x₁ τ'∈Γ ¬p₁ ¬p₂)
swapping num[ n ] τ'∈Γ
  = num[ n ]
swapping str[ s ] τ'∈Γ
  = str[ s ]
swapping (plus ε ε₁) τ'∈Γ
  = plus (swapping ε τ'∈Γ) (swapping ε₁ τ'∈Γ)
swapping (mult ε ε₁) τ'∈Γ
  = mult (swapping ε τ'∈Γ) (swapping ε₁ τ'∈Γ)
swapping (ccat ε ε₁) τ'∈Γ
  = ccat (swapping ε τ'∈Γ) (swapping ε₁ τ'∈Γ)
swapping (len ε) τ'∈Γ
  = len (swapping ε τ'∈Γ)
swapping (lett {e₂ = e₂} {τ₁ = τ₁} ε₁ ε₂) τ'∈Γ
  with swapping ε₁ τ'∈Γ
  |    swapping ε₂ (there τ'∈Γ)
...
  | ε₁' | ε₂'
  with ∈at-swap (τ₁ ∷ _) (there τ'∈Γ) ≡ τ₁ ∷ ∈at-swap _ τ'∈Γ -- type annotation
       ∋ ∈at-swap-preserve₀ {x = τ₁} τ'∈Γ
    where
      open import Data.List using (_∷_)
      open import Function  using (_∋_)
...
  | eq
  with subst (λ Γ → Γ ⊢ swap (suc _) e₂ ∷ _) eq ε₂'
...
  | ε₂″
  = lett ε₁' ε₂″
