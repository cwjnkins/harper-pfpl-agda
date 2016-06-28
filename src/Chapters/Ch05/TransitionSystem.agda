module Chapters.Ch05.TransitionSystem where

open import Data.Nat

module TransitionSystem
  {S : Set}
  (_↦_ : (s₁ s₂ : S) → Set)
  where

  data _↦*_ : (s₁ s₂ : S) → Set where
    refl  : ∀ s
            --------
            → s ↦* s

    trans : ∀ {s s' s″}
            → s  ↦  s'
            → s' ↦* s″
            ----------------
            → s ↦* s″

  data _↦*_^_ : (s₁ s₂ : S) → (n : ℕ) → Set where
    refl : ∀ s
           ------------
           → s ↦* s ^ 0

    trans : ∀ {s s' s″ n}
            → s  ↦ s'
            → s' ↦* s″ ^ n
            → s  ↦* s″ ^ (suc n)


  module Proofs where
    open import Data.Product

    isoₗ : ∀ {s₁ s₂}
           → s₁ ↦* s₂
           → Σ[ k ∈ ℕ ] s₁ ↦* s₂ ^ k
    isoₗ (refl s₁) = 0 , refl s₁
    isoₗ (trans s₁↦s' s₁↦*s₂)
      with isoₗ s₁↦*s₂
    isoₗ (trans s₁↦s' s₁↦*s₂)
      | k , s₁↦*s₂^k
      = (suc k) , trans s₁↦s' s₁↦*s₂^k

    isoᵣ : ∀ {s₁ s₂}
           → Σ[ k ∈ ℕ ] s₁ ↦* s₂ ^ k -- so the types line up
           → s₁ ↦* s₂
    isoᵣ (.0 , refl s₁) = refl s₁
    isoᵣ (._ , trans s₁↦s' s₁↦*s₂^k) = trans s₁↦s' (isoᵣ (_ , s₁↦*s₂^k))
