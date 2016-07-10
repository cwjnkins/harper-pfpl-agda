module Chapters.Ch04.Proofs.Substituting where

open import Util.Membership
open import Util.Insert
open Util.Insert.Proofs

open import Chapters.Ch04.Language
open import Chapters.Ch04.Proofs.Weakening

open import Data.List
open import Data.Nat
open import Data.Fin
  hiding (compare ; _+_)

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Function

syntax substitute j e eₛ = [ eₛ / j ] e
substitute : (i : ℕ) → (e eₛ : Exp) → Exp
substitute i (var x) eₛ
  with compare i x
substitute i (var .(suc (i + k))) eₛ
  | less .i k
  -- n₀, n₁, ... nᵢ₋₁, nᵢ, nᵢ₊₁, ..., nₓ ⇒
  -- n₀, n₁, ... nᵢ₋₁, nᵢ₊₁, ... nₓ
  = var (i + k)
substitute i (var .i) eₛ
  | equal .i
  = eₛ
substitute .(suc (x + k)) (var x) eₛ
  | greater .x k
  = var x
substitute i num[ n ] eₛ
  = num[ n ]
substitute i str[ s ] eₛ
  = str[ s ]
substitute i (plus e e₁) eₛ
  = plus (substitute i e eₛ) (substitute i e₁ eₛ)
substitute i (mult e e₁) eₛ
  = mult (substitute i e eₛ) (substitute i e₁ eₛ)
substitute i (ccat e e₁) eₛ
  = ccat (substitute i e eₛ) (substitute i e₁ eₛ)
substitute i (len e) eₛ
  = len (substitute i e eₛ)
substitute i (lett e e₁) eₛ
  = lett (substitute i e eₛ) (substitute (suc i) e₁ (weaken eₛ))

substituting : ∀ {Γ τ τₛ e eₛ} {j : Fin (suc ∘ length $ Γ)}
               → (insert Γ j τₛ) ⊢ e ∷ τ
               → Γ ⊢ eₛ ∷ τₛ
               → Γ ⊢ [ eₛ / toℕ j ] e ∷ τ
substituting {j = j} (var {x = x} x₁) εₛ
  with toℕ j
  | inspect toℕ j
...
  | j' | inspj
  with compare j' x
substituting {Γ} {j = j} (var x₁) εₛ
  -- var: less
  | m | Reveal_·_is_.[ eq ]
  | less .m k
  with subst (λ m' → _ ∈ insert Γ j _ at suc (m' + k))
             (sym eq) x₁
...
  | x₁'
  with insert-∈at-before-inv Γ {j} x₁'
...
  | x₁″
  with subst (λ m' → _ ∈ Γ at (m' + k))
             eq x₁″
...
  | x₁‴
  = var x₁‴
substituting {Γ} {j = j} (var x₁) εₛ
  -- var: equal
  | x | Reveal_·_is_.[ eq ]
  | equal .x
  with subst (λ m' → _ ∈ insert Γ j _ at m')
             (sym eq) x₁
...
  | x₁'
  with insert-∈at-eq Γ x₁'
  -- the type of eₛ (τₛ) has to be the same as
  -- the type indexed by x₁', since this is
  -- the var we're replacing
...
  | τ≡τₛ
  = subst (λ τ' → _ ⊢ _ ∷ τ') (sym τ≡τₛ) εₛ
substituting (var x₁) εₛ
  -- var: greater
  | .(suc (x + k)) | Reveal_·_is_.[ eq ]
  | greater x k
  = var (insert-∈at-after-inv _ x₁ eq)

substituting num[ n ] εₛ
  = num[ n ]
substituting str[ s ] εₛ
  = str[ s ]
substituting (plus ε ε₁) εₛ
  = plus (substituting ε εₛ) (substituting ε₁ εₛ)
substituting (mult ε ε₁) εₛ
  = mult (substituting ε εₛ) (substituting ε₁ εₛ)
substituting (ccat ε ε₁) εₛ
  = ccat (substituting ε εₛ) (substituting ε₁ εₛ)
substituting (len ε) εₛ
  = len (substituting ε εₛ)
substituting (lett ε ε₁) εₛ
  = lett (substituting ε εₛ) (substituting ε₁ (weakening εₛ))
