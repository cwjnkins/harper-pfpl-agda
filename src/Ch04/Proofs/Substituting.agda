module Proofs.Substituting where

open import Syntax
open import Inference

open import Data.List
open import Data.Nat
open import Data.Fin
  hiding (compare ; _+_)

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Function

open import Util.Membership
open import Util.Insert
open Util.Insert.Proofs

open import Proofs.Weakening

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

substituting : ∀ {Γ τ τₛ e eₛ} {j : Fin (length Γ)}
               → (insert Γ j τₛ) ⊢ e ∷ τ
               → Γ ⊢ eₛ ∷ τₛ
               → Γ ⊢ [ eₛ / toℕ j ] e ∷ τ
substituting {[]} {j = ()} (var x₁) εₛ
substituting {x ∷ Γ} {j = j} (var {x = x₁} x₂) εₛ
  with toℕ j
  | inspect toℕ j
...
  | j' | inspj
  with compare j' x₁
substituting {x ∷ Γ} {j = j} (var x₂) εₛ
  | m | Reveal_·_is_.[ eq ]
  | less .m k
  with subst
         (λ m' → _ ∈ insert (x ∷ Γ) j _ at suc (m' + k))
         (sym eq) x₂
...
  | x₂'
  with insert-∈at-before-inv (x ∷ Γ) {j} x₂'
  -- remove the insert subexpr from the type of x₂' 
...
  | x₂″
  with subst
    (λ m' → _ ∈ x ∷ Γ at (m' + k))
    eq x₂″
...
  | x₂‴
  = var x₂‴
substituting {x₁ ∷ Γ} {j = j} (var x₂) εₛ
  | x | Reveal_·_is_.[ eq ]
  | equal .x
  with subst
         (λ m' → _ ∈ insert (x₁ ∷ Γ) j _ at m')
         (sym eq) x₂
...
  | x₂'
  with insert-∈at-eq (x₁ ∷ Γ) x₂'
  -- the type of eₛ has to be the same as
  -- the type indexed by x₂'
...
  | τ'≡τₛ
  = subst (λ τ' → _ ⊢ _ ∷ τ') (sym τ'≡τₛ) εₛ
substituting {x₁ ∷ Γ} (var x₂) εₛ
  | .(suc (x + k)) | Reveal_·_is_.[ eq ]
  | greater x k
  = var (insert-∈at-after-inv (x₁ ∷ Γ) x₂ eq)
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
