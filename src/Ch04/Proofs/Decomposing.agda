module Proofs.Decomposing where

open import Syntax
open import Inference
open import Proofs.Substituting
open import Proofs.Unicity
open import Proofs.Weakening
open import Util.Insert
open Util.Insert.Proofs
open import Util.Membership

open import Data.Fin
  hiding (compare ; _+_)
open import Data.List
open import Data.Nat

open import Relation.Binary.PropositionalEquality

decomposing : ∀ {Γ τ τₛ e eₛ} {j : Fin (length Γ)}
              → Γ ⊢ [ eₛ / toℕ j ] e ∷ τ
              → Γ ⊢ eₛ ∷ τₛ
              → (insert Γ j τₛ) ⊢ e ∷ τ
decomposing {e = var x} {j = j} ε εₛ
  with j
  -- make j visible as j', because reasons
...
  | j'
  with toℕ j'
  |    inspect toℕ j'
...
  | m | insp
  with compare m x
decomposing {Γ} {τ} {τₛ} {var .(suc (m + k))} (var x) εₛ
  | j'
  | m | Reveal_·_is_.[ eq ]
  | less .m k
  with subst (λ m' → τ ∈ Γ at (m' + k)) (sym eq) x
  -- rewrite the type of x so that the location τₛ was inserted
  -- and the location of its type in Γ
  -- are both in terms to j'
...
  | x'
  with insert-∈at-before {y = τₛ} Γ {j'} x'
  -- find out where x's type is in Γ after inserting τₛ
...
  | x″
  = var (
      subst
        (λ m' → τ ∈ insert Γ j' τₛ at suc (m' + k))
        eq x″
    )
  -- and rewrite x's location in Γ back to a term of m
decomposing {Γ} {τ} {τₛ} {var .m} ε εₛ
  | j'
  | m | Reveal_·_is_.[ eq ]
  | equal .m
  with unicity ε εₛ
  -- ε and εₛ now both share Exp eₛ, but appear to have different types
...
  | τ≡τₛ
  with insert-∈at Γ j' τ
  -- τ is where we insert it, j
...
  | x∈iΓ
  with subst (λ τ' → τ ∈ insert Γ j' τ' at toℕ j') τ≡τₛ x∈iΓ
  -- rewrite τ to be where we insert τₛ, j
...
  | x∈iΓ'
  with subst (λ m' → τ ∈ insert Γ j' τₛ at m') eq x∈iΓ'
  -- rewrite the location of τ to be m
...
  | x∈iΓ″
  = var x∈iΓ″
decomposing {Γ} {τ} {τₛ} {var .x} (var x₁) εₛ
  | j'
  | .(suc (x + k)) | Reveal_·_is_.[ eq ]
  | greater x k
  = var (insert-∈at-after Γ x₁ eq)
decomposing {e = num[ .n ]} num[ n ] εₛ
  = num[ n ]
decomposing {e = str[ .s ]} str[ s ] εₛ
  = str[ s ]
decomposing {e = plus e e₁} (plus ε ε₁) εₛ
  = plus (decomposing ε εₛ) (decomposing ε₁ εₛ)
decomposing {e = mult e e₁} (mult ε ε₁) εₛ
  = mult (decomposing ε εₛ) (decomposing ε₁ εₛ)
decomposing {e = ccat e e₁} (ccat ε ε₁) εₛ
  = ccat (decomposing ε εₛ) (decomposing ε₁ εₛ)
decomposing {e = len e} (len ε) εₛ
  = len (decomposing ε εₛ)
decomposing {e = lett e e₁} (lett ε ε₁) εₛ
  = lett (decomposing ε εₛ) (decomposing ε₁ (weakening εₛ))
