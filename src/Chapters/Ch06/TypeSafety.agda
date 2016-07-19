module Chapters.Ch06.TypeSafety where

open import Util.Insert
open import Util.Membership

open import Chapters.Ch04.Language
open import Chapters.Ch04.Proofs.Substituting
open import Chapters.Ch05.Dynamics.Structural
open import Chapters.Ch05.Dynamics.Val

open import Data.Nat
import Data.Fin as Fin
open import Data.List
open import Data.String as String

open import Function

preservation : ∀ {Γ e e' τ}
               → Γ ⊢ e ∷ τ
               → e ↦ₛ e'
               → Γ ⊢ e' ∷ τ
preservation (plus num[ n ] num[ n₁ ]) plusᵥ
  = num[ n + n₁ ]
preservation (plus ε₁ ε₂) (plusₗ e₁↦e₁')
  with preservation ε₁ e₁↦e₁'
...
  | ε₁'
  = plus ε₁' ε₂
preservation (plus ε₁ ε₂) (plusᵣ e₁-val e₂↦e₂')
  with preservation ε₂ e₂↦e₂'
...
  | ε₂'
  = plus ε₁ ε₂'
preservation (mult num[ n ] num[ n₁ ]) multᵥ
  = num[ n * n₁ ]
preservation (mult ε₁ ε₂) (multₗ e₁↦e₁')
  with preservation ε₁ e₁↦e₁'
...
  | ε₁'
  = mult ε₁' ε₂
preservation (mult ε₁ ε₂) (multᵣ e₁-val e₂↦e₂')
  with preservation ε₂ e₂↦e₂'
...
  | ε₂'
  = mult ε₁ ε₂'
preservation (ccat str[ s ] str[ s₁ ]) ccatᵥ
  = str[ s String.++ s₁ ]
preservation (ccat ε₁ ε₂) (ccatₗ e₁↦e₁')
  with preservation ε₁ e₁↦e₁'
...
  | ε₁'
  = ccat ε₁' ε₂
preservation (ccat ε₁ ε₂) (ccatᵣ e₁-val e₂↦e₂')
  with preservation ε₂ e₂↦e₂'
...
  | ε₂'
  = ccat ε₁ ε₂'
preservation (len str[ s ]) lenᵥ
  = num[ length ∘ toList $ s ]
preservation (len ε) (lenₑ e↦e')
  = len (preservation ε e↦e')
preservation (lett ε₁ ε₂) lettₑ
  = substituting {j = Fin.zero} ε₂ ε₁
