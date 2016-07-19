module Chapters.Ch06.Progress where

open import Util.Membership

open import Chapters.Ch04.Language
open import Chapters.Ch05.Dynamics.Val
open import Chapters.Ch05.Dynamics.Structural

open import Data.List
  hiding (_++_)
open import Data.Nat
open import Data.String
open import Data.Product
open import Data.Sum
  renaming (_⊎_ to _:+:_)

open import Relation.Binary.PropositionalEquality

cannonical-num : ∀ {Γ e}
                 → Val e
                 → Γ ⊢ e ∷ num
                 → Σ[ n ∈ ℕ ] e ≡ num[ n ]
cannonical-num num[ n ] num[ .n ] = n , refl
cannonical-num str[ s ] ()

cannonical-str : ∀ {Γ e}
                 → Val e
                 → Γ ⊢ e ∷ str
                 → Σ[ s ∈ String ] e ≡ str[ s ]
cannonical-str num[ n ] ()
cannonical-str str[ s ] str[ .s ] = s , refl

progress : ∀ {e τ}
           → [] ⊢ e ∷ τ
           → Val e :+: Σ[ e' ∈ Exp ] e ↦ₛ e'
progress (var ())
progress num[ n ] = inj₁ num[ n ]
progress str[ s ] = inj₁ str[ s ]
progress (plus ε₁ ε₂)
  with progress ε₁
progress (plus ε₁ ε₂)
  | inj₂ (e₁' , e₁↦e₁')
  = inj₂ (plus e₁' _ , (plusₗ e₁↦e₁'))
progress (plus ε₁ ε₂)
  | inj₁ e₁-val
  with progress ε₂
progress (plus ε₁ ε₂)
  | inj₁ e₁-val
  | inj₂ (e₂' , e₂↦e₂')
  = inj₂ (plus _ e₂' , (plusᵣ e₁-val e₂↦e₂'))
progress (plus ε₁ ε₂)
  | inj₁ e₁-val
  | inj₁ e₂-val
  with cannonical-num e₁-val ε₁
  | cannonical-num e₂-val ε₂
progress (plus ε₁ ε₂)
  | inj₁ e₁-val
  | inj₁ e₂-val
  | n , refl | m , refl
  = inj₂ (num[ n + m ] , plusᵥ)
progress (mult ε₁ ε₂)
  with progress ε₁
progress (mult ε₁ ε₂)
  | inj₂ (e₁' , e₁↦e₁')
  = inj₂ (mult e₁' _ , multₗ e₁↦e₁')
progress (mult ε₁ ε₂)
  | inj₁ e₁-val
  with progress ε₂
progress (mult ε₁ ε₂)
  | inj₁ e₁-val
  | inj₂ (e₂' , e₂↦e₂')
  = inj₂ (mult _ e₂' , multᵣ e₁-val e₂↦e₂')
progress (mult ε₁ ε₂)
  | inj₁ e₁-val
  | inj₁ e₂-val
  with cannonical-num e₁-val ε₁
  | cannonical-num e₂-val ε₂
progress (mult ε₁ ε₂)
  | inj₁ e₁-val
  | inj₁ e₂-val
  | n , refl | m , refl
  = inj₂ (num[ n * m ] , multᵥ)
progress (ccat ε₁ ε₂)
  with progress ε₁
progress (ccat ε₁ ε₂)
  | inj₂ (e₁' , e₁↦e₁')
  = inj₂ (ccat e₁' _ , ccatₗ e₁↦e₁')
progress (ccat ε₁ ε₂)
  | inj₁ e₁-val
  with progress ε₂
progress (ccat ε₁ ε₂)
  | inj₁ e₁-val
  | inj₂ (e₂' , e₂↦e₂')
  = inj₂ (ccat _ e₂' , ccatᵣ e₁-val e₂↦e₂')
progress (ccat ε₁ ε₂)
  | inj₁ e₁-val
  | inj₁ e₂-val
  with cannonical-str e₁-val ε₁
  | cannonical-str e₂-val ε₂
progress (ccat ε₁ ε₂)
  | inj₁ e₁-val
  | inj₁ e₂-val
  | s , refl | t , refl
  = inj₂ (str[ s ++ t ] , ccatᵥ)
progress (len ε)
  with progress ε
progress (len ε)
  | inj₂ (e' , e↦e')
  = inj₂ (len e' , (lenₑ e↦e'))
progress (len ε)
  | inj₁ e-val
  with cannonical-str e-val ε
progress (len ε)
  | inj₁ e-val
  | s , refl
  = inj₂ (_ , lenᵥ)
progress (lett ε ε₁)
  = inj₂ (_ , lettₑ)
