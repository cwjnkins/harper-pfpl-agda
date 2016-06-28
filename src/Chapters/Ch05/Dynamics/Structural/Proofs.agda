module Chapters.Ch05.Dynamics.Structural.Proofs where

open import Chapters.Ch04.Language
open import Chapters.Ch05.Dynamics.Structural

open import Data.Empty

open import Relation.Binary.PropositionalEquality

finality : ∀ {e e'}
           → Val e
           → e ↦ₛ e'
           → ⊥
finality num[ n ] ()
finality str[ s ] ()

determinacy : ∀ {e e' e″}
              → e ↦ₛ e'
              → e ↦ₛ e″
              → e' ≡ e″
determinacy {var x}    () _
determinacy {num[ n ]} () _
determinacy {str[ s ]} () _

determinacy {plus ._ ._} plusᵥ plusᵥ
  = refl
determinacy {plus ._ ._} plusᵥ (plusₗ ())
determinacy {plus ._ ._} plusᵥ (plusᵣ x ())

determinacy {plus ._ ._} (plusₗ ()) plusᵥ
determinacy {plus e₂ e₁} (plusₗ e↦ₛe') (plusₗ e↦ₛe″)
  with determinacy e↦ₛe' e↦ₛe″
determinacy {plus e₂ e₁} (plusₗ e↦ₛe') (plusₗ e↦ₛe″)
  | refl
  = refl
determinacy {plus e₂ e₃} (plusₗ e↦ₛe') (plusᵣ x e↦ₛe″)
  = ⊥-elim (finality x e↦ₛe')

-- plus, mult, and ccat are all the same
determinacy {plus ._ ._} (plusᵣ x ())   plusᵥ
determinacy {plus e₁ e₂} (plusᵣ x e↦ₛe') (plusₗ e↦ₛe″)
  = ⊥-elim (finality x e↦ₛe″)
determinacy {plus e₁ e₂} (plusᵣ x e↦ₛe') (plusᵣ x₁ e↦ₛe″)
  with determinacy e↦ₛe' e↦ₛe″
determinacy {plus e₁ e₂} (plusᵣ x e↦ₛe') (plusᵣ x₁ e↦ₛe″)
  | refl
  = refl

determinacy {mult ._ ._} multᵥ multᵥ
  = refl
determinacy {mult ._ ._} multᵥ (multₗ ())
determinacy {mult ._ ._} multᵥ (multᵣ x ())

determinacy {mult ._ ._} (multₗ ()) multᵥ
determinacy {mult e₂ e₁} (multₗ e↦ₛe') (multₗ e↦ₛe″)
  with determinacy e↦ₛe' e↦ₛe″
determinacy {mult e₂ e₁} (multₗ e↦ₛe') (multₗ e↦ₛe″)
  | refl
  = refl
determinacy {mult e₂ e₃} (multₗ e↦ₛe') (multᵣ x e↦ₛe″)
  = ⊥-elim (finality x e↦ₛe')

determinacy {mult ._ ._} (multᵣ x ())   multᵥ
determinacy {mult e₁ e₂} (multᵣ x e↦ₛe') (multₗ e↦ₛe″)
  = ⊥-elim (finality x e↦ₛe″)
determinacy {mult e₁ e₂} (multᵣ x e↦ₛe') (multᵣ x₁ e↦ₛe″)
  with determinacy e↦ₛe' e↦ₛe″
determinacy {mult e₁ e₂} (multᵣ x e↦ₛe') (multᵣ x₁ e↦ₛe″)
  | refl
  = refl

determinacy {ccat ._ ._} ccatᵥ ccatᵥ
  = refl
determinacy {ccat ._ ._} ccatᵥ (ccatₗ ())
determinacy {ccat ._ ._} ccatᵥ (ccatᵣ x ())

determinacy {ccat ._ ._} (ccatₗ ()) ccatᵥ
determinacy {ccat e₂ e₁} (ccatₗ e↦ₛe') (ccatₗ e↦ₛe″)
  with determinacy e↦ₛe' e↦ₛe″
determinacy {ccat e₂ e₁} (ccatₗ e↦ₛe') (ccatₗ e↦ₛe″)
  | refl
  = refl
determinacy {ccat e₂ e₃} (ccatₗ e↦ₛe') (ccatᵣ x e↦ₛe″)
  = ⊥-elim (finality x e↦ₛe')

determinacy {ccat ._ ._} (ccatᵣ x ())   ccatᵥ
determinacy {ccat e₁ e₂} (ccatᵣ x e↦ₛe') (ccatₗ e↦ₛe″)
  = ⊥-elim (finality x e↦ₛe″)
determinacy {ccat e₁ e₂} (ccatᵣ x e↦ₛe') (ccatᵣ x₁ e↦ₛe″)
  with determinacy e↦ₛe' e↦ₛe″
determinacy {ccat e₁ e₂} (ccatᵣ x e↦ₛe') (ccatᵣ x₁ e↦ₛe″)
  | refl
  = refl

determinacy {len ._} lenᵥ lenᵥ
  = refl
determinacy {len ._} lenᵥ (lenₑ ())
determinacy {len ._} (lenₑ ()) lenᵥ
determinacy {len e} (lenₑ e↦ₛe') (lenₑ e↦ₛe″)
  with determinacy e↦ₛe' e↦ₛe″
determinacy {len e} (lenₑ e↦ₛe') (lenₑ e↦ₛe″)
  | refl
  = refl
determinacy {lett e e₁} lettₑ lettₑ
  = refl
