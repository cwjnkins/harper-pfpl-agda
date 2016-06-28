module Chapters.Ch05.Dynamics.Contextual.Proofs where

open import Chapters.Ch04.Language
open import Chapters.Ch04.Proofs.Substituting
open import Chapters.Ch05.Dynamics.Val
open import Chapters.Ch05.Dynamics.Structural
open import Chapters.Ch05.Dynamics.Contextual

open import Data.Nat

cxt-str-isoₗ : ∀ {e₁ e₂}
               → e₁ ↦ₛ e₂
               → e₁ ↦ₑ e₂
-- you need only examine the three cases for plus,
-- the others are basically the same and lett is trivial
cxt-str-isoₗ plusᵥ
  = intro↦ₑ e-self plus e-self
cxt-str-isoₗ (plusₗ e₁ₛ↦ₛe₁')
  with cxt-str-isoₗ e₁ₛ↦ₛe₁'
cxt-str-isoₗ (plusₗ e₁ₛ↦ₛe₁')
  | intro↦ₑ e₁≔E[e₉'] e₀→ₑe₉' e₁'≔E[e₀']
  = intro↦ₑ (plusₗ e₁≔E[e₉']) e₀→ₑe₉' (plusₗ e₁'≔E[e₀'])
cxt-str-isoₗ (plusᵣ e₁-val e₂ₛ↦ₛe₂')
  with cxt-str-isoₗ e₂ₛ↦ₛe₂'
cxt-str-isoₗ (plusᵣ e₁-val e₂ₛ↦ₛe₂')
  | intro↦ₑ e₂≔E[e₀] e₀→ₑe₀' e₂'≔E[e₀]
  = intro↦ₑ (plusᵣ e₁-val e₂≔E[e₀]) e₀→ₑe₀' (plusᵣ e₁-val e₂'≔E[e₀])

-- go ahead and skip to lett if you made it this far...
cxt-str-isoₗ multᵥ
  = intro↦ₑ e-self mult e-self
cxt-str-isoₗ (multₗ e₁ₛ↦ₛe₂)
  with cxt-str-isoₗ e₁ₛ↦ₛe₂
cxt-str-isoₗ (multₗ e₁ₛ↦ₛe₂)
  | intro↦ₑ e₂≔E[e₀] e₀→ₑe₀' e₂'≔E[e₀]
  = intro↦ₑ (multₗ e₂≔E[e₀]) e₀→ₑe₀' (multₗ e₂'≔E[e₀])
cxt-str-isoₗ (multᵣ e₁-val e₂ₛ↦ₛe₂')
  with cxt-str-isoₗ e₂ₛ↦ₛe₂'
...
  | intro↦ₑ e₂≔E[e₀] e₀→ₑe₀' e₂'≔E[e₀]
  = intro↦ₑ (multᵣ e₁-val e₂≔E[e₀]) e₀→ₑe₀' (multᵣ e₁-val e₂'≔E[e₀])

cxt-str-isoₗ ccatᵥ
  = intro↦ₑ e-self ccat e-self
cxt-str-isoₗ (ccatₗ e₁ₛ↦ₛe₁')
  with cxt-str-isoₗ e₁ₛ↦ₛe₁'
...
  | intro↦ₑ e₁≔E[e₉'] e₀→ₑe₉' e₁'≔E[e₀']
  = intro↦ₑ (ccatₗ e₁≔E[e₉']) e₀→ₑe₉' (ccatₗ e₁'≔E[e₀'])
cxt-str-isoₗ (ccatᵣ e₁-val e₂ₛ↦ₛe₂')
  with cxt-str-isoₗ e₂ₛ↦ₛe₂'
...
  | intro↦ₑ e₂≔E[e₀] e₀→ₑe₀' e₂'≔E[e₀]
  = intro↦ₑ (ccatᵣ e₁-val e₂≔E[e₀]) e₀→ₑe₀' (ccatᵣ e₁-val e₂'≔E[e₀])

cxt-str-isoₗ lenᵥ
  = intro↦ₑ e-self len e-self

cxt-str-isoₗ (lenₑ e↦ₛe')
  with cxt-str-isoₗ e↦ₛe'
cxt-str-isoₗ (lenₑ e↦ₛe')
  | intro↦ₑ e≔E[e₀] e₀→ₑe₀' e'≔E[e₀']
  = intro↦ₑ (len e≔E[e₀]) e₀→ₑe₀' (len e'≔E[e₀'])

-- only the trivial evaluation context needed here
cxt-str-isoₗ lettₑ
  = intro↦ₑ e-self lett e-self

cxt-str-isoᵣ : ∀ {e₁ e₂}
               → e₁ ↦ₑ e₂
               → e₁ ↦ₛ e₂
-- trivial value cases
cxt-str-isoᵣ (intro↦ₑ e-self plus e-self)
  = plusᵥ
cxt-str-isoᵣ (intro↦ₑ e-self mult e-self)
  = multᵥ
cxt-str-isoᵣ (intro↦ₑ e-self ccat e-self)
  = ccatᵥ
cxt-str-isoᵣ (intro↦ₑ e-self len e-self)
  = lenᵥ
cxt-str-isoᵣ (intro↦ₑ e-self lett e-self)
  = lettₑ

-- again, only really need to read the plus case
-- to understand the rest
cxt-str-isoᵣ (intro↦ₑ (plusₗ e₁'≔E[e₀]) e₀→ₑe₀' (plusₗ e₁″≔E[e₀']))
  = plusₗ (cxt-str-isoᵣ (intro↦ₑ e₁'≔E[e₀] e₀→ₑe₀' e₁″≔E[e₀']))
cxt-str-isoᵣ (intro↦ₑ (plusᵣ e₁-val e₂'≔E[e₀]) e₀→ₑe₀' (plusᵣ _ e₂″≔E[e₀']))
  = plusᵣ e₁-val (cxt-str-isoᵣ (intro↦ₑ e₂'≔E[e₀] e₀→ₑe₀' e₂″≔E[e₀']))

cxt-str-isoᵣ (intro↦ₑ (multₗ e₁'≔E[e₀]) e₀→ₑe₀' (multₗ e₁″≔E[e₀']))
  = multₗ (cxt-str-isoᵣ (intro↦ₑ e₁'≔E[e₀] e₀→ₑe₀' e₁″≔E[e₀']))
cxt-str-isoᵣ (intro↦ₑ (multᵣ e₁-val e₂'≔E[e₀]) e₀→ₑe₀' (multᵣ _ e₂″≔E[e₀']))
  = multᵣ e₁-val (cxt-str-isoᵣ (intro↦ₑ e₂'≔E[e₀] e₀→ₑe₀' e₂″≔E[e₀']))

cxt-str-isoᵣ (intro↦ₑ (ccatₗ e₁'≔E[e₀]) e₀→ₑe₀' (ccatₗ e₁″≔E[e₀']))
  = ccatₗ (cxt-str-isoᵣ (intro↦ₑ e₁'≔E[e₀] e₀→ₑe₀' e₁″≔E[e₀']))
cxt-str-isoᵣ (intro↦ₑ (ccatᵣ e₁-val e₂'≔E[e₀]) e₀→ₑe₀' (ccatᵣ _ e₂″≔E[e₀']))
  = ccatᵣ e₁-val (cxt-str-isoᵣ (intro↦ₑ e₂'≔E[e₀] e₀→ₑe₀' e₂″≔E[e₀']))

cxt-str-isoᵣ (intro↦ₑ (len e₁'≔E[e₀]) e₀→ₑe₀' (len e₁″≔E[e₀']))
  = lenₑ (cxt-str-isoᵣ (intro↦ₑ e₁'≔E[e₀] e₀→ₑe₀' e₁″≔E[e₀']))
