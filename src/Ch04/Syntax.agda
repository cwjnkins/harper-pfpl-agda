module Syntax where

open import Data.Nat
open import Data.String

data Typ : Set where
  num str : Typ

data Exp : Set where
  var    : (x : ℕ) → Exp
  num[_] : (n : ℕ) → Exp
  str[_] : (s : String) → Exp
  plus mult ccat : (e₁ e₂ : Exp) → Exp
  len    : (e : Exp) → Exp
  lett   : (e₁ : Exp) → (e₂ : Exp) → Exp
