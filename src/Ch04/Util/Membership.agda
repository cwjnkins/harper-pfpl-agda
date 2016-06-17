module Util.Membership where

open import Data.Nat
open import Data.List

data _∈_at_ {A : Set} : A →  List A → ℕ → Set where
  here  : ∀ {x} {xs}
          → x ∈ (x ∷ xs) at 0
  there : ∀ {x y} {n} {xs}
          → x ∈ xs at n
          → x ∈ (y ∷ xs) at (suc n)

-- swap a thing in a list with the thing before it
∈at-swap : ∀ {A : Set} {i x}
           → (xs : List A)
           → x ∈ xs at (suc i)
           → List A
∈at-swap .(y ∷ x ∷ xs) (there .{x = x} {y} (here {x = x} {xs}))
  = x ∷ y ∷ xs
∈at-swap .(y ∷ y' ∷ _) (there {y = y} (there {y = y'} x∈xs))
  = y ∷ ∈at-swap (y' ∷ _) (there x∈xs)

module Proofs where
  open import Relation.Binary.PropositionalEquality
  -- two things in the same place in the same list
  -- are the same thing
  ∈at-same : ∀ {A : Set} {x y n} {xs : List A}
             → x ∈ xs at n
             → y ∈ xs at n
             → x ≡ y
  ∈at-same {n = zero} here here = refl
  ∈at-same {n = suc n} (there x∈xs) (there y∈xs) = ∈at-same x∈xs y∈xs

  module Swap where
    open import Data.Empty

    -- swap the thing in front of x and
    -- x is now in front of it
    ∈at-swap-i : ∀ {A : Set} {xs : List A} {x y i}
                  → (x∈xs : x ∈ xs at i)
                  → (y∈xs : y ∈ xs at (suc i))
                  → x ∈ (∈at-swap xs y∈xs) at suc i
    ∈at-swap-i here (there here)
      = there here
    ∈at-swap-i (there x∈xs) (there (there y∈xs))
      = there (∈at-swap-i x∈xs (there y∈xs))

    -- swap x and now x is one thing further behind
    ∈at-swap-si : ∀ {A : Set} {xs : List A} {x i}
                  → (x∈xs : x ∈ xs at suc i)
                  → x ∈ (∈at-swap xs x∈xs) at i
    ∈at-swap-si (there here)
      = here
    ∈at-swap-si (there (there x∈xs))
      = there (∈at-swap-si (there x∈xs))

    -- if you're not swapping x, it's in the same place as it was
    ∈at-swap-preserve : ∀ {A : Set} {xs : List A} {x y i j}
                        → (x∈xs : x ∈ xs at i)
                        → (y∈xs : y ∈ xs at (suc j))
                        → j ≢ i → (suc j) ≢ i
                        → x ∈ ∈at-swap xs y∈xs at i
    ∈at-swap-preserve here (there here) i≢j i≢sj
      = ⊥-elim (i≢j refl)
    ∈at-swap-preserve here (there (there y∈xs)) i≢j i≢sj
      = here
    ∈at-swap-preserve (there here) (there here) i≢j i≢sj
      = ⊥-elim (i≢sj refl)
    ∈at-swap-preserve (there (there x∈xs)) (there here) i≢j i≢sj
      = there (there x∈xs)
    ∈at-swap-preserve (there x∈xs) (there (there y∈xs)) i≢j i≢sj
      = there (
        ∈at-swap-preserve
          x∈xs (there y∈xs)
          (λ pi≡pj → i≢j  (cong suc pi≡pj))
          (λ pi≡j  → i≢sj (cong suc pi≡j ))
        )

    ∈at-swap-preserve₀ : ∀ {A : Set} {xs : List A} {x y i}
                         → (y∈xs : y ∈ xs at (suc i))
                         → ∈at-swap (x ∷ xs) (there y∈xs) ≡ (x ∷ ∈at-swap xs y∈xs)
    ∈at-swap-preserve₀ (there y∈xs) = refl
