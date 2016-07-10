module Util.Insert where

open import Data.Nat
open import Data.Fin
  hiding (_+_ ; pred)
open import Data.List
open import Function

insert : ∀ {A : Set}
         → (xs : List A)
         → (i : Fin (suc ∘ length $ xs))
         → (x : A)
         → List A
insert xs zero x = x ∷ xs
insert [] (suc ()) x
insert (x ∷ xs) (suc j) x₁ = x ∷ insert xs j x₁

module Proofs where
  open import Util.Membership

  open import Relation.Binary.PropositionalEquality

  -- a thing is where we inserted it
  insert-∈at : ∀ {A : Set}
               → (xs : List A)
               → (i : Fin (suc ∘ length $ xs))
               → (x : A)
               → x ∈ insert xs i x at (toℕ i)
  insert-∈at xs zero x
    = here
  insert-∈at [] (suc ()) x
  insert-∈at (x ∷ xs) (suc j) x₁
    = there (insert-∈at xs j x₁)

  -- if y is where we inserted x, then y is really x
  insert-∈at-eq : ∀ {A : Set} {x y}
                   → (xs : List A) → {i : Fin (suc ∘ length $ xs)}
                   → x ∈ insert xs i y at toℕ i
                   → x ≡ y
  insert-∈at-eq [] {zero} here
    = refl
  insert-∈at-eq [] {suc ()} x∈xs
  insert-∈at-eq (x₁ ∷ xs) {zero} here
    = refl
  insert-∈at-eq (x₁ ∷ xs) {suc i} (there x∈xs)
    = insert-∈at-eq xs x∈xs

  -- if we insert y in xs somewhere before x,
  -- then x's new place is 1 + the old place
  insert-∈at-before-inv : ∀ {A : Set} {x y k}
                          → (xs : List A) → {j : Fin (suc ∘ length $ xs)}
                          → x ∈ insert xs j y at suc (toℕ j + k)
                          → x ∈ xs at (toℕ j + k)
  insert-∈at-before-inv xs {zero} (there x∈ixs)
    = x∈ixs
  insert-∈at-before-inv [] {suc ()} x∈ixs
  insert-∈at-before-inv (x₁ ∷ xs) {suc j} (there x∈ixs)
    = there (insert-∈at-before-inv xs {j} x∈ixs)

  insert-∈at-before : ∀ {A : Set} {x y k}
                      → (xs : List A) → {j : Fin (suc ∘ length $ xs)}
                      → x ∈ xs at (toℕ j + k)
                      → x ∈ insert xs j y at suc (toℕ j + k)
  insert-∈at-before [] {zero} ()
  insert-∈at-before (x₁ ∷ xs) {zero} x∈xs
    = there x∈xs
  insert-∈at-before ._ {suc j} (there x∈xs)
    = there (insert-∈at-before _ {j} x∈xs)

  -- if we insert y in xs somewhere after x,
  -- then x is still in the same place
  insert-∈at-after-inv : ∀ {A : Set} {x y k l}
                         → (xs : List A) → {j : Fin (suc ∘ length $ xs)}
                         → x ∈ insert xs j y at k
                         → (toℕ j ≡ suc k + l)
                         → x ∈ xs at k
  insert-∈at-after-inv xs {zero} x∈xs ()
  insert-∈at-after-inv [] {suc ()} x∈xs j≡sk+l
  insert-∈at-after-inv (x ∷ xs) {suc j} here j≡sk+l
    = here
  insert-∈at-after-inv (x₁ ∷ xs) {suc j} (there x∈xs) j≡sk+l
    = there (insert-∈at-after-inv xs x∈xs (cong pred j≡sk+l))

  insert-∈at-after : ∀ {A : Set} {x y k l}
                     → (xs : List A) → {j : Fin (suc ∘ length $ xs)}
                     → x ∈ xs at k
                     → (toℕ j ≡ suc k + l)
                     → x ∈ insert xs j y at k
  insert-∈at-after xs {zero} x∈xs ()
  insert-∈at-after ._ {suc j} here j≡sk+l = here
  insert-∈at-after ._ {suc j} (there x∈xs) j≡sk+l
    = there (insert-∈at-after _ x∈xs (cong pred j≡sk+l))
