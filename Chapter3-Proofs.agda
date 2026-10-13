module Chapter3-Proofs where

module Definition where
  data _≡_ {A : Set} : A → A → Set where
    refl : {x : A} → x ≡ x
