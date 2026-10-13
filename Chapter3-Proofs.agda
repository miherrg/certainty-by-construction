module Chapter3-Proofs where

module Definition where
  data _≡_ {A : Set} : A → A → Set where
    refl : {x : A} → x ≡ x

  sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

  module ≡-Reasoning where
    _∎ : {A : Set} → (x : A) → x ≡ x
    x ∎ = refl

    infix 3 _∎

    _≡⟨⟩_ : {A : Set} {y : A} → (x : A) → x ≡ y → x ≡ y
    x ≡⟨⟩ p = p

    infixr 2 _≡⟨⟩_

    _≡⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
    x ≡⟨ p ⟩ q = trans p q

    infixr 2 _≡⟨_⟩_

    begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
    begin p = p
