module Chapter3-Proofs where
open import Chapter1-Agda
open import Chapter2-Numbers

module Definition where
  data _≡_ {A : Set} : A → A → Set where
    refl : {x : A} → x ≡ x

  sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

  cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  module ≡-Reasoning where
    _∎ : {A : Set} → (x : A) → x ≡ x
    x ∎ = refl

    infix 3 _∎

    _≡⟨⟩_ : {A : Set} {y : A} → (x : A) → x ≡ y → x ≡ y
    x ≡⟨⟩ p = p

    infixr 2 _≡⟨⟩_

    _≡⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
    x ≡⟨ p ⟩ q = trans p q

    infixr 2 _≡⟨_⟩_

    begin_ : {A : Set} → {x y : A} → (x ≡ y) → (x ≡ y)
    begin p = p

  ∨-assoc : (a b c : Bool) → ((a ∨ b) ∨ c) ≡ (a ∨ (b ∨ c))
  ∨-assoc false b c = refl
  ∨-assoc true b c = refl

  +-assoc : (a b c : ℕ) → ((a + b) + c) ≡ (a + (b + c))
  +-assoc zero b c = refl
  +-assoc (suc a) b c = begin (
    suc a + b + c ≡⟨ cong suc (+-assoc a b c) ⟩ 
    suc a + (b + c) ∎
    ) where open ≡-Reasoning

  +-suc : (x y : ℕ) → (x + (suc y)) ≡ (suc (x + y))
  +-suc zero y = refl
  +-suc (suc x) y = cong suc (+-suc x y)

  +-identityʳ : (x : ℕ) → (x + 0) ≡ x
  +-identityʳ zero = refl
  +-identityʳ (suc x) = cong suc (+-identityʳ x)

  +-comm : (x y : ℕ) → (x + y) ≡ (y + x)
  +-comm zero y = sym (+-identityʳ y)
  +-comm (suc x) y = begin (
    suc (x + y) ≡⟨ cong suc (+-comm x y) ⟩
    suc (y + x) ≡⟨ sym (+-suc y x) ⟩
    y + suc x ∎
    ) where open ≡-Reasoning
   
  suc-injective : {x y : ℕ} → suc x ≡ suc y → x ≡ y
  suc-injective refl = refl

  *-suc : (x y : ℕ) → (x * (suc y)) ≡ (x + x * y)
  *-suc zero y = refl
  *-suc (suc x) y = begin (
    suc x * suc y ≡⟨⟩
    suc (y + x * suc y) ≡⟨ cong (λ ϕ → suc y + ϕ) (*-suc x y) ⟩
    suc y + (x + x * y) ≡⟨ cong suc (sym (+-assoc y x (x * y))) ⟩
    suc (y + x + x * y) ≡⟨ cong (λ ϕ → (suc ϕ) + x * y) (+-comm y x) ⟩
    suc (x + y + x * y) ≡⟨ cong suc (+-assoc x y (x * y)) ⟩
    suc (x + (y + x * y)) ≡⟨⟩
    suc x + suc x * y ∎
    ) where open ≡-Reasoning

  *-zeroʳ : (x : ℕ) → (x * 0) ≡ 0
  *-zeroʳ zero = refl
  *-zeroʳ (suc x) = *-zeroʳ x

  *-comm : (x y : ℕ) → (x * y) ≡ (y * x)
  *-comm zero y = sym (*-zeroʳ y)
  *-comm (suc x) y = sym (begin (
    y * suc x ≡⟨ *-suc y x ⟩
    y + y * x ≡⟨ cong (λ ϕ → y + ϕ) (*-comm y x) ⟩
    y + x * y ≡⟨⟩
    suc x * y ∎
    )) where open ≡-Reasoning

open import Relation.Binary.PropositionalEquality
  using (_≡_; module ≡-Reasoning)
  public

module PropEq where
  open Relation.Binary.PropositionalEquality
    using (refl; cong; sym; trans)
    public
open import Data.Bool
  using (if_then_else_)
  public
open import Function
  using (case_of_)
  public
open import Data.Bool.Properties
  using ( ∨-identityˡ ; ∨-identityʳ
        ; ∨-zeroˡ
        ; ∨-zeroʳ
        ; ∨-assoc
        ; ∧-assoc
        ; ∧-identityˡ ; ∧-identityʳ
        ; ∧-zeroˡ
        ; ∧-zeroʳ
        ; not-involutive
        )
  public
open import Data.Nat.Properties
  using ( +-identityˡ ; +-identityʳ
        ; *-identityˡ ; *-identityʳ
        ; *-zeroˡ
        ; *-zeroʳ
        ; +-assoc
        ; *-assoc
        ; +-comm
        ; *-comm
        ; ^-identityʳ
        ; +-suc
        ; suc-injective
        ; *-distribˡ-+ ; *-distribʳ-+
        )
  public
