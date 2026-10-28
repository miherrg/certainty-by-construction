{-# OPTIONS --large-indices #-}

module Chapter6-Decidability where
open import Chapter1-Agda
  using(Bool; true; false)

open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_)

open import Chapter3-Proofs
  using (_≡_; module PropEq; module ≡-Reasoning; suc-injective)
open PropEq

open import Chapter4-Relations
  using (Level; _⊔_; lsuc; Σ; _,_)

module Definition-Bottom where
  data ⊥ : Set where

  ⊥-elim : ⊥ → {A : Set} → A
  ⊥-elim ()

  ¬_ : {ℓ : Level} → Set ℓ → Set ℓ
  ¬_ P = P → ⊥
  infix 3 ¬_

  _≢_ : {A : Set} → A → A → Set
  x ≢ y = ¬ x ≡ y
  infix 4 _≢_

  ≢-sym : {A : Set} {x y : A} → x ≢ y → y ≢ x
  ≢-sym p q = p (sym q)

  Reflexive : {c ℓ : Level } {A : Set c} → (A → A → Set ℓ) → Set (ℓ ⊔ c)
  Reflexive {A = A} _≈_ = {x : A} → x ≈ x

  ¬≢-refl : ¬({A : Set} → Reflexive {A = A} _≢_)
  ¬≢-refl ¬≡-refl = ¬≡-refl {ℕ} {zero} refl

  Transitive : {c ℓ : Level} {A : Set c} → (A → A → Set ℓ) → Set (ℓ ⊔ c)
  Transitive {A = A} _∼_ = {x y z : A} → x ∼ y → y ∼ z → x ∼ z

  ¬≢-trans : ¬({A : Set} → Transitive {A = A} _≢_)
  ¬≢-trans ¬≡-trans = ¬≡-trans {ℕ} {0} {1} {0} (λ ()) (λ ()) refl 

open import Relation.Nullary
  using (¬_)

module Example-NoMonusLeftIdentity where
  open  Chapter2-Numbers using (_∸_)

  ¬∸-identityˡ : ¬(Σ ℕ (λ e → (x : ℕ) → e ∸ x ≡ x))
  ¬∸-identityˡ (e , e-id) 
    with e-id 0 | e-id 1
  ... | refl | ()

module Sandbox-Decidablity where
  data Dec {ℓ : Level} (P : Set ℓ) : Set ℓ where
    yes :   P → Dec P
    no  : ¬ P → Dec P

open import Relation.Nullary using (Dec; yes; no)

module Nat-Properties where
  
  _≟_ : (x y : ℕ) → Dec (x ≡ y)
  zero ≟ zero = yes refl
  zero ≟ suc y = no (λ ())
  suc x ≟ zero = no (λ ())
  suc x ≟ suc y with x ≟ y
  ... | yes refl = yes refl
  ... | no x≢y   = no λ { refl → x≢y refl }

  DecidableEquality : {ℓ : Level} (A : Set ℓ) → Set ℓ
  DecidableEquality A = (x y : A) → Dec (x ≡ y)

  _≟ℕ_ : DecidableEquality ℕ
  _≟ℕ_ = _≟_

  map-dec : {ℓ₁ ℓ₂ : Level} {P : Set ℓ₁} {Q : Set ℓ₂} → (P → Q) → (Q → P) → Dec P → Dec Q
  map-dec f g (yes p) = yes (f p)
  map-dec f g (no ¬p) = no (λ q → ¬p (g q))

open import Relation.Binary using (DecidableEquality)

module BinaryTrees where
  data BinTree {ℓ : Level} (A : Set ℓ) : Set ℓ where
    empty : BinTree A
    branch : BinTree A → A → BinTree A → BinTree A
  pattern leaf a = branch empty a empty

  private variable
    ℓ : Level
    A : Set ℓ
    a b : A
    l r : BinTree A

  data _∈_  : A → BinTree A → Set where
    node    : a         ∈ branch l a r
    left    : a ∈ l → a ∈ branch l b r
    right   : a ∈ r → a ∈ branch l b r

  Decidable : {c ℓ : Level} {A : Set c} → (A → Set ℓ) → Set (c ⊔ ℓ)
  Decidable {A = A} P = (a : A) → Dec (P a)

  Decidable₂ : {c ℓ : Level} {A : Set c} → (A → A → Set ℓ) → Set (c ⊔ ℓ)
  Decidable₂ {A = A} _~_ = (x y : A) → Dec (x ~ y)

  ∈? : DecidableEquality A → (t : BinTree A) → Decidable (_∈ t)
  ∈? _≟_ empty a = no (λ ())
  ∈? _≟_ (branch l x r) a 
    with x ≟ a  | ∈? _≟_ l a  | ∈? _≟_ r a
  ... | yes refl  | _           | _             = yes node
  ... | _         | yes p       | _             = yes (left p)
  ... | _         | _           | yes p         = yes (right p)
  ... | no p      | no pl       | no pr
      = no λ { node → p refl
             ; (left x) → pl x
             ; (right x) → pr x}
  
open import Data.Empty
  using (⊥; ⊥-elim)
  public

open import Relation.Nullary
  using (Dec; yes; no; ¬_)
  public

open import Relation.Unary
  using (Decidable)
  public

open import Relation.Binary.PropositionalEquality
  using (_≢_; ≢-sym)
  public

open import Relation.Binary
  using (Reflexive; Transitive; DecidableEquality)
  using (Trichotomous; Tri)
  renaming (Decidable to Decidable₂)
  public

open import Relation.Nullary.Decidable
  renaming (map′ to map-dec)
  public

open import Data.Nat.Properties
  using (<-cmp)
  public

open BinaryTrees
  using (BinTree; empty; branch; leaf)
  public

-- Técnicamente faltan cosas de árboles binarios de busqueda, pero no me importan una mierda lmao