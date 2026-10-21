{-# OPTIONS --large-indices #-}
module Chapter4-Relations where
open import Chapter1-Agda
  using (Bool; false; true; not; _×_)
open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_)
open import Chapter3-Proofs

open import Agda.Primitive
  using (Level; _⊔_; lzero; lsuc)

private variable
  ℓ ℓ₁ ℓ₂ a b c : Level
  A : Set a
  B : Set b
  C : Set c

module Definition-DependentPair where
  open Chapter3-Proofs

  record Σ (A : Set ℓ₁) (B : A → Set ℓ₂)
      : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁

open import Data.Product
  using (Σ; _,_)

module Sandbox-Relations where
  REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
  REL A B ℓ = A → B → Set ℓ

  data _maps_↦_ (f : A → B) : REL A B lzero where
    app : {x : A} → f maps x ↦ f x
  _ : not maps true ↦ false
  _ = app

  Functional : REL A B ℓ → Set _
  Functional {A = A} {B = B} _~_ = {x : A} {y z : B} → x ~ y → x ~ z → y ≡ z

  Total : REL A B ℓ → Set _
  Total {A = A} {B = B} _~_ = (x : A) → Σ B (λ y → x ~ y)

  relToFn : (_~_ : REL A B ℓ) → Functional _~_ → Total _~_ → Σ (A → B) (λ f → ((x : A) → x ~ f x))
  relToFn _~_ ~Fun ~Tot =  (λ x → Σ.proj₁ (~Tot x)) , λ x → Σ.proj₂ (~Tot x)

  Rel : Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
  Rel A ℓ = REL A A ℓ

  Reflexive : Rel A ℓ → Set _
  Reflexive {A = A} _~_ = {x : A} → x ~ x

  Symmetric : Rel A ℓ → Set _
  Symmetric {A = A} _~_ = {x y : A} → x ~ y → y ~ x

  Transitive : Rel A ℓ → Set _
  Transitive {A = A} _~_ = {x y z : A} → x ~ y → y ~ z → x ~ z

open import Relation.Binary
  using (Rel; Reflexive; Symmetric; Transitive)

module Definition-LessThenOrEqualTo where
  data _≤_ : Rel ℕ lzero where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {n m : ℕ} → n ≤ m → suc n ≤ suc m
  infix 4 _≤_

  _ : 2 ≤ 5
  _ = s≤s (s≤s z≤n)

open import Data.Nat
  using (_≤_; z≤n; s≤s)

module Sandbox-≤ where

  suc-mono : {x y : ℕ} → x ≤ y → suc x ≤ suc y
  suc-mono x≤y = s≤s x≤y

  ≤-refl : Reflexive _≤_
  ≤-refl {zero} = z≤n
  ≤-refl {suc x} = s≤s ≤-refl

  ≤-trans : Transitive _≤_
  ≤-trans z≤n q = z≤n
  ≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

module Sandbox-Preorders where
  open Sandbox-≤

  record IsPreorder {A : Set a} (_~_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      refl : Reflexive _~_
      trans : Transitive _~_
  ≤-preorder : IsPreorder _≤_
  IsPreorder.refl ≤-preorder = ≤-refl
  IsPreorder.trans ≤-preorder = ≤-trans

  module Preorder-Reasoning
    {_~_ : Rel A ℓ} (~-preorder : IsPreorder _~_) where
    open IsPreorder ~-preorder public

    begin_ : {x y : A} → x ~ y → x ~ y
    begin x~y = x~y
    infix 1 begin_

    _∎ : (x : A) → x ~ x
    _∎ x = refl
    infix 3 _∎

    _≡⟨⟩_ : (x : A) → {y : A} → x ~ y → x ~ y
    x ≡⟨⟩ p = p
    infixr 2 _≡⟨⟩_

    _≈⟨_⟩_ : (x : A) → ∀ {y z} → x ~ y → y ~ z → x ~ z
    _ ≈⟨ x~y ⟩ y~z = trans x~y y~z
    infixr 2 _≈⟨_⟩_

    _≡⟨_⟩_ : (x : A) → ∀ {y z} → x ≡ y → y ~ z → x ~ z
    _ ≡⟨ PropEq.refl ⟩ y~z = y~z
    infixr 2 _≡⟨_⟩_

  module ≤-Reasoning where
    open Preorder-Reasoning ≤-preorder
      renaming (_≈⟨_⟩_ to _≤⟨_⟩_)
      public

  Antisymmetric : Rel A ℓ₁ → Rel A ℓ₂ → Set _
  Antisymmetric _≈_ _≤_ = ∀ {x y} → x ≤ y → y ≤ x → x ≈ y

  module _ {a ℓ : Level} {A : Set a} (_~_ : Rel A ℓ) where
    record IsEquivalence : Set (a ⊔ ℓ) where
      field
        isPreorder : IsPreorder _~_
        sym        : Symmetric  _~_
      open IsPreorder isPreorder public

    record IsPartialOrder : Set (a ⊔ ℓ) where
      field
        isPreorder : IsPreorder _~_
        antisym    : Antisymmetric _≡_ _~_
      open IsPreorder isPreorder public
    
  ≡-preorder : IsPreorder (_≡_ {A = A})
  ≡-preorder .IsPreorder.refl = PropEq.refl
  ≡-preorder .IsPreorder.trans = PropEq.trans

  ≡-equiv : IsEquivalence (_≡_ {A = A})
  ≡-equiv .IsEquivalence.isPreorder = ≡-preorder
  ≡-equiv .IsEquivalence.sym = PropEq.sym

  ≤-antisym : Antisymmetric _≡_ _≤_
  ≤-antisym {x} {y} z≤n z≤n = PropEq.refl
  ≤-antisym {x} {y} (s≤s p) (s≤s q) = PropEq.cong suc (≤-antisym p q)

  ≤-poset : IsPartialOrder _≤_
  ≤-poset .IsPartialOrder.isPreorder = ≤-preorder
  ≤-poset .IsPartialOrder.antisym = ≤-antisym

open import Agda.Primitive
  using (Level; _⊔_; lzero; lsuc)
  public

open import Data.Product
  using (Σ; _,_)
  public

open import Relation.Binary
  using (Rel; REL; Transitive; Reflexive; Symmetric; Antisymmetric)
  public

open import Data.Nat
  using (_≤_; z≤n; s≤s; _<_)
  public

open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-antisym; n≤1+n; module ≤-Reasoning)
  public

open Sandbox-Preorders
  using (IsPreorder; IsEquivalence; IsPartialOrder
        ; module Preorder-Reasoning
        ; ≡-preorder; ≡-equiv
        ; ≤-preorder; ≤-poset
        )
  public