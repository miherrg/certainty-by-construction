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