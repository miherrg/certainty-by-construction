module Chapter5-Modular-Arithmetic where
open import Chapter1-Agda

open import Chapter2-Numbers

open import Chapter3-Proofs
open PropEq using (cong)

open import Chapter4-Relations

module Playground-Instances where
  open PropEq

  default : {ℓ : Level} {A : Set ℓ} → ⦃ a : A ⦄ → A
  default {ℓ} {A} ⦃ a ⦄ = a

  private instance
    find-z≤n : {n : ℕ} → 0 ≤ n
    find-z≤n = z≤n

    find-s≤s : {m n : ℕ} → ⦃ m ≤ n ⦄ → suc m ≤ suc n
    find-s≤s {m} {n} ⦃ p ⦄ = s≤s p

  _ : 10 ≤ 20
  _ = default

module Playground-Instances₂ where
  record HasDefault {ℓ : Level} (A : Set ℓ) : Set ℓ where
    constructor default-of
    field
      the-default : A
  
  default : {ℓ : Level} {A : Set ℓ} → ⦃ HasDefault A ⦄ → A
  default {ℓ} {A} ⦃ default-of the-default ⦄ = the-default

open IsEquivalence ⦃ ... ⦄ public
instance
  equiv-to-preorder : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {_~_ : Rel A ℓ₂} → ⦃ IsEquivalence _~_ ⦄ → IsPreorder _~_
  equiv-to-preorder = isPreorder

  ≡-is-equivalence = ≡-equiv

module ℕ/nℕ (n : ℕ) where

  record _≈_ (a b : ℕ) : Set where
    constructor ≈-mod
    field 
      x y : ℕ
      is-mod : a + x * n ≡ b + y * n
  infix 4 _≈_

  ≈-refl : Reflexive _≈_
  ≈-refl = ≈-mod 0 0 refl

  ≈-sym : Symmetric _≈_
  ≈-sym (≈-mod x y is-mod) = ≈-mod y x (sym is-mod)

  ≈-trans : Transitive _≈_
  ≈-trans {x} {y} {z} (≈-mod a b p) (≈-mod c d q) = ≈-mod (a + c) (b + d) (begin (
    x + (a + c) * n ≡⟨ cong (λ ϕ → x + ϕ) (*-distribʳ-+ n a c) ⟩
    x + (a * n + c * n) ≡⟨ sym (+-assoc x (a * n) (c * n)) ⟩
    x + a * n + c * n ≡⟨ cong (λ ϕ → ϕ + c * n) p ⟩
    y + b * n + c * n ≡⟨ +-assoc y (b * n) (c * n) ⟩
    y + (b * n + c * n) ≡⟨ cong (λ ϕ → y + ϕ) (+-comm (b * n) (c * n)) ⟩
    y + (c * n + b * n) ≡⟨ sym (+-assoc y (c * n) (b * n))  ⟩
    y + c * n + b * n ≡⟨ cong (λ ϕ → ϕ + b * n) q ⟩
    z + d * n + b * n ≡⟨ +-assoc z (d * n) (b * n) ⟩
    z + (d * n + b * n) ≡⟨ cong (λ ϕ → z + ϕ) (+-comm (d * n) (b * n)) ⟩
    z + (b * n + d * n) ≡⟨ cong (λ ϕ → z + ϕ) ( sym (*-distribʳ-+ n b d)) ⟩
    z + (b + d) * n ∎
    )) where open ≡-Reasoning

  ≈-preorder : IsPreorder _≈_
  ≈-preorder .IsPreorder.refl = ≈-refl
  ≈-preorder .IsPreorder.trans = ≈-trans

  ≈-equiv : IsEquivalence _≈_
  ≈-equiv .IsEquivalence.isPreorder = ≈-preorder
  ≈-equiv .IsEquivalence.sym = ≈-sym

  instance
    _ = ≈-equiv

  module Mod-Reasoning where
    open Preorder-Reasoning ≈-preorder
      hiding (refl; trans)
      public

  0≈n : 0 ≈ n
  0≈n = ≈-mod 1 0 refl

  suc-cong-mod : {a b : ℕ} → a ≈ b → suc a ≈ suc b
  suc-cong-mod (≈-mod x y is-mod) = ≈-mod x y (cong suc is-mod)

  +-zero-mod : (a b : ℕ) → a ≈ 0 → a + b ≈ b
  +-zero-mod a b (≈-mod x y is-mod) = ≈-mod x y (begin (
    a + b + x * n ≡⟨ cong (λ ϕ → ϕ + x * n) (+-comm a b) ⟩
    b + a + x * n ≡⟨ +-assoc b a (x * n) ⟩
    b + (a + x * n) ≡⟨ cong (λ ϕ → b + ϕ) is-mod ⟩
    b + y * n ∎
    )) where open ≡-Reasoning

  suc-injective-mod : {a b : ℕ} → suc a ≈ suc b → a ≈ b
  suc-injective-mod (≈-mod x y is-mod) = ≈-mod x y (suc-injective is-mod)

  +-cong₂-mod : {a b c d : ℕ} → a ≈ b → c ≈ d → a + c ≈ b + d
  +-cong₂-mod {zero} {b} {c} {d} a≈b c≈d = begin (
    c ≈⟨ c≈d ⟩
    d ≈⟨ sym (+-zero-mod b d (sym a≈b)) ⟩
    b + d ∎
    ) where open Mod-Reasoning
  +-cong₂-mod {suc a} {zero} {c} {d} a≈b c≈d = ≈-sym (begin (
    d ≈⟨ sym c≈d ⟩
    c ≈⟨ sym (+-zero-mod (suc a) c a≈b) ⟩
    suc a + c ∎
    )) where open Mod-Reasoning
  +-cong₂-mod {suc a} {suc b} {c} {d} a≈b c≈d = suc-cong-mod (+-cong₂-mod (suc-injective-mod a≈b) c≈d)
  
  *-zero-mod : (a b : ℕ) → b ≈ 0 → a * b ≈ 0
  *-zero-mod zero b p = refl
  *-zero-mod (suc a) b p = begin (
    b + a * b ≈⟨ +-zero-mod b (a * b) p ⟩
    a * b ≈⟨ *-zero-mod a b p ⟩
    0 ∎
    ) where open Mod-Reasoning

  *-cong₂-mod : {a b c d : ℕ} → a ≈ b → c ≈ d → a * c ≈ b * d
  *-cong₂-mod {zero} {b} {c} {d} pab pcd = sym (begin (
    b * d ≡⟨ *-comm b d ⟩
    d * b ≈⟨ *-zero-mod d b (sym pab) ⟩
    0 ∎
    )) where open Mod-Reasoning
  *-cong₂-mod {suc a} {zero} {c} {d} pab pcd = (begin (
    suc a * c ≡⟨ *-comm (suc a) c ⟩
    c * suc a ≈⟨ *-zero-mod c (suc a) pab ⟩
    0 ∎
    )) where open Mod-Reasoning
  *-cong₂-mod {suc a} {suc b} {c} {d} pab pcd = (begin (
    c + a * c ≈⟨ +-cong₂-mod pcd (*-cong₂-mod (suc-injective-mod pab) pcd) ⟩
    d + b * d ∎
    )) where open Mod-Reasoning