{-# OPTIONS --large-indices #-}

module Chapter7-Structures where

open import Chapter1-Agda

open import Chapter2-Numbers

open import Chapter3-Proofs
  renaming (module PropEq to ≡)

open import Chapter4-Relations

open import Chapter5-Modular-Arithmetic
  using (equiv-to-preorder; ≡-is-equivalence; refl; sym
        ; trans)

open import Chapter6-Decidability
  using (¬_; ⊥)
open Chapter6-Decidability.BinaryTrees
  using (BinTree; leaf; branch; empty)

private variable
  ℓ ℓ₁ ℓ₂ : Level
  A B C : Set ℓ

private
  Op₂ : {ℓ : Level} → Set ℓ → Set ℓ
  Op₂ A = A → A → A

module Sandbox-Naive-Monoids where
  record IsMonoid {Carrier : Set ℓ}
                  (_·_ : Op₂ Carrier)
                  (ε : Carrier)
    : Set (lsuc ℓ) where
    field
      assoc     : (x y z : Carrier) → (x · y) · z ≡ x · (y · z)
      identityˡ : (x : Carrier) → ε · x ≡ x
      identityʳ : (x : Carrier) → x · ε ≡ x
  open IsMonoid

  *-1 : IsMonoid _*_ 1
  *-1 .assoc = *-assoc
  *-1 .identityˡ = *-identityˡ
  *-1 .identityʳ = *-identityʳ

  +-0 : IsMonoid _+_ 0
  +-0 .assoc = +-assoc
  +-0 .identityˡ = +-identityˡ
  +-0 .identityʳ = +-identityʳ

  record Monoid {c : Level} (Carrier : Set c) : Set (lsuc c) where
    infixl 7 _·_
    field
      _·_ : Op₂ Carrier
      ε   : Carrier
      is-monoid : IsMonoid _·_ ε
    
  bundle 
    : {c : Level} {A : Set c} {· : Op₂ A} {ε : A}
    → IsMonoid · ε
    → Monoid A
  bundle {· = ·} {ε = ε} A-monoid
    = record { _·_ = · ; ε = ε ; is-monoid = A-monoid }
  
  open Monoid ⦃ ... ⦄

  _∘_ : (B → C) → (A → B) → (A → C)
  (f ∘ g) x = f (g x)

  id : A → A
  id a = a

  ∘-id : IsMonoid {Carrier = A → A} _∘_ id
  ∘-id .assoc f g h = refl
  ∘-id .identityˡ f = refl
  ∘-id .identityʳ f = refl

  open import Data.List using (List; []; _∷_; _++_)

  ++-assoc : {A : Set ℓ} (x y z : List A) → (x ++ y) ++ z ≡ x ++ (y ++ z)
  ++-assoc [] y z = refl
  ++-assoc (x ∷ xs) y z rewrite ++-assoc xs y z = refl

  ++-identityˡ : {A : Set ℓ} (xs : List A) → [] ++ xs ≡ xs
  ++-identityˡ xs = refl

  ++-identityʳ : {A : Set ℓ} (xs : List A) → xs ++ [] ≡ xs
  ++-identityʳ [] = refl
  ++-identityʳ (x ∷ xs) rewrite ++-identityʳ xs = refl


  ++-[] : IsMonoid {Carrier = List A} _++_ []
  ++-[] .assoc = ++-assoc
  ++-[] .identityˡ = ++-identityˡ
  ++-[] .identityʳ = ++-identityʳ

  open import Function using (id; const)

  record Foldable {ℓ₁ ℓ₂ : Level} (Container : Set ℓ₁ → Set ℓ₂)
      : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    field
      fold : {B : Set ℓ₂} → ⦃ monoid : Monoid B ⦄ → (A → B) → Container A → B

  open Foldable ⦃ ... ⦄
  
  instance
    fold-list : Foldable {ℓ} List
    fold-list .Foldable.fold f [] = ε
    fold-list .Foldable.fold f (x ∷ l) = (f x) · Foldable.fold fold-list f l

    fold-bintree : Foldable {ℓ} BinTree
    fold-bintree .Foldable.fold f empty = ε
    fold-bintree .Foldable.fold f (branch l x r) 
      = Foldable.fold fold-bintree f l · f x · Foldable.fold fold-bintree f r
    
    fold-maybe : Foldable {ℓ} Maybe
    fold-maybe .Foldable.fold f (just x) = f x
    fold-maybe .Foldable.fold f nothing = ε

  size : {A : Set ℓ} {Container : Set ℓ → Set} → ⦃ Foldable Container ⦄ → Container A → ℕ
  size = fold ⦃ monoid = bundle +-0 ⦄ (const 1)

  build : ∀ {Container} → ⦃ Foldable Container ⦄ → Container A → List A
  build = fold ⦃ monoid = bundle ++-[] ⦄ (_∷ [])

  module _ ⦃ m₁ : Monoid A ⦄ ⦃ m₂ : Monoid B ⦄ where
    _⊗_ : Op₂ (A × B)
    (a , b) ⊗ (a' , b') = (a · a') , (b · b') 

    ⊗-assoc : (x y z : A × B) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    ⊗-assoc (a , b) (a' , b') (a'' , b'') 
      rewrite assoc is-monoid a a' a'' 
      rewrite assoc is-monoid b b' b''
      = refl
    
    ⊗-identityˡ : (x : A × B) → (ε , ε) ⊗ x ≡ x
    ⊗-identityˡ (fst , snd) 
      rewrite identityˡ is-monoid fst
      rewrite identityˡ is-monoid snd
      = refl

    ⊗-identityʳ : (x : A × B) → x ⊗ (ε , ε) ≡ x
    ⊗-identityʳ (a , b)
      rewrite identityʳ is-monoid a
      rewrite identityʳ is-monoid b
      = refl

    ×-is-monoid : IsMonoid _⊗_ (ε , ε)
    ×-is-monoid .assoc = ⊗-assoc
    ×-is-monoid .identityˡ = ⊗-identityˡ
    ×-is-monoid .identityʳ = ⊗-identityʳ

  ⊙ : ⦃ Monoid B ⦄ → Op₂ (A → B)
  ⊙ f g = λ x → (f x) · (g x)

  --pointwise : ⦃ _ : Monoid B ⦄ → IsMonoid (⊙ {A = A}) (const ε)
  --pointwise .assoc = {!   !}
  --pointwise .identityˡ = {!   !}
  --pointwise .identityʳ = {!   !}

  _≗_ : {A : Set ℓ₁} {B : A → Set ℓ₂} → Rel ((x : A) → B x) _
  _≗_ {A = A} f g = (x : A) → f x ≡ g x

  module _ {A : Set ℓ₁} {B : A → Set ℓ₂} where
    private
      Fn : Set _
      Fn = (x : A) → B x
    
    ≗-refl : Reflexive {A = Fn} _≗_
    ≗-refl {f} x = refl

    ≗-sym : Symmetric {A = Fn} _≗_
    ≗-sym {f} {g} p x = sym (p x)

    ≗-trans : Transitive {A = Fn} _≗_
    ≗-trans {f} {g} {h} p q x = trans (p x) (q x)

    ≗-equiv : IsEquivalence {A = Fn} _≗_
    ≗-equiv .IsEquivalence.isPreorder .IsPreorder.refl = ≗-refl
    ≗-equiv .IsEquivalence.isPreorder .IsPreorder.trans = ≗-trans
    ≗-equiv .IsEquivalence.sym = ≗-sym

    instance
      ≗-is-equiv = ≗-equiv
  postulate
    fun-ext : {A : Set ℓ₁} {B : A → Set ℓ₂} {f g : (x : A) → B x}
      → f ≗ g → f ≡ g

record Setoid (c ℓ : Level) : Set (lsuc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : (x y : Carrier) → Set ℓ
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

  module Reasoning where
    open Preorder-Reasoning (IsEquivalence.isPreorder isEquivalence) public

module Setoid-Renaming where
  open Setoid
    hiding (refl; sym; trans)
    renaming (isEquivalence to equiv)
    public
  open IsPreorder
    using ()
    renaming (refl to refl' ; trans to trans')
    public

  open IsEquivalence
    using ()
    renaming (isPreorder to pre; sym to sym')
    public

module _ where
  open Setoid-Renaming

  prop-setoid : Set ℓ → Setoid ℓ ℓ
  Carrier (prop-setoid A)             = A
  _≈_ (prop-setoid A)                 = _≡_
  equiv (prop-setoid A) .pre .refl'   = refl
  equiv (prop-setoid A) .pre .trans'  = trans
  equiv (prop-setoid A) .sym'         = sym

  instance
    prop-setoid-inst : {c : Level} {A : Set c} → Setoid c c
    prop-setoid-inst {A = A} = prop-setoid A

  private variable
    c c₁ c₂ : Level

  module _ (s₁ : Setoid c₁ ℓ₁) (s₂ : Setoid c₂ ℓ₂) where
    private instance
      s₁-equiv = equiv s₁
      s₂-equiv = equiv s₂

    private
      Carrier₁ = s₁ .Carrier
      Carrier₂ = s₂ .Carrier
      _≈₁_ = s₁ ._≈_
      _≈₂_ = s₂ ._≈_

    ×-setoid : Setoid _ _
    Carrier ×-setoid = Carrier₁ × Carrier₂
    _≈_ ×-setoid (x , y) (a , b) = (x ≈₁ a) × (y ≈₂ b)
    equiv ×-setoid .pre .refl' = refl , refl
    equiv ×-setoid .pre .trans' (fst , snd) (fst₁ , snd₁) = (trans fst fst₁) , (trans snd snd₁)
    equiv ×-setoid .sym' (fst , snd) = (sym fst) , (sym snd)

    data ⊎-Pointwise : Rel (Carrier₁ ⊎ Carrier₂) (ℓ₁ ⊔ ℓ₂) where
      inj₁ : {x y : Carrier₁} → x ≈₁ y → ⊎-Pointwise (inj₁ x) (inj₁ y)
      inj₂ : {x y : Carrier₂} → x ≈₂ y → ⊎-Pointwise (inj₂ x) (inj₂ y)

    ⊎-refl : Reflexive ⊎-Pointwise
    ⊎-refl {inj₁ x} = inj₁ refl
    ⊎-refl {inj₂ y} = inj₂ refl

    ⊎-trans : Transitive ⊎-Pointwise
    ⊎-trans (inj₁ p) (inj₁ q) = inj₁ (trans p q)
    ⊎-trans (inj₂ p) (inj₂ q) = inj₂ (trans p q)

    ⊎-preorder : IsPreorder ⊎-Pointwise
    ⊎-preorder .refl' = ⊎-refl
    ⊎-preorder .trans' = ⊎-trans

    ⊎-sym : Symmetric ⊎-Pointwise
    ⊎-sym (inj₁ p) = inj₁ (sym p)
    ⊎-sym (inj₂ p) = inj₂ (sym p)

    ⊎-equiv : IsEquivalence ⊎-Pointwise
    ⊎-equiv .pre = ⊎-preorder
    ⊎-equiv .sym' = ⊎-sym

    ⊎-setoid : Setoid (c₁ ⊔ c₂) (ℓ₁ ⊔ ℓ₂)
    ⊎-setoid .Carrier = s₁ .Carrier ⊎ s₂ .Carrier
    ⊎-setoid ._≈_ = ⊎-Pointwise
    ⊎-setoid .equiv = ⊎-equiv

  module _ {a b : Level} (s₁ : Setoid a ℓ₁) (s₂ : Setoid b ℓ₂) where
    open Setoid s₁ renaming (Carrier to From; _≈_ to _≈₁_)
    open Setoid s₂ renaming (Carrier to To; _≈_ to _≈₂_)

    record Fn : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
      constructor fn
      field
        func : From → To
        cong : {x y : From} → x ≈₁ y → func x ≈₂ func y
    open Fn

    fun-ext : Setoid _ _
    fun-ext .Carrier = Fn
    fun-ext ._≈_ f g = {x y : From} → x ≈₁ y → (f .func x) ≈₂ (g .func y)
    fun-ext .equiv .pre .refl' {f} {x} {y} p = f .cong p
    fun-ext .equiv .pre .trans' {f} {g} {h} p q r = trans' (pre (equiv s₂)) (p r) (q (refl' (pre (equiv s₁))))
    fun-ext .equiv .sym' {f} {g} p q = sym' (equiv s₂) (p (sym' (equiv s₁) q))

    _⇒_ = fun-ext

record Monoid (c ℓ : Level) : Set (lsuc (c ⊔ ℓ)) where
  field
    setoid : Setoid c ℓ

  open Setoid setoid
    hiding (refl; sym; trans)
    public
  
  infixl 7 _·_

  field
    _·_ : Op₂ Carrier
    ε : Carrier
    assoc : (x y z : Carrier) → (x · y) · z ≈ x · (y · z)
    identityˡ : (x : Carrier) → ε · x ≈ x
    identityʳ : (x : Carrier) → x · ε ≈ x
    ·-cong : {x y z w : Carrier} → x ≈ y → z ≈ w → x · z ≈ y · w

module Naive = Sandbox-Naive-Monoids

recover : {_·_ : Op₂ A} {ε : A} → Naive.IsMonoid _·_ ε → Monoid _ _
recover {A = A} {_·_} {ε} M = record
  { setoid = prop-setoid A
  ; _·_ = _·_
  ; ε = ε
  ; assoc = Sandbox-Naive-Monoids.IsMonoid.assoc M
  ; identityˡ = Sandbox-Naive-Monoids.IsMonoid.identityˡ M
  ; identityʳ = Sandbox-Naive-Monoids.IsMonoid.identityʳ M
  ; ·-cong = λ {≡.refl ≡.refl → refl}
  }

module _ {a c : Level} (A : Set a) (mb : Monoid c ℓ) where
  open Monoid
  open Monoid mb
    renaming (ε to εᴮ; _·_ to _·ᴮ_; _≈_ to _≈ᴮ_ ; ·-cong to ·-congᴮ; setoid to setoidᴮ)
  open Fn

  reflᴮ : Reflexive _≈ᴮ_
  reflᴮ = refl' (pre (equiv setoidᴮ)) where open Setoid-Renaming

  pointwise : Monoid _ _
  pointwise .setoid = prop-setoid A ⇒ setoidᴮ
  (pointwise · fn f cong₁) (fn g cong₂) .func x = (f x) ·ᴮ (g x)
  ((pointwise · f) g) .cong ≡.refl = ·-congᴮ reflᴮ reflᴮ
  pointwise .ε .func x = εᴮ
  pointwise .ε .cong {x} {y} ≡.refl = reflᴮ
  pointwise .assoc f g h {x} ≡.refl = assoc mb (f .func x) (g .func x) (h .func x)
  pointwise .identityˡ f {x} ≡.refl = identityˡ mb (f .func x)
  pointwise .identityʳ f {x} ≡.refl = identityʳ mb (f .func x)
  pointwise .·-cong {f} {f'} {g} {g'} p q {x} ≡.refl = ·-congᴮ (p refl) (q refl)

private variable
  c c₁ c₂ : Level

module _ (m₁ : Monoid c₁ ℓ₁) (m₂ : Monoid c₂ ℓ₂) where
  open Monoid ⦃ ... ⦄

  private instance
    _ = m₁
    _ = m₂

  From  = m₁ .Monoid.Carrier
  To    = m₂ .Monoid.Carrier
  _≈₁_  = m₁ .Monoid._≈_
  _≈₂_  = m₂ .Monoid._≈_
  ε₁    = m₁ .Monoid.ε
  ε₂    = m₂ .Monoid.ε
  _·₁_  = m₁ .Monoid._·_
  _·₂_  = m₂ .Monoid._·_

  record MonHom (f : From → To) : Set (c₁ ⊔ c₂ ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      preserves-ε : f ε₁ ≈₂ ε₂
      preserves-· : (a b : From) → (f (a ·₁ b)) ≈₂ ((f a) ·₂ (f b))
      f-cong      : {a b : From} → a ≈₁ b → f a ≈₂ f b

open MonHom

open import Algebra
  using (Op₂)
  public

open import Data.List
  using (List; []; _∷_; _++_)
  public

open import Data.Maybe
  using (_<∣>_)
  public

open import Function
  using (id; _∘_; const; flip)
  public

open import Relation.Binary.PropositionalEquality
  using (_≗_)
  public