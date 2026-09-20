module Chapter2-Numbers where

open import Chapter1-Agda

module Definition-Naturals where
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

module Sandbox-Naturals where
  open import Data.Nat
    using (ℕ; zero; suc)

  data IsEven : ℕ → Set where
    zero-even : IsEven zero
    next-even : {n : ℕ} → IsEven n → IsEven (suc (suc n))

  four-is-even : IsEven 4
  four-is-even = next-even (next-even zero-even)

  data IsOdd : ℕ → Set where
    one-odd  : IsOdd 1
    next-odd : {n : ℕ} → IsOdd n → IsOdd (suc (suc n))

  evenOdd : {n : ℕ} → IsEven n → IsOdd (suc n)
  evenOdd zero-even = one-odd
  evenOdd (next-even evenN) = next-odd (evenOdd evenN)

  data Maybe (A : Set) : Set where
    just    : A → Maybe A
    nothing :     Maybe A

  evenEv : (n : ℕ) → Maybe (IsEven n)
  evenEv zero = just zero-even
  evenEv (suc zero) = nothing
  evenEv (suc (suc n)) with evenEv n
  ... | just x = just (next-even x)
  ... | nothing = nothing

  _+_ : ℕ → ℕ → ℕ
  zero + y = y
  suc x + y = suc (x + y)
  infixl 6 _+_

  _*_ : ℕ → ℕ → ℕ
  zero * y = zero
  suc x * y = y + x * y
  infixl 7 _*_

  _^_ : ℕ → ℕ → ℕ
  x ^ zero = 1
  x ^ suc y = x * x ^ y
  infixr 8 _^_

  _∸_ : ℕ → ℕ → ℕ
  zero ∸ y = zero
  suc x ∸ zero = suc x
  suc x ∸ suc y = x ∸ y
  infixl 6 _∸_

module Sandbox-Integers where
  import Data.Nat as ℕ
  open ℕ using (ℕ)

  data ℤ : Set where
    +_     : ℕ → ℤ
    -[1+_] : ℕ → ℤ

  suc : ℤ → ℤ
  suc (+ x) = + ℕ.suc x
  suc -[1+ ℕ.zero ] = + 0
  suc -[1+ ℕ.suc x ] = -[1+ x ]

  pred : ℤ → ℤ
  pred (+ ℕ.zero) = -[1+ ℕ.zero ]
  pred (+ ℕ.suc x) = + x
  pred -[1+ x ] = -[1+ (ℕ.suc x) ]

  pattern +[1+_] n = + ℕ.suc n
  pattern +0 = + ℕ.zero

  -_ : ℤ → ℤ
  - +0       = +0
  - +[1+ x ] = -[1+ x ]
  - -[1+ x ] = +[1+ x ]

  infixl 5 _⊖_
  _⊖_ : ℕ → ℕ → ℤ
  ℕ.zero ⊖ ℕ.zero = +0
  ℕ.zero ⊖ ℕ.suc y = -[1+ y ]
  ℕ.suc x ⊖ ℕ.zero = +[1+ x ]
  ℕ.suc x ⊖ ℕ.suc y = x ⊖ y

  infixl 5 _+_
  _+_ : ℤ → ℤ → ℤ
  (+ x) + (+ y) = + (x ℕ.+ y)
  (+ x) + -[1+ y ] = x ⊖ (ℕ.suc y)
  -[1+ x ] + (+ y) = y ⊖ (ℕ.suc x)
  -[1+ x ] + -[1+ y ] = -[1+ (x ℕ.+ ℕ.suc y) ]

  infixl 5 _-_
  _-_ : ℤ → ℤ → ℤ
  x - y = x + (- y)

  infixl 6 _*_
  _*_ : ℤ → ℤ → ℤ
  x * +0       = +0
  x * +[1+ ℕ.zero ] = x
  x * +[1+ ℕ.suc y ] = (x * +[1+ y ]) + x
  x * -[1+ ℕ.zero ] = - x
  x * -[1+ ℕ.suc y ] = (x * -[1+ y ]) - x

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
  public

open Sandbox-Naturals
  using (IsEven)
  renaming ( zero-even to z-even
           ; next-even to ss-even
           )
  public

open import Data.Maybe
  using (Maybe; just; nothing)
  public
