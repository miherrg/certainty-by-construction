module Chapter1-Agda where

module Booleans where
  open import Relation.Binary.PropositionalEquality
  data Bool : Set where
    false : Bool
    true : Bool

  ¬ : Bool → Bool
  ¬ false = true
  ¬ true = false

  _ : ¬ (¬ false) ≡ false
  _ = refl

  _∨_ : Bool → Bool → Bool
  false ∨ y = y
  true ∨ y = true

  _∧_ : Bool → Bool → Bool
  false ∧ y = false
  true ∧ y = y

module Example-Employees where
  open Booleans
  open import Data.String
    using (String)

  data Department : Set where
    administrative : Department
    engineering    : Department
    finance        : Department
    marketing      : Department
    sales          : Department

  record Employee : Set where
    field
      name        : String
      department  : Department
      is-new-hire : Bool

  tillman : Employee
  tillman = record  {name =  "Tillman" ; department = engineering ; is-new-hire = false}

module Sandbox-Tuples-Constructless where
  record _×_ (A B : Set) : Set where
    field
      fst : A
      snd : B

  open Booleans
  open _×_

  my-tuple : Bool × Bool
  my-tuple = record { fst = true ∨ true ; snd = ¬ true }

  my-tuple-fst : Bool
  my-tuple-fst = fst my-tuple

  _,_ : {A B : Set} → A → B → A × B
  x , y = record { fst = x ; snd = y }

module Sandbox-Tuples where
  open Booleans

  infixr 4 _,_
  infixr 2 _×_
  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      π₁ : A
      π₂ : B
  open _×_

  infixr 1 _⊎_
  data _⊎_ (A B : Set) : Set where
    ι₁ : A → A ⊎ B
    ι₂ : B → A ⊎ B
