module plfa.Equality where

-- The only way to show equality is every value is equal to itself
-- Equality takes two arguments
-- The first is given by parameter `x : A`
-- (We favor parameters over indexes)
-- The second is given by index `A`
-- The first argument can be a parameter because it doesn't vary
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

-- Equality is an equivalence relation
-- Equivalence relation is:
--  reflxive, symmetric, and transitive
sym : ∀ {A : Set} {x y : A}
  → x ≡ y
  → y ≡ x
-- The proof below works because the type system requires x == y (refl is the only possible ctor)
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
  → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
  → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
  → f u v ≡ f x y
cong₂ f refl refl = refl 

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
  -------------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

-- Substitution:
-- If two values are equal and a predicate holds for the first value,
-- then it also holds for the second
-- NOTE: A predicate is a unary relation
subst : ∀ {A : Set} (P : A → Set) {x y : A}
  → x ≡ y
  → P x → P y
subst p refl px = px

module ≡-Reasoning {A : Set} where
  infix 1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix 3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
    → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
    → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl

open ≡-Reasoning

trans' : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
  → x ≡ z
trans' {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

module ≤-Reasoning {A : Set} where
  infix 1 begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix 3 _∎

  -- begin_

  -- _≤⟨⟩_

  -- _≤⟨_⟩_

  -- _∎

open ≤-Reasoning