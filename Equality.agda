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

-- Copying previous definition to avoid importing builtin equality
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)
infixl 6 _+_
{-# BUILTIN NATPLUS _+_ #-}

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
  -----------------
    → zero ≤ n
  s≤s : ∀ {m n : ℕ}
    → m ≤ n
  -----------------
    → suc m ≤ suc n
infix 4 _≤_

-- NOTE: We cannot use the +-comm and +-identityʳ defined in the previous chapter
-- Because they use the builtin ≡ from standard library
-- Using `postulate` to avoid redefining everything
postulate
  +-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  ≤-trans : ∀ {m n p : ℕ}
    → m ≤ n
    → n ≤ p
    → m ≤ p
  ≤-refl : ∀ {n} → n ≤ n

-- redefine commutativity of +
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = +-identityʳ m
+-comm m (suc n) =
  begin
    m + (suc n)
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    (suc n) + m
  ∎

module ≤-Reasoning where
  infix 1 ≤begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_ _≡≤⟨_⟩_
  infix 3 _≤∎

  ≤begin_ : ∀ {x y : ℕ}
    → x ≤ y
    → x ≤ y
  ≤begin x≤y = x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
    → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
    → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

  _≡≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≡ y
    → y ≤ z
    → x ≤ z
  x ≡≤⟨ refl ⟩ y≤z = y≤z

  _≤∎ : ∀ (x : ℕ)
    → x ≤ x
  x ≤∎ = ≤-refl

open ≤-Reasoning

+-monoʳ-≤' : ∀ (n p q : ℕ)
  → p ≤ q
  → n + p ≤ n + q
+-monoʳ-≤' zero p q p≤q =
  ≤begin
    zero + p
  ≤⟨ p≤q ⟩
    zero + q
  ≤∎
+-monoʳ-≤' (suc n) p q p≤q =
  ≤begin
    suc n + p
  ≤⟨ s≤s (+-monoʳ-≤' n p q p≤q) ⟩
    suc n + q
  ≤∎

+-monoˡ-≤' : ∀ (m n p : ℕ)
  → m ≤ n
  → m + p ≤ n + p
+-monoˡ-≤' m n p m≤n =
  ≤begin
    m + p
  ≡≤⟨ +-comm m p ⟩
    p + m
  ≤⟨ +-monoʳ-≤' p m n m≤n ⟩
    p + n
  ≡≤⟨ +-comm p n ⟩
    n + p
  ≤∎

+-mono-≤' : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
  → m + p ≤ n + q
+-mono-≤' m n p q m≤n p≤q =
  ≤begin
    m + p
  ≤⟨ +-monoˡ-≤' m n p m≤n ⟩
    n + p
  ≤⟨ +-monoʳ-≤' n p q p≤q ⟩
    n + q
  ≤∎

-- Specify equality to enable rewriting
{-# BUILTIN EQUALITY _≡_ #-}

-- Trying out the dot pattern
data even : ℕ → Set
data odd : ℕ → Set

data even where
  even-zero : even zero
  even-suc : ∀ {n : ℕ}
    → odd n
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
    → odd (suc n)

even-comm : ∀ {m n : ℕ}
  → even (m + n)
  → even (n + m)
even-comm {m} {n} e-m+n rewrite +-comm m n = e-m+n

even-comm' : ∀ {m n : ℕ}
  → even (m + n)
  → even (n + m)
even-comm' {m} {n} e-m+n with   m + n  | +-comm m n
...                         | .(n + m) | refl       = e-m+n

even-comm'' : ∀ {m n : ℕ}
  → even (m + n)
  → even (n + m)
even-comm'' {m} {n} = subst even (+-comm m n)

-- Leibniz Equality
-- Two objects are equal if they satisfy the same properties
--
-- This closely relates to Spock's Law
-- "A difference that makes no difference is no difference"
--
-- We show two terms satisfy Leibniz equality iff they satisfy Martin-Lof equality

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
  → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

-- !?
sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy
  where
    -- Predicate Q
    -- Note that (P z → P x) : Set
    -- Q z holds if P z implies P x
    Q : A → Set
    Q z = P z → P x
    -- Q x holds trivially
    Qx : Q x
    Qx = refl-≐ P
    -- Q y holds because of Leibniz equality
    -- And Q y is indeed the thing we want to proof
    Qy : Q y
    Qy = x≐y Q Qx

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
  → x ≐ y
≡-implies-≐ x≡y P = subst P x≡y

-- The proof strategy is similar to the symmetry proof
≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
  → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = Qy
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx

-- NOTE:
-- Thoughts, since Leibniz equality is universally quantified over a property P
-- Our proof structure is to try comming up with a concrete P that has the shape of our proof goal.

-- Universe Polymorphism
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

-- The definition of levels are isomorphic to natural numbers
-- lzero : Level
-- lsuc : Level → Level
--
-- Set₀ = Set lzero
-- Set₁ = Set (lsuc lzero)
-- ... and so on

-- Generalized equality to arbitrary levels
data _≡'_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl' : x ≡' x

sym' : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
  → x ≡' y
  → y ≡' x
sym' refl' = refl'

_≐'_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐'_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

-- Example: generalized function composition
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B)
  → (A → C)
(g ∘ f) x = g (f x)