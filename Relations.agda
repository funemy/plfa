module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)

-- Indexed datatype
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
  -----------------
    → zero ≤ n
  s≤s : ∀ {m n : ℕ}
    → m ≤ n
  -----------------
    → suc m ≤ suc n
-- (1 ≤ 2) ≤ 3 or 1 ≤ (2 ≤ 3) do not make sense
-- so we do not specify associativity
infix 4 _≤_

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
  -------------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
  -----------------
  → m ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ}
  ----------------
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
  ---------------------
  → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
  ---------------------
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- Specify Totality
-- Parametrized datatype
-- Parametrized dataype can be translated to indexed datatype
data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                     | forward m≤n = forward (s≤s m≤n)
...                     | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
  -----------------------
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
  -----------------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
  ------------------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : (n p q : ℕ)
  → p ≤ q
  → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : (m n p : ℕ)
  → m ≤ n
  → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
  ------------------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

-- Strict Inequality
data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ}
    -------------
    → zero < suc n -- NOTE: suc n
  s<s : ∀ {m n : ℕ}
    → m < n
    ---------------
    → suc m < suc n
infix 4 _<_

<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
  → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

data Trichotomy (m n : ℕ) : Set where
  forward : m < n → Trichotomy m n
  flipped : n < m → Trichotomy m n
  equal : m ≡ n → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = equal refl
<-trichotomy zero (suc n) = forward z<s
<-trichotomy (suc m) zero = flipped z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
... | forward m<n = forward (s<s m<n)
... | flipped n<m = flipped (s<s n<m)
... | equal n≡m = equal (cong suc n≡m)

+-monoʳ-< : ∀ (n p q : ℕ)
  → p < q
  → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
  → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
  → m + p < n + q
+-mono-< m n p q  m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

≤-iffʳ-< : ∀ (m n : ℕ)
  → suc m ≤ n
  → m < n
≤-iffʳ-< zero (suc n) _ = z<s
≤-iffʳ-< (suc m) (suc n) (s≤s sm≤n) = s<s (≤-iffʳ-< m n sm≤n)

≤-iffˡ-< : ∀ (m n : ℕ)
  → m < n
  → suc m ≤ n
≤-iffˡ-< zero (suc n) _ = s≤s z≤n
≤-iffˡ-< (suc m) (suc n) (s<s m<n) = s≤s (≤-iffˡ-< m n m<n)

≤-suc : ∀ (n : ℕ) → n ≤ suc n
≤-suc zero = z≤n
≤-suc (suc n) = s≤s (≤-suc n)

<-trans-revisit : ∀ (m n p : ℕ)
  → m < n
  → n < p
  → m < p
<-trans-revisit m n p m<n n<p = ≤-iffʳ-< m p (helper (≤-iffˡ-< m n m<n) (≤-iffˡ-< n p n<p))
  where
  helper : ∀ {m n p : ℕ}
    → suc m ≤ n
    → suc n ≤ p
    → suc m ≤ p
  helper sm≤n (s≤s {_} {n} sn≤p) =  ≤-trans (≤-trans sm≤n sn≤p) (≤-suc n)

-- Predicates
data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀ {n : ℕ} → even n → odd (suc n)