module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) = cong suc (+-identityʳ m)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = +-identityʳ m
-- This is the step-by-step proof
-- _≡⟨_⟩_ operator is a syntax sugar for `trans`
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
-- Below is the oversimplied proof
-- which involves the type-level function `trans`
-- +-comm m (suc n) = trans (+-suc m n) (cong suc (+-comm m n))

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
-- A proof without using induction (i.e., pattern matching)
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨⟩
    m + n + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_ ) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    m + (n + p) + q
  ∎
-- A different proof using induction
-- +-rearrange zero n p q =
--   begin
--     (zero + n) + (p + q)
--   ≡⟨⟩
--     n + (p + q)
--   ≡⟨ sym (+-assoc n p q) ⟩
--     (n + p) + q
--   ≡⟨⟩
--     zero + (n + p) + q
--   ∎
-- +-rearrange (suc m) n p q = cong suc (+-rearrange m n p q)

-- proving associativity with rewrite
+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero n p = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl

-- +-identityʳ and +-suc can also be proved by using rewrite

-- proving commutativity with rewrite
+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero = +-identityʳ m
+-comm' m (suc n) rewrite +-suc m n | +-comm' m n = refl

-- Exercise
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p
  rewrite sym (+-assoc m n p)
  | sym (+-assoc n m p)
  | +-comm m n
  = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p
  rewrite *-distrib-+ m n p
  | +-assoc p (m * p) (n * p)
  = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p
  rewrite *-distrib-+ n (m * n) p
  | *-assoc m n p
  = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero zero = refl
*-comm zero (suc n) = *-comm zero n
*-comm (suc m) zero = *-comm m zero
*-comm (suc m) (suc n)
  rewrite *-comm m (suc n)
  | sym (*-comm (suc m) n)
  | sym (+-assoc n m (n * m))
  | sym (+-assoc m n (m * n))
  | +-comm n m
  | *-comm m n
  = refl

0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ 0
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-|-assoc zero n p
  rewrite 0∸n≡0 n
  | 0∸n≡0 p
  | 0∸n≡0 (n + p)
  = refl
∸-|-assoc (suc m) zero p = refl
∸-|-assoc (suc m) (suc n) p = ∸-|-assoc m n p

^-distribˡ-|-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-|-* m zero p rewrite +-identityʳ (m ^ p) = refl
^-distribˡ-|-* m (suc n) p
 rewrite *-assoc m (m ^ n) (m ^ p)
  = cong (m *_) (^-distribˡ-|-* m n p)

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p)
  rewrite sym (*-assoc (m * (m ^ p)) n (n ^ p))
  | *-assoc m (m ^ p) n
  | *-comm (m ^ p) n
  | sym (*-assoc m n (m ^ p))
  | *-assoc (m * n) (m ^ p) (n ^ p)
  = cong (m * n *_) (^-distribʳ-* m n p)

^-one : ∀ (m : ℕ) → 1 ^ m ≡ 1
^-one zero = refl
^-one (suc m) rewrite +-identityʳ (1 ^ m) = ^-one m

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m zero p = ^-one p
^-*-assoc m (suc n) p
  rewrite ^-distribʳ-* m (m ^ n) p
  | ^-distribˡ-|-* m p (n * p)
  | ^-*-assoc m n p
  = refl

-- TODO: Bin-laws
