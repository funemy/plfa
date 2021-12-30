data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

seven' : ℕ
seven' = 7

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)
infixl 6 _+_
{-# BUILTIN NATPLUS _+_ #-}

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

+-example : 3 + 4 ≡ 7
+-example =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc ((suc 1  + 4))
  ≡⟨⟩
    suc (suc (suc 0 + 4))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    7
  ∎

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = (m * n) + n
infixl 7 _*_
{-# BUILTIN NATTIMES _*_ #-}

_ =
  begin
    2 * 3
  ≡⟨⟩
    1 * 3 + 3
  ≡⟨⟩
    0 * 3 + 3 + 3
  ≡⟨⟩
    0 + 3 + 3
  ≡⟨⟩
    6
  ∎

_ =
  begin
    3 * 4
  ≡⟨⟩
    12
  ∎

_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ (suc n) = m * (m ^ n)

_ =
  begin
    3 ^ 4
  ≡⟨⟩
    81
  ∎

{- monus -}
_∸_ : ℕ → ℕ → ℕ
0 ∸ n = 0
(suc m) ∸ 0 = (suc m)
(suc m) ∸ (suc n) = m ∸ n
infixl 6 _∸_
{-# BUILTIN NATMINUS _∸_ #-}

_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

data Bin : Set where
  ⟨⟩ : Bin
  _I : Bin → Bin
  _O : Bin → Bin

_ : Bin
_ = ⟨⟩ I O I I

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b I) = (inc b) O
inc (b O) = b I

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

_ : inc (⟨⟩ I I I I) ≡ ⟨⟩ I O O O O
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc x) = inc (to x)

from : Bin → ℕ
from ⟨⟩ = zero
from (x I) = 2 * (from x) + 1
from (x O) = 2 * (from x)

_ : to 0 ≡ ⟨⟩ O
_ = refl

_ : from (⟨⟩ O) ≡ 0
_ = refl

_ : inc (⟨⟩ I O I I) ≡ to 12
_ = refl

