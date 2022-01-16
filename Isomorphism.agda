module plfa.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- Extensionality:
-- The only way to distinguish functions is by applying them.
-- If two functions applied to the same argument always yield the same result
-- then they are the same function.

-- We defined cong-app before
cong-app' : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
  → ∀ (x : A) → f x ≡ g x
cong-app' refl x = refl
-- The converse of cong-app is extensionality

-- NOTE: Agda does not assume extensionality
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g

_+'_ : ℕ → ℕ → ℕ
m +' zero = m
m +' suc n = suc (m +' n)

same-app : ∀ (m n : ℕ) → m +' n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +' n ≡ n + m
  helper m zero = refl
  helper m (suc n) = cong suc (helper m n)

-- same-app proved ∀ m n : ℕ, the two definitions of the addtion
-- give the same result.
-- Thus we can use that to prove the two addition definitions are equivalent.
same : _+'_ ≡ _+_
same = extensionality λ m → extensionality λ n → same-app m n

-- More generic extensionality
postulate
  -- NOTE: I think here ∀ is just for explicity, but doesn't really change the meaning of the propositiion?
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g