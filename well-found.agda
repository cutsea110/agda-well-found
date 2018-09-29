module well-found where

open import Data.Nat

-- | Accessibility
data Acc {A : Set}(_<_ : A → A → Set) : A → Set where
  acc : ∀ x → (∀ y → y < x → Acc _<_ y) → Acc _<_ x

-- | well-found
well-found : {A : Set} → (_<_ : A → A → Set) → Set
well-found _<_ = ∀ x → Acc _<_ x

-- | _<′_ over ℕ is well-found
ℕ<-wf : well-found _<′_
ℕ<-wf n = acc n (access n)
  where
    access : (n m : ℕ) → m <′ n → Acc _<′_ m
    access zero m ()
    access (suc n) .n ≤′-refl = acc n (access n)
    access (suc n) m (≤′-step m<n) = access n m m<n

-- | well-founded recursion
acc-fold : {A : Set} (_<_ : A → A → Set) {P : A → Set} →
  ((x : A) → ((y : A) → y < x → P y) → P x) →
  (z : A) → Acc _<_ z  → P z
acc-fold _<_ φ z (acc .z h) = φ z (λ y y<z → acc-fold _<_ φ y (h y y<z))
