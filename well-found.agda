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

-- | When _<_ is well-founded,all elemnts are accessible.
rec-wf : {A : Set}{_<_ : A → A → Set}{P : A → Set} →
  well-found _<_ →
  ((x : A) → ((y : A) → y < x → P y) → P x) →
  (x : A) → P x
rec-wf {A}{_<_} wf f x = acc-fold _<_ f x (wf x)

-- --------------------------------------------------------------------------

-- example div, which cannot terminating.
{-# TERMINATING #-}
_div_ : ℕ → ℕ → ℕ
zero div n = zero
suc m div zero = suc m
suc m div suc n = suc ((suc m ∸ suc n) div (suc n))

n∸d<sn : ∀ n d → n ∸ d <′ suc n
n∸d<sn n zero = ≤′-refl
n∸d<sn zero (suc d) = ≤′-refl
n∸d<sn (suc n) (suc d) = ≤′-step (n∸d<sn n d)

-- example div
_div-wf_ : ℕ → ℕ → ℕ
n div-wf d = rec-wf ℕ<-wf (body d) n
  where
    body : (d : ℕ) → (n : ℕ) → ((k : ℕ) → k <′ n → ℕ) → ℕ
    body d zero rec = zero
    body zero (suc n) rec = suc n
    body (suc d) (suc n) rec = suc (rec (suc n ∸ suc d) (n∸d<sn n d))

-- example div'
_div-wf'_ : ∀ m → ℕ → Acc _<′_ m → ℕ
(zero div-wf' d) a = zero
(suc n div-wf' zero) a = suc n
(suc n div-wf' suc d) (acc .(suc n) h) = suc (((suc n ∸ suc d) div-wf' (suc d)) (h (suc n ∸ suc d) (n∸d<sn n d)))


open import Data.Product

-- Upper bound reverse ordering
_<_≤_ : ℕ → ℕ → ℕ → Set
m < n ≤ k = m <′ n × n ≤′ k

◁ : ℕ → ℕ → ℕ → Set
(◁ k) m n = m < n ≤ k
