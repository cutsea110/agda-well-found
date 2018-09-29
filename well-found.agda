module well-found where

data Acc {A : Set}(_<_ : A → A → Set) : A → Set where
  acc : ∀ x → (∀ y → y < x → Acc _<_ y) → Acc _<_ x

well-found : {A : Set} → (_<_ : A → A → Set) → Set
well-found _<_ = ∀ x → Acc _<_ x

