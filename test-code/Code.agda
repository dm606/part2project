module Code where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (succ n)
  fsucc : {n : ℕ} → (i : Fin n) → Fin (succ n)

nth : {A : Set} → {m : ℕ} → Vec A m → Fin m → A
nth (a :: l) fzero = a
nth (a :: l) (fsucc i) = nth l i

map : {A B : Set} → (A → B) → {n : ℕ} → Vec A n → Vec B n
map _ [] = []
map f (x :: l) = (f x) :: (map f l)

_+_ : ℕ → ℕ → ℕ
zero + y = y
(succ z) + y = succ (z + y)

_++_ : {A : Set} → {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
[] ++ y = y
(a :: z) ++ y = a :: (z ++ y)

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥

data _∨_ (A : Set) (B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

data _∧_ (A : Set) (B : Set) : Set where
  _,_ : A → B → A ∧ B

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

data ∃ (A : Set) (B : A → Set) : Set where
  Ex : (a : A) → B a → ∃ A B

mutual
  data DistinctList (A : Set) (_≠_ : A → A → Set) : Set where
    <> : DistinctList A _≠_
    dcons : (a : A) → (l : DistinctList A _≠_) → Fresh _≠_ a l
          → DistinctList A _≠_
      
  Fresh : {A : Set} → (_≠_ : A → A → Set) → (a : A) → (l : DistinctList A _≠_)
        → Set
  Fresh _ _ <> = ⊤
  Fresh _≠_ a (dcons b l p) = (a ≠ b) ∧ Fresh _≠_ a l

⊥-elim : {X : Set} → ⊥ → X
⊥-elim ()

proof : {A B : Set} → (¬ A) ∧ (A ∨ B) → B
proof (a , (inl x)) = ⊥-elim (a x)
proof (a , (inr x)) = x

proof2 : (n : ℕ) → ¬ (n ≡ zero) → ∃ ℕ (λ m → n ≡ (succ m))
proof2 zero f = ⊥-elim (f refl)
proof2 (succ n) _ = Ex n refl

