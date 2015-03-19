module Bench where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

double : ℕ → ℕ
double zero = zero
double (succ n) = succ (succ (double n))

pow2 : ℕ → ℕ
pow2 zero = succ zero
pow2 (succ n) = double (pow2 n)

double-tr : ℕ → ℕ
double-tr =
  aux zero
  where
    aux : ℕ → ℕ → ℕ
    aux acc zero = acc
    aux acc (succ n) = aux (succ (succ acc)) n

pow2-tr : ℕ → ℕ
pow2-tr =
  aux (succ zero)
  where
    aux : ℕ → ℕ → ℕ
    aux acc zero = acc
    aux acc (succ n) = aux (double acc) n

data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

data List : Set where
  nil : List
  cons : ℕ → List → List

lt-nat : ℕ → ℕ → 𝔹
lt-nat _ zero = false
lt-nat zero (succ _) = true
lt-nat (succ x) (succ y) = lt-nat x y

insert : ℕ → List → List
insert a nil = cons a nil
insert a (cons b l) with lt-nat a b
... | false = cons b (insert a l)
... | true = cons a (cons b l)

insert-sort : List → List
insert-sort = aux nil
  where
    aux : List → List → List
    aux acc nil = acc
    aux acc (cons a l) = aux (insert a acc) l
 
