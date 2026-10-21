import Mathlib

/-!
# Challenge: Park (arXiv:2609.08137), the Fibonacci numbers are not an additive uniqueness set

Statement-only file for `lake comparator`: it imports only Mathlib, contains the definitions the
statements depend on, and states the theorems with `sorry`. The proofs are in
`RecentResults/ParkFibonacci.lean`; `comparator/ParkFibonacci.json` checks that they prove
exactly these statements with the standard axioms only.
-/

open ArithmeticFunction

namespace FibSpiro

/-- Additive uniqueness set (Spiro), for complex multiplicative functions: `E ⊆ ℕ` is an AU set
if every multiplicative `f` with `f (a + b) = f a + f b` for all `a, b ∈ E` is the identity on
the positive integers. (An `ArithmeticFunction` vanishes at `0`, hence `0 < n`.) -/
def IsAUSet (E : Set ℕ) : Prop :=
  ∀ f : ArithmeticFunction ℂ, f.IsMultiplicative →
    (∀ a ∈ E, ∀ b ∈ E, f (a + b) = f a + f b) → ∀ n, 0 < n → f n = n

/-- The set of positive Fibonacci numbers `{F n | n ≥ 1}`. -/
def posFib : Set ℕ := {a | ∃ n, 1 ≤ n ∧ a = Nat.fib n}

/-- **Main theorem**, positive-integer-valued form: a multiplicative `f`, positive on positive
integers, with `f (F n + F m) = f (F n) + f (F m)` for all `n, m ≥ 1`, and `f 557 = 2417`,
`f 2417 = 557` (so `f ≠ id`). -/
theorem exists_nat_counterexample :
    ∃ f : ArithmeticFunction ℕ, f.IsMultiplicative ∧ (∀ n, 0 < n → 0 < f n) ∧
      (∀ n m, 1 ≤ n → 1 ≤ m →
        f (Nat.fib n + Nat.fib m) = f (Nat.fib n) + f (Nat.fib m)) ∧
      f 557 = 2417 ∧ f 2417 = 557 := by
  sorry

/-- **Main theorem**: the positive Fibonacci numbers are not an additive uniqueness set for
complex multiplicative functions. This answers Spiro's 1992 question negatively. -/
theorem not_isAUSet_posFib : ¬ IsAUSet posFib := by
  sorry

end FibSpiro

namespace FibCrit

/-- The hypotheses of Theorem 4.1 on one prime `ℓ`: `r` is odd and `≥ 5`, `ℓ > 2`, and `r` is
the rank of apparition of `ℓ` (`ℓ ∤ F k` for `0 < k < r`, and `ℓ ∣ F r`). -/
structure Hyp (ℓ r : ℕ) : Prop where
  r5 : 5 ≤ r
  rodd : Odd r
  two_lt : 2 < ℓ
  hz : ∀ k, 0 < k → k < r → ¬ ℓ ∣ Nat.fib k
  hr : ℓ ∣ Nat.fib r

variable {ℓ r : ℕ}

/-- **Theorem 4.1** of Park (the divisibility equivalence), for all `n, m` (the paper takes
`n, m ≥ 1`); `p ≠ q` is not needed. -/
theorem criterion {r p q : ℕ} (hp : p.Prime) (hq : q.Prime) (Hp : Hyp p r) (Hq : Hyp q r)
    (hdp : ∀ i j, 2 ≤ i → i ≤ (r - 1) / 2 → 2 ≤ j → j ≤ (r - 1) / 2 →
      Nat.fib i ^ 4 % p = Nat.fib j ^ 4 % p → i = j)
    (hdq : ∀ i j, 2 ≤ i → i ≤ (r - 1) / 2 → 2 ≤ j → j ≤ (r - 1) / 2 →
      Nat.fib i ^ 4 % q = Nat.fib j ^ 4 % q → i = j)
    (n m : ℕ) : p ∣ Nat.fib n + Nat.fib m ↔ q ∣ Nat.fib n + Nat.fib m := by
  sorry

end FibCrit
