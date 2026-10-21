import Mathlib

/-!
# Challenge: Erdős Problem #33, an additive complement of the squares with `limsup ≤ 13√2/4`

Statement-only file for `lake comparator`: it imports only Mathlib, contains the definitions the
statements depend on, and states the theorems with `sorry`. The proofs are in
`RecentResults/Erdos33.lean`; `comparator/Erdos33.json` checks that they prove exactly these
statements with the standard axioms only.
-/

open Set Filter
open scoped goldenRatio

namespace Erdos33

/-- Verbatim from formal-conjectures `FormalConjectures/ErdosProblems/33.lean` (commit 2a315101):
every natural number `k` is `a + n²` with `a ∈ A`. -/
def AdditiveBasisCondition (A : Set ℕ) : Prop :=
  ∀ (k : ℕ), ∃ (n : ℕ) (a : ℕ), a ∈ A ∧ k = a + n^2

/-- The new bound `13√2/4 ≈ 4.596` for the infimum in formal-conjectures' `erdos_33`
(an upper bound only: the exact value `erdos_33.answer` is still open). -/
theorem erdos_33_le_13_sqrt2_div_4 :
    ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N =>
    (A.1 ∩ Icc 1 N).ncard / (√N : EReal)) ≤ ((13 * √2 / 4 : ℝ) : EReal) := by
  sorry

/-- formal-conjectures `erdos_33.variants.vanDoorn` (bound `2φ^{5/2} ≈ 6.66`, due to
W. van Doorn), statement verbatim minus the `@[category research solved, AMS 11]` attribute. -/
theorem erdos_33.variants.vanDoorn :
    ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N =>
    (A.1 ∩ Icc 1 N).ncard / (√N : EReal)) ≤ ↑(2 * (φ ^ ((5 : ℝ) / 2))) := by
  sorry

end Erdos33
