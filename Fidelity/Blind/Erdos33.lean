import Mathlib

/-!
# Erdős Problem #33 — new upper bound `13√2/4` (blind formalization)

Sources read:
* https://www.erdosproblems.com/33 (problem statement):
  "Let `A ⊂ ℕ` be such that every large integer can be written as `n² + a` for some `a ∈ A` and
  `n ≥ 0`. What is the smallest possible value of
  `limsup_{N→∞} |A ∩ {1,…,N}| / N^{1/2}` ?"
* Forum post (07 Sep 2026, thread 33): improves the limsup bound to `13√2/4`.
* LeanMeanBean/erdos-33, file `erdos33_limsup_4_596.pdf` / LaTeX `erdos33_limsup`:
  "There exists an additive complement `A` to the squares such that
   `limsup_{x→∞} A(x)/√x ≤ 13/(2√2) = 13√2/4 ≈ 4.596194`.  Hence `L ≤ 13√2/4`."
  (The construction gives that "every sufficiently large `m` has a representation `m = n² + a`,
  `a ∈ A`", after "Include finitely many small integers in `A`".)
* formal-conjectures `ErdosProblems/33.lean` (for the shape of `erdos_33.variants.vanDoorn`).
-/

open Filter Set

namespace Blind.Erdos33

/-- `A ⊆ ℕ` is an additive complement of the squares: every natural number `m` can be written
as `m = n ^ 2 + a` with `n ≥ 0` (so `n : ℕ`) and `a ∈ A`. -/
def IsAddComplSquares (A : Set ℕ) : Prop :=
  ∀ m : ℕ, ∃ n a : ℕ, a ∈ A ∧ m = n ^ 2 + a

/-- Literal "every large integer" version of the complement property (as on erdosproblems.com and
in the source's "every sufficiently large `m`"). -/
def IsAddComplSquaresEventually (A : Set ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ n a : ℕ, a ∈ A ∧ m = n ^ 2 + a

/-- Counting function `A(N) = |A ∩ {1, …, N}|`. -/
noncomputable def countUpTo (A : Set ℕ) (N : ℕ) : ℕ := (A ∩ Icc 1 N).ncard

/-- `limsup_{N→∞} |A ∩ {1,…,N}| / √N`, taken in `EReal` so that an unbounded ratio gives `⊤`
(rather than a junk value as a real-valued `limsup` would). -/
noncomputable def normLimsup (A : Set ℕ) : EReal :=
  limsup (fun N : ℕ => (((countUpTo A N : ℝ) / Real.sqrt N : ℝ) : EReal)) atTop

/-- The constant `13√2/4 = 13/(2√2) ≈ 4.596`. -/
noncomputable def c : ℝ := 13 * Real.sqrt 2 / 4

/-- `L`: the smallest possible value (infimum) of the normalized limsup over all additive
complements of the squares. -/
noncomputable def L : EReal :=
  ⨅ A : {A : Set ℕ // IsAddComplSquares A}, normLimsup A.1

/-! ## Main claim (source: first displayed statement of `erdos33_limsup_4_596.pdf`)
"There exists an additive complement A to the squares such that
 limsup_{x→∞} A(x)/√x ≤ 13/(2√2) = 13√2/4." -/

/-- **Main claim.** There is `A ⊆ ℕ` with every natural number of the form `n² + a`, `a ∈ A`,
such that `limsup_{N→∞} |A ∩ [1,N]| / √N ≤ 13√2/4`. -/
theorem erdos33_exists_le :
    ∃ A : Set ℕ, IsAddComplSquares A ∧ normLimsup A ≤ ((13 * Real.sqrt 2 / 4 : ℝ) : EReal) := by
  sorry

/-- Same claim, with the complement property only for all sufficiently large `m`
(the literal wording "every sufficiently large m" / "every large integer"). Implied by
`erdos33_exists_le`. -/
theorem erdos33_exists_le_eventually :
    ∃ A : Set ℕ, IsAddComplSquaresEventually A ∧
      normLimsup A ≤ ((13 * Real.sqrt 2 / 4 : ℝ) : EReal) := by
  sorry

/-- Same claim, limsup unfolded into an explicit `ε`-form (equivalent for a fixed `A`):
for every `ε > 0`, eventually `|A ∩ [1,N]| ≤ (13√2/4 + ε) √N`. -/
theorem erdos33_exists_le_eps :
    ∃ A : Set ℕ, IsAddComplSquares A ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
        ((A ∩ Icc 1 N).ncard : ℝ) ≤ (13 * Real.sqrt 2 / 4 + ε) * Real.sqrt N := by
  sorry

/-! ## Consequence (source: "Hence L ≤ 13√2/4.") -/

/-- **Corollary.** The smallest possible limsup `L` is at most `13√2/4`. -/
theorem erdos33_L_le : L ≤ ((13 * Real.sqrt 2 / 4 : ℝ) : EReal) := by
  sorry

/-! ## Same consequence written in the exact shape of formal-conjectures' `erdos_33` family -/

/-- formal-conjectures' `AdditiveBasisCondition` (restated). -/
def AdditiveBasisCondition (A : Set ℕ) : Prop :=
  ∀ (k : ℕ), ∃ (n : ℕ) (a : ℕ), a ∈ A ∧ k = a + n ^ 2

/-- The new bound in formal-conjectures shape (infimum over admissible `A`, `EReal` limsup). -/
theorem erdos33_new_bound_fc_shape :
    ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
      ((A.1 ∩ Icc 1 N).ncard : EReal) / (Real.sqrt N : EReal)) ≤
        ((13 * Real.sqrt 2 / 4 : ℝ) : EReal) := by
  sorry

/-- formal-conjectures `erdos_33.variants.vanDoorn` (bound `2φ^{5/2} ≈ 6.66`), restated;
it follows from the new bound since `13√2/4 < 2φ^{5/2}`. -/
theorem erdos33_vanDoorn :
    ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
      ((A.1 ∩ Icc 1 N).ncard : EReal) / (Real.sqrt N : EReal)) ≤
        ((2 * (Real.goldenRatio ^ ((5 : ℝ) / 2)) : ℝ) : EReal) := by
  sorry

/-- Sanity check: the new constant is strictly smaller than van Doorn's `2φ^{5/2}`. -/
theorem new_const_lt_vanDoorn :
    13 * Real.sqrt 2 / 4 < 2 * (Real.goldenRatio ^ ((5 : ℝ) / 2)) := by
  have hφ1 : (1 : ℝ) ≤ Real.goldenRatio := Real.one_lt_goldenRatio.le
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hφ : (3 : ℝ) / 2 < Real.goldenRatio := by
    rw [Real.goldenRatio]; linarith
  have hsq : Real.goldenRatio ^ (2 : ℝ) ≤ Real.goldenRatio ^ ((5 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hφ1 (by norm_num)
  have hsq' : Real.goldenRatio ^ (2 : ℝ) = Real.goldenRatio + 1 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.goldenRatio_sq]
  have h2 : Real.sqrt 2 < 3 / 2 := by
    rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith

end Blind.Erdos33
