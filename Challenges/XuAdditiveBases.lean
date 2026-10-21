import Mathlib

/-!
# Challenge: Xu (arXiv:2605.10771), the strengthened Bukh–van Hintum–Keevash conjecture

Statement-only file for `lake comparator`: it imports only Mathlib, contains the definitions the
statements depend on, and states the theorems with `sorry`. The proofs are in
`RecentResults/XuAdditiveBases.lean`; `comparator/XuAdditiveBases.json` checks that they prove
exactly these statements with the standard axioms only.
-/

open Finset
open scoped Pointwise

namespace XuBvHK

/-- **Theorem 1.1** (Xu, arXiv:2605.10771): if `S` is a basis of `ℝⁿ`, `S + S ⊆ A + B`,
`0 ≤ t ≤ n − 1` and `|A| ≤ n − t`, then `|B| ≥ n + C(t+1, 2)`. -/
theorem theorem_1_1
    (n : ℕ) (S : Module.Basis (Fin n) ℝ (Fin n → ℝ)) (A B : Set (Fin n → ℝ))
    (hcontains : (Set.range S + Set.range S : Set (Fin n → ℝ)) ⊆ A + B)
    (t : ℕ) (ht : t < n) (hA : A.encard ≤ ((n - t : ℕ) : ℕ∞)) :
    ((n + (t + 1).choose 2 : ℕ) : ℕ∞) ≤ B.encard := by
  sorry

/-- **Sharpness of Theorem 1.1**: the bound is attained for every basis `S` and every `t < n`. -/
theorem theorem_1_1_sharp
    (n : ℕ) (S : Module.Basis (Fin n) ℝ (Fin n → ℝ)) (t : ℕ) (ht : t < n) :
    ∃ A B : Set (Fin n → ℝ),
      (Set.range S + Set.range S : Set (Fin n → ℝ)) ⊆ A + B ∧
      A.encard = ((n - t : ℕ) : ℕ∞) ∧ B.encard = ((n + (t + 1).choose 2 : ℕ) : ℕ∞) := by
  sorry

/-- **Corollary 1.2** (Xu): the extension of BvHK Conjecture 13 (arXiv:2409.07442) in the
rational vector model. -/
theorem corollary_1_2
    (n : ℕ) (A B : Set (Fin n → ℚ))
    (hcontains : ∀ i j : Fin n, i ≤ j →
      (Pi.single i 1 + Pi.single j 1 : Fin n → ℚ) ∈ A + B)
    (t : ℕ) (ht : t < n) (hA : A.encard ≤ ((n - t : ℕ) : ℕ∞)) :
    ((n + (t + 1).choose 2 : ℕ) : ℕ∞) ≤ B.encard := by
  sorry

end XuBvHK

namespace XuBvHK.Check

/-- plby's coordinate model of `ℝⁿ` (verbatim from plby/lean-proofs). -/
abbrev RealSpace (n : ℕ) : Type := Fin n → ℝ

/-- **Bukh's question, sum form** (`|A| + |B| ≥ 2n` over `ℝⁿ`, arbitrary basis `S`): the
statement of `BasisSubset.basis_sumset_cardinality_bound` in plby/lean-proofs. -/
theorem basis_sumset_cardinality_bound
    (n : ℕ) (S : Module.Basis (Fin n) ℝ (RealSpace n)) (A B : Set (RealSpace n))
    (hcontains : (Set.range S + Set.range S : Set (RealSpace n)) ⊆ A + B) :
    (2 * n : ℕ∞) ≤ A.encard + B.encard := by
  sorry

end XuBvHK.Check
