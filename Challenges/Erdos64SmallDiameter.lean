import Mathlib

/-!
# Challenge: Erdős Problem 64 in small diameter (Carr, arXiv:2508.19302; proof claim #383)

Statement-only file for `lake comparator`: it imports only Mathlib, contains the definitions the
statements depend on (none here: the statements use Mathlib notions only), and states the
theorems with `sorry`. The proofs are in `RecentResults/Erdos64SmallDiameter.lean`;
`comparator/Erdos64SmallDiameter.json` checks that they prove exactly these statements with the
standard axioms only.
-/

open SimpleGraph

namespace Erdos64Diam

variable {V : Type*} {G : SimpleGraph V}

variable [Fintype V] [DecidableRel G.Adj]

/-- **Diameter `≤ 3`, minimum degree `≥ 4`**: a finite graph with minimum degree `≥ 4` and
diameter `≤ 3` contains a cycle of length 4 or 8 (proof claim #383 on erdosproblems.com). -/
theorem diam3_minDegree4 (hδ : 4 ≤ G.minDegree) (hd : G.ediam ≤ 3) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ (c.length = 4 ∨ c.length = 8) := by
  sorry

/-- **Carr's theorem** (A. Carr, arXiv:2508.19302, Theorem 1.1): a finite graph with minimum
degree `≥ 3` and diameter `≤ 2` contains a cycle of length 4 or 8. -/
theorem carr_diam2 (hδ : 3 ≤ G.minDegree) (hd : G.ediam ≤ 2) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ (c.length = 4 ∨ c.length = 8) := by
  sorry

/-- `diam3_minDegree4` with its conclusion in the form of formal-conjectures'
`Erdos64.erdos_64` (a cycle of length `2 ^ k` with `k ≥ 2`). -/
theorem erdos_64_of_diam3 (hδ : 4 ≤ G.minDegree) (hd : G.ediam ≤ 3) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  sorry

/-- Carr's theorem with its conclusion in the form of formal-conjectures' `Erdos64.erdos_64`
(a cycle of length `2 ^ k` with `k ≥ 2`). -/
theorem erdos_64_of_diam2 (hδ : 3 ≤ G.minDegree) (hd : G.ediam ≤ 2) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  sorry

end Erdos64Diam
