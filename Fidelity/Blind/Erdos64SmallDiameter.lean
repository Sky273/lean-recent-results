import Mathlib

/-!
# Two results toward Erdős Problem #64 (Erdős–Gyárfás), blind formalization

Erdős #64 (erdosproblems.com/64): "Does every finite graph with minimum degree at least 3
contain a cycle of length 2^k for some k ≥ 2?"

(a) A. Carr, "Cycles of Length 4 or 8 in Graphs with Diameter 2 and Minimum Degree at
    Least 3", arXiv:2508.19302 (v4), Theorem 1.1:
    "Let G be a graph with diameter 2 and minimum degree at least 3. Then G contains a
     cycle of length 4 or 8."
    Preliminaries: "All graphs considered in this note are finite, simple, and undirected."
    Diameter = max over pairs of the distance (length of a shortest path).
    A cycle of length k = a sequence v₀, …, v_{k-1}, v₀ of distinct v₀,…,v_{k-1} with
    consecutive vertices adjacent (indices mod k).

(b) GitHub issue zey9310/zey9310-math#1 (2026-10-02), title "Partial result on Erdős #64:
    graphs of diameter ≤ 3 and minimum degree ≥ 4 contain a 4-cycle or an 8-cycle".
    Theorem: "Every finite graph with minimum degree at least 4 and diameter at most 3
    contains a cycle of length 4 or 8."

Modelling choices:
* "finite simple undirected graph" = `G : SimpleGraph V` with `[Fintype V]`.
* "minimum degree" = Mathlib's `G.minDegree` (which is `0` on the empty vertex type, so the
  null graph is automatically excluded by `3 ≤ G.minDegree` / `4 ≤ G.minDegree`).
* "diameter" = Mathlib's extended diameter `G.ediam : ℕ∞` (supremum of `G.edist`, which is
  `⊤` for disconnected graphs). Hence `G.ediam = 2` / `G.ediam ≤ 3` force connectedness,
  matching the informal convention that the diameter is a finite maximum of distances.
  (We avoid `G.diam : ℕ`, whose junk value `0` on disconnected graphs would make
  `G.diam ≤ 3` true for every disconnected graph.)
* "cycle of length k" = a closed walk `c : G.Walk v v` with `c.IsCycle` and
  `c.length = k`. For k ≥ 3 this is exactly Carr's definition (k distinct vertices,
  cyclically consecutive ones adjacent).
-/

namespace Erdos64Blind

open SimpleGraph

variable {V : Type*}

/-- `G` contains a cycle of length `n` (as a walk-cycle, i.e. `n` distinct vertices,
cyclically consecutive ones adjacent, `n ≥ 3`). -/
def HasCycleOfLength (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = n

/-- (a) Carr, arXiv:2508.19302, Theorem 1.1: every finite simple graph of diameter
(exactly) 2 and minimum degree at least 3 contains a cycle of length 4 or 8. -/
theorem carr_diam_two [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdiam : G.ediam = 2) (hdeg : 3 ≤ G.minDegree) :
    HasCycleOfLength G 4 ∨ HasCycleOfLength G 8 := by
  sorry

/-- (b) Claim of GitHub issue zey9310/zey9310-math#1: every finite (simple) graph with
minimum degree at least 4 and diameter at most 3 contains a cycle of length 4 or 8. -/
theorem zey9310_diam_le_three [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdiam : G.ediam ≤ 3) (hdeg : 4 ≤ G.minDegree) :
    HasCycleOfLength G 4 ∨ HasCycleOfLength G 8 := by
  sorry

/-! ### Sanity checks on the encoding (fully proved) -/

/-- A finite diameter bound forces connectedness (for a nonempty vertex type). -/
example [Nonempty V] (G : SimpleGraph V) (h : G.ediam ≤ 3) : G.Connected := by
  apply SimpleGraph.connected_of_ediam_ne_top
  intro htop
  rw [htop] at h
  exact absurd h (by decide)

/-- With `minDegree`, the empty vertex type is excluded by the degree hypothesis. -/
example [Fintype V] [IsEmpty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.minDegree = 0 := by
  simp [SimpleGraph.minDegree]

end Erdos64Blind
