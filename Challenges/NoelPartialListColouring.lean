import Mathlib

/-!
# Challenge: Noel (arXiv:2609.23291), the Partial List Colouring Conjecture is false

Statement-only file for `lake comparator`: it imports only Mathlib, contains the definitions the
statements depend on, and states the theorems with `sorry`. The proofs are in
`RecentResults/NoelPartialListColouring.lean`; `comparator/NoelPartialListColouring.json` checks
that they prove exactly these statements with the standard axioms only.
-/

open Finset

namespace Noel

/-- `G` is `k`-choosable (verbatim from formal-conjectures,
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/List.lean` @ 2a315101). -/
def IsKChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) → ∃ C : G.Coloring ℕ, ∀ v, C v ∈ L v

/-- The list chromatic number (verbatim from formal-conjectures, same file and commit). -/
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsKChoosable G k}

/-- `S` can be properly coloured from the lists `L` (values of `f` outside `S` are irrelevant). -/
def IsPartialLColoring {V : Type*} (G : SimpleGraph V) (L : V → Finset ℕ) (S : Finset V) : Prop :=
  ∃ f : V → ℕ, (∀ v ∈ S, f v ∈ L v) ∧ ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → f v ≠ f w

/-- The Partial List Colouring Conjecture of Albertson, Grossman and Haas (2000), as stated in
the introduction of arXiv:2609.23291, with the bound `n · (ℓ / k) ≤ |S|` written in `ℕ`. -/
def AGHConjecture : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (k ℓ : ℕ),
    listChromaticNumber G = k → 2 ≤ k → 1 ≤ ℓ → ℓ < k →
    ∀ L : V → Finset ℕ, (∀ v, (L v).card = ℓ) →
      ∃ S : Finset V, IsPartialLColoring G L S ∧ ℓ * Fintype.card V ≤ k * S.card

/-- Theorem 1.1 of arXiv:2609.23291: a graph with 14 vertices and list chromatic number 3,
with a 2-list assignment from which at most 9 vertices can be properly coloured. -/
theorem main : ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W), Fintype.card W = 14 ∧
    listChromaticNumber H = 3 ∧ ∃ M : W → Finset ℕ, (∀ v, (M v).card = 2) ∧
      ∀ S : Finset W, IsPartialLColoring H M S → S.card ≤ 9 := by
  sorry

/-- The Albertson–Grossman–Haas conjecture is false. -/
theorem not_AGH : ¬ AGHConjecture := by
  sorry

end Noel

/-! Definitions copied from facebookresearch/atlas-lean @ 8920030e
(`MathlibExt/Combinatorics/SimpleGraph/ListColoring.lean`); only the namespace differs
(upstream: `SimpleGraph`). -/

namespace AtlasLeanCopy

-- Needed for the dot notation `G.IsListColorable` in `IsChoiceNumber`.
open AtlasLeanCopy

namespace SimpleGraph

variable {V : Type*}

/-- A graph is `q`-list-colorable if every assignment of at least `q` colors to
each vertex admits a proper coloring chosen from those lists. -/
def IsListColorable (G : SimpleGraph V) (q : ℕ) : Prop :=
  ∀ (C : Type) [DecidableEq C] (lists : V → Finset C),
    (∀ v, q ≤ (lists v).card) →
      ∃ color : G.Coloring C, ∀ v, color v ∈ lists v

/-- `q` is the choice number of `G` if `G` is `q`-list-colorable but is not
list-colorable with any smaller number of colors. -/
def IsChoiceNumber (G : SimpleGraph V) (q : ℕ) : Prop :=
  G.IsListColorable q ∧ ∀ r < q, ¬G.IsListColorable r

end SimpleGraph

end AtlasLeanCopy

open AtlasLeanCopy

namespace PartialListColoringProportionalBoundWanted

/-- A vertex subset `S` is partially list-colorable from `lists` when the induced
subgraph on `S` admits a proper coloring choosing each vertex color from its list. -/
def IsPartialListColoring {V C : Type*} [DecidableEq C]
    (G : SimpleGraph V) (lists : V → Finset C) (S : Finset V) : Prop :=
  ∃ color : S → C, (∀ v : S, color v ∈ lists (v : V)) ∧
    (∀ v w : S, G.Adj (v : V) (w : V) → color v ≠ color w)

/-- Albertson–Grossman–Haas partial list colouring conjecture
(atlas-lean PartialListColoringProportionalBoundWanted). -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ),
    0 < q → G.IsChoiceNumber q →
    ∀ (t : ℕ), t ≤ q →
    ∀ (C : Type) [DecidableEq C] (lists : V → Finset C),
    (∀ v, (lists v).card = t) →
    ∃ S : Finset V, IsPartialListColoring G lists S ∧ t * Fintype.card V ≤ q * S.card

/-- Noel's example refutes atlas-lean's statement of the AGH conjecture. -/
theorem conjecture_refuted : ¬ conjecture := by
  sorry

end PartialListColoringProportionalBoundWanted

namespace PartialListColoringWanted

/-- A proper coloring of the vertex subset `S` respecting the list assignment `L`. -/
def IsListColoring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : V → Finset ℕ) (f : V → ℕ) (S : Finset V) : Prop :=
  (∀ v ∈ S, f v ∈ L v) ∧ ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → f v ≠ f w

/-- `lambdaMax G L` is `λ_L`: the maximum number of vertices of `G` colorable
with respect to the list assignment `L`. -/
noncomputable def lambdaMax {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : V → Finset ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset V, ∃ f : V → ℕ, S.card = k ∧ IsListColoring G L f S}

/-- `lambdaMin G t` is `λ_t`: the minimum of `λ_L` over all list assignments
`L` with every list of size `t`. -/
noncomputable def lambdaMin {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ L : V → Finset ℕ, (∀ v, (L v).card = t) ∧ lambdaMax G L = k}

/-- Iradmusa's ratio-monotonicity conjecture λ_r/r ≥ λ_s/s, Open Problem Garden OPG-788
(atlas-lean PartialListColoringWanted); it implies AGH (s = χ_ℓ). -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (χ_ℓ r s : ℕ),
    G.IsChoiceNumber χ_ℓ →
    1 ≤ r → r ≤ s → s ≤ χ_ℓ →
    (lambdaMin G r : ℚ) / (r : ℚ) ≥ (lambdaMin G s : ℚ) / (s : ℚ)

/-- Noel's example refutes Iradmusa's conjecture at `χ_ℓ = 3`, `r = 2`, `s = 3`. -/
theorem conjecture_refuted : ¬ conjecture := by
  sorry

end PartialListColoringWanted
