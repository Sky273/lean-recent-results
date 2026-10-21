import Mathlib

/-!
# Blind formalization: J. A. Noel, "The List Total Colouring Conjecture is False"
(arXiv:2609.38417, v2).

Source definitions (Introduction):
* "A total colouring of a loopless multigraph G assigns a colour to each vertex and edge so
  that adjacent vertices receive different colours, edges sharing an endpoint receive different
  colours, and each edge receives a colour different from those of its endpoints."
* The total chromatic number χ''(G) "is the minimum number of colours in any total colouring".
* The list total chromatic number χ''_ℓ(G) "is the minimum k such that, for every assignment of
  lists of k colours to the vertices and edges of G, there exists a total colouring in which
  each vertex and edge receives a colour from its list."
* LTCC: every multigraph G satisfies χ''_ℓ(G) = χ''(G).

Main result (Theorem 1.1): "There exists a simple cubic graph G on 20 vertices such that
χ''(G) = 4 and χ''_ℓ(G) = 5."
-/

open SimpleGraph

namespace NoelLTCC

variable {V : Type*}

/-- The objects coloured by a total colouring: the vertices and the edges of `G`. -/
abbrev TotalElem (G : SimpleGraph V) := V ⊕ G.edgeSet

/-- A total colouring of `G` (colours in an arbitrary type `α`), with exactly the three
conditions of the source:
1. adjacent vertices receive different colours;
2. (distinct) edges sharing an endpoint receive different colours;
3. each edge receives a colour different from those of its endpoints. -/
def IsTotalColouring (G : SimpleGraph V) {α : Type*} (c : TotalElem G → α) : Prop :=
  (∀ u v : V, G.Adj u v → c (Sum.inl u) ≠ c (Sum.inl v)) ∧
  (∀ e f : G.edgeSet, e ≠ f → (∃ v : V, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)) →
      c (Sum.inr e) ≠ c (Sum.inr f)) ∧
  (∀ (e : G.edgeSet) (v : V), v ∈ (e : Sym2 V) → c (Sum.inr e) ≠ c (Sum.inl v))

/-- Total chromatic number `χ''(G)`: the minimum number `k` of colours such that a total
colouring with colours from a `k`-element set exists. -/
noncomputable def totalChromaticNumber (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ c : TotalElem G → Fin k, IsTotalColouring G c}

/-- `G` is totally `k`-choosable: for every assignment of lists of (exactly) `k` colours to the
vertices and edges of `G`, there is a total colouring in which each vertex and edge receives a
colour from its list.  Colours are natural numbers. -/
def IsTotalChoosable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : TotalElem G → Finset ℕ, (∀ x, (L x).card = k) →
    ∃ c : TotalElem G → ℕ, (∀ x, c x ∈ L x) ∧ IsTotalColouring G c

/-- List total chromatic number `χ''_ℓ(G)`: the minimum `k` such that `G` is totally
`k`-choosable. -/
noncomputable def listTotalChromaticNumber (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsTotalChoosable G k}

/-- **Theorem 1.1** (Noel). There exists a simple cubic graph `G` on 20 vertices such that
`χ''(G) = 4` and `χ''_ℓ(G) = 5`. -/
theorem theorem_1_1 :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      Fintype.card V = 20 ∧ G.IsRegularOfDegree 3 ∧
      totalChromaticNumber G = 4 ∧ listTotalChromaticNumber G = 5 := by
  sorry

/-- Abstract / title: the List Total Colouring Conjecture is false (already among finite simple
graphs, which are in particular loopless multigraphs). -/
theorem ltcc_is_false :
    ¬ ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      listTotalChromaticNumber G = totalChromaticNumber G := by
  sorry

/-- The same result phrased without the `sInf`-defined invariants: a simple cubic 20-vertex
graph that has a total colouring with 4 colours, none with 3 colours, is not totally
4-choosable, but is totally 5-choosable. -/
theorem theorem_1_1_unfolded :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      Fintype.card V = 20 ∧ G.IsRegularOfDegree 3 ∧
      (∃ c : TotalElem G → Fin 4, IsTotalColouring G c) ∧
      (¬ ∃ c : TotalElem G → Fin 3, IsTotalColouring G c) ∧
      ¬ IsTotalChoosable G 4 ∧ IsTotalChoosable G 5 := by
  sorry

/-! ## The explicit counterexample of Section 2

Four disjoint copies `B₁,…,B₄` of `K_{2,3}`; in `Bᵢ` the 2-side is `{aᵢ, bᵢ}` and the 3-side is
`{v_{i,j} : j ≠ i}`; for each `i ≠ j` one cross edge joins `v_{i,j}` and `v_{j,i}`.
Encoding (indices `0..3` stand for the paper's `1..4`):
* `Sum.inl ⟨(i, j), _⟩` is the terminal vertex `v_{i,j}` (`i ≠ j`);
* `Sum.inr (i, 0)` is `aᵢ` and `Sum.inr (i, 1)` is `bᵢ`. -/

/-- Vertex type of the counterexample (12 terminal vertices and 8 private vertices). -/
abbrev NoelV := {p : Fin 4 × Fin 4 // p.1 ≠ p.2} ⊕ (Fin 4 × Fin 2)

/-- Adjacency of the counterexample. -/
def noelAdj : NoelV → NoelV → Prop
  | Sum.inl p, Sum.inl q => q.1.1 = p.1.2 ∧ q.1.2 = p.1.1   -- cross edge v_{i,j} v_{j,i}
  | Sum.inl p, Sum.inr a => p.1.1 = a.1                      -- v_{i,j} ~ aᵢ, bᵢ
  | Sum.inr a, Sum.inl p => p.1.1 = a.1
  | Sum.inr _, Sum.inr _ => False                            -- aᵢ, bᵢ not adjacent

/-- The graph of Section 2 (graph 27005 in House of Graphs, per the source). -/
def noelGraph : SimpleGraph NoelV where
  Adj := noelAdj
  symm := by
    constructor
    intro x y h
    rcases x with p | a <;> rcases y with q | b <;> simp only [noelAdj] at h ⊢
    · exact ⟨h.2.symm, h.1.symm⟩
    · exact h
    · exact h
  loopless := by
    constructor
    intro x h
    rcases x with p | a
    · simp only [noelAdj] at h
      exact p.2 h.2.symm
    · simp only [noelAdj] at h

instance : DecidableRel noelGraph.Adj := fun x y => by
  rcases x with p | a <;> rcases y with q | b <;>
    simp only [noelGraph, noelAdj] <;> infer_instance

/-- Sanity check: the explicit graph has 20 vertices. -/
theorem noelGraph_card : Fintype.card NoelV = 20 := by
  decide

/-- Sanity check: the explicit graph is cubic. -/
theorem noelGraph_cubic : noelGraph.IsRegularOfDegree 3 := by
  intro v
  revert v
  decide

/-- **Section 2**: the explicit graph has `χ'' = 4` and `χ''_ℓ = 5`. -/
theorem noelGraph_main :
    totalChromaticNumber noelGraph = 4 ∧ listTotalChromaticNumber noelGraph = 5 := by
  sorry

/-- **Section 2**: the explicit graph is not totally 4-choosable. -/
theorem noelGraph_not_total_four_choosable : ¬ IsTotalChoosable noelGraph 4 := by
  sorry

end NoelLTCC
