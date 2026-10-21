import Mathlib

/-!
# Blind formalization: J. A. Noel, "The Partial List Colouring Conjecture is False"
(arXiv:2609.23291v1)

Source text (abstract / Theorem 1.1):
"There exists a graph G with 14 vertices and list chromatic number equal to 3 and a
 2-list assignment L of G such that at most 9 vertices of G can be properly coloured from L."
"This disproves the conjecture of [1] since 9 < 28/3 = 14 · 2/3."

Conjecture (Albertson–Grossman–Haas, as stated in the Introduction of the source):
"if G has n vertices and list chromatic number equal to k ≥ 2 and 1 ≤ ℓ < k, then, for any
 ℓ-list assignment L of G, it is possible to properly L-colour at least n(ℓ/k) vertices."

Mathlib (this version) has no notion of list colouring / choosability, so these notions
are defined below. Colours are natural numbers.
-/

namespace NoelBlind

open SimpleGraph

variable {V : Type*}

/-- A proper colouring of `G` *from the lists* `L`: a proper colouring (Mathlib's
`G.Coloring ℕ`, i.e. adjacent vertices get distinct colours) with `C v ∈ L v` for every `v`. -/
def IsListColouring (G : SimpleGraph V) (L : V → Finset ℕ) (C : G.Coloring ℕ) : Prop :=
  ∀ v, C v ∈ L v

/-- `G` is `k`-choosable: for every list assignment with all lists of size at least `k`,
there is a proper colouring from the lists. -/
def IsChoosable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, k ≤ (L v).card) → ∃ C : G.Coloring ℕ, IsListColouring G L C

/-- The list chromatic number (choice number) of `G`: the least `k` such that `G` is
`k`-choosable (`⊤` if there is none), defined exactly like Mathlib's `chromaticNumber`. -/
noncomputable def listChromaticNumber (G : SimpleGraph V) : ℕ∞ :=
  ⨅ k ∈ {k : ℕ | IsChoosable G k}, (k : ℕ∞)

/-- A partial proper colouring from the lists `L`: the vertices of `S` are coloured by `c`
(values of `c` outside `S` are irrelevant), every coloured vertex gets a colour from its own
list, and two adjacent coloured vertices get distinct colours. "`S` can be properly coloured
from `L`" means some such `c` exists. -/
def IsPartialListColouring (G : SimpleGraph V) (L : V → Finset ℕ) (S : Finset V)
    (c : V → ℕ) : Prop :=
  (∀ v ∈ S, c v ∈ L v) ∧ ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v

/-- An `ℓ`-list assignment: every list has exactly `ℓ` colours. -/
def IsListAssignment (L : V → Finset ℕ) (ℓ : ℕ) : Prop :=
  ∀ v, (L v).card = ℓ

/-- The Partial List Colouring Conjecture of Albertson, Grossman and Haas, as stated in the
Introduction of the source: for every finite graph `G` on `n` vertices with list chromatic
number `k ≥ 2`, every `1 ≤ ℓ < k` and every `ℓ`-list assignment `L`, at least `n · (ℓ / k)`
vertices can be properly coloured from `L`. -/
def PartialListColouringConjecture : Prop :=
  ∀ (W : Type) [Fintype W] (G : SimpleGraph W) (k ℓ : ℕ),
    listChromaticNumber G = k → 2 ≤ k → 1 ≤ ℓ → ℓ < k →
    ∀ L : W → Finset ℕ, IsListAssignment L ℓ →
      ∃ (S : Finset W) (c : W → ℕ), IsPartialListColouring G L S c ∧
        (Fintype.card W : ℚ) * ((ℓ : ℚ) / (k : ℚ)) ≤ (S.card : ℚ)

/-! ## Main claim: Theorem 1.1 -/

/-- **Theorem 1.1** (Noel, arXiv:2609.23291). There exists a graph `G` with 14 vertices and
list chromatic number equal to 3 and a 2-list assignment `L` of `G` such that at most 9
vertices of `G` can be properly coloured from `L`. -/
theorem theorem_1_1 :
    ∃ G : SimpleGraph (Fin 14), listChromaticNumber G = 3 ∧
      ∃ L : Fin 14 → Finset ℕ, IsListAssignment L 2 ∧
        ∀ (S : Finset (Fin 14)) (c : Fin 14 → ℕ), IsPartialListColouring G L S c →
          S.card ≤ 9 := by
  sorry

/-- Same statement with an arbitrary 14-element vertex type ("a graph with 14 vertices"). -/
theorem theorem_1_1' :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W), Fintype.card W = 14 ∧
      listChromaticNumber G = 3 ∧
      ∃ L : W → Finset ℕ, IsListAssignment L 2 ∧
        ∀ (S : Finset W) (c : W → ℕ), IsPartialListColouring G L S c → S.card ≤ 9 := by
  sorry

/-- "This disproves the conjecture of [1] since 9 < 28/3 = 14 · 2/3." -/
theorem partialListColouringConjecture_false : ¬ PartialListColouringConjecture := by
  sorry

/-! ## The explicit counterexample of Section 2

Vertices: `Sum.inl 0 = s₁`, `Sum.inl 1 = s₂` (the terminals), and `Sum.inr (i, j)` is vertex
`j` of the triangle `T_{i+1}`; the private vertex `p_{i+1}` of `T_{i+1}` is `Sum.inr (i, 2)`.
Edges: the four triangles, plus all edges from both terminals to the non-private vertices of
each triangle; the terminals are non-adjacent and no other edges are present. -/

/-- Vertex type of the counterexample: 2 terminals and 4 triangles of 3 vertices. -/
abbrev NoelVertex := Fin 2 ⊕ (Fin 4 × Fin 3)

/-- Generating relation (symmetrized, loops removed, by `SimpleGraph.fromRel`). -/
def noelRel : NoelVertex → NoelVertex → Prop
  | .inl _, .inr (_, j) => j ≠ 2
  | .inr (i, j), .inr (i', j') => i = i' ∧ j ≠ j'
  | _, _ => False

/-- The graph `G` of Section 2. -/
def noelGraph : SimpleGraph NoelVertex := SimpleGraph.fromRel noelRel

/-- The lists of the four triangles: `T₁ ↦ {1,3}`, `T₂ ↦ {1,4}`, `T₃ ↦ {2,3}`, `T₄ ↦ {2,4}`. -/
def triangleList : Fin 4 → Finset ℕ := ![{1, 3}, {1, 4}, {2, 3}, {2, 4}]

/-- The 2-list assignment `L` of Section 2: `L(s₁) = {1,2}`, `L(s₂) = {3,4}`, and every vertex
of `T_i` gets the list of `T_i`. -/
def noelList : NoelVertex → Finset ℕ
  | .inl 0 => {1, 2}
  | .inl 1 => {3, 4}
  | .inr (i, _) => triangleList i

theorem noel_card : Fintype.card NoelVertex = 14 := by
  rfl

theorem noelList_isListAssignment : IsListAssignment noelList 2 := by
  intro v
  rcases v with a | ⟨i, j⟩
  · fin_cases a <;> rfl
  · fin_cases i <;> rfl

/-- Section 2: "it is not possible to properly colour more than 9 vertices of G from the
assignment L". -/
theorem noel_at_most_nine (S : Finset NoelVertex) (c : NoelVertex → ℕ)
    (h : IsPartialListColouring noelGraph noelList S c) : S.card ≤ 9 := by
  sorry

/-- Section 2: "G has list chromatic number equal to three". -/
theorem noel_listChromaticNumber : listChromaticNumber noelGraph = 3 := by
  sorry

/-! Sanity checks on the construction (no sorry). -/
example : ¬ noelGraph.Adj (.inl 0) (.inl 1) := by simp [noelGraph, noelRel]
example : noelGraph.Adj (.inl 0) (.inr (2, 1)) := by simp [noelGraph, noelRel]
example : ¬ noelGraph.Adj (.inl 1) (.inr (2, 2)) := by simp [noelGraph, noelRel]
example : noelGraph.Adj (.inr (3, 2)) (.inr (3, 0)) := by simp [noelGraph, noelRel]
example : ¬ noelGraph.Adj (.inr (3, 2)) (.inr (1, 0)) := by simp [noelGraph, noelRel]
example : noelList (.inr (1, 2)) = {1, 4} := rfl

end NoelBlind
