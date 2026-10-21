import Mathlib

/-!
# Challenge: Noel (arXiv:2609.38417), the List Total Colouring Conjecture is false

Statement-only file for `lake comparator`: it imports only Mathlib, contains the definitions the
statements depend on, and states the theorems with `sorry`. The proofs are in
`RecentResults/NoelListTotalColouring.lean`; `comparator/NoelListTotalColouring.json` checks that
they prove exactly these statements with the standard axioms only.
-/

namespace NoelLTCC

open SimpleGraph

/-- `G` is `k`-choosable (verbatim from formal-conjectures,
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/List.lean` @ 2a315101). -/
def IsKChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) → ∃ C : G.Coloring ℕ, ∀ v, C v ∈ L v

/-- The list chromatic number (verbatim from formal-conjectures, same file and commit). -/
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsKChoosable G k}

/-- The total graph `T(G)` on `V(G) ⊔ E(G)`: vertices adjacent as in `G`; two distinct edges
adjacent iff they share an endpoint; a vertex and an edge adjacent iff the vertex is an endpoint.
A total colouring of `G` is a proper colouring of `T(G)`. -/
def totalGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph (V ⊕ G.edgeSet) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inr e, .inr f => e ≠ f ∧ ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)
    | .inl v, .inr e => v ∈ (e : Sym2 V)
    | .inr e, .inl v => v ∈ (e : Sym2 V)
  symm.symm
    | .inl _, .inl _, h => G.adj_symm h
    | .inl _, .inr _, h => h
    | .inr _, .inl _, h => h
    | .inr _, .inr _, h => ⟨Ne.symm h.1, h.2.imp fun _ h => h.symm⟩
  loopless.irrefl
    | .inl u, h => G.loopless.irrefl u h
    | .inr _, h => h.1 rfl

/-- The total chromatic number `χ''(G)`. -/
noncomputable abbrev totalChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ∞ :=
  (totalGraph G).chromaticNumber

/-- The list total chromatic number `χ''_ℓ(G)`. -/
noncomputable abbrev listTotalChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  listChromaticNumber (totalGraph G)

/-- There is a cubic graph on 20 vertices with `χ''(G) = 4` that is not totally `k`-choosable for
any `k ≤ 4` (so `χ''_ℓ(G) ≥ 5`). -/
theorem exists_cubic_totalChromatic_four_not_totalChoosable_four :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      Fintype.card V = 20 ∧ G.IsRegularOfDegree 3 ∧
      totalChromaticNumber G = 4 ∧ ∀ k ≤ 4, ¬ IsKChoosable (totalGraph G) k := by
  sorry

/-- The List Total Colouring Conjecture `χ''_ℓ(G) = χ''(G)` is false. -/
theorem list_total_colouring_conjecture_false :
    ¬ ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
        (listTotalChromaticNumber G : ℕ∞) = totalChromaticNumber G := by
  sorry

end NoelLTCC
