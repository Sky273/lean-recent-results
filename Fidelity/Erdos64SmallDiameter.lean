import RecentResults.Erdos64SmallDiameter
import Mathlib

/-! Bridge: derive the blind statements of `Fidelity/Blind/Erdos64SmallDiameter.lean` (copied
verbatim, separate namespace) from our verified theorems `Erdos64Diam.carr_diam2` and
`Erdos64Diam.diam3_minDegree4`.

The name `zey9310_diam_le_three` comes from the blind formalization (`zey9310` is the GitHub
account that published issue zey9310/zey9310-math#1); it states the same result as
`Erdos64Diam.diam3_minDegree4`. -/

namespace Erdos64BlindBridge

open SimpleGraph

variable {V : Type*}

/-- Blind definition, copied verbatim. -/
def HasCycleOfLength (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = n

/-- Blind (a), proved from `Erdos64Diam.carr_diam2` (which only needs `ediam ≤ 2`). -/
theorem carr_diam_two [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdiam : G.ediam = 2) (hdeg : 3 ≤ G.minDegree) :
    HasCycleOfLength G 4 ∨ HasCycleOfLength G 8 := by
  obtain ⟨v, c, hc, h | h⟩ := Erdos64Diam.carr_diam2 (G := G) hdeg hdiam.le
  · exact Or.inl ⟨v, c, hc, h⟩
  · exact Or.inr ⟨v, c, hc, h⟩

/-- Blind (b), proved from `Erdos64Diam.diam3_minDegree4`. -/
theorem zey9310_diam_le_three [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdiam : G.ediam ≤ 3) (hdeg : 4 ≤ G.minDegree) :
    HasCycleOfLength G 4 ∨ HasCycleOfLength G 8 := by
  obtain ⟨v, c, hc, h | h⟩ := Erdos64Diam.diam3_minDegree4 (G := G) hdeg hdiam
  · exact Or.inl ⟨v, c, hc, h⟩
  · exact Or.inr ⟨v, c, hc, h⟩

/-! Converse direction (sanity): our statements follow from the blind ones, so they are not
stronger than what the sources claim. Our conclusion is equivalent to the blind one
(`concl_iff`). For (a), our hypothesis `ediam ≤ 2` is recovered from the blind `ediam = 2`
plus the case `ediam ≤ 1`, i.e. the complete graph, which has a 4-cycle once its minimum degree
is `≥ 3` (`carr_diam2_of_blind`). For (b), the hypotheses are literally the same
(`diam3_minDegree4_of_blind`). -/

theorem concl_iff (G : SimpleGraph V) :
    (∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ (c.length = 4 ∨ c.length = 8)) ↔
      (HasCycleOfLength G 4 ∨ HasCycleOfLength G 8) := by
  constructor
  · rintro ⟨v, c, hc, h | h⟩
    · exact Or.inl ⟨v, c, hc, h⟩
    · exact Or.inr ⟨v, c, hc, h⟩
  · rintro (⟨v, c, hc, h⟩ | ⟨v, c, hc, h⟩)
    · exact ⟨v, c, hc, Or.inl h⟩
    · exact ⟨v, c, hc, Or.inr h⟩

/-- The blind statement (a) for `G` (diameter exactly 2) implies the statement of
`Erdos64Diam.carr_diam2` for `G` (diameter `≤ 2`): the extra case `ediam ≤ 1` is the complete
graph, where three neighbours of any vertex give a 4-cycle. -/
theorem carr_diam2_of_blind [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (blind : G.ediam = 2 → 3 ≤ G.minDegree → HasCycleOfLength G 4 ∨ HasCycleOfLength G 8)
    (hδ : 3 ≤ G.minDegree) (hd : G.ediam ≤ 2) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ (c.length = 4 ∨ c.length = 8) := by
  rcases eq_or_lt_of_le hd with h2 | hlt
  · exact (concl_iff G).mpr (blind h2 hδ)
  · -- `ediam ≤ 1`: any two distinct vertices are adjacent
    have hadj : ∀ x y : V, x ≠ y → G.Adj x y := fun x y hxy => by
      have h1 : G.edist x y ≤ 1 := (G.edist_le_ediam).trans (Order.le_of_lt_add_one hlt)
      have h0 : G.edist x y ≠ 0 := by simpa [edist_eq_zero_iff] using hxy
      rw [← edist_eq_one_iff_adj]
      exact le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h0)
    classical
    have hne : Nonempty V := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp [SimpleGraph.minDegree_of_subsingleton] at hδ
    obtain ⟨x⟩ := hne
    have h3 : 3 ≤ G.degree x := hδ.trans (G.minDegree_le_degree x)
    obtain ⟨a, hxa, -⟩ := Erdos64Diam.exists_nbr_not_mem (G := G) x ∅ (by simp; omega)
    obtain ⟨b, hxb, hb⟩ := Erdos64Diam.exists_nbr_not_mem (G := G) x {a} (by simp; omega)
    obtain ⟨c, hxc, hc⟩ := Erdos64Diam.exists_nbr_not_mem (G := G) x {a, b}
      ((Finset.card_le_two).trans_lt (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb hc
    obtain ⟨v, p, hp, hl⟩ := Erdos64Diam.cycle4_of hxa (hadj a b (Ne.symm hb))
      (hadj b c (Ne.symm hc.2)) hxc.symm hxb.ne (Ne.symm hc.1)
    exact ⟨v, p, hp, Or.inl hl⟩

/-- The blind statement (b) for `G` implies the statement of `Erdos64Diam.diam3_minDegree4`
for `G` (same hypotheses, equivalent conclusions). -/
theorem diam3_minDegree4_of_blind [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (blind : G.ediam ≤ 3 → 4 ≤ G.minDegree → HasCycleOfLength G 4 ∨ HasCycleOfLength G 8)
    (hδ : 4 ≤ G.minDegree) (hd : G.ediam ≤ 3) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ (c.length = 4 ∨ c.length = 8) :=
  (concl_iff G).mpr (blind hd hδ)

end Erdos64BlindBridge

#print axioms Erdos64BlindBridge.carr_diam_two
#print axioms Erdos64BlindBridge.zey9310_diam_le_three
#print axioms Erdos64BlindBridge.concl_iff
#print axioms Erdos64BlindBridge.carr_diam2_of_blind
#print axioms Erdos64BlindBridge.diam3_minDegree4_of_blind
#print axioms Erdos64Diam.carr_diam2
#print axioms Erdos64Diam.diam3_minDegree4
