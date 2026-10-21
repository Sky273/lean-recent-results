import RecentResults.NoelListTotalColouring
import Mathlib

/-!
# Fidelity bridge: blind statements vs our `RecentResults.NoelListTotalColouring`

The blind statements are in `Fidelity/Blind/NoelListTotalColouring.lean`. Their definitions and
statements are copied verbatim (docstrings and comments omitted) into namespace `BlindNoel`
(the blind file used namespace `NoelLTCC`, which clashes with ours).
Each blind statement is either proved from our theorems, or (when it needs the
upper bound `χ''_ℓ ≤ 5`, which we do not formalize) proved *conditionally* on that
missing ingredient, with the unconditional remainder proved separately.

The blind `listTotalChromaticNumber` is an `sInf`; for a finite graph it is never the junk value
`sInf ∅ = 0` (`setOf_isTotalChoosable_nonempty`), so the lower bound `χ''_ℓ ≥ 5` is stated
directly on it (`five_le_listTotalChromaticNumber`, `noelGraph_main_lower`).
-/

open SimpleGraph

namespace BlindNoel

variable {V : Type*}

/-! ## Blind definitions (verbatim copy; docstrings and comments omitted) -/

abbrev TotalElem (G : SimpleGraph V) := V ⊕ G.edgeSet

def IsTotalColouring (G : SimpleGraph V) {α : Type*} (c : TotalElem G → α) : Prop :=
  (∀ u v : V, G.Adj u v → c (Sum.inl u) ≠ c (Sum.inl v)) ∧
  (∀ e f : G.edgeSet, e ≠ f → (∃ v : V, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)) →
      c (Sum.inr e) ≠ c (Sum.inr f)) ∧
  (∀ (e : G.edgeSet) (v : V), v ∈ (e : Sym2 V) → c (Sum.inr e) ≠ c (Sum.inl v))

noncomputable def totalChromaticNumber (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ c : TotalElem G → Fin k, IsTotalColouring G c}

def IsTotalChoosable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : TotalElem G → Finset ℕ, (∀ x, (L x).card = k) →
    ∃ c : TotalElem G → ℕ, (∀ x, c x ∈ L x) ∧ IsTotalColouring G c

noncomputable def listTotalChromaticNumber (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsTotalChoosable G k}

abbrev NoelV := {p : Fin 4 × Fin 4 // p.1 ≠ p.2} ⊕ (Fin 4 × Fin 2)

def noelAdj : NoelV → NoelV → Prop
  | Sum.inl p, Sum.inl q => q.1.1 = p.1.2 ∧ q.1.2 = p.1.1
  | Sum.inl p, Sum.inr a => p.1.1 = a.1
  | Sum.inr a, Sum.inl p => p.1.1 = a.1
  | Sum.inr _, Sum.inr _ => False

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

theorem noelGraph_card : Fintype.card NoelV = 20 := by
  decide

theorem noelGraph_cubic : noelGraph.IsRegularOfDegree 3 := by
  intro v
  revert v
  decide

/-! ## Generic bridge lemmas -/

section Generic

variable {W : Type*}

/-- The blind three-clause total colouring = proper colouring of our total graph. -/
theorem isTotalColouring_iff (G : SimpleGraph V) {α : Type*} (c : TotalElem G → α) :
    IsTotalColouring G c ↔ ∀ x y, (NoelLTCC.totalGraph G).Adj x y → c x ≠ c y := by
  constructor
  · rintro ⟨h1, h2, h3⟩ (u | e) (v | f) h
    · exact h1 u v h
    · exact (h3 f u h).symm
    · exact h3 e v h
    · exact h2 e f h.1 h.2
  · intro H
    exact ⟨fun u v h => H (.inl u) (.inl v) h,
      fun e f hne hv => H (.inr e) (.inr f) ⟨hne, hv⟩,
      fun e v hv => H (.inr e) (.inl v) hv⟩

theorem exists_isTotalColouring_iff_colorable (G : SimpleGraph V) (k : ℕ) :
    (∃ c : TotalElem G → Fin k, IsTotalColouring G c) ↔
      (NoelLTCC.totalGraph G).Colorable k := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk c fun h => (isTotalColouring_iff G c).1 hc _ _ h⟩
  · rintro ⟨C⟩
    exact ⟨C, (isTotalColouring_iff G C).2 fun x y h => C.valid h⟩

/-- Blind total `k`-choosability = our `IsKChoosable (totalGraph G) k`. -/
theorem isTotalChoosable_iff (G : SimpleGraph V) (k : ℕ) :
    IsTotalChoosable G k ↔ NoelLTCC.IsKChoosable (NoelLTCC.totalGraph G) k := by
  constructor
  · intro h L hL
    obtain ⟨c, hcL, hc⟩ := h L hL
    exact ⟨Coloring.mk c fun h => (isTotalColouring_iff G c).1 hc _ _ h, hcL⟩
  · intro h L hL
    obtain ⟨C, hC⟩ := h L hL
    exact ⟨C, hC, (isTotalColouring_iff G C).2 fun x y h => C.valid h⟩

/-- Our `ℕ∞`-valued total chromatic number determines the blind `ℕ`-valued one. -/
theorem totalChromaticNumber_eq_of (G : SimpleGraph V) (n : ℕ)
    (h : (NoelLTCC.totalGraph G).chromaticNumber = n) : totalChromaticNumber G = n := by
  have hcol : ∀ k : ℕ, (NoelLTCC.totalGraph G).Colorable k ↔ n ≤ k := by
    intro k
    rw [← chromaticNumber_le_iff_colorable, h]
    exact_mod_cast Iff.rfl
  have hS : {k : ℕ | ∃ c : TotalElem G → Fin k, IsTotalColouring G c} = {k | n ≤ k} := by
    ext k
    simp only [Set.mem_ofPred_eq]
    rw [exists_isTotalColouring_iff_colorable, hcol]
  unfold totalChromaticNumber
  rw [hS]
  exact le_antisymm (Nat.sInf_le (le_refl n)) (le_csInf ⟨n, le_refl n⟩ fun k hk => hk)

/-- The blind `ℕ`-valued list total chromatic number is our `listTotalChromaticNumber`. -/
theorem listTotalChromaticNumber_eq (G : SimpleGraph V) :
    listTotalChromaticNumber G = NoelLTCC.listTotalChromaticNumber G := by
  unfold listTotalChromaticNumber NoelLTCC.listTotalChromaticNumber NoelLTCC.listChromaticNumber
  simp only [isTotalChoosable_iff]

/-- For a finite graph the set whose `sInf` is the blind `listTotalChromaticNumber` is nonempty
(every finite graph is totally `k`-choosable for some `k`), so the junk value `0` never occurs. -/
theorem setOf_isTotalChoosable_nonempty (G : SimpleGraph V) [Finite V] :
    {k | IsTotalChoosable G k}.Nonempty := by
  obtain ⟨k, hk⟩ := NoelLTCC.setOf_isKChoosable_nonempty (NoelLTCC.totalGraph G)
  exact ⟨k, (isTotalChoosable_iff G k).2 hk⟩

/-- Not totally `k`-choosable for any `k ≤ 4` (our form) ⇒ every `k` with blind total
`k`-choosability is `≥ 5`. -/
theorem five_le_of_choosable (G : SimpleGraph V)
    (h4 : ∀ k ≤ 4, ¬ NoelLTCC.IsKChoosable (NoelLTCC.totalGraph G) k) :
    ∀ k, IsTotalChoosable G k → 5 ≤ k := by
  intro k hk
  by_contra hlt
  exact h4 k (by omega) ((isTotalChoosable_iff G k).1 hk)

/-- Same hypothesis, for a finite graph ⇒ blind `χ''_ℓ(G) ≥ 5`. -/
theorem five_le_listTotalChromaticNumber (G : SimpleGraph V) [Finite V]
    (h4 : ∀ k ≤ 4, ¬ NoelLTCC.IsKChoosable (NoelLTCC.totalGraph G) k) :
    5 ≤ listTotalChromaticNumber G :=
  five_le_of_choosable G h4 _ (Nat.sInf_mem (setOf_isTotalChoosable_nonempty G))

theorem listTotalChromaticNumber_eq_five (G : SimpleGraph V)
    (h4 : ∀ k ≤ 4, ¬ NoelLTCC.IsKChoosable (NoelLTCC.totalGraph G) k)
    (h5 : IsTotalChoosable G 5) : listTotalChromaticNumber G = 5 :=
  le_antisymm (Nat.sInf_le h5) (le_csInf ⟨5, h5⟩ (five_le_of_choosable G h4))

/-! ### Transfer along graph isomorphisms -/

def totalEquiv {G : SimpleGraph V} {H : SimpleGraph W} (ψ : G ≃g H) :
    TotalElem G ≃ TotalElem H :=
  Equiv.sumCongr ψ.toEquiv ψ.mapEdgeSet

theorem isTotalColouring_comp {G : SimpleGraph V} {H : SimpleGraph W} (ψ : G ≃g H)
    {α : Type*} {c : TotalElem H → α} (hc : IsTotalColouring H c) :
    IsTotalColouring G (c ∘ totalEquiv ψ) := by
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨fun u v h => h1 (ψ u) (ψ v) (ψ.map_adj_iff.2 h), ?_, ?_⟩
  · rintro e f hne ⟨v, hve, hvf⟩
    exact h2 (ψ.mapEdgeSet e) (ψ.mapEdgeSet f) (fun h => hne (ψ.mapEdgeSet.injective h))
      ⟨ψ v, Sym2.mem_map.2 ⟨v, hve, rfl⟩, Sym2.mem_map.2 ⟨v, hvf, rfl⟩⟩
  · intro e v hv
    exact h3 (ψ.mapEdgeSet e) (ψ v) (Sym2.mem_map.2 ⟨v, hv, rfl⟩)

theorem isTotalChoosable_of_iso {G : SimpleGraph V} {H : SimpleGraph W} (ψ : G ≃g H) {k : ℕ}
    (h : IsTotalChoosable H k) : IsTotalChoosable G k := by
  intro L hL
  obtain ⟨c, hcL, hc⟩ := h (L ∘ (totalEquiv ψ).symm) (fun x => hL _)
  refine ⟨c ∘ totalEquiv ψ, fun x => ?_, isTotalColouring_comp ψ hc⟩
  simpa using hcL (totalEquiv ψ x)

theorem isTotalChoosable_iso_iff {G : SimpleGraph V} {H : SimpleGraph W} (ψ : G ≃g H) (k : ℕ) :
    IsTotalChoosable G k ↔ IsTotalChoosable H k :=
  ⟨isTotalChoosable_of_iso ψ.symm, isTotalChoosable_of_iso ψ⟩

theorem totalChromaticNumber_iso {G : SimpleGraph V} {H : SimpleGraph W} (ψ : G ≃g H) :
    totalChromaticNumber G = totalChromaticNumber H := by
  unfold totalChromaticNumber
  congr 1
  ext k
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c ∘ totalEquiv ψ.symm, isTotalColouring_comp ψ.symm hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c ∘ totalEquiv ψ, isTotalColouring_comp ψ hc⟩

theorem listTotalChromaticNumber_iso {G : SimpleGraph V} {H : SimpleGraph W} (ψ : G ≃g H) :
    listTotalChromaticNumber G = listTotalChromaticNumber H := by
  unfold listTotalChromaticNumber
  simp only [isTotalChoosable_iso_iff ψ]

end Generic

/-! ## The blind graph `noelGraph` is isomorphic to our `NoelLTCC.NG` -/

theorem tgt_ne : ∀ (i : Fin 4) (d : Fin 3), i ≠ NoelLTCC.tgt i d := by decide

/-- `a i ↦ a_i`, `b i ↦ b_i`, `t i d ↦ v_{i, tgt i d}`. -/
def toNoel : NoelLTCC.NV → NoelV
  | .a i => Sum.inr (i, 0)
  | .b i => Sum.inr (i, 1)
  | .t i d => Sum.inl ⟨(i, NoelLTCC.tgt i d), tgt_ne i d⟩

theorem toNoel_bijective : Function.Bijective toNoel := by decide +kernel

theorem toNoel_adj :
    ∀ u v, noelGraph.Adj (toNoel u) (toNoel v) ↔ NoelLTCC.NG.Adj u v := by decide +kernel

noncomputable def isoNG : NoelLTCC.NG ≃g noelGraph where
  toEquiv := Equiv.ofBijective toNoel toNoel_bijective
  map_rel_iff' := fun {a b} => toNoel_adj a b

/-! ## Blind statements proved from our theorems -/

/-- Blind `ltcc_is_false`, PROVED from our main existential theorem. -/
theorem ltcc_is_false :
    ¬ ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      listTotalChromaticNumber G = totalChromaticNumber G := by
  intro H
  obtain ⟨V, hV, G, hG, -, -, hχ, hnot⟩ :=
    NoelLTCC.exists_cubic_totalChromatic_four_not_totalChoosable_four
  have h4 : totalChromaticNumber G = 4 :=
    totalChromaticNumber_eq_of G 4 (by exact_mod_cast hχ)
  have h := H V G
  rw [h4] at h
  have h5 := five_le_listTotalChromaticNumber G hnot
  omega

/-- Blind `noelGraph_not_total_four_choosable`, PROVED from our `not_choosable_four`
via the explicit isomorphism `NG ≃g noelGraph`. -/
theorem noelGraph_not_total_four_choosable : ¬ IsTotalChoosable noelGraph 4 := by
  rw [← isTotalChoosable_iso_iff isoNG, isTotalChoosable_iff]
  exact NoelLTCC.not_choosable_four

/-- Unconditional part of blind `noelGraph_main`: `χ'' = 4` exactly, and `χ''_ℓ ≥ 5`. -/
theorem noelGraph_main_lower :
    totalChromaticNumber noelGraph = 4 ∧
      (∀ k, IsTotalChoosable noelGraph k → 5 ≤ k) ∧
      5 ≤ listTotalChromaticNumber noelGraph := by
  have hnot : ∀ k ≤ 4, ¬ NoelLTCC.IsKChoosable (NoelLTCC.totalGraph NoelLTCC.NG) k :=
    fun k hk hc => NoelLTCC.not_choosable_four (hc.mono hk)
  refine ⟨?_, ?_, ?_⟩
  · rw [← totalChromaticNumber_iso isoNG]
    exact totalChromaticNumber_eq_of _ 4 (by exact_mod_cast NoelLTCC.totalChromaticNumber_NG)
  · intro k hk
    exact five_le_of_choosable _ hnot k ((isTotalChoosable_iso_iff isoNG k).2 hk)
  · rw [← listTotalChromaticNumber_iso isoNG]
    exact five_le_listTotalChromaticNumber _ hnot

/-- Blind `noelGraph_main`, PROVED CONDITIONALLY on the one ingredient we do not formalize:
total 5-choosability of the graph (paper: "By [7, Theorem 3.1], χ''_ℓ(G) ≤ 5"). -/
theorem noelGraph_main_of_five (h5 : IsTotalChoosable NoelLTCC.NG 5) :
    totalChromaticNumber noelGraph = 4 ∧ listTotalChromaticNumber noelGraph = 5 := by
  refine ⟨noelGraph_main_lower.1, ?_⟩
  rw [← listTotalChromaticNumber_iso isoNG]
  exact listTotalChromaticNumber_eq_five _
    (fun k hk hc => NoelLTCC.not_choosable_four (hc.mono hk)) h5

/-- Unconditional part of blind `theorem_1_1` / `theorem_1_1_unfolded`
(everything except the upper bound `χ''_ℓ ≤ 5` / total 5-choosability). -/
theorem theorem_1_1_unfolded_lower :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      Fintype.card V = 20 ∧ G.IsRegularOfDegree 3 ∧
      (∃ c : TotalElem G → Fin 4, IsTotalColouring G c) ∧
      (¬ ∃ c : TotalElem G → Fin 3, IsTotalColouring G c) ∧
      ¬ IsTotalChoosable G 4 ∧
      totalChromaticNumber G = 4 ∧
      (∀ k, IsTotalChoosable G k → 5 ≤ k) := by
  obtain ⟨V, hV, G, hG, hcard, hreg, hχ, hnot⟩ :=
    NoelLTCC.exists_cubic_totalChromatic_four_not_totalChoosable_four
  have hχ' : (NoelLTCC.totalGraph G).chromaticNumber = ((4 : ℕ) : ℕ∞) := by exact_mod_cast hχ
  refine ⟨V, hV, G, hG, hcard, hreg, ?_, ?_, ?_, totalChromaticNumber_eq_of G 4 hχ',
    five_le_of_choosable G hnot⟩
  · rw [exists_isTotalColouring_iff_colorable, ← chromaticNumber_le_iff_colorable, hχ']
  · rw [exists_isTotalColouring_iff_colorable, ← chromaticNumber_le_iff_colorable, hχ']
    norm_num
  · rw [isTotalChoosable_iff]; exact hnot 4 le_rfl

/-- Blind `theorem_1_1_unfolded`, PROVED CONDITIONALLY on total 5-choosability of our `NG`. -/
theorem theorem_1_1_unfolded_of_five (h5 : IsTotalChoosable NoelLTCC.NG 5) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      Fintype.card V = 20 ∧ G.IsRegularOfDegree 3 ∧
      (∃ c : TotalElem G → Fin 4, IsTotalColouring G c) ∧
      (¬ ∃ c : TotalElem G → Fin 3, IsTotalColouring G c) ∧
      ¬ IsTotalChoosable G 4 ∧ IsTotalChoosable G 5 := by
  refine ⟨NoelLTCC.NV, inferInstance, NoelLTCC.NG, inferInstance, NoelLTCC.card_NV,
    NoelLTCC.NG_cubic, ?_, ?_, ?_, h5⟩
  · exact (exists_isTotalColouring_iff_colorable _ 4).2 NoelLTCC.colorable_four
  · rw [exists_isTotalColouring_iff_colorable]; exact NoelLTCC.not_colorable_three
  · rw [isTotalChoosable_iff]; exact NoelLTCC.not_choosable_four

/-- Blind `theorem_1_1`, PROVED CONDITIONALLY on total 5-choosability of our `NG`. -/
theorem theorem_1_1_of_five (h5 : IsTotalChoosable NoelLTCC.NG 5) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      Fintype.card V = 20 ∧ G.IsRegularOfDegree 3 ∧
      totalChromaticNumber G = 4 ∧ listTotalChromaticNumber G = 5 := by
  refine ⟨NoelLTCC.NV, inferInstance, NoelLTCC.NG, inferInstance, NoelLTCC.card_NV,
    NoelLTCC.NG_cubic, ?_, ?_⟩
  · exact totalChromaticNumber_eq_of _ 4 (by exact_mod_cast NoelLTCC.totalChromaticNumber_NG)
  · exact listTotalChromaticNumber_eq_five _
      (fun k hk hc => NoelLTCC.not_choosable_four (hc.mono hk)) h5

/-- Same, conditional on the cited Juvan–Mohar–Škrekovski theorem in the form the paper
quotes it ("every cubic graph G satisfies χ''_ℓ(G) ≤ 5"), stated as a hypothesis. -/
theorem theorem_1_1_of_JMS
    (JMS : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree 3 → IsTotalChoosable G 5) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      Fintype.card V = 20 ∧ G.IsRegularOfDegree 3 ∧
      totalChromaticNumber G = 4 ∧ listTotalChromaticNumber G = 5 :=
  theorem_1_1_of_five (JMS _ _ NoelLTCC.NG_cubic)

/-- The gap is exactly the upper bound: given our results, blind `theorem_1_1` for our
graph is *equivalent* to its total 5-choosability. -/
theorem gap_is_exactly_five_choosability :
    listTotalChromaticNumber NoelLTCC.NG = 5 ↔ IsTotalChoosable NoelLTCC.NG 5 := by
  constructor
  · intro h
    have := Nat.sInf_mem (setOf_isTotalChoosable_nonempty NoelLTCC.NG)
    unfold listTotalChromaticNumber at h
    rwa [h] at this
  · exact listTotalChromaticNumber_eq_five _
      (fun k hk hc => NoelLTCC.not_choosable_four (hc.mono hk))

end BlindNoel

#print axioms BlindNoel.ltcc_is_false
#print axioms BlindNoel.noelGraph_not_total_four_choosable
#print axioms BlindNoel.noelGraph_main_lower
#print axioms BlindNoel.noelGraph_main_of_five
#print axioms BlindNoel.theorem_1_1_unfolded_lower
#print axioms BlindNoel.theorem_1_1_unfolded_of_five
#print axioms BlindNoel.theorem_1_1_of_five
#print axioms BlindNoel.theorem_1_1_of_JMS
#print axioms BlindNoel.gap_is_exactly_five_choosability
#print axioms BlindNoel.listTotalChromaticNumber_eq
#print axioms BlindNoel.isoNG
#print axioms BlindNoel.noelGraph_card
#print axioms BlindNoel.noelGraph_cubic
