import Mathlib
import RecentResults.NoelPartialListColouring

/-!
# Fidelity bridge for `RecentResults.NoelPartialListColouring`

The blind definitions and statements are copied verbatim, with their docstrings, from
`Fidelity/Blind/NoelPartialListColouring.lean`, which was written without seeing our
formalization and is not part of the build. Only the namespace is changed
(`NoelBlind` → `NoelBridge`), and every `sorry` is replaced by a proof from the theorems of
`RecentResults.NoelPartialListColouring`. The blind declarations appear here in a different order,
interleaved with bridge lemmas.

Main bridges:
* `theorem_1_1'` and `theorem_1_1` are derived from `Noel.main`;
* `partialListColouringConjecture_false` is derived from `Noel.not_AGH` via `conj_imp_AGH`.
  Together with `AGH_imp_conj`, this shows that the blind conjecture (rational bound
  `n · (ℓ / k) ≤ |S|`, `ℕ∞`-valued list chromatic number, lists of size at least `k`) is
  equivalent to `Noel.AGHConjecture`;
* `noel_listChromaticNumber` and `noel_at_most_nine` are derived from
  `Noel.listChromaticNumber_eq_three` and `Noel.atMostNine`, after proving that the blind graph and
  list assignment are ours up to the explicit relabelling `φ`.
-/

namespace NoelBridge

open SimpleGraph

variable {V : Type*}

/-! ## Blind definitions (verbatim) -/

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

/-! ## The explicit counterexample of Section 2 (blind, verbatim)

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

/-! ## Bridge lemmas: blind notions vs. ours -/

open Finset

/-- Blind `IsChoosable` (lists of size `≥ k`) coincides with our `Noel.IsKChoosable`
(lists of size exactly `k`). -/
theorem isChoosable_iff (G : SimpleGraph V) (k : ℕ) :
    IsChoosable G k ↔ Noel.IsKChoosable G k := by
  constructor
  · intro h L hL
    obtain ⟨C, hC⟩ := h L (fun v => (hL v).ge)
    exact ⟨C, hC⟩
  · intro h L hL
    choose L' hsub hcard using fun v => exists_subset_card_eq (hL v)
    obtain ⟨C, hC⟩ := h L' hcard
    exact ⟨C, fun v => hsub v (hC v)⟩

theorem choosableSet_eq (G : SimpleGraph V) :
    {k : ℕ | IsChoosable G k} = {k : ℕ | Noel.IsKChoosable G k} :=
  Set.ext fun k => isChoosable_iff G k

/-- When our ℕ-valued list chromatic number is nonzero, the blind ℕ∞-valued one equals it. -/
theorem lcn_eq_of_ne_zero (G : SimpleGraph V) (h : Noel.listChromaticNumber G ≠ 0) :
    listChromaticNumber G = (Noel.listChromaticNumber G : ℕ∞) := by
  have hne : {k : ℕ | Noel.IsKChoosable G k}.Nonempty := by
    by_contra h'
    rw [Set.not_nonempty_iff_eq_empty] at h'
    apply h
    unfold Noel.listChromaticNumber
    rw [h', Nat.sInf_empty]
  unfold listChromaticNumber Noel.listChromaticNumber
  rw [choosableSet_eq, ENat.natCast_sInf hne]

/-- Conversely, a finite value of the blind list chromatic number is our value. -/
theorem noel_lcn_of_lcn (G : SimpleGraph V) (k : ℕ) (h : listChromaticNumber G = k) :
    Noel.listChromaticNumber G = k := by
  have hne : {k : ℕ | Noel.IsKChoosable G k}.Nonempty := by
    by_contra h'
    rw [Set.not_nonempty_iff_eq_empty] at h'
    unfold listChromaticNumber at h
    rw [choosableSet_eq, h', iInf_emptyset] at h
    exact ENat.top_ne_natCast k h
  unfold listChromaticNumber at h
  rw [choosableSet_eq, ← ENat.natCast_sInf hne] at h
  unfold Noel.listChromaticNumber
  exact_mod_cast h

/-- Blind choosability is invariant under relabelling the vertices along an equivalence. -/
theorem isChoosable_comap {W W' : Type*} (e : W' ≃ W) (H : SimpleGraph W) (k : ℕ) :
    IsChoosable (H.comap e) k ↔ IsChoosable H k := by
  constructor
  · intro h L hL
    obtain ⟨C, hC⟩ := h (L ∘ e) (fun v => hL (e v))
    refine ⟨Coloring.mk (fun w => C (e.symm w)) ?_, ?_⟩
    · intro u v huv
      apply C.valid
      simpa [SimpleGraph.comap_adj] using huv
    · intro w
      change C (e.symm w) ∈ L w
      simpa using hC (e.symm w)
  · intro h L hL
    obtain ⟨C, hC⟩ := h (L ∘ e.symm) (fun w => hL _)
    refine ⟨Coloring.mk (fun v => C (e v)) ?_, ?_⟩
    · intro u v huv
      exact C.valid huv
    · intro v
      change C (e v) ∈ L v
      simpa using hC (e v)

theorem lcn_comap {W W' : Type*} (e : W' ≃ W) (H : SimpleGraph W) :
    listChromaticNumber (H.comap e) = listChromaticNumber H := by
  unfold listChromaticNumber
  have : {k : ℕ | IsChoosable (H.comap e) k} = {k : ℕ | IsChoosable H k} :=
    Set.ext fun k => isChoosable_comap e H k
  rw [this]

/-- Partial list colourings transport along an equivalence. -/
theorem partial_comap {W W' : Type*} (e : W' ≃ W) (H : SimpleGraph W) (M : W → Finset ℕ)
    (S : Finset W') (c : W' → ℕ) (h : IsPartialListColouring (H.comap e) (M ∘ e) S c) :
    IsPartialListColouring H M (S.map e.toEmbedding) (c ∘ e.symm) := by
  constructor
  · intro v hv
    rw [Finset.mem_map_equiv] at hv
    simpa using h.1 _ hv
  · intro u hu v hv huv
    rw [Finset.mem_map_equiv] at hu hv
    exact h.2 _ hu _ hv (by simpa [SimpleGraph.comap_adj] using huv)

/-! ## Bridges for the main blind statements -/

/-- Same statement with an arbitrary 14-element vertex type ("a graph with 14 vertices").

Bridge: derived from our `Noel.main`. -/
theorem theorem_1_1' :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W), Fintype.card W = 14 ∧
      listChromaticNumber G = 3 ∧
      ∃ L : W → Finset ℕ, IsListAssignment L 2 ∧
        ∀ (S : Finset W) (c : W → ℕ), IsPartialListColouring G L S c → S.card ≤ 9 := by
  obtain ⟨W, hW, H, hcard, hlcn, M, hM, hS⟩ := Noel.main
  refine ⟨W, hW, H, hcard, ?_, M, hM, fun S c h => hS S ⟨c, h.1, h.2⟩⟩
  rw [lcn_eq_of_ne_zero H (by rw [hlcn]; norm_num), hlcn]
  rfl

/-- **Theorem 1.1** (Noel, arXiv:2609.23291). There exists a graph `G` with 14 vertices and
list chromatic number equal to 3 and a 2-list assignment `L` of `G` such that at most 9
vertices of `G` can be properly coloured from `L`.

Bridge: derived from `theorem_1_1'` by relabelling the vertices along `W ≃ Fin 14`. -/
theorem theorem_1_1 :
    ∃ G : SimpleGraph (Fin 14), listChromaticNumber G = 3 ∧
      ∃ L : Fin 14 → Finset ℕ, IsListAssignment L 2 ∧
        ∀ (S : Finset (Fin 14)) (c : Fin 14 → ℕ), IsPartialListColouring G L S c →
          S.card ≤ 9 := by
  obtain ⟨W, hW, H, hcard, hlcn, M, hM, hS⟩ := theorem_1_1'
  let e : Fin 14 ≃ W := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨H.comap e, by rw [lcn_comap, hlcn], M ∘ e, fun v => hM (e v), fun S c h => ?_⟩
  have := hS _ _ (partial_comap e H M S c h)
  simpa using this

/-- The blind conjecture implies ours (`Noel.AGHConjecture`). -/
theorem conj_imp_AGH : PartialListColouringConjecture → Noel.AGHConjecture := by
  intro h W _ G k ℓ hk h2 h1 hlt L hL
  have hk' : listChromaticNumber G = k := by
    rw [lcn_eq_of_ne_zero G (by omega), hk]
  obtain ⟨S, c, hc, hcard⟩ := h W G k ℓ hk' h2 h1 hlt L hL
  refine ⟨S, ⟨c, hc.1, hc.2⟩, ?_⟩
  have hkpos : (0 : ℚ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [mul_div_assoc', div_le_iff₀ hkpos] at hcard
  have : (ℓ : ℚ) * Fintype.card W ≤ k * S.card := by linarith
  exact_mod_cast this

/-- Our conjecture implies the blind one: the two formulations are equivalent. -/
theorem AGH_imp_conj : Noel.AGHConjecture → PartialListColouringConjecture := by
  intro h W _ G k ℓ hk h2 h1 hlt L hL
  have hk' : Noel.listChromaticNumber G = k := noel_lcn_of_lcn G k hk
  obtain ⟨S, ⟨c, hc1, hc2⟩, hcard⟩ := h W G k ℓ hk' h2 h1 hlt L hL
  refine ⟨S, c, ⟨hc1, hc2⟩, ?_⟩
  have hkpos : (0 : ℚ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [mul_div_assoc', div_le_iff₀ hkpos]
  have : (ℓ : ℚ) * Fintype.card W ≤ k * S.card := by exact_mod_cast hcard
  linarith

/-- "This disproves the conjecture of [1] since 9 < 28/3 = 14 · 2/3."

Bridge: derived from our `Noel.not_AGH`, via `conj_imp_AGH`. -/
theorem partialListColouringConjecture_false : ¬ PartialListColouringConjecture :=
  fun h => Noel.not_AGH (conj_imp_AGH h)

/-! ## The explicit Section 2 construction: blind encoding vs. ours

Blind: terminals `inl t`, triangle vertex `inr (i, j)`, private vertex `j = 2`.
Ours:  terminals `inr t`, triangle vertex `inl (i, j)`, private vertex `j = 0`.
The isomorphism swaps the summands and the indices `0 ↔ 2` inside a triangle. -/

instance : DecidableRel noelRel := fun a b => by
  rcases a with s | ⟨i, j⟩ <;> rcases b with t | ⟨i', j'⟩ <;> unfold noelRel <;> infer_instance

/-- Blind vertex ↦ our vertex. -/
def φf : NoelVertex → Noel.V
  | .inl t => .inr t
  | .inr (i, j) => .inl (i, ![2, 1, 0] j)

/-- Our vertex ↦ blind vertex (inverse of `φf`). -/
def ψf : Noel.V → NoelVertex
  | .inl (i, j) => .inr (i, ![2, 1, 0] j)
  | .inr t => .inl t

/-- The explicit relabelling between the blind vertex type and ours. -/
def φ : NoelVertex ≃ Noel.V where
  toFun := φf
  invFun := ψf
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

/-- The blind graph is our graph `Noel.G`, relabelled along `φ` (checked by `decide`). -/
theorem noelGraph_eq : noelGraph = Noel.G.comap φ := by
  ext u v
  rw [SimpleGraph.comap_adj, noelGraph, SimpleGraph.fromRel_adj]
  show _ ↔ Noel.adj (φf u) (φf v)
  revert u v
  decide

/-- The blind list assignment is our `Noel.L`, relabelled along `φ` (checked by `decide`). -/
theorem noelList_eq : noelList = Noel.L ∘ φ := by
  funext v
  revert v
  decide

/-- Section 2: "G has list chromatic number equal to three".

Bridge: derived from our `Noel.listChromaticNumber_eq_three`. -/
theorem noel_listChromaticNumber : listChromaticNumber noelGraph = 3 := by
  rw [noelGraph_eq, lcn_comap,
    lcn_eq_of_ne_zero _ (by rw [Noel.listChromaticNumber_eq_three]; norm_num),
    Noel.listChromaticNumber_eq_three]
  rfl

/-- Section 2: "it is not possible to properly colour more than 9 vertices of G from the
assignment L".

Bridge: derived from our `Noel.atMostNine`. -/
theorem noel_at_most_nine (S : Finset NoelVertex) (c : NoelVertex → ℕ)
    (h : IsPartialListColouring noelGraph noelList S c) : S.card ≤ 9 := by
  rw [noelGraph_eq, noelList_eq] at h
  have hp := partial_comap φ Noel.G Noel.L S c h
  have := Noel.atMostNine _ ⟨_, hp.1, hp.2⟩
  simpa using this

/-! Sanity checks on the construction, copied verbatim from the blind file. -/
example : ¬ noelGraph.Adj (.inl 0) (.inl 1) := by simp [noelGraph, noelRel]
example : noelGraph.Adj (.inl 0) (.inr (2, 1)) := by simp [noelGraph, noelRel]
example : ¬ noelGraph.Adj (.inl 1) (.inr (2, 2)) := by simp [noelGraph, noelRel]
example : noelGraph.Adj (.inr (3, 2)) (.inr (3, 0)) := by simp [noelGraph, noelRel]
example : ¬ noelGraph.Adj (.inr (3, 2)) (.inr (1, 0)) := by simp [noelGraph, noelRel]
example : noelList (.inr (1, 2)) = {1, 4} := rfl

end NoelBridge

#print axioms NoelBridge.theorem_1_1
#print axioms NoelBridge.theorem_1_1'
#print axioms NoelBridge.partialListColouringConjecture_false
#print axioms NoelBridge.noel_at_most_nine
#print axioms NoelBridge.noel_listChromaticNumber
#print axioms NoelBridge.noel_card
#print axioms NoelBridge.noelList_isListAssignment
#print axioms NoelBridge.AGH_imp_conj
#print axioms NoelBridge.conj_imp_AGH
