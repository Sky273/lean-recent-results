import Mathlib

/-!
# Noel (arXiv:2609.38417v2, 2026): the List Total Colouring Conjecture is false

Formalization (AI-produced: Claude, Anthropic) of the lower-bound half of the paper's
Theorem 1.1 and of the refutation of the conjecture. It follows Section 2 of the paper:
* Part A: the explicit total 4-colouring (Figure 1 and its table), checked by `decide +kernel`.
* Part B: the list assignment of Figure 2; Lemma 2.1 (`K_{2,3}`); the cross-edge lemma
  (`c(v_{i,j}v_{j,i}) ∈ S_i`); then a finite case check over the `4^4 = 256` possible values of
  `(s_1, …, s_4)` (`final_check`, by `decide +kernel`), in place of the paper's argument that
  the four sets `S_i` share a colour `t`.

Not formalized: the upper bound `χ''_ℓ(G) ≤ 5`, which the paper takes from
Juvan–Mohar–Škrekovski [7, Theorem 3.1] (every cubic graph is totally 5-choosable). The
refutation of the conjecture does not need it.

`listChromaticNumber` is an `sInf`. For every finite graph the set it is taken over is nonempty
(`setOf_isKChoosable_nonempty`, via Hall's theorem), so the junk value `sInf ∅ = 0` never occurs
for the graphs considered here.

Sanity checks on the self-written `totalGraph`: its edge–edge clause is Mathlib's `lineGraph`
(`totalGraph_adj_inr_inr`), and the formal conjecture holds for `K₂` (`ltcc_K2`), so the
statement refuted here is not false for a trivial reason.
-/

namespace NoelLTCC

open SimpleGraph

/-! ## Definitions -/

/-- `G` is `k`-choosable: for any lists of exactly `k` natural-number colours on the vertices,
some proper colouring picks every colour from its list. Body copied verbatim from
formal-conjectures, `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/List.lean`
(commit 2a315101), where it is `SimpleGraph.IsKChoosable`. -/
def IsKChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) → ∃ C : G.Coloring ℕ, ∀ v, C v ∈ L v

/-- The list chromatic number: the least `k` such that `G` is `k`-choosable. Body copied verbatim
from formal-conjectures (same file and commit), where it is `SimpleGraph.listChromaticNumber`.
Its junk value `sInf ∅ = 0` cannot occur for a finite graph (`setOf_isKChoosable_nonempty`). -/
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsKChoosable G k}

/-- The total graph `T(G)` on `V(G) ⊔ E(G)` (self-written). Two vertices are adjacent iff they
are adjacent in `G`; two edges iff they are distinct and share an endpoint (this clause is
Mathlib's `lineGraph`, see `totalGraph_adj_inr_inr`); a vertex and an edge iff the vertex is an
endpoint of the edge. A total colouring of `G` is thus a proper colouring of `T(G)`. -/
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

instance {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (totalGraph G).Adj
  | .inl u, .inl v => inferInstanceAs (Decidable (G.Adj u v))
  | .inr e, .inr f =>
      inferInstanceAs (Decidable (e ≠ f ∧ ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)))
  | .inl v, .inr e => inferInstanceAs (Decidable (v ∈ (e : Sym2 V)))
  | .inr e, .inl v => inferInstanceAs (Decidable (v ∈ (e : Sym2 V)))

/-- The total chromatic number `χ''(G)`, valued in `ℕ∞` like Mathlib's `chromaticNumber`. -/
noncomputable abbrev totalChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ∞ :=
  (totalGraph G).chromaticNumber

/-- The list total chromatic number `χ''_ℓ(G)`: the list chromatic number of `T(G)`. -/
noncomputable abbrev listTotalChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  listChromaticNumber (totalGraph G)

/-- The vertex–vertex clause of `totalGraph` is the adjacency of `G`. -/
theorem totalGraph_adj_inl_inl {V : Type*} (G : SimpleGraph V) (u v : V) :
    (totalGraph G).Adj (.inl u) (.inl v) ↔ G.Adj u v :=
  Iff.rfl

/-- The edge–edge clause of `totalGraph` is the adjacency of Mathlib's `lineGraph`. -/
theorem totalGraph_adj_inr_inr {V : Type*} (G : SimpleGraph V) (e f : G.edgeSet) :
    (totalGraph G).Adj (.inr e) (.inr f) ↔ G.lineGraph.Adj e f :=
  lineGraph_adj_iff_exists.symm

/-! ## General facts on choosability -/

/-- Monotonicity in `k`: shrink every list to `k` of its colours. -/
theorem IsKChoosable.mono {V : Type*} {G : SimpleGraph V} {k m : ℕ} (h : IsKChoosable G k)
    (hkm : k ≤ m) : IsKChoosable G m := by
  intro L hL
  have : ∀ v, ∃ t ⊆ L v, t.card = k := fun v =>
    Finset.exists_subset_card_eq (by rw [hL]; exact hkm)
  choose L' hsub hcard using this
  obtain ⟨C, hC⟩ := h L' hcard
  exact ⟨C, fun v => hsub v (hC v)⟩

/-- A `k`-choosable graph is `k`-colourable (give every vertex the list `{0, …, k-1}`); statement
and proof as in formal-conjectures (same file and commit). -/
theorem IsKChoosable.colorable {V : Type*} {G : SimpleGraph V} {k : ℕ} (h : IsKChoosable G k) :
    G.Colorable k := by
  obtain ⟨C, hC⟩ := h (fun _ => Finset.range k) (fun _ => Finset.card_range k)
  exact ⟨Coloring.mk (fun v => ⟨C v, Finset.mem_range.1 (hC v)⟩)
    fun hab heq => C.valid hab (congrArg Fin.val heq)⟩

/-- Every graph on a finite type `V` is `|V|`-choosable: lists of size `|V|` satisfy Hall's
condition, so they have an injective choice function, which is a proper colouring. -/
theorem isKChoosable_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    IsKChoosable G (Fintype.card V) := by
  classical
  intro L hL
  obtain ⟨f, hf, hfL⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective L).1 fun s => by
    rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp
    · calc s.card ≤ Fintype.card V := Finset.card_le_univ s
        _ = (L v).card := (hL v).symm
        _ ≤ (s.biUnion L).card := Finset.card_le_card (Finset.subset_biUnion_of_mem L hv)
  exact ⟨Coloring.mk f fun h => hf.ne h.ne, hfL⟩

/-- For a finite graph, the set whose `sInf` is `listChromaticNumber` is nonempty, so
`listChromaticNumber` is never the junk value `sInf ∅ = 0` there. -/
theorem setOf_isKChoosable_nonempty {V : Type*} [Finite V] (G : SimpleGraph V) :
    {k | IsKChoosable G k}.Nonempty :=
  have := Fintype.ofFinite V
  ⟨_, isKChoosable_card G⟩

/-- A finite graph is `listChromaticNumber G`-choosable. -/
theorem isKChoosable_listChromaticNumber {V : Type*} [Finite V] (G : SimpleGraph V) :
    IsKChoosable G (listChromaticNumber G) :=
  Nat.sInf_mem (setOf_isKChoosable_nonempty G)

/-! ## The graph (Section 2 of the paper; indices `0..3` stand for the paper's `1..4`)

Four copies `B_i` of `K_{2,3}` with private vertices `a_i, b_i` and terminal vertices
`v_{i,j}` (`j ≠ i`), and one cross edge `v_{i,j} v_{j,i}` for each pair `i ≠ j`. -/

/-- `a i`, `b i`: private vertices of `B_i`; `t i d`: terminal of `B_i` towards `B_(tgt i d)`. -/
inductive NV
  | a (i : Fin 4)
  | b (i : Fin 4)
  | t (i : Fin 4) (d : Fin 3)
  deriving DecidableEq, Fintype

/-- The block that the terminal `t i d` points to: `tgt i d` runs over the three `j ≠ i`. -/
def tgt (i : Fin 4) (d : Fin 3) : Fin 4 := i + (d.castSucc + 1)

/-- Adjacency of the graph, as a Boolean function: `a_i` and `b_i` are joined to the three
terminals of `B_i`, and `t i d` is joined to `t (tgt i d) d.rev` (the cross edge). -/
def adjB : NV → NV → Bool
  | .a i, .t i' _ => i == i'
  | .t i' _, .a i => i == i'
  | .b i, .t i' _ => i == i'
  | .t i' _, .b i => i == i'
  | .t i d, .t i' d' => i' == tgt i d && d' == d.rev
  | _, _ => false

/-- The counterexample graph of the paper (which notes that it is graph 27005 in House of
Graphs). -/
def NG : SimpleGraph NV where
  Adj u v := adjB u v = true
  symm.symm := by decide
  loopless.irrefl := by decide

instance : DecidableRel NG.Adj := fun u v => inferInstanceAs (Decidable (adjB u v = true))

theorem card_NV : Fintype.card NV = 20 := by decide +kernel

theorem NG_cubic : NG.IsRegularOfDegree 3 := by
  intro v; revert v; decide +kernel

/-! ## Part A: a total 4-colouring (Figure 1; paper colours `1, 2, 3, 4` are `0, 1, 2, 3`) -/

/-- The paper's table, shifted down by one: `termCol i j` is the colour of the terminal vertex
`v_{i,j}` (the diagonal is unused). -/
def termCol : Fin 4 → Fin 4 → Fin 4 :=
  ![![3, 1, 2, 0], ![0, 3, 2, 1], ![0, 1, 3, 2], ![1, 2, 0, 3]]

/-- Vertex colours: private vertices get the paper's colour 4, terminals follow the table. -/
def vcol : NV → Fin 4
  | .a _ => 3
  | .b _ => 3
  | .t i d => termCol i (tgt i d)

/-- The colour that follows (`succ3`) or precedes (`pred3`) a colour of `{0, 1, 2}` cyclically. -/
def succ3 : Fin 4 → Fin 4 := ![1, 2, 0, 3]
@[inherit_doc succ3] def pred3 : Fin 4 → Fin 4 := ![2, 0, 1, 3]

/-- Edge colours, as a symmetric function of the endpoints: `v a_i` gets the colour following
`c(v)`, `v b_i` the colour preceding it, and cross edges the paper's colour 4. -/
def ecolF : NV → NV → Fin 4
  | .a _, .t i d => succ3 (vcol (.t i d))
  | .t i d, .a _ => succ3 (vcol (.t i d))
  | .b _, .t i d => pred3 (vcol (.t i d))
  | .t i d, .b _ => pred3 (vcol (.t i d))
  | _, _ => 3

theorem ecolF_symm : ∀ u v, ecolF u v = ecolF v u := by decide

/-- The total 4-colouring of Figure 1. -/
def tcol : NV ⊕ NG.edgeSet → Fin 4
  | .inl v => vcol v
  | .inr e => Sym2.lift ⟨ecolF, ecolF_symm⟩ e

theorem tcol_valid : ∀ x y, (totalGraph NG).Adj x y → tcol x ≠ tcol y := by
  decide +kernel

theorem colorable_four : (totalGraph NG).Colorable 4 :=
  ⟨Coloring.mk tcol fun h => tcol_valid _ _ h⟩

/-! ## Named elements -/

/-- `eA i d`, `eB i d`: the edges joining `a_i`, resp. `b_i`, to the terminal `t i d`;
`eX i d`: the cross edge at `t i d`. -/
def eA (i : Fin 4) (d : Fin 3) : NG.edgeSet := ⟨s(.a i, .t i d), by simp [NG, adjB]⟩
@[inherit_doc eA]
def eB (i : Fin 4) (d : Fin 3) : NG.edgeSet := ⟨s(.b i, .t i d), by simp [NG, adjB]⟩
@[inherit_doc eA]
def eX (i : Fin 4) (d : Fin 3) : NG.edgeSet :=
  ⟨s(.t i d, .t (tgt i d) d.rev), by simp [NG, adjB]⟩

/-- The total graph of the counterexample. -/
abbrev T := totalGraph NG

/-- `a_0` and its three edges form a 4-clique of `T`, so `χ''(G) ≥ 4`. -/
theorem not_colorable_three : ¬ T.Colorable 3 := by
  rintro ⟨C⟩
  let f : Fin 4 → NV ⊕ NG.edgeSet := ![.inl (.a 0), .inr (eA 0 0), .inr (eA 0 1), .inr (eA 0 2)]
  have hf : ∀ i j, i ≠ j → T.Adj (f i) (f j) := by decide +kernel
  have hinj : Function.Injective (C ∘ f) := fun i j h => by
    by_contra hij
    exact C.valid (hf i j hij) h
  simpa using Fintype.card_le_of_injective _ hinj

/-- `χ''(G) = 4`. -/
theorem totalChromaticNumber_NG : totalChromaticNumber NG = 4 := by
  have := (chromaticNumber_eq_iff_colorable_not_colorable (G := T) (n := 3)).2
    ⟨colorable_four, not_colorable_three⟩
  exact this.trans (by norm_num)

/-! ## Part B: the list assignment (Figure 2); paper colours `1..5`, block `i` is paper `i+1`. -/

/-- The list `{1, …, 5} \ {i + 1}` of every vertex and edge of the block `B_i` (the paper's
`{1, …, 5} \ {p}` for its block `B_p`, `p = i + 1`). -/
def blockL (i : Fin 4) : Finset ℕ := ({1, 2, 3, 4, 5} : Finset ℕ).erase (i.val + 1)

/-- The colour missing from the list of the cross edge at `t i d`. In the paper's indexing
(block `B_p` with `p = i + 1`, indices cyclic in `{1, 2, 3, 4}`): the edge from `B_p` to
`B_{p+1}` (`d = 0`) misses colour `p + 2`; the edges `B_1B_3` and `B_2B_4` (`d = 1`) miss
colour `5`; the edge from `B_p` to `B_{p-1}` (`d = 2`) is the edge from `B_{p-1}` to `B_p`, so
it misses colour `p + 1`. -/
def crossExcl (i : Fin 4) : Fin 3 → ℕ
  | 0 => (i.val + 2) % 4 + 1
  | 1 => 5
  | 2 => (i.val + 1) % 4 + 1

/-- The list `{1, …, 5} \ {crossExcl i d}` of the cross edge at `t i d`. -/
def crossL (i : Fin 4) (d : Fin 3) : Finset ℕ := ({1, 2, 3, 4, 5} : Finset ℕ).erase (crossExcl i d)

/-- Lists of the edges, as a symmetric function of the endpoints (pairs that are not edges get
an arbitrary 4-element list). -/
def lF : NV → NV → Finset ℕ
  | .a i, .t _ _ => blockL i
  | .t _ _, .a i => blockL i
  | .b i, .t _ _ => blockL i
  | .t _ _, .b i => blockL i
  | .t i d, .t i' d' => if i' = tgt i d ∧ d' = d.rev then crossL i d else {1, 2, 3, 4}
  | _, _ => {1, 2, 3, 4}

theorem lF_symm : ∀ u v, lF u v = lF v u := by decide +kernel

theorem lF_card : ∀ u v, (lF u v).card = 4 := by decide +kernel

/-- The list assignment `L` of Figure 2. -/
def L : NV ⊕ NG.edgeSet → Finset ℕ
  | .inl (.a i) => blockL i
  | .inl (.b i) => blockL i
  | .inl (.t i _) => blockL i
  | .inr e => Sym2.lift ⟨lF, lF_symm⟩ e

theorem L_card : ∀ x, (L x).card = 4 := by
  rintro (v | ⟨e, he⟩)
  · revert v; decide +kernel
  · show (Sym2.lift ⟨lF, lF_symm⟩ e).card = 4
    clear he
    induction e using Sym2.ind with
    | _ u v => exact lF_card u v

theorem fin3_aux : ∀ p q k l : Fin 3, k ≠ l → p ≠ k → p ≠ l → q ≠ k → q ≠ l → p = q := by
  decide

/-! ## Lemma 2.1: in a total 4-colouring of K_{2,3}, the two "private" vertices agree. -/

theorem k23 (S : Finset ℕ) (hS : S.card = 4) (ca cb : ℕ) (cv ea eb : Fin 3 → ℕ)
    (hca : ca ∈ S) (hcb : cb ∈ S) (hcv : ∀ k, cv k ∈ S) (hea : ∀ k, ea k ∈ S)
    (heb : ∀ k, eb k ∈ S)
    (h1 : ∀ k, ca ≠ cv k) (h2 : ∀ k, cb ≠ cv k) (h3 : ∀ k, ea k ≠ ca) (h4 : ∀ k, eb k ≠ cb)
    (h5 : ∀ k, ea k ≠ cv k) (h6 : ∀ k, eb k ≠ cv k)
    (h7 : Function.Injective ea) (h8 : Function.Injective eb) (h9 : ∀ k, ea k ≠ eb k) :
    ca = cb := by
  by_contra hab
  have hT : ((S.erase ca).erase cb).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hab, hcb⟩),
      Finset.card_erase_of_mem hca, hS]
  obtain ⟨k, -, l, -, hkl, hcvkl⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.univ)
      (t := (S.erase ca).erase cb) (f := cv) (by simp [hT]) (fun k _ =>
        Finset.mem_erase.2 ⟨(h2 k).symm, Finset.mem_erase.2 ⟨(h1 k).symm, hcv k⟩⟩)
  -- three distinct edge colours at a vertex avoiding its colour fill `S \ {c}`
  have surj : ∀ (e : Fin 3 → ℕ) (c : ℕ), c ∈ S → Function.Injective e → (∀ k, e k ∈ S) →
      (∀ k, e k ≠ c) → ∀ g ∈ S, g ≠ c → ∃ p, e p = g := by
    intro e c hc he hS' hne g hg hgc
    have hsub : Finset.univ.image e ⊆ S.erase c := by
      intro x hx
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_erase.2 ⟨hne p, hS' p⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_erase_of_mem hc, hS, Finset.card_image_of_injective _ he]; simp)
    obtain ⟨p, -, hp⟩ := Finset.mem_image.1 (heq ▸ Finset.mem_erase.2 ⟨hgc, hg⟩)
    exact ⟨p, hp⟩
  obtain ⟨p, hp⟩ := surj ea ca hca h7 hea h3 (cv k) (hcv k) (h1 k).symm
  obtain ⟨q, hq⟩ := surj eb cb hcb h8 heb h4 (cv k) (hcv k) (h2 k).symm
  have hpk : p ≠ k := by rintro rfl; exact h5 p hp
  have hpl : p ≠ l := by rintro rfl; exact h5 p (hp.trans hcvkl)
  have hqk : q ≠ k := by rintro rfl; exact h6 q hq
  have hql : q ≠ l := by rintro rfl; exact h6 q (hq.trans hcvkl)
  have hpq : p = q := fin3_aux p q k l hkl hpk hpl hqk hql
  exact h9 p (by rw [hp, hpq, hq])

/-! ## Cross-edge lemma: five distinct colours in `{1..5}` force `c(cross) ∈ {i, s_i}`. -/

theorem mem_blockL {i : Fin 4} {c : ℕ} : c ∈ blockL i ↔ c ≠ i.val + 1 ∧ 1 ≤ c ∧ c ≤ 5 := by
  simp only [blockL, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega

theorem mem_crossL {i : Fin 4} {d : Fin 3} {c : ℕ} : c ∈ crossL i d → 1 ≤ c ∧ c ≤ 5 := by
  simp only [crossL, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega

theorem cross_aux (n s x c1 c2 c3 : ℕ) (hn : 1 ≤ n ∧ n ≤ 5) (hs : s ≠ n ∧ 1 ≤ s ∧ s ≤ 5)
    (h1 : c1 ≠ n ∧ 1 ≤ c1 ∧ c1 ≤ 5) (h2 : c2 ≠ n ∧ 1 ≤ c2 ∧ c2 ≤ 5)
    (h3 : c3 ≠ n ∧ 1 ≤ c3 ∧ c3 ≤ 5) (hx : 1 ≤ x ∧ x ≤ 5)
    (d12 : c1 ≠ c2) (d13 : c1 ≠ c3) (d23 : c2 ≠ c3) (s1 : c1 ≠ s) (s2 : c2 ≠ s) (s3 : c3 ≠ s)
    (x1 : x ≠ c1) (x2 : x ≠ c2) (x3 : x ≠ c3) : x = n ∨ x = s := by
  omega

/-! ## Final case check: no choice of `s_i` lets all six cross edges be coloured.

This replaces the paper's last two paragraphs (the four sets `S_i = {i, s_i}` share a colour `t`;
then a case analysis on `t`) by an exhaustive check of the `4^4 = 256` choices of `s_i`. -/

theorem final_check : ∀ s0 ∈ blockL 0, ∀ s1 ∈ blockL 1, ∀ s2 ∈ blockL 2, ∀ s3 ∈ blockL 3,
    ¬ ∀ i : Fin 4, ∀ d : Fin 3, ∃ x ∈ crossL i d,
      (x = i.val + 1 ∨ x = ![s0, s1, s2, s3] i) ∧
      (x = (tgt i d).val + 1 ∨ x = ![s0, s1, s2, s3] (tgt i d)) := by
  decide +kernel

/-! ## Adjacency facts in the total graph -/

theorem adj_facts :
    (∀ i d, T.Adj (.inl (.a i)) (.inl (.t i d))) ∧
    (∀ i d, T.Adj (.inl (.b i)) (.inl (.t i d))) ∧
    (∀ i d, T.Adj (.inr (eA i d)) (.inl (.a i))) ∧
    (∀ i d, T.Adj (.inr (eB i d)) (.inl (.b i))) ∧
    (∀ i d, T.Adj (.inr (eA i d)) (.inl (.t i d))) ∧
    (∀ i d, T.Adj (.inr (eB i d)) (.inl (.t i d))) ∧
    (∀ i d d', d ≠ d' → T.Adj (.inr (eA i d)) (.inr (eA i d'))) ∧
    (∀ i d d', d ≠ d' → T.Adj (.inr (eB i d)) (.inr (eB i d'))) ∧
    (∀ i d, T.Adj (.inr (eA i d)) (.inr (eB i d))) ∧
    (∀ i d, T.Adj (.inr (eX i d)) (.inl (.t i d))) ∧
    (∀ i d, T.Adj (.inr (eX i d)) (.inr (eA i d))) ∧
    (∀ i d, T.Adj (.inr (eX i d)) (.inr (eB i d))) := by
  decide +kernel

theorem eX_rev : ∀ i d, eX (tgt i d) d.rev = eX i d := by decide +kernel

/-- The total graph of the counterexample is not 4-choosable: it cannot be coloured from `L`. -/
theorem not_choosable_four : ¬ IsKChoosable T 4 := by
  intro h
  obtain ⟨C, hC⟩ := h L L_card
  obtain ⟨A1, A2, A3, A4, A5, A6, A7, A8, A9, X1, X2, X3⟩ := adj_facts
  have hA : ∀ i, C (.inl (.a i)) ∈ blockL i := fun i => hC (.inl (.a i))
  have hB : ∀ i, C (.inl (.b i)) ∈ blockL i := fun i => hC (.inl (.b i))
  have hT : ∀ i d, C (.inl (.t i d)) ∈ blockL i := fun i d => hC (.inl (.t i d))
  have hEA : ∀ i d, C (.inr (eA i d)) ∈ blockL i := fun i d => hC (.inr (eA i d))
  have hEB : ∀ i d, C (.inr (eB i d)) ∈ blockL i := fun i d => hC (.inr (eB i d))
  have hEX : ∀ i d, C (.inr (eX i d)) ∈ crossL i d := fun i d => by
    simpa [L, eX, lF] using hC (.inr (eX i d))
  have card_blockL : ∀ i, (blockL i).card = 4 := by decide +kernel
  -- Lemma 2.1 in each block
  have hab : ∀ i, C (.inl (.a i)) = C (.inl (.b i)) := fun i =>
    k23 (blockL i) (card_blockL i) _ _ (fun k => C (.inl (.t i k)))
      (fun k => C (.inr (eA i k))) (fun k => C (.inr (eB i k)))
      (hA i) (hB i) (hT i) (hEA i) (hEB i)
      (fun k => C.valid (A1 i k)) (fun k => C.valid (A2 i k))
      (fun k => C.valid (A3 i k)) (fun k => C.valid (A4 i k))
      (fun k => C.valid (A5 i k)) (fun k => C.valid (A6 i k))
      (fun k l h => by by_contra hkl; exact C.valid (A7 i k l hkl) h)
      (fun k l h => by by_contra hkl; exact C.valid (A8 i k l hkl) h)
      (fun k => C.valid (A9 i k))
  -- cross-edge lemma
  have hx : ∀ i d, C (.inr (eX i d)) = i.val + 1 ∨ C (.inr (eX i d)) = C (.inl (.a i)) := by
    intro i d
    have hs := mem_blockL.1 (hA i)
    exact cross_aux (i.val + 1) _ _ (C (.inl (.t i d))) (C (.inr (eA i d))) (C (.inr (eB i d)))
      (by omega) hs (mem_blockL.1 (hT i d)) (mem_blockL.1 (hEA i d)) (mem_blockL.1 (hEB i d))
      (mem_crossL (hEX i d))
      (fun h => C.valid (A5 i d) h.symm) (fun h => C.valid (A6 i d) h.symm)
      (C.valid (A9 i d))
      (fun h => C.valid (A1 i d) h.symm) (C.valid (A3 i d))
      (by rw [hab i]; exact C.valid (A4 i d))
      (C.valid (X1 i d)) (C.valid (X2 i d)) (C.valid (X3 i d))
  have hvec : ∀ i, ![C (.inl (.a 0)), C (.inl (.a 1)), C (.inl (.a 2)), C (.inl (.a 3))] i =
      C (.inl (.a i)) := by
    intro i; fin_cases i <;> rfl
  refine final_check _ (hA 0) _ (hA 1) _ (hA 2) _ (hA 3) fun i d => ?_
  refine ⟨C (.inr (eX i d)), hEX i d, ?_, ?_⟩
  · rw [hvec]; exact hx i d
  · rw [hvec, ← eX_rev i d]; exact hx (tgt i d) d.rev

/-- `χ''_ℓ(G) ≥ 5`, stated on the invariant itself (no junk value: `T` is finite). -/
theorem five_le_listTotalChromaticNumber_NG : 5 ≤ listTotalChromaticNumber NG := by
  by_contra h
  exact not_choosable_four
    ((isKChoosable_listChromaticNumber T).mono (Nat.lt_succ_iff.1 (not_le.1 h)))

/-! ## Main results -/

/-- **Theorem 1.1 of the paper, lower-bound half.** A simple cubic graph on 20 vertices with
`χ''(G) = 4` that is not totally `k`-choosable for any `k ≤ 4`, i.e. `χ''_ℓ(G) ≥ 5`. -/
theorem exists_cubic_totalChromatic_four_not_totalChoosable_four :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      Fintype.card V = 20 ∧ G.IsRegularOfDegree 3 ∧
      totalChromaticNumber G = 4 ∧ ∀ k ≤ 4, ¬ IsKChoosable (totalGraph G) k :=
  ⟨NV, inferInstance, NG, inferInstance, card_NV, NG_cubic, totalChromaticNumber_NG,
    fun _ hk hc => not_choosable_four (hc.mono hk)⟩

/-- **The List Total Colouring Conjecture is false**: `χ''_ℓ(G) = χ''(G)` fails for a finite
simple graph. (The conjecture is stated for loopless multigraphs, so a simple counterexample
suffices.) -/
theorem list_total_colouring_conjecture_false :
    ¬ ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
        (listTotalChromaticNumber G : ℕ∞) = totalChromaticNumber G := by
  intro h
  have h1 := h NV NG
  rw [totalChromaticNumber_NG] at h1
  have h2 : listTotalChromaticNumber NG = 4 := by exact_mod_cast h1
  have h5 := five_le_listTotalChromaticNumber_NG
  omega

/-! ## Sanity check: the formal conjecture holds for `K₂` (`χ'' = χ''_ℓ = 3`)

So the formal statement refuted above is not false for a trivial reason. -/

/-- `T(K₂)` has three elements: the two vertices and the edge of `K₂`. -/
theorem K2_card : Fintype.card (Fin 2 ⊕ (⊤ : SimpleGraph (Fin 2)).edgeSet) = 3 := by
  decide +kernel

/-- `T(K₂)` is a triangle, so it is not 2-colourable. -/
theorem K2_not_colorable_two : ¬ (totalGraph (⊤ : SimpleGraph (Fin 2))).Colorable 2 := by
  rintro ⟨C⟩
  let e : (⊤ : SimpleGraph (Fin 2)).edgeSet := ⟨s(0, 1), by simp⟩
  let f : Fin 3 → Fin 2 ⊕ (⊤ : SimpleGraph (Fin 2)).edgeSet := ![.inl 0, .inl 1, .inr e]
  have hf : ∀ i j, i ≠ j → (totalGraph (⊤ : SimpleGraph (Fin 2))).Adj (f i) (f j) := by
    decide +kernel
  have hinj : Function.Injective (C ∘ f) := fun i j h => by
    by_contra hij
    exact C.valid (hf i j hij) h
  simpa using Fintype.card_le_of_injective _ hinj

/-- The formal LTCC holds for `K₂`: `χ''_ℓ(K₂) = χ''(K₂) = 3`. -/
theorem ltcc_K2 :
    (listTotalChromaticNumber (⊤ : SimpleGraph (Fin 2)) : ℕ∞) =
      totalChromaticNumber (⊤ : SimpleGraph (Fin 2)) := by
  have h3 : IsKChoosable (totalGraph (⊤ : SimpleGraph (Fin 2))) 3 :=
    K2_card ▸ isKChoosable_card _
  have hl : listTotalChromaticNumber (⊤ : SimpleGraph (Fin 2)) = 3 :=
    le_antisymm (Nat.sInf_le h3) (le_csInf ⟨3, h3⟩ fun k hk => by
      by_contra hlt
      exact K2_not_colorable_two (hk.mono (show k ≤ 2 by omega)).colorable)
  have hc : totalChromaticNumber (⊤ : SimpleGraph (Fin 2)) = 3 :=
    (chromaticNumber_eq_iff_colorable_not_colorable (n := 2)).2
      ⟨h3.colorable, K2_not_colorable_two⟩
  rw [hl, hc]; rfl

end NoelLTCC

#print axioms NoelLTCC.exists_cubic_totalChromatic_four_not_totalChoosable_four
#print axioms NoelLTCC.list_total_colouring_conjecture_false
#print axioms NoelLTCC.five_le_listTotalChromaticNumber_NG
#print axioms NoelLTCC.ltcc_K2
