import Mathlib

/-!
# Erdős Problem 64 (Erdős–Gyárfás) in small diameter — machine-checked

Erdős Problem 64 asks whether every finite graph of minimum degree `≥ 3` contains a cycle whose
length is a power of 2. This file proves two small-diameter cases.

* `carr_diam2` : A. Carr, *Cycles of Length 4 or 8 in Graphs with Diameter 2 and Minimum Degree
  at Least 3*, arXiv:2508.19302 (v1 2025-08-25, v4 2026-01-30), Theorem 1.1:
  min degree ≥ 3 and diameter 2 ⇒ a cycle of length 4 or 8. It is stated here for `ediam ≤ 2`,
  which only adds the complete graphs (see the converse check in
  `Fidelity/Erdos64SmallDiameter.lean`).
* `diam3_minDegree4` : min degree ≥ 4 and diameter ≤ 3 ⇒ a cycle of length 4 or 8.
  Proof claim #383 on erdosproblems.com
  (https://www.erdosproblems.com/forum/thread/64/proof-claims, submitted 2026-10-02), claimed by
  Murat Can Temeller using Claude Opus 5.5 (Anthropic); proof published in GitHub issue
  zey9310/zey9310-math#1, which states the theorem, proof, code and computations were produced
  by Claude Opus 5.5 in a session directed by @zey9310.

**Scope.** The diameter-3 result needs minimum degree `≥ 4`, not the `≥ 3` of Erdős Problem 64.
It does not settle the problem in diameter 3: diameter-3 graphs with vertices of degree 3 remain
open, as the issue itself states ("the remaining gap for diameter 3"). Among the diameter cases,
only diameter `≤ 2` is settled here under the problem's own hypothesis (Carr).

**Proofs.** The Lean proofs were written by Claude (AI) on 2026-10-21 following the informal
arguments. `diam3_minDegree4` follows the issue's case split (Case 1, and Steps 1–4 of Case 2).
`carr_diam2` does not follow Carr's case split (whether `v3 = v5`): it splits on whether the base
edge `v1v2` lies in a triangle. Carr's Claim 2.2 and his Subcases 2A/2B (2B is only sketched in
v4) are therefore not formalized as written: the 2A/2B configurations have the base edge in a
triangle and fall under the triangle case, and the triangle-free case does not need Claim 2.2.
Carr's Theorem 1.1 itself is fully verified.

Checked with Lean 4 v4.36.0-rc1 / Mathlib v4.36.0-rc1.
-/

/-! ### Shared lemmas used by both proofs -/

open SimpleGraph

namespace Erdos64Diam

variable {V : Type*} {G : SimpleGraph V}

/-- A 4-cycle from a closed sequence a-b-c-d-a with `a ≠ c`, `b ≠ d`. -/
theorem cycle4_of {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hda : G.Adj d a) (hac : a ≠ c) (hbd : b ≠ d) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = 4 := by
  refine ⟨a, .cons hab (.cons hbc (.cons hcd (.cons hda .nil))), ?_, rfl⟩
  have := hab.ne; have := hbc.ne; have := hcd.ne; have := hda.ne
  rw [Walk.cons_isCycle_iff, Walk.isPath_def]
  simp only [Walk.support_cons, Walk.support_nil, Walk.edges_cons, Walk.edges_nil,
    List.nodup_cons, List.mem_cons, List.not_mem_nil, Sym2.eq, Sym2.rel_iff']
  grind

/-- The closing edge of an 8-cycle does not reappear. -/
theorem edge_not_mem8 {v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : V}
    (h₀ : G.Adj v₀ v₁) (hnd : [v₀, v₁, v₂, v₃, v₄, v₅, v₆, v₇].Nodup) :
    s(v₀, v₁) ∉ [s(v₁, v₂), s(v₂, v₃), s(v₃, v₄), s(v₄, v₅), s(v₅, v₆), s(v₆, v₇), s(v₇, v₀)] := by
  intro h
  simp only [List.mem_cons, List.not_mem_nil, Sym2.eq_iff, or_false] at h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  have := h₀.ne
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp_all

/-- An 8-cycle from a closed sequence v₀-…-v₇-v₀ of pairwise distinct vertices. -/
theorem cycle8_of {v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : V}
    (h₀ : G.Adj v₀ v₁) (h₁ : G.Adj v₁ v₂) (h₂ : G.Adj v₂ v₃) (h₃ : G.Adj v₃ v₄)
    (h₄ : G.Adj v₄ v₅) (h₅ : G.Adj v₅ v₆) (h₆ : G.Adj v₆ v₇) (h₇ : G.Adj v₇ v₀)
    (hnd : [v₀, v₁, v₂, v₃, v₄, v₅, v₆, v₇].Nodup) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = 8 := by
  refine ⟨v₀, .cons h₀ (.cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ (.cons h₆
    (.cons h₇ .nil))))))), ?_, rfl⟩
  rw [Walk.cons_isCycle_iff, Walk.isPath_def]
  have hperm : [v₁, v₂, v₃, v₄, v₅, v₆, v₇, v₀].Perm [v₀, v₁, v₂, v₃, v₄, v₅, v₆, v₇] := by
    simpa using (List.perm_append_comm (l₁ := [v₁, v₂, v₃, v₄, v₅, v₆, v₇]) (l₂ := [v₀]))
  refine ⟨by simpa using hperm.nodup_iff.mpr hnd, ?_⟩
  simpa using edge_not_mem8 h₀ hnd

/-- Diameter ≤ 3: any two vertices are equal, adjacent, joined by a 2-path, or by a 3-walk. -/
theorem short_conn {x y : V} (h : G.edist x y ≤ 3) :
    x = y ∨ G.Adj x y ∨ (∃ w, G.Adj x w ∧ G.Adj w y) ∨
      (∃ p q, G.Adj x p ∧ G.Adj p q ∧ G.Adj q y) := by
  have hr : G.Reachable x y := reachable_of_edist_ne_top (ne_top_of_le_ne_top (by simp) h)
  obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_edist
  have hl : w.length ≤ 3 := by rw [← hw] at h; exact_mod_cast h
  match w, hl with
  | .nil, _ => exact Or.inl rfl
  | .cons h1 .nil, _ => exact Or.inr (Or.inl h1)
  | .cons h1 (.cons h2 .nil), _ => exact Or.inr (Or.inr (Or.inl ⟨_, h1, h2⟩))
  | .cons h1 (.cons h2 (.cons h3 .nil)), _ => exact Or.inr (Or.inr (Or.inr ⟨_, _, h1, h2, h3⟩))
  | .cons _ (.cons _ (.cons _ (.cons _ _))), hl => simp at hl; omega

/-- Diameter ≤ 2: two distinct non-adjacent vertices have a common neighbour. -/
theorem common_nbr_of_edist_le_two {x y : V} (h : G.edist x y ≤ 2) (hne : x ≠ y)
    (hna : ¬ G.Adj x y) : ∃ w, G.Adj x w ∧ G.Adj w y := by
  have hr : G.Reachable x y := reachable_of_edist_ne_top (ne_top_of_le_ne_top (by simp) h)
  obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_edist
  have hl : w.length ≤ 2 := by rw [← hw] at h; exact_mod_cast h
  match w, hl with
  | .nil, _ => exact absurd rfl hne
  | .cons h1 .nil, _ => exact absurd h1 hna
  | .cons h1 (.cons h2 .nil), _ => exact ⟨_, h1, h2⟩
  | .cons _ (.cons _ (.cons _ _)), hl => simp at hl

/-- Degree counting: a vertex of degree > |s| has a neighbour outside `s`. -/
theorem exists_nbr_not_mem [Fintype V] [DecidableRel G.Adj] [DecidableEq V] (v : V)
    (s : Finset V) (hs : s.card < G.degree v) : ∃ w, G.Adj v w ∧ w ∉ s := by
  by_contra hcon
  push Not at hcon
  have : G.neighborFinset v ⊆ s := fun w hw => hcon w ((G.mem_neighborFinset v w).mp hw)
  have := Finset.card_le_card this
  rw [card_neighborFinset_eq_degree] at this
  omega

/-- Pairwise distinctness of 8 vertices, hypotheses in lexicographic order. -/
theorem nodup8 {a b c d e f g h : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f) (hag : a ≠ g)
    (hah : a ≠ h) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f) (hbg : b ≠ g)
    (hbh : b ≠ h) (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f) (hcg : c ≠ g) (hch : c ≠ h)
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g) (hdh : d ≠ h) (hef : e ≠ f) (heg : e ≠ g)
    (heh : e ≠ h) (hfg : f ≠ g) (hfh : f ≠ h) (hgh : g ≠ h) :
    [a, b, c, d, e, f, g, h].Nodup := by
  simp [List.nodup_cons, *]

theorem card_pair_lt [DecidableEq V] (a b : V) : ({a, b} : Finset V).card < 3 :=
  (Finset.card_le_two).trans_lt (by norm_num)

theorem card_pair_lt4 [DecidableEq V] (a b : V) : ({a, b} : Finset V).card < 4 :=
  (Finset.card_le_two).trans_lt (by norm_num)

theorem card_triple_lt4 [DecidableEq V] (a b c : V) : ({a, b, c} : Finset V).card < 4 :=
  (Finset.card_le_three).trans_lt (by norm_num)

/-- No 4-cycle, in usable form. -/
abbrev NoC4 (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a ≠ c → b ≠ d → False

/-- No 8-cycle, in usable form. -/
abbrev NoC8 (G : SimpleGraph V) : Prop :=
  ∀ v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : V, G.Adj v₀ v₁ → G.Adj v₁ v₂ → G.Adj v₂ v₃ →
    G.Adj v₃ v₄ → G.Adj v₄ v₅ → G.Adj v₅ v₆ → G.Adj v₆ v₇ → G.Adj v₇ v₀ →
    [v₀, v₁, v₂, v₃, v₄, v₅, v₆, v₇].Nodup → False

/-- Diameter ≤ 3, in usable form. -/
abbrev ShortConn (G : SimpleGraph V) : Prop :=
  ∀ x y : V, x = y ∨ G.Adj x y ∨ (∃ w, G.Adj x w ∧ G.Adj w y) ∨
    (∃ p q, G.Adj x p ∧ G.Adj p q ∧ G.Adj q y)

/-- Minimum degree ≥ 4, in usable form. -/
abbrev Nbr4 [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (s : Finset V), s.card < 4 → ∃ w, G.Adj v w ∧ w ∉ s

/-! ### Case 1: every edge lies in a triangle -/

theorem diam3_case1 [DecidableEq V] (hC4 : NoC4 G) (hC8 : NoC8 G) (hconn : ShortConn G)
    (hnb : Nbr4 G) (htri : ∀ a b, G.Adj a b → ∃ t, G.Adj a t ∧ G.Adj b t) (x : V) : False := by
  obtain ⟨y1, hxy1, -⟩ := hnb x ∅ (by simp)
  obtain ⟨y1', hxy1', h11'⟩ := htri x y1 hxy1
  obtain ⟨y2, hxy2, hy2⟩ := hnb x {y1, y1'} (card_pair_lt4 _ _)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy2
  have n21 : y2 ≠ y1 := hy2.1
  have n21' : y2 ≠ y1' := hy2.2
  obtain ⟨y2', hxy2', h22'⟩ := htri x y2 hxy2
  have n2'1 : y2' ≠ y1 := by
    rintro rfl; exact hC4 _ _ _ _ hxy1' h11'.symm h22'.symm hxy2.symm hxy1.ne n21'.symm
  have n2'1' : y2' ≠ y1' := by
    rintro rfl; exact hC4 _ _ _ _ hxy1 h11' h22'.symm hxy2.symm hxy1'.ne n21.symm
  have a12 : ¬ G.Adj y1 y2 := fun h =>
    hC4 _ _ _ _ hxy1' h11'.symm h hxy2.symm hxy1.ne n21'.symm
  have a12' : ¬ G.Adj y1 y2' := fun h =>
    hC4 _ _ _ _ hxy1' h11'.symm h hxy2'.symm hxy1.ne n2'1'.symm
  have a1'2 : ¬ G.Adj y1' y2 := fun h =>
    hC4 _ _ _ _ hxy1 h11' h hxy2.symm hxy1'.ne n21.symm
  -- facts about "outer" neighbours of y1 and of y2
  have o1 : ∀ z, G.Adj y1 z → z ≠ x → z ≠ y1' →
      ¬ G.Adj z x ∧ ¬ G.Adj z y1' ∧ ¬ G.Adj z y2 ∧ ¬ G.Adj z y2' := by
    intro z hz hzx hz1'
    exact ⟨fun h => hC4 _ _ _ _ hxy1' h11'.symm hz h hxy1.ne hz1'.symm,
      fun h => hC4 _ _ _ _ hxy1 hz h hxy1'.symm hzx.symm h11'.ne,
      fun h => hC4 _ _ _ _ hxy1 hz h hxy2.symm hzx.symm n21.symm,
      fun h => hC4 _ _ _ _ hxy1 hz h hxy2'.symm hzx.symm n2'1.symm⟩
  have o2 : ∀ z, G.Adj y2 z → z ≠ x → z ≠ y2' →
      ¬ G.Adj z x ∧ ¬ G.Adj z y2' ∧ ¬ G.Adj z y1 ∧ ¬ G.Adj z y1' := by
    intro z hz hzx hz2'
    exact ⟨fun h => hC4 _ _ _ _ hxy2' h22'.symm hz h hxy2.ne hz2'.symm,
      fun h => hC4 _ _ _ _ hxy2 hz h hxy2'.symm hzx.symm h22'.ne,
      fun h => hC4 _ _ _ _ hxy2 hz h hxy1.symm hzx.symm n21,
      fun h => hC4 _ _ _ _ hxy2 hz h hxy1'.symm hzx.symm n21'⟩
  -- a common neighbour of two outer neighbours closes an 8-cycle through both triangles
  have L : ∀ z1 z2 w, G.Adj y1 z1 → z1 ≠ x → z1 ≠ y1' → G.Adj y2 z2 → z2 ≠ x → z2 ≠ y2' →
      G.Adj z1 w → G.Adj w z2 → False := by
    intro z1 z2 w hz1 hz1x hz11' hz2 hz2x hz22' h1w hw2
    obtain ⟨p1, p2, p3, p4⟩ := o1 z1 hz1 hz1x hz11'
    obtain ⟨q1, q2, q3, q4⟩ := o2 z2 hz2 hz2x hz22'
    exact hC8 _ _ _ _ _ _ _ _ hxy1' h11'.symm hz1 h1w hw2 hz2.symm h22' hxy2'.symm
      (nodup8 hxy1'.ne hxy1.ne hz1x.symm (by rintro rfl; exact p1 h1w) hz2x.symm hxy2.ne
        hxy2'.ne h11'.ne.symm hz11'.symm (by rintro rfl; exact p2 h1w)
        (by rintro rfl; exact a1'2 hz2.symm) n21'.symm n2'1'.symm hz1.ne
        (by rintro rfl; exact q3 hw2.symm) (by rintro rfl; exact a12 hz2.symm) n21.symm
        n2'1.symm h1w.ne (by rintro rfl; exact p3 hz2.symm) (by rintro rfl; exact a12 hz1)
        (by rintro rfl; exact a12' hz1) hw2.ne (by rintro rfl; exact p3 h1w)
        (by rintro rfl; exact p4 h1w) hz2.ne.symm hz22' h22'.ne)
  -- an edge between two outer neighbours lies in a triangle, so `L` applies
  have E : ∀ z1 z2, G.Adj y1 z1 → z1 ≠ x → z1 ≠ y1' → G.Adj y2 z2 → z2 ≠ x → z2 ≠ y2' →
      G.Adj z1 z2 → False := by
    intro z1 z2 hz1 hz1x hz11' hz2 hz2x hz22' h
    obtain ⟨t, h1t, h2t⟩ := htri z1 z2 h
    exact L z1 z2 t hz1 hz1x hz11' hz2 hz2x hz22' h1t h2t.symm
  obtain ⟨z1, hz1, hz1s⟩ := hnb y1 {x, y1'} (card_pair_lt4 _ _)
  obtain ⟨z2, hz2, hz2s⟩ := hnb y2 {x, y2'} (card_pair_lt4 _ _)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz1s hz2s
  have hz1x : z1 ≠ x := hz1s.1
  have hz11' : z1 ≠ y1' := hz1s.2
  have hz2x : z2 ≠ x := hz2s.1
  have hz22' : z2 ≠ y2' := hz2s.2
  obtain ⟨p1, p2, p3, p4⟩ := o1 z1 hz1 hz1x hz11'
  obtain ⟨q1, q2, q3, q4⟩ := o2 z2 hz2 hz2x hz22'
  rcases hconn z1 z2 with h | h | ⟨w, h1w, hw2⟩ | ⟨p, q, h1p, hpq, hq2⟩
  · rw [← h] at hz2; exact p3 hz2.symm
  · exact E z1 z2 hz1 hz1x hz11' hz2 hz2x hz22' h
  · exact L z1 z2 w hz1 hz1x hz11' hz2 hz2x hz22' h1w hw2
  · by_cases hp : p = y1
    · rw [hp] at hpq
      exact E q z2 hpq (by rintro rfl; exact q1 hq2.symm) (by rintro rfl; exact q4 hq2.symm)
        hz2 hz2x hz22' hq2
    · by_cases hq : q = y2
      · rw [hq] at hpq
        exact E z1 p hz1 hz1x hz11' hpq.symm (by rintro rfl; exact p1 h1p)
          (by rintro rfl; exact p4 h1p) h1p
      · have nq1 : q ≠ z1 := by
          rintro rfl; exact E _ _ hz1 hz1x hz11' hz2 hz2x hz22' hq2
        have np2 : p ≠ z2 := by
          rintro rfl; exact E _ _ hz1 hz1x hz11' hz2 hz2x hz22' h1p
        exact hC8 _ _ _ _ _ _ _ _ hxy1' h11'.symm hz1 h1p hpq hq2 hz2.symm hxy2.symm
          (nodup8 hxy1'.ne hxy1.ne hz1x.symm (by rintro rfl; exact p1 h1p)
            (by rintro rfl; exact q1 hq2.symm) hz2x.symm hxy2.ne h11'.ne.symm hz11'.symm
            (by rintro rfl; exact p2 h1p) (by rintro rfl; exact q4 hq2.symm)
            (by rintro rfl; exact a1'2 hz2.symm) n21'.symm hz1.ne (fun h => hp h.symm)
            (by rintro rfl; exact q3 hq2.symm) (by rintro rfl; exact a12 hz2.symm) n21.symm
            h1p.ne nq1.symm (by rintro rfl; exact p3 hz2.symm) (by rintro rfl; exact a12 hz1)
            hpq.ne np2 (by rintro rfl; exact p3 h1p) hq2.ne hq hz2.ne.symm)

/-! ### Case 2, Step 1: bridges -/

/-- `(a, b)` is a *label*: `a ∈ N(u) \ {v}`, `b ∈ N(v) \ {u}` and `a`, `b` have a common
neighbour (a *bridge*). -/
abbrev Lab (G : SimpleGraph V) (u v a b : V) : Prop :=
  G.Adj u a ∧ a ≠ v ∧ G.Adj v b ∧ b ≠ u ∧ ∃ z, G.Adj a z ∧ G.Adj z b

/-- Step 1: all labels share a coordinate, so one side has a vertex free of labels. -/
theorem diam3_step1 [DecidableEq V] (hC4 : NoC4 G) (hC8 : NoC8 G) (hnb : Nbr4 G)
    {u v : V} (huv : G.Adj u v) (hnt : ∀ t, G.Adj u t → G.Adj v t → False) :
    (∃ b, G.Adj v b ∧ b ≠ u ∧ (∀ a z, G.Adj u a → a ≠ v → G.Adj a z → ¬ G.Adj z b) ∧
      (∀ a z b', G.Adj u a → a ≠ v → G.Adj v b' → b' ≠ u → G.Adj b b' → G.Adj a z →
        ¬ G.Adj z b')) ∨
    (∃ a, G.Adj u a ∧ a ≠ v ∧ (∀ b z, G.Adj v b → b ≠ u → G.Adj b z → ¬ G.Adj z a) ∧
      (∀ b z a', G.Adj v b → b ≠ u → G.Adj u a' → a' ≠ v → G.Adj a a' → G.Adj b z →
        ¬ G.Adj z a')) := by
  -- basic facts about A = N(u) \ {v} and B = N(v) \ {u}
  have nAB : ∀ a b, G.Adj u a → a ≠ v → G.Adj v b → b ≠ u → ¬ G.Adj a b := fun a b hua hav hvb hbu h =>
    hC4 _ _ _ _ hua h hvb.symm huv.symm hbu.symm hav
  have nuB : ∀ b, G.Adj v b → ¬ G.Adj u b := fun b hvb h => hnt b h hvb
  have nvA : ∀ a, G.Adj u a → ¬ G.Adj v a := fun a hua h => hnt a hua h
  -- labels
  have two : ∀ a1 b1 a2 b2, Lab G u v a1 b1 → Lab G u v a2 b2 → a1 ≠ a2 → b1 ≠ b2 → False := by
    rintro a1 b1 a2 b2 ⟨hua1, ha1v, hvb1, hb1u, z1, ha1z, hzb1⟩
      ⟨hua2, ha2v, hvb2, hb2u, z2, ha2z, hzb2⟩ ha hb
    have z1u : z1 ≠ u := by rintro rfl; exact nuB _ hvb1 hzb1
    have z2u : z2 ≠ u := by rintro rfl; exact nuB _ hvb2 hzb2
    have z1v : z1 ≠ v := by rintro rfl; exact nvA _ hua1 ha1z.symm
    have z2v : z2 ≠ v := by rintro rfl; exact nvA _ hua2 ha2z.symm
    exact hC8 _ _ _ _ _ _ _ _ hua1 ha1z hzb1 hvb1.symm hvb2 hzb2.symm ha2z.symm hua2.symm
      (nodup8 hua1.ne z1u.symm hb1u.symm huv.ne hb2u.symm z2u.symm hua2.ne ha1z.ne
        (by rintro rfl; exact hnt _ hua1 hvb1) ha1v (by rintro rfl; exact hnt _ hua1 hvb2)
        (by rintro rfl; exact nAB _ _ hua1 ha1v hvb2 hb2u hzb2) ha hzb1.ne z1v
        (by rintro rfl; exact nAB _ _ hua1 ha1v hvb2 hb2u ha1z)
        (by rintro rfl; exact hC4 _ _ _ _ hua1 ha1z ha2z.symm hua2.symm z1u.symm ha)
        (by rintro rfl; exact nAB _ _ hua2 ha2v hvb1 hb1u hzb1) hvb1.ne.symm hb
        (by rintro rfl; exact nAB _ _ hua2 ha2v hvb1 hb1u ha2z)
        (by rintro rfl; exact hnt _ hua2 hvb1) hvb2.ne z2v.symm ha2v.symm hzb2.ne.symm
        (by rintro rfl; exact hnt _ hua2 hvb2) ha2z.ne.symm)
  -- pick a vertex of B other than b0 and not adjacent to b0 (resp. for A)
  have pickB : ∀ b0, G.Adj v b0 → ∃ b, G.Adj v b ∧ b ≠ u ∧ b ≠ b0 ∧ ¬ G.Adj b b0 := by
    intro b0 hvb0
    by_cases hp : ∃ p, G.Adj v p ∧ G.Adj b0 p
    · obtain ⟨p, hvp, hb0p⟩ := hp
      obtain ⟨b, hvb, hbs⟩ := hnb v {u, b0, p} (card_triple_lt4 _ _ _)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbs
      exact ⟨b, hvb, hbs.1, hbs.2.1,
        fun h => hC4 _ _ _ _ hvp hb0p.symm h.symm hvb.symm hvb0.ne (Ne.symm hbs.2.2)⟩
    · push Not at hp
      obtain ⟨b, hvb, hbs⟩ := hnb v {u, b0} (card_pair_lt4 _ _)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbs
      exact ⟨b, hvb, hbs.1, hbs.2, fun h => hp b hvb h.symm⟩
  have pickA : ∀ a0, G.Adj u a0 → ∃ a, G.Adj u a ∧ a ≠ v ∧ a ≠ a0 ∧ ¬ G.Adj a a0 := by
    intro a0 hua0
    by_cases hp : ∃ p, G.Adj u p ∧ G.Adj a0 p
    · obtain ⟨p, hup, ha0p⟩ := hp
      obtain ⟨a, hua, has⟩ := hnb u {v, a0, p} (card_triple_lt4 _ _ _)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at has
      exact ⟨a, hua, has.1, has.2.1,
        fun h => hC4 _ _ _ _ hup ha0p.symm h.symm hua.symm hua0.ne (Ne.symm has.2.2)⟩
    · push Not at hp
      obtain ⟨a, hua, has⟩ := hnb u {v, a0} (card_pair_lt4 _ _)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at has
      exact ⟨a, hua, has.1, has.2, fun h => hp a hua h.symm⟩
  by_cases hL : ∃ a b, Lab G u v a b
  · obtain ⟨a0, b0, hL0⟩ := hL
    by_cases hall : ∀ a b, Lab G u v a b → b = b0
    · left
      obtain ⟨b, hvb, hbu, hbb0, hnadj⟩ := pickB b0 hL0.2.2.1
      refine ⟨b, hvb, hbu, fun a z hua hav haz hzb =>
        hbb0 (hall a b ⟨hua, hav, hvb, hbu, z, haz, hzb⟩), ?_⟩
      intro a z b' hua hav hvb' hb'u hbb' haz hzb'
      have e := hall a b' ⟨hua, hav, hvb', hb'u, z, haz, hzb'⟩
      rw [e] at hbb'
      exact hnadj hbb'
    · right
      obtain ⟨a1, b1, hL1, hb1⟩ : ∃ a1 b1, Lab G u v a1 b1 ∧ b1 ≠ b0 := by
        by_contra hc
        apply hall
        intro a b hab
        by_contra hne
        exact hc ⟨a, b, hab, hne⟩
      have ha1 : a1 = a0 := by
        by_contra h
        exact two _ _ _ _ hL1 hL0 h hb1
      have hallA : ∀ a b, Lab G u v a b → a = a0 := by
        intro a b hab
        by_contra h
        rcases eq_or_ne b b0 with hb | hb
        · exact two _ _ _ _ hab hL1 (by rw [ha1]; exact h) (by rw [hb]; exact fun e => hb1 e.symm)
        · exact two _ _ _ _ hab hL0 h hb
      obtain ⟨a, hua, hav, haa0, hnadj⟩ := pickA a0 hL0.1
      refine ⟨a, hua, hav, fun b z hvb hbu hbz hza =>
        haa0 (hallA a b ⟨hua, hav, hvb, hbu, z, hza.symm, hbz.symm⟩), ?_⟩
      intro b z a' hvb hbu hua' ha'v haa' hbz hza'
      have e := hallA a' b ⟨hua', ha'v, hvb, hbu, z, hza'.symm, hbz.symm⟩
      rw [e] at haa'
      exact hnadj haa'
  · left
    have hL' : ∀ a b, ¬ Lab G u v a b := fun a b h => hL ⟨a, b, h⟩
    obtain ⟨b, hvb, hbs⟩ := hnb v {u} (by simp)
    simp only [Finset.mem_singleton] at hbs
    exact ⟨b, hvb, hbs, fun a z hua hav haz hzb => hL' a b ⟨hua, hav, hvb, hbs, z, haz, hzb⟩,
      fun a z b' hua hav hvb' hb'u _ haz hzb' => hL' a b' ⟨hua, hav, hvb', hb'u, z, haz, hzb'⟩⟩

/-! ### Case 2, Steps 2–4 (core) -/

/-- Steps 2–4 for an edge `uv` in no triangle and a vertex `b ∈ N(v) \ {u}` none of whose
neighbours in `N(v) \ {u}` (nor `b` itself) is adjacent to a neighbour of a vertex of
`N(u) \ {v}`. -/
theorem diam3_case2_core [DecidableEq V] (hC4 : NoC4 G) (hC8 : NoC8 G) (hconn : ShortConn G)
    (hnb : Nbr4 G) {u v b : V} (huv : G.Adj u v) (hnt : ∀ t, G.Adj u t → G.Adj v t → False)
    (hvb : G.Adj v b) (hbu : b ≠ u)
    (hb1 : ∀ a z, G.Adj u a → a ≠ v → G.Adj a z → ¬ G.Adj z b)
    (hb2 : ∀ a z b', G.Adj u a → a ≠ v → G.Adj v b' → b' ≠ u → G.Adj b b' → G.Adj a z →
      ¬ G.Adj z b') : False := by
  have nAB : ∀ a c, G.Adj u a → a ≠ v → G.Adj v c → c ≠ u → ¬ G.Adj a c :=
    fun a c hua hav hvc hcu h => hC4 _ _ _ _ hua h hvc.symm huv.symm hcu.symm hav
  have nvA : ∀ a, G.Adj u a → ¬ G.Adj v a := fun a hua h => hnt a hua h
  have nuB : ∀ c, G.Adj v c → ¬ G.Adj u c := fun c hvc h => hnt c h hvc
  -- children `y` of `b`: `Adj b y`, `y ≠ v`, `¬ Adj v y`
  have Yf : ∀ y, G.Adj b y → y ≠ v → ¬ G.Adj v y →
      (∀ a, G.Adj u a → a ≠ v → ¬ G.Adj a y) ∧ ¬ G.Adj u y ∧ y ≠ u := by
    intro y hby hyv hvy
    refine ⟨fun a hua hav h => hb1 a y hua hav h hby.symm,
      fun h => nAB y b h hyv hvb hbu hby.symm, ?_⟩
    rintro rfl; exact nuB b hvb hby.symm
  -- children `x` of `a ∈ A`: `Adj a x`, `x ≠ u`, `¬ Adj u x`
  have Xf : ∀ a x, G.Adj u a → a ≠ v → G.Adj a x → x ≠ u → ¬ G.Adj u x →
      ¬ G.Adj v x ∧ ¬ G.Adj x b ∧ (∀ c, G.Adj v c → c ≠ u → G.Adj b c → ¬ G.Adj x c) ∧
      (∀ a', G.Adj u a' → G.Adj a' x → a' = a) ∧ x ≠ v := by
    intro a x hua hav hax hxu hux
    refine ⟨fun h => nAB a x hua hav h hxu hax, hb1 a x hua hav hax,
      fun c hvc hcu hbc => hb2 a x c hua hav hvc hcu hbc hax, fun a' hua' ha'x => ?_, ?_⟩
    · by_contra hne
      exact hC4 _ _ _ _ hua hax ha'x.symm hua'.symm hxu.symm (Ne.symm hne)
    · rintro rfl; exact nvA a hua hax.symm
  -- every `a ∈ A` has two children
  have twoA : ∀ a, G.Adj u a → a ≠ v → ∃ x1 x2, (G.Adj a x1 ∧ x1 ≠ u ∧ ¬ G.Adj u x1) ∧
      (G.Adj a x2 ∧ x2 ≠ u ∧ ¬ G.Adj u x2) ∧ x1 ≠ x2 := by
    intro a hua hav
    by_cases hp : ∃ p, G.Adj u p ∧ G.Adj a p
    · obtain ⟨p, hup, hap⟩ := hp
      have np : ∀ x, G.Adj a x → x ≠ p → ¬ G.Adj u x := fun x hax hxp hux =>
        hC4 _ _ _ _ hap hup.symm hux hax.symm hua.ne.symm (Ne.symm hxp)
      obtain ⟨x1, hax1, hs1⟩ := hnb a {u, p} (card_pair_lt4 _ _)
      obtain ⟨x2, hax2, hs2⟩ := hnb a {u, p, x1} (card_triple_lt4 _ _ _)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs1 hs2
      exact ⟨x1, x2, ⟨hax1, hs1.1, np x1 hax1 hs1.2⟩, ⟨hax2, hs2.1, np x2 hax2 hs2.2.1⟩,
        Ne.symm hs2.2.2⟩
    · push Not at hp
      obtain ⟨x1, hax1, hs1⟩ := hnb a {u} (by simp)
      obtain ⟨x2, hax2, hs2⟩ := hnb a {u, x1} (card_pair_lt4 _ _)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs1 hs2
      exact ⟨x1, x2, ⟨hax1, hs1, fun h => hp x1 h hax1⟩, ⟨hax2, hs2.1, fun h => hp x2 h hax2⟩,
        Ne.symm hs2.2⟩
  -- a vertex `y0 ≠ a` is adjacent to at most one child of `a`
  have pickX : ∀ a y0, G.Adj u a → a ≠ v → a ≠ y0 →
      ∃ x, (G.Adj a x ∧ x ≠ u ∧ ¬ G.Adj u x) ∧ ¬ G.Adj x y0 := by
    intro a y0 hua hav hay0
    obtain ⟨x1, x2, hx1, hx2, hx12⟩ := twoA a hua hav
    by_cases h1 : G.Adj x1 y0
    · exact ⟨x2, hx2, fun h2 => hC4 _ _ _ _ hx1.1 h1 h2.symm hx2.1.symm hay0 hx12⟩
    · exact ⟨x1, hx1, h1⟩
  -- Step 2 (funnel): two children of `b` cannot reach two different vertices of `A`
  have F : ∀ y1 y2 a1 a2 x1 x2, G.Adj b y1 → y1 ≠ v → ¬ G.Adj v y1 → G.Adj b y2 → y2 ≠ v →
      ¬ G.Adj v y2 → y1 ≠ y2 → G.Adj u a1 → a1 ≠ v → G.Adj u a2 → a2 ≠ v → a1 ≠ a2 →
      G.Adj a1 x1 → x1 ≠ u → ¬ G.Adj u x1 → G.Adj a2 x2 → x2 ≠ u → ¬ G.Adj u x2 →
      G.Adj y1 x1 → G.Adj y2 x2 → False := by
    intro y1 y2 a1 a2 x1 x2 hby1 hy1v hvy1 hby2 hy2v hvy2 hy12 hua1 ha1v hua2 ha2v ha12
      hax1 hx1u hux1 hax2 hx2u hux2 hyx1 hyx2
    obtain ⟨Y3a, Y1a, Y4a⟩ := Yf y1 hby1 hy1v hvy1
    obtain ⟨Y3b, Y1b, Y4b⟩ := Yf y2 hby2 hy2v hvy2
    obtain ⟨-, -, -, X5a, -⟩ := Xf a1 x1 hua1 ha1v hax1 hx1u hux1
    exact hC8 _ _ _ _ _ _ _ _ hby1 hyx1 hax1.symm hua1.symm hua2 hax2 hyx2.symm hby2.symm
      (nodup8 hby1.ne (by rintro rfl; exact nAB _ _ hua1 ha1v hvb hbu hax1)
        (by rintro rfl; exact hnt _ hua1 hvb) hbu (by rintro rfl; exact hnt _ hua2 hvb)
        (by rintro rfl; exact nAB _ _ hua2 ha2v hvb hbu hax2) hby2.ne hyx1.ne
        (by rintro rfl; exact Y1a hua1) Y4a (by rintro rfl; exact Y1a hua2)
        (by rintro rfl; exact Y3a _ hua2 ha2v hax2) hy12 hax1.ne.symm hx1u
        (by rintro rfl; exact hux1 hua2) (by rintro rfl; exact ha12 (X5a _ hua2 hax2).symm)
        (by rintro rfl; exact Y3b _ hua1 ha1v hax1) hua1.ne.symm ha12
        (by rintro rfl; exact hux2 hua1) (by rintro rfl; exact Y1b hua1) hua2.ne hx2u.symm
        Y4b.symm hax2.ne (by rintro rfl; exact Y1b hua2) hyx2.ne.symm)
  -- funnel dichotomy: an unreached vertex of `A`, or at most one linked child `y0`
  have FD : (∃ a, G.Adj u a ∧ a ≠ v ∧ ∀ y x, G.Adj b y → y ≠ v → ¬ G.Adj v y →
        G.Adj a x → x ≠ u → ¬ G.Adj u x → ¬ G.Adj x y) ∨
      (∃ y0, (G.Adj b y0 ∧ y0 ≠ v ∧ ¬ G.Adj v y0) ∧ ∀ y, G.Adj b y → y ≠ v → ¬ G.Adj v y →
        y ≠ y0 → ∀ a x, G.Adj u a → a ≠ v → G.Adj a x → x ≠ u → ¬ G.Adj u x →
        ¬ G.Adj x y) := by
    by_cases hα : ∃ a, G.Adj u a ∧ a ≠ v ∧ ∀ y x, G.Adj b y → y ≠ v → ¬ G.Adj v y →
        G.Adj a x → x ≠ u → ¬ G.Adj u x → ¬ G.Adj x y
    · exact Or.inl hα
    · right
      have hα' : ∀ a, G.Adj u a → a ≠ v → ∃ y x, (G.Adj b y ∧ y ≠ v ∧ ¬ G.Adj v y) ∧
          (G.Adj a x ∧ x ≠ u ∧ ¬ G.Adj u x) ∧ G.Adj x y := by
        intro a hua hav
        by_contra hc
        exact hα ⟨a, hua, hav, fun y x hby hyv hvy hax hxu hux hxy =>
          hc ⟨y, x, ⟨hby, hyv, hvy⟩, ⟨hax, hxu, hux⟩, hxy⟩⟩
      obtain ⟨a1, hua1, ha1⟩ := hnb u {v} (by simp)
      simp only [Finset.mem_singleton] at ha1
      obtain ⟨y1, x1, ⟨hby1, hy1v, hvy1⟩, ⟨hax1, hx1u, hux1⟩, hxy1⟩ := hα' a1 hua1 ha1
      refine ⟨y1, ⟨hby1, hy1v, hvy1⟩, fun y hby hyv hvy hyy1 a x hua hav hax hxu hux hxy => ?_⟩
      by_cases haa1 : a = a1
      · rw [haa1] at hax
        obtain ⟨a3, hua3, ha3⟩ := hnb u {v, a1} (card_pair_lt4 _ _)
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha3
        obtain ⟨y3, x3, ⟨hby3, hy3v, hvy3⟩, ⟨hax3, hx3u, hux3⟩, hxy3⟩ := hα' a3 hua3 ha3.1
        by_cases hy31 : y3 = y1
        · rw [hy31] at hby3 hy3v hvy3 hxy3
          exact F y y1 a1 a3 x x3 hby hyv hvy hby3 hy3v hvy3 hyy1 hua1 ha1 hua3 ha3.1
            (Ne.symm ha3.2) hax hxu hux hax3 hx3u hux3 hxy.symm hxy3.symm
        · exact F y3 y1 a3 a1 x3 x1 hby3 hy3v hvy3 hby1 hy1v hvy1 hy31 hua3 ha3.1 hua1 ha1
            ha3.2 hax3 hx3u hux3 hax1 hx1u hux1 hxy3.symm hxy1.symm
      · exact F y y1 a a1 x x1 hby hyv hvy hby1 hy1v hvy1 hyy1 hua hav hua1 ha1 haa1 hax hxu
          hux hax1 hx1u hux1 hxy.symm hxy1.symm
  -- Step 3 (short connections)
  have S3 : ∀ a x y, G.Adj u a → a ≠ v → G.Adj a x → x ≠ u → ¬ G.Adj u x →
      G.Adj b y → y ≠ v → ¬ G.Adj v y →
      G.Adj x y ∨ (∃ w, G.Adj x w ∧ G.Adj w y) ∨
      (∃ x', (G.Adj a x' ∧ x' ≠ u ∧ ¬ G.Adj u x') ∧ x' ≠ x ∧ G.Adj x' y) ∨
      (∃ y', (G.Adj b y' ∧ y' ≠ v ∧ ¬ G.Adj v y') ∧ y' ≠ y ∧ G.Adj x y') := by
    intro a x y hua hav hax hxu hux hby hyv hvy
    obtain ⟨Y3, Y1, Y4⟩ := Yf y hby hyv hvy
    obtain ⟨X1, X3, X4, -, X6⟩ := Xf a x hua hav hax hxu hux
    by_cases hxy : G.Adj x y
    · exact Or.inl hxy
    rcases hconn x y with h | h | h | ⟨p, q, hxp, hpq, hqy⟩
    · exact absurd (h ▸ hax) (Y3 a hua hav)
    · exact absurd h hxy
    · exact Or.inr (Or.inl h)
    · by_cases hp : p = a
      · rw [hp] at hpq
        refine Or.inr (Or.inr (Or.inl ⟨q, ⟨hpq, ?_, ?_⟩, ?_, hqy⟩))
        · rintro rfl; exact Y1 hqy
        · intro huq
          exact Y3 q huq (by rintro rfl; exact hvy hqy) hqy
        · rintro rfl; exact hxy hqy
      · by_cases hq : q = b
        · rw [hq] at hpq
          refine Or.inr (Or.inr (Or.inr ⟨p, ⟨hpq.symm, ?_, ?_⟩, ?_, hxp⟩))
          · rintro rfl; exact X1 hxp.symm
          · intro hvp
            exact X4 p hvp (by rintro rfl; exact hux hxp.symm) hpq.symm hxp
          · rintro rfl; exact hxy hxp
        · exfalso
          exact hC8 _ _ _ _ _ _ _ _ hua hax hxp hpq hqy hby.symm hvb.symm huv.symm
            (nodup8 hua.ne hxu.symm (by rintro rfl; exact hux hxp.symm)
              (by rintro rfl; exact Y1 hqy) Y4.symm hbu.symm huv.ne hax.ne (Ne.symm hp)
              (by rintro rfl; exact Y3 _ hua hav hqy) (by rintro rfl; exact Y1 hua)
              (by rintro rfl; exact hnt _ hua hvb) hav hxp.ne (by rintro rfl; exact hxy hqy)
              (by rintro rfl; exact Y3 _ hua hav hax)
              (by rintro rfl; exact nAB _ _ hua hav hvb hbu hax) X6 hpq.ne
              (by rintro rfl; exact hxy hxp) (by rintro rfl; exact X3 hxp)
              (by rintro rfl; exact X1 hxp.symm) hqy.ne hq (by rintro rfl; exact hvy hqy)
              hby.ne.symm hyv hvb.ne.symm)
  -- Step 3 with (i), (iii), (iv) excluded: only a common neighbour remains
  have S3' : ∀ a x y, G.Adj u a → a ≠ v → G.Adj a x → x ≠ u → ¬ G.Adj u x →
      G.Adj b y → y ≠ v → ¬ G.Adj v y →
      (∀ y', G.Adj b y' → y' ≠ v → ¬ G.Adj v y' → G.Adj x y' → False) →
      (∀ x', G.Adj a x' → x' ≠ u → ¬ G.Adj u x' → G.Adj x' y → False) →
      ∃ w, G.Adj x w ∧ G.Adj w y := by
    intro a x y hua hav hax hxu hux hby hyv hvy k1 k2
    rcases S3 a x y hua hav hax hxu hux hby hyv hvy with
      h | h | ⟨x', ⟨h1, h2, h3⟩, -, h4⟩ | ⟨y', ⟨h1, h2, h3⟩, -, h4⟩
    · exact (k1 y hby hyv hvy h).elim
    · exact h
    · exact (k2 x' h1 h2 h3 h4).elim
    · exact (k1 y' h1 h2 h3 h4).elim
  by_cases hpb : ∃ c, G.Adj v c ∧ c ≠ u ∧ G.Adj b c
  · ---------------------------------------------------------------- Step 4a: `b` has a partner
    obtain ⟨c, hvc, hcu, hbc⟩ := hpb
    have chB : ∀ y, G.Adj b y → y ≠ v → y ≠ c → ¬ G.Adj v y := fun y hby hyv hyc hvy =>
      hC4 _ _ _ _ hvc hbc.symm hby hvy.symm hvb.ne (Ne.symm hyc)
    obtain ⟨y1, hby1, hs1⟩ := hnb b {v, c} (card_pair_lt4 _ _)
    obtain ⟨y2, hby2, hs2⟩ := hnb b {v, c, y1} (card_triple_lt4 _ _ _)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs1 hs2
    have hvy1 := chB y1 hby1 hs1.1 hs1.2
    have hvy2 := chB y2 hby2 hs2.1 hs2.2.1
    -- (ii) is impossible
    have no_ii : ∀ a x y w, G.Adj u a → a ≠ v → G.Adj a x → x ≠ u → ¬ G.Adj u x →
        G.Adj b y → y ≠ v → ¬ G.Adj v y → G.Adj x w → G.Adj w y → False := by
      intro a x y w hua hav hax hxu hux hby hyv hvy hxw hwy
      obtain ⟨Y3, Y1, Y4⟩ := Yf y hby hyv hvy
      obtain ⟨X1, X3, X4, -, X6⟩ := Xf a x hua hav hax hxu hux
      exact hC8 _ _ _ _ _ _ _ _ hxw hwy hby.symm hbc hvc.symm huv.symm hua hax
        (nodup8 hxw.ne (by rintro rfl; exact Y3 _ hua hav hax)
          (by rintro rfl; exact nAB _ _ hua hav hvb hbu hax)
          (by rintro rfl; exact nAB _ _ hua hav hvc hcu hax) X6 hxu hax.ne.symm hwy.ne
          (by rintro rfl; exact X3 hxw) (by rintro rfl; exact X4 _ hvc hcu hbc hxw)
          (by rintro rfl; exact X1 hxw.symm) (by rintro rfl; exact hux hxw.symm)
          (by rintro rfl; exact Y3 _ hua hav hwy) hby.ne.symm (by rintro rfl; exact hvy hvc)
          hyv Y4 (by rintro rfl; exact Y1 hua) hbc.ne hvb.ne.symm hbu
          (by rintro rfl; exact hnt _ hua hvb) hvc.ne.symm hcu
          (by rintro rfl; exact hnt _ hua hvc) huv.ne.symm (Ne.symm hav) hua.ne)
    rcases FD with ⟨a, hua, hav, hα⟩ | ⟨y0, ⟨hby0, hy0v, hvy0⟩, hβ⟩
    · obtain ⟨x1, x2, ⟨hax1, hx1u, hux1⟩, -, -⟩ := twoA a hua hav
      obtain ⟨w, hxw, hwy⟩ := S3' a x1 y1 hua hav hax1 hx1u hux1 hby1 hs1.1 hvy1
        (fun y' h1 h2 h3 h4 => hα y' x1 h1 h2 h3 hax1 hx1u hux1 h4)
        (fun x' h1 h2 h3 h4 => hα y1 x' hby1 hs1.1 hvy1 h1 h2 h3 h4)
      exact no_ii a x1 y1 w hua hav hax1 hx1u hux1 hby1 hs1.1 hvy1 hxw hwy
    · obtain ⟨a, hua, has⟩ := hnb u {v} (by simp)
      simp only [Finset.mem_singleton] at has
      obtain ⟨-, Y1₀, -⟩ := Yf y0 hby0 hy0v hvy0
      obtain ⟨x, ⟨hax, hxu, hux⟩, hxy0⟩ := pickX a y0 hua has (by rintro rfl; exact Y1₀ hua)
      obtain ⟨y, hby, hyv, hvy, hyy0⟩ : ∃ y, G.Adj b y ∧ y ≠ v ∧ ¬ G.Adj v y ∧ y ≠ y0 := by
        by_cases h : y1 = y0
        · exact ⟨y2, hby2, hs2.1, hvy2, fun e => hs2.2.2 (e.trans h.symm)⟩
        · exact ⟨y1, hby1, hs1.1, hvy1, h⟩
      obtain ⟨w, hxw, hwy⟩ := S3' a x y hua has hax hxu hux hby hyv hvy
        (fun y' h1 h2 h3 h4 => by
          by_cases e : y' = y0
          · rw [e] at h4; exact hxy0 h4
          · exact hβ y' h1 h2 h3 e a x hua has hax hxu hux h4)
        (fun x' h1 h2 h3 h4 => hβ y hby hyv hvy hyy0 a x' hua has h1 h2 h3 h4)
      exact no_ii a x y w hua has hax hxu hux hby hyv hvy hxw hwy
  · ---------------------------------------------------------------- Step 4b: no partner
    have chB : ∀ y, G.Adj b y → ¬ G.Adj v y := fun y hby hvy =>
      hpb ⟨y, hvy, by rintro rfl; exact nuB b hvb hby.symm, hby⟩
    obtain ⟨y1, hby1, hs1⟩ := hnb b {v} (by simp)
    obtain ⟨y2, hby2, hs2⟩ := hnb b {v, y1} (card_pair_lt4 _ _)
    obtain ⟨y3, hby3, hs3⟩ := hnb b {v, y1, y2} (card_triple_lt4 _ _ _)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs1 hs2 hs3
    have hvy1 := chB y1 hby1
    have hvy2 := chB y2 hby2
    have hvy3 := chB y3 hby3
    rcases FD with ⟨a, hua, hav, hα⟩ | ⟨y0, ⟨hby0, hy0v, hvy0⟩, hβ⟩
    · obtain ⟨x1, x2, ⟨hax1, hx1u, hux1⟩, ⟨hax2, hx2u, hux2⟩, hx12⟩ := twoA a hua hav
      obtain ⟨w1, hxw1, hwy1⟩ := S3' a x1 y1 hua hav hax1 hx1u hux1 hby1 hs1 hvy1
        (fun y' h1 h2 h3 h4 => hα y' x1 h1 h2 h3 hax1 hx1u hux1 h4)
        (fun x' h1 h2 h3 h4 => hα y1 x' hby1 hs1 hvy1 h1 h2 h3 h4)
      obtain ⟨w2, hxw2, hwy2⟩ := S3' a x2 y2 hua hav hax2 hx2u hux2 hby2 hs2.1 hvy2
        (fun y' h1 h2 h3 h4 => hα y' x2 h1 h2 h3 hax2 hx2u hux2 h4)
        (fun x' h1 h2 h3 h4 => hα y2 x' hby2 hs2.1 hvy2 h1 h2 h3 h4)
      obtain ⟨Y3a, Y1a, -⟩ := Yf y1 hby1 hs1 hvy1
      obtain ⟨Y3b, Y1b, -⟩ := Yf y2 hby2 hs2.1 hvy2
      obtain ⟨-, X3a, -, -, -⟩ := Xf a x1 hua hav hax1 hx1u hux1
      obtain ⟨-, X3b, -, -, -⟩ := Xf a x2 hua hav hax2 hx2u hux2
      have wa1 : a ≠ w1 := by rintro rfl; exact Y3a _ hua hav hwy1
      exact hC8 _ _ _ _ _ _ _ _ hax1 hxw1 hwy1 hby1.symm hby2 hwy2.symm hxw2.symm hax2.symm
        (nodup8 hax1.ne (by rintro rfl; exact Y3a _ hua hav hwy1) (by rintro rfl; exact Y1a hua)
          (by rintro rfl; exact hnt _ hua hvb) (by rintro rfl; exact Y1b hua)
          (by rintro rfl; exact Y3b _ hua hav hwy2) hax2.ne hxw1.ne
          (by rintro rfl; exact Y3a _ hua hav hax1)
          (by rintro rfl; exact nAB _ _ hua hav hvb hbu hax1)
          (by rintro rfl; exact Y3b _ hua hav hax1)
          (by rintro rfl; exact hα y2 _ hby2 hs2.1 hvy2 hax1 hx1u hux1 hwy2) hx12 hwy1.ne
          (by rintro rfl; exact X3a hxw1)
          (by rintro rfl; exact hα _ x1 hby2 hs2.1 hvy2 hax1 hx1u hux1 hxw1)
          (by rintro rfl; exact hC4 _ _ _ _ hax1 hxw1 hxw2.symm hax2.symm wa1 hx12)
          (by rintro rfl; exact hα y1 _ hby1 hs1 hvy1 hax2 hx2u hux2 hwy1) hby1.ne.symm
          (Ne.symm hs2.2) (by rintro rfl; exact hα _ x2 hby1 hs1 hvy1 hax2 hx2u hux2 hxw2)
          (by rintro rfl; exact Y3a _ hua hav hax2) hby2.ne (by rintro rfl; exact X3b hxw2)
          (by rintro rfl; exact nAB _ _ hua hav hvb hbu hax2) hwy2.ne.symm
          (by rintro rfl; exact Y3b _ hua hav hax2) hxw2.ne.symm)
    · obtain ⟨a1, hua1, ha1⟩ := hnb u {v} (by simp)
      obtain ⟨a2, hua2, ha2⟩ := hnb u {v, a1} (card_pair_lt4 _ _)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha1 ha2
      obtain ⟨-, Y1₀, -⟩ := Yf y0 hby0 hy0v hvy0
      obtain ⟨x1, ⟨hax1, hx1u, hux1⟩, hx1y0⟩ :=
        pickX a1 y0 hua1 ha1 (by rintro rfl; exact Y1₀ hua1)
      obtain ⟨x2, ⟨hax2, hx2u, hux2⟩, hx2y0⟩ :=
        pickX a2 y0 hua2 ha2.1 (by rintro rfl; exact Y1₀ hua2)
      obtain ⟨yA, yB, ⟨hbyA, hyAv, hvyA, hyA0⟩, ⟨hbyB, hyBv, hvyB, hyB0⟩, hAB⟩ :
          ∃ yA yB, (G.Adj b yA ∧ yA ≠ v ∧ ¬ G.Adj v yA ∧ yA ≠ y0) ∧
            (G.Adj b yB ∧ yB ≠ v ∧ ¬ G.Adj v yB ∧ yB ≠ y0) ∧ yA ≠ yB := by
        by_cases h1 : y1 = y0
        · exact ⟨y2, y3, ⟨hby2, hs2.1, hvy2, fun e => hs2.2 (e.trans h1.symm)⟩,
            ⟨hby3, hs3.1, hvy3, fun e => hs3.2.1 (e.trans h1.symm)⟩, Ne.symm hs3.2.2⟩
        · by_cases h2 : y2 = y0
          · exact ⟨y1, y3, ⟨hby1, hs1, hvy1, h1⟩,
              ⟨hby3, hs3.1, hvy3, fun e => hs3.2.2 (e.trans h2.symm)⟩, Ne.symm hs3.2.1⟩
          · exact ⟨y1, y2, ⟨hby1, hs1, hvy1, h1⟩, ⟨hby2, hs2.1, hvy2, h2⟩, Ne.symm hs2.2⟩
      have k1 : ∀ (a x : V), G.Adj u a → a ≠ v → G.Adj a x → x ≠ u → ¬ G.Adj u x →
          ¬ G.Adj x y0 → ∀ y', G.Adj b y' → y' ≠ v → ¬ G.Adj v y' → G.Adj x y' → False := by
        intro a x hua hav hax hxu hux hxy0 y' h1 h2 h3 h4
        by_cases e : y' = y0
        · rw [e] at h4; exact hxy0 h4
        · exact hβ y' h1 h2 h3 e a x hua hav hax hxu hux h4
      have W : ∀ (a x y : V), G.Adj u a → a ≠ v → G.Adj a x → x ≠ u → ¬ G.Adj u x →
          ¬ G.Adj x y0 → G.Adj b y → y ≠ v → ¬ G.Adj v y → y ≠ y0 →
          ∃ w, G.Adj x w ∧ G.Adj w y :=
        fun a x y hua hav hax hxu hux hxy0 hby hyv hvy hyy0 =>
          S3' a x y hua hav hax hxu hux hby hyv hvy (k1 a x hua hav hax hxu hux hxy0)
            (fun x' h1 h2 h3 h4 => hβ y hby hyv hvy hyy0 a x' hua hav h1 h2 h3 h4)
      obtain ⟨-, X3a, -, X5a, -⟩ := Xf a1 x1 hua1 ha1 hax1 hx1u hux1
      have x12 : x1 ≠ x2 := by rintro rfl; exact ha2.2 (X5a a2 hua2 hax2)
      have M : ∀ y w w', G.Adj b y → y ≠ v → ¬ G.Adj v y → G.Adj x1 w → G.Adj w y →
          G.Adj x2 w' → G.Adj w' y → w = w' := by
        intro y w w' hby hyv hvy h1w hwy h2w hw'y
        by_contra hne
        obtain ⟨Y3, Y1, Y4⟩ := Yf y hby hyv hvy
        exact hC8 _ _ _ _ _ _ _ _ h1w hwy hw'y.symm h2w.symm hax2.symm hua2.symm hua1 hax1
          (nodup8 h1w.ne (by rintro rfl; exact Y3 _ hua1 ha1 hax1)
            (by rintro rfl; exact k1 a1 _ hua1 ha1 hax1 hx1u hux1 hx1y0 y hby hyv hvy hw'y)
            x12 (by rintro rfl; exact hux1 hua2) hx1u hax1.ne.symm hwy.ne hne
            (by rintro rfl; exact k1 a2 _ hua2 ha2.1 hax2 hx2u hux2 hx2y0 y hby hyv hvy hwy)
            (by rintro rfl; exact Y3 _ hua2 ha2.1 hwy) (by rintro rfl; exact hux1 h1w.symm)
            (by rintro rfl; exact Y3 _ hua1 ha1 hwy) hw'y.ne.symm
            (by rintro rfl; exact Y3 _ hua2 ha2.1 hax2) (by rintro rfl; exact Y1 hua2) Y4
            (by rintro rfl; exact Y1 hua1) h2w.ne.symm
            (by rintro rfl; exact Y3 _ hua2 ha2.1 hw'y)
            (by rintro rfl; exact hux2 h2w.symm) (by rintro rfl; exact Y3 _ hua1 ha1 hw'y)
            hax2.ne.symm hx2u (by rintro rfl; exact hux2 hua1) hua2.ne.symm ha2.2 hua1.ne)
      obtain ⟨wA, h1A, hAy⟩ := W a1 x1 yA hua1 ha1 hax1 hx1u hux1 hx1y0 hbyA hyAv hvyA hyA0
      obtain ⟨wA', h2A, hA'y⟩ := W a2 x2 yA hua2 ha2.1 hax2 hx2u hux2 hx2y0 hbyA hyAv hvyA hyA0
      obtain ⟨wB, h1B, hBy⟩ := W a1 x1 yB hua1 ha1 hax1 hx1u hux1 hx1y0 hbyB hyBv hvyB hyB0
      obtain ⟨wB', h2B, hB'y⟩ := W a2 x2 yB hua2 ha2.1 hax2 hx2u hux2 hx2y0 hbyB hyBv hvyB hyB0
      have eA := M yA wA wA' hbyA hyAv hvyA h1A hAy h2A hA'y
      have eB := M yB wB wB' hbyB hyBv hvyB h1B hBy h2B hB'y
      rw [← eA] at h2A
      rw [← eB] at h2B
      have nAB' : wA ≠ wB := by
        rintro rfl
        exact hC4 _ _ _ _ hbyA hAy.symm hBy hbyB.symm (by rintro rfl; exact X3a h1A) hAB
      exact hC4 _ _ _ _ h1A h2A.symm h2B h1B.symm x12 nAB'

variable [Fintype V] [DecidableRel G.Adj]

/-- **Diameter `≤ 3`, minimum degree `≥ 4`**: a finite graph with minimum degree `≥ 4` and
diameter `≤ 3` contains a cycle of length 4 or 8.

Proof claim #383 on erdosproblems.com
(https://www.erdosproblems.com/forum/thread/64/proof-claims, submitted 2026-10-02), claimed by
Murat Can Temeller using Claude Opus 5.5 (Anthropic); proof published in GitHub issue
zey9310/zey9310-math#1, which states the theorem, proof, code and computations were produced by
Claude Opus 5.5 in a session directed by @zey9310.

The minimum-degree hypothesis is `≥ 4`: diameter-3 graphs with vertices of degree 3 remain open,
as the issue states. -/
theorem diam3_minDegree4 (hδ : 4 ≤ G.minDegree) (hd : G.ediam ≤ 3) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ (c.length = 4 ∨ c.length = 8) := by
  classical
  by_contra hno
  have hC4 : NoC4 G := by
    intro a b c d h1 h2 h3 h4 h5 h6
    obtain ⟨v, p, hp, hl⟩ := cycle4_of h1 h2 h3 h4 h5 h6
    exact hno ⟨v, p, hp, Or.inl hl⟩
  have hC8 : NoC8 G := by
    intro v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ hnd
    obtain ⟨v, p, hp, hl⟩ := cycle8_of h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ hnd
    exact hno ⟨v, p, hp, Or.inr hl⟩
  have hconn : ShortConn G := fun x y => short_conn ((ediam_le_iff.mp hd) x y)
  have hnb : Nbr4 G := fun v s hs =>
    exists_nbr_not_mem v s (lt_of_lt_of_le hs (hδ.trans (G.minDegree_le_degree v)))
  have hne : Nonempty V := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [SimpleGraph.minDegree_of_subsingleton] at hδ
  obtain ⟨x⟩ := hne
  by_cases htri : ∀ a b, G.Adj a b → ∃ t, G.Adj a t ∧ G.Adj b t
  · exact diam3_case1 hC4 hC8 hconn hnb htri x
  · push Not at htri
    obtain ⟨u, v, huv, hnt'⟩ := htri
    have hnt : ∀ t, G.Adj u t → G.Adj v t → False := fun t h1 h2 => hnt' t h1 h2
    rcases diam3_step1 hC4 hC8 hnb huv hnt with ⟨b, hvb, hbu, hb1, hb2⟩ | ⟨a, hua, hav, ha1, ha2⟩
    · exact diam3_case2_core hC4 hC8 hconn hnb huv hnt hvb hbu hb1 hb2
    · exact diam3_case2_core hC4 hC8 hconn hnb huv.symm (fun t h1 h2 => hnt t h2 h1) hua hav
        ha1 ha2

/-- **Carr's theorem** (A. Carr, arXiv:2508.19302, Theorem 1.1): a finite graph with minimum
degree `≥ 3` and diameter `≤ 2` contains a cycle of length 4 or 8.

Carr states it for diameter exactly 2; the hypothesis `ediam ≤ 2` only adds the complete graphs
(`ediam ≤ 1`), see the converse check in `Fidelity/Erdos64SmallDiameter.lean`. -/
theorem carr_diam2 (hδ : 3 ≤ G.minDegree) (hd : G.ediam ≤ 2) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ (c.length = 4 ∨ c.length = 8) := by
  classical
  by_contra hno
  have hC4 : ∀ a b c d : V, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a ≠ c → b ≠ d →
      False := by
    intro a b c d h1 h2 h3 h4 h5 h6
    obtain ⟨v, p, hp, hl⟩ := cycle4_of h1 h2 h3 h4 h5 h6
    exact hno ⟨v, p, hp, Or.inl hl⟩
  have hC8 : ∀ v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : V, G.Adj v₀ v₁ → G.Adj v₁ v₂ → G.Adj v₂ v₃ →
      G.Adj v₃ v₄ → G.Adj v₄ v₅ → G.Adj v₅ v₆ → G.Adj v₆ v₇ → G.Adj v₇ v₀ →
      [v₀, v₁, v₂, v₃, v₄, v₅, v₆, v₇].Nodup → False := by
    intro v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ hnd
    obtain ⟨v, p, hp, hl⟩ := cycle8_of h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ hnd
    exact hno ⟨v, p, hp, Or.inr hl⟩
  have hdeg : ∀ v, 3 ≤ G.degree v := fun v => hδ.trans (G.minDegree_le_degree v)
  have hcn : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ w, G.Adj x w ∧ G.Adj w y :=
    fun x y hne hna => common_nbr_of_edist_le_two ((ediam_le_iff.mp hd) x y) hne hna
  have hnb : ∀ (v : V) (s : Finset V), s.card < 3 → ∃ w, G.Adj v w ∧ w ∉ s :=
    fun v s hs => exists_nbr_not_mem v s (lt_of_lt_of_le hs (hdeg v))
  have hne : Nonempty V := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [SimpleGraph.minDegree_of_subsingleton] at hδ
  obtain ⟨v1⟩ := hne
  obtain ⟨v2, h12, -⟩ := hnb v1 ∅ (by simp)
  by_cases htri : ∃ t, G.Adj v1 t ∧ G.Adj v2 t
  · ------------------------------------------------------------------ Case 1: a triangle
    obtain ⟨v3, h13, h23⟩ := htri
    obtain ⟨v4, h14, hv4⟩ := hnb v1 {v2, v3} (card_pair_lt _ _)
    obtain ⟨v6, h26, hv6⟩ := hnb v2 {v1, v3} (card_pair_lt _ _)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv4 hv6
    have n42 : v4 ≠ v2 := hv4.1
    have n43 : v4 ≠ v3 := hv4.2
    have n61 : v6 ≠ v1 := hv6.1
    have n63 : v6 ≠ v3 := hv6.2
    have n46 : v4 ≠ v6 := by
      rintro rfl; exact hC4 _ _ _ _ h13 h23.symm h26 h14.symm h12.ne n43.symm
    have a46 : ¬ G.Adj v4 v6 := fun h => hC4 _ _ _ _ h14.symm h12 h26 h.symm n42 n61.symm
    obtain ⟨v7, h47, h76⟩ := hcn v4 v6 n46 a46
    have n71 : v7 ≠ v1 := by
      rintro rfl; exact hC4 _ _ _ _ h13 h23.symm h26 h76.symm h12.ne n63.symm
    have n72 : v7 ≠ v2 := by
      rintro rfl; exact hC4 _ _ _ _ h23 h13.symm h14 h47 h12.ne.symm n43.symm
    have n73 : v7 ≠ v3 := by
      rintro rfl; exact hC4 _ _ _ _ h47 h23.symm h12.symm h14 n42 h13.ne.symm
    have a37 : ¬ G.Adj v3 v7 := fun h =>
      hC4 _ _ _ _ h.symm h13.symm h14 h47 n71 n43.symm
    obtain ⟨v8, h38, h87⟩ := hcn v3 v7 n73.symm a37
    have n81 : v8 ≠ v1 := by
      rintro rfl; exact hC4 _ _ _ _ h12 h26 h76.symm h87.symm n61.symm n72.symm
    have n82 : v8 ≠ v2 := by
      rintro rfl; exact hC4 _ _ _ _ h12.symm h14 h47 h87.symm n42.symm n71.symm
    have n84 : v8 ≠ v4 := by
      rintro rfl; exact hC4 _ _ _ _ h38.symm h23.symm h12.symm h14 n42 h13.ne.symm
    have n86 : v8 ≠ v6 := by
      rintro rfl; exact hC4 _ _ _ _ h38.symm h13.symm h12 h26 n61 h23.ne.symm
    obtain ⟨v9, h89, hv9⟩ := hnb v8 {v3, v7} (card_pair_lt _ _)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv9
    have n93 : v9 ≠ v3 := hv9.1
    have n97 : v9 ≠ v7 := hv9.2
    have a91 : ¬ G.Adj v9 v1 := fun h => hC4 _ _ _ _ h13 h38 h89 h n81.symm n93.symm
    have a92 : ¬ G.Adj v9 v2 := fun h => hC4 _ _ _ _ h23 h38 h89 h n82.symm n93.symm
    have a94 : ¬ G.Adj v9 v4 := fun h => hC4 _ _ _ _ h47 h87.symm h89 h n84.symm n97.symm
    have a96 : ¬ G.Adj v9 v6 := fun h => hC4 _ _ _ _ h76.symm h87.symm h89 h n86.symm n97.symm
    have n91 : v9 ≠ v1 := by
      rintro rfl; exact hC4 _ _ _ _ h14 h47 h87.symm h89 n71.symm n84.symm
    have n92 : v9 ≠ v2 := by
      rintro rfl; exact hC4 _ _ _ _ h12.symm h13 h38 h89 h23.ne n81.symm
    have n94 : v9 ≠ v4 := by
      rintro rfl; exact hC4 _ _ _ _ h89.symm h38.symm h13.symm h14 n43 n81
    have n96 : v9 ≠ v6 := by
      rintro rfl; exact hC4 _ _ _ _ h26.symm h23 h38 h89 n63 n82.symm
    obtain ⟨a, h9a, ha4⟩ := hcn v9 v4 n94 a94
    obtain ⟨b, h9b, hb2⟩ := hcn v9 v2 n92 a92
    have na1 : a ≠ v1 := by rintro rfl; exact a91 h9a
    have na2 : a ≠ v2 := by rintro rfl; exact a92 h9a
    have na3 : a ≠ v3 := by
      rintro rfl; exact hC4 _ _ _ _ ha4.symm h23.symm h12.symm h14 n42 h13.ne.symm
    have na6 : a ≠ v6 := by rintro rfl; exact a96 h9a
    have na8 : a ≠ v8 := by
      rintro rfl; exact hC4 _ _ _ _ ha4.symm h38.symm h13.symm h14 n43 n81
    by_cases na7 : a = v7
    · rw [na7] at h9a
      have nb1 : b ≠ v1 := by rintro rfl; exact a91 h9b
      have nb4 : b ≠ v4 := by rintro rfl; exact a94 h9b
      have nb6 : b ≠ v6 := by rintro rfl; exact a96 h9b
      have nb7 : b ≠ v7 := by
        rintro rfl; exact hC4 _ _ _ _ h12.symm h14 h47 hb2 n42.symm n71.symm
      have nb8 : b ≠ v8 := by
        rintro rfl; exact hC4 _ _ _ _ h12.symm h13 h38 hb2 h23.ne n81.symm
      by_cases nb3 : b = v3
      · subst nb3
        exact hC4 _ _ _ _ h38 h87 h9a.symm h9b n73.symm h89.ne
      · exact hC8 _ _ _ _ _ _ _ _ hb2 h23 h13.symm h14 h47 h87.symm h89 h9b
          (nodup8 hb2.ne nb3 nb1 nb4 nb7 nb8 h9b.ne.symm h23.ne h12.ne.symm n42.symm n72.symm
            n82.symm n92.symm h13.ne.symm n43.symm n73.symm h38.ne n93.symm h14.ne n71.symm
            n81.symm n91.symm h47.ne n84.symm n94.symm h87.ne.symm n97.symm h89.ne)
    · exact hC8 _ _ _ _ _ _ _ _ ha4 h14.symm h12 h26 h76.symm h87.symm h89 h9a
        (nodup8 ha4.ne na1 na2 na6 na7 na8 h9a.ne.symm h14.ne.symm n42 n46 h47.ne n84.symm
          n94.symm h12.ne n61.symm n71.symm n81.symm n91.symm h26.ne n72.symm n82.symm n92.symm
          h76.ne.symm n86.symm n96.symm h87.ne.symm n97.symm h89.ne)
  · ------------------------------------------------------------------ Case 2: no triangle on v1v2
    have nt : ∀ t, G.Adj v1 t → G.Adj v2 t → False := fun t h1 h2 => htri ⟨t, h1, h2⟩
    obtain ⟨v3, h13, hv3⟩ := hnb v1 {v2} (by simp)
    obtain ⟨v4, h14, hv4⟩ := hnb v1 {v2, v3} (card_pair_lt _ _)
    obtain ⟨v5, h25, hv5⟩ := hnb v2 {v1} (by simp)
    obtain ⟨v6, h26, hv6⟩ := hnb v2 {v1, v5} (card_pair_lt _ _)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv3 hv4 hv5 hv6
    have n42 : v4 ≠ v2 := hv4.1
    have n43 : v4 ≠ v3 := hv4.2
    have n61 : v6 ≠ v1 := hv6.1
    have n65 : v6 ≠ v5 := hv6.2
    replace hv3 : v3 ≠ v2 := hv3
    replace hv5 : v5 ≠ v1 := hv5
    have a15 : ¬ G.Adj v1 v5 := fun h => nt v5 h h25
    have a16 : ¬ G.Adj v1 v6 := fun h => nt v6 h h26
    have a23 : ¬ G.Adj v2 v3 := fun h => nt v3 h13 h
    have a24 : ¬ G.Adj v2 v4 := fun h => nt v4 h14 h
    have n35 : v3 ≠ v5 := by rintro rfl; exact nt _ h13 h25
    have n36 : v3 ≠ v6 := by rintro rfl; exact nt _ h13 h26
    have n45 : v4 ≠ v5 := by rintro rfl; exact nt _ h14 h25
    have n46 : v4 ≠ v6 := by rintro rfl; exact nt _ h14 h26
    have a35 : ¬ G.Adj v3 v5 := fun h => hC4 _ _ _ _ h13 h h25.symm h12.symm hv5.symm hv3
    have a36 : ¬ G.Adj v3 v6 := fun h => hC4 _ _ _ _ h13 h h26.symm h12.symm n61.symm hv3
    have a45 : ¬ G.Adj v4 v5 := fun h => hC4 _ _ _ _ h14 h h25.symm h12.symm hv5.symm n42
    have a46 : ¬ G.Adj v4 v6 := fun h => hC4 _ _ _ _ h14 h h26.symm h12.symm n61.symm n42
    obtain ⟨v7, h37, h75⟩ := hcn v3 v5 n35 a35
    have n71 : v7 ≠ v1 := by rintro rfl; exact a15 h75
    have n72 : v7 ≠ v2 := by rintro rfl; exact a23 h37.symm
    have n74 : v7 ≠ v4 := by rintro rfl; exact a45 h75
    have n76 : v7 ≠ v6 := by rintro rfl; exact a36 h37
    have a47 : ¬ G.Adj v4 v7 := fun h => hC4 _ _ _ _ h h37.symm h13.symm h14 n43 n71
    obtain ⟨v8, h48, h86⟩ := hcn v4 v6 n46 a46
    have n81 : v8 ≠ v1 := by rintro rfl; exact a16 h86
    have n82 : v8 ≠ v2 := by rintro rfl; exact a24 h48.symm
    have n83 : v8 ≠ v3 := by rintro rfl; exact a36 h86
    have n85 : v8 ≠ v5 := by rintro rfl; exact a45 h48
    have n87 : v8 ≠ v7 := by rintro rfl; exact a47 h48
    exact hC8 _ _ _ _ _ _ _ _ h37.symm h13.symm h14 h48 h86 h26.symm h25 h75.symm
      (nodup8 h37.ne.symm n71 n74 n87.symm n76 n72 h75.ne h13.ne.symm n43.symm n83.symm n36 hv3
        n35 h14.ne n81.symm n61.symm h12.ne hv5.symm h48.ne n46 n42 n45 h86.ne n82 n85
        h26.ne.symm n65 h25.ne)

/-- `diam3_minDegree4` with its conclusion in the form of formal-conjectures'
`Erdos64.erdos_64` (a cycle of length `2 ^ k` with `k ≥ 2`). Only the conclusion has that form:
the hypotheses (`ediam ≤ 3`, minimum degree `≥ 4`) are stronger than `erdos_64`'s. -/
theorem erdos_64_of_diam3 (hδ : 4 ≤ G.minDegree) (hd : G.ediam ≤ 3) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  obtain ⟨v, c, hc, h | h⟩ := diam3_minDegree4 hδ hd
  · exact ⟨2, v, c, le_rfl, hc, by simpa using h⟩
  · exact ⟨3, v, c, by norm_num, hc, by simpa using h⟩

/-- Carr's theorem with its conclusion in the form of formal-conjectures' `Erdos64.erdos_64`
(a cycle of length `2 ^ k` with `k ≥ 2`). Only the conclusion has that form: the extra
hypothesis `ediam ≤ 2` is not in `erdos_64`. -/
theorem erdos_64_of_diam2 (hδ : 3 ≤ G.minDegree) (hd : G.ediam ≤ 2) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  obtain ⟨v, c, hc, h | h⟩ := carr_diam2 hδ hd
  · exact ⟨2, v, c, le_rfl, hc, by simpa using h⟩
  · exact ⟨3, v, c, by norm_num, hc, by simpa using h⟩

end Erdos64Diam

#print axioms Erdos64Diam.carr_diam2
#print axioms Erdos64Diam.diam3_minDegree4
#print axioms Erdos64Diam.erdos_64_of_diam3
#print axioms Erdos64Diam.erdos_64_of_diam2
