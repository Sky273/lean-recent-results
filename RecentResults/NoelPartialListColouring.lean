import Mathlib

/-!
# Noel (arXiv:2609.23291): the Partial List Colouring Conjecture is false

Formal verification of Theorem 1.1 of J. A. Noel, *The Partial List Colouring Conjecture is
False*, arXiv:2609.23291v1 (2026-09-20): there is a graph with 14 vertices and list chromatic
number 3, together with a 2-list assignment from which at most 9 vertices can be properly
coloured. Since `9 < 28/3 = 14 · (2/3)`, this refutes the Partial List Colouring Conjecture of
Albertson, Grossman and Haas (*Partial list colorings*, Discrete Math. 214 (2000)).

## Main results

* `Noel.main`: Theorem 1.1.
* `Noel.not_AGH`: the refutation of `Noel.AGHConjecture`, our statement of the conjecture as
  given in the paper's introduction.
* `PartialListColoringProportionalBoundWanted.conjecture_refuted` and
  `PartialListColoringWanted.conjecture_refuted`: the two corresponding `theorem_wanted` targets
  of facebookresearch/atlas-lean (commit 8920030e), whose statements are copied verbatim. The
  first is the AGH conjecture again. The second is Iradmusa's ratio-monotonicity conjecture
  `λ_r / r ≥ λ_s / s`, which implies AGH; it fails at `r = 2`, `s = 3`, an immediate corollary
  of Noel's example. See the section on atlas-lean below.

## Provenance of the definitions

* `Noel.IsKChoosable` and `Noel.listChromaticNumber`: copied verbatim, with their docstrings,
  from google-deepmind/formal-conjectures (commit 2a315101). Only the namespace differs.
* `Noel.IsPartialLColoring` and `Noel.AGHConjecture`: written for this project.
* `AtlasLeanCopy.SimpleGraph.IsListColorable`, `AtlasLeanCopy.SimpleGraph.IsChoiceNumber` and the
  definitions in the two `…Wanted` namespaces: copied from atlas-lean (commit 8920030e).

`Noel` is just this module's namespace, named after the paper's author. The conjecture itself is
due to Albertson, Grossman and Haas, and the copied definitions are credited above.

The proof follows Section 2 of the paper. The paper's closing remark (taking disjoint unions of
copies makes the additive gap arbitrarily large) is not formalized.
-/

open Finset

namespace Noel

/-! ### Definitions copied verbatim from formal-conjectures

From google-deepmind/formal-conjectures, file
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/List.lean` (commit 2a315101).
Bodies and docstrings are verbatim; only the namespace differs (upstream: `SimpleGraph`). -/

/--
A graph $G$ is $k$-choosable if for any assignment of a list of $k$ colours to each vertex of $G$
(perhaps different lists for different vertices) a colouring of each vertex by a colour on its list
can be chosen such that adjacent vertices receive distinct colours.
-/
def IsKChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) → ∃ C : G.Coloring ℕ, ∀ v, C v ∈ L v

/--
The list chromatic number $\chi_L(G)$, defined to be the minimal $k$ such that $G$ is
$k$-choosable. It is `0` if $G$ is not $k$-choosable for any $k$, which can only happen for an
infinite graph.
-/
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsKChoosable G k}

/-! ### Partial list colourings and the AGH conjecture (written for this project) -/

/-- `S` can be properly coloured from the lists `L`: some `f` gives every vertex of `S` a colour
from its own list, and adjacent vertices of `S` distinct colours (values of `f` outside `S` are
irrelevant). -/
def IsPartialLColoring {V : Type*} (G : SimpleGraph V) (L : V → Finset ℕ) (S : Finset V) : Prop :=
  ∃ f : V → ℕ, (∀ v ∈ S, f v ∈ L v) ∧ ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → f v ≠ f w

/-- The Partial List Colouring Conjecture of Albertson, Grossman and Haas (2000), as stated in
the introduction of arXiv:2609.23291: if a finite graph on `n` vertices has list chromatic number
`k ≥ 2` and `1 ≤ ℓ < k`, then for every `ℓ`-list assignment `L` at least `n · (ℓ / k)` vertices
can be properly coloured from `L`. The bound is stated as `ℓ * n ≤ k * |S|` in `ℕ`. The
hypothesis `2 ≤ k` also rules out the value `0` that `listChromaticNumber` takes when no `k`
works. -/
def AGHConjecture : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (k ℓ : ℕ),
    listChromaticNumber G = k → 2 ≤ k → 1 ≤ ℓ → ℓ < k →
    ∀ L : V → Finset ℕ, (∀ v, (L v).card = ℓ) →
      ∃ S : Finset V, IsPartialLColoring G L S ∧ ℓ * Fintype.card V ≤ k * S.card

/-! ### The counterexample (Section 2 of the paper)

`Sum.inl (i, j)` is vertex `j` of the triangle `T_{i+1}`, whose private vertex `p_{i+1}` is
`j = 0`; `Sum.inr 0` and `Sum.inr 1` are the terminals `s₁` and `s₂`. -/

/-- The 14 vertices: four triangles of 3 vertices, and 2 terminals. -/
abbrev V := (Fin 4 × Fin 3) ⊕ Fin 2

/-- Adjacency: the four triangles, plus all edges from both terminals to the non-private
vertices of each triangle. -/
def adj : V → V → Prop
  | .inl (i, j), .inl (i', j') => i = i' ∧ j ≠ j'
  | .inl (_, j), .inr _ => j ≠ 0
  | .inr _, .inl (_, j) => j ≠ 0
  | .inr _, .inr _ => False

instance : DecidableRel adj := fun a b => by
  rcases a with ⟨i, j⟩ | s <;> rcases b with ⟨i', j'⟩ | t <;> unfold adj <;> infer_instance

/-- The graph `G` of Section 2. -/
def G : SimpleGraph V where
  Adj := adj
  symm := ⟨by
    rintro (⟨i, j⟩ | s) (⟨i', j'⟩ | t) h <;> simp only [adj] at h ⊢ <;> tauto⟩
  loopless := ⟨by rintro (⟨i, j⟩ | s) h <;> simp [adj] at h⟩

instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel adj)

/-- The 2-list assignment of Section 2: `T₁, T₂, T₃, T₄` get `{1,3}, {1,4}, {2,3}, {2,4}`,
`L(s₁) = {1,2}` and `L(s₂) = {3,4}`. -/
def L : V → Finset ℕ
  | .inl (i, _) => ![{1, 3}, {1, 4}, {2, 3}, {2, 4}] i
  | .inr s => ![{1, 2}, {3, 4}] s

example : Fintype.card V = 14 := rfl
example : G.edgeFinset.card = 28 := by decide
example : ∀ v, (L v).card = 2 := by decide

/-! ### Part 1: at most 9 vertices are `L`-colourable -/

lemma adj_tri {i : Fin 4} {j j' : Fin 3} (h : j ≠ j') : G.Adj (.inl (i, j)) (.inl (i, j')) :=
  ⟨rfl, h⟩

lemma adj_term {i : Fin 4} {j : Fin 3} (t : Fin 2) (h : j ≠ 0) :
    G.Adj (.inr t) (.inl (i, j)) := h

lemma L_card (v : V) : (L v).card = 2 := by revert v; decide

lemma three_le_card {α : Type*} [DecidableEq α] {T : Finset α} {a b c : α} (ha : a ∈ T)
    (hb : b ∈ T) (hc : c ∈ T) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ T.card := by
  have h3 : ({a, b, c} : Finset α).card = 3 := card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩
  rw [← h3]
  apply card_le_card
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

theorem atMostNine (S : Finset V) (hS : IsPartialLColoring G L S) : S.card ≤ 9 := by
  obtain ⟨f, hf, hadj⟩ := hS
  -- no triangle is fully coloured: three pairwise distinct colours from a 2-element list
  have tri : ∀ i : Fin 4,
      ¬ (Sum.inl (i, 0) ∈ S ∧ Sum.inl (i, 1) ∈ S ∧ Sum.inl (i, 2) ∈ S) := by
    rintro i ⟨h0, h1, h2⟩
    have e01 := hadj _ h0 _ h1 (adj_tri (by decide))
    have e02 := hadj _ h0 _ h2 (adj_tri (by decide))
    have e12 := hadj _ h1 _ h2 (adj_tri (by decide))
    have m0 : f (.inl (i, 0)) ∈ L (.inl (i, 0)) := hf _ h0
    have m1 : f (.inl (i, 1)) ∈ L (.inl (i, 0)) := hf _ h1
    have m2 : f (.inl (i, 2)) ∈ L (.inl (i, 0)) := hf _ h2
    have := three_le_card m0 m1 m2 e01 e02 e12
    rw [L_card] at this
    omega
  -- if both terminals are coloured, the triangle whose list is {f s₁, f s₂} has its two
  -- non-private vertices uncoloured
  have term : Sum.inr 0 ∈ S → Sum.inr 1 ∈ S →
      ∃ i : Fin 4, Sum.inl (i, 1) ∉ S ∧ Sum.inl (i, 2) ∉ S := by
    intro hs1 hs2
    have m1 := hf _ hs1
    have m2 := hf _ hs2
    simp [L] at m1 m2
    have key : ∀ i : Fin 4, ∀ j : Fin 3, j ≠ 0 → f (.inr 0) ∈ L (.inl (i, j)) →
        f (.inr 1) ∈ L (.inl (i, j)) → Sum.inl (i, j) ∉ S := by
      intro i j hj hc hd hmem
      have a1 := hadj _ hs1 _ hmem (adj_term 0 hj)
      have a2 := hadj _ hs2 _ hmem (adj_term 1 hj)
      have m := hf _ hmem
      have hcd : f (.inr 0) ≠ f (.inr 1) := by omega
      have := three_le_card hc hd m hcd a1 a2
      rw [L_card] at this
      omega
    rcases m1 with h1 | h1 <;> rcases m2 with h2 | h2
    · exact ⟨0, key 0 1 (by decide) (by simp [L, h1]) (by simp [L, h2]),
        key 0 2 (by decide) (by simp [L, h1]) (by simp [L, h2])⟩
    · exact ⟨1, key 1 1 (by decide) (by simp [L, h1]) (by simp [L, h2]),
        key 1 2 (by decide) (by simp [L, h1]) (by simp [L, h2])⟩
    · exact ⟨2, key 2 1 (by decide) (by simp [L, h1]) (by simp [L, h2]),
        key 2 2 (by decide) (by simp [L, h1]) (by simp [L, h2])⟩
    · exact ⟨3, key 3 1 (by decide) (by simp [L, h1]) (by simp [L, h2]),
        key 3 2 (by decide) (by simp [L, h1]) (by simp [L, h2])⟩
  -- counting
  set F : Fin 4 → Finset (Fin 4 × Fin 3) := fun i => S.toLeft.filter (fun x => x.1 = i)
    with hF
  have hsplit : S.card = S.toLeft.card + S.toRight.card := card_toLeft_add_card_toRight.symm
  have hfib : S.toLeft.card = ∑ i : Fin 4, (F i).card :=
    card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (by intro x _; simp)
  rw [Fin.sum_univ_four] at hfib
  have hsubF : ∀ i, F i ⊆ {(i, 0), (i, 1), (i, 2)} := by
    intro i x hx
    obtain ⟨x1, x2⟩ := x
    simp only [hF, mem_filter, mem_toLeft] at hx
    obtain ⟨_, rfl⟩ := hx
    fin_cases x2 <;> simp
  have fib_le_two : ∀ i, (F i).card ≤ 2 := by
    intro i
    by_contra! hcon
    have heq := eq_of_subset_of_card_le (hsubF i) (card_le_three.trans hcon)
    have mem : ∀ j : Fin 3, Sum.inl (i, j) ∈ S := by
      intro j
      have : (i, j) ∈ F i := by
        rw [heq]; fin_cases j <;> simp
      simp only [hF, mem_filter, mem_toLeft] at this
      exact this.1
    exact tri i ⟨mem 0, mem 1, mem 2⟩
  have fib_le_one : ∀ i, Sum.inl (i, 1) ∉ S → Sum.inl (i, 2) ∉ S → (F i).card ≤ 1 := by
    intro i h1 h2
    rw [card_le_one]
    intro a ha b hb
    have ha' := hsubF i ha
    have hb' := hsubF i hb
    simp only [hF, mem_filter, mem_toLeft] at ha hb
    simp only [mem_insert, mem_singleton] at ha' hb'
    rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;> simp_all
  have hR : S.toRight.card ≤ 2 := (card_le_univ _).trans (by simp)
  have f0 := fib_le_two 0
  have f1 := fib_le_two 1
  have f2 := fib_le_two 2
  have f3 := fib_le_two 3
  by_cases hboth : Sum.inr 0 ∈ S ∧ Sum.inr 1 ∈ S
  · obtain ⟨i, h1, h2⟩ := term hboth.1 hboth.2
    have := fib_le_one i h1 h2
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at this <;> omega
  · have hR1 : S.toRight.card ≤ 1 := by
      rw [card_le_one]
      intro a ha b hb
      rw [mem_toRight] at ha hb
      fin_cases a <;> fin_cases b <;> simp_all
    omega

/-! ### Part 2: `G` is 3-choosable and not 2-choosable -/

/-- Greedy colouring of one triangle `u, v, p` from lists of sizes `≥ 1, ≥ 2, ≥ 3`. -/
lemma greedy {C : Type*} [DecidableEq C] (A B P : Finset C) (hA : 1 ≤ A.card)
    (hB : 2 ≤ B.card) (hP : 3 ≤ P.card) :
    ∃ x ∈ A, ∃ y ∈ B, ∃ z ∈ P, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  obtain ⟨x, hx⟩ := card_pos.1 (by omega : 0 < A.card)
  have hB' : 0 < (B.erase x).card := by
    have := pred_card_le_card_erase (s := B) (a := x); omega
  obtain ⟨y, hy⟩ := card_pos.1 hB'
  have hP' : 0 < ((P.erase x).erase y).card := by
    have := pred_card_le_card_erase (s := P) (a := x)
    have := pred_card_le_card_erase (s := P.erase x) (a := y)
    omega
  obtain ⟨z, hz⟩ := card_pos.1 hP'
  simp only [mem_erase] at hy hz
  exact ⟨x, hx, y, hy.2, z, hz.2.2, Ne.symm hy.1, Ne.symm hz.2.1, Ne.symm hz.1⟩

/-- The core of the 3-choosability argument, for lists of size exactly 3 from any colour type. -/
theorem choosable_exact {C : Type*} [DecidableEq C] (M : V → Finset C)
    (hM : ∀ v, (M v).card = 3) : ∃ col : G.Coloring C, ∀ v, col v ∈ M v := by
  -- Step 1: choose the colours `c` of `s₁` and `d` of `s₂`.
  obtain ⟨c, hc, d, hd, hgood⟩ : ∃ c ∈ M (.inr 0), ∃ d ∈ M (.inr 1),
      ∀ i : Fin 4, 2 ≤ (M (.inl (i, 2)) \ {c, d}).card := by
    by_cases hint : (M (.inr 0) ∩ M (.inr 1)).Nonempty
    · -- a common colour: give it to both terminals
      obtain ⟨c, hc⟩ := hint
      rw [mem_inter] at hc
      refine ⟨c, hc.1, c, hc.2, fun i => ?_⟩
      have h1 : ({c, c} ∩ M (.inl (i, 2))).card ≤ 1 :=
        (card_le_card inter_subset_left).trans (by simp)
      rw [card_sdiff]
      have := hM (.inl (i, 2))
      omega
    · -- disjoint lists: counting, 4 * 2 < 3 * 3
      rw [not_nonempty_iff_eq_empty] at hint
      set A := M (.inr 0) with hAdef
      set B := M (.inr 1) with hBdef
      set X : Fin 4 → Finset C := fun i => M (.inl (i, 2)) with hXdef
      set bad := (univ : Finset (Fin 4)).biUnion (fun i => (X i ∩ A) ×ˢ (X i ∩ B)) with hbad
      have hab : ∀ i, (X i ∩ A).card * (X i ∩ B).card ≤ 2 := by
        intro i
        have hdisj : Disjoint (X i ∩ A) (X i ∩ B) := by
          rw [disjoint_left]
          intro a ha hb
          have : a ∈ A ∩ B := mem_inter.2 ⟨(mem_inter.1 ha).2, (mem_inter.1 hb).2⟩
          rw [hint] at this
          simp at this
        have hu : ((X i ∩ A) ∪ (X i ∩ B)).card ≤ 3 := by
          rw [← hM (.inl (i, 2))]
          exact card_le_card (union_subset inter_subset_left inter_subset_left)
        rw [card_union_of_disjoint hdisj] at hu
        have : (X i ∩ A).card ≤ 3 := by omega
        interval_cases (X i ∩ A).card <;> omega
      have hbadcard : bad.card ≤ 8 := by
        calc bad.card ≤ ∑ i, ((X i ∩ A) ×ˢ (X i ∩ B)).card := card_biUnion_le
          _ ≤ ∑ _i : Fin 4, 2 := sum_le_sum fun i _ => by rw [card_product]; exact hab i
          _ = 8 := by simp
      have hAB : (A ×ˢ B).card = 9 := by
        rw [card_product, hAdef, hBdef, hM, hM]
      obtain ⟨⟨c, d⟩, hp, hpbad⟩ :=
        exists_mem_notMem_of_card_lt_card (by omega : bad.card < (A ×ˢ B).card)
      rw [mem_product] at hp
      refine ⟨c, hp.1, d, hp.2, fun i => ?_⟩
      have hnot : ¬ (c ∈ X i ∧ d ∈ X i) := by
        rintro ⟨h1, h2⟩
        apply hpbad
        simp only [hbad, mem_biUnion, mem_univ, true_and, mem_product, mem_inter]
        exact ⟨i, ⟨h1, hp.1⟩, ⟨h2, hp.2⟩⟩
      have h1 : ({c, d} ∩ X i).card ≤ 1 := by
        rw [card_le_one]
        intro a ha b hb
        simp only [mem_inter, mem_insert, mem_singleton] at ha hb
        rcases ha with ⟨rfl | rfl, ha⟩ <;> rcases hb with ⟨rfl | rfl, hb⟩ <;> tauto
      rw [card_sdiff]
      have := hM (.inl (i, 2))
      simp only [hXdef] at h1
      omega
  -- the other non-private vertex keeps at least one colour
  have hu : ∀ i : Fin 4, 1 ≤ (M (.inl (i, 1)) \ {c, d}).card := by
    intro i
    have h2 : ({c, d} ∩ M (.inl (i, 1))).card ≤ 2 :=
      (card_le_card inter_subset_left).trans card_le_two
    rw [card_sdiff]
    have := hM (.inl (i, 1))
    omega
  -- Step 2: colour each triangle greedily.
  have hg : ∀ i : Fin 4, ∃ x ∈ M (.inl (i, 1)) \ {c, d}, ∃ y ∈ M (.inl (i, 2)) \ {c, d},
      ∃ z ∈ M (.inl (i, 0)), x ≠ y ∧ x ≠ z ∧ y ≠ z := fun i =>
    greedy _ _ _ (hu i) (hgood i) (hM _).ge
  choose x hx y hy z hz hxy hxz hyz using hg
  simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hx hy
  have hx' : ∀ i, c ≠ x i ∧ d ≠ x i := fun i => ⟨Ne.symm (hx i).2.1, Ne.symm (hx i).2.2⟩
  have hy' : ∀ i, c ≠ y i ∧ d ≠ y i := fun i => ⟨Ne.symm (hy i).2.1, Ne.symm (hy i).2.2⟩
  let col : V → C := fun v => match v with
    | .inl (i, j) => if j = 0 then z i else if j = 1 then x i else y i
    | .inr t => if t = 0 then c else d
  refine ⟨SimpleGraph.Coloring.mk col ?_, ?_⟩
  · rintro (⟨i, j⟩ | s) (⟨i', j'⟩ | t) hadj
    · obtain ⟨rfl, hj⟩ := hadj
      fin_cases j <;> fin_cases j' <;> simp_all [col] <;> tauto
    · change j ≠ 0 at hadj
      fin_cases j <;> fin_cases t <;> simp_all [col]
    · change j' ≠ 0 at hadj
      fin_cases j' <;> fin_cases s <;> simp_all [col]
    · exact hadj.elim
  · intro v
    change col v ∈ M v
    rcases v with ⟨i, j⟩ | t
    · fin_cases j <;> simp_all [col]
    · fin_cases t <;> simp_all [col]

/-- 3-choosability for lists of size at least 3 (trim each list to exactly 3 colours). -/
theorem choosable_ge {C : Type*} [DecidableEq C] (M : V → Finset C)
    (hM : ∀ v, 3 ≤ (M v).card) : ∃ col : G.Coloring C, ∀ v, col v ∈ M v := by
  choose M' hM'sub hM'card using fun v => exists_subset_card_eq (hM v)
  obtain ⟨col, hcol⟩ := choosable_exact M' hM'card
  exact ⟨col, fun v => hM'sub v (hcol v)⟩

theorem isKChoosable_three : IsKChoosable G 3 := fun M hM => choosable_exact M hM

/-- A triangle cannot be coloured from lists `range k` with `k < 3`. -/
theorem not_colorable_range (k : ℕ) (hk : k < 3) (C : G.Coloring ℕ)
    (hC : ∀ v, C v ∈ range k) : False := by
  have h01 : C (.inl (0, 0)) ≠ C (.inl (0, 1)) := C.valid (adj_tri (by decide))
  have h02 : C (.inl (0, 0)) ≠ C (.inl (0, 2)) := C.valid (adj_tri (by decide))
  have h12 : C (.inl (0, 1)) ≠ C (.inl (0, 2)) := C.valid (adj_tri (by decide))
  have a := mem_range.1 (hC (.inl (0, 0)))
  have b := mem_range.1 (hC (.inl (0, 1)))
  have c := mem_range.1 (hC (.inl (0, 2)))
  omega

theorem not_isKChoosable_of_lt_three (k : ℕ) (hk : k < 3) : ¬ IsKChoosable G k := by
  intro h
  obtain ⟨C, hC⟩ := h (fun _ => range k) (fun _ => card_range k)
  exact not_colorable_range k hk C hC

theorem listChromaticNumber_eq_three : listChromaticNumber G = 3 := by
  unfold listChromaticNumber
  apply le_antisymm (Nat.sInf_le isKChoosable_three)
  apply le_csInf ⟨3, isKChoosable_three⟩
  intro b hb
  by_contra hlt
  exact not_isKChoosable_of_lt_three b (by omega) hb

/-- Theorem 1.1 of arXiv:2609.23291: a graph with 14 vertices and list chromatic number 3,
with a 2-list assignment from which at most 9 vertices can be properly coloured. -/
theorem main : ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W), Fintype.card W = 14 ∧
    listChromaticNumber H = 3 ∧ ∃ M : W → Finset ℕ, (∀ v, (M v).card = 2) ∧
      ∀ S : Finset W, IsPartialLColoring H M S → S.card ≤ 9 :=
  ⟨V, inferInstance, G, rfl, listChromaticNumber_eq_three, L, by decide, atMostNine⟩

/-- The Albertson–Grossman–Haas conjecture is false (`k = 3`, `ℓ = 2`): it would require
`2 · 14 ≤ 3 · |S|`, i.e. `|S| ≥ 10`, but at most 9 vertices can be coloured. -/
theorem not_AGH : ¬ AGHConjecture := by
  intro h
  obtain ⟨S, hS, hcard⟩ := h V G 3 2 listChromaticNumber_eq_three (by norm_num) one_le_two
    (by norm_num) L (by decide)
  have := atMostNine S hS
  change 2 * 14 ≤ 3 * S.card at hcard
  omega

end Noel

/-! ### The two atlas-lean `theorem_wanted` targets (facebookresearch/atlas-lean @ 8920030e)

* `PartialListColoringProportionalBoundWanted.conjecture` is the Albertson–Grossman–Haas
  conjecture, written independently by atlas-lean (exact `t`-lists from an arbitrary colour type,
  `t ≤ q`).
* `PartialListColoringWanted.conjecture` is a different conjecture: Iradmusa's
  ratio-monotonicity conjecture `λ_r / r ≥ λ_s / s` for `1 ≤ r ≤ s ≤ χ_ℓ` (Open Problem Garden,
  record OPG-788). It implies AGH (take `s = χ_ℓ`), so its refutation here (at `r = 2`, `s = 3`)
  is an immediate corollary of Noel's example, not a new result.

Copied from `MathlibExt/Combinatorics/SimpleGraph/ListColoring.lean`,
`WantedExt/Combinatorics/PartialListColoringProportionalBoundWanted.lean` and
`WantedExt/GraphTheory/PartialListColoringWanted.lean`. Definition bodies and docstrings are
verbatim, except that the docstrings of the two `conjecture`s are shortened to one sentence. Only
the namespaces differ:
* `SimpleGraph` upstream becomes `AtlasLeanCopy.SimpleGraph` here, so that this project adds no
  declarations to Mathlib's namespace; `open AtlasLeanCopy` keeps the upstream dot notation
  `G.IsChoiceNumber` working;
* `MathlibExt.Combinatorics.PartialListColoringProportionalBoundWanted` becomes
  `PartialListColoringProportionalBoundWanted`;
* `MathlibExt.GraphTheory.PartialListColoringWanted` becomes `PartialListColoringWanted`.

Upstream, `conjecture_refuted` is a `theorem_wanted` (a statement without proof); here it is
proved. -/

namespace AtlasLeanCopy

-- Needed for the dot notation `G.IsListColorable` in `IsChoiceNumber`: Lean resolves it
-- through opened namespaces, not through the current one.
open AtlasLeanCopy

/-! Copied from atlas-lean @ 8920030e, `MathlibExt/Combinatorics/SimpleGraph/ListColoring.lean`.
Only the namespace differs (upstream: `SimpleGraph`). -/
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

namespace Noel

/-- `G` has choice number 3 in the sense of atlas-lean (`IsListColorable` uses lists of size at
least `q` from an arbitrary colour type). -/
theorem isChoiceNumber_three : G.IsChoiceNumber 3 := by
  refine ⟨fun C _ lists hl => choosable_ge lists hl, fun r hr hcol => ?_⟩
  obtain ⟨col, hcol⟩ := hcol ℕ (fun _ => range r) (fun _ => by simp)
  exact not_colorable_range r hr col hcol

end Noel

namespace PartialListColoringProportionalBoundWanted

/-- A vertex subset `S` is partially list-colorable from `lists` when the induced
subgraph on `S` admits a proper coloring choosing each vertex color from its list.
The coloring is defined only on the subtype `S`, so no colors are required
outside `S`. -/
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

/-- Noel's example refutes atlas-lean's statement of the AGH conjecture at `q = 3`, `t = 2`. -/
theorem conjecture_refuted : ¬ conjecture := by
  intro h
  obtain ⟨S, ⟨color, hmem, hadj⟩, hcard⟩ :=
    h Noel.V Noel.G 3 (by norm_num) Noel.isChoiceNumber_three 2 (by norm_num) ℕ Noel.L Noel.L_card
  have hS : Noel.IsPartialLColoring Noel.G Noel.L S := by
    refine ⟨fun v => if hv : v ∈ S then color ⟨v, hv⟩ else 0, ?_, ?_⟩
    · intro v hv
      simp only [hv, dite_true]
      exact hmem ⟨v, hv⟩
    · intro v hv w hw hvw
      simp only [hv, hw, dite_true]
      exact hadj ⟨v, hv⟩ ⟨w, hw⟩ hvw
  have := Noel.atMostNine S hS
  change 2 * 14 ≤ 3 * S.card at hcard
  omega

end PartialListColoringProportionalBoundWanted

namespace PartialListColoringWanted

/-- A proper coloring of the vertex subset `S` respecting the list assignment `L`:
every vertex of `S` gets a color from its own list, and adjacent vertices get distinct colors. -/
def IsListColoring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : V → Finset ℕ) (f : V → ℕ) (S : Finset V) : Prop :=
  (∀ v ∈ S, f v ∈ L v) ∧ ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → f v ≠ f w

/-- `lambdaMax G L` is `λ_L`: the maximum number of vertices of `G` colorable
with respect to the list assignment `L` (the largest `k` for which some
`k`-element subset admits a proper list coloring). -/
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

/-- Noel's example refutes Iradmusa's conjecture at `χ_ℓ = 3`, `r = 2`, `s = 3`:
`λ_2 / 2 ≤ 9 / 2 < 14 / 3 ≤ λ_3 / 3`. -/
theorem conjecture_refuted : ¬ conjecture := by
  intro h
  have h' := h Noel.V Noel.G 3 2 3 Noel.isChoiceNumber_three (by norm_num) (by norm_num) le_rfl
  have h2 : lambdaMin Noel.G 2 ≤ 9 := by
    have hmax : lambdaMax Noel.G Noel.L ≤ 9 := by
      apply csSup_le'
      rintro k ⟨S, f, rfl, hf⟩
      exact Noel.atMostNine S ⟨f, hf.1, hf.2⟩
    unfold lambdaMin
    refine le_trans (Nat.sInf_le ?_) hmax
    exact ⟨Noel.L, Noel.L_card, rfl⟩
  have h3 : 14 ≤ lambdaMin Noel.G 3 := by
    apply le_csInf
    · exact ⟨lambdaMax Noel.G (fun _ => {0, 1, 2}), fun _ => {0, 1, 2}, fun _ => rfl, rfl⟩
    · rintro k ⟨M, hM, rfl⟩
      obtain ⟨col, hcol⟩ := Noel.choosable_exact M hM
      apply le_csSup
      · refine ⟨14, ?_⟩
        rintro k ⟨S, f, rfl, _⟩
        exact card_le_univ S
      · exact ⟨univ, col, rfl, fun v _ => hcol v, fun v _ w _ hvw => col.valid hvw⟩
  have h2q : (lambdaMin Noel.G 2 : ℚ) ≤ 9 := by exact_mod_cast h2
  have h3q : (14 : ℚ) ≤ lambdaMin Noel.G 3 := by exact_mod_cast h3
  simp only [Nat.cast_ofNat] at h'
  linarith

end PartialListColoringWanted

#print axioms Noel.main
#print axioms Noel.not_AGH
#print axioms PartialListColoringProportionalBoundWanted.conjecture_refuted
#print axioms PartialListColoringWanted.conjecture_refuted
