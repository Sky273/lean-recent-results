import Mathlib

/-!
# Xu's theorem on the strengthened Bukh–van Hintum–Keevash conjecture

Formalization of Z. Xu, *A solution to a strengthened conjecture of Bukh, van Hintum and
Keevash on additive bases*, arXiv:2605.10771 (v1, 2026-05-11).

Main results (namespace `XuBvHK`):
* `theorem_1_1` (Theorem 1.1): if `S` is a basis of `ℝⁿ`, `A, B ⊆ ℝⁿ`, `S + S ⊆ A + B`,
  `0 ≤ t ≤ n − 1` and `|A| ≤ n − t`, then `|B| ≥ n + C(t+1, 2)`;
* `theorem_1_1_sharp`: the bound is attained for every basis `S` and every such `t`
  (the construction stated right after Theorem 1.1);
* `corollary_1_2` (Corollary 1.2): the rational vector model, `A, B ⊆ ℚⁿ` with
  `{eᵢ + eⱼ : i ≤ j} ⊆ A + B`, i.e. the extension of BvHK Conjecture 13 (Bukh, van Hintum and
  Keevash, arXiv:2409.07442).

Cardinalities are `Set.encard : ℕ∞`, so `A` and `B` may be infinite.

The sum form `|A| + |B| ≥ 2n` (Bukh's question over `ℝⁿ`, whose case `ℚⁿ` with the standard
basis is BvHK Conjecture 13) had already been proved in Lean by B. Alexeev in
plby/lean-proofs; see the last section, where that statement is re-derived from
`theorem_1_1`.

## Structure of the proof

The file follows §2 of the paper, with one change: Claim 2.1 (the diagonal edges form a
forest), the contraction count (2) and the bound `|C| ≤ |V(H)|` are replaced by a single
rank–nullity argument, `forest_colour_bound`, so no graph theory is needed.

1. `forest_colour_bound`: the rank–nullity replacement just described.
2. `lemma_K_of_zero_mem`, `lemma_2_2_K`: Lemma 2.2 when `X, C ⊆ K = 𝔽₂ⁿ` (Claim 2.3 and the
   counting that follows it).
3. `fold_to_K`: the reduction of the general case of Lemma 2.2 to `K` (folding the
   `K`-cosets, Claim 2.4).
4. `Γ`, `ι`, `pi_pair_eq_ι`: the colour group `ℝⁿ/2ℤⁿ` and the identification
   `K = ℤⁿ/2ℤⁿ ≅ 𝔽₂ⁿ` under which Lemma 2.2 is applied.
5. `core`, `theorem_1_1`: the final count of §2 for the standard basis, then the reduction
   from an arbitrary basis (first paragraph of §2).
6. `theorem_1_1_sharp`, `corollary_1_2`.
7. `XuBvHK.Check.basis_sumset_cardinality_bound`: plby's statement, re-derived.

The fidelity bridge `Fidelity/XuAdditiveBases.lean` derives from these theorems the
independently written ("blind") statements of `Fidelity/Blind/XuAdditiveBases.lean`.
-/

open Finset
open scoped Pointwise

namespace XuBvHK

/-! ## Rank–nullity replacement for Claim 2.1 and the contraction count (2) -/

/-- Rank–nullity replacement for Claim 2.1, the contraction count (2) and `|C| ≤ |V(H)|`
in §2 of the paper. The vertices `V` carry potentials `φ` and colours `c`; the edges
`(u i, w i)`, `i : ι`, play the role of the diagonal edges. If `c` is constant along every
edge and the potential differences `φ (u i) - φ (w i)` are linearly independent, then
`#ι + #(colours) ≤ #V`. -/
theorem forest_colour_bound
    {V ι Γ M : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq Γ]
    [AddCommGroup M] [Module ℝ M]
    (φ : V → M) (c : V → Γ) (u w : ι → V)
    (hc : ∀ i, c (u i) = c (w i))
    (hli : LinearIndependent ℝ (fun i => φ (u i) - φ (w i))) :
    Fintype.card ι + (univ.image c).card ≤ Fintype.card V := by
  classical
  set T : Finset Γ := univ.image c with hT
  -- class-sum map  Σ : ℝ^V → ℝ^T
  let Sg : (V → ℝ) →ₗ[ℝ] (T → ℝ) :=
    LinearMap.pi fun γ => Fintype.linearCombination ℝ (fun v => if c v = γ.1 then (1 : ℝ) else 0)
  have Sg_apply : ∀ f γ, Sg f γ = ∑ v, f v * (if c v = γ.1 then (1 : ℝ) else 0) := by
    intro f γ
    simp [Sg, Fintype.linearCombination_apply, smul_eq_mul]
  -- edge vectors
  let f : ι → (V → ℝ) := fun i => Pi.single (u i) 1 - Pi.single (w i) 1
  -- potential map
  let Φ : (V → ℝ) →ₗ[ℝ] M := Fintype.linearCombination ℝ φ
  have hΦ : ∀ i, Φ (f i) = φ (u i) - φ (w i) := by
    intro i
    simp [Φ, f, Fintype.linearCombination_apply, sub_smul, Finset.sum_sub_distrib,
      Pi.single_apply]
  have hf : LinearIndependent ℝ f := by
    apply LinearIndependent.of_comp Φ
    have : (Φ ∘ f) = fun i => φ (u i) - φ (w i) := funext hΦ
    rw [this]; exact hli
  have hfker : Submodule.span ℝ (Set.range f) ≤ LinearMap.ker Sg := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    funext γ
    rw [Sg_apply]
    simp only [f, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hc i, sub_self,
      Pi.zero_apply]
  have hker : Fintype.card ι ≤ Module.finrank ℝ (LinearMap.ker Sg) := by
    rw [← finrank_span_eq_card hf]
    exact Submodule.finrank_mono hfker
  -- surjectivity of Σ
  have hsurj : LinearMap.range Sg = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℝ T).span_eq, Submodule.span_le]
    rintro _ ⟨γ, rfl⟩
    obtain ⟨v₀, -, hv₀⟩ := Finset.mem_image.mp γ.2
    refine ⟨Pi.single v₀ 1, ?_⟩
    funext δ
    rw [Sg_apply, Pi.basisFun_apply]
    simp only [Pi.single_apply]
    rw [Finset.sum_eq_single v₀ (by intro b _ hb; simp [hb]) (by simp)]
    by_cases h : δ = γ
    · subst h; simp [hv₀]
    · have : c v₀ ≠ δ.1 := by
        intro h'; exact h (Subtype.ext (h'.symm.trans hv₀))
      simp [h, this]
  have hrange : Module.finrank ℝ (LinearMap.range Sg) = T.card := by
    rw [hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hrn := LinearMap.finrank_range_add_finrank_ker Sg
  rw [hrange, Module.finrank_fintype_fun_eq_card] at hrn
  omega

/-! ## Lemma 2.2 when `X, C ⊆ K = 𝔽₂ⁿ`

The paper's proof of this case reaches `|C| ≥ m + C(s, 2)` with `m = |X|` and
`s = dim(𝔽₂ⁿ/W) ≥ n − m + 1`, hence `|C| ≥ |X| + C(n + 1 − |X|, 2)`; this is the form proved
here. Since `m + C(n − m + 1, 2) = n + C(n − m, 2)`, it is Lemma 2.2 with `u = n − |X|`
(for `|X| ≤ n`), and it implies Lemma 2.2 for every `u ≤ n − |X|`. -/

/-- `𝔽₂ⁿ`. -/
abbrev F2n (n : ℕ) := Fin n → ZMod 2

/-- In a `ZMod 2`-module, `-q = q`. -/
lemma zmod2_module_neg_eq {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q] (q : Q) :
    -q = q := by
  have h : q + q = 0 := by
    rw [← two_smul (ZMod 2) q]
    have : (2 : ZMod 2) = 0 := by decide
    rw [this, zero_smul]
  rw [neg_eq_iff_add_eq_zero]; exact h

/-- Over `ZMod 2`, sums of a linearly independent family over finite subsets are injective. -/
lemma subset_sum_inj {ι Q : Type*} [DecidableEq ι] [AddCommGroup Q] [Module (ZMod 2) Q]
    {v : ι → Q} {J : Set ι} (hv : LinearIndepOn (ZMod 2) v J)
    {P P' : Finset ι} (hP : (P : Set ι) ⊆ J) (hP' : (P' : Set ι) ⊆ J)
    (h : ∑ i ∈ P, v i = ∑ i ∈ P', v i) : P = P' := by
  have hv' : LinearIndepOn (ZMod 2) v ((P ∪ P' : Finset ι) : Set ι) :=
    hv.mono (by rw [coe_union]; exact Set.union_subset hP hP')
  rw [linearIndepOn_finset_iff] at hv'
  let g : ι → ZMod 2 := fun i => (if i ∈ P then 1 else 0) - (if i ∈ P' then 1 else 0)
  have hsum : ∑ i ∈ P ∪ P', g i • v i = 0 := by
    simp only [g, sub_smul, ite_smul, one_smul, zero_smul, sum_sub_distrib]
    rw [← sum_filter, ← sum_filter]
    have e1 : (P ∪ P').filter (· ∈ P) = P := by
      ext i; simp only [mem_filter, mem_union]; tauto
    have e2 : (P ∪ P').filter (· ∈ P') = P' := by
      ext i; simp only [mem_filter, mem_union]; tauto
    rw [e1, e2, h, sub_self]
  have key := hv' g hsum
  ext i
  by_cases hi : i ∈ P ∪ P'
  · have := key i hi
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    by_cases h1 : i ∈ P <;> by_cases h2 : i ∈ P' <;> simp [g, h1, h2] at this ⊢
  · simp only [mem_union, not_or] at hi
    simp [hi.1, hi.2]

/-- Lemma 2.2 for `X, C ⊆ K = 𝔽₂ⁿ` with `0 ∈ X`, in the form `|C| ≥ |X| + C(n + 1 − |X|, 2)`
(step (b) below is Claim 2.3). -/
theorem lemma_K_of_zero_mem (n : ℕ) (X C : Finset (F2n n)) (hXC : X ⊆ C) (h0 : (0 : F2n n) ∈ X)
    (hD : ∀ i j : Fin n, i ≠ j → (Pi.single i 1 + Pi.single j 1 : F2n n) ∈ X - C) :
    X.card + (n + 1 - X.card).choose 2 ≤ C.card := by
  classical
  set W : Submodule (ZMod 2) (F2n n) := Submodule.span (ZMod 2) (X : Set (F2n n)) with hWdef
  set ρ := W.mkQ with hρ
  -- (a) dim W ≤ |X| - 1
  have hW : Module.finrank (ZMod 2) W ≤ X.card - 1 := by
    have hWe : W = Submodule.span (ZMod 2) ((X.erase 0 : Finset (F2n n)) : Set (F2n n)) := by
      rw [hWdef]
      conv_lhs => rw [← insert_erase h0, coe_insert]
      rw [Submodule.span_insert_zero]
    have := finrank_span_finset_le_card (R := ZMod 2) (X.erase 0)
    rw [card_erase_of_mem h0] at this
    rw [hWe]; exact this
  have hQ : Module.finrank (ZMod 2) (F2n n ⧸ W) + Module.finrank (ZMod 2) W = n := by
    rw [Submodule.finrank_quotient_add_finrank, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  have hXpos : 1 ≤ X.card := card_pos.mpr ⟨0, h0⟩
  -- (b) ρ(D) ⊆ ρ(C)
  have hρD : ∀ i j : Fin n, i ≠ j →
      ∃ c ∈ C, ρ c = ρ (Pi.single i 1 + Pi.single j 1) := by
    intro i j hij
    obtain ⟨x, hx, c, hc, hxc⟩ := mem_sub.mp (hD i j hij)
    refine ⟨c, hc, ?_⟩
    rw [← hxc, map_sub]
    have hx0 : ρ x = 0 := (Submodule.Quotient.mk_eq_zero W).mpr (Submodule.subset_span hx)
    rw [hx0, zero_sub, zmod2_module_neg_eq]
  -- (c) a spanning independent set of indices
  let v : Fin n → (F2n n ⧸ W) := fun i => ρ (Pi.single i 1)
  obtain ⟨J, -, -, hJspan, hJli⟩ :=
    exists_linearIndepOn_extension (K := ZMod 2) (v := v) (s := ∅) (t := Set.univ)
      (linearIndepOn_empty _ _) (Set.empty_subset _)
  have hspanJ : Submodule.span (ZMod 2) (v '' J) = ⊤ := by
    rw [eq_top_iff]
    have h1 : Submodule.span (ZMod 2) (Set.range v) = ⊤ := by
      have : Set.range v = ρ '' Set.range (fun i : Fin n => (Pi.single i 1 : F2n n)) := by
        rw [← Set.range_comp]; rfl
      rw [this, Submodule.span_image]
      have hb := (Pi.basisFun (ZMod 2) (Fin n)).span_eq
      rw [show (fun i : Fin n => (Pi.single i 1 : F2n n)) = ⇑(Pi.basisFun (ZMod 2) (Fin n)) from
        funext fun i => (Pi.basisFun_apply _ _ i).symm]
      rw [hb, Submodule.map_top, hρ, Submodule.range_mkQ]
    rw [← h1, Submodule.span_le, ← Set.image_univ]
    exact hJspan
  have hJcard : Module.finrank (ZMod 2) (F2n n ⧸ W) = J.toFinset.card := by
    have := finrank_span_eq_card (R := ZMod 2) (b := fun x : J => v x) hJli
    rw [← finrank_top (ZMod 2) (F2n n ⧸ W), ← hspanJ, Set.image_eq_range, this,
      Set.toFinset_card]
  -- (d) counting
  have hcount1 : X.card + ((C.image ρ).erase 0).card ≤ C.card := by
    rw [← card_filter_add_card_filter_not (s := C) (fun c => ρ c = 0)]
    apply add_le_add
    · apply card_le_card
      intro x hx
      rw [mem_filter]
      exact ⟨hXC hx, (Submodule.Quotient.mk_eq_zero W).mpr (Submodule.subset_span hx)⟩
    · calc ((C.image ρ).erase 0).card
          = ((C.filter fun c => ¬ ρ c = 0).image ρ).card := by
            congr 1; ext q; simp only [mem_erase, mem_image, mem_filter]
            constructor
            · rintro ⟨hq, c, hc, rfl⟩; exact ⟨c, ⟨hc, hq⟩, rfl⟩
            · rintro ⟨c, ⟨hc, hq⟩, rfl⟩; exact ⟨hq, c, hc, rfl⟩
        _ ≤ _ := card_image_le
  have hcount2 : (J.toFinset.powersetCard 2).card ≤ ((C.image ρ).erase 0).card := by
    apply card_le_card_of_injOn (fun P => ∑ i ∈ P, v i)
    · intro P hP
      rw [mem_coe, mem_powersetCard] at hP
      obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp hP.2
      rw [mem_coe, mem_erase, mem_image]
      constructor
      · intro hzero
        have hsub : ((({i, j} : Finset (Fin n))) : Set (Fin n)) ⊆ J := by
          intro k hk; have := hP.1 (mem_coe.mp hk); simpa using this
        have := subset_sum_inj hJli hsub (P' := ∅) (by simp) (by simpa using hzero)
        simp at this
      · obtain ⟨c, hc, hρc⟩ := hρD i j hij
        refine ⟨c, hc, ?_⟩
        show ρ c = ∑ k ∈ {i, j}, v k
        rw [sum_pair hij, hρc, map_add]
    · intro P hP P' hP' h
      rw [mem_coe, mem_powersetCard] at hP hP'
      have s1 : (P : Set (Fin n)) ⊆ J := fun k hk => by simpa using hP.1 (mem_coe.mp hk)
      have s2 : (P' : Set (Fin n)) ⊆ J := fun k hk => by simpa using hP'.1 (mem_coe.mp hk)
      exact subset_sum_inj hJli s1 s2 h
  rw [card_powersetCard, ← hJcard] at hcount2
  have hmono : (n + 1 - X.card).choose 2 ≤ (Module.finrank (ZMod 2) (F2n n ⧸ W)).choose 2 :=
    Nat.choose_le_choose 2 (by omega)
  omega

/-- Lemma 2.2 for `X, C ⊆ K = 𝔽₂ⁿ`, in the form `|C| ≥ |X| + C(n + 1 − |X|, 2)` (equivalent
to Lemma 2.2 with `u = n − |X|`, see the section header). The translation by `x₀ ∈ X`
reduces it to `lemma_K_of_zero_mem`. The covering hypothesis is stated for `i ≠ j`; since
`eᵢ + eⱼ = eⱼ + eᵢ`, this is the paper's `Dₙ ⊆ X − C` (`i < j`). -/
theorem lemma_2_2_K
    (n : ℕ) (X C : Finset (F2n n)) (hXC : X ⊆ C) (hX : X.Nonempty)
    (hD : ∀ i j : Fin n, i ≠ j → (Pi.single i 1 + Pi.single j 1 : F2n n) ∈ X - C) :
    X.card + (n + 1 - X.card).choose 2 ≤ C.card := by
  classical
  obtain ⟨x₀, hx₀⟩ := hX
  have hinj : Function.Injective (fun y : F2n n => y - x₀) := sub_left_injective
  have h := lemma_K_of_zero_mem n (X.image (· - x₀)) (C.image (· - x₀))
    (image_subset_image hXC) (mem_image.mpr ⟨x₀, hx₀, sub_self x₀⟩) (by
      intro i j hij
      obtain ⟨x, hx, c, hc, hxc⟩ := mem_sub.mp (hD i j hij)
      exact mem_sub.mpr ⟨x - x₀, mem_image_of_mem _ hx, c - x₀, mem_image_of_mem _ hc,
        by rw [← hxc]; abel⟩)
  rwa [card_image_of_injective _ hinj, card_image_of_injective _ hinj] at h

/-! ## General case of Lemma 2.2: folding onto `K` -/

/-- The reduction of the general case of Lemma 2.2 to `K` (Claim 2.4): every `K`-coset
meeting `X` is folded back onto `K`, where `K` is the image of the injective homomorphism
`ι : 𝔽₂ⁿ →+ G`. The folded sets `X' ⊆ C' ⊆ 𝔽₂ⁿ` are no larger than `X` and `C`, and still
satisfy the covering hypothesis. -/
theorem fold_to_K {G : Type*} [AddCommGroup G] [DecidableEq G] (n : ℕ)
    (ι : (Fin n → ZMod 2) →+ G) (hι : Function.Injective ι)
    (X C : Finset G) (hXC : X ⊆ C) (hX : X.Nonempty)
    (hD : ∀ i j : Fin n, i ≠ j → ι (Pi.single i 1 + Pi.single j 1) ∈ X - C) :
    ∃ X' C' : Finset (Fin n → ZMod 2), X' ⊆ C' ∧ X'.Nonempty ∧ X'.card ≤ X.card ∧
      C'.card ≤ C.card ∧ ∀ i j : Fin n, i ≠ j → (Pi.single i 1 + Pi.single j 1) ∈ X' - C' := by
  classical
  let K : AddSubgroup G := ι.range
  let q : G → G ⧸ K := QuotientAddGroup.mk
  let r : G ⧸ K → G := fun κ => if h : ∃ x ∈ X, q x = κ then h.choose else 0
  have hr : ∀ γ : G, (∃ x ∈ X, q γ = q x) → q (r (q γ)) = q γ := by
    intro γ ⟨x, hx, hγx⟩
    have h : ∃ x ∈ X, q x = q γ := ⟨x, hx, hγx.symm⟩
    simp only [r, h, dite_true]
    exact h.choose_spec.2
  let g : G → (Fin n → ZMod 2) := fun γ => Function.invFun ι (γ - r (q γ))
  have hg : ∀ γ : G, (∃ x ∈ X, q γ = q x) → ι (g γ) = γ - r (q γ) := by
    intro γ hγ
    have hmem : γ - r (q γ) ∈ K := by
      have := hr γ hγ
      rw [QuotientAddGroup.eq] at this
      have h2 : -(-r (q γ) + γ) ∈ K := K.neg_mem this
      have h3 : γ - r (q γ) = -(-(-r (q γ) + γ)) := by abel
      rw [h3]; exact K.neg_mem h2
    obtain ⟨y, hy⟩ := hmem
    exact Function.invFun_eq ⟨y, hy⟩
  let Cf := C.filter (fun c => ∃ x ∈ X, q c = q x)
  refine ⟨X.image g, Cf.image g, ?_, hX.image g, card_image_le, ?_, ?_⟩
  · apply image_subset_image
    intro x hx
    exact mem_filter.mpr ⟨hXC hx, x, hx, rfl⟩
  · exact card_image_le.trans (card_filter_le _ _)
  · intro i j hij
    obtain ⟨x, hx, c, hc, hxc⟩ := mem_sub.mp (hD i j hij)
    have hqc : q c = q x := by
      rw [QuotientAddGroup.eq]
      refine ⟨Pi.single i 1 + Pi.single j 1, ?_⟩
      change ι _ = -c + x
      rw [← hxc]; abel
    have hcX : ∃ x' ∈ X, q c = q x' := ⟨x, hx, hqc⟩
    have hxX : ∃ x' ∈ X, q x = q x' := ⟨x, hx, rfl⟩
    refine mem_sub.mpr ⟨g x, mem_image_of_mem _ hx, g c,
      mem_image_of_mem _ (mem_filter.mpr ⟨hc, hcX⟩), ?_⟩
    apply hι
    rw [map_sub, hg x hxX, hg c hcX, hqc, ← hxc]
    abel

/-! ## The colour group `ℝⁿ/2ℤⁿ`

The colour group `Γ = ℝⁿ/2ℤⁿ`, the embedding `ι : 𝔽₂ⁿ →+ Γ` with image `K = ℤⁿ/2ℤⁿ`, and
`π(eᵢ + eⱼ) = ι(eᵢ + eⱼ)` for `i ≠ j`: the identification of `K` with `𝔽₂ⁿ` under which the
paper applies Lemma 2.2 at the end of §2. -/

/-- `2ℤⁿ ⊆ ℝⁿ`. -/
def L (n : ℕ) : AddSubgroup (Fin n → ℝ) :=
  AddSubgroup.pi Set.univ (fun _ => AddSubgroup.zmultiples (2 : ℝ))

/-- The colour group `ℝⁿ/2ℤⁿ`. -/
abbrev Γ (n : ℕ) := (Fin n → ℝ) ⧸ L n

lemma mem_L {n : ℕ} (v : Fin n → ℝ) : v ∈ L n ↔ ∀ i, ∃ k : ℤ, k • (2 : ℝ) = v i := by
  simp [L, AddSubgroup.mem_pi, AddSubgroup.mem_zmultiples_iff]

/-- `ZMod 2 → ℝ`, `0 ↦ 0`, `1 ↦ 1`. -/
noncomputable def lift2 (a : ZMod 2) : ℝ := if a = 0 then 0 else 1

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

lemma one_ne_zero2 : (1 : ZMod 2) ≠ 0 := by decide
lemma one_add_one2 : (1 + 1 : ZMod 2) = 0 := by decide

lemma lift2_add_sub (a b : ZMod 2) : ∃ k : ℤ, k • (2 : ℝ) = lift2 a + lift2 b - lift2 (a + b) := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · exact ⟨0, by simp [lift2]⟩
  · exact ⟨0, by simp [lift2]⟩
  · exact ⟨0, by simp [lift2]⟩
  · exact ⟨1, by simp [lift2, one_add_one2]; norm_num⟩

/-- The embedding `ι : 𝔽₂ⁿ →+ ℝⁿ/2ℤⁿ`. -/
noncomputable def ι (n : ℕ) : (Fin n → ZMod 2) →+ Γ n where
  toFun v := QuotientAddGroup.mk (fun i => lift2 (v i))
  map_zero' := by
    rw [QuotientAddGroup.eq_zero_iff]
    simp only [Pi.zero_apply, lift2]
    exact (L n).zero_mem
  map_add' v w := by
    rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq, mem_L]
    intro i
    obtain ⟨k, hk⟩ := lift2_add_sub (v i) (w i)
    exact ⟨k, by rw [hk]; simp; ring⟩

lemma lift2_eq_zero_of {a : ZMod 2} (h : ∃ k : ℤ, k • (2 : ℝ) = -lift2 a) : a = 0 := by
  obtain ⟨k, hk⟩ := h
  rcases zmod2_cases a with rfl | rfl
  · rfl
  · exfalso
    simp only [lift2, one_ne_zero2, ite_false, zsmul_eq_mul] at hk
    have h2 : (k * 2 : ℤ) = -1 := by exact_mod_cast hk
    omega

lemma ι_injective (n : ℕ) : Function.Injective (ι n) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  change QuotientAddGroup.mk _ = ((0 : Fin n → ℝ) : Γ n) at hv
  rw [QuotientAddGroup.eq, mem_L] at hv
  funext i
  apply lift2_eq_zero_of
  obtain ⟨k, hk⟩ := hv i
  exact ⟨k, by rw [hk]; simp⟩

/-- `π(eᵢ + eⱼ) = ι(eᵢ + eⱼ)` for `i ≠ j`. -/
lemma pi_pair_eq_ι {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (QuotientAddGroup.mk (Pi.single i 1 + Pi.single j 1 : Fin n → ℝ) : Γ n) =
      ι n (Pi.single i 1 + Pi.single j 1) := by
  change _ = QuotientAddGroup.mk _
  congr 1
  funext k
  by_cases hki : k = i
  · subst hki; simp [lift2, hij]
  · by_cases hkj : k = j
    · subst hkj; simp [lift2, hki]
    · simp [lift2, hki, hkj]

/-! ## Theorem 1.1 -/

/-- The vectors `2eᵢ` are linearly independent. -/
lemma two_single_li (n : ℕ) :
    LinearIndependent ℝ (fun i : Fin n => (Pi.single i 1 + Pi.single i 1 : Fin n → ℝ)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have := congrFun hg i
  simp [Finset.sum_apply, Pi.single_apply] at this
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq] at this
  simp at this
  linarith

/-- `C(k+1, 2) = k + C(k, 2)`. -/
lemma choose_two_succ (k : ℕ) : (k + 1).choose 2 = k + k.choose 2 := by
  have := Nat.choose_succ_succ' k 1
  simpa [Nat.choose_one_right] using this

/-- Finite core, standard basis: `|A| ≤ n - u` implies `|A| + |B| ≥ 2n + C(u,2)`.
This is the final count of §2: the vertices `A ⊔ B` get the potential `a ↦ a`, `b ↦ -b` and
its colour in `ℝⁿ/2ℤⁿ`; `forest_colour_bound` handles the diagonal sums `2eᵢ`, and Lemma 2.2
(`fold_to_K`, then `lemma_2_2_K`) the off-diagonal sums `eᵢ + eⱼ`. -/
theorem core (n u : ℕ) (hn : 1 ≤ n) (A B : Finset (Fin n → ℝ))
    (hcontains : ∀ i j : Fin n, ∃ a ∈ A, ∃ b ∈ B,
      a + b = (Pi.single i 1 + Pi.single j 1 : Fin n → ℝ))
    (hu : A.card ≤ n - u) :
    n + n + u.choose 2 ≤ A.card + B.card := by
  classical
  choose a ha b hb hab using hcontains
  let φ : (↥A ⊕ ↥B) → (Fin n → ℝ) := Sum.elim (fun x => x.1) (fun y => -y.1)
  let c : (↥A ⊕ ↥B) → Γ n := fun v => (QuotientAddGroup.mk (φ v) : Γ n)
  let uu : Fin n → (↥A ⊕ ↥B) := fun i => Sum.inl ⟨a i i, ha i i⟩
  let ww : Fin n → (↥A ⊕ ↥B) := fun i => Sum.inr ⟨b i i, hb i i⟩
  have hc : ∀ i, c (uu i) = c (ww i) := by
    intro i
    simp only [c, φ, uu, ww, Sum.elim_inl, Sum.elim_inr]
    rw [QuotientAddGroup.eq, mem_L]
    intro k
    have := congrFun (hab i i) k
    by_cases hk : k = i
    · subst hk; refine ⟨-1, ?_⟩; simp at this ⊢; linarith
    · refine ⟨0, ?_⟩; simp [hk] at this ⊢; linarith
  have hli : LinearIndependent ℝ (fun i => φ (uu i) - φ (ww i)) := by
    have : (fun i => φ (uu i) - φ (ww i)) =
        fun i => (Pi.single i 1 + Pi.single i 1 : Fin n → ℝ) := by
      funext i; simp only [φ, uu, ww, Sum.elim_inl, Sum.elim_inr, sub_neg_eq_add]; exact hab i i
    rw [this]; exact two_single_li n
  have hforest := forest_colour_bound φ c uu ww hc hli
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, Fintype.card_fin] at hforest
  set Cset := (Finset.univ : Finset (↥A ⊕ ↥B)).image c with hCset
  set Xset := (Finset.univ : Finset ↥A).image (fun x => c (Sum.inl x)) with hXset
  have hXC : Xset ⊆ Cset := by
    intro γ hγ
    obtain ⟨x, -, rfl⟩ := mem_image.mp hγ
    exact mem_image_of_mem _ (mem_univ _)
  have hXcard : Xset.card ≤ A.card := by
    calc Xset.card ≤ (Finset.univ : Finset ↥A).card := card_image_le
      _ = A.card := by simp
  have hXne : Xset.Nonempty := by
    let i0 : Fin n := ⟨0, hn⟩
    exact ⟨_, mem_image_of_mem _ (mem_univ ⟨a i0 i0, ha i0 i0⟩)⟩
  have hD : ∀ i j : Fin n, i ≠ j → ι n (Pi.single i 1 + Pi.single j 1) ∈ Xset - Cset := by
    intro i j hij
    refine mem_sub.mpr ⟨c (Sum.inl ⟨a i j, ha i j⟩), mem_image_of_mem _ (mem_univ _),
      c (Sum.inr ⟨b i j, hb i j⟩), mem_image_of_mem _ (mem_univ _), ?_⟩
    rw [← pi_pair_eq_ι hij, ← hab i j]
    simp only [c, φ, Sum.elim_inl, Sum.elim_inr]
    rw [← QuotientAddGroup.mk_sub, sub_neg_eq_add]
  obtain ⟨X', C', hX'C', hX'ne, hX'card, hC'card, hD'⟩ :=
    fold_to_K n (ι n) (ι_injective n) Xset Cset hXC hXne hD
  have hK := lemma_2_2_K n X' C' hX'C' hX'ne hD'
  have hm1 : 1 ≤ X'.card := card_pos.mpr hX'ne
  have hmle : X'.card ≤ n - u := by omega
  have hk1 : n + 1 - X'.card = (n - X'.card) + 1 := by omega
  rw [hk1, choose_two_succ] at hK
  have hku : u.choose 2 ≤ (n - X'.card).choose 2 := Nat.choose_le_choose 2 (by omega)
  omega

/-- **Theorem 1.1** (Xu, arXiv:2605.10771). The basis is an indexed `Module.Basis`,
`|A|` and `|B|` are `Set.encard` (an infinite `B` makes the conclusion trivial), and
`0 ≤ t ≤ n − 1` is `t < n`. The proof maps `S` to the standard basis (first paragraph of §2)
and applies `core`. -/
theorem theorem_1_1
    (n : ℕ) (S : Module.Basis (Fin n) ℝ (Fin n → ℝ)) (A B : Set (Fin n → ℝ))
    (hcontains : (Set.range S + Set.range S : Set (Fin n → ℝ)) ⊆ A + B)
    (t : ℕ) (ht : t < n) (hA : A.encard ≤ ((n - t : ℕ) : ℕ∞)) :
    ((n + (t + 1).choose 2 : ℕ) : ℕ∞) ≤ B.encard := by
  classical
  by_cases hBtop : B.encard = ⊤
  · simp [hBtop]
  have hBfin : B.Finite := Set.encard_ne_top_iff.mp hBtop
  have hAfin : A.Finite := Set.encard_ne_top_iff.mp (ne_top_of_le_ne_top (by simp) hA)
  let e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) := S.equivFun
  have heS : ∀ i, e (S i) = (Pi.single i 1 : Fin n → ℝ) := by
    intro i; funext j
    simp [e, Pi.single_apply, eq_comm]
  let A' := hAfin.toFinset.image e
  let B' := hBfin.toFinset.image e
  have hcont' : ∀ i j : Fin n, ∃ a ∈ A', ∃ b ∈ B',
      a + b = (Pi.single i 1 + Pi.single j 1 : Fin n → ℝ) := by
    intro i j
    have hmem : S i + S j ∈ (Set.range S + Set.range S : Set (Fin n → ℝ)) :=
      Set.mem_add.mpr ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    obtain ⟨a, haA, b, hbB, habS⟩ := Set.mem_add.mp (hcontains hmem)
    refine ⟨e a, mem_image_of_mem _ (hAfin.mem_toFinset.mpr haA), e b,
      mem_image_of_mem _ (hBfin.mem_toFinset.mpr hbB), ?_⟩
    rw [← map_add, habS, map_add, heS, heS]
  have hA'card : A'.card = A.ncard := by
    rw [card_image_of_injective _ e.injective, Set.ncard_eq_toFinset_card A hAfin]
  have hB'card : B'.card = B.ncard := by
    rw [card_image_of_injective _ e.injective, Set.ncard_eq_toFinset_card B hBfin]
  have hAle : A.ncard ≤ n - t := by
    rw [← hAfin.cast_ncard_eq] at hA; exact_mod_cast hA
  have hcore := core n t (by omega) A' B' hcont' (by rw [hA'card]; exact hAle)
  rw [hA'card, hB'card] at hcore
  rw [← hBfin.cast_ncard_eq]
  have : n + (t + 1).choose 2 ≤ B.ncard := by
    rw [choose_two_succ]
    omega
  exact_mod_cast this

/-! ## Sharpness and Corollary 1.2 -/

/-- **Sharpness of Theorem 1.1** (construction stated after Theorem 1.1 in Xu's paper):
`A = {s_i : i < n − t}` and `B = S ∪ {s_i + s_j − s_0 : n − t ≤ i ≤ j}` (0-indexed). -/
theorem theorem_1_1_sharp
    (n : ℕ) (S : Module.Basis (Fin n) ℝ (Fin n → ℝ)) (t : ℕ) (ht : t < n) :
    ∃ A B : Set (Fin n → ℝ),
      (Set.range S + Set.range S : Set (Fin n → ℝ)) ⊆ A + B ∧
      A.encard = ((n - t : ℕ) : ℕ∞) ∧ B.encard = ((n + (t + 1).choose 2 : ℕ) : ℕ∞) := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let IA : Finset (Fin n) := univ.filter (fun k => (k : ℕ) < n - t)
  let IT : Finset (Fin n) := univ.filter (fun k => ¬ (k : ℕ) < n - t)
  have hIA : IA.card = n - t := by
    simp only [IA, Fin.card_filter_val_lt]; omega
  have hIT : IT.card = t := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun k : Fin n => (k : ℕ) < n - t)
    rw [card_univ, Fintype.card_fin] at this
    change IA.card + IT.card = n at this
    omega
  have hi0A : i0 ∈ IA := by simp [IA, i0]; omega
  have hITne : ∀ k ∈ IT, k ≠ i0 := by
    intro k hk h; subst h; simp [IT, i0] at hk; omega
  have hSinj : Function.Injective S := S.injective
  -- coordinates w.r.t. S
  let e := S.equivFun
  have heS : ∀ k j, e (S k) j = if k = j then 1 else 0 := fun k j => by simp [e]
  let f : Sym2 (Fin n) → (Fin n → ℝ) :=
    Sym2.lift ⟨fun i j => S i + S j - S i0, fun i j => by simp only; rw [add_comm (S i)]⟩
  have hf : ∀ i j, f s(i, j) = S i + S j - S i0 := fun i j => rfl
  let Af : Finset (Fin n → ℝ) := IA.image S
  let B1 : Finset (Fin n → ℝ) := univ.image S
  let B2 : Finset (Fin n → ℝ) := IT.sym2.image f
  -- f values have coordinate -1 at i0, basis vectors have coordinate 0 or 1
  have hf_i0 : ∀ i ∈ IT, ∀ j ∈ IT, e (f s(i, j)) i0 = -1 := by
    intro i hi j hj
    rw [hf, map_sub, map_add]
    simp only [Pi.sub_apply, Pi.add_apply, heS, ite_eq_right (hITne i hi),
      ite_eq_right (hITne j hj)]
    simp
  have hdisj : Disjoint B1 B2 := by
    rw [disjoint_left]
    intro v hv1 hv2
    obtain ⟨k, -, rfl⟩ := mem_image.mp hv1
    obtain ⟨z, hz, hzk⟩ := mem_image.mp hv2
    induction z using Sym2.ind with
    | _ i j =>
      rw [mk_mem_sym2_iff] at hz
      have h1 := hf_i0 i hz.1 j hz.2
      rw [hzk, heS] at h1
      split_ifs at h1 <;> norm_num at h1
  have hfinj : Set.InjOn f (IT.sym2 : Set (Sym2 (Fin n))) := by
    intro z hz z' hz' hzz'
    induction z using Sym2.ind with
    | _ i j =>
    induction z' using Sym2.ind with
    | _ i' j' =>
      rw [hf, hf, sub_left_inj] at hzz'
      have hc : ∀ k, (if i = k then (1:ℝ) else 0) + (if j = k then 1 else 0) =
          (if i' = k then 1 else 0) + (if j' = k then 1 else 0) := by
        intro k
        have := congrArg (fun v => e v k) hzz'
        simpa [heS] using this
      rw [Sym2.eq_iff]
      rcases (show i = i' ∨ i = j' from by
          by_contra hne
          push Not at hne
          have h := hc i
          rw [ite_eq_left rfl, ite_eq_right (Ne.symm hne.1), ite_eq_right (Ne.symm hne.2)] at h
          split_ifs at h <;> norm_num at h) with h | h
      · subst h
        left; refine ⟨rfl, ?_⟩
        by_contra hjj
        have h := hc j
        rw [ite_eq_left rfl, ite_eq_right (Ne.symm hjj)] at h
        linarith
      · subst h
        right; refine ⟨rfl, ?_⟩
        by_contra hji
        have h := hc j
        rw [ite_eq_left rfl, ite_eq_right (Ne.symm hji)] at h
        linarith
  refine ⟨(Af : Set (Fin n → ℝ)), ((B1 ∪ B2 : Finset _) : Set (Fin n → ℝ)), ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    rw [Set.mem_add]
    by_cases hi : i ∈ IA
    · exact ⟨S i, mem_coe.mpr (mem_image_of_mem _ hi), S j, by simp [B1], rfl⟩
    by_cases hj : j ∈ IA
    · exact ⟨S j, mem_coe.mpr (mem_image_of_mem _ hj), S i, by simp [B1], add_comm _ _⟩
    have hiT : i ∈ IT := by simpa [IT, IA] using hi
    have hjT : j ∈ IT := by simpa [IT, IA] using hj
    refine ⟨S i0, by simp only [Af, coe_image]; exact ⟨i0, hi0A, rfl⟩, f s(i, j), ?_, ?_⟩
    · rw [coe_union]; right
      exact mem_coe.mpr (mem_image_of_mem _ (mk_mem_sym2_iff.mpr ⟨hiT, hjT⟩))
    · rw [hf, add_sub_cancel]
  · rw [Set.encard_coe_eq_coe_finsetCard, card_image_of_injective _ hSinj, hIA]
  · rw [Set.encard_coe_eq_coe_finsetCard, card_union_of_disjoint hdisj,
      card_image_of_injective _ hSinj, card_image_of_injOn hfinj, card_sym2, hIT, card_univ,
      Fintype.card_fin]

/-- **Corollary 1.2** (Xu): the extension of BvHK Conjecture 13 (arXiv:2409.07442) in the
rational vector model, with `|A| ≤ n − t` (BvHK wrote `|A| = n − t`). Conjecture 13 itself,
the sum form `|A| + |B| ≥ 2n`, is derived from it in `Fidelity/XuAdditiveBases.lean`
(`FidelityBridge.XuBVHK.bvhk_conjecture_13`). -/
theorem corollary_1_2
    (n : ℕ) (A B : Set (Fin n → ℚ))
    (hcontains : ∀ i j : Fin n, i ≤ j →
      (Pi.single i 1 + Pi.single j 1 : Fin n → ℚ) ∈ A + B)
    (t : ℕ) (ht : t < n) (hA : A.encard ≤ ((n - t : ℕ) : ℕ∞)) :
    ((n + (t + 1).choose 2 : ℕ) : ℕ∞) ≤ B.encard := by
  classical
  let ψ : (Fin n → ℚ) →+ (Fin n → ℝ) := AddMonoidHom.compLeft (Rat.castHom ℝ).toAddMonoidHom _
  have hψ : Function.Injective ψ := by
    intro v w h; funext k
    have := congrFun h k
    simpa [ψ] using this
  have hψe : ∀ i : Fin n, ψ (Pi.single i 1) = Pi.single i 1 := by
    intro i; funext k
    by_cases h : k = i
    · subst h; simp [ψ]
    · simp [ψ, h]
  have key := theorem_1_1 n (Pi.basisFun ℝ (Fin n)) (ψ '' A) (ψ '' B) ?_ t ht
    (by rw [hψ.encard_image]; exact hA)
  · rwa [hψ.encard_image] at key
  · rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    simp only [Pi.basisFun_apply]
    rcases le_total i j with hij | hij
    · obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp (hcontains i j hij)
      refine Set.mem_add.mpr ⟨ψ a, ⟨a, ha, rfl⟩, ψ b, ⟨b, hb, rfl⟩, ?_⟩
      rw [← map_add, hab, map_add, hψe, hψe]
    · obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp (hcontains j i hij)
      refine Set.mem_add.mpr ⟨ψ a, ⟨a, ha, rfl⟩, ψ b, ⟨b, hb, rfl⟩, ?_⟩
      rw [← map_add, hab, map_add, hψe, hψe, add_comm]

end XuBvHK

/-! ## The sum form proved in plby/lean-proofs, re-derived

Bukh's question (https://borisbukh.org/problems.html#l20, cited as [2, Problem 12] in Xu's
paper) asks whether `S + S ⊆ A + B` for a basis `S` of `ℝⁿ` forces `|A| + |B| ≥ 2n`. Its
special case `A, B ⊆ ℚⁿ`, `S` the standard basis, is BvHK Conjecture 13. B. Alexeev had
already formalized and fully proved this `ℝⁿ` statement in https://github.com/plby/lean-proofs:
statement in `src/latest/ComparatorChallenges/BorisBukh/BasisSubset.lean`, proof in
`src/latest/BorisBukh/BasisSubset.lean`, both first added on 2026-07-27. plby's
`data/more_sources.yaml` credits the formal proof to Boris Alexeev with Codex and the informal
proof to ChatGPT Pro. That statement gives Theorem 1.1 for `t ≤ 1` (as `C(2, 2) = 1`), but
only `|B| ≥ n + t` for `t ≥ 2`.

Below, plby's statement is re-derived from `XuBvHK.theorem_1_1`. It is copied verbatim
(plby's text as of 2026-10-21), including plby's `RealSpace` abbreviation; only the namespace
differs (`XuBvHK.Check` here, `BasisSubset` in plby). -/

namespace XuBvHK.Check

/-- plby's coordinate model of `ℝⁿ`, kept so that the statement below matches plby's text. -/
abbrev RealSpace (n : ℕ) : Type := Fin n → ℝ

/-- **Bukh's question, sum form** (`|A| + |B| ≥ 2n` over `ℝⁿ`, arbitrary basis `S`): the
statement of `BasisSubset.basis_sumset_cardinality_bound` in plby/lean-proofs, already proved
there by B. Alexeev (see the section header). Here it follows from `XuBvHK.theorem_1_1`,
applied with `t = n − |A|` when `1 ≤ |A| ≤ n`, otherwise with `A` and `B` swapped. -/
theorem basis_sumset_cardinality_bound
    (n : ℕ) (S : Module.Basis (Fin n) ℝ (RealSpace n)) (A B : Set (RealSpace n))
    (hcontains : (Set.range S + Set.range S : Set (RealSpace n)) ⊆ A + B) :
    (2 * n : ℕ∞) ≤ A.encard + B.encard := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  by_cases hAtop : A.encard = ⊤
  · simp [hAtop]
  by_cases hBtop : B.encard = ⊤
  · simp [hBtop]
  have hAf : A.Finite := Set.encard_ne_top_iff.mp hAtop
  have hBf : B.Finite := Set.encard_ne_top_iff.mp hBtop
  -- both nonempty
  have hmem : S ⟨0, hn⟩ + S ⟨0, hn⟩ ∈ (Set.range S + Set.range S : Set (RealSpace n)) :=
    Set.mem_add.mpr ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩
  obtain ⟨a, ha, b, hb, -⟩ := Set.mem_add.mp (hcontains hmem)
  have hA1 : 1 ≤ A.ncard := Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos hAf).mpr ⟨a, ha⟩).ne'
  have hB1 : 1 ≤ B.ncard := Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos hBf).mpr ⟨b, hb⟩).ne'
  rw [← hAf.cast_ncard_eq, ← hBf.cast_ncard_eq]
  suffices h : 2 * n ≤ A.ncard + B.ncard by exact_mod_cast h
  have hcomm : (Set.range S + Set.range S : Set (RealSpace n)) ⊆ B + A := by
    rw [add_comm B A]; exact hcontains
  have step : ∀ (X Y : Set (RealSpace n)), X.Finite → Y.Finite → 1 ≤ X.ncard →
      X.ncard ≤ n → (Set.range S + Set.range S : Set (RealSpace n)) ⊆ X + Y →
      2 * n ≤ X.ncard + Y.ncard := by
    intro X Y hXf hYf hX1 hXn hXY
    have h := XuBvHK.theorem_1_1 n S X Y hXY (n - X.ncard) (by omega)
      (by rw [← hXf.cast_ncard_eq]; exact_mod_cast (by omega : X.ncard ≤ n - (n - X.ncard)))
    rw [← hYf.cast_ncard_eq] at h
    have h' : n + (n - X.ncard + 1).choose 2 ≤ Y.ncard := by exact_mod_cast h
    rw [XuBvHK.choose_two_succ] at h'
    omega
  by_cases hAn : A.ncard ≤ n
  · exact step A B hAf hBf hA1 hAn hcontains
  by_cases hBn : B.ncard ≤ n
  · have := step B A hBf hAf hB1 hBn hcomm; omega
  omega

end XuBvHK.Check

#print axioms XuBvHK.theorem_1_1
#print axioms XuBvHK.theorem_1_1_sharp
#print axioms XuBvHK.corollary_1_2
#print axioms XuBvHK.Check.basis_sumset_cardinality_bound
