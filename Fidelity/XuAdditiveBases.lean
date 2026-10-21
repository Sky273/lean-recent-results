import RecentResults.XuAdditiveBases
import Mathlib

/-!
# Fidelity bridge: blind statements (Xu arXiv:2605.10771 / BvHK arXiv:2409.07442)
derived from the verified module `RecentResults.XuAdditiveBases`.

The blind definitions and statements are copied verbatim (namespace changed to
`FidelityBridge.XuBVHK` to avoid clashes); every proof below uses only the theorems of
`XuBvHK` (our formalization) plus Mathlib.
-/

open Pointwise

namespace FidelityBridge.XuBVHK

/-- `S` is a basis of the real vector space `ℝ^n`, viewed as a *set* of vectors. -/
def IsBasisSet {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  LinearIndepOn ℝ id S ∧ Submodule.span ℝ S = ⊤

/-- `{e_i + e_j : 1 ≤ i ≤ j ≤ n} ⊆ A + B` in `ℚ^n`. -/
def CoversDiagSums {n : ℕ} (A B : Set (Fin n → ℚ)) : Prop :=
  {v : Fin n → ℚ | ∃ i j : Fin n, i ≤ j ∧ v = Pi.single i 1 + Pi.single j 1} ⊆ A + B

/-! ### Glue lemmas -/

/-- A set-basis of `ℝ^n` is the range of an indexed `Module.Basis (Fin n)`. -/
lemma exists_basis_of_isBasisSet {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsBasisSet S) :
    ∃ b : Module.Basis (Fin n) ℝ (Fin n → ℝ), Set.range b = S := by
  obtain ⟨hli, hsp⟩ := hS
  have hli' := hli.linearIndependent
  have hsp' : ⊤ ≤ Submodule.span ℝ (Set.range fun x : S => id (x : Fin n → ℝ)) := by
    have : (Set.range fun x : S => id (x : Fin n → ℝ)) = S := by
      simp only [id]; exact Subtype.range_coe
    rw [this, hsp]
  let b0 : Module.Basis S ℝ (Fin n → ℝ) := Module.Basis.mk hli' hsp'
  let e : S ≃ Fin n := b0.indexEquiv (Pi.basisFun ℝ (Fin n))
  refine ⟨b0.reindex e, ?_⟩
  rw [Module.Basis.range_reindex, Module.Basis.coe_mk]
  simp only [id]; exact Subtype.range_coe

lemma covers_iff {n : ℕ} {A B : Set (Fin n → ℚ)} (h : CoversDiagSums A B) :
    ∀ i j : Fin n, i ≤ j → (Pi.single i 1 + Pi.single j 1 : Fin n → ℚ) ∈ A + B :=
  fun i j hij => h ⟨i, j, hij, rfl⟩

lemma covers_symm {n : ℕ} {A B : Set (Fin n → ℚ)} (h : CoversDiagSums A B) :
    CoversDiagSums B A := by
  unfold CoversDiagSums at *; rw [add_comm]; exact h

/-! ### Bridges -/

-- Xu, Theorem 1.1
theorem theorem_1_1 (n : ℕ) (S A B : Set (Fin n → ℝ)) (hS : IsBasisSet S)
    (hSAB : S + S ⊆ A + B) (t : ℕ) (ht : t + 1 ≤ n)
    (hA : A.encard ≤ ((n - t : ℕ) : ℕ∞)) :
    ((n + (t + 1).choose 2 : ℕ) : ℕ∞) ≤ B.encard := by
  obtain ⟨b, hb⟩ := exists_basis_of_isBasisSet hS
  exact _root_.XuBvHK.theorem_1_1 n b A B (by rw [hb]; exact hSAB) t (by omega) hA

-- Xu, sharpness paragraph after Theorem 1.1
theorem theorem_1_1_sharp (n : ℕ) (S : Set (Fin n → ℝ)) (hS : IsBasisSet S)
    (t : ℕ) (ht : t + 1 ≤ n) :
    ∃ A B : Set (Fin n → ℝ), S + S ⊆ A + B ∧
      A.encard = ((n - t : ℕ) : ℕ∞) ∧
      B.encard = ((n + (t + 1).choose 2 : ℕ) : ℕ∞) := by
  obtain ⟨b, hb⟩ := exists_basis_of_isBasisSet hS
  obtain ⟨A, B, h1, h2, h3⟩ := _root_.XuBvHK.theorem_1_1_sharp n b t (by omega)
  exact ⟨A, B, by rw [← hb]; exact h1, h2, h3⟩

-- Xu, Corollary 1.2
theorem corollary_1_2 (n : ℕ) (A B : Set (Fin n → ℚ)) (hAB : CoversDiagSums A B)
    (t : ℕ) (ht : t + 1 ≤ n) (hA : A.encard ≤ ((n - t : ℕ) : ℕ∞)) :
    ((n + (t + 1).choose 2 : ℕ) : ℕ∞) ≤ B.encard :=
  _root_.XuBvHK.corollary_1_2 n A B (covers_iff hAB) t (by omega) hA

/-- Sum form over `ℚ^n`, derived from our Corollary 1.2 (with the `A ↔ B` symmetry). -/
lemma sum_step {n : ℕ} (X Y : Set (Fin n → ℚ)) (hXf : X.Finite) (hYf : Y.Finite)
    (hXY : CoversDiagSums X Y) (hX1 : 1 ≤ X.ncard) (hXn : X.ncard ≤ n) :
    2 * n ≤ X.ncard + Y.ncard := by
  have h := _root_.XuBvHK.corollary_1_2 n X Y (covers_iff hXY) (n - X.ncard) (by omega)
    (by rw [← hXf.cast_ncard_eq]; exact_mod_cast (by omega : X.ncard ≤ n - (n - X.ncard)))
  rw [← hYf.cast_ncard_eq] at h
  have h' : n + (n - X.ncard + 1).choose 2 ≤ Y.ncard := by exact_mod_cast h
  rw [_root_.XuBvHK.choose_two_succ] at h'
  omega

-- BvHK Conjecture 13. Derived here from our Corollary 1.2; it also follows from the sum form
-- over `ℝ^n` already proved by B. Alexeev in plby/lean-proofs (see `bukh_question_sum`).
theorem bvhk_conjecture_13 (n : ℕ) (B₀ B₁ : Set (Fin n → ℚ)) (h : CoversDiagSums B₀ B₁) :
    ((2 * n : ℕ) : ℕ∞) ≤ B₀.encard + B₁.encard := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  by_cases h0 : B₀.encard = ⊤
  · simp [h0]
  by_cases h1 : B₁.encard = ⊤
  · simp [h1]
  have hf0 : B₀.Finite := Set.encard_ne_top_iff.mp h0
  have hf1 : B₁.Finite := Set.encard_ne_top_iff.mp h1
  obtain ⟨a, ha, b, hb, -⟩ := Set.mem_add.mp (covers_iff h ⟨0, hn⟩ ⟨0, hn⟩ le_rfl)
  have hA1 : 1 ≤ B₀.ncard := Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos hf0).mpr ⟨a, ha⟩).ne'
  have hB1 : 1 ≤ B₁.ncard := Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos hf1).mpr ⟨b, hb⟩).ne'
  rw [← hf0.cast_ncard_eq, ← hf1.cast_ncard_eq]
  suffices hs : 2 * n ≤ B₀.ncard + B₁.ncard by exact_mod_cast hs
  by_cases hAn : B₀.ncard ≤ n
  · exact sum_step B₀ B₁ hf0 hf1 h hA1 hAn
  by_cases hBn : B₁.ncard ≤ n
  · have := sum_step B₁ B₀ hf1 hf0 (covers_symm h) hB1 hBn; omega
  omega

-- BvHK extension of Conjecture 13, original "=" wording
theorem bvhk_conjecture_13_extension (n : ℕ) (B₀ B₁ : Set (Fin n → ℚ))
    (h : CoversDiagSums B₀ B₁) (t : ℕ) (hB₀ : B₀.encard + t = n) :
    ((n + (t + 1).choose 2 : ℕ) : ℕ∞) ≤ B₁.encard := by
  have hfin : B₀.encard ≠ ⊤ := by
    intro htop; rw [htop, top_add] at hB₀; exact ENat.top_ne_natCast n hB₀
  have hf0 : B₀.Finite := Set.encard_ne_top_iff.mp hfin
  rw [← hf0.cast_ncard_eq] at hB₀
  have hcard : B₀.ncard + t = n := by exact_mod_cast hB₀
  rcases Nat.eq_zero_or_pos B₀.ncard with h0 | hpos
  · -- `B₀ = ∅`: vacuous for `n ≥ 1`, trivial for `n = 0`
    have hempty : B₀ = ∅ := (Set.ncard_eq_zero hf0).mp h0
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; have : t = 0 := by omega
      subst this; simp
    · exfalso
      have := covers_iff h ⟨0, hn⟩ ⟨0, hn⟩ le_rfl
      rw [hempty, Set.empty_add] at this
      exact this
  · apply corollary_1_2 n B₀ B₁ h t (by omega)
    rw [← hf0.cast_ncard_eq]; exact_mod_cast (by omega : B₀.ncard ≤ n - t)

-- Bukh's question, sum form, over `ℝ^n` with an arbitrary basis: "Must |A|+|B|≥2n hold?"
-- (https://borisbukh.org/problems.html#l20, now item 9 under "...but someone else can!";
-- cited as [2, Problem 12] in Xu's paper). Already proved by B. Alexeev in plby/lean-proofs
-- (`src/latest/BorisBukh/BasisSubset.lean`); here it is derived from our Theorem 1.1 through
-- `XuBvHK.Check.basis_sumset_cardinality_bound`, which has plby's statement verbatim.
theorem bukh_question_sum (n : ℕ) (S A B : Set (Fin n → ℝ)) (hS : IsBasisSet S)
    (hSAB : S + S ⊆ A + B) :
    ((2 * n : ℕ) : ℕ∞) ≤ A.encard + B.encard := by
  obtain ⟨b, hb⟩ := exists_basis_of_isBasisSet hS
  have := _root_.XuBvHK.Check.basis_sumset_cardinality_bound n b A B (by rw [hb]; exact hSAB)
  push_cast; exact this

-- Xu, Lemma 2.2
theorem lemma_2_2 (n : ℕ) (hn : 2 ≤ n) {Γ : Type*} [AddCommGroup Γ] (K : AddSubgroup Γ)
    (φ : (Fin n → ZMod 2) ≃+ K) (u : ℕ) (hu : u ≤ n) (X C : Set Γ) (hXC : X ⊆ C)
    (hX : X.encard ≤ ((n - u : ℕ) : ℕ∞))
    (hD : ∀ i j : Fin n, i < j →
      ((φ (Pi.single i 1 + Pi.single j 1) : K) : Γ) ∈ X - C) :
    ((n + u.choose 2 : ℕ) : ℕ∞) ≤ C.encard := by
  classical
  by_cases hCtop : C.encard = ⊤
  · simp [hCtop]
  have hCf : C.Finite := Set.encard_ne_top_iff.mp hCtop
  have hXf : X.Finite := hCf.subset hXC
  let ι : (Fin n → ZMod 2) →+ Γ := K.subtype.comp φ.toAddMonoidHom
  have hιapp : ∀ v, ι v = ((φ v : K) : Γ) := fun v => rfl
  have hι : Function.Injective ι := by
    intro v w hvw
    rw [hιapp, hιapp] at hvw
    exact φ.injective (Subtype.ext hvw)
  let Xf := hXf.toFinset
  let Cf := hCf.toFinset
  have hXCf : Xf ⊆ Cf := by
    intro x hx
    exact hCf.mem_toFinset.mpr (hXC (hXf.mem_toFinset.mp hx))
  have hDf : ∀ i j : Fin n, i ≠ j → ι (Pi.single i 1 + Pi.single j 1) ∈ Xf - Cf := by
    intro i j hij
    have hmem : ((φ (Pi.single i 1 + Pi.single j 1) : K) : Γ) ∈ X - C := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact hD i j h
      · rw [add_comm]; exact hD j i h
    obtain ⟨x, hx, c, hc, hxc⟩ := Set.mem_sub.mp hmem
    exact Finset.mem_sub.mpr ⟨x, hXf.mem_toFinset.mpr hx, c, hCf.mem_toFinset.mpr hc, hxc⟩
  have hXne : Xf.Nonempty := by
    have h01 : (⟨0, by omega⟩ : Fin n) < ⟨1, by omega⟩ := by simp [Fin.lt_def]
    obtain ⟨x, hx, -, -, -⟩ := Set.mem_sub.mp (hD _ _ h01)
    exact ⟨x, hXf.mem_toFinset.mpr hx⟩
  obtain ⟨X', C', hX'C', hX'ne, hX'card, hC'card, hD'⟩ :=
    _root_.XuBvHK.fold_to_K n ι hι Xf Cf hXCf hXne hDf
  have hK := _root_.XuBvHK.lemma_2_2_K n X' C' hX'C' hX'ne hD'
  have hXcard : Xf.card ≤ n - u := by
    rw [hXf.encard_eq_coe_toFinset_card] at hX; exact_mod_cast hX
  rw [hCf.encard_eq_coe_toFinset_card]
  have hm1 : 1 ≤ X'.card := Finset.card_pos.mpr hX'ne
  have hmle : X'.card ≤ n - u := by omega
  have hk1 : n + 1 - X'.card = (n - X'.card) + 1 := by omega
  rw [hk1, _root_.XuBvHK.choose_two_succ] at hK
  have hku : u.choose 2 ≤ (n - X'.card).choose 2 := Nat.choose_le_choose 2 (by omega)
  have : n + u.choose 2 ≤ Cf.card := by omega
  exact_mod_cast this

/-- BvHK notation `D(A) = min{|B| : B ⊆ D, A ⊆ B + B}`. -/
noncomputable def basisNumber {G : Type*} [AddCommMonoid G] (D A : Set G) : ℕ∞ :=
  ⨅ (B : Set G) (_ : B ⊆ D) (_ : A ⊆ B + B), B.encard

def intsInRat : Set ℚ := Set.range (Int.cast : ℤ → ℚ)

/-! ### Change-of-domain consequence (Xu, paragraph after Corollary 1.2)

Our module contains neither BvHK's reduction (Lemmas 6–7) nor BvHK Theorem 1, so the
statement is derived here from our Corollary 1.2 (through the bridged `bvhk_conjecture_13`)
with a self-contained version of BvHK's reduction, specialised to `k = 2`:
`A_x = {2x_i + 2x_j + 1}` has the rational 2-basis `{2x_i + 1/2}` and the integer 2-basis
`{2x_i} ∪ {2x_i + 1}`. If every `A_x` (`x ∈ ℤⁿ`) had an integer 2-basis of size `< 2n`,
splitting it by parity would put every `x` in one of finitely many "pattern" subspaces of
`ℚⁿ`. Then one pattern subspace would be all of `ℚⁿ` (a vector space over an infinite field is
not a finite union of proper subspaces), and evaluating it at the standard basis gives a
vector-model pair contradicting Conjecture 13. -/

lemma basisNumber_le {G : Type*} [AddCommMonoid G] {D A B : Set G} (hBD : B ⊆ D)
    (hAB : A ⊆ B + B) : basisNumber D A ≤ B.encard :=
  iInf_le_of_le B (iInf_le_of_le hBD (iInf_le_of_le hAB le_rfl))

lemma le_basisNumber {G : Type*} [AddCommMonoid G] {D A : Set G} {k : ℕ∞}
    (h : ∀ B : Set G, B ⊆ D → A ⊆ B + B → k ≤ B.encard) : k ≤ basisNumber D A :=
  le_iInf fun B => le_iInf fun hBD => le_iInf fun hAB => h B hBD hAB

lemma encard_range_fin_le {α : Type*} {n : ℕ} (f : Fin n → α) :
    (Set.range f).encard ≤ (n : ℕ∞) := by
  rw [← Set.image_univ]
  refine (Set.encard_image_le f _).trans ?_
  simp

/-- The pattern subspace: `x` such that `x_i + x_j = y_{P(i,j).1} + z_{P(i,j).2}` is solvable. -/
def patSub (n m0 m1 : ℕ) (P : Fin n → Fin n → Fin m0 × Fin m1) :
    Submodule ℚ (Fin n → ℚ) where
  carrier := {x | ∃ y : Fin m0 → ℚ, ∃ z : Fin m1 → ℚ,
    ∀ i j, x i + x j = y (P i j).1 + z (P i j).2}
  add_mem' := by
    rintro x x' ⟨y, z, h⟩ ⟨y', z', h'⟩
    refine ⟨y + y', z + z', fun i j => ?_⟩
    simp only [Pi.add_apply]
    linarith [h i j, h' i j]
  zero_mem' := ⟨0, 0, fun i j => by simp⟩
  smul_mem' := by
    rintro c x ⟨y, z, h⟩
    refine ⟨c • y, c • z, fun i j => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_add, ← mul_add, h i j]

lemma patSub_ne_top (n m0 m1 : ℕ) (hm : m0 + m1 < 2 * n)
    (P : Fin n → Fin n → Fin m0 × Fin m1) : patSub n m0 m1 P ≠ ⊤ := by
  intro htop
  have hk : ∀ k : Fin n, ∃ y : Fin m0 → ℚ, ∃ z : Fin m1 → ℚ, ∀ i j,
      (Pi.single k 1 : Fin n → ℚ) i + (Pi.single k 1 : Fin n → ℚ) j =
        y (P i j).1 + z (P i j).2 := by
    intro k
    have : (Pi.single k 1 : Fin n → ℚ) ∈ patSub n m0 m1 P := by
      rw [htop]; exact Submodule.mem_top
    exact this
  choose y z hyz using hk
  let b : Fin m0 → (Fin n → ℚ) := fun p k => y k p
  let c : Fin m1 → (Fin n → ℚ) := fun q k => z k q
  have hcov : CoversDiagSums (Set.range b) (Set.range c) := by
    rintro _ ⟨i, j, -, rfl⟩
    refine Set.mem_add.mpr ⟨b (P i j).1, ⟨_, rfl⟩, c (P i j).2, ⟨_, rfl⟩, ?_⟩
    funext k
    simp only [Pi.add_apply, b, c]
    rw [← hyz k i j]
    simp only [Pi.single_apply]
    by_cases hi : i = k <;> by_cases hj : j = k <;> simp [hi, hj, eq_comm]
  have h13 := bvhk_conjecture_13 n _ _ hcov
  have hsum : (Set.range b).encard + (Set.range c).encard ≤ ((m0 + m1 : ℕ) : ℕ∞) := by
    push_cast; exact add_le_add (encard_range_fin_le b) (encard_range_fin_le c)
  have : 2 * n ≤ m0 + m1 := by exact_mod_cast h13.trans hsum
  omega

/-- Index type of the patterns with `m0 + m1 < 2n`. -/
abbrev PatIdx (n : ℕ) :=
  Σ m : {m : Fin (2 * n) × Fin (2 * n) // (m.1 : ℕ) + m.2 < 2 * n},
    (Fin n → Fin n → Fin (m.1.1 : ℕ) × Fin (m.1.2 : ℕ))

/-- `A_x = {2x_i + 2x_j + 1}` as a set of rationals. -/
def Ax {n : ℕ} (x : Fin n → ℤ) : Set ℚ :=
  Set.range (fun ij : Fin n × Fin n => ((2 * x ij.1 + 2 * x ij.2 + 1 : ℤ) : ℚ))

/-- Parity splitting: a small integer 2-basis of `A_x` puts `x` in a pattern subspace. -/
lemma mem_pat_of_small_basis {n : ℕ} (x : Fin n → ℤ) (B : Set ℚ) (hBZ : B ⊆ intsInRat)
    (hAB : Ax x ⊆ B + B) (hB : B.encard < ((2 * n : ℕ) : ℕ∞)) :
    ∃ s : PatIdx n, (fun i => (x i : ℚ)) ∈ patSub n s.1.1.1 s.1.1.2 s.2 := by
  classical
  let B' : Set ℤ := Int.cast ⁻¹' B
  have hcast : Function.Injective (Int.cast : ℤ → ℚ) := Int.cast_injective
  have hBimg : (Int.cast : ℤ → ℚ) '' B' = B := by
    ext q; constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hq; obtain ⟨u, rfl⟩ := hBZ hq; exact ⟨u, hq, rfl⟩
  have hB'enc : B'.encard = B.encard := by rw [← hBimg, hcast.encard_image]
  let B0 : Set ℤ := {a | 2 * a ∈ B'}
  let B1 : Set ℤ := {a | 2 * a + 1 ∈ B'}
  have hsplit : B0.encard + B1.encard ≤ B'.encard := by
    have hinj0 : Function.Injective (fun a : ℤ => 2 * a) := fun a b h => by simpa using h
    have hinj1 : Function.Injective (fun a : ℤ => 2 * a + 1) := fun a b h => by simpa using h
    have hdisj : Disjoint ((fun a : ℤ => 2 * a) '' B0) ((fun a : ℤ => 2 * a + 1) '' B1) := by
      rw [Set.disjoint_left]
      rintro _ ⟨a, -, rfl⟩ ⟨b, -, hb⟩
      simp only at hb; omega
    have hsub : (fun a : ℤ => 2 * a) '' B0 ∪ (fun a : ℤ => 2 * a + 1) '' B1 ⊆ B' := by
      rintro _ (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · exact ha
      · exact ha
    have := Set.encard_le_encard hsub
    rwa [Set.encard_union_eq hdisj, hinj0.encard_image, hinj1.encard_image] at this
  have hlt : B0.encard + B1.encard < ((2 * n : ℕ) : ℕ∞) :=
    (hsplit.trans_eq hB'enc).trans_lt hB
  have hB0f : B0.Finite := Set.encard_ne_top_iff.mp (by
    intro h; rw [h, top_add] at hlt; exact absurd hlt (not_lt.mpr le_top))
  have hB1f : B1.Finite := Set.encard_ne_top_iff.mp (by
    intro h; rw [h, add_top] at hlt; exact absurd hlt (not_lt.mpr le_top))
  let F0 := hB0f.toFinset
  let F1 := hB1f.toFinset
  have hcard : F0.card + F1.card < 2 * n := by
    rw [hB0f.encard_eq_coe_toFinset_card, hB1f.encard_eq_coe_toFinset_card] at hlt
    exact_mod_cast hlt
  -- every `x_i + x_j` lies in `B0 + B1`
  have hrep : ∀ i j : Fin n, ∃ a ∈ B0, ∃ b ∈ B1, a + b = x i + x j := by
    intro i j
    have hmem : ((2 * x i + 2 * x j + 1 : ℤ) : ℚ) ∈ B + B := hAB ⟨(i, j), rfl⟩
    obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Set.mem_add.mp hmem
    obtain ⟨u, rfl⟩ := hBZ hβ
    obtain ⟨v, rfl⟩ := hBZ hγ
    have huv : u + v = 2 * x i + 2 * x j + 1 := by exact_mod_cast hβγ
    have hu : u ∈ B' := hβ
    have hv : v ∈ B' := hγ
    rcases Int.even_or_odd' u with ⟨r, hr | hr⟩
    · refine ⟨r, ?_, x i + x j - r, ?_, by ring⟩
      · show 2 * r ∈ B'; rw [← hr]; exact hu
      · show 2 * (x i + x j - r) + 1 ∈ B'
        have : 2 * (x i + x j - r) + 1 = v := by omega
        rw [this]; exact hv
    · refine ⟨x i + x j - r, ?_, r, ?_, by ring⟩
      · show 2 * (x i + x j - r) ∈ B'
        have : 2 * (x i + x j - r) = v := by omega
        rw [this]; exact hv
      · show 2 * r + 1 ∈ B'; rw [← hr]; exact hu
  choose a ha b hb hab using hrep
  let e0 := F0.equivFin
  let e1 := F1.equivFin
  let P : Fin n → Fin n → Fin F0.card × Fin F1.card := fun i j =>
    (e0 ⟨a i j, hB0f.mem_toFinset.mpr (ha i j)⟩, e1 ⟨b i j, hB1f.mem_toFinset.mpr (hb i j)⟩)
  refine ⟨⟨⟨(⟨F0.card, by omega⟩, ⟨F1.card, by omega⟩), hcard⟩, P⟩, ?_⟩
  refine ⟨fun p => ((e0.symm p : F0) : ℤ), fun q => ((e1.symm q : F1) : ℤ), fun i j => ?_⟩
  simp only [P, Equiv.symm_apply_apply]
  exact_mod_cast (hab i j).symm

lemma exists_common_denom {n : ℕ} (q : Fin n → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ z : Fin n → ℤ, ∀ i, (z i : ℚ) = d * q i := by
  classical
  refine ⟨∏ i, (q i).den, Finset.prod_pos fun i _ => (q i).den_pos, ?_⟩
  have hdvd : ∀ i, (q i).den ∣ ∏ k, (q k).den :=
    fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  choose k hk using hdvd
  refine ⟨fun i => (k i : ℤ) * (q i).num, fun i => ?_⟩
  rw [hk i]
  push_cast
  rw [mul_comm ((q i).den : ℚ) (k i : ℚ), mul_assoc, Rat.den_mul_eq_num]

-- Xu, paragraph after Corollary 1.2 (change-of-domain consequence)
theorem change_of_domain_factor_two_sharp (n : ℕ) :
    ∃ A : Set ℚ, A ⊆ intsInRat ∧
      basisNumber (Set.univ : Set ℚ) A ≤ (n : ℕ∞) ∧
      basisNumber intsInRat A = ((2 * n : ℕ) : ℕ∞) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨∅, Set.empty_subset _, ?_, ?_⟩
    · exact (basisNumber_le (B := ∅) (Set.empty_subset _) (Set.empty_subset _)).trans (by simp)
    · apply le_antisymm
      · exact (basisNumber_le (B := ∅) (Set.empty_subset _) (Set.empty_subset _)).trans
          (by simp)
      · simp
  -- a "generic" `x ∈ ℤⁿ`
  obtain ⟨x, hx⟩ : ∃ x : Fin n → ℤ, ∀ B : Set ℚ, B ⊆ intsInRat → Ax x ⊆ B + B →
      ((2 * n : ℕ) : ℕ∞) ≤ B.encard := by
    by_contra hcon
    push Not at hcon
    have hcover : ⋃ s : PatIdx n, (patSub n s.1.1.1 s.1.1.2 s.2 : Set (Fin n → ℚ)) =
        Set.univ := by
      apply Set.eq_univ_of_forall
      intro q
      obtain ⟨d, hd, z, hz⟩ := exists_common_denom q
      obtain ⟨B, hBZ, hAB, hlt⟩ := hcon z
      obtain ⟨s, hs⟩ := mem_pat_of_small_basis z B hBZ hAB hlt
      refine Set.mem_iUnion.mpr ⟨s, ?_⟩
      have hq : q = (d : ℚ)⁻¹ • (fun i => (z i : ℚ)) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, hz i]
        have : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
        field_simp
      rw [hq]
      exact (patSub n s.1.1.1 s.1.1.2 s.2).smul_mem _ hs
    obtain ⟨s, hs⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcover
    exact patSub_ne_top n _ _ s.1.2 s.2 hs
  refine ⟨Ax x, ?_, ?_, ?_⟩
  · rintro _ ⟨ij, rfl⟩; exact ⟨_, rfl⟩
  · -- rational 2-basis `{2x_i + 1/2}` of size `≤ n`
    refine (basisNumber_le (B := Set.range fun i : Fin n => 2 * (x i : ℚ) + 1 / 2)
      (Set.subset_univ _) ?_).trans (encard_range_fin_le _)
    rintro _ ⟨⟨i, j⟩, rfl⟩
    refine Set.mem_add.mpr ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, ?_⟩
    push_cast; ring
  · apply le_antisymm
    · -- integer 2-basis `{2x_i} ∪ {2x_i + 1}` of size `≤ 2n`
      let B0 : Set ℚ := Set.range fun i : Fin n => ((2 * x i : ℤ) : ℚ)
      let B1 : Set ℚ := Set.range fun i : Fin n => ((2 * x i + 1 : ℤ) : ℚ)
      refine (basisNumber_le (B := B0 ∪ B1) ?_ ?_).trans ?_
      · rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> exact ⟨_, rfl⟩
      · rintro _ ⟨⟨i, j⟩, rfl⟩
        refine Set.mem_add.mpr ⟨_, Or.inl ⟨i, rfl⟩, _, Or.inr ⟨j, rfl⟩, ?_⟩
        push_cast; ring
      · refine (Set.encard_union_le _ _).trans ?_
        have h0 := encard_range_fin_le (fun i : Fin n => ((2 * x i : ℤ) : ℚ))
        have h1 := encard_range_fin_le (fun i : Fin n => ((2 * x i + 1 : ℤ) : ℚ))
        calc B0.encard + B1.encard ≤ (n : ℕ∞) + n := add_le_add h0 h1
          _ = ((2 * n : ℕ) : ℕ∞) := by push_cast; ring
    · exact le_basisNumber fun B hBD hAB => hx B hBD hAB

end FidelityBridge.XuBVHK

#print axioms FidelityBridge.XuBVHK.theorem_1_1
#print axioms FidelityBridge.XuBVHK.theorem_1_1_sharp
#print axioms FidelityBridge.XuBVHK.corollary_1_2
#print axioms FidelityBridge.XuBVHK.bvhk_conjecture_13
#print axioms FidelityBridge.XuBVHK.bvhk_conjecture_13_extension
#print axioms FidelityBridge.XuBVHK.bukh_question_sum
#print axioms FidelityBridge.XuBVHK.lemma_2_2
#print axioms FidelityBridge.XuBVHK.change_of_domain_factor_two_sharp
