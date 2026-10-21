import Mathlib
import RecentResults.Erdos33

/-!
# Fidelity bridge: blind statements of Erdős #33 (13√2/4 bound) ← `RecentResults.Erdos33`

The blind definitions and statements of `Fidelity/Blind/Erdos33.lean` (written from the sources
without access to this repository) are copied verbatim. Only the namespace is renamed, to
`FidelityBridge.Erdos33Blind`, to avoid clashes; docstrings are dropped and the blind
`AdditiveBasisCondition` is moved up with the other definitions. Every `sorry` is replaced by a
proof that uses only our verified theorems `_root_.Erdos33.Aset_basis`,
`_root_.Erdos33.Aset_limsup`, `_root_.Erdos33.erdos_33_le_13_sqrt2_div_4` and
`_root_.Erdos33.erdos_33.variants.vanDoorn`.

What each blind statement is evidence for:
* **Independent of our formalization.** `IsAddComplSquares` (`m = n² + a`), its "every large
  integer" variant `IsAddComplSquaresEventually`, and `normLimsup` (real division, then cast to
  `EReal`) were written by the blind agent. The statements built on them,
  `erdos33_exists_le`, `erdos33_exists_le_eventually`, `erdos33_exists_le_eps` (real-valued
  `ε`-form) and `erdos33_L_le`, are bridged by the glue lemmas `isAddCompl_of_ours` and
  `normLimsup_eq`.
* **Same source as ours.** The blind `AdditiveBasisCondition`, `erdos33_new_bound_fc_shape` and
  `erdos33_vanDoorn` restate formal-conjectures' `erdos_33` shape, which our module also copies.
  They check the transcription, not the reading of the source; `erdos33_vanDoorn` and
  `erdos33_new_bound_fc_shape'` are closed by our theorems as bare terms.
* `new_const_lt_vanDoorn` is already proved in the blind file; `erdos33_new_bound_fc_shape'`,
  `erdos33_vanDoorn'` and `normLimsup_nonneg` are extra checks added here, not blind statements.
-/

open Filter Set

namespace FidelityBridge.Erdos33Blind

/-! ## Blind definitions (verbatim) -/

def IsAddComplSquares (A : Set ℕ) : Prop :=
  ∀ m : ℕ, ∃ n a : ℕ, a ∈ A ∧ m = n ^ 2 + a

def IsAddComplSquaresEventually (A : Set ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ n a : ℕ, a ∈ A ∧ m = n ^ 2 + a

noncomputable def countUpTo (A : Set ℕ) (N : ℕ) : ℕ := (A ∩ Icc 1 N).ncard

noncomputable def normLimsup (A : Set ℕ) : EReal :=
  limsup (fun N : ℕ => (((countUpTo A N : ℝ) / Real.sqrt N : ℝ) : EReal)) atTop

noncomputable def c : ℝ := 13 * Real.sqrt 2 / 4

noncomputable def L : EReal :=
  ⨅ A : {A : Set ℕ // IsAddComplSquares A}, normLimsup A.1

def AdditiveBasisCondition (A : Set ℕ) : Prop :=
  ∀ (k : ℕ), ∃ (n : ℕ) (a : ℕ), a ∈ A ∧ k = a + n ^ 2

/-! ## Glue lemmas -/

/-- Our `AdditiveBasisCondition` (k = a + n²) gives the blind `IsAddComplSquares` (m = n² + a). -/
lemma isAddCompl_of_ours {A : Set ℕ} (h : _root_.Erdos33.AdditiveBasisCondition A) :
    IsAddComplSquares A := by
  intro m
  obtain ⟨n, a, ha, hm⟩ := h m
  exact ⟨n, a, ha, by rw [hm, add_comm]⟩

/-- The blind real-then-coerce limsup equals the formal-conjectures-style `EReal` division. -/
lemma normLimsup_eq (A : Set ℕ) :
    normLimsup A = atTop.limsup (fun N : ℕ => ((A ∩ Icc 1 N).ncard : EReal) / (√N : EReal)) := by
  unfold normLimsup countUpTo
  refine congrArg (fun f => limsup f atTop) (funext fun N => ?_)
  simp only [EReal.coe_div, EReal.coe_natCast]

/-- The blind `normLimsup` of our witness `Aset` is at most `13√2/4`. -/
lemma normLimsup_Aset : normLimsup _root_.Erdos33.Aset ≤ ((13 * Real.sqrt 2 / 4 : ℝ) : EReal) := by
  rw [normLimsup_eq]
  exact _root_.Erdos33.Aset_limsup

/-! ## Bridged blind statements -/

theorem erdos33_exists_le :
    ∃ A : Set ℕ, IsAddComplSquares A ∧ normLimsup A ≤ ((13 * Real.sqrt 2 / 4 : ℝ) : EReal) :=
  ⟨_root_.Erdos33.Aset, isAddCompl_of_ours _root_.Erdos33.Aset_basis, normLimsup_Aset⟩

theorem erdos33_exists_le_eventually :
    ∃ A : Set ℕ, IsAddComplSquaresEventually A ∧
      normLimsup A ≤ ((13 * Real.sqrt 2 / 4 : ℝ) : EReal) := by
  obtain ⟨A, hA, hl⟩ := erdos33_exists_le
  exact ⟨A, Eventually.of_forall hA, hl⟩

theorem erdos33_exists_le_eps :
    ∃ A : Set ℕ, IsAddComplSquares A ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
        ((A ∩ Icc 1 N).ncard : ℝ) ≤ (13 * Real.sqrt 2 / 4 + ε) * Real.sqrt N := by
  obtain ⟨A, hA, hl⟩ := erdos33_exists_le
  refine ⟨A, hA, fun ε hε => ?_⟩
  have hlt : normLimsup A < ((13 * Real.sqrt 2 / 4 + ε : ℝ) : EReal) :=
    lt_of_le_of_lt hl (EReal.coe_lt_coe_iff.2 (by linarith))
  unfold normLimsup at hlt
  have hev := Filter.eventually_lt_of_limsup_lt hlt (by isBoundedDefault)
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  rw [EReal.coe_lt_coe_iff] at hN
  have hpos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN1)
  rw [div_lt_iff₀ hpos] at hN
  exact hN.le

theorem erdos33_L_le : L ≤ ((13 * Real.sqrt 2 / 4 : ℝ) : EReal) :=
  iInf_le_of_le ⟨_root_.Erdos33.Aset, isAddCompl_of_ours _root_.Erdos33.Aset_basis⟩ normLimsup_Aset

theorem erdos33_new_bound_fc_shape :
    ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
      ((A.1 ∩ Icc 1 N).ncard : EReal) / (Real.sqrt N : EReal)) ≤
        ((13 * Real.sqrt 2 / 4 : ℝ) : EReal) :=
  iInf_le_of_le ⟨_root_.Erdos33.Aset, _root_.Erdos33.Aset_basis⟩ _root_.Erdos33.Aset_limsup

/-- Also directly by defeq from our `erdos_33_le_13_sqrt2_div_4` (the two
`AdditiveBasisCondition`s have identical bodies). -/
theorem erdos33_new_bound_fc_shape' :
    ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
      ((A.1 ∩ Icc 1 N).ncard : EReal) / (Real.sqrt N : EReal)) ≤
        ((13 * Real.sqrt 2 / 4 : ℝ) : EReal) :=
  _root_.Erdos33.erdos_33_le_13_sqrt2_div_4

theorem erdos33_vanDoorn :
    ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
      ((A.1 ∩ Icc 1 N).ncard : EReal) / (Real.sqrt N : EReal)) ≤
        ((2 * (Real.goldenRatio ^ ((5 : ℝ) / 2)) : ℝ) : EReal) :=
  _root_.Erdos33.erdos_33.variants.vanDoorn

theorem new_const_lt_vanDoorn :
    13 * Real.sqrt 2 / 4 < 2 * (Real.goldenRatio ^ ((5 : ℝ) / 2)) := by
  have hφ1 : (1 : ℝ) ≤ Real.goldenRatio := Real.one_lt_goldenRatio.le
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hφ : (3 : ℝ) / 2 < Real.goldenRatio := by
    rw [Real.goldenRatio]; linarith
  have hsq : Real.goldenRatio ^ (2 : ℝ) ≤ Real.goldenRatio ^ ((5 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hφ1 (by norm_num)
  have hsq' : Real.goldenRatio ^ (2 : ℝ) = Real.goldenRatio + 1 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.goldenRatio_sq]
  have h2 : Real.sqrt 2 < 3 / 2 := by
    rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith

/-- `erdos33_vanDoorn` also re-derived from the new bound + the strict comparison above. -/
theorem erdos33_vanDoorn' :
    ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
      ((A.1 ∩ Icc 1 N).ncard : EReal) / (Real.sqrt N : EReal)) ≤
        ((2 * (Real.goldenRatio ^ ((5 : ℝ) / 2)) : ℝ) : EReal) :=
  erdos33_new_bound_fc_shape.trans (EReal.coe_le_coe_iff.2 new_const_lt_vanDoorn.le)

/-- Sanity: the blind `normLimsup` is always `≥ 0` (so the `EReal` bound is not trivialised
by a `⊥`/junk value). -/
lemma normLimsup_nonneg (A : Set ℕ) : 0 ≤ normLimsup A := by
  unfold normLimsup
  exact Filter.le_limsup_of_frequently_le (Frequently.of_forall fun N =>
    EReal.coe_nonneg.2 (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))) (by isBoundedDefault)

end FidelityBridge.Erdos33Blind

#print axioms FidelityBridge.Erdos33Blind.erdos33_exists_le
#print axioms FidelityBridge.Erdos33Blind.erdos33_exists_le_eventually
#print axioms FidelityBridge.Erdos33Blind.erdos33_exists_le_eps
#print axioms FidelityBridge.Erdos33Blind.erdos33_L_le
#print axioms FidelityBridge.Erdos33Blind.erdos33_new_bound_fc_shape
#print axioms FidelityBridge.Erdos33Blind.erdos33_new_bound_fc_shape'
#print axioms FidelityBridge.Erdos33Blind.erdos33_vanDoorn
#print axioms FidelityBridge.Erdos33Blind.erdos33_vanDoorn'
#print axioms FidelityBridge.Erdos33Blind.new_const_lt_vanDoorn
