import Mathlib

/-!
# Erdős Problem #33: an additive complement of the squares with `limsup ≤ 13√2/4`

Erdős Problem #33 (https://www.erdosproblems.com/33) asks for the smallest possible value of
`limsup_{N→∞} |A ∩ {1, …, N}| / √N` over the sets `A ⊆ ℕ` such that every large integer can be
written as `n² + a` with `n ≥ 0` and `a ∈ A`. That optimal value is still open: this file proves
an upper bound only, for one explicit construction.

* Construction: forum post #8879 by donteatllamas (erdosproblems.com, 2026-09-07), made
  "with the help of GPT"; write-up in GitHub LeanMeanBean/erdos-33 (`erdos33_limsup_4_596.pdf`
  and its TeX source). The displays (1)–(7) cited below are those of that write-up. The
  problem page erdosproblems.com/33 (last edited 2025-12-27) does not record this bound.
* Previous record: `2φ^{5/2} ≈ 6.66`, W. van Doorn (forum post #77, 2025-08-12; a version
  valid for every `N` in post #866, 2025-10-03), as recorded on erdosproblems.com/33.

Main results:
* `Aset_basis`: the explicit set `Aset` covers every natural number `m`, including `0`
  (formal-conjectures' `AdditiveBasisCondition`). The write-up covers every sufficiently large
  `m`, after adding finitely many unspecified small integers to `A`. Here the bands are used
  from scale `0` on, and the only element outside them is `0` (not counted in
  `|A ∩ [1, N]|`), so the Lean statement is slightly stronger.
* `Aset_limsup`: `limsup_{N→∞} |Aset ∩ [1, N]| / √N ≤ 13√2/4 ≈ 4.596`.
* `erdos_33_le_13_sqrt2_div_4`: hence the infimum in formal-conjectures' `erdos_33` is at most
  `13√2/4`.
* `erdos_33.variants.vanDoorn`: formal-conjectures' statement of van Doorn's bound, obtained here
  as a corollary of the new bound (via `13√2/4 ≤ 2φ^{5/2}`). Van Doorn's own construction is not
  formalized.

Lean proof AI-produced (Claude); checked with Lean 4 v4.36.0-rc1 / Mathlib v4.36.0-rc1.
-/

open Set Filter
open scoped goldenRatio

namespace Erdos33

/-- Verbatim from formal-conjectures `FormalConjectures/ErdosProblems/33.lean` (commit 2a315101):
every natural number `k` is `a + n²` with `a ∈ A`. -/
def AdditiveBasisCondition (A : Set ℕ) : Prop :=
  ∀ (k : ℕ), ∃ (n : ℕ) (a : ℕ), a ∈ A ∧ k = a + n^2

/-! ## The construction of forum post #8879 (donteatllamas, 2026-09-07) -/

/-- `L k = ⌈9^k / 4⌉ = (9^k + 3) / 4`. -/
def L (k : ℕ) : ℕ := (9 ^ k + 3) / 4

/-- The three bands of scale `k` (`q = 3^k`), exactly as in display (1) of the write-up. -/
def band (k a : ℕ) : Prop :=
  (a < 9 ^ k ∧ a % 3 ^ k ∈ ({0, 1, 2} : Finset ℕ)) ∨
  (9 ^ k ≤ a ∧ a < 2 * 9 ^ k ∧
      a % (3 * 3 ^ k) ∈ ({0, 1, 2, 3 ^ k, 3 ^ k + 1, 3 ^ k + 2} : Finset ℕ)) ∨
  (2 * 9 ^ k ≤ a ∧ a % (3 * 3 ^ k) ∈ ({0, 1, 2} : Finset ℕ))

/-- The set `A`: `0`, plus every `a ≥ 1` satisfying the band condition of its scale
`L k ≤ a < L (k+1)` (scale `0` included, so the write-up's "finitely many small integers" are
not needed). -/
def Aset : Set ℕ := {a | a = 0 ∨ ∃ k, L k ≤ a ∧ a < L (k + 1) ∧ band k a}

lemma four_mul_L (k : ℕ) : 4 * L k = 9 ^ k + 3 := by
  have h : 9 ^ k % 4 = 1 := by
    rw [Nat.pow_mod]; norm_num
  unfold L; omega

lemma L_lt_succ (k : ℕ) : L k < L (k + 1) := by
  have h1 := four_mul_L k
  have h2 := four_mul_L (k + 1)
  have : 9 ^ k < 9 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

lemma L_strictMono : StrictMono L := strictMono_nat_of_lt_succ L_lt_succ

lemma L_zero : L 0 = 1 := rfl

lemma exists_scale (N : ℕ) (hN : 1 ≤ N) : ∃ k, L k ≤ N ∧ N < L (k + 1) := by
  classical
  have hex : ∃ k, N < L (k + 1) := ⟨N, by
    have : N + 1 ≤ L (N + 1) := L_strictMono.id_le (N + 1)
    omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h, L_zero]; exact hN
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
    omega

lemma thirteen_le (k : ℕ) : 13 * k + 14 ≤ 14 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]; omega

/-- Hensel lifting for `X² - u` at `p = 3`, in `ℤ`. -/
lemma exists_sqrt_int (k : ℕ) (hk : 1 ≤ k) (u : ℤ) (hu : u % 3 = 1) :
    ∃ r : ℤ, (3 : ℤ) ^ k ∣ r ^ 2 - u := by
  induction k, hk using Nat.le_induction with
  | base => exact ⟨1, by omega⟩
  | succ k hk ih =>
    obtain ⟨r, w, hw⟩ := ih
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h3 : (3 : ℤ) ∣ r ^ 2 - u :=
      (dvd_pow_self 3 (by omega : j + 1 ≠ 0)).trans ⟨w, hw⟩
    have h4 : (3 : ℤ) ∣ 1 - 4 * r ^ 2 := by omega
    obtain ⟨t, ht⟩ := h4
    refine ⟨r - 2 * w * r * 3 ^ (j + 1), w * t + 4 * w ^ 2 * r ^ 2 * 3 ^ j, ?_⟩
    linear_combination hw + 3 ^ (j + 1) * w * ht

/-- (2): every `u ≡ 1 (mod 3)` has a square root `r` mod `3^k` with `1 ≤ r ≤ (3^k-1)/2`. -/
lemma exists_sqrt_mod_three_pow (k : ℕ) (hk : 1 ≤ k) (u : ℕ) (hu : u % 3 = 1) :
    ∃ r : ℕ, 1 ≤ r ∧ 2 * r + 1 ≤ 3 ^ k ∧ r ^ 2 % 3 ^ k = u % 3 ^ k := by
  obtain ⟨r, hr⟩ := exists_sqrt_int k hk u (by omega)
  set q : ℕ := 3 ^ k with hq
  have hq3 : 3 ∣ q := dvd_pow_self 3 (by omega)
  have hqpos : 0 < q := by positivity
  have hr3 : ¬ (3 : ℤ) ∣ r := by
    intro h
    have h1 : (3 : ℤ) ∣ r ^ 2 - u := (Int.natCast_dvd_natCast.2 hq3).trans (by exact_mod_cast hr)
    have h2 : (3 : ℤ) ∣ r ^ 2 := dvd_pow h (by norm_num)
    omega
  set r0 : ℕ := (r % (q : ℤ)).toNat with hr0
  have hr0' : (r0 : ℤ) = r % q := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hr0lt : r0 < q := by
    have := Int.emod_lt_of_pos r (show (0 : ℤ) < q by omega); omega
  have hr0ne : r0 ≠ 0 := by
    intro h0
    apply hr3
    have : (q : ℤ) ∣ r := Int.dvd_of_emod_eq_zero (by omega)
    exact (Int.natCast_dvd_natCast.2 hq3).trans this
  have hsq : (q : ℤ) ∣ (r0 : ℤ) ^ 2 - u := by
    have : (q : ℤ) ∣ (r0 : ℤ) - r := by
      exact ⟨-(r / q), by rw [hr0', Int.emod_def]; ring⟩
    have e : (r0 : ℤ) ^ 2 - u = ((r0 : ℤ) - r) * ((r0 : ℤ) + r) + (r ^ 2 - u) := by ring
    rw [e]; exact dvd_add (dvd_mul_of_dvd_left this _) (by exact_mod_cast hr)
  have hodd : q % 2 = 1 := by rw [hq, Nat.pow_mod]; norm_num
  have key : ∀ r1 : ℕ, (q : ℤ) ∣ (r1 : ℤ) ^ 2 - u → r1 ^ 2 % q = u % q := by
    intro r1 h
    exact Nat.modEq_iff_dvd.2 (by push_cast; exact dvd_sub_comm.1 h)
  by_cases hle : 2 * r0 + 1 ≤ q
  · exact ⟨r0, by omega, hle, key r0 hsq⟩
  · refine ⟨q - r0, by omega, by omega, key _ ?_⟩
    have e : ((q - r0 : ℕ) : ℤ) ^ 2 - u = ((r0 : ℤ) ^ 2 - u) + q * (q - 2 * r0) := by
      push_cast [hr0lt.le]; ring
    rw [e]; exact dvd_add hsq (dvd_mul_right _ _)

/-- (3): `0 < a < 9^k` and `a ≡ d (mod 3^k)` with `d ∈ {0,1,2}` imply `a ∈ A`. -/
lemma mem_Aset_of_lt (k a : ℕ) (ha0 : 0 < a) (ha : a < 9 ^ k) (had : a % 3 ^ k < 3) :
    a ∈ Aset := by
  obtain ⟨j, hj1, hj2⟩ := exists_scale a ha0
  have hjk : j ≤ k := by
    by_contra h
    push Not at h
    have h1 := L_strictMono.monotone (show k + 1 ≤ j by omega)
    have h2 := four_mul_L (k + 1)
    have h3 : 9 ^ (k + 1) = 9 * 9 ^ k := by ring
    omega
  right
  refine ⟨j, hj1, hj2, ?_⟩
  have mem3 : ∀ x : ℕ, x < 3 → x ∈ ({0, 1, 2} : Finset ℕ) := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have mem6 : ∀ x y : ℕ, x < 3 → x ∈ ({0, 1, 2, y, y + 1, y + 2} : Finset ℕ) := by
    intro x y hx; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  rcases hjk.lt_or_eq with hlt | rfl
  · have hdvd : 3 * 3 ^ j ∣ 3 ^ k := by
      rw [← pow_succ']; exact pow_dvd_pow 3 hlt
    have hdvd' : 3 ^ j ∣ 3 ^ k := pow_dvd_pow 3 hlt.le
    have e1 : a % (3 * 3 ^ j) = a % 3 ^ k := by
      rw [← Nat.mod_mod_of_dvd a hdvd]
      apply Nat.mod_eq_of_lt
      have : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
      omega
    have e2 : a % 3 ^ j < 3 := by
      rw [← Nat.mod_mod_of_dvd a hdvd']
      exact lt_of_le_of_lt (Nat.mod_le _ _) had
    by_cases h1 : a < 9 ^ j
    · exact Or.inl ⟨h1, mem3 _ e2⟩
    by_cases h2 : a < 2 * 9 ^ j
    · exact Or.inr (Or.inl ⟨by omega, h2, by rw [e1]; exact mem6 _ _ had⟩)
    · exact Or.inr (Or.inr ⟨by omega, by rw [e1]; exact mem3 _ had⟩)
  · exact Or.inl ⟨ha, mem3 _ had⟩

/-- Membership criterion at scale `k ≥ 1` in terms of the lift index `ℓ = ⌊a/q⌋ mod 3`. -/
lemma mem_of_lift (k a : ℕ) (hk : 1 ≤ k) (ha0 : 0 < a) (haL : a < L (k + 1))
    (had : a % 3 ^ k < 3)
    (h : a < 9 ^ k ∨ (a < 2 * 9 ^ k ∧ a / 3 ^ k % 3 ≠ 2) ∨ a / 3 ^ k % 3 = 0) : a ∈ Aset := by
  by_cases hsmall : a < 9 ^ k
  · exact mem_Aset_of_lt k a ha0 hsmall had
  have hLk : L k ≤ a := by
    have := four_mul_L k
    have : 1 ≤ 9 ^ k := Nat.one_le_pow _ _ (by norm_num)
    omega
  right
  refine ⟨k, hLk, haL, ?_⟩
  have hmod : a % (3 * 3 ^ k) = a % 3 ^ k + 3 ^ k * (a / 3 ^ k % 3) := by
    rw [mul_comm]; exact Nat.mod_mul
  have hq : 3 ≤ 3 ^ k := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hl3 : a / 3 ^ k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  right
  by_cases h2 : a < 2 * 9 ^ k
  · left
    refine ⟨by omega, h2, ?_⟩
    have hl : a / 3 ^ k % 3 = 0 ∨ a / 3 ^ k % 3 = 1 := by omega
    rw [hmod]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hl with hl | hl <;> rw [hl] <;> omega
  · right
    refine ⟨by omega, ?_⟩
    have hl : a / 3 ^ k % 3 = 0 := by omega
    rw [hmod, hl]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

/-- Coverage: `A` is an additive complement of the squares (every `m`, including `0`). -/
theorem Aset_basis : AdditiveBasisCondition Aset := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨0, 0, Or.inl rfl, rfl⟩
  obtain ⟨k, hk1, hk2⟩ := exists_scale m hm
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨0, m, mem_Aset_of_lt 1 m hm ?_ (Nat.mod_lt _ (by norm_num)), by ring⟩
    have : L (0 + 1) = 3 := rfl
    omega
  have hk' : 1 ≤ k := hk
  have hL1 := four_mul_L k
  have hL2 := four_mul_L (k + 1)
  have hq9 : 9 ^ k = 3 ^ k * 3 ^ k := by rw [← mul_pow]; norm_num
  have h9 : 9 ^ (k + 1) = 9 * (3 ^ k * 3 ^ k) := by rw [pow_succ, hq9]; ring
  have mem0 := fun a => mem_of_lift k a hk'
  set q := 3 ^ k with hq
  have hq3 : 3 ∣ q := dvd_pow_self 3 (by omega)
  have hqge : 3 ≤ q := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk'
  rw [hq9] at hL1 mem0
  rw [h9] at hL2
  have mem : ∀ a d' : ℕ, 0 < a → a ≤ m → a % q = d' → d' < 3 →
      (a < q * q ∨ (a < 2 * (q * q) ∧ a / q % 3 ≠ 2) ∨ a / q % 3 = 0) → a ∈ Aset := by
    intro a d' ha0 ham had hd' h
    exact mem0 a ha0 (by omega) (by omega) h
  set d := (m + 2) % 3 with hd
  have hdlt : d < 3 := Nat.mod_lt _ (by norm_num)
  have hm3 : 3 ≤ m := by nlinarith
  have hdm : d ≤ m := by omega
  have hu : (m - d) % 3 = 1 := by omega
  obtain ⟨r, hr1, hr2, hr⟩ := exists_sqrt_mod_three_pow k hk' (m - d) hu
  rw [← hq] at hr2 hr
  have hr3 : r % 3 = 1 ∨ r % 3 = 2 := by
    have h1 : r ^ 2 % 3 = 1 := by
      rw [← Nat.mod_mod_of_dvd (r ^ 2) hq3, hr, Nat.mod_mod_of_dvd _ hq3, hu]
    rw [Nat.pow_mod] at h1
    rcases (show r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 by omega) with h | h | h
    · rw [h] at h1; norm_num at h1
    · exact Or.inl h
    · exact Or.inr h
  -- `m - n²` is `≡ d (mod q)` whenever `n ≡ ±r (mod q)`
  have h2 : (q : ℤ) ∣ ((m : ℤ) - d) - (r : ℤ) ^ 2 := by
    have := Nat.modEq_iff_dvd.1 hr
    push_cast [hdm] at this
    exact this
  have hmodq : ∀ n : ℕ, n ^ 2 ≤ m → (q : ℤ) ∣ (n : ℤ) ^ 2 - (r : ℤ) ^ 2 →
      (m - n ^ 2) % q = d := by
    intro n hn hdiv
    have h1 : d ≡ m - n ^ 2 [MOD q] := by
      rw [Nat.modEq_iff_dvd]
      push_cast [hn]
      have e : (m : ℤ) - n ^ 2 - d = ((m : ℤ) - d - r ^ 2) - (n ^ 2 - r ^ 2) := by ring
      rw [e]; exact dvd_sub h2 hdiv
    rw [← h1]; exact Nat.mod_eq_of_lt (by omega)
  have hsplit : ∀ n : ℕ, n ^ 2 ≤ m → (q : ℤ) ∣ (n : ℤ) ^ 2 - (r : ℤ) ^ 2 →
      (q : ℤ) * (((m - n ^ 2) / q : ℕ) : ℤ) + d = m - n ^ 2 := by
    intro n hn hdiv
    have h := Nat.div_add_mod (m - n ^ 2) q
    rw [hmodq n hn hdiv] at h
    have h' : ((q * ((m - n ^ 2) / q) + d : ℕ) : ℤ) = ((m - n ^ 2 : ℕ) : ℤ) := by rw [h]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hn, Nat.cast_pow] at h'
    exact h'
  have hrq : r ≤ q := by omega
  have hrm : r ^ 2 < m := by nlinarith
  have hdiv1 : (q : ℤ) ∣ (r : ℤ) ^ 2 - (r : ℤ) ^ 2 := by simp
  have hdiv2 : (q : ℤ) ∣ ((q - r : ℕ) : ℤ) ^ 2 - (r : ℤ) ^ 2 :=
    ⟨q - 2 * r, by push_cast [hrq]; ring⟩
  have hdiv3 : (q : ℤ) ∣ ((q + r : ℕ) : ℤ) ^ 2 - (r : ℤ) ^ 2 := ⟨q + 2 * r, by push_cast; ring⟩
  have e1 := hsplit r hrm.le hdiv1
  have hm1 : m = (m - r ^ 2) + r ^ 2 := (Nat.sub_add_cancel hrm.le).symm
  have ha1 : 0 < m - r ^ 2 := Nat.sub_pos_of_lt hrm
  -- Case 1: `m < q²`
  by_cases hA : m < q * q
  · exact ⟨r, m - r ^ 2, mem _ _ ha1 (Nat.sub_le _ _) (hmodq r hrm.le hdiv1) hdlt
      (Or.inl (by omega)), hm1⟩
  push Not at hA
  set p := q - r with hp
  have hpq : p + r = q := by omega
  have hpm : p ^ 2 < m := by
    have : p < q := by omega
    nlinarith [Nat.mul_self_lt_mul_self this]
  have e2 := hsplit p hpm.le hdiv2
  have hm2 : m = (m - p ^ 2) + p ^ 2 := (Nat.sub_add_cancel hpm.le).symm
  have ha2 : 0 < m - p ^ 2 := Nat.sub_pos_of_lt hpm
  set s1 := (m - r ^ 2) / q with hs1
  set s2 := (m - p ^ 2) / q with hs2
  have hs12 : (s1 : ℤ) - s2 = q - 2 * r := by
    have : (q : ℤ) * ((s1 : ℤ) - s2) = q * (q - 2 * r) := by
      have hp' : (p : ℤ) = q - r := by rw [hp]; push_cast [hrq]; ring
      rw [hp'] at e2
      linear_combination e1 - e2
    exact mul_left_cancel₀ (by positivity) this
  have hq3' : q % 3 = 0 := Nat.mod_eq_zero_of_dvd hq3
  -- Case 2: `q² ≤ m < 2q²`
  by_cases hB : m < 2 * (q * q)
  · by_cases hl1 : s1 % 3 = 2
    · exact ⟨p, m - p ^ 2, mem _ _ ha2 (Nat.sub_le _ _) (hmodq p hpm.le hdiv2) hdlt
        (Or.inr (Or.inl ⟨by omega, by omega⟩)), hm2⟩
    · exact ⟨r, m - r ^ 2, mem _ _ ha1 (Nat.sub_le _ _) (hmodq r hrm.le hdiv1) hdlt
        (Or.inr (Or.inl ⟨by omega, hl1⟩)), hm1⟩
  push Not at hB
  -- Case 3: `2q² ≤ m < L (k+1)`
  by_cases hC : (q + r) ^ 2 < m
  · have e3 := hsplit (q + r) hC.le hdiv3
    have hm3' : m = (m - (q + r) ^ 2) + (q + r) ^ 2 := (Nat.sub_add_cancel hC.le).symm
    have ha3 : 0 < m - (q + r) ^ 2 := Nat.sub_pos_of_lt hC
    set s3 := (m - (q + r) ^ 2) / q with hs3
    have hs13 : (s1 : ℤ) - s3 = q + 2 * r := by
      have : (q : ℤ) * ((s1 : ℤ) - s3) = q * (q + 2 * r) := by
        push_cast at e3
        linear_combination e1 - e3
      exact mul_left_cancel₀ (by positivity) this
    have : s1 % 3 = 0 ∨ s2 % 3 = 0 ∨ s3 % 3 = 0 := by omega
    rcases this with h | h | h
    · exact ⟨r, m - r ^ 2, mem _ _ ha1 (Nat.sub_le _ _) (hmodq r hrm.le hdiv1) hdlt
        (Or.inr (Or.inr h)), hm1⟩
    · exact ⟨p, m - p ^ 2, mem _ _ ha2 (Nat.sub_le _ _) (hmodq p hpm.le hdiv2) hdlt
        (Or.inr (Or.inr h)), hm2⟩
    · exact ⟨q + r, m - (q + r) ^ 2, mem _ _ ha3 (Nat.sub_le _ _) (hmodq _ hC.le hdiv3) hdlt
        (Or.inr (Or.inr h)), hm3'⟩
  push Not at hC
  have : s1 % 3 = 0 ∨ s2 % 3 = 0 ∨ (r % 3 = 1 ∧ s2 % 3 = 1) ∨ (r % 3 = 2 ∧ s1 % 3 = 1) := by
    omega
  rcases this with h | h | ⟨hr', h⟩ | ⟨hr', h⟩
  · exact ⟨r, m - r ^ 2, mem _ _ ha1 (Nat.sub_le _ _) (hmodq r hrm.le hdiv1) hdlt
      (Or.inr (Or.inr h)), hm1⟩
  · exact ⟨p, m - p ^ 2, mem _ _ ha2 (Nat.sub_le _ _) (hmodq p hpm.le hdiv2) hdlt
      (Or.inr (Or.inr h)), hm2⟩
  · -- lift-1 remainder is `m - (q-r)²`, and it is `< 2q²`
    have hlt : m - p ^ 2 < 2 * (q * q) := by
      rw [Nat.sub_lt_iff_lt_add hpm.le]
      have h2p : q + 1 ≤ 2 * p := by omega
      have h3 := Nat.mul_le_mul h2p h2p
      have e4 : (2 * p) * (2 * p) = 4 * p ^ 2 := by ring
      have e5 : (q + 1) * (q + 1) = q * q + 2 * q + 1 := by ring
      rw [e4, e5] at h3
      omega
    exact ⟨p, m - p ^ 2, mem _ _ ha2 (Nat.sub_le _ _) (hmodq p hpm.le hdiv2) hdlt
      (Or.inr (Or.inl ⟨hlt, by omega⟩)), hm2⟩
  · -- lift-1 remainder is `m - r²`, and it is `< 2q²` by `(q+r)² ≥ m`
    have hlt : m - r ^ 2 < 2 * (q * q) := by
      rw [Nat.sub_lt_iff_lt_add hrm.le]
      have e6 : (q + r) ^ 2 = q * q + 2 * (q * r) + r ^ 2 := by ring
      have h3 : q * (2 * r + 1) ≤ q * q := Nat.mul_le_mul_left q hr2
      have e7 : q * (2 * r + 1) = 2 * (q * r) + q := by ring
      rw [e7] at h3
      rw [e6] at hC
      omega
    exact ⟨r, m - r ^ 2, mem _ _ ha1 (Nat.sub_le _ _) (hmodq r hrm.le hdiv1) hdlt
      (Or.inr (Or.inl ⟨hlt, by omega⟩)), hm1⟩

/-! ### Counting -/

lemma count_residue (lo hi m v : ℕ) (hm : 0 < m) (hlh : lo ≤ hi) :
    (((Finset.Ico lo hi).filter (fun x => x ≡ v [MOD m])).card : ℝ) ≤ ((hi : ℝ) - lo) / m + 1 := by
  have h := Nat.Ico_filter_modEq_card lo hi hm v
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  have hlhq : (lo : ℚ) ≤ hi := by exact_mod_cast hlh
  have key : ((((Finset.Ico lo hi).filter (fun x => x ≡ v [MOD m])).card : ℤ) : ℚ)
      ≤ ((hi : ℚ) - lo) / m + 1 := by
    rw [h]
    push_cast
    apply max_le
    · have h1 := Int.ceil_lt_add_one (((hi : ℚ) - v) / m)
      have h2 := Int.le_ceil (((lo : ℚ) - v) / m)
      have : ((hi : ℚ) - v) / m - ((lo : ℚ) - v) / m = ((hi : ℚ) - lo) / m := by ring
      linarith
    · have : (0 : ℚ) ≤ ((hi : ℚ) - lo) / m := div_nonneg (by linarith) hmq.le
      linarith
  have key' : ((((Finset.Ico lo hi).filter (fun x => x ≡ v [MOD m])).card : ℚ) : ℝ)
      ≤ ((((hi : ℚ) - lo) / m + 1 : ℚ) : ℝ) := by
    rw [Rat.cast_le]; exact_mod_cast key
  push_cast at key'
  exact key'

lemma count_mod (lo hi m : ℕ) (R : Finset ℕ) (hm : 0 < m) (hlh : lo ≤ hi) :
    (((Finset.Ico lo hi).filter (fun a => a % m ∈ R)).card : ℝ)
      ≤ R.card * (((hi : ℝ) - lo) / m + 1) := by
  classical
  have hsub : (Finset.Ico lo hi).filter (fun a => a % m ∈ R) ⊆
      R.biUnion (fun v => (Finset.Ico lo hi).filter (fun x => x ≡ v [MOD m])) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_biUnion]
    exact ⟨a % m, ha.2, Finset.mem_filter.2 ⟨ha.1, (Nat.mod_modEq a m).symm⟩⟩
  calc (((Finset.Ico lo hi).filter (fun a => a % m ∈ R)).card : ℝ)
      ≤ ((R.biUnion (fun v => (Finset.Ico lo hi).filter (fun x => x ≡ v [MOD m]))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ v ∈ R, (((Finset.Ico lo hi).filter (fun x => x ≡ v [MOD m])).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ v ∈ R, (((hi : ℝ) - lo) / m + 1) :=
        Finset.sum_le_sum (fun v _ => count_residue lo hi m v hm hlh)
    _ = R.card * (((hi : ℝ) - lo) / m + 1) := by rw [Finset.sum_const, nsmul_eq_mul]

lemma scale_unique {j j' a : ℕ} (h1 : L j ≤ a) (h2 : a < L (j + 1)) (h1' : L j' ≤ a)
    (h2' : a < L (j' + 1)) : j = j' := by
  by_contra h
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have := L_strictMono.monotone (show j + 1 ≤ j' by omega); omega
  · have := L_strictMono.monotone (show j' + 1 ≤ j by omega); omega

lemma band_of_mem {j a : ℕ} (h1 : L j ≤ a) (h2 : a < L (j + 1)) (ha : a ∈ Aset) :
    band j a := by
  obtain h0 | ⟨j', h1', h2', hb⟩ := ha
  · have : L 0 ≤ L j := L_strictMono.monotone (Nat.zero_le j)
    rw [L_zero] at this; omega
  · rwa [scale_unique h1 h2 h1' h2']

lemma two_nine_le_L_succ (j : ℕ) : 2 * 9 ^ j ≤ L (j + 1) := by
  have h4 := four_mul_L (j + 1)
  have h5 : 9 ^ (j + 1) = 9 * 9 ^ j := by ring
  omega

lemma L_le_nine (j : ℕ) : L j ≤ 9 ^ j := by
  have h4 := four_mul_L j
  have : 1 ≤ 9 ^ j := Nat.one_le_pow _ _ (by norm_num)
  omega

open Classical in
lemma band1_count (j lo hi : ℕ) (h1 : L j ≤ lo) (h2 : lo ≤ hi) (h3 : hi ≤ 9 ^ j) :
    (((Finset.Ico lo hi).filter (· ∈ Aset)).card : ℝ) ≤ 3 * (((hi : ℝ) - lo) / 3 ^ j + 1) := by
  have hsub : (Finset.Ico lo hi).filter (· ∈ Aset) ⊆
      (Finset.Ico lo hi).filter (fun a => a % 3 ^ j ∈ ({0, 1, 2} : Finset ℕ)) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
    refine ⟨ha.1, ?_⟩
    have hL : a < L (j + 1) := by have := two_nine_le_L_succ j; omega
    rcases band_of_mem (by omega) hL ha.2 with hb | hb | hb
    · exact hb.2
    · exact absurd hb.1 (by omega)
    · exact absurd hb.1 (by omega)
  calc (((Finset.Ico lo hi).filter (· ∈ Aset)).card : ℝ)
      ≤ (((Finset.Ico lo hi).filter (fun a => a % 3 ^ j ∈ ({0, 1, 2} : Finset ℕ))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (({0, 1, 2} : Finset ℕ).card : ℝ) * (((hi : ℝ) - lo) / ((3 ^ j : ℕ) : ℝ) + 1) :=
        count_mod _ _ _ _ (by positivity) h2
    _ = 3 * (((hi : ℝ) - lo) / 3 ^ j + 1) := by
        rw [show ({0, 1, 2} : Finset ℕ).card = 3 by decide]; push_cast; ring

open Classical in
lemma band2_count (j lo hi : ℕ) (h1 : 9 ^ j ≤ lo) (h2 : lo ≤ hi) (h3 : hi ≤ 2 * 9 ^ j) :
    (((Finset.Ico lo hi).filter (· ∈ Aset)).card : ℝ)
      ≤ 6 * (((hi : ℝ) - lo) / (3 * 3 ^ j) + 1) := by
  have hsub : (Finset.Ico lo hi).filter (· ∈ Aset) ⊆ (Finset.Ico lo hi).filter
      (fun a => a % (3 * 3 ^ j) ∈ ({0, 1, 2, 3 ^ j, 3 ^ j + 1, 3 ^ j + 2} : Finset ℕ)) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
    refine ⟨ha.1, ?_⟩
    have hL : a < L (j + 1) := by have := two_nine_le_L_succ j; omega
    have hLj := L_le_nine j
    rcases band_of_mem (by omega) hL ha.2 with hb | hb | hb
    · exact absurd hb.1 (by omega)
    · exact hb.2.2
    · exact absurd hb.1 (by omega)
  have hR : ((({0, 1, 2, 3 ^ j, 3 ^ j + 1, 3 ^ j + 2} : Finset ℕ)).card : ℝ) ≤ 6 := by
    exact_mod_cast Finset.card_le_six
  have hnn : 0 ≤ ((hi : ℝ) - lo) / (3 * 3 ^ j) + 1 := by
    have : (lo : ℝ) ≤ hi := by exact_mod_cast h2
    have : 0 ≤ ((hi : ℝ) - lo) / (3 * 3 ^ j) := div_nonneg (by linarith) (by positivity)
    linarith
  calc (((Finset.Ico lo hi).filter (· ∈ Aset)).card : ℝ)
      ≤ (((Finset.Ico lo hi).filter (fun a => a % (3 * 3 ^ j) ∈
          ({0, 1, 2, 3 ^ j, 3 ^ j + 1, 3 ^ j + 2} : Finset ℕ))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((({0, 1, 2, 3 ^ j, 3 ^ j + 1, 3 ^ j + 2} : Finset ℕ)).card : ℝ) *
          (((hi : ℝ) - lo) / ((3 * 3 ^ j : ℕ) : ℝ) + 1) :=
        count_mod _ _ _ _ (by positivity) h2
    _ ≤ 6 * (((hi : ℝ) - lo) / (3 * 3 ^ j) + 1) := by
        push_cast; exact mul_le_mul_of_nonneg_right hR hnn

open Classical in
lemma band3_count (j lo hi : ℕ) (h1 : 2 * 9 ^ j ≤ lo) (h2 : lo ≤ hi) (h3 : hi ≤ L (j + 1)) :
    (((Finset.Ico lo hi).filter (· ∈ Aset)).card : ℝ)
      ≤ 3 * (((hi : ℝ) - lo) / (3 * 3 ^ j) + 1) := by
  have hsub : (Finset.Ico lo hi).filter (· ∈ Aset) ⊆
      (Finset.Ico lo hi).filter (fun a => a % (3 * 3 ^ j) ∈ ({0, 1, 2} : Finset ℕ)) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
    refine ⟨ha.1, ?_⟩
    have hLj := L_le_nine j
    rcases band_of_mem (j := j) (by omega) (by omega) ha.2 with hb | hb | hb
    · exact absurd hb.1 (by omega)
    · exact absurd hb.2.1 (by omega)
    · exact hb.2
  calc (((Finset.Ico lo hi).filter (· ∈ Aset)).card : ℝ)
      ≤ (((Finset.Ico lo hi).filter
          (fun a => a % (3 * 3 ^ j) ∈ ({0, 1, 2} : Finset ℕ))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (({0, 1, 2} : Finset ℕ).card : ℝ) * (((hi : ℝ) - lo) / ((3 * 3 ^ j : ℕ) : ℝ) + 1) :=
        count_mod _ _ _ _ (by positivity) h2
    _ = 3 * (((hi : ℝ) - lo) / (3 * 3 ^ j) + 1) := by
        rw [show ({0, 1, 2} : Finset ℕ).card = 3 by decide]; push_cast; ring

lemma nine_pow_real (j : ℕ) : (9 : ℝ) ^ j = ((3 : ℝ) ^ j) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

lemma L_real (j : ℕ) : ((L j : ℕ) : ℝ) = (((3 : ℝ) ^ j) ^ 2 + 3) / 4 := by
  have e := four_mul_L j
  have e' : ((4 * L j : ℕ) : ℝ) = ((9 ^ j + 3 : ℕ) : ℝ) := by rw [e]
  push_cast at e'
  rw [nine_pow_real] at e'
  linarith

lemma L_succ_real (j : ℕ) : ((L (j + 1) : ℕ) : ℝ) = (9 * ((3 : ℝ) ^ j) ^ 2 + 3) / 4 := by
  rw [L_real, pow_succ]; ring

/-- Full band 1 of scale `j` contributes at most `(9/4)·3^j + 3`. -/
lemma band1_full (j : ℕ) :
    3 * ((((9 ^ j : ℕ) : ℝ) - ((L j : ℕ) : ℝ)) / 3 ^ j + 1) ≤ 9 / 4 * 3 ^ j + 3 := by
  have hQ : (1 : ℝ) ≤ 3 ^ j := one_le_pow₀ (by norm_num)
  rw [L_real]; push_cast; rw [nine_pow_real]
  have : (((3 : ℝ) ^ j) ^ 2 - (((3 : ℝ) ^ j) ^ 2 + 3) / 4) / 3 ^ j ≤ 3 / 4 * 3 ^ j := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- Full band 2 of scale `j` contributes at most `2·3^j + 6`. -/
lemma band2_full (j : ℕ) :
    6 * ((((2 * 9 ^ j : ℕ) : ℝ) - ((9 ^ j : ℕ) : ℝ)) / (3 * 3 ^ j) + 1) = 2 * 3 ^ j + 6 := by
  push_cast; rw [nine_pow_real]
  have hQ : (0 : ℝ) < 3 ^ j := by positivity
  field_simp; ring

/-- Full band 3 of scale `j` contributes at most `(1/4)·3^j + 4`. -/
lemma band3_full (j : ℕ) :
    3 * ((((L (j + 1) : ℕ) : ℝ) - ((2 * 9 ^ j : ℕ) : ℝ)) / (3 * 3 ^ j) + 1)
      ≤ 1 / 4 * 3 ^ j + 4 := by
  have hQ : (1 : ℝ) ≤ 3 ^ j := one_le_pow₀ (by norm_num)
  rw [L_succ_real]; push_cast; rw [nine_pow_real]
  have : ((9 * ((3 : ℝ) ^ j) ^ 2 + 3) / 4 - 2 * ((3 : ℝ) ^ j) ^ 2) / (3 * 3 ^ j)
      ≤ 3 ^ j / 12 + 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

lemma card_union3_le {s t u : Finset ℕ} :
    ((s ∪ (t ∪ u)).card : ℝ) ≤ (s.card : ℝ) + t.card + u.card := by
  have h1 := Finset.card_union_le s (t ∪ u)
  have h2 := Finset.card_union_le t u
  have : (s ∪ (t ∪ u)).card ≤ s.card + t.card + u.card := by omega
  exact_mod_cast this

lemma card_union2_le {s t : Finset ℕ} :
    ((s ∪ t).card : ℝ) ≤ (s.card : ℝ) + t.card := by
  exact_mod_cast Finset.card_union_le s t

open Classical in
/-- One complete scale contributes at most `(9/2)·3^j + 13`  (display (6)). -/
lemma scale_count (j : ℕ) :
    (((Finset.Ico (L j) (L (j + 1))).filter (· ∈ Aset)).card : ℝ) ≤ 9 / 2 * 3 ^ j + 13 := by
  have hA := L_le_nine j
  have hB : 9 ^ j ≤ 2 * 9 ^ j := by omega
  have hC := two_nine_le_L_succ j
  rw [← Finset.Ico_union_Ico_eq_Ico hA (hB.trans hC), ← Finset.Ico_union_Ico_eq_Ico hB hC,
    Finset.filter_union, Finset.filter_union]
  have c1 := band1_count j (L j) (9 ^ j) le_rfl hA le_rfl
  have c2 := band2_count j (9 ^ j) (2 * 9 ^ j) le_rfl hB le_rfl
  have c3 := band3_count j (2 * 9 ^ j) (L (j + 1)) le_rfl hC le_rfl
  have u := @card_union3_le ((Finset.Ico (L j) (9 ^ j)).filter (· ∈ Aset))
    ((Finset.Ico (9 ^ j) (2 * 9 ^ j)).filter (· ∈ Aset))
    ((Finset.Ico (2 * 9 ^ j) (L (j + 1))).filter (· ∈ Aset))
  have b1 := band1_full j
  have b2 := band2_full j
  have b3 := band3_full j
  linarith

open Classical in
/-- All scales below `k` together: `|A ∩ [1, L_k)| ≤ (9/4)·3^k + 13k`  (display (7)). -/
lemma cum_count (k : ℕ) :
    (((Finset.Ico 1 (L k)).filter (· ∈ Aset)).card : ℝ) ≤ 9 / 4 * 3 ^ k + 13 * k := by
  induction k with
  | zero => norm_num [L_zero]
  | succ k ih =>
    have h1 : 1 ≤ L k := by
      have := L_strictMono.monotone (Nat.zero_le k); rw [L_zero] at this; exact this
    rw [← Finset.Ico_union_Ico_eq_Ico h1 (L_lt_succ k).le, Finset.filter_union]
    have u := @card_union2_le ((Finset.Ico 1 (L k)).filter (· ∈ Aset))
      ((Finset.Ico (L k) (L (k + 1))).filter (· ∈ Aset))
    have hs := scale_count k
    push_cast
    rw [pow_succ]
    linarith

open Classical in
/-- Counting with explicit error: on scale `k`, `A(N) ≤ (13√2/4)·√N + 13k + 14`. -/
lemma card_le (k N : ℕ) (hN : L k ≤ N) (hN' : N < L (k + 1)) :
    (((Finset.Icc 1 N).filter (· ∈ Aset)).card : ℝ) ≤ 13 * √2 / 4 * √N + 13 * k + 14 := by
  have h1 : 1 ≤ L k := by
    have := L_strictMono.monotone (Nat.zero_le k); rw [L_zero] at this; exact this
  rw [← Finset.Ico_add_one_right_eq_Icc,
    ← Finset.Ico_union_Ico_eq_Ico h1 (show L k ≤ N + 1 by omega), Finset.filter_union]
  have u := @card_union2_le ((Finset.Ico 1 (L k)).filter (· ∈ Aset))
      ((Finset.Ico (L k) (N + 1)).filter (· ∈ Aset))
  have hcum := cum_count k
  -- real-variable facts: `Q = 3^k`, `t = √N`, `s = √2`
  have hQ1 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have ht0 : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
  have hNt : (N : ℝ) = √(N : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg N)).symm
  have hs0 : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg _
  have hs2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs14 : (1.4 : ℝ) ≤ √2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs16 : √(2 : ℝ) ≤ 1.6 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hQ0 : (0 : ℝ) ≤ 3 ^ k := by positivity
  have hLk := L_real k
  have hLk1 := L_succ_real k
  have hlo : (((3 : ℝ) ^ k) ^ 2 + 3) / 4 ≤ √(N : ℝ) ^ 2 := by
    rw [← hLk, ← hNt]; exact_mod_cast hN
  have hhi : √(N : ℝ) ^ 2 < (9 * ((3 : ℝ) ^ k) ^ 2 + 3) / 4 := by
    rw [← hLk1, ← hNt]; exact_mod_cast hN'
  have hN9 : ((9 ^ k : ℕ) : ℝ) = ((3 : ℝ) ^ k) ^ 2 := by push_cast; exact nine_pow_real k
  by_cases hb1 : N + 1 ≤ 9 ^ k
  · -- `N` in band 1
    have c := band1_count k (L k) (N + 1) le_rfl (by omega) hb1
    have hNq : √(N : ℝ) ^ 2 < ((3 : ℝ) ^ k) ^ 2 := by
      rw [← hN9, ← hNt]; exact_mod_cast (show N < 9 ^ k by omega)
    have htq : √(N : ℝ) ≤ 3 ^ k :=
      ((pow_lt_pow_iff_left₀ ht0 hQ0 two_ne_zero).1 hNq).le
    have htq2 : 3 ^ k / 2 ≤ √(N : ℝ) := by
      refine (pow_le_pow_iff_left₀ (by positivity) ht0 two_ne_zero).1 ?_
      rw [div_pow]; linarith
    have key : (((N + 1 : ℕ) : ℝ) - ((L k : ℕ) : ℝ)) / 3 ^ k
        ≤ 3 / 2 * √(N : ℝ) - 3 / 4 * 3 ^ k + 1 / 3 := by
      rw [hLk, div_le_iff₀ (by positivity)]
      push_cast
      linarith [mul_nonneg (sub_nonneg.2 htq) (sub_nonneg.2 htq2)]
    linarith [mul_nonneg (sub_nonneg.2 hs14) ht0]
  by_cases hb2 : N + 1 ≤ 2 * 9 ^ k
  · -- `N` in band 2
    have hA := L_le_nine k
    rw [← Finset.Ico_union_Ico_eq_Ico hA (show 9 ^ k ≤ N + 1 by omega), Finset.filter_union] at u ⊢
    have u2 := @card_union2_le ((Finset.Ico (L k) (9 ^ k)).filter (· ∈ Aset))
      ((Finset.Ico (9 ^ k) (N + 1)).filter (· ∈ Aset))
    have c1 := band1_count k (L k) (9 ^ k) le_rfl hA le_rfl
    have b1 := band1_full k
    have c2 := band2_count k (9 ^ k) (N + 1) le_rfl (by omega) hb2
    have hNq : ((3 : ℝ) ^ k) ^ 2 ≤ √(N : ℝ) ^ 2 := by
      rw [← hN9, ← hNt]; exact_mod_cast (show 9 ^ k ≤ N by omega)
    have hNq2 : √(N : ℝ) ^ 2 < 2 * ((3 : ℝ) ^ k) ^ 2 := by
      rw [← hN9, ← hNt]; exact_mod_cast (show N < 2 * 9 ^ k by omega)
    have htq : 3 ^ k ≤ √(N : ℝ) := (pow_le_pow_iff_left₀ hQ0 ht0 two_ne_zero).1 hNq
    have htq2 : √(N : ℝ) ≤ √2 * 3 ^ k := by
      have : √(N : ℝ) ^ 2 < (√2 * 3 ^ k) ^ 2 := by rw [mul_pow, hs2]; exact hNq2
      exact ((pow_lt_pow_iff_left₀ ht0 (by positivity) two_ne_zero).1 this).le
    have htq3 : 5 * √2 / 8 * 3 ^ k ≤ √(N : ℝ) := by
      have h58 : 5 * √2 / 8 ≤ 1 := by linarith
      linarith [mul_le_mul_of_nonneg_right h58 hQ0]
    have key : (((N + 1 : ℕ) : ℝ) - ((9 ^ k : ℕ) : ℝ)) / (3 * 3 ^ k)
        ≤ (13 * √2 / 4 * √(N : ℝ) - 9 / 2 * 3 ^ k + 5) / 6 := by
      rw [hN9, div_le_iff₀ (by positivity)]
      push_cast
      have hsQ : √(2 : ℝ) ^ 2 * ((3 : ℝ) ^ k) ^ 2 = 2 * ((3 : ℝ) ^ k) ^ 2 := by rw [hs2]
      linarith [mul_nonneg (sub_nonneg.2 htq2) (sub_nonneg.2 htq3)]
    linarith
  · -- `N` in band 3
    have hA := L_le_nine k
    have hB : 9 ^ k ≤ 2 * 9 ^ k := by omega
    rw [← Finset.Ico_union_Ico_eq_Ico hA (show 9 ^ k ≤ N + 1 by omega),
      ← Finset.Ico_union_Ico_eq_Ico hB (show 2 * 9 ^ k ≤ N + 1 by omega),
      Finset.filter_union, Finset.filter_union] at u ⊢
    have u3 := @card_union3_le ((Finset.Ico (L k) (9 ^ k)).filter (· ∈ Aset))
      ((Finset.Ico (9 ^ k) (2 * 9 ^ k)).filter (· ∈ Aset))
      ((Finset.Ico (2 * 9 ^ k) (N + 1)).filter (· ∈ Aset))
    have c1 := band1_count k (L k) (9 ^ k) le_rfl hA le_rfl
    have b1 := band1_full k
    have c2 := band2_count k (9 ^ k) (2 * 9 ^ k) le_rfl hB le_rfl
    have b2 := band2_full k
    have c3 := band3_count k (2 * 9 ^ k) (N + 1) le_rfl (by omega) (by omega)
    have hNq : 2 * ((3 : ℝ) ^ k) ^ 2 ≤ √(N : ℝ) ^ 2 := by
      rw [← hN9, ← hNt]; exact_mod_cast (show 2 * 9 ^ k ≤ N by omega)
    have htq : √2 * 3 ^ k ≤ √(N : ℝ) := by
      have : (√2 * 3 ^ k) ^ 2 ≤ √(N : ℝ) ^ 2 := by rw [mul_pow, hs2]; exact hNq
      exact (pow_le_pow_iff_left₀ (by positivity) ht0 two_ne_zero).1 this
    have htq2 : √(N : ℝ) ≤ 9 * √2 / 4 * 3 ^ k := by
      have : √(N : ℝ) ^ 2 < (9 * √2 / 4 * 3 ^ k) ^ 2 := by
        have e : (9 * √2 / 4 * 3 ^ k) ^ 2 = 81 / 8 * ((3 : ℝ) ^ k) ^ 2 := by
          rw [mul_pow, div_pow, mul_pow, hs2]; ring
        rw [e]; nlinarith
      exact ((pow_lt_pow_iff_left₀ ht0 (by positivity) two_ne_zero).1 this).le
    have key : (((N + 1 : ℕ) : ℝ) - ((2 * 9 ^ k : ℕ) : ℝ)) / (3 * 3 ^ k)
        ≤ (13 * √2 / 4 * √(N : ℝ) - 13 / 2 * 3 ^ k + 2) / 3 := by
      rw [show ((2 * 9 ^ k : ℕ) : ℝ) = 2 * ((9 ^ k : ℕ) : ℝ) by push_cast; ring, hN9,
        div_le_iff₀ (by positivity)]
      push_cast
      have hsQ : √(2 : ℝ) ^ 2 * ((3 : ℝ) ^ k) ^ 2 = 2 * ((3 : ℝ) ^ k) ^ 2 := by rw [hs2]
      linarith [mul_nonneg (sub_nonneg.2 htq) (sub_nonneg.2 htq2)]
    linarith

/-- The limsup bound for the explicit witness `Aset`, in formal-conjectures' `EReal` form.
Together with `Aset_basis` this is the plain existential claim "there is an additive complement
of the squares with `limsup ≤ 13√2/4`". At `N = 0` the `EReal` quotient is `x / 0 = 0`; a single
term does not affect the limsup. The fidelity bridge also derives the real-valued `ε`-form
(`Fidelity/Erdos33.lean`, `erdos33_exists_le_eps`). -/
theorem Aset_limsup :
    atTop.limsup (fun N : ℕ => ((Aset ∩ Icc 1 N).ncard : EReal) / (√N : EReal))
      ≤ ((13 * √2 / 4 : ℝ) : EReal) := by
  classical
  set c : ℝ := 13 * √2 / 4 with hc
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  induction b using EReal.rec with
  | bot => exact absurd hb not_lt_bot
  | top => exact le_top
  | coe b =>
    have hcb : c < b := EReal.coe_lt_coe_iff.1 hb
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < (b - c) / 28 by linarith)
      (show (2 / 3 : ℝ) < 1 by norm_num)
    apply Filter.limsup_le_of_le (by isBoundedDefault)
    filter_upwards [eventually_ge_atTop (L K)] with N hN
    have hN1 : 1 ≤ N := le_trans (by rw [← L_zero]; exact L_strictMono.monotone (Nat.zero_le K)) hN
    obtain ⟨k, hk1, hk2⟩ := exists_scale N hN1
    have hKk : K ≤ k := by
      by_contra h
      push Not at h
      have := L_strictMono.monotone (show k + 1 ≤ K by omega)
      omega
    have hcard := card_le k N hk1 hk2
    have hset : Aset ∩ Icc 1 N = ↑((Finset.Icc 1 N).filter (· ∈ Aset)) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Finset.coe_filter, Finset.mem_Icc,
        Set.mem_ofPred_eq]
      tauto
    rw [hset, Set.ncard_coe_finset, ← EReal.coe_natCast, ← EReal.coe_div, EReal.coe_le_coe_iff]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hsqrt : 0 < √(N : ℝ) := Real.sqrt_pos.2 hNpos
    rw [div_le_iff₀ hsqrt]
    have h4 : (9 : ℝ) ^ k ≤ 4 * N := by
      have := four_mul_L k
      have : (9 : ℕ) ^ k ≤ 4 * N := by omega
      exact_mod_cast this
    have hq : (3 : ℝ) ^ k ≤ 2 * √(N : ℝ) := by
      have h9 : ((3 : ℝ) ^ k) ^ 2 = 9 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have hs : √(N : ℝ) ^ 2 = N := Real.sq_sqrt hNpos.le
      nlinarith [sq_nonneg ((3 : ℝ) ^ k - 2 * √(N : ℝ)), pow_pos (show (0:ℝ) < 3 by norm_num) k]
    have hexp : (13 * k + 14 : ℝ) ≤ 14 * 2 ^ k := by exact_mod_cast thirteen_le k
    have hpow : (2 / 3 : ℝ) ^ k ≤ (2 / 3) ^ K := pow_le_pow_of_le_one (by norm_num) (by norm_num) hKk
    have h23 : (2 : ℝ) ^ k = (2 / 3) ^ k * 3 ^ k := by rw [← mul_pow]; norm_num
    have e1 : (13 * k + 14 : ℝ) ≤ 28 * (2 / 3) ^ K * √(N : ℝ) := by
      calc (13 * k + 14 : ℝ) ≤ 14 * ((2 / 3) ^ k * 3 ^ k) := by rw [← h23]; exact hexp
        _ ≤ 14 * ((2 / 3) ^ K * (2 * √(N : ℝ))) := by gcongr
        _ = 28 * (2 / 3) ^ K * √(N : ℝ) := by ring
    have e2 : 28 * (2 / 3) ^ K * √(N : ℝ) ≤ (b - c) * √(N : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hsqrt.le; linarith
    rw [← hc] at hcard
    linarith

/-- The new bound `13√2/4 ≈ 4.596` for the infimum in formal-conjectures' `erdos_33`
(an upper bound only: the exact value `erdos_33.answer` is still open). -/
theorem erdos_33_le_13_sqrt2_div_4 :
    ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N =>
    (A.1 ∩ Icc 1 N).ncard / (√N : EReal)) ≤ ((13 * √2 / 4 : ℝ) : EReal) :=
  iInf_le_of_le ⟨Aset, Aset_basis⟩ Aset_limsup

/-- `13√2/4 ≤ 2φ^{5/2}` -/
lemma thirteen_sqrt2_le : 13 * √2 / 4 ≤ 2 * (φ ^ ((5 : ℝ) / 2)) := by
  have h1 : (1 : ℝ) ≤ φ := Real.one_lt_goldenRatio.le
  have h2 : φ ^ (2 : ℝ) ≤ φ ^ ((5 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  have h3 : φ ^ (2 : ℝ) = φ + 1 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.goldenRatio_sq]
  have hs2 : √2 < 1.5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hφ : 1.5 < φ := by
    have : (2 : ℝ) < √5 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    rw [Real.goldenRatio]; linarith
  nlinarith

/-- formal-conjectures' `vanDoorn` variant follows from the new bound (it does not use van Doorn's
construction). -/
theorem vanDoorn_of_new :
    ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N =>
    (A.1 ∩ Icc 1 N).ncard / (√N : EReal)) ≤ ↑(2 * (φ ^ ((5 : ℝ) / 2))) :=
  erdos_33_le_13_sqrt2_div_4.trans (EReal.coe_le_coe_iff.2 thirteen_sqrt2_le)

/-- formal-conjectures `erdos_33.variants.vanDoorn` (bound `2φ^{5/2} ≈ 6.66`, due to
W. van Doorn), statement verbatim minus the `@[category research solved, AMS 11]` attribute.

**Obtained as a corollary of the new bound** `erdos_33_le_13_sqrt2_div_4` and of
`13√2/4 ≤ 2φ^{5/2}` (`thirteen_sqrt2_le`). This is **not** a formalization of van Doorn's
construction, nor of his stronger statement `|A ∩ [1, N]| < 2φ^{5/2}·√N` for every `N`; it only
proves formal-conjectures' weaker statement about the infimum of the limsup. -/
theorem erdos_33.variants.vanDoorn :
    ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N =>
    (A.1 ∩ Icc 1 N).ncard / (√N : EReal)) ≤ ↑(2 * (φ ^ ((5 : ℝ) / 2))) :=
  vanDoorn_of_new

end Erdos33

#print axioms Erdos33.erdos_33_le_13_sqrt2_div_4
#print axioms Erdos33.erdos_33.variants.vanDoorn
#print axioms Erdos33.Aset_basis
#print axioms Erdos33.Aset_limsup
