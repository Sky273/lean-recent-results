import Mathlib

/-!
# Park (arXiv:2609.08137): the Fibonacci numbers are not an additive uniqueness set

Formalization of P.-S. Park, *The Fibonacci numbers are not an additive uniqueness set for
multiplicative functions* (arXiv:2609.08137). The paper answers negatively a question of Spiro
(J. Number Theory 42, 1992): there is a multiplicative `f ≠ id`, even one with positive integer
values, such that `f (F n + F m) = f (F n) + f (F m)` for all `n, m ≥ 1`.

## The counterexample

Let `p = 557` and `q = 2417`, the two prime factors of `F 31 = 1346269`. The paper's function
(`FibSpiro.parkFun`) is `f N = N * (q / p) ^ (𝟙[p ∣ N] - 𝟙[q ∣ N])`, that is
`f N = (N / p) * q` if `p ∣ N` and `q ∤ N`, `f N = (N / q) * p` if `q ∣ N` and `p ∤ N`, and
`f N = N` otherwise. On prime powers, `f (p ^ a) = p ^ (a - 1) * q` and
`f (q ^ b) = q ^ (b - 1) * p` for `a, b ≥ 1`, and `f` fixes every other prime power: a single
factor `p` is traded for a single factor `q`. It is not the exponent swap
`p ^ a * q ^ b * m ↦ q ^ a * p ^ b * m`; for instance `f (557 ^ 2) = 557 * 2417`
(`FibSpiro.parkFun_557_sq`). Everything rests on the key lemma, the paper's Theorem 2.1:
`557 ∣ F n + F m ↔ 2417 ∣ F n + F m`.

## Contents

* `FibSpiro` (Section 2 of the paper): the definitions `IsAUSet` and `posFib`; the key lemma
  `key`, proved by periodicity of `F` modulo `F 31` (period `124`) plus a kernel check of the
  `124 × 124` residue pairs (`finite_check`); the function `parkFun`; and the main theorems
  `exists_nat_counterexample` (positive-integer-valued form) and `not_isAUSet_posFib`.
* `FibCrit` (Sections 3 to 5): Park's Theorem 4.1, the fourth-power criterion, in general
  (`criterion`, proved symbolically, with no computation); its instance `r = 31`, which gives
  a second, independent proof of the key lemma, as in the paper (`key_via_criterion`); the
  divisibility equivalences for the five other rows of the table of Section 5 (`row41` to
  `row73`); and the multiplicativity and fixing parts of Proposition 3.1 (`switchFun_*`).
* At the end, the main theorems again, with the key lemma taken from Theorem 4.1 instead of
  `finite_check` (`parkFun_fib_add'`, `exists_nat_counterexample'`, `not_isAUSet_posFib'`).

The fidelity bridge `Fidelity/ParkFibonacci.lean` derives from this file the parts of the
paper's statements that are not stated here: positive integer values of `f_t` for `t = q / p`
and a general pair `p, q`, the non-identity clause of Proposition 3.1, the counterexample
conclusion of Theorem 4.1, and the Pisano periods `4 r` of the table.

Kernel computation: `finite_check` uses `decide +kernel` (no `native_decide`). The table rows
use small `decide` checks; `row61` raises `maxRecDepth` so that the kernel can check `norm_num`'s
proof that `555003497` is prime.
-/

open ArithmeticFunction

/-! ## Section 2 of the paper: the explicit counterexample -/

namespace FibSpiro

/-- Additive uniqueness set (Spiro), for complex multiplicative functions: `E ⊆ ℕ` is an AU set
if every multiplicative `f` with `f (a + b) = f a + f b` for all `a, b ∈ E` is the identity on
the positive integers. (An `ArithmeticFunction` vanishes at `0`, hence `0 < n`.) -/
def IsAUSet (E : Set ℕ) : Prop :=
  ∀ f : ArithmeticFunction ℂ, f.IsMultiplicative →
    (∀ a ∈ E, ∀ b ∈ E, f (a + b) = f a + f b) → ∀ n, 0 < n → f n = n

/-- The set of positive Fibonacci numbers `{F n | n ≥ 1}`. -/
def posFib : Set ℕ := {a | ∃ n, 1 ≤ n ∧ a = Nat.fib n}

/-- Sanity check 1: `IsAUSet` is not always false; `ℕ` itself is an AU set. -/
theorem isAUSet_univ : IsAUSet Set.univ := by
  intro f hf hadd n _
  induction n with
  | zero => simp
  | succ k ih =>
    rw [hadd k trivial 1 trivial, hf.map_one]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [ih hk]; push_cast; ring

/-- Sanity check 2: the identity satisfies the hypotheses of `IsAUSet E`, for any `E`. -/
theorem id_satisfies (E : Set ℕ) :
    ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℂ).IsMultiplicative ∧
    ∀ a ∈ E, ∀ b ∈ E, ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)
      (a + b) = ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) a +
        ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) b :=
  ⟨isMultiplicative_id.natCast, fun a _ b _ => by simp⟩


/-! ### The key lemma (the paper's Theorem 2.1): `557 ∣ F n + F m ↔ 2417 ∣ F n + F m`

Proved here without Theorem 4.1. Modulo `F 31 = 1346269 = 557 * 2417`, the Fibonacci sequence
has period `124` (`fib_period`, from `F 123 ≡ 1` and `F 124 ≡ 0`), so both divisibilities depend
only on `(n % 124, m % 124)`; the `124 × 124` cases are checked by the kernel (`finite_check`).
The lemma holds for all `n, m` (the paper takes `n, m ≥ 1`). The paper's own proof, via
Theorem 4.1, is formalized below as `FibCrit.key_via_criterion`. -/

/-- `124` is a period of the Fibonacci sequence modulo `F 31 = 1346269`. -/
theorem fib_period (n : ℕ) : Nat.fib (n + 124) % 1346269 = Nat.fib n % 1346269 := by
  have h := Nat.fib_add n 123
  have h1 : Nat.fib 123 % 1346269 = 1 := by decide
  have h2 : Nat.fib 124 % 1346269 = 0 := by decide
  rw [show n + 124 = n + 123 + 1 by omega, h, Nat.add_mod, Nat.mul_mod, h1,
    Nat.mul_mod (Nat.fib (n + 1)), h2]
  simp

/-- Reduction of the index modulo `124`. -/
theorem fib_mod (n : ℕ) : Nat.fib n % 1346269 = Nat.fib (n % 124) % 1346269 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 124 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 124 := ⟨n - 124, by omega⟩
      rw [fib_period, ih k (by omega), Nat.add_mod_right]

/-- The `124 × 124` residue pairs, checked by kernel evaluation (`decide +kernel`). -/
theorem finite_check : ∀ i < 124, ∀ j < 124,
    ((Nat.fib i % 1346269 + Nat.fib j % 1346269) % 557 = 0 ↔
      (Nat.fib i % 1346269 + Nat.fib j % 1346269) % 2417 = 0) := by
  decide +kernel

/-- **Key lemma** (the paper's Theorem 2.1), for all `n, m`. -/
theorem key (n m : ℕ) : 557 ∣ Nat.fib n + Nat.fib m ↔ 2417 ∣ Nat.fib n + Nat.fib m := by
  have e557 : ∀ x, x % 557 = x % 1346269 % 557 := fun x =>
    (Nat.mod_mod_of_dvd x (by norm_num : 557 ∣ 1346269)).symm
  have e2417 : ∀ x, x % 2417 = x % 1346269 % 2417 := fun x =>
    (Nat.mod_mod_of_dvd x (by norm_num : 2417 ∣ 1346269)).symm
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, e557, e2417, Nat.add_mod (Nat.fib n),
    fib_mod n, fib_mod m]
  have := finite_check (n % 124) (Nat.mod_lt _ (by norm_num)) (m % 124)
    (Nat.mod_lt _ (by norm_num))
  rw [← e557, ← e2417]
  simpa [Nat.mod_mod] using this

/-- The case `m = 0` of the key lemma: `557 ∣ F n ↔ 2417 ∣ F n`. -/
theorem key_single (n : ℕ) : 557 ∣ Nat.fib n ↔ 2417 ∣ Nat.fib n := by
  simpa using key n 0

/-! ### The counterexample -/

/-- Park's counterexample, with `p = 557` and `q = 2417`:
`f N = N * (q / p) ^ (𝟙[p ∣ N] - 𝟙[q ∣ N])`, i.e. `(N / p) * q` if `p ∣ N` and `q ∤ N`,
`(N / q) * p` if `q ∣ N` and `p ∤ N`, and `N` otherwise. A single factor `p` is traded for a
single factor `q`, or conversely; higher powers are not swapped (see `parkFun_557_sq`). -/
def parkFun : ArithmeticFunction ℕ where
  toFun N :=
    if 557 ∣ N ∧ ¬ 2417 ∣ N then N / 557 * 2417
    else if 2417 ∣ N ∧ ¬ 557 ∣ N then N / 2417 * 557
    else N
  map_zero' := by simp

theorem parkFun_apply (N : ℕ) : parkFun N =
    if 557 ∣ N ∧ ¬ 2417 ∣ N then N / 557 * 2417
    else if 2417 ∣ N ∧ ¬ 557 ∣ N then N / 2417 * 557
    else N := rfl

/-- If `p ∣ N ↔ q ∣ N`, then `f N = N`. -/
theorem parkFun_of_iff {N : ℕ} (h : 557 ∣ N ↔ 2417 ∣ N) : parkFun N = N := by
  rw [parkFun_apply]
  by_cases h1 : 557 ∣ N
  · simp [h1, h.1 h1]
  · simp [h1, show ¬ 2417 ∣ N from fun h2 => h1 (h.2 h2)]

/-- The divisibility indicator `𝟙[d ∣ N]`, as a natural number. -/
def ind (d N : ℕ) : ℕ := if d ∣ N then 1 else 0

/-- For a prime `d`, the indicator is additive on coprime products. -/
theorem ind_mul {d m n : ℕ} (hd : d.Prime) (hmn : m.Coprime n) :
    ind d (m * n) = ind d m + ind d n := by
  unfold ind
  by_cases hm : d ∣ m <;> by_cases hn : d ∣ n
  · have h1 : d ∣ 1 := hmn.gcd_eq_one ▸ Nat.dvd_gcd hm hn
    exact absurd (Nat.dvd_one.mp h1) hd.one_lt.ne'
  all_goals simp [hm, hn, hd.dvd_mul]

/-- Division-free form of the defining formula:
`f N * p ^ 𝟙[p ∣ N] * q ^ 𝟙[q ∣ N] = N * q ^ 𝟙[p ∣ N] * p ^ 𝟙[q ∣ N]`. -/
theorem parkFun_char (N : ℕ) :
    parkFun N * (557 ^ ind 557 N * 2417 ^ ind 2417 N) =
      N * (2417 ^ ind 557 N * 557 ^ ind 2417 N) := by
  rw [parkFun_apply]; unfold ind
  by_cases h1 : 557 ∣ N <;> by_cases h2 : 2417 ∣ N
  · simp [h1, h2, mul_comm]
  · simp only [h1, h2, not_false_eq_true, and_self, ite_true, ite_false, pow_one, pow_zero]
    obtain ⟨k, rfl⟩ := h1; rw [Nat.mul_div_cancel_left _ (by norm_num)]; ring
  · simp only [h1, h2, not_false_eq_true, and_self, ite_true, ite_false, pow_one, pow_zero,
      false_and]
    obtain ⟨k, rfl⟩ := h2; rw [Nat.mul_div_cancel_left _ (by norm_num)]; ring
  · simp [h1, h2]

/-- `parkFun` is multiplicative. -/
theorem parkFun_isMultiplicative : parkFun.IsMultiplicative := by
  refine ⟨by decide, fun {m n} hmn => ?_⟩
  have p1 : Nat.Prime 557 := by norm_num
  have p2 : Nat.Prime 2417 := by norm_num
  have hm := parkFun_char m
  have hn := parkFun_char n
  have hmn' := parkFun_char (m * n)
  rw [ind_mul p1 hmn, ind_mul p2 hmn] at hmn'
  apply Nat.eq_of_mul_eq_mul_right
    (show 0 < 557 ^ (ind 557 m + ind 557 n) * 2417 ^ (ind 2417 m + ind 2417 n) by positivity)
  rw [hmn']
  calc m * n * (2417 ^ (ind 557 m + ind 557 n) * 557 ^ (ind 2417 m + ind 2417 n))
      = (m * (2417 ^ ind 557 m * 557 ^ ind 2417 m)) *
          (n * (2417 ^ ind 557 n * 557 ^ ind 2417 n)) := by ring
    _ = (parkFun m * (557 ^ ind 557 m * 2417 ^ ind 2417 m)) *
          (parkFun n * (557 ^ ind 557 n * 2417 ^ ind 2417 n)) := by rw [hm, hn]
    _ = parkFun m * parkFun n *
          (557 ^ (ind 557 m + ind 557 n) * 2417 ^ (ind 2417 m + ind 2417 n)) := by ring

/-- `parkFun` is positive on positive integers. -/
theorem parkFun_pos {N : ℕ} (hN : 0 < N) : 0 < parkFun N := by
  rw [parkFun_apply]
  split_ifs with h1 h2
  · obtain ⟨k, rfl⟩ := h1.1; rw [Nat.mul_div_cancel_left _ (by norm_num)]; omega
  · obtain ⟨k, rfl⟩ := h2.1; rw [Nat.mul_div_cancel_left _ (by norm_num)]; omega
  · exact hN

/-- `f (F n) = F n`. -/
theorem parkFun_fib (n : ℕ) : parkFun (Nat.fib n) = Nat.fib n :=
  parkFun_of_iff (key_single n)

/-- `f (F n + F m) = F n + F m`. -/
theorem parkFun_fib_add (n m : ℕ) :
    parkFun (Nat.fib n + Nat.fib m) = Nat.fib n + Nat.fib m :=
  parkFun_of_iff (key n m)

theorem parkFun_557 : parkFun 557 = 2417 := by decide
theorem parkFun_2417 : parkFun 2417 = 557 := by decide

/-- `parkFun` is not the exponent swap `557 ^ a * 2417 ^ b * m ↦ 2417 ^ a * 557 ^ b * m`. -/
theorem parkFun_557_sq : parkFun (557 ^ 2) = 557 * 2417 := by decide

/-- **Main theorem**, positive-integer-valued form: a multiplicative `f`, positive on positive
integers, with `f (F n + F m) = f (F n) + f (F m)` for all `n, m ≥ 1`, and `f 557 = 2417`,
`f 2417 = 557` (so `f ≠ id`). -/
theorem exists_nat_counterexample :
    ∃ f : ArithmeticFunction ℕ, f.IsMultiplicative ∧ (∀ n, 0 < n → 0 < f n) ∧
      (∀ n m, 1 ≤ n → 1 ≤ m →
        f (Nat.fib n + Nat.fib m) = f (Nat.fib n) + f (Nat.fib m)) ∧
      f 557 = 2417 ∧ f 2417 = 557 :=
  ⟨parkFun, parkFun_isMultiplicative, fun _ h => parkFun_pos h,
    fun n m _ _ => by rw [parkFun_fib_add, parkFun_fib, parkFun_fib], parkFun_557, parkFun_2417⟩

/-- **Main theorem**: the positive Fibonacci numbers are not an additive uniqueness set for
complex multiplicative functions. This answers Spiro's 1992 question negatively. -/
theorem not_isAUSet_posFib : ¬ IsAUSet posFib := by
  intro h
  have := h (parkFun : ArithmeticFunction ℂ) parkFun_isMultiplicative.natCast
    (by
      rintro a ⟨n, -, rfl⟩ b ⟨m, -, rfl⟩
      simp only [natCoe_apply]
      rw [parkFun_fib_add, parkFun_fib, parkFun_fib]; push_cast; rfl)
    557 (by norm_num)
  rw [natCoe_apply, parkFun_557] at this
  norm_num at this

end FibSpiro



/-!
## Sections 3 to 5 of the paper: Theorem 4.1 (the fourth-power criterion) and the table

Park's Theorem 4.1: let `r ≥ 5` be odd and let `p ≠ q` be odd primes, both of rank of apparition
`r`, such that for each `ℓ ∈ {p, q}` the residues `F i ^ 4 mod ℓ` (`2 ≤ i ≤ (r - 1) / 2`) are
pairwise distinct. Then `p ∣ F n + F m ↔ q ∣ F n + F m` for all `n, m ≥ 1`.

`FibCrit.criterion` proves this equivalence for all `n, m`, without assuming `p ≠ q`. The
rank-of-apparition hypothesis is phrased through the structure `Hyp`; for an odd prime `ℓ` and
odd `r ≥ 5`, the bridge proves `Hyp ℓ r` equivalent to the paper's `z(ℓ) = r`. The proof follows
the paper: with `c = F (r + 1) mod ℓ`, one has `F (n + r) ≡ c * F n` (`shift`), `c ^ 2 = -1`
(`c_sq`), the reflection `F (r - i) ≡ (-1) ^ (i + 1) * c * F i` (`reflect`), and the normal form
`F n ≡ c ^ e(n) * F (i(n))` with `e`, `i` independent of `ℓ` (`normal_form`).
-/

namespace FibCrit

/-- The hypotheses of Theorem 4.1 on one prime `ℓ`: `r` is odd and `≥ 5`, `ℓ > 2`, and `r` is
the rank of apparition of `ℓ` (`ℓ ∤ F k` for `0 < k < r`, and `ℓ ∣ F r`). Primality of `ℓ` is a
separate hypothesis where it is needed. -/
structure Hyp (ℓ r : ℕ) : Prop where
  r5 : 5 ≤ r
  rodd : Odd r
  two_lt : 2 < ℓ
  hz : ∀ k, 0 < k → k < r → ¬ ℓ ∣ Nat.fib k
  hr : ℓ ∣ Nat.fib r

variable {ℓ r : ℕ}

/-- `ℓ ∣ F n ↔ r ∣ n`. -/
theorem dvd_fib_iff (H : Hyp ℓ r) (n : ℕ) : ℓ ∣ Nat.fib n ↔ r ∣ n := by
  have r5 := H.r5
  constructor
  · intro h
    have hg : ℓ ∣ Nat.fib (Nat.gcd n r) := by
      rw [Nat.fib_gcd]; exact Nat.dvd_gcd h H.hr
    have hpos : 0 < Nat.gcd n r := Nat.gcd_pos_of_pos_right _ (by omega)
    have hle : Nat.gcd n r ≤ r := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right n r)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact absurd hg (H.hz _ hpos hlt)
    · rw [← heq]; exact Nat.gcd_dvd_left n r
  · intro h
    exact dvd_trans H.hr (Nat.fib_dvd r n h)

theorem fib_r (H : Hyp ℓ r) : (Nat.fib r : ZMod ℓ) = 0 :=
  (ZMod.natCast_eq_zero_iff _ _).2 H.hr

/-- `F (n + r) ≡ c * F n (mod ℓ)` with `c = F (r + 1)`. -/
theorem shift (H : Hyp ℓ r) (n : ℕ) :
    (Nat.fib (n + r) : ZMod ℓ) = (Nat.fib (r + 1) : ZMod ℓ) * Nat.fib n := by
  cases n with
  | zero => simp [fib_r H]
  | succ k =>
    have h := Nat.fib_add r k
    rw [show k + 1 + r = r + k + 1 by ring, h]
    push_cast
    rw [fib_r H]; ring

theorem shift_mul (H : Hyp ℓ r) (n k : ℕ) :
    (Nat.fib (n + k * r) : ZMod ℓ) = (Nat.fib (r + 1) : ZMod ℓ) ^ k * Nat.fib n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show n + (k + 1) * r = (n + k * r) + r by ring, shift H, ih]; ring

/-- `F (r - 1) ≡ F (r + 1) (mod ℓ)`. -/
theorem fib_pred (H : Hyp ℓ r) :
    (Nat.fib (r - 1) : ZMod ℓ) = (Nat.fib (r + 1) : ZMod ℓ) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by have := H.r5; omega⟩
  have h0 := fib_r H
  rw [show s + 1 + 1 = s + 2 by ring, Nat.fib_add_two]
  push_cast
  rw [h0]; simp

/-- Cassini (with `r` odd): `c ^ 2 = -1`. -/
theorem c_sq (H : Hyp ℓ r) : (Nat.fib (r + 1) : ZMod ℓ) ^ 2 = -1 := by
  have hc := Int.fib_succ_mul_fib_pred_sub_fib_sq (r : ℤ)
  have h1 : Int.fib ((r : ℤ) + 1) = (Nat.fib (r + 1) : ℤ) := by
    rw [show (r : ℤ) + 1 = ((r + 1 : ℕ) : ℤ) by push_cast; ring]; exact Int.fib_natCast _
  have h2 : Int.fib ((r : ℤ) - 1) = (Nat.fib (r - 1) : ℤ) := by
    rw [show (r : ℤ) - 1 = ((r - 1 : ℕ) : ℤ) by have := H.r5; omega]; exact Int.fib_natCast _
  rw [h1, h2, Int.fib_natCast, Int.natAbs_natCast, H.rodd.neg_one_pow] at hc
  have hc' := congrArg (Int.cast : ℤ → ZMod ℓ) hc
  push_cast at hc'
  rw [fib_r H, fib_pred H] at hc'
  linear_combination hc'

/-- Reflection: `F (r - i) ≡ (-1) ^ (i + 1) * c * F i (mod ℓ)` for `i ≤ r`. -/
theorem reflect (H : Hyp ℓ r) : ∀ i, i ≤ r →
    (Nat.fib (r - i) : ZMod ℓ) = (-1) ^ (i + 1) * (Nat.fib (r + 1) : ZMod ℓ) * Nat.fib i
  | 0, _ => by simp [fib_r H]
  | 1, _ => by simp [fib_pred H]
  | i + 2, hi => by
    have e1 : r - i = (r - (i + 2)) + 2 := by omega
    have e2 : r - (i + 1) = (r - (i + 2)) + 1 := by omega
    have h := Nat.fib_add_two (n := r - (i + 2))
    rw [← e1, ← e2] at h
    have ih0 := reflect H i (by omega)
    have ih1 := reflect H (i + 1) (by omega)
    have h' : (Nat.fib (r - (i + 2)) : ZMod ℓ) =
        (Nat.fib (r - i) : ZMod ℓ) - Nat.fib (r - (i + 1)) := by
      rw [h]; push_cast; ring
    rw [h', ih0, ih1, Nat.fib_add_two]
    push_cast
    ring

/-! ### Normal form `F n ≡ c ^ e(n) * F (i(n))`, with `e`, `i` independent of `ℓ` -/

/-- The index `i(n)` of the normal form; for `r ∤ n` it lies in `[2, (r - 1) / 2]`
(`idx_range`). -/
def idx (r n : ℕ) : ℕ :=
  if n % r ≤ (r - 1) / 2 then (if n % r = 1 then 2 else n % r)
  else (if r - n % r = 1 then 2 else r - n % r)

/-- The exponent `e(n)` of the normal form (only its class modulo `4` matters). -/
def ex (r n : ℕ) : ℕ :=
  if n % r ≤ (r - 1) / 2 then n / r else n / r + 2 * (r - n % r + 1) + 1

/-- Normal form: `F n ≡ c ^ e(n) * F (i(n)) (mod ℓ)`, with `c = F (r + 1)`. -/
theorem normal_form (H : Hyp ℓ r) (n : ℕ) :
    (Nat.fib n : ZMod ℓ) = (Nat.fib (r + 1) : ZMod ℓ) ^ ex r n * Nat.fib (idx r n) := by
  have hc2 := c_sq H
  have hn : n = n % r + n / r * r := (Nat.mod_add_div' n r).symm
  have hlt : n % r < r := Nat.mod_lt _ (by have := H.r5; omega)
  have hrefl : (Nat.fib (n % r) : ZMod ℓ) =
      (Nat.fib (r + 1) : ZMod ℓ) ^ (2 * (r - n % r + 1) + 1) * Nat.fib (r - n % r) := by
    have h := reflect H (r - n % r) (by omega)
    rw [show r - (r - n % r) = n % r by omega, ← hc2, ← pow_mul] at h
    rw [h]; ring
  conv_lhs => rw [hn, shift_mul H]
  unfold idx ex
  split_ifs with h1 h2 h3
  · rw [h2]; rfl
  · rfl
  · rw [hrefl, h3, pow_add]
    simp only [Nat.fib_one, Nat.fib_two, Nat.cast_one]
    ring
  · rw [hrefl, pow_add]
    ring

theorem idx_range (H : Hyp ℓ r) {n : ℕ} (hn : ¬ r ∣ n) :
    2 ≤ idx r n ∧ idx r n ≤ (r - 1) / 2 := by
  have r5 := H.r5
  have hlt : n % r < r := Nat.mod_lt _ (by omega)
  have hne : n % r ≠ 0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
  obtain ⟨t, ht⟩ := H.rodd
  unfold idx
  split_ifs <;> omega

/-- The core: for `r ∤ n, m`, divisibility of `F n + F m` by `ℓ` is an `ℓ`-independent
condition on `(n, m)`. -/
theorem sum_iff (H : Hyp ℓ r) [Fact ℓ.Prime]
    (hd : ∀ i j, 2 ≤ i → i ≤ (r - 1) / 2 → 2 ≤ j → j ≤ (r - 1) / 2 →
      Nat.fib i ^ 4 % ℓ = Nat.fib j ^ 4 % ℓ → i = j)
    {n m : ℕ} (hn : ¬ r ∣ n) (hm : ¬ r ∣ m) :
    ℓ ∣ Nat.fib n + Nat.fib m ↔ (idx r n = idx r m ∧ ex r n % 4 = (ex r m + 2) % 4) := by
  have : Fact (2 < ℓ) := ⟨H.two_lt⟩
  set c : ZMod ℓ := (Nat.fib (r + 1) : ZMod ℓ) with hcdef
  have hc2 : c ^ 2 = -1 := c_sq H
  have hc4 : c ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by rfl, pow_mul, hc2]; norm_num
  have hfin : IsOfFinOrder c := isOfFinOrder_iff_pow_eq_one.2 ⟨4, by norm_num, hc4⟩
  have hord : orderOf c = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := c)
      (by rw [pow_one, hc2]; exact ZMod.neg_one_ne_one) (by simpa using hc4)
    simpa using this
  have hn' := idx_range H hn
  have hm' := idx_range H hm
  have hφm : (Nat.fib (idx r m) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact H.hz _ (by omega) (by have := H.r5; omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, normal_form H n, normal_form H m]
  constructor
  · intro h
    have h1 : c ^ ex r n * Nat.fib (idx r n) = -(c ^ ex r m * Nat.fib (idx r m)) :=
      eq_neg_of_add_eq_zero_left h
    have h4 : ((Nat.fib (idx r n) : ZMod ℓ)) ^ 4 = ((Nat.fib (idx r m) : ZMod ℓ)) ^ 4 := by
      have hpow : ∀ (e : ℕ) (x : ZMod ℓ), (c ^ e * x) ^ 4 = x ^ 4 := by
        intro e x
        rw [mul_pow, ← pow_mul, mul_comm e 4, pow_mul, hc4, one_pow, one_mul]
      rw [← hpow (ex r n) (Nat.fib (idx r n) : ZMod ℓ), h1,
        ← hpow (ex r m) (Nat.fib (idx r m) : ZMod ℓ)]
      ring
    have hi : idx r n = idx r m := by
      apply hd _ _ hn'.1 hn'.2 hm'.1 hm'.2
      rw [← ZMod.natCast_eq_natCast_iff']; push_cast; exact h4
    refine ⟨hi, ?_⟩
    rw [hi] at h
    have h' : (c ^ ex r n + c ^ ex r m) * Nat.fib (idx r m) = 0 := by rw [add_mul]; exact h
    have h'' := (mul_eq_zero.1 h').resolve_right hφm
    have : c ^ ex r n = c ^ (ex r m + 2) := by
      rw [pow_add, hc2]; linear_combination h''
    rw [hfin.pow_inj_mod, hord] at this
    exact this
  · rintro ⟨hi, he⟩
    rw [hi]
    have : c ^ ex r n = c ^ (ex r m + 2) := by rw [hfin.pow_inj_mod, hord]; exact he
    rw [this, pow_add, hc2]; ring

/-- **Theorem 4.1** of Park (the divisibility equivalence), for all `n, m` (the paper takes
`n, m ≥ 1`); `p ≠ q` is not needed. -/
theorem criterion {r p q : ℕ} (hp : p.Prime) (hq : q.Prime) (Hp : Hyp p r) (Hq : Hyp q r)
    (hdp : ∀ i j, 2 ≤ i → i ≤ (r - 1) / 2 → 2 ≤ j → j ≤ (r - 1) / 2 →
      Nat.fib i ^ 4 % p = Nat.fib j ^ 4 % p → i = j)
    (hdq : ∀ i j, 2 ≤ i → i ≤ (r - 1) / 2 → 2 ≤ j → j ≤ (r - 1) / 2 →
      Nat.fib i ^ 4 % q = Nat.fib j ^ 4 % q → i = j)
    (n m : ℕ) : p ∣ Nat.fib n + Nat.fib m ↔ q ∣ Nat.fib n + Nat.fib m := by
  have := Fact.mk hp
  have := Fact.mk hq
  by_cases hn : r ∣ n <;> by_cases hm : r ∣ m
  · exact ⟨fun _ => dvd_add ((dvd_fib_iff Hq n).2 hn) ((dvd_fib_iff Hq m).2 hm),
      fun _ => dvd_add ((dvd_fib_iff Hp n).2 hn) ((dvd_fib_iff Hp m).2 hm)⟩
  · constructor
    · intro h; exact absurd ((Nat.dvd_add_right ((dvd_fib_iff Hp n).2 hn)).1 h)
        (by rw [dvd_fib_iff Hp]; exact hm)
    · intro h; exact absurd ((Nat.dvd_add_right ((dvd_fib_iff Hq n).2 hn)).1 h)
        (by rw [dvd_fib_iff Hq]; exact hm)
  · constructor
    · intro h; exact absurd ((Nat.dvd_add_left ((dvd_fib_iff Hp m).2 hm)).1 h)
        (by rw [dvd_fib_iff Hp]; exact hn)
    · intro h; exact absurd ((Nat.dvd_add_left ((dvd_fib_iff Hq m).2 hm)).1 h)
        (by rw [dvd_fib_iff Hq]; exact hn)
  · rw [sum_iff Hp hdp hn hm, sum_iff Hq hdq hn hm]

/-! ### Instantiation `r = 31`, `p = 557`, `q = 2417`: the paper's proof of Theorem 2.1 -/

theorem hyp557 : Hyp 557 31 where
  r5 := by norm_num
  rodd := by decide
  two_lt := by norm_num
  hz := by
    have : ∀ k < 31, 0 < k → ¬ 557 ∣ Nat.fib k := by decide
    exact fun k h0 h1 => this k h1 h0
  hr := by decide

theorem hyp2417 : Hyp 2417 31 where
  r5 := by norm_num
  rodd := by decide
  two_lt := by norm_num
  hz := by
    have : ∀ k < 31, 0 < k → ¬ 2417 ∣ Nat.fib k := by decide
    exact fun k h0 h1 => this k h1 h0
  hr := by decide

/-- The key lemma (Theorem 2.1) again, obtained from Theorem 4.1 as in the paper. It does not
use `FibSpiro.finite_check`. -/
theorem key_via_criterion (n m : ℕ) :
    557 ∣ Nat.fib n + Nat.fib m ↔ 2417 ∣ Nat.fib n + Nat.fib m := by
  refine criterion (by norm_num) (by norm_num) hyp557 hyp2417 ?_ ?_ n m
  · have : ∀ i < 16, ∀ j < 16, 2 ≤ i → 2 ≤ j →
        Nat.fib i ^ 4 % 557 = Nat.fib j ^ 4 % 557 → i = j := by decide
    intro i j hi1 hi2 hj1 hj2; exact this i (by omega) j (by omega) hi1 hj1
  · have : ∀ i < 16, ∀ j < 16, 2 ≤ i → 2 ≤ j →
        Nat.fib i ^ 4 % 2417 = Nat.fib j ^ 4 % 2417 → i = j := by decide
    intro i j hi1 hi2 hj1 hj2; exact this i (by omega) j (by omega) hi1 hj1


/-! ### Section 5: the other rows of the table, via Theorem 4.1

For each further row `(r, p, q)` of the paper's table, the divisibility equivalence
`p ∣ F n + F m ↔ q ∣ F n + F m`, with the hypotheses of `criterion` checked by `decide` and
`norm_num`. The Pisano periods `4 r` and the resulting counterexamples are derived in the
bridge. -/

/-- `Hyp` from conditions that `decide` can check. -/
theorem hyp_of (ℓ r : ℕ) (h5 : 5 ≤ r) (hodd : r % 2 = 1) (h2 : 2 < ℓ)
    (hz : ∀ k < r, 0 < k → ¬ ℓ ∣ Nat.fib k) (hr : Nat.fib r % ℓ = 0) : Hyp ℓ r :=
  ⟨h5, Nat.odd_iff.2 hodd, h2, fun k h0 h1 => hz k h1 h0, Nat.dvd_of_mod_eq_zero hr⟩

/-- The fourth-power distinctness hypothesis, from a bounded form that `decide` can check. -/
theorem distinct_of (ℓ r : ℕ)
    (h : ∀ i < (r - 1) / 2 + 1, ∀ j < (r - 1) / 2 + 1, 2 ≤ i → 2 ≤ j →
      Nat.fib i ^ 4 % ℓ = Nat.fib j ^ 4 % ℓ → i = j) :
    ∀ i j, 2 ≤ i → i ≤ (r - 1) / 2 → 2 ≤ j → j ≤ (r - 1) / 2 →
      Nat.fib i ^ 4 % ℓ = Nat.fib j ^ 4 % ℓ → i = j :=
  fun i j hi1 hi2 hj1 hj2 => h i (by omega) j (by omega) hi1 hj1

theorem row41 (n m : ℕ) : 2789 ∣ Nat.fib n + Nat.fib m ↔ 59369 ∣ Nat.fib n + Nat.fib m :=
  criterion (by norm_num) (by norm_num)
    (hyp_of 2789 41 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (hyp_of 59369 41 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (distinct_of 2789 41 (by decide)) (distinct_of 59369 41 (by decide)) n m

theorem row55 (n m : ℕ) : 661 ∣ Nat.fib n + Nat.fib m ↔ 474541 ∣ Nat.fib n + Nat.fib m :=
  criterion (by norm_num) (by norm_num)
    (hyp_of 661 55 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (hyp_of 474541 55 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (distinct_of 661 55 (by decide)) (distinct_of 474541 55 (by decide)) n m

-- `maxRecDepth` is raised so that the kernel can check `norm_num`'s proof that `555003497` is
-- prime (with the default limit it reports "deep recursion detected").
set_option maxRecDepth 200000 in
theorem row61 (n m : ℕ) : 4513 ∣ Nat.fib n + Nat.fib m ↔ 555003497 ∣ Nat.fib n + Nat.fib m :=
  criterion (by norm_num) (by norm_num)
    (hyp_of 4513 61 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (hyp_of 555003497 61 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (distinct_of 4513 61 (by decide)) (distinct_of 555003497 61 (by decide)) n m

theorem row67 (n m : ℕ) : 116849 ∣ Nat.fib n + Nat.fib m ↔ 1429913 ∣ Nat.fib n + Nat.fib m :=
  criterion (by norm_num) (by norm_num)
    (hyp_of 116849 67 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (hyp_of 1429913 67 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (distinct_of 116849 67 (by decide)) (distinct_of 1429913 67 (by decide)) n m

theorem row73 (n m : ℕ) : 9375829 ∣ Nat.fib n + Nat.fib m ↔ 86020717 ∣ Nat.fib n + Nat.fib m :=
  criterion (by norm_num) (by norm_num)
    (hyp_of 9375829 73 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (hyp_of 86020717 73 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (distinct_of 9375829 73 (by decide)) (distinct_of 86020717 73 (by decide)) n m

/-! ### Proposition 3.1 (signature switching), complex `t ≠ 0`

`switchFun p q t` is the paper's `f_t N = N * t ^ (𝟙[p ∣ N] - 𝟙[q ∣ N])`, set to `0` at `N = 0`
(an `ArithmeticFunction` vanishes at `0`). This file proves that `f_t` is multiplicative
(`switchFun_isMultiplicative`), that it fixes every `N` with `p ∣ N ↔ q ∣ N` (`switchFun_fix`),
and that `f_t p = p * t` (`switchFun_p`). The bridge derives from these the remaining clauses:
`f_t ≠ id` for `t ≠ 1`, and positive integer values for `t = q / p`. -/

/-- The paper's `f_t` (Proposition 3.1), extended by `0` at `N = 0`. -/
noncomputable def switchFun (p q : ℕ) (t : ℂ) : ArithmeticFunction ℂ where
  toFun N := if N = 0 then 0 else
    (N : ℂ) * t ^ ((if p ∣ N then (1 : ℤ) else 0) - (if q ∣ N then (1 : ℤ) else 0))
  map_zero' := by simp

theorem switchFun_apply (p q : ℕ) (t : ℂ) (N : ℕ) : switchFun p q t N = if N = 0 then 0 else
    (N : ℂ) * t ^ ((if p ∣ N then (1 : ℤ) else 0) - (if q ∣ N then (1 : ℤ) else 0)) := rfl

/-- For a prime `d`, the integer-valued indicator `𝟙[d ∣ N]` is additive on coprime products. -/
theorem indZ_mul {d m n : ℕ} (hd : d.Prime) (hmn : m.Coprime n) :
    (if d ∣ m * n then (1 : ℤ) else 0) = (if d ∣ m then 1 else 0) + (if d ∣ n then 1 else 0) := by
  by_cases hm : d ∣ m <;> by_cases hn : d ∣ n
  · have h1 : d ∣ 1 := hmn.gcd_eq_one ▸ Nat.dvd_gcd hm hn
    exact absurd (Nat.dvd_one.mp h1) hd.one_lt.ne'
  all_goals simp [hm, hn, hd.dvd_mul]

/-- `f_t` is multiplicative (for primes `p`, `q` and `t ≠ 0`). -/
theorem switchFun_isMultiplicative {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {t : ℂ}
    (ht : t ≠ 0) : (switchFun p q t).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨?_, fun {m n} hm hn hmn => ?_⟩
  · simp [switchFun_apply, hp.ne_one, hq.ne_one, Nat.dvd_one]
  · simp only [switchFun_apply, mul_ne_zero hm hn, hm, hn, ite_false, Nat.cast_mul]
    rw [indZ_mul hp hmn, indZ_mul hq hmn,
      show ∀ a b c d : ℤ, a + b - (c + d) = (a - c) + (b - d) from fun _ _ _ _ => by ring,
      zpow_add₀ ht]
    ring

/-- `f_t N = N` whenever `p ∣ N ↔ q ∣ N`. -/
theorem switchFun_fix {p q N : ℕ} {t : ℂ} (h : p ∣ N ↔ q ∣ N) : switchFun p q t N = N := by
  rw [switchFun_apply]
  by_cases h0 : N = 0
  · simp [h0]
  by_cases hp : p ∣ N
  · simp [h0, hp, h.1 hp]
  · simp [h0, hp, show ¬ q ∣ N from fun hq => hp (h.2 hq)]

/-- `f_t p = p * t` for distinct primes `p`, `q`. -/
theorem switchFun_p {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {t : ℂ} :
    switchFun p q t p = p * t := by
  have : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 h).symm
  simp [switchFun_apply, hp.ne_zero, this]

end FibCrit


/-!
## The main theorems again, with the key lemma from Theorem 4.1

The same statements as `parkFun_fib`, `parkFun_fib_add`, `exists_nat_counterexample` and
`not_isAUSet_posFib`, proved through `FibCrit.key_via_criterion` instead of `FibSpiro.key`, hence
without the `124 × 124` kernel check `FibSpiro.finite_check`.
-/

namespace FibSpiro

/-- `f (F n) = F n`, via Theorem 4.1. -/
theorem parkFun_fib' (n : ℕ) : parkFun (Nat.fib n) = Nat.fib n :=
  parkFun_of_iff (by simpa using FibCrit.key_via_criterion n 0)

/-- `f (F n + F m) = F n + F m`, via Theorem 4.1. -/
theorem parkFun_fib_add' (n m : ℕ) :
    parkFun (Nat.fib n + Nat.fib m) = Nat.fib n + Nat.fib m :=
  parkFun_of_iff (FibCrit.key_via_criterion n m)

/-- `exists_nat_counterexample`, via Theorem 4.1. -/
theorem exists_nat_counterexample' :
    ∃ f : ArithmeticFunction ℕ, f.IsMultiplicative ∧ (∀ n, 0 < n → 0 < f n) ∧
      (∀ n m, 1 ≤ n → 1 ≤ m →
        f (Nat.fib n + Nat.fib m) = f (Nat.fib n) + f (Nat.fib m)) ∧
      f 557 = 2417 ∧ f 2417 = 557 :=
  ⟨parkFun, parkFun_isMultiplicative, fun _ h => parkFun_pos h,
    fun n m _ _ => by rw [parkFun_fib_add', parkFun_fib', parkFun_fib'], parkFun_557,
    parkFun_2417⟩

/-- `not_isAUSet_posFib`, via Theorem 4.1. -/
theorem not_isAUSet_posFib' : ¬ IsAUSet posFib := by
  intro h
  have := h (parkFun : ArithmeticFunction ℂ) parkFun_isMultiplicative.natCast
    (by
      rintro a ⟨n, -, rfl⟩ b ⟨m, -, rfl⟩
      simp only [natCoe_apply]
      rw [parkFun_fib_add', parkFun_fib', parkFun_fib']; push_cast; rfl)
    557 (by norm_num)
  rw [natCoe_apply, parkFun_557] at this
  norm_num at this

end FibSpiro

#print axioms FibSpiro.isAUSet_univ
#print axioms FibSpiro.not_isAUSet_posFib
#print axioms FibSpiro.exists_nat_counterexample
#print axioms FibSpiro.parkFun_557_sq
#print axioms FibSpiro.parkFun_fib'
#print axioms FibSpiro.parkFun_fib_add'
#print axioms FibSpiro.exists_nat_counterexample'
#print axioms FibSpiro.not_isAUSet_posFib'
#print axioms FibCrit.criterion
#print axioms FibCrit.key_via_criterion
#print axioms FibCrit.row41
#print axioms FibCrit.row55
#print axioms FibCrit.row61
#print axioms FibCrit.row67
#print axioms FibCrit.row73
#print axioms FibCrit.switchFun_isMultiplicative
#print axioms FibCrit.switchFun_fix
#print axioms FibCrit.switchFun_p
