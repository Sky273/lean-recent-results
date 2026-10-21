import RecentResults.ParkFibonacci
import Mathlib

/-!
# Fidelity bridge: blind statements of Park (arXiv:2609.08137) derived from our formalization

The blind definitions and statements are copied verbatim (namespace `ParkFibBlind`, to avoid
clashes with `FibSpiro` / `FibCrit`), and every statement is proved from the theorems of
`RecentResults.ParkFibonacci`, plus elementary glue lemmas proved here.

Some glue lemmas prove facts that the module does not state: positive integer values of
`switchFn p q (q / p)` for general primes `p, q` (`switchFn_posInt`), the Pisano period `4 r`
(`pisano_of_hyp`), and the equivalence of `FibCrit.Hyp` with the blind `rankOfApparition`
(`hyp_of_rank`, `rank_of_hyp`). They are used for `prop_3_1`, `thm_4_1`,
`thm_4_1_counterexample` and the table rows.

Some verbatim hypotheses are unused in the proofs (linter warnings on `thm_2_1`, `prop_3_1`,
`thm_4_1`): our theorems do not need them, i.e. they are slightly stronger than the blind
statements.
-/

open ArithmeticFunction

namespace ParkFibBlind

/-! ## Blind definitions (verbatim) -/

def posFib : Set ℕ := {a | ∃ n : ℕ, 1 ≤ n ∧ Nat.fib n = a}

def IsAUSetMult (E : Set ℕ) : Prop :=
  ∀ f : ArithmeticFunction ℂ, f.IsMultiplicative →
    (∀ a ∈ E, ∀ b ∈ E, f (a + b) = f a + f b) → ∀ n : ℕ, f n = (n : ℂ)

def FibAdditive {R : Type*} [MonoidWithZero R] [Add R] (f : ArithmeticFunction R) : Prop :=
  ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → f (Nat.fib n + Nat.fib m) = f (Nat.fib n) + f (Nat.fib m)

noncomputable def switchFn (p q : ℕ) (t : ℂ) : ArithmeticFunction ℂ where
  toFun N := (N : ℂ) * t ^ ((if p ∣ N then (1 : ℤ) else 0) - (if q ∣ N then (1 : ℤ) else 0))
  map_zero' := by simp

def PosIntValued (f : ArithmeticFunction ℂ) : Prop := ∀ N : ℕ, 0 < N → ∃ k : ℕ, 0 < k ∧ f N = (k : ℂ)

noncomputable def rankOfApparition (ℓ : ℕ) : ℕ := sInf {r : ℕ | 0 < r ∧ ℓ ∣ Nat.fib r}

def FourthPowersDistinct (ℓ r : ℕ) : Prop :=
  ∀ i j : ℕ, 2 ≤ i → i ≤ (r - 1) / 2 → 2 ≤ j → j ≤ (r - 1) / 2 →
    Nat.fib i ^ 4 ≡ Nat.fib j ^ 4 [MOD ℓ] → i = j

noncomputable def pisanoPeriod (ℓ : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ ∀ n : ℕ, Nat.fib (n + k) ≡ Nat.fib n [MOD ℓ]}

def Thm41Hyp (r p q : ℕ) : Prop :=
  5 ≤ r ∧ Odd r ∧ p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p ≠ q ∧
    rankOfApparition p = r ∧ rankOfApparition q = r ∧ FourthPowersDistinct p r ∧
      FourthPowersDistinct q r

def lucas : ℕ → ℕ | 0 => 2 | 1 => 1 | (n + 2) => lucas (n + 1) + lucas n

noncomputable def parkF : ArithmeticFunction ℂ := switchFn 557 2417 ((2417 : ℂ) / 557)

def parkTable : List (ℕ × ℕ × ℕ) :=
  [(31, 557, 2417), (41, 2789, 59369), (55, 661, 474541), (61, 4513, 555003497),
    (67, 116849, 1429913), (73, 9375829, 86020717)]

/-! ## Glue lemmas (relating blind definitions to ours) -/

theorem switchFn_apply (p q : ℕ) (t : ℂ) (N : ℕ) : switchFn p q t N =
    (N : ℂ) * t ^ ((if p ∣ N then (1 : ℤ) else 0) - (if q ∣ N then (1 : ℤ) else 0)) := rfl

/-- The blind `switchFn` is literally our `FibCrit.switchFun` (they differ only by the explicit
`N = 0` guard, and both vanish at `0`). -/
theorem switchFn_eq_switchFun (p q : ℕ) (t : ℂ) : switchFn p q t = FibCrit.switchFun p q t :=
  ArithmeticFunction.ext fun N => by
    rw [switchFn_apply, FibCrit.switchFun_apply]
    split_ifs with h0 <;> simp_all

theorem switchFn_isMultiplicative {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {t : ℂ} (ht : t ≠ 0) :
    (switchFn p q t).IsMultiplicative := by
  rw [switchFn_eq_switchFun]; exact FibCrit.switchFun_isMultiplicative hp hq ht

theorem switchFn_fix {p q N : ℕ} {t : ℂ} (h : p ∣ N ↔ q ∣ N) : switchFn p q t N = N := by
  rw [switchFn_eq_switchFun]; exact FibCrit.switchFun_fix h

theorem switchFn_p {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {t : ℂ} :
    switchFn p q t p = p * t := by
  rw [switchFn_eq_switchFun]; exact FibCrit.switchFun_p hp hq hpq

/-- Positive integer values for `t = q / p` (general primes). Not in the module in this
generality: the module only has the ℕ-valued `FibSpiro.parkFun` for `p = 557`, `q = 2417`. -/
theorem switchFn_posInt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    PosIntValued (switchFn p q ((q : ℂ) / p)) := by
  intro N hN
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [switchFn_apply]
  by_cases h1 : p ∣ N <;> by_cases h2 : q ∣ N
  · exact ⟨N, hN, by simp [h1, h2]⟩
  · obtain ⟨k, rfl⟩ := h1
    have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
    refine ⟨k * q, Nat.mul_pos hk hq.pos, ?_⟩
    rw [ite_eq_left (dvd_mul_right p k), ite_eq_right h2]
    norm_num
    field_simp
  · obtain ⟨k, rfl⟩ := h2
    have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
    refine ⟨k * p, Nat.mul_pos hk hp.pos, ?_⟩
    rw [ite_eq_right h1, ite_eq_left (dvd_mul_right q k)]
    norm_num
    field_simp
  · exact ⟨N, hN, by simp [h1, h2]⟩

theorem switchFn_qp_ne_id {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ N : ℕ, switchFn p q ((q : ℂ) / p) N ≠ (N : ℂ) := by
  refine ⟨p, ?_⟩
  rw [switchFn_p hp hq hpq]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [mul_div_cancel₀ _ hp0]
  exact_mod_cast (Ne.symm hpq)

/-- Hypotheses of our `FibCrit.Hyp` from the blind's `rankOfApparition` formulation. -/
theorem hyp_of_rank {ℓ r : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ) (hr5 : 5 ≤ r) (hr : Odd r)
    (hz : rankOfApparition ℓ = r) : FibCrit.Hyp ℓ r where
  r5 := hr5
  rodd := hr
  two_lt := by
    have := hℓ.two_le
    obtain ⟨k, hk⟩ := hodd
    omega
  hz := fun k hk hkr hdvd => by
    have := Nat.sInf_le (show k ∈ {r : ℕ | 0 < r ∧ ℓ ∣ Nat.fib r} from ⟨hk, hdvd⟩)
    unfold rankOfApparition at hz
    omega
  hr := by
    have hne : {r : ℕ | 0 < r ∧ ℓ ∣ Nat.fib r}.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      unfold rankOfApparition at hz
      rw [h, Nat.sInf_empty] at hz
      omega
    have := Nat.sInf_mem hne
    unfold rankOfApparition at hz
    rw [hz] at this
    exact this.2

/-- Conversely `FibCrit.Hyp ℓ r` pins down the rank of apparition. -/
theorem rank_of_hyp {ℓ r : ℕ} (H : FibCrit.Hyp ℓ r) : rankOfApparition ℓ = r := by
  unfold rankOfApparition
  apply IsLeast.csInf_eq
  refine ⟨⟨by have := H.r5; omega, H.hr⟩, fun k hk => ?_⟩
  by_contra h
  push Not at h
  exact H.hz k hk.1 h hk.2

/-- Pisano period `4 r` under our hypotheses (not in the module; proved here from
`FibCrit.shift_mul`, `FibCrit.c_sq` and `FibCrit.dvd_fib_iff`). -/
theorem pisano_of_hyp {ℓ r : ℕ} (H : FibCrit.Hyp ℓ r) : pisanoPeriod ℓ = 4 * r := by
  have : Fact (2 < ℓ) := ⟨H.two_lt⟩
  have hc2 := FibCrit.c_sq H
  have hr5 := H.r5
  unfold pisanoPeriod
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨by omega, fun n => ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff, mul_comm 4 r, mul_comm r 4, FibCrit.shift_mul H n 4,
      show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hc2]
    norm_num
  · rintro k ⟨hk0, hk⟩
    by_contra hlt
    push Not at hlt
    have h0 := hk 0
    have h1 := hk 1
    rw [zero_add, Nat.fib_zero] at h0
    have hdvd : ℓ ∣ Nat.fib k := (Nat.modEq_zero_iff_dvd).1 h0
    obtain ⟨j, rfl⟩ := (FibCrit.dvd_fib_iff H k).1 hdvd
    have hj4 : j < 4 := by nlinarith
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · simp at hk0
      · exact h
    rw [← ZMod.natCast_eq_natCast_iff, mul_comm r j, FibCrit.shift_mul H 1 j] at h1
    simp only [Nat.fib_one, Nat.cast_one, mul_one] at h1
    have hne := ZMod.neg_one_ne_one (n := ℓ)
    interval_cases j
    · apply hne; rw [← hc2, pow_one] at *; rw [h1]; norm_num
    · exact hne (hc2.symm.trans h1)
    · apply hne
      have hc3 : (Nat.fib (r + 1) : ZMod ℓ) ^ 3 =
          -(Nat.fib (r + 1) : ZMod ℓ) := by
        rw [show 3 = 2 + 1 from rfl, pow_add, hc2]; ring
      rw [hc3] at h1
      have hc : (Nat.fib (r + 1) : ZMod ℓ) = -1 := by linear_combination -h1
      rw [hc] at hc2
      rw [← hc2]; norm_num

theorem distinct_of_ours {ℓ r : ℕ}
    (h : ∀ i j, 2 ≤ i → i ≤ (r - 1) / 2 → 2 ≤ j → j ≤ (r - 1) / 2 →
      Nat.fib i ^ 4 % ℓ = Nat.fib j ^ 4 % ℓ → i = j) : FourthPowersDistinct ℓ r := h

theorem ours_of_distinct {ℓ r : ℕ} (h : FourthPowersDistinct ℓ r) :
    ∀ i j, 2 ≤ i → i ≤ (r - 1) / 2 → 2 ≤ j → j ≤ (r - 1) / 2 →
      Nat.fib i ^ 4 % ℓ = Nat.fib j ^ 4 % ℓ → i = j := h

/-- `parkF` is our `FibSpiro.parkFun`, cast to `ℂ`. -/
theorem parkF_apply (N : ℕ) : parkF N = ((FibSpiro.parkFun N : ℕ) : ℂ) := by
  rw [parkF, switchFn_apply, FibSpiro.parkFun_apply]
  by_cases h1 : 557 ∣ N <;> by_cases h2 : 2417 ∣ N
  · simp [h1, h2]
  · obtain ⟨k, rfl⟩ := h1
    rw [ite_eq_left (dvd_mul_right 557 k), ite_eq_right h2,
      ite_eq_left ⟨dvd_mul_right 557 k, h2⟩, Nat.mul_div_cancel_left _ (by norm_num)]
    push_cast
    norm_num
    field_simp
  · obtain ⟨k, rfl⟩ := h2
    rw [ite_eq_right h1, ite_eq_left (dvd_mul_right 2417 k), ite_eq_right (fun h => h1 h.1),
      ite_eq_left ⟨dvd_mul_right 2417 k, h1⟩, Nat.mul_div_cancel_left _ (by norm_num)]
    push_cast
    norm_num
    field_simp
  · simp [h1, h2]

theorem parkF_eq_coe : parkF = ((FibSpiro.parkFun : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) :=
  ArithmeticFunction.ext fun N => by rw [parkF_apply, natCoe_apply]

theorem lucas_succ (n : ℕ) : lucas (n + 1) = Nat.fib n + Nat.fib (n + 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | k + 2, ih =>
      rw [show k + 2 + 1 = (k + 1) + 2 from rfl, lucas, ih (k + 1) (by omega), ih k (by omega)]
      simp only [Nat.fib_add_two]
      ring

/-! ## Blind statements, proved from ours -/

theorem not_isAUSetMult_posFib : ¬ IsAUSetMult posFib := by
  intro h
  apply FibSpiro.not_isAUSet_posFib
  intro f hf hadd n _
  refine h f hf (fun a ha b hb => hadd a ?_ b ?_) n
  · obtain ⟨k, hk, rfl⟩ := ha; exact ⟨k, hk, rfl⟩
  · obtain ⟨k, hk, rfl⟩ := hb; exact ⟨k, hk, rfl⟩

theorem exists_posInt_mult_fibAdditive_ne_id :
    ∃ f : ArithmeticFunction ℕ, f.IsMultiplicative ∧ (∀ N : ℕ, 0 < N → 0 < f N) ∧
      f ≠ ArithmeticFunction.id ∧ FibAdditive f := by
  obtain ⟨f, hm, hpos, hadd, h557, -⟩ := FibSpiro.exists_nat_counterexample
  refine ⟨f, hm, hpos, ?_, hadd⟩
  intro heq
  have := congrArg (fun g : ArithmeticFunction ℕ => g 557) heq
  simp only [h557, ArithmeticFunction.id_apply] at this
  norm_num at this

theorem fib_31_factor : Nat.fib 31 = 557 * 2417 := by decide

-- `hn`, `hm` are unused: `FibSpiro.key` holds for all `n, m`.
theorem thm_2_1 (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    557 ∣ Nat.fib n + Nat.fib m ↔ 2417 ∣ Nat.fib n + Nat.fib m := FibSpiro.key n m

theorem parkF_counterexample :
    parkF.IsMultiplicative ∧ PosIntValued parkF ∧ FibAdditive parkF ∧
      (∀ n : ℕ, 1 ≤ n → parkF (Nat.fib n) = (Nat.fib n : ℂ)) ∧
      (∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
        parkF (Nat.fib n + Nat.fib m) = ((Nat.fib n + Nat.fib m : ℕ) : ℂ)) ∧
      parkF 557 = 2417 ∧ parkF 2417 = 557 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [parkF_eq_coe]; exact FibSpiro.parkFun_isMultiplicative.natCast
  · intro N hN
    exact ⟨FibSpiro.parkFun N, FibSpiro.parkFun_pos hN, parkF_apply N⟩
  · intro n m _ _
    rw [parkF_apply, parkF_apply, parkF_apply, FibSpiro.parkFun_fib_add, FibSpiro.parkFun_fib,
      FibSpiro.parkFun_fib]
    push_cast; rfl
  · intro n _
    rw [parkF_apply, FibSpiro.parkFun_fib]
  · intro n m _ _
    rw [parkF_apply, FibSpiro.parkFun_fib_add]
  · rw [parkF_apply, FibSpiro.parkFun_557]; norm_num
  · rw [parkF_apply, FibSpiro.parkFun_2417]; norm_num

theorem parkF_lucas_pow_two :
    (∀ n : ℕ, parkF (lucas n) = (lucas n : ℂ)) ∧
      (∀ a : ℕ, parkF (2 ^ a) = ((2 ^ a : ℕ) : ℂ)) := by
  refine ⟨fun n => ?_, fun a => ?_⟩
  · rw [parkF_apply]
    congr 1
    rcases n with _ | n
    · exact FibSpiro.parkFun_of_iff (by decide)
    · rw [lucas_succ]; exact FibSpiro.parkFun_fib_add n (n + 2)
  · rw [parkF_apply]
    congr 1
    apply FibSpiro.parkFun_of_iff
    constructor
    · intro h
      exact absurd ((Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 557) h)) (by norm_num)
    · intro h
      exact absurd ((Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 2417) h)) (by norm_num)

-- `h𝒜` (positivity of the elements of `𝒜`) is unused.
theorem prop_3_1 (𝒜 : Set ℕ) (h𝒜 : ∀ A ∈ 𝒜, 0 < A) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hsig : ∀ A ∈ 𝒜, (p ∣ A ↔ q ∣ A)) (t : ℂ) (ht : t ≠ 0) :
    (switchFn p q t).IsMultiplicative ∧ (∀ A ∈ 𝒜, switchFn p q t A = (A : ℂ)) ∧
      (t ≠ 1 → ∃ N : ℕ, switchFn p q t N ≠ (N : ℂ)) ∧
      (t = (q : ℂ) / p → PosIntValued (switchFn p q t)) := by
  refine ⟨switchFn_isMultiplicative hp hq ht, fun A hA => switchFn_fix (hsig A hA), ?_, ?_⟩
  · intro ht1
    refine ⟨p, ?_⟩
    rw [switchFn_p hp hq hpq]
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    intro h
    apply ht1
    have : (p : ℂ) * t = p * 1 := by rw [h, mul_one]
    exact mul_left_cancel₀ hp0 this
  · rintro rfl
    exact switchFn_posInt hp hq

-- `hpq` (`p ≠ q`) is unused: `FibCrit.criterion` does not need it.
theorem thm_4_1 (r p q : ℕ) (hr5 : 5 ≤ r) (hr : Odd r)
    (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q) (hpq : p ≠ q)
    (hzp : rankOfApparition p = r) (hzq : rankOfApparition q = r)
    (h4p : FourthPowersDistinct p r) (h4q : FourthPowersDistinct q r) :
    ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → (p ∣ Nat.fib n + Nat.fib m ↔ q ∣ Nat.fib n + Nat.fib m) :=
  fun n m _ _ => FibCrit.criterion hp hq (hyp_of_rank hp hpodd hr5 hr hzp)
    (hyp_of_rank hq hqodd hr5 hr hzq) (ours_of_distinct h4p) (ours_of_distinct h4q) n m

theorem thm_4_1_counterexample (r p q : ℕ) (h : Thm41Hyp r p q) :
    (switchFn p q ((q : ℂ) / p)).IsMultiplicative ∧ PosIntValued (switchFn p q ((q : ℂ) / p)) ∧
      (∃ N : ℕ, switchFn p q ((q : ℂ) / p) N ≠ (N : ℂ)) ∧
      FibAdditive (switchFn p q ((q : ℂ) / p)) := by
  obtain ⟨hr5, hr, hp, hq, hpo, hqo, hpq, hzp, hzq, h4p, h4q⟩ := h
  have Hp := hyp_of_rank hp hpo hr5 hr hzp
  have Hq := hyp_of_rank hq hqo hr5 hr hzq
  have crit := FibCrit.criterion hp hq Hp Hq (ours_of_distinct h4p) (ours_of_distinct h4q)
  have ht : (q : ℂ) / p ≠ 0 :=
    div_ne_zero (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hp.ne_zero)
  refine ⟨switchFn_isMultiplicative hp hq ht, switchFn_posInt hp hq,
    switchFn_qp_ne_id hp hq hpq, fun n m _ _ => ?_⟩
  have hn : p ∣ Nat.fib n ↔ q ∣ Nat.fib n := by simpa using crit n 0
  have hm : p ∣ Nat.fib m ↔ q ∣ Nat.fib m := by simpa using crit m 0
  rw [switchFn_fix (crit n m), switchFn_fix hn, switchFn_fix hm]
  push_cast; rfl

/-! ### Table rows: hypotheses recomputed with our own `hyp_of` / `distinct_of` (same `decide`
calls as in our `row41` … `row73`, which do not export them as named facts). -/

theorem thm41Hyp_of {r p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (Hp : FibCrit.Hyp p r) (Hq : FibCrit.Hyp q r)
    (dp : ∀ i j, 2 ≤ i → i ≤ (r - 1) / 2 → 2 ≤ j → j ≤ (r - 1) / 2 →
      Nat.fib i ^ 4 % p = Nat.fib j ^ 4 % p → i = j)
    (dq : ∀ i j, 2 ≤ i → i ≤ (r - 1) / 2 → 2 ≤ j → j ≤ (r - 1) / 2 →
      Nat.fib i ^ 4 % q = Nat.fib j ^ 4 % q → i = j) :
    Thm41Hyp r p q ∧ pisanoPeriod p = 4 * r ∧ pisanoPeriod q = 4 * r := by
  have hpo : Odd p := hp.odd_of_ne_two (by have := Hp.two_lt; omega)
  have hqo : Odd q := hq.odd_of_ne_two (by have := Hq.two_lt; omega)
  exact ⟨⟨Hp.r5, Hp.rodd, hp, hq, hpo, hqo, hpq, rank_of_hyp Hp, rank_of_hyp Hq,
    distinct_of_ours dp, distinct_of_ours dq⟩, pisano_of_hyp Hp, pisano_of_hyp Hq⟩

theorem row31 : Thm41Hyp 31 557 2417 ∧ pisanoPeriod 557 = 4 * 31 ∧ pisanoPeriod 2417 = 4 * 31 :=
  thm41Hyp_of (by norm_num) (by norm_num) (by norm_num) FibCrit.hyp557 FibCrit.hyp2417
    (FibCrit.distinct_of 557 31 (by decide)) (FibCrit.distinct_of 2417 31 (by decide))

theorem row41 : Thm41Hyp 41 2789 59369 ∧ pisanoPeriod 2789 = 4 * 41 ∧
    pisanoPeriod 59369 = 4 * 41 :=
  thm41Hyp_of (by norm_num) (by norm_num) (by norm_num)
    (FibCrit.hyp_of 2789 41 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (FibCrit.hyp_of 59369 41 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (FibCrit.distinct_of 2789 41 (by decide)) (FibCrit.distinct_of 59369 41 (by decide))

theorem row55 : Thm41Hyp 55 661 474541 ∧ pisanoPeriod 661 = 4 * 55 ∧
    pisanoPeriod 474541 = 4 * 55 :=
  thm41Hyp_of (by norm_num) (by norm_num) (by norm_num)
    (FibCrit.hyp_of 661 55 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (FibCrit.hyp_of 474541 55 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (FibCrit.distinct_of 661 55 (by decide)) (FibCrit.distinct_of 474541 55 (by decide))

-- As for `FibCrit.row61`: `maxRecDepth` is raised so that the kernel can check `norm_num`'s
-- proof that `555003497` is prime.
set_option maxRecDepth 200000 in
theorem row61 : Thm41Hyp 61 4513 555003497 ∧ pisanoPeriod 4513 = 4 * 61 ∧
    pisanoPeriod 555003497 = 4 * 61 :=
  thm41Hyp_of (by norm_num) (by norm_num) (by norm_num)
    (FibCrit.hyp_of 4513 61 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (FibCrit.hyp_of 555003497 61 (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide))
    (FibCrit.distinct_of 4513 61 (by decide)) (FibCrit.distinct_of 555003497 61 (by decide))

theorem row67 : Thm41Hyp 67 116849 1429913 ∧ pisanoPeriod 116849 = 4 * 67 ∧
    pisanoPeriod 1429913 = 4 * 67 :=
  thm41Hyp_of (by norm_num) (by norm_num) (by norm_num)
    (FibCrit.hyp_of 116849 67 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (FibCrit.hyp_of 1429913 67 (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide))
    (FibCrit.distinct_of 116849 67 (by decide)) (FibCrit.distinct_of 1429913 67 (by decide))

theorem row73 : Thm41Hyp 73 9375829 86020717 ∧ pisanoPeriod 9375829 = 4 * 73 ∧
    pisanoPeriod 86020717 = 4 * 73 :=
  thm41Hyp_of (by norm_num) (by norm_num) (by norm_num)
    (FibCrit.hyp_of 9375829 73 (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide))
    (FibCrit.hyp_of 86020717 73 (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide))
    (FibCrit.distinct_of 9375829 73 (by decide)) (FibCrit.distinct_of 86020717 73 (by decide))

theorem table_rows :
    ∀ x ∈ parkTable, Thm41Hyp x.1 x.2.1 x.2.2 ∧
      pisanoPeriod x.2.1 = 4 * x.1 ∧ pisanoPeriod x.2.2 = 4 * x.1 := by
  intro x hx
  simp only [parkTable, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row31
  · exact row41
  · exact row55
  · exact row61
  · exact row67
  · exact row73

theorem table_counterexamples :
    ∀ x ∈ parkTable,
      (switchFn x.2.1 x.2.2 ((x.2.2 : ℂ) / x.2.1)).IsMultiplicative ∧
      PosIntValued (switchFn x.2.1 x.2.2 ((x.2.2 : ℂ) / x.2.1)) ∧
      (∃ N : ℕ, switchFn x.2.1 x.2.2 ((x.2.2 : ℂ) / x.2.1) N ≠ (N : ℂ)) ∧
      FibAdditive (switchFn x.2.1 x.2.2 ((x.2.2 : ℂ) / x.2.1)) :=
  fun x hx => thm_4_1_counterexample x.1 x.2.1 x.2.2 (table_rows x hx).1

theorem remark_37_113 :
    Nat.fib 19 = 37 * 113 ∧ 37 ∣ Nat.fib 9 + Nat.fib 4 ∧ ¬ 113 ∣ Nat.fib 9 + Nat.fib 4 := by
  decide

end ParkFibBlind

#print axioms ParkFibBlind.not_isAUSetMult_posFib
#print axioms ParkFibBlind.exists_posInt_mult_fibAdditive_ne_id
#print axioms ParkFibBlind.fib_31_factor
#print axioms ParkFibBlind.thm_2_1
#print axioms ParkFibBlind.parkF_counterexample
#print axioms ParkFibBlind.parkF_lucas_pow_two
#print axioms ParkFibBlind.prop_3_1
#print axioms ParkFibBlind.thm_4_1
#print axioms ParkFibBlind.thm_4_1_counterexample
#print axioms ParkFibBlind.table_rows
#print axioms ParkFibBlind.table_counterexamples
#print axioms ParkFibBlind.remark_37_113
