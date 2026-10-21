import Mathlib

/-!
# Blind formalization of Poo-Sung Park, arXiv:2609.08137
"The Fibonacci numbers are not an additive uniqueness set for multiplicative functions"

Conventions of the paper: `F_0 = 0, F_1 = 1, F_{n+2} = F_{n+1} + F_n` (this is Mathlib's `Nat.fib`).
A function `f` on the positive integers is multiplicative if `f 1 = 1` and `f (a*b) = f a * f b`
whenever `gcd(a,b) = 1`.  We use Mathlib's `ArithmeticFunction R` (functions `ℕ → R` with the
harmless extra normalisation `f 0 = 0`) and `ArithmeticFunction.IsMultiplicative`, which is exactly
`f 1 = 1 ∧ ∀ {m n}, m.Coprime n → f (m*n) = f m * f n`.

Proofs are all `sorry`.
-/

open ArithmeticFunction

namespace ParkFib

/-! ## Definitions -/

/-- The set of positive Fibonacci numbers `{F_n : n ≥ 1} = {1, 2, 3, 5, 8, ...}`. -/
def posFib : Set ℕ := {a | ∃ n : ℕ, 1 ≤ n ∧ Nat.fib n = a}

/-- `E ⊆ ℕ` is an *additive uniqueness (AU) set* for the class of (complex-valued) multiplicative
functions: every multiplicative `f : ℕ → ℂ` with `f (a + b) = f a + f b` for all `a, b ∈ E`
is the identity. (The identity always satisfies the condition, so "uniquely determined" is the
same as "equal to the identity".) -/
def IsAUSetMult (E : Set ℕ) : Prop :=
  ∀ f : ArithmeticFunction ℂ, f.IsMultiplicative →
    (∀ a ∈ E, ∀ b ∈ E, f (a + b) = f a + f b) → ∀ n : ℕ, f n = (n : ℂ)

/-- Condition (1)/(2) of the paper: `f(F_n + F_m) = f(F_n) + f(F_m)` for all `n, m ≥ 1`. -/
def FibAdditive {R : Type*} [MonoidWithZero R] [Add R] (f : ArithmeticFunction R) : Prop :=
  ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → f (Nat.fib n + Nat.fib m) = f (Nat.fib n) + f (Nat.fib m)

/-- The "signature switching" function of Proposition 3.1 / equation (3):
`f_t(N) = N · t ^ (1_{p ∣ N} - 1_{q ∣ N})` (with `f_t(0) = 0`). -/
noncomputable def switchFn (p q : ℕ) (t : ℂ) : ArithmeticFunction ℂ where
  toFun N := (N : ℂ) * t ^ ((if p ∣ N then (1 : ℤ) else 0) - (if q ∣ N then (1 : ℤ) else 0))
  map_zero' := by simp

/-- `f` takes positive integer values on positive integers. -/
def PosIntValued (f : ArithmeticFunction ℂ) : Prop :=
  ∀ N : ℕ, 0 < N → ∃ k : ℕ, 0 < k ∧ f N = (k : ℂ)

/-- Rank of apparition `z(ℓ)`: the least positive `r` with `ℓ ∣ F_r`
(`sInf ∅ = 0`, which never matters below since we always assert `z(ℓ) = r ≥ 5`). -/
noncomputable def rankOfApparition (ℓ : ℕ) : ℕ := sInf {r : ℕ | 0 < r ∧ ℓ ∣ Nat.fib r}

/-- Condition (2) of Theorem 4.1 (condition (4) in the text): the residues `F_i^4 (mod ℓ)`,
`2 ≤ i ≤ (r-1)/2`, are pairwise distinct. -/
def FourthPowersDistinct (ℓ r : ℕ) : Prop :=
  ∀ i j : ℕ, 2 ≤ i → i ≤ (r - 1) / 2 → 2 ≤ j → j ≤ (r - 1) / 2 →
    Nat.fib i ^ 4 ≡ Nat.fib j ^ 4 [MOD ℓ] → i = j

/-- The Pisano period of `ℓ`: least `k > 0` such that `F_{n+k} ≡ F_n (mod ℓ)` for all `n`. -/
noncomputable def pisanoPeriod (ℓ : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ ∀ n : ℕ, Nat.fib (n + k) ≡ Nat.fib n [MOD ℓ]}

/-- Hypotheses of Theorem 4.1 bundled (used for the table of Section 5). -/
def Thm41Hyp (r p q : ℕ) : Prop :=
  5 ≤ r ∧ Odd r ∧ p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p ≠ q ∧
    rankOfApparition p = r ∧ rankOfApparition q = r ∧
    FourthPowersDistinct p r ∧ FourthPowersDistinct q r

/-- Lucas numbers `L_0 = 2, L_1 = 1, L_{n+2} = L_{n+1} + L_n`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

/-! ## Main result (Abstract / Introduction): answer to Spiro's 1992 question -/

/-- **Main theorem.** The set of positive Fibonacci numbers is *not* an additive uniqueness set
for multiplicative functions (negative answer to Spiro's question). -/
theorem not_isAUSetMult_posFib : ¬ IsAUSetMult posFib := sorry

/-- **Main theorem, as stated in the abstract/introduction.** There is a positive-integer-valued
multiplicative function `f : ℕ → ℕ`, not the identity, with
`f(F_n + F_m) = f(F_n) + f(F_m)` for all `n, m ≥ 1`. -/
theorem exists_posInt_mult_fibAdditive_ne_id :
    ∃ f : ArithmeticFunction ℕ, f.IsMultiplicative ∧ (∀ N : ℕ, 0 < N → 0 < f N) ∧
      f ≠ ArithmeticFunction.id ∧ FibAdditive f := sorry

/-! ## Section 2: the explicit counterexample, `p = 557`, `q = 2417`, `F_31 = 557 · 2417` -/

/-- `F_31 = 1346269 = 557 · 2417`. -/
theorem fib_31_factor : Nat.fib 31 = 557 * 2417 := sorry

/-- **Theorem 2.1.** For all `n, m ≥ 1`: `557 ∣ F_n + F_m ↔ 2417 ∣ F_n + F_m`. -/
theorem thm_2_1 (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    557 ∣ Nat.fib n + Nat.fib m ↔ 2417 ∣ Nat.fib n + Nat.fib m := sorry

/-- The explicit function of equation (3): `f(N) = N · (q/p)^(1_{p∣N} - 1_{q∣N})`,
`p = 557`, `q = 2417`. -/
noncomputable def parkF : ArithmeticFunction ℂ := switchFn 557 2417 ((2417 : ℂ) / 557)

/-- **Section 2 (the counterexample (3)).** `f` is multiplicative, positive-integer valued,
satisfies (2), fixes every `F_n` and every `F_n + F_m`, and swaps `557 ↔ 2417`
(so it is not the identity). -/
theorem parkF_counterexample :
    parkF.IsMultiplicative ∧ PosIntValued parkF ∧ FibAdditive parkF ∧
      (∀ n : ℕ, 1 ≤ n → parkF (Nat.fib n) = (Nat.fib n : ℂ)) ∧
      (∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
        parkF (Nat.fib n + Nat.fib m) = ((Nat.fib n + Nat.fib m : ℕ) : ℂ)) ∧
      parkF 557 = 2417 ∧ parkF 2417 = 557 := sorry

/-- Side remark of Section 2: the counterexample also fixes every Lucas number and every power
of `2` (properties previously suggested the identity might be forced). -/
theorem parkF_lucas_pow_two :
    (∀ n : ℕ, parkF (lucas n) = (lucas n : ℂ)) ∧
      (∀ a : ℕ, parkF (2 ^ a) = ((2 ^ a : ℕ) : ℂ)) := sorry

/-! ## Section 3: Proposition 3.1 (signature switching) -/

/-- **Proposition 3.1.** Let `𝒜` be a set of positive integers and `p ≠ q` primes with identical
signatures on `𝒜` (`1_{p∣A} = 1_{q∣A}` for all `A ∈ 𝒜`), and `t ∈ ℂˣ`. Then
`f_t(N) = N t^(1_{p∣N} - 1_{q∣N})` is multiplicative and `f_t(A) = A` for all `A ∈ 𝒜`;
if `t ≠ 1`, `f_t` is not the identity; for `t = q/p`, `f_t` is positive-integer valued. -/
theorem prop_3_1 (𝒜 : Set ℕ) (h𝒜 : ∀ A ∈ 𝒜, 0 < A) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hsig : ∀ A ∈ 𝒜, (p ∣ A ↔ q ∣ A)) (t : ℂ) (ht : t ≠ 0) :
    (switchFn p q t).IsMultiplicative ∧
      (∀ A ∈ 𝒜, switchFn p q t A = (A : ℂ)) ∧
      (t ≠ 1 → ∃ N : ℕ, switchFn p q t N ≠ (N : ℂ)) ∧
      (t = (q : ℂ) / p → PosIntValued (switchFn p q t)) := sorry

/-! ## Section 4: the Fibonacci criterion -/

/-- **Theorem 4.1.** Let `r ≥ 5` be odd and `p ≠ q` odd primes with
(1) `z(p) = z(q) = r`, and (2) for each `ℓ ∈ {p, q}` the residues `F_i^4 (mod ℓ)`,
`2 ≤ i ≤ (r-1)/2`, pairwise distinct. Then for all `n, m ≥ 1`,
`p ∣ F_n + F_m ↔ q ∣ F_n + F_m`. -/
theorem thm_4_1 (r p q : ℕ) (hr5 : 5 ≤ r) (hr : Odd r)
    (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q) (hpq : p ≠ q)
    (hzp : rankOfApparition p = r) (hzq : rankOfApparition q = r)
    (h4p : FourthPowersDistinct p r) (h4q : FourthPowersDistinct q r) :
    ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → (p ∣ Nat.fib n + Nat.fib m ↔ q ∣ Nat.fib n + Nat.fib m) := sorry

/-- **Theorem 4.1, "consequently" part.** Under the hypotheses of Theorem 4.1, the function
`f(N) = N (q/p)^(1_{p∣N} - 1_{q∣N})` is a positive-integer-valued multiplicative function, not the
identity, satisfying `f(F_n + F_m) = f(F_n) + f(F_m)` for all `n, m ≥ 1`. -/
theorem thm_4_1_counterexample (r p q : ℕ) (h : Thm41Hyp r p q) :
    (switchFn p q ((q : ℂ) / p)).IsMultiplicative ∧ PosIntValued (switchFn p q ((q : ℂ) / p)) ∧
      (∃ N : ℕ, switchFn p q ((q : ℂ) / p) N ≠ (N : ℂ)) ∧
      FibAdditive (switchFn p q ((q : ℂ) / p)) := sorry

/-! ## Section 5: further counterexamples (table) -/

/-- The table of Section 5: triples `(r, p, q)`. -/
def parkTable : List (ℕ × ℕ × ℕ) :=
  [(31, 557, 2417), (41, 2789, 59369), (55, 661, 474541), (61, 4513, 555003497),
    (67, 116849, 1429913), (73, 9375829, 86020717)]

/-- **Section 5 table.** Every row `(r, p, q)` satisfies the hypotheses of Theorem 4.1
(primes `p ≠ q`, odd, `z(p) = z(q) = r`, `r ≥ 5` odd, distinct fourth powers), and the common
Pisano period of `p` and `q` is `4r`. -/
theorem table_rows :
    ∀ x ∈ parkTable, Thm41Hyp x.1 x.2.1 x.2.2 ∧
      pisanoPeriod x.2.1 = 4 * x.1 ∧ pisanoPeriod x.2.2 = 4 * x.1 := sorry

/-- **Section 5.** Each row of the table yields a counterexample to Spiro's question. -/
theorem table_counterexamples :
    ∀ x ∈ parkTable,
      (switchFn x.2.1 x.2.2 ((x.2.2 : ℂ) / x.2.1)).IsMultiplicative ∧
      PosIntValued (switchFn x.2.1 x.2.2 ((x.2.2 : ℂ) / x.2.1)) ∧
      (∃ N : ℕ, switchFn x.2.1 x.2.2 ((x.2.2 : ℂ) / x.2.1) N ≠ (N : ℂ)) ∧
      FibAdditive (switchFn x.2.1 x.2.2 ((x.2.2 : ℂ) / x.2.1)) := sorry

/-- **Section 5 remark.** Sharing a divisor of the same Fibonacci number is not sufficient:
`F_19 = 37 · 113`, but `37 ∣ F_9 + F_4 = 37` while `113 ∤ F_9 + F_4`. -/
theorem remark_37_113 :
    Nat.fib 19 = 37 * 113 ∧ 37 ∣ Nat.fib 9 + Nat.fib 4 ∧ ¬ 113 ∣ Nat.fib 9 + Nat.fib 4 := sorry

end ParkFib
