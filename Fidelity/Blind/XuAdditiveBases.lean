import Mathlib

/-!
# Blind formalization: Xu, "A solution to a strengthened conjecture of Bukh, van Hintum and
Keevash on additive bases" (arXiv:2605.10771), together with the conjecture it resolves
(Bukh–van Hintum–Keevash, "Additive bases: change of domain", arXiv:2409.07442, Conjecture 13
and the extension stated right after it).

Conventions.
* `ℝ^n` is modelled as `Fin n → ℝ`, `ℚ^n` as `Fin n → ℚ`; indices `1 ≤ i ≤ n` become `i : Fin n`.
* `e_i` (standard basis vector) is `Pi.single i 1`.
* Sumsets `X + Y`, `X - Y` are Mathlib's pointwise set operations (`open Pointwise`).
* Cardinalities `|A|` of arbitrary (possibly infinite) sets are `Set.encard : ℕ∞`
  (an infinite set has `encard = ⊤`; the paper explicitly allows `B` infinite:
  "If B is infinite, then the conclusion is immediate").
* "t an integer with 0 ≤ t ≤ n - 1" is encoded as `t : ℕ` with `t + 1 ≤ n`
  (so `n - t` below is an honest, non-truncated subtraction).
* `C(t+1, 2)` is `(t + 1).choose 2`.
-/

open Pointwise

namespace XuBVHK

/-- `S` is a basis of the real vector space `ℝ^n`, viewed as a *set* of vectors:
it is linearly independent and spans `ℝ^n`. -/
def IsBasisSet {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  LinearIndepOn ℝ id S ∧ Submodule.span ℝ S = ⊤

/-- The covering hypothesis of the vector model of BvHK:
`{e_i + e_j : 1 ≤ i ≤ j ≤ n} ⊆ A + B` in `ℚ^n`. -/
def CoversDiagSums {n : ℕ} (A B : Set (Fin n → ℚ)) : Prop :=
  {v : Fin n → ℚ | ∃ i j : Fin n, i ≤ j ∧ v = Pi.single i 1 + Pi.single j 1} ⊆ A + B

/-- **Theorem 1.1** (Xu, arXiv:2605.10771).
"Let S be a basis of ℝ^n, and let A, B ⊆ ℝ^n. Suppose that S + S ⊆ A + B. Let t be an
integer with 0 ≤ t ≤ n − 1. If |A| ≤ n − t, then |B| ≥ n + C(t+1, 2)." -/
theorem theorem_1_1 (n : ℕ) (S A B : Set (Fin n → ℝ)) (hS : IsBasisSet S)
    (hSAB : S + S ⊆ A + B) (t : ℕ) (ht : t + 1 ≤ n)
    (hA : A.encard ≤ ((n - t : ℕ) : ℕ∞)) :
    ((n + (t + 1).choose 2 : ℕ) : ℕ∞) ≤ B.encard := by
  sorry

/-- **Sharpness of Theorem 1.1** (Xu, paragraph after Theorem 1.1).
"The bound is sharp for every basis S = {s_1, …, s_n} and 0 ≤ t ≤ n − 1": there are
`A, B ⊆ ℝ^n` with `S + S ⊆ A + B`, `|A| = n − t` and `|B| = n + C(t+1, 2)`.
(The paper's witnesses: `A = {s_1,…,s_{n−t}}`,
`B = {s_1,…,s_n} ∪ {s_i + s_j − s_1 : n − t < i ≤ j ≤ n}`.) -/
theorem theorem_1_1_sharp (n : ℕ) (S : Set (Fin n → ℝ)) (hS : IsBasisSet S)
    (t : ℕ) (ht : t + 1 ≤ n) :
    ∃ A B : Set (Fin n → ℝ), S + S ⊆ A + B ∧
      A.encard = ((n - t : ℕ) : ℕ∞) ∧
      B.encard = ((n + (t + 1).choose 2 : ℕ) : ℕ∞) := by
  sorry

/-- **Corollary 1.2** (Xu) = the extension of BvHK Conjecture 13 (arXiv:2409.07442, §5).
"Let A, B ⊆ ℚ^n, and suppose that {e_i + e_j : 1 ≤ i ≤ j ≤ n} ⊆ A + B. If 0 ≤ t ≤ n − 1
and |A| ≤ n − t, then |B| ≥ n + C(t+1, 2)." -/
theorem corollary_1_2 (n : ℕ) (A B : Set (Fin n → ℚ)) (hAB : CoversDiagSums A B)
    (t : ℕ) (ht : t + 1 ≤ n) (hA : A.encard ≤ ((n - t : ℕ) : ℕ∞)) :
    ((n + (t + 1).choose 2 : ℕ) : ℕ∞) ≤ B.encard := by
  sorry

/-- **BvHK Conjecture 13** (arXiv:2409.07442), which Xu states is "immediately yielded" by
Theorem 1.1: "Suppose B_0, B_1 ⊆ ℚ^n are such that B_0 + B_1 contains every e_i + e_j with
1 ≤ i ≤ j ≤ n. Then |B_0| + |B_1| ≥ 2n." -/
theorem bvhk_conjecture_13 (n : ℕ) (B₀ B₁ : Set (Fin n → ℚ)) (h : CoversDiagSums B₀ B₁) :
    ((2 * n : ℕ) : ℕ∞) ≤ B₀.encard + B₁.encard := by
  sorry

/-- **BvHK extension of Conjecture 13**, in its original wording (arXiv:2409.07442, §5):
"if |B_0| = n − t for some t ≥ 0 then |B_1| ≥ n + C(t+1, 2)".
(`|B_0| = n - t` is written `|B_0| + t = n` to avoid truncated subtraction.) -/
theorem bvhk_conjecture_13_extension (n : ℕ) (B₀ B₁ : Set (Fin n → ℚ))
    (h : CoversDiagSums B₀ B₁) (t : ℕ) (hB₀ : B₀.encard + t = n) :
    ((n + (t + 1).choose 2 : ℕ) : ℕ∞) ≤ B₁.encard := by
  sorry

/-- **Bukh's question (Problem 12), sum form, over ℝ^n with an arbitrary basis**, answered
affirmatively by Theorem 1.1 ("do the same bounds still hold?"):
if `S` is a basis of `ℝ^n` and `S + S ⊆ A + B` then `|A| + |B| ≥ 2n`. -/
theorem bukh_question_sum (n : ℕ) (S A B : Set (Fin n → ℝ)) (hS : IsBasisSet S)
    (hSAB : S + S ⊆ A + B) :
    ((2 * n : ℕ) : ℕ∞) ≤ A.encard + B.encard := by
  sorry

/-- **Lemma 2.2** (Xu; the "new coloring lemma over 𝔽₂ⁿ", auxiliary).
"Let n ≥ 2 and Γ be an abelian group, and let K ≤ Γ be a subgroup identified with 𝔽₂ⁿ.
Write D_n = {e_i + e_j : 1 ≤ i < j ≤ n} ⊆ K. Let u be an integer with 0 ≤ u ≤ n. Suppose that
X ⊆ C ⊆ Γ, |X| ≤ n − u, and D_n ⊆ X − C. Then |C| ≥ n + C(u, 2)."
The identification of `K` with `𝔽₂ⁿ` is an additive isomorphism `φ : (Fin n → ZMod 2) ≃+ K`. -/
theorem lemma_2_2 (n : ℕ) (hn : 2 ≤ n) {Γ : Type*} [AddCommGroup Γ] (K : AddSubgroup Γ)
    (φ : (Fin n → ZMod 2) ≃+ K) (u : ℕ) (hu : u ≤ n) (X C : Set Γ) (hXC : X ⊆ C)
    (hX : X.encard ≤ ((n - u : ℕ) : ℕ∞))
    (hD : ∀ i j : Fin n, i < j →
      ((φ (Pi.single i 1 + Pi.single j 1) : K) : Γ) ∈ X - C) :
    ((n + u.choose 2 : ℕ) : ℕ∞) ≤ C.encard := by
  sorry

/-- BvHK notation: for an abelian group `G` and `A ⊆ D ⊆ G`,
`D(A) = min {|B| : B ⊆ D, A ⊆ B + B}` (valued in `ℕ∞`; `⊤` if no finite such `B`). -/
noncomputable def basisNumber {G : Type*} [AddCommMonoid G] (D A : Set G) : ℕ∞ :=
  ⨅ (B : Set G) (_ : B ⊆ D) (_ : A ⊆ B + B), B.encard

/-- The integers as a subset of `ℚ`. -/
def intsInRat : Set ℚ := Set.range (Int.cast : ℤ → ℚ)

/-- **Consequence for the change-of-domain problem** (Xu, paragraph after Corollary 1.2,
combined with BvHK's reduction, Lemma 7, and BvHK Theorem 1):
"for every n, there exists a set of integers with a rational 2-basis of size at most n whose
smallest integer 2-basis has size exactly 2n", i.e. `ℚ(A) ≤ n` and `ℤ(A) = 2n`. -/
theorem change_of_domain_factor_two_sharp (n : ℕ) :
    ∃ A : Set ℚ, A ⊆ intsInRat ∧
      basisNumber (Set.univ : Set ℚ) A ≤ (n : ℕ∞) ∧
      basisNumber intsInRat A = ((2 * n : ℕ) : ℕ∞) := by
  sorry

end XuBVHK
