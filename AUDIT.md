# Audit sheet

For each result, this page gives:

- the source claim;
- the Lean statement that is proved;
- the definitions we wrote ourselves, which is where a mis-formalization could hide;
- the independent fidelity evidence;
- what is **not** verified.

All of this was produced by AI agents (Claude, Anthropic). The Lean kernel guarantees the
proofs. The match between the formal statements and the sources deserves a human look; this
sheet is meant to make that look take minutes.

**Global guarantees (all six results).**

- No `sorry`, `admit`, `native_decide` or added `axiom`.
- `#print axioms` on every main theorem gives exactly `[propext, Classical.choice, Quot.sound]`.
- Every module, including every `Fidelity/` bridge, was replayed by `leanchecker`, the
  toolchain's independent kernel checker. Run it one module per invocation (see `README.md`). A
  negative control fails as expected.
- Toolchain: Lean `v4.36.0-rc1` and Mathlib `v4.36.0-rc1`, a release candidate. Some tactics
  used (`grind`, `push Not`, `decide +kernel`) are recent.

**Fidelity method.**

1. For each result, an agent that had *never seen our files* read the source and wrote its own
   Lean statements of the main claims, with `sorry` proofs. These are in `Fidelity/Blind/`, not
   built.
2. A second agent copied those statements verbatim into `Fidelity/<Result>.lean` and **proved
   them from our theorems**. A script checked the copy.
3. Where a blind statement could not be derived, the gap is identified exactly below.

---

## 1. Noel — the List Total Colouring Conjecture is false

- **Source:** Jonathan A. Noel, *The List Total Colouring Conjecture is False*,
  [arXiv:2609.38417](https://arxiv.org/abs/2609.38417) (v1 2026-09-29, v2 2026-10-09). Not
  peer-reviewed.
  - **AI declaration (abstract):** "ChatGPT 6 Astra Ultra discovered the counterexample with
    little input from the author."
  - **AI declaration (body):** the paper says the author checked the arguments and rewrote the
    exposition from AI-generated drafts.
  - **The graph is not new:** it appeared earlier (Abreu–Goedgebeur–Labbate–Mazzuoccolo,
    J. Graph Theory 2019; House of Graphs 27005). What is new is its role as an LTCC
    counterexample, together with the list assignment.
- **Claim (Theorem 1.1):** there is a simple cubic graph on 20 vertices with χ''(G) = 4 and
  χ''_ℓ(G) = 5. The conjecture is stated for multigraphs, so a simple counterexample suffices.
- **Proved** (`RecentResults/NoelListTotalColouring.lean`, namespace `NoelLTCC`):

  ```lean
  theorem exists_cubic_totalChromatic_four_not_totalChoosable_four :
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 20 ∧ G.IsRegularOfDegree 3 ∧
        totalChromaticNumber G = 4 ∧ ∀ k ≤ 4, ¬ IsKChoosable (totalGraph G) k
  theorem five_le_listTotalChromaticNumber_NG : 5 ≤ listTotalChromaticNumber NG
  theorem list_total_colouring_conjecture_false :
      ¬ ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
          (listTotalChromaticNumber G : ℕ∞) = totalChromaticNumber G
  ```

- **Self-written definition: `totalGraph G` on `V ⊕ G.edgeSet`.**
  - Two vertices are adjacent as in `G`.
  - Two distinct edges are adjacent iff they share an endpoint; this clause is proved equal to
    Mathlib's `lineGraph` adjacency.
  - A vertex and an edge are adjacent iff the vertex is an endpoint.
  - Sanity check: χ''(K₂) = χ''_ℓ(K₂) = 3.
- **Copied definitions:** `IsKChoosable` and `listChromaticNumber` are verbatim from
  google-deepmind/formal-conjectures,
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/List.lean` @ `2a315101`.
  Lists have exactly `k` natural-number colours.
- **No junk value:** every finite graph is `|V|`-choosable (via Hall's theorem), so χ''_ℓ ≥ 5 is
  proved on the invariant itself.
- **Fidelity:**
  - The blind three-clause total colouring is proved equivalent to a proper colouring of our
    `totalGraph`.
  - The blind encoding of the paper's graph is proved isomorphic to ours, by `decide +kernel`.
  - The blind "LTCC is false" is proved.
- **Not verified:** the upper bound χ''_ℓ(G) ≤ 5, which the paper takes from
  Juvan–Mohar–Škrekovski (Combin. Probab. Comput. 7 (1998), [7, Theorem 3.1]). We do not
  formalize that theorem.
  - The bridge proves the paper's full Theorem 1.1 with that cited result as a hypothesis, and
    shows that exactly this is missing.
  - The refutation of the conjecture does not need it.
- **Proof route:** the last step is a kernel `decide` over the 4⁴ = 256 cases. It replaces the
  paper's argument that the four sets S_i share a colour t.
- **What the formalization adds:** an end-to-end machine check of an AI-found counterexample,
  including the list assignment. The mathematics is a finite check, which a short program can
  also confirm.

## 2. Noel — the Partial List Colouring Conjecture is false

- **Source:** Jonathan A. Noel, [arXiv:2609.23291](https://arxiv.org/abs/2609.23291) (v1,
  2026-09-20). Not peer-reviewed.
  - **AI declaration (abstract):** the counterexample was discovered and fully verified by
    ChatGPT 6 Astra Ultra after persistent prompting, with almost no mathematical input from the
    author.
  - **AI declaration (body):** the AI also found the short proof given. The author rewrote the
    paper from an AI draft and checked all arguments.
- **Claim (Theorem 1.1):** there is a graph with 14 vertices and list chromatic number 3, and a
  2-list assignment from which at most 9 vertices can be properly coloured. This refutes the
  Albertson–Grossman–Haas conjecture (Discrete Math. 214 (2000)), which requires at least
  2·14/3 vertices.
- **Proved** (`RecentResults/NoelPartialListColouring.lean`, namespace `Noel`):

  ```lean
  def IsPartialLColoring {V : Type*} (G : SimpleGraph V) (L : V → Finset ℕ) (S : Finset V) : Prop :=
    ∃ f : V → ℕ, (∀ v ∈ S, f v ∈ L v) ∧ ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → f v ≠ f w
  def AGHConjecture : Prop :=
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (k ℓ : ℕ),
      listChromaticNumber G = k → 2 ≤ k → 1 ≤ ℓ → ℓ < k →
      ∀ L : V → Finset ℕ, (∀ v, (L v).card = ℓ) →
        ∃ S : Finset V, IsPartialLColoring G L S ∧ ℓ * Fintype.card V ≤ k * S.card
  theorem main : ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W), Fintype.card W = 14 ∧
      listChromaticNumber H = 3 ∧ ∃ M : W → Finset ℕ, (∀ v, (M v).card = 2) ∧
        ∀ S : Finset W, IsPartialLColoring H M S → S.card ≤ 9
  theorem not_AGH : ¬ AGHConjecture
  ```

- **atlas-lean targets:** the module also proves two `theorem_wanted` targets of
  facebookresearch/atlas-lean (@ `8920030e`). Their statements are copied verbatim, apart from
  namespaces; their docstrings are shortened.
  - `PartialListColoringProportionalBoundWanted.conjecture_refuted`: an independently written
    statement of the AGH conjecture.
  - `PartialListColoringWanted.conjecture_refuted`: refutes **Iradmusa's ratio conjecture**
    λ_r/r ≥ λ_s/s for 1 ≤ r ≤ s ≤ χ_ℓ (Open Problem Garden, 2008).
  - Iradmusa's conjecture implies AGH (take s = χ_ℓ), and Noel's example refutes it at r = 2,
    s = 3. This is an immediate corollary, not a new result.
- **Self-written definitions:** `IsPartialLColoring` and `AGHConjecture` (shown above). The
  `ℓ = k` case is omitted because it is trivial; this makes the refuted statement weaker and the
  refutation stronger.
- **Copied definitions:** `IsKChoosable` and `listChromaticNumber` are verbatim from
  formal-conjectures (see section 1). The junk value 0 cannot occur, since `2 ≤ k`.
- **Fidelity:**
  - The blind conjecture, with a rational bound n·(ℓ/k) ≤ |S|, is proved **equivalent** to our
    `AGHConjecture`.
  - The blind graph and list assignment are proved equal to ours up to an explicit relabelling.
- **Not verified:** nothing in Theorem 1.1 or the refutation. Not formalized: the paper's
  closing remark on disjoint unions, and the cited prior results.
- **What the formalization adds:** a machine check of a short, author-checked argument. Its main
  practical use is closing the two atlas-lean `theorem_wanted` targets with checked proofs.

## 3. Erdős problem #33 — an additive complement of the squares with limsup ≤ 13√2/4

- **Source:** forum post #8879 by **donteatllamas**
  ([erdosproblems.com, 2026-09-07](https://www.erdosproblems.com/forum/thread/33#post-8879)),
  made "with the help of GPT", per the post.
  - The post links ("formalized here") to a PDF write-up. The repository
    [LeanMeanBean/erdos-33](https://github.com/LeanMeanBean/erdos-33) holds that PDF and its LaTeX
    source, and no Lean code.
  - The write-up is unsigned. No review is recorded in the thread, and the result is not (yet)
    on the problem page.
- **Claim:** there is A ⊆ ℕ such that every natural number m can be written m = n² + a with
  n ≥ 0 and a ∈ A, and limsup |A ∩ [1, N]| / √N ≤ 13√2/4 ≈ 4.596.
  - The write-up needs this only for large m; the Lean statement covers all m.
  - Previous bound: 2φ^{5/2} ≈ 6.66, by W. van Doorn (forum, 2025-08-12, as recorded on the
    problem page).
  - **The problem remains open:** the optimal constant is unknown.
- **Proved** (`RecentResults/Erdos33.lean`, namespace `Erdos33`):

  ```lean
  theorem Aset_basis : AdditiveBasisCondition Aset
  theorem Aset_limsup :
      atTop.limsup (fun N : ℕ => ((Aset ∩ Icc 1 N).ncard : EReal) / (√N : EReal))
        ≤ ((13 * √2 / 4 : ℝ) : EReal)
  theorem erdos_33_le_13_sqrt2_div_4 :
      ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N =>
      (A.1 ∩ Icc 1 N).ncard / (√N : EReal)) ≤ ((13 * √2 / 4 : ℝ) : EReal)
  ```

  - `Aset` is the explicit construction of the write-up.
  - A plain real-number ε-form is also proved, in the bridge (`erdos33_exists_le_eps`):
    `∃ A, IsAddComplSquares A ∧ ∀ ε > 0, ∀ᶠ N in atTop, |A ∩ [1,N]| ≤ (13√2/4 + ε)·√N`.
- **`vanDoorn` variant:** `erdos_33.variants.vanDoorn` is formal-conjectures' statement,
  verbatim apart from its attribute. It is **derived** from the 13√2/4 bound. Van Doorn's own
  construction and his all-N inequality are not formalized.
- **Self-written definitions:** none for the statement. `AdditiveBasisCondition` and the
  statement shape are verbatim from formal-conjectures (`FormalConjectures/ErdosProblems/33.lean`
  @ `2a315101`), where they had no proof.
- **Fidelity:** all seven blind statements are proved.
  - Independent of formal-conjectures' shape: `IsAddComplSquares`, real-division limsup, the
    ε-form and the bound on the infimum.
  - Two reuse formal-conjectures' shape, and are therefore weaker evidence of fidelity.
- **Not verified:**
  - only the upper bound for this construction is verified;
  - the optimal constant is not addressed;
  - a different construction with limsup **9/2** was recorded on 2026-10-19 by Plasma AI
    ([plasma-ai/erdos @ bdb2d5d5ba](https://github.com/plasma-ai/erdos/blob/bdb2d5d5ba/wiki/problems/additive_bases/E0033/claims/2026_10_19_plasma_ai.md),
    status "claimed"). It has no Lean proof and is **not** checked here.

## 4. Park — Fibonacci numbers are not an additive uniqueness set for multiplicative functions

- **Source:** Poo-Sung Park, *The Fibonacci numbers are not an additive uniqueness set for
  multiplicative functions*, [arXiv:2609.08137](https://arxiv.org/abs/2609.08137) (v1 only,
  2026-09-08; comments: "AI-assisted"). Not peer-reviewed.
  - **AI declaration (Section 6):** the example was found in an interactive ChatGPT session
    (OpenAI GPT-6 Astra), which proposed the switching construction and ran the search.
  - The paper answers a question of C. A. Spiro (J. Number Theory 42 (1992)).
- **Claim:** there is a positive-integer-valued multiplicative f ≠ id with
  f(F_n + F_m) = f(F_n) + f(F_m) for all n, m ≥ 1.
  - It is f(N) = N·(q/p)^{[p∣N] − [q∣N]}, with p = 557 and q = 2417, where F₃₁ = p·q.
  - In particular f(557) = 2417 and f(2417) = 557. It is **not** an exponent swap:
    f(557²) = 557·2417.
  - The paper also gives a general criterion (Theorem 4.1) and five further prime pairs
    (Section 5).
- **Proved** (`RecentResults/ParkFibonacci.lean`):

  ```lean
  theorem not_isAUSet_posFib : ¬ IsAUSet posFib
  theorem exists_nat_counterexample :
      ∃ f : ArithmeticFunction ℕ, f.IsMultiplicative ∧ (∀ n, 0 < n → 0 < f n) ∧
        (∀ n m, 1 ≤ n → 1 ≤ m →
          f (Nat.fib n + Nat.fib m) = f (Nat.fib n) + f (Nat.fib m)) ∧
        f 557 = 2417 ∧ f 2417 = 557
  ```

- **Also proved in the module:**
  - Theorem 4.1's divisibility equivalence (`FibCrit.criterion`);
  - the multiplicativity and fixing parts of Proposition 3.1;
  - the divisibility equivalences for the five other table rows.
- **Proved only in the bridge:**
  - the remaining clauses of Proposition 3.1 (positive integer values for t = q/p; "not the
    identity" for t ≠ 1);
  - the counterexample conclusion of Theorem 4.1;
  - the Pisano periods 4r;
  - the rank-of-apparition reformulation.
- **Self-written definitions:**
  - `IsAUSet`: complex-valued multiplicative arithmetic functions, additive on E, conclusion
    `f n = n` for `n > 0`;
  - `posFib`;
  - `FibCrit.Hyp ℓ r`: r ≥ 5 odd, ℓ > 2, ℓ ∤ F_k for 0 < k < r, ℓ ∣ F_r. The bridge proves it
    equivalent to "rank of apparition = r";
  - `FibCrit.switchFun`: the paper's f_t, proved equal to the blind version.

  formal-conjectures has no statement of this question.
- **Fidelity:** all blind statements are proved. Our versions are slightly more general: n, m ≥ 0
  in the key lemma, and no p ≠ q hypothesis.
- **Two independent proofs of the headline result:**
  - via `FibSpiro.key`: Pisano periodicity modulo F₃₁ plus a `decide +kernel` over
    124 × 124 residue pairs;
  - via Theorem 4.1 (`not_isAUSet_posFib'`), with only small checks.
- **Not formalized:**
  - the introduction's remarks that every admissible f fixes F_n and L_n;
  - the remark that disjoint pairs can be switched simultaneously;
  - the explicit factorizations of F₄₁ and F₅₅.
- **Caveat:** table row r = 61 uses `maxRecDepth 200000` for a primality certificate
  (555003497). It is sound but may be fragile across toolchains.

## 5. Erdős problem #64: diameter 2 (Carr) and a partial diameter-3 result (minimum degree ≥ 4)

- **Sources.**
  - (a) Avery Carr, *Cycles of Length 4 or 8 in Graphs with Diameter 2 and Minimum Degree at
    Least 3*, [arXiv:2508.19302](https://arxiv.org/abs/2508.19302) (v4, 2026-01-30), Theorem 1.1.
    The arXiv comments say it is accepted in the Bull. Inst. Combin. Appl.
  - (b) [Proof claim #383](https://www.erdosproblems.com/forum/thread/64/proof-claims) on
    erdosproblems.com (2026-10-02), claimed by Murat Can Temeller "using Claude Opus 5.5
    (Anthropic)". The proof is published in GitHub issue
    [zey9310/zey9310-math#1](https://github.com/zey9310/zey9310-math/issues/1). The issue states
    that the theorem, proof, code and computations were produced by Claude Opus 5.5 in a session
    directed by @zey9310, and that it had not yet been independently verified by a human expert.
- **Claims.**
  - (a) Every finite graph with diameter 2 and minimum degree ≥ 3 has a cycle of length 4 or 8.
  - (b) Every finite graph with minimum degree ≥ 4 and diameter ≤ 3 has a cycle of length 4
    or 8.
- **Proved** (`RecentResults/Erdos64SmallDiameter.lean`), with `[Fintype V] [DecidableRel G.Adj]`:

  ```lean
  theorem carr_diam2 (hδ : 3 ≤ G.minDegree) (hd : G.ediam ≤ 2) :
      ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ (c.length = 4 ∨ c.length = 8)
  theorem diam3_minDegree4 (hδ : 4 ≤ G.minDegree) (hd : G.ediam ≤ 3) :
      ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ (c.length = 4 ∨ c.length = 8)
  ```

  The corollaries `erdos_64_of_diam2` and `erdos_64_of_diam3` restate these in the conclusion
  shape of formal-conjectures' `erdos_64`: a cycle of length 2^k with k ≥ 2.
- **Scope.** Erdős #64 is settled here only for diameter ≤ 2. Result (b) needs minimum degree
  ≥ 4. Diameter-3 graphs with vertices of degree 3 remain open; the issue lists this as "the
  remaining gap for diameter 3".
- **Self-written definitions:** none; only Mathlib's `minDegree`, `ediam` and `Walk.IsCycle`.
  - `ediam` (in ℕ∞) is ⊤ for disconnected graphs, so `ediam ≤ 2` forces connectedness.
  - `ediam ≤ 2` weakens Carr's `diam = 2`. It only adds complete graphs; this is proved in the
    bridge.
- **Fidelity:**
  - Both blind statements are proved.
  - The converse implications are also proved (`carr_diam2_of_blind`,
    `diam3_minDegree4_of_blind`).
  - The two conclusion forms are proved equivalent.
- **Not verified:** the issue's computer searches. Its main search is implied by theorem (b);
  the degree 3–4 search and the positive-control counts are not. Every theorem the sources state
  is verified.
- **Proof route.** The Lean proof of (a) splits on whether the base edge lies in a triangle.
  Carr's Claim 2.2 and Subcases 2A/2B are therefore not formalized as written; those triangle
  configurations are covered by the triangle case.

## 6. Xu — the strengthened Bukh–van Hintum–Keevash conjecture

- **Source:** Zixiang Xu, [arXiv:2605.10771](https://arxiv.org/abs/2605.10771) (v1 only,
  2026-05-11). Not peer-reviewed. The paper declares no AI assistance.
- **Prior Lean work.** B. Alexeev had already formalized and proved Bukh's question
  |A| + |B| ≥ 2n over ℝⁿ for an arbitrary basis.
  - Where: [plby/lean-proofs](https://github.com/plby/lean-proofs), 2026-07-27. Statement in
    `src/latest/ComparatorChallenges/BorisBukh/BasisSubset.lean`, proof in
    `src/latest/BorisBukh/BasisSubset.lean`.
  - Credits: formal proof with Codex; informal proof credited to ChatGPT Pro in plby's metadata.
  - This sum form implies Theorem 1.1 for t ≤ 1, and BvHK Conjecture 13.
  - Bukh's [problem page](https://borisbukh.org/problems.html) notes that the sum-form question
    was first solved, unpublished, by ChatGPT Pro 5.4 (2026-04-08), and that the first public
    solution is Xu's.
- **Claim (Theorem 1.1):** if S is a basis of ℝⁿ, A, B ⊆ ℝⁿ with S + S ⊆ A + B, and
  |A| ≤ n − t (0 ≤ t ≤ n − 1), then |B| ≥ n + C(t+1, 2).
  - The bound is sharp for every basis and every t (construction after Theorem 1.1).
  - Corollary 1.2 is the ℚⁿ vector model, i.e. the BvHK extension of Conjecture 13.
- **New in this formalization:**
  - the quadratic bound for t ≥ 2;
  - the sharpness construction;
  - Corollary 1.2 in refined form;
  - Lemma 2.2;
  - the change-of-domain consequence (proved in the bridge).
- **Proved** (`RecentResults/XuAdditiveBases.lean`, namespace `XuBvHK`):

  ```lean
  theorem theorem_1_1 (n : ℕ) (S : Module.Basis (Fin n) ℝ (Fin n → ℝ)) (A B : Set (Fin n → ℝ))
      (hcontains : (Set.range S + Set.range S : Set (Fin n → ℝ)) ⊆ A + B)
      (t : ℕ) (ht : t < n) (hA : A.encard ≤ ((n - t : ℕ) : ℕ∞)) :
      ((n + (t + 1).choose 2 : ℕ) : ℕ∞) ≤ B.encard
  theorem theorem_1_1_sharp (n : ℕ) (S : Module.Basis (Fin n) ℝ (Fin n → ℝ)) (t : ℕ) (ht : t < n) :
      ∃ A B : Set (Fin n → ℝ), (Set.range S + Set.range S : Set (Fin n → ℝ)) ⊆ A + B ∧
        A.encard = ((n - t : ℕ) : ℕ∞) ∧ B.encard = ((n + (t + 1).choose 2 : ℕ) : ℕ∞)
  theorem corollary_1_2 (n : ℕ) (A B : Set (Fin n → ℚ))
      (hcontains : ∀ i j : Fin n, i ≤ j → (Pi.single i 1 + Pi.single j 1 : Fin n → ℚ) ∈ A + B)
      (t : ℕ) (ht : t < n) (hA : A.encard ≤ ((n - t : ℕ) : ℕ∞)) :
      ((n + (t + 1).choose 2 : ℕ) : ℕ∞) ≤ B.encard
  ```

- **Self-written definitions:** none beyond Mathlib (`Module.Basis`, `Set.encard`, pointwise `+`).
- **Fidelity:** all eight blind statements are proved.
  - These include the set-basis formulation, BvHK Conjecture 13 and its extension, Lemma 2.2 in
    the paper's general form, and the change-of-domain remark.
  - plby's sum-form statement is re-derived verbatim from Theorem 1.1. As explained above,
    `bukh_question_sum` and `bvhk_conjecture_13` were already covered by plby's proof.
- **Not verified:** nothing that the paper claims.
- **Proof route:** `XuBvHK.forest_colour_bound` uses a rank–nullity argument in place of the
  paper's forest-contraction count.

---

## Prior art (searches of 2026-10-21)

**What we searched, and what we found.**

We found no public Lean formalization of the six results above, with two exceptions:

- the sum form of result 6, proved by plby (see section 6);
- atlas-lean's unproved `theorem_wanted` statements for result 2.

Searched:

- Mathlib and the titles of all 44,463 mathlib4 PRs;
- google-deepmind/formal-conjectures;
- plby/lean-proofs and openai/math;
- about 550 public Lean repositories about Erdős problems;
- the Palomar registry;
- facebookresearch/atlas-lean;
- GitHub code search and web search.

Other Lean work on Erdős #64 that we know of does not cover the diameter cases. The proof
claim's "formalisation" link points to the issue, which contains no Lean.

**Known gap.** Our copy of the public Lean Zulip archive ends on 2026-09-25, and it could not be
searched after that date. That cutoff falls:

- **before** result 1 appeared (2026-09-29);
- 5 days after result 2 (2026-09-20);
- 17 days after result 4 (2026-09-08).

A logged-in Zulip search should be done before any announcement.
