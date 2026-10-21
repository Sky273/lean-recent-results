# RecentResults — machine-checked verification of recent mathematical results

This repository contains Lean 4 / Mathlib verifications of six research results from 2025–2026.
Most of them are preprints (arXiv) or posts on erdosproblems.com, and several were obtained with
the help of AI systems. In our searches of 21 October 2026 we found no public Lean formalization
of any of them, apart from the partial cases reported in [AUDIT.md](AUDIT.md). That file also
explains the limits of those searches.

| File | Result | Source | Origin of the result |
|---|---|---|---|
| `NoelListTotalColouring.lean` | The List Total Colouring Conjecture is false (a cubic graph on 20 vertices) | [arXiv:2609.38417](https://arxiv.org/abs/2609.38417) | J. A. Noel; counterexample and drafts by ChatGPT 6 Astra Ultra, checked and rewritten by the author |
| `NoelPartialListColouring.lean` | The Albertson–Grossman–Haas partial list colouring conjecture is false (14 vertices) | [arXiv:2609.23291](https://arxiv.org/abs/2609.23291) | J. A. Noel; counterexample and proof found by ChatGPT 6 Astra Ultra, paper written and checked by the author |
| `Erdos33.lean` | Erdős #33: an additive complement of the squares with limsup \|A∩[1,N]\|/√N ≤ 13√2/4 (the problem remains open) | [erdosproblems.com forum, post #8879](https://www.erdosproblems.com/forum/thread/33#post-8879) | forum user donteatllamas, "with the help of GPT" |
| `ParkFibonacci.lean` | The Fibonacci numbers are not an additive uniqueness set for multiplicative functions (question of Spiro, 1992) | [arXiv:2609.08137](https://arxiv.org/abs/2609.08137) | P.-S. Park, declared AI-assisted (ChatGPT) |
| `Erdos64SmallDiameter.lean` | Erdős #64: a cycle of length 4 or 8 in graphs of diameter ≤ 2 with minimum degree ≥ 3 (Carr), and of diameter ≤ 3 with minimum degree ≥ 4 (partial: diameter 3 with degree-3 vertices remains open) | [arXiv:2508.19302](https://arxiv.org/abs/2508.19302); [proof claim #383](https://www.erdosproblems.com/forum/thread/64/proof-claims) and [GitHub issue](https://github.com/zey9310/zey9310-math/issues/1) | A. Carr (diameter 2); proof produced by Claude Opus 5.5, claimed by M. C. Temeller (diameter 3) |
| `XuAdditiveBases.lean` | The strengthened Bukh–van Hintum–Keevash conjecture on additive bases, with sharpness | [arXiv:2605.10771](https://arxiv.org/abs/2605.10771) | Z. Xu (no AI assistance declared). The weaker sum form had already been formalized by B. Alexeev ([plby/lean-proofs](https://github.com/plby/lean-proofs)). |

**Verification.**

- **Comparator:** for each result, a statement-only challenge file (`Challenges/`, importing
  only Mathlib) and a config (`comparator/`). `lake comparator --paranoid` checks, in CI and in
  a sandbox, that our proofs establish exactly these statements with the standard axioms only.
  It also checks them with the external kernels bundled with Lean (nanoda, con-leche, con-ron).
- No `sorry`, `admit` or `native_decide`.
- `#print axioms` on the main theorems reports only `propext`, `Classical.choice` and
  `Quot.sound`.
- Every module, including the fidelity bridges, passes `leanchecker`.
- Project metadata follows the [formalization.yaml](formalization.yaml) standard (v0.4).

**Statement fidelity.** Lean guarantees the proofs, but not that a formal statement says what
the paper says. To check that independently:

- `Fidelity/Blind/` holds statements written "blind" from the sources, by an agent that had not
  seen our files;
- `Fidelity/` proves those statements from ours;
- [AUDIT.md](AUDIT.md) gives, for each result, the source's claim, the Lean statement, the
  self-written definitions and what is **not** verified. A human review of the statements should
  take a few minutes per result.

**Scope, in short.**

- **Noel (list total colouring):** the bound χ''_ℓ ≤ 5, which the paper takes from a 1998
  theorem, is not formalized. The refutation of the conjecture does not need it.
- **Erdős #33:** only the bound 13√2/4 for an explicit construction is verified, and the optimal
  constant remains open. A different construction with limsup 9/2, announced by Plasma AI on
  2026-10-19, is not checked here.
- **Erdős #64:** the diameter-3 result assumes minimum degree ≥ 4.

**How this was made (transparency).** This work was produced entirely by an AI system (Claude,
Anthropic), in a multi-agent process:

- prior-art search;
- writing statements and proofs;
- adversarial checking;
- blind fidelity checks;
- a referee-style review before publication.

It is published by Luc Moreau, a computer scientist, not a mathematician. Corrections and
comments are welcome through GitHub issues. The working log, in French, is in
[JOURNAL.md](JOURNAL.md).

## Build and check

```bash
lake exe cache get
lake build
```

Check one result with Comparator (Linux, requires `bubblewrap`):

```bash
lake comparator --config comparator/Erdos64SmallDiameter.json --paranoid
```

Replay the kernel checker, one module per invocation:

```bash
for m in RecentResults.NoelListTotalColouring RecentResults.NoelPartialListColouring RecentResults.Erdos33 RecentResults.ParkFibonacci RecentResults.Erdos64SmallDiameter RecentResults.XuAdditiveBases Fidelity.NoelListTotalColouring Fidelity.NoelPartialListColouring Fidelity.Erdos33 Fidelity.ParkFibonacci Fidelity.Erdos64SmallDiameter Fidelity.XuAdditiveBases; do lake env leanchecker $m || echo "FAILED $m"; done
```

Toolchain: Lean `v4.36.0-rc1`, Mathlib `v4.36.0-rc1`.

## License

Apache License 2.0 (see [LICENSE](LICENSE)). Third-party excerpts and their licenses are listed
in [NOTICE](NOTICE).
