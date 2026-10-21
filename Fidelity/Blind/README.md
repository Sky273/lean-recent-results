# Blind statements

Each file here was written by an agent that had **not** seen this repository. It worked only from the cited source and Mathlib. Every statement has a `sorry` proof: these files are statements, not proofs.

They are **not** part of `lake build`. The corresponding `Fidelity/<Result>.lean` files copy these statements verbatim, with a script check, and prove them from the verified theorems in `RecentResults/`. Only the namespace changes, and the `sorry` proofs are replaced by real ones.

To check that a blind file compiles on its own:

    lake env lean Fidelity/Blind/<Result>.lean

The only warnings expected are `declaration uses 'sorry'`.
