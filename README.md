# Beit Hamikdash III — Terceiro Templo

A small, honestly-scoped Lean 4 + Mathlib library formalizing specific mathematical structures
inspired by comparative religious symbolism (starting with Kabbalah / Sefer Yetzirah).

**Status: research notebook, not a proof of anything beyond what is stated in each theorem.**
No theorem in this repository is claimed, or intended, to bridge to the Riemann Hypothesis, P
vs NP, Navier–Stokes, Yang–Mills, the Birch and Swinnerton-Dyer conjecture, the Hodge
conjecture, or Beal's conjecture. See `TerceiroTemplo.lean` for the exact status taxonomy this
library follows (`SYMBOLIC` / `FORMAL` / `PROVED` / `CERTIFIED` / `BRIDGE` / `OPEN_MATH`) and for
an explicit list of what is and is not proved here.

## What's here

- `TerceiroTemplo/Foundations/Invariants.lean` — generic lemmas about invariants preserved under
  transformations, and a generic positivity fact about sums of squared operator norms.
- `TerceiroTemplo/Traditions/SeferYetzirah.lean` — one specific, commonly published edge
  convention for the Kabbalistic Tree of Life (10 sephirot, 22 paths), formalized as a
  `SimpleGraph`, with a proof that it is connected and that its circuit rank is 13.

## CI

`.github/workflows/kernel.yml` installs Lean via `elan`, fetches the cached Mathlib build, runs
`lake build`, rejects any `sorry`/`admit`/custom `axiom` in the source, and audits that every
printed theorem's axiom footprint stays within `{propext, Classical.choice, Quot.sound}`.
