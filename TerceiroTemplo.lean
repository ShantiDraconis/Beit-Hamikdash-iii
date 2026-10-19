import TerceiroTemplo.Foundations.Invariants
import TerceiroTemplo.Traditions.SeferYetzirah

/-!
# Terceiro Templo — honest formal status

This library formalizes specific, named mathematical structures inspired by (but not claimed to
be *the* unique canonical form of) religious and symbolic traditions, following this status
taxonomy:

* `SYMBOLIC` — a religious, philosophical or interpretive structure, not yet given mathematical
  form here.
* `FORMAL` — a Lean definition that names one specific mathematical reading of a symbolic
  structure (there can be more than one legitimate reading; this library commits to exactly one,
  stated explicitly in each module).
* `PROVED` — a theorem derived from that definition, checked by the Lean kernel.
* `CERTIFIED` — `PROVED`, plus the kernel's `#print axioms` reports only
  `{propext, Classical.choice, Quot.sound}`, and the source contains no `sorry`/`admit`/custom
  `axiom`.
* `BRIDGE` — a proved implication from a structure in this library to a statement of one of the
  Millennium Prize problems (or Beal's conjecture). As of this file, **no such bridge exists**.
* `OPEN_MATH` — a mathematical obligation this library's `FORMAL` structures imply, but that no
  one has proved.

## What is actually in this library right now

* `TerceiroTemplo.pathQuadForm_nonneg` (`CERTIFIED`): for any finite family of continuous
  linear operators on a complex normed space, the sum of squared operator norms is
  nonnegative. True, and completely generic — it says nothing about any specific operator family
  being physically or religiously meaningful, and in particular it does **not** produce a
  spectral gap (that would need an extra inequality, not supplied here).
* `TerceiroTemplo.SeferYetzirah.circuitRank_eq_thirteen` (`CERTIFIED`): for one specific,
  commonly published 10-sephirot/22-path edge convention of the Kabbalistic Tree of Life, the
  graph is connected and its circuit rank (cycle-space dimension) is 13. True, and purely
  combinatorial — a fact about this graph, not a fact about any Millennium Prize problem.

## What is explicitly absent

There is no `BRIDGE` theorem anywhere in this library connecting the Tree of Life, Sefer
Yetzirah, or any other symbolic structure to the Riemann Hypothesis, P vs NP, Navier–Stokes,
Yang–Mills, the Birch and Swinnerton-Dyer conjecture, the Hodge conjecture, or Beal's conjecture.
The source material motivating this library said so explicitly, and nothing proved here changes
that: a graph invariant of a religious diagram is a fact about that diagram, not a step toward
any of those statements, unless and until someone actually proves an implication from one to the
other.
-/
