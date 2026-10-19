import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Hipótese de Riemann

O enunciado é o do próprio Mathlib (`RiemannHypothesis`): todo zero não trivial de ζ,
diferente de 1, tem parte real 1/2.

**Status: OPEN_MATH.** Este arquivo não contém prova, e não deve conter nenhum
`theorem riemann : RiemannHypothesis` enquanto não houver uma prova completa
verificada pelo kernel.
-/

namespace BeitHamikdash.Milenio

/-- Alias em português para o enunciado oficial do Mathlib. -/
abbrev HipoteseDeRiemann : Prop := RiemannHypothesis

end BeitHamikdash.Milenio
