import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Uma representação das três letras mães por matrizes 2×2

As matrizes abaixo são uma **escolha** feita neste projeto, não uma atribuição
histórica. O *Sefer Yetzirah* associa א, מ e ש ao ar, à água e ao fogo, e não
fala em matrizes. Outras escolhas dariam outras relações.

Com esta escolha, as três matrizes satisfazem as relações dos **quatérnios
divididos** (*split-quaternions*): Alef ao quadrado é −1, Mem e Shin ao quadrado são +1,
e Alef · Mem = Shin. Os comutadores fecham: [א, מ] = 2ש, [מ, ש] = −2א, [ש, א] = 2מ.
-/

namespace BeitHamikdash.Cabala

abbrev M2 := Matrix (Fin 2) (Fin 2) ℤ

/-- Rotação de 90°. -/
def tAlef : M2 := !![0, -1; 1, 0]
/-- Reflexão diagonal. -/
def tMem : M2 := !![1, 0; 0, -1]
/-- Troca das coordenadas. -/
def tShin : M2 := !![0, 1; 1, 0]

theorem alef_quadrado : tAlef * tAlef = -1 := by decide
theorem mem_quadrado : tMem * tMem = 1 := by decide
theorem shin_quadrado : tShin * tShin = 1 := by decide

theorem alef_mem : tAlef * tMem = tShin := by decide
theorem mem_alef : tMem * tAlef = -tShin := by decide

theorem comutador_alef_mem : tAlef * tMem - tMem * tAlef = 2 • tShin := by decide
theorem comutador_mem_shin : tMem * tShin - tShin * tMem = -(2 • tAlef) := by decide
theorem comutador_shin_alef : tShin * tAlef - tAlef * tShin = 2 • tMem := by decide

/-- As três anticomutam duas a duas. -/
theorem anticomutam :
    tAlef * tMem + tMem * tAlef = 0 ∧ tMem * tShin + tShin * tMem = 0 ∧
    tShin * tAlef + tAlef * tShin = 0 := by
  decide

/-- A combinação `a·1 + b·א + c·מ + d·ש`. -/
def combinacao (a b c d : ℤ) : M2 := !![a, 0; 0, a] + b • tAlef + c • tMem + d • tShin

/-- Explicitamente: `!![a + c, d − b; b + d, a − c]`. -/
theorem combinacao_eq (a b c d : ℤ) :
    combinacao a b c d = !![a + c, d - b; b + d, a - c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [combinacao, tAlef, tMem, tShin] <;> ring

/-- O determinante é `a² + b² − c² − d²`, a norma dos quatérnios divididos. -/
theorem det_combinacao (a b c d : ℤ) :
    (combinacao a b c d).det = a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2 := by
  rw [combinacao_eq, Matrix.det_fin_two_of]
  ring

end BeitHamikdash.Cabala
