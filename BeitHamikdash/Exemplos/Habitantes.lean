import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Habitantes auxiliares da série "Terceiro Templo", verificados pelo kernel

Os textos "Habitantes preenchidos" e "Preenchimento integral" calculam vários
exemplos e terminam com "certificação pelo kernel: não realizada". Aqui os
cálculos que fazem sentido em Lean passam pelo kernel.

Todos são proposições **auxiliares** ou **instâncias particulares**. Nenhum deles
é, nem implica, um dos sete enunciados.
-/

namespace BeitHamikdash.Exemplos

open Matrix

/-! ## H2: operadores que não comutam -/

def opT (x : ℚ) : ℚ := x / 2
def opU (x : ℚ) : ℚ := x + 3

theorem H2_nao_comutam : opU (opT 8) = 7 ∧ opT (opU 8) = 11 / 2 := by
  norm_num [opT, opU]

/-! ## H6: certificado de SAT para uma fórmula concreta -/

/-- `F = (x₁ ∨ x₂) ∧ (¬x₁ ∨ x₃)`. -/
def F (x₁ x₂ x₃ : Bool) : Bool := (x₁ || x₂) && (!x₁ || x₃)

/-- `v = (1, 0, 1)` satisfaz `F`, logo `F ∈ SAT`. Isso não diz nada sobre `SAT ∉ P`. -/
theorem H6_certificado : F true false true = true := rfl

/-- `#SAT(F) = 4` das 8 atribuições. -/
theorem H6_contagem :
    (Finset.univ.filter fun v : Bool × Bool × Bool => F v.1 v.2.1 v.2.2 = true).card = 4 := by
  decide

/-! ## H7: cota auxiliar do modelo Navier–Stokes -/

/-- Se `X ≤ c_B·X + c_T·X + C` com `c_B + c_T < 1`, então `X ≤ C / (1 − c_B − c_T)`. -/
theorem H7_cota {cB cT C X : ℝ} (hδ : cB + cT < 1) (h : X ≤ cB * X + cT * X + C) :
    X ≤ C / (1 - cB - cT) := by
  rw [le_div_iff₀ (by linarith)]
  have : X * (1 - cB - cT) = X - cB * X - cT * X := by ring
  linarith

/-- Com `c_B = 1/4`, `c_T = 1/3`, `C = 1/5`: a cota é `12/25`, e `X = 12/25` a satura. -/
theorem H7_valores :
    (1 / 5 : ℝ) / (1 - 1 / 4 - 1 / 3) = 12 / 25 ∧
    (1 / 4 : ℝ) * (12 / 25) + 1 / 3 * (12 / 25) + 1 / 5 = 12 / 25 := by
  norm_num

/-! ## H9: matriz auxiliar do modelo BSD -/

/-- `2x² + 2xy + 3y² > 0` para `(x, y) ≠ 0`: a matriz `!![2, 1; 1, 3]` é positiva definida. -/
theorem H9_positiva (x y : ℚ) (h : (x, y) ≠ (0, 0)) : 0 < 2 * x ^ 2 + 2 * x * y + 3 * y ^ 2 := by
  by_cases hy : y = 0
  · subst hy
    have hx : x ≠ 0 := fun hx => h (by simp [hx])
    have := mul_self_pos.mpr hx
    nlinarith
  · have := mul_self_pos.mpr hy
    nlinarith [sq_nonneg (2 * x + y)]

theorem H9_det : (!![2, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℤ).det = 5 := by
  rw [Matrix.det_fin_two]
  rfl

/-! ## H10: representação linear do modelo Hodge -/

def MH : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, -1]

theorem H10_representacao : MH *ᵥ ![2, 1] = ![3, 1] := by decide
theorem H10_quadrado : MH * MH = 2 • 1 := by decide

/-! ## H11: um exemplo da equação de Beal, com fator comum -/

theorem H11_exemplo : 2 ^ 3 + 2 ^ 3 = 2 ^ 4 ∧ Nat.gcd (Nat.gcd 2 2) 2 = 2 := by decide

/-! ## Modelo de Gram (exemplo de brinquedo, não o critério de Nyman–Beurling) -/

def G : Matrix (Fin 2) (Fin 2) ℚ := !![2, 1; 1, 2]
def b : Fin 2 → ℚ := ![1 / 2, 1 / 3]

theorem G_inv : G⁻¹ = (1 / 3 : ℚ) • !![2, -1; -1, 2] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [G, Matrix.mul_apply, Fin.sum_univ_two]

/-- `D = 1 − bᵀ G⁻¹ b = 47/54`. -/
theorem defeito_gram : 1 - dotProduct b (G⁻¹ *ᵥ b) = 47 / 54 := by
  rw [G_inv]
  norm_num [b, dotProduct, mulVec, Fin.sum_univ_two]

end BeitHamikdash.Exemplos
