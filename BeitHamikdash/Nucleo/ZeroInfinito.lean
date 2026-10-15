import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Zero, infinito e o defeito `D`

A proposta: `D = 0/∞`, `0/D = ∞` e `D/0 = ∞` ao mesmo tempo. Este arquivo mostra
onde isso falha e o que sobra de verdadeiro.

* Nos reais do Lean, dividir por zero dá 0 por convenção (`D / 0 = 0`). Então
  `D/0 = ∞` nem é escrevível em `ℝ`.
* Nos reais estendidos não negativos `[0, ∞]`, `0 / D = 0` para todo `D`. Logo
  `0/D = ∞` é impossível, e as três relações não valem juntas.
* O que é verdadeiro é a versão com limites: para uma sequência positiva,
  `D_N → 0` **se e somente se** `1/D_N → +∞`. Isso é uma reformulação. Não ajuda a
  provar que o defeito de Nyman–Beurling vai a zero.
* A forma `0/0` não tem valor: `x²/x`, `x/x` e `x/x²` têm numerador e denominador
  indo a 0, e os quocientes vão a 0, 1 e +∞.
-/

namespace BeitHamikdash.Nucleo

open Filter Topology

/-- Nos reais do Lean, `D / 0 = 0` (convenção). -/
theorem dividir_por_zero_em_R (D : ℝ) : D / 0 = 0 := div_zero D

/-- Em `[0, ∞]`, zero dividido por qualquer coisa é zero, nunca `∞`. -/
theorem zero_div_nunca_infinito (D : ENNReal) : 0 / D ≠ ⊤ := by
  rw [div_eq_mul_inv, zero_mul]
  exact ENNReal.zero_ne_top

/-- **As três relações não valem juntas em `[0, ∞]`.** -/
theorem tres_relacoes_incompativeis :
    ¬ ∃ D : ENNReal, D = 0 / ⊤ ∧ 0 / D = ⊤ ∧ D / 0 = ⊤ :=
  fun ⟨D, _, h, _⟩ => zero_div_nunca_infinito D h

/-- **Dualidade anulação ↔ divergência.** Para uma sequência positiva,
`D_N → 0` exatamente quando `1/D_N → +∞`. -/
theorem tende_a_zero_iff_inverso_diverge (D : ℕ → ℝ) (hpos : ∀ n, 0 < D n) :
    Tendsto D atTop (𝓝 0) ↔ Tendsto (fun n => (D n)⁻¹) atTop atTop := by
  constructor
  · intro h
    have h' : Tendsto D atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨h, Eventually.of_forall hpos⟩
    exact tendsto_inv_nhdsGT_zero.comp h'
  · intro h
    have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp h
    simpa [Function.comp_def, inv_inv] using this

/-- **`0/0` é indeterminado.** Três quocientes com numerador e denominador indo a 0
(quando `x → 0⁺`) têm limites 0, 1 e +∞. -/
theorem zero_sobre_zero_indeterminado :
    Tendsto (fun x : ℝ => x ^ 2 / x) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun x : ℝ => x / x) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun x : ℝ => x / x ^ 2) (𝓝[>] 0) atTop := by
  have hpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ≠ 0 :=
    eventually_nhdsWithin_of_forall fun x hx => (Set.mem_Ioi.mp hx).ne'
  refine ⟨?_, ?_, ?_⟩
  · have hid : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds tendsto_id
    refine hid.congr' (hpos.mono fun x hx => ?_)
    show x = x ^ 2 / x
    rw [pow_two, mul_div_assoc, div_self hx, mul_one]
  · exact tendsto_const_nhds.congr' (hpos.mono fun x hx => (div_self hx).symm)
  · refine tendsto_inv_nhdsGT_zero.congr' (hpos.mono fun x hx => ?_)
    show x⁻¹ = x / x ^ 2
    rw [pow_two, ← div_div, div_self hx, one_div]

end BeitHamikdash.Nucleo
