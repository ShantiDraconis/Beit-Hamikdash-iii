import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# I Ching: trigramas, hexagramas e aritmética binária

Esta é uma ponte histórica real entre um sistema simbólico e a computação. Em 1701 o
jesuíta Joachim Bouvet enviou a Leibniz o diagrama dos hexagramas na ordem de Fu Xi.
Leibniz reconheceu nele a contagem binária que ele mesmo vinha descrevendo e publicou
a *Explication de l'Arithmétique Binaire* (1703).

Convenção: `true` é a linha contínua (yang), `false` a quebrada (yin);
a linha `i` vale `2^i`, de baixo para cima.
-/

namespace BeitHamikdash.Tradicoes.IChing

abbrev Linha := Bool
abbrev Trigrama := Fin 3 → Linha
abbrev Hexagrama := Fin 6 → Linha

theorem card_trigramas : Fintype.card Trigrama = 8 := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; rfl

theorem card_hexagramas : Fintype.card Hexagrama = 64 := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; rfl

/-- Todo hexagrama é um trigrama inferior sob um trigrama superior. -/
def emTrigramas : Hexagrama ≃ Trigrama × Trigrama :=
  (Equiv.arrowCongr (finSumFinEquiv (m := 3) (n := 3)) (Equiv.refl Bool)).symm.trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

/-- A leitura de Leibniz: o hexagrama como número binário. -/
def valorBinario (h : Hexagrama) : ℕ := ∑ i, if h i then 2 ^ (i : ℕ) else 0

/-- O hexagrama de um número de 0 a 63: a linha `i` é o `i`-ésimo bit. -/
def deNumero (n : Fin 64) : Hexagrama := fun i => n.val.testBit i

/-- Ler em binário o hexagrama de `n` devolve `n` (verificado para os 64 números). -/
theorem valorBinario_deNumero : ∀ n : Fin 64, valorBinario (deNumero n) = n := by
  decide +kernel

theorem deNumero_injetivo : Function.Injective deNumero := fun a b h =>
  Fin.ext <| by
    have := congrArg valorBinario h
    rwa [valorBinario_deNumero, valorBinario_deNumero] at this

/-- Os 64 números de 0 a 63 dão exatamente os 64 hexagramas. -/
theorem deNumero_bijetivo : Function.Bijective deNumero :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨deNumero_injetivo, by rw [Fintype.card_fin, card_hexagramas]⟩

/-- Os 64 hexagramas são exatamente os números de 0 a 63 escritos em binário. -/
noncomputable def comoNumero : Hexagrama ≃ Fin 64 :=
  (Equiv.ofBijective deNumero deNumero_bijetivo).symm

theorem valorBinario_eq (h : Hexagrama) : valorBinario h = comoNumero h := by
  have e := (Equiv.ofBijective deNumero deNumero_bijetivo).apply_symm_apply h
  conv_lhs => rw [← e]
  exact valorBinario_deNumero _

theorem valorBinario_lt (h : Hexagrama) : valorBinario h < 64 := by
  rw [valorBinario_eq]; exact (comoNumero h).isLt

/-- Hexagramas diferentes dão números diferentes. -/
theorem valorBinario_injetivo : Function.Injective valorBinario := fun a b e => by
  rw [valorBinario_eq, valorBinario_eq] at e
  exact comoNumero.injective (Fin.ext e)

end BeitHamikdash.Tradicoes.IChing
