import Mathlib.Data.Fintype.Pi
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

theorem card_trigramas : Fintype.card Trigrama = 8 := by simp
theorem card_hexagramas : Fintype.card Hexagrama = 64 := by simp

/-- Todo hexagrama é um trigrama inferior sob um trigrama superior. -/
def emTrigramas : Hexagrama ≃ Trigrama × Trigrama :=
  (Equiv.arrowCongr (finSumFinEquiv (m := 3) (n := 3)) (Equiv.refl Bool)).symm.trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

/-- A leitura de Leibniz: o hexagrama como número binário. -/
def valorBinario (h : Hexagrama) : ℕ := ∑ i, if h i then 2 ^ (i : ℕ) else 0

theorem valorBinario_lt (h : Hexagrama) : valorBinario h < 64 := by
  revert h; decide

/-- Hexagramas diferentes dão números diferentes. -/
theorem valorBinario_injetivo : Function.Injective valorBinario := by
  decide

/-- Os 64 hexagramas são exatamente os números de 0 a 63 escritos em binário. -/
noncomputable def comoNumero : Hexagrama ≃ Fin 64 :=
  Equiv.ofBijective (fun h => ⟨valorBinario h, valorBinario_lt h⟩) <|
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun _ _ e => valorBinario_injetivo (congrArg Fin.val e), by simp⟩

end BeitHamikdash.Tradicoes.IChing
