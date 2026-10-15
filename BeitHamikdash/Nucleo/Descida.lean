import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Init

/-!
# Correção por descida finita

Se uma correção `C` diminui estritamente um defeito natural sempre que ele é
positivo, então, a partir de qualquer estado, o defeito chega a zero em no máximo
`e x` passos.

Este é um teorema geral. Não depende de nenhuma tradição. Ele é instanciado com o
I Ching em `Tradicoes/IChingCorrecao.lean`.
-/

namespace BeitHamikdash.Nucleo

variable {X : Type*}

theorem correcao_finita (e : X → ℕ) (C : X → X)
    (h : ∀ x, 0 < e x → e (C x) < e x) (x : X) :
    ∃ n ≤ e x, e (C^[n] x) = 0 := by
  suffices aux : ∀ k, ∀ y, e y = k → ∃ n ≤ k, e (C^[n] y) = 0 from aux _ x rfl
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih y hy
  rcases Nat.eq_zero_or_pos (e y) with hz | hp
  · exact ⟨0, Nat.zero_le _, hz⟩
  · have hlt : e (C y) < k := by rw [← hy]; exact h y hp
    obtain ⟨n, hn, hzero⟩ := ih (e (C y)) hlt (C y) rfl
    exact ⟨n + 1, by omega, by rwa [Function.iterate_succ_apply]⟩

end BeitHamikdash.Nucleo
