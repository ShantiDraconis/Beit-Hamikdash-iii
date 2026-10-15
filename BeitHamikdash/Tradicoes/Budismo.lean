import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Iterate

/-!
# Os 12 elos da originação dependente (*pratītyasamutpāda*)

O ciclo do *saṃsāra* é descrito como 12 elos em que cada um condiciona o seguinte e o
último volta ao primeiro. Formalmente isso é uma permutação cíclica de período 12.
-/

namespace BeitHamikdash.Tradicoes.Budismo

inductive Nidana
  | avidya       -- ignorância
  | samskara     -- formações
  | vijnana      -- consciência
  | namarupa     -- nome e forma
  | shadayatana  -- seis bases
  | sparsha      -- contato
  | vedana       -- sensação
  | trishna      -- sede
  | upadana      -- apego
  | bhava        -- existência
  | jati         -- nascimento
  | jaramarana   -- velhice e morte
  deriving DecidableEq, Repr, Fintype

namespace Nidana

theorem card_eq : Fintype.card Nidana = 12 := by decide

/-- Cada elo condiciona o seguinte; velhice e morte reconduzem à ignorância. -/
def proximo : Nidana → Nidana
  | avidya => samskara | samskara => vijnana | vijnana => namarupa
  | namarupa => shadayatana | shadayatana => sparsha | sparsha => vedana
  | vedana => trishna | trishna => upadana | upadana => bhava
  | bhava => jati | jati => jaramarana | jaramarana => avidya

/-- Doze passos reconduzem qualquer elo a si mesmo. -/
theorem ciclo_12 : ∀ n, proximo^[12] n = n := by decide

/-- E nenhum número menor de passos faz isso: o período é exatamente 12. -/
theorem periodo_minimo : ∀ k : Fin 12, 0 < (k : ℕ) → ∀ n, proximo^[k] n ≠ n := by
  decide

end Nidana

end BeitHamikdash.Tradicoes.Budismo
