import BeitHamikdash.Tradicoes.IChing
import BeitHamikdash.Nucleo.Descida
import Mathlib.Data.Fin.VecNotation

/-!
# Correção de erros sobre hexagramas

O defeito de um hexagrama em relação a um alvo é a distância de Hamming: quantas
linhas diferem. A correção troca a primeira linha divergente, de baixo para cima.

Prova-se que cada correção reduz o defeito em exatamente 1, que defeito zero é
o próprio alvo e que qualquer hexagrama chega a qualquer alvo em no máximo 6 passos.
-/

namespace BeitHamikdash.Tradicoes.IChing

/-- Distância de Hamming até o alvo. -/
def defeito (alvo h : Hexagrama) : ℕ := (Finset.univ.filter fun i => h i ≠ alvo i).card

/-- Corrige a primeira linha (de baixo para cima) que difere do alvo. -/
def corrige (alvo h : Hexagrama) : Hexagrama :=
  match (List.finRange 6).find? (fun i => h i != alvo i) with
  | some i => Function.update h i (alvo i)
  | none => h

theorem defeito_eq_zero_iff (alvo h : Hexagrama) : defeito alvo h = 0 ↔ h = alvo := by
  simp [defeito, Finset.card_eq_zero, Finset.filter_eq_empty_iff, funext_iff]

theorem defeito_le_seis (alvo h : Hexagrama) : defeito alvo h ≤ 6 :=
  (Finset.card_filter_le _ _).trans (by simp)

private theorem corrige_desce_numeros :
    ∀ a b : Fin 64, 0 < defeito (deNumero a) (deNumero b) →
      defeito (deNumero a) (corrige (deNumero a) (deNumero b)) + 1 =
        defeito (deNumero a) (deNumero b) := by
  decide +kernel

/-- Cada correção reduz o defeito em exatamente 1 (todos os 64 × 64 casos,
verificados pelo kernel e transportados pela bijeção de Leibniz). -/
theorem corrige_desce (alvo h : Hexagrama) (hpos : 0 < defeito alvo h) :
    defeito alvo (corrige alvo h) + 1 = defeito alvo h := by
  obtain ⟨a, rfl⟩ := deNumero_bijetivo.2 alvo
  obtain ⟨b, rfl⟩ := deNumero_bijetivo.2 h
  exact corrige_desce_numeros a b hpos

/-- Todo hexagrama alcança qualquer alvo em no máximo 6 correções. -/
theorem alcanca_alvo (alvo h : Hexagrama) :
    ∃ n ≤ 6, (corrige alvo)^[n] h = alvo := by
  obtain ⟨n, hn, h0⟩ := Nucleo.correcao_finita (defeito alvo) (corrige alvo)
    (fun x hx => by have := corrige_desce alvo x hx; omega) h
  exact ⟨n, hn.trans (defeito_le_seis alvo h), (defeito_eq_zero_iff _ _).1 h0⟩

/-! ## O exemplo concreto: 101100 → 111001 -/

def exemplo : Hexagrama := ![true, false, true, true, false, false]
def alvoExemplo : Hexagrama := ![true, true, true, false, false, true]

theorem exemplo_defeito : defeito alvoExemplo exemplo = 3 := by decide

/-- 3 → 2 → 1 → 0: três correções bastam. -/
theorem exemplo_trajetoria :
    defeito alvoExemplo (corrige alvoExemplo exemplo) = 2 ∧
    defeito alvoExemplo ((corrige alvoExemplo)^[2] exemplo) = 1 ∧
    (corrige alvoExemplo)^[3] exemplo = alvoExemplo := by
  decide

end BeitHamikdash.Tradicoes.IChing
