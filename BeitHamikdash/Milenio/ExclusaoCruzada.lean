import Mathlib.Data.Set.Basic

/-!
# Exclusão cruzada: `T ∉ P/SA`, `A ∉ P/ST`, `S ∉ P/AT`

A proposta: excluir cada um dos três símbolos S, A, T de uma classe construída com
os outros dois, e daí concluir `SAT ∉ P`. Lendo `/` como diferença de conjuntos,
este arquivo prova três coisas.

1. `x ∉ P \ Q ↔ x ∉ P ∨ x ∈ Q`. Ficar fora de uma diferença **não** obriga a
   ficar fora de `P`.
2. Por isso, as três exclusões podem valer todas com os três elementos **dentro**
   de `P` (contraexemplo explícito abaixo). Elas sozinhas não dão `∉ P`.
3. O argumento que funciona é outro: se três famílias **cobrem** `P` e o **mesmo**
   alvo está fora de cada uma, ele está fora de `P`. A lógica está provada; as duas
   hipóteses (cobertura de todos os algoritmos polinomiais e exclusão de SAT de cada
   família) são exatamente o problema P vs NP e continuam OPEN_MATH.

Uma observação sobre os nomes: a sigla SAT vem do inglês *satisfiability*. As letras
S, A e T da sigla não carregam estrutura do problema, então uma ligação entre os
símbolos S, A, T (ou as letras Shin, Alef, Tav) e o problema SAT seria coincidência
de nome, do mesmo tipo da armadilha do 13 em `Pontes.lean`.
-/

namespace BeitHamikdash.Milenio

/-- Estar fora de uma diferença: fora de `P`, ou dentro de `Q`. -/
theorem fora_da_diferenca_iff {U : Type*} (P Q : Set U) (x : U) :
    x ∉ P \ Q ↔ x ∉ P ∨ x ∈ Q := by
  simp only [Set.mem_sdiff, not_and_or, not_not]

/-- **As três exclusões não bastam.** Com `P = {1, 2, 3}`, `S = A = T = {3}` e os três
elementos iguais a 3, as três exclusões valem e, mesmo assim, 3 ∈ P. -/
theorem exclusao_tripla_nao_basta :
    let P : Set ℕ := {1, 2, 3}
    let S : Set ℕ := {3}
    let A : Set ℕ := {3}
    let T : Set ℕ := {3}
    (3 ∉ P \ (S ∩ A)) ∧ (3 ∉ P \ (S ∩ T)) ∧ (3 ∉ P \ (A ∩ T)) ∧ 3 ∈ P := by
  intro P S A T
  have h3 : (3 : ℕ) ∈ ({3} : Set ℕ) := rfl
  have hP : (3 : ℕ) ∈ P := Or.inr (Or.inr rfl)
  refine ⟨?_, ?_, ?_, hP⟩ <;> exact fun h => h.2 ⟨h3, h3⟩

/-- **O argumento que funciona (condicional).** Se três famílias cobrem `P` e o alvo
está fora de cada uma, o alvo está fora de `P`. As hipóteses `cobertura`, `hSA`,
`hST` e `hAT` são o conteúdo matemático real, e para P vs NP estão em aberto. -/
theorem exclusao_por_cobertura {L : Type*} (P PSA PST PAT : Set L) (alvo : L)
    (cobertura : P = PSA ∪ PST ∪ PAT)
    (hSA : alvo ∉ PSA) (hST : alvo ∉ PST) (hAT : alvo ∉ PAT) :
    alvo ∉ P := by
  rw [cobertura]
  rintro ((h | h) | h)
  · exact hSA h
  · exact hST h
  · exact hAT h

end BeitHamikdash.Milenio
