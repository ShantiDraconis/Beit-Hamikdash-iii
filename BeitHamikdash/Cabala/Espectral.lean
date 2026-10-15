import BeitHamikdash.Cabala.Arvore
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Energia e laplaciano da Árvore da Vida

Atribua um número real `f s` a cada sefirah. A **energia** soma, sobre os 22 caminhos,
o quadrado da diferença entre as pontas. Prova-se:

* a energia é a forma quadrática `⟨f, L f⟩` do laplaciano da Árvore;
* ela é sempre ≥ 0;
* ela é 0 exatamente quando `f` é constante, porque a Árvore é conexa;
* o núcleo do laplaciano tem dimensão 1.

O último item equivale a dizer que o segundo autovalor do laplaciano (a
"conectividade algébrica", λ₂) é positivo. Essa equivalência é um fato padrão de
álgebra linear e não é reprovada aqui. O valor numérico de λ₂ aparece em
`scripts/espectro_arvore.py`, como cálculo em ponto flutuante, não certificado.

Nada disto toca o gap de massa de Yang–Mills: um grafo finito tem gap por razões
elementares, e o problema de Yang–Mills é construir a teoria contínua em 4D.
-/

namespace BeitHamikdash.Cabala

open Matrix

/-- Energia: cada caminho entra nas duas direções, daí o fator 1/2. -/
noncomputable def energia (f : Sefirah → ℝ) : ℝ :=
  (∑ i, ∑ j, if arvore.Adj i j then (f i - f j) ^ 2 else 0) / 2

/-- A energia é a forma quadrática do laplaciano: `⟨f, L f⟩`. -/
theorem energia_eq_forma_laplaciano (f : Sefirah → ℝ) :
    energia f = toLinearMap₂' ℝ (arvore.lapMatrix ℝ) f f :=
  (SimpleGraph.lapMatrix_toLinearMap₂' ℝ arvore f).symm

theorem energia_nao_negativa (f : Sefirah → ℝ) : 0 ≤ energia f := by
  unfold energia
  positivity

/-- Energia zero ⇔ a atribuição é constante. -/
theorem energia_eq_zero_iff (f : Sefirah → ℝ) : energia f = 0 ↔ ∀ i j, f i = f j := by
  rw [energia_eq_forma_laplaciano,
    SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable]
  exact ⟨fun h i j => h i j (arvore_conexa.preconnected i j), fun h i j _ => h i j⟩

/-- O laplaciano anula exatamente as atribuições constantes. -/
theorem laplaciano_anula_iff (f : Sefirah → ℝ) :
    arvore.lapMatrix ℝ *ᵥ f = 0 ↔ ∀ i j, f i = f j := by
  rw [SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable]
  exact ⟨fun h i j => h i j (arvore_conexa.preconnected i j), fun h i j _ => h i j⟩

/-- A Árvore tem uma única componente conexa. -/
theorem uma_componente : Fintype.card arvore.ConnectedComponent = 1 := by
  haveI := arvore_conexa.preconnected.subsingleton_connectedComponent
  exact Fintype.card_eq_one_iff.mpr
    ⟨arvore.connectedComponentMk .keter, fun _ => Subsingleton.elim _ _⟩

/-- O núcleo do laplaciano tem dimensão 1 (equivalente a λ₂ > 0). -/
theorem dim_nucleo_laplaciano :
    Module.finrank ℝ (arvore.lapMatrix ℝ).toLin'.ker = 1 := by
  rw [← SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix, uma_componente]

end BeitHamikdash.Cabala
