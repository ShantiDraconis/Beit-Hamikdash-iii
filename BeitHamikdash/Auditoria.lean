import BeitHamikdash.Pontes
import BeitHamikdash.Exemplos.Habitantes

/-!
# Auditoria de axiomas

Cada teorema principal deve depender só dos axiomas padrão do Lean
(`propext`, `Classical.choice`, `Quot.sound`) ou de nenhum.
A saída destes comandos aparece no log do build e do CI.
-/

open BeitHamikdash BeitHamikdash.Cabala BeitHamikdash.Tradicoes BeitHamikdash.Milenio
  BeitHamikdash.Exemplos

#print axioms card_portoes
#print axioms card_casas
#print axioms portoes_por_familia
#print axioms familias_esgotam
#print axioms dois_pow_lt_casas
#print axioms arvore_conexa
#print axioms num_arestas
#print axioms postoCiclico_eq
#print axioms gematria_nao_injetiva
#print axioms energia_eq_zero_iff
#print axioms dim_nucleo_laplaciano
#print axioms comutador_alef_mem
#print axioms anticomutam
#print axioms IChing.valorBinario_injetivo
#print axioms IChing.alcanca_alvo
#print axioms IChing.exemplo_trajetoria
#print axioms Nucleo.correcao_finita
#print axioms Nucleo.defeito_zero_de_invariancia_e_contracao
#print axioms Nucleo.contracao_tende_a_zero
#print axioms Nucleo.transporte_de_contracao
#print axioms Budismo.Nidana.periodo_minimo
#print axioms beal_implica_fermat
#print axioms primo_em_duas_bases_divide_terceira
#print axioms mdcs_par_a_par_podem_diferir
#print axioms exclusao_tripla_nao_basta
#print axioms exclusao_por_cobertura
#print axioms Nucleo.tres_relacoes_incompativeis
#print axioms Nucleo.tende_a_zero_iff_inverso_diverge
#print axioms Nucleo.zero_sobre_zero_indeterminado
#print axioms det_combinacao
#print axioms H6_contagem
#print axioms H7_cota
#print axioms H9_positiva
#print axioms H10_quadrado
#print axioms defeito_gram
#print axioms certificados_terminais
#print axioms pontes_fechadas_provadas
#print axioms armadilha_13
