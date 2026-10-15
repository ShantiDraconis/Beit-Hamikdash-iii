import BeitHamikdash.Pontes

/-!
# Auditoria de axiomas

Cada teorema principal deve depender só dos axiomas padrão do Lean
(`propext`, `Classical.choice`, `Quot.sound`) ou de nenhum.
A saída destes comandos aparece no log do build e do CI.
-/

open BeitHamikdash BeitHamikdash.Cabala BeitHamikdash.Tradicoes BeitHamikdash.Milenio

#print axioms card_portoes
#print axioms card_casas
#print axioms dois_pow_lt_casas
#print axioms arvore_conexa
#print axioms num_arestas
#print axioms postoCiclico_eq
#print axioms gematria_nao_injetiva
#print axioms IChing.valorBinario_injetivo
#print axioms Budismo.Nidana.periodo_minimo
#print axioms beal_implica_fermat
#print axioms certificados_terminais
#print axioms pontes_fechadas_provadas
#print axioms armadilha_13
