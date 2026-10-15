import BeitHamikdash.Cabala.Arvore
import BeitHamikdash.Cabala.Gematria
import BeitHamikdash.Tradicoes.IChing
import BeitHamikdash.Tradicoes.Budismo
import BeitHamikdash.Milenio.Problemas

/-!
# Pontes entre tradições simbólicas e os problemas

Há dois tipos de ponte, e o tipo de dado impede misturá-los.

* `PonteFechada` carrega um enunciado **e a sua prova**. Não existe maneira de
  construir uma sem prova, então o kernel do Lean garante a regra CLOSED_MATH.
* `PonteAberta` é só um registro: de onde vem a analogia, para qual problema
  aponta e que tipo de analogia é. Não prova nada, e o status do problema
  continua OPEN_MATH.

Uma analogia vira ponte fechada quando gera um enunciado preciso e alguém prova.
-/

namespace BeitHamikdash

open Cabala Tradicoes Milenio

/-- Ponte com prova verificada pelo kernel. -/
structure PonteFechada where
  tradicao : String
  descricao : String
  enunciado : Prop
  prova : enunciado

/-- Que tipo de ligação uma ponte aberta sugere. -/
inductive Natureza
  /-- Imagem sugestiva, sem conteúdo matemático próprio. -/
  | metafora
  /-- Programa de pesquisa matemático ou físico real, em aberto. -/
  | programaDePesquisa
  /-- Fato matemático conhecido, cuja prova está fora deste repositório. -/
  | fatoConhecido
  /-- Nenhuma ligação identificada (registrado para não fingir que há). -/
  | nenhuma
  deriving DecidableEq, Repr

/-- Ponte sem prova: um registro de analogia. -/
structure PonteAberta where
  tradicao : String
  fonte : String
  problema : Problema
  analogia : String
  natureza : Natureza

/-! ## Pontes fechadas -/

def pontesFechadas : List PonteFechada :=
  [ ⟨"Cabala (Sefer Yetzirah, cap. 2)", "os 231 portões são C(22, 2)",
      portoes.card = 231, card_portoes⟩,
    ⟨"Cabala (Sefer Yetzirah, cap. 4)", "n pedras constroem n! casas",
      ∀ n, Fintype.card (Casas n) = n.factorial, card_casas⟩,
    ⟨"Cabala (Sefer Yetzirah, cap. 4)", "a busca exaustiva supera 2^n a partir de n = 4",
      ∀ n, 4 ≤ n → 2 ^ n < Fintype.card (Casas n), fun _ h => dois_pow_lt_casas h⟩,
    ⟨"Cabala (Árvore de Kircher)", "conexa, 22 arestas, Tiferet no centro, posto cíclico 13",
      arvore.Connected ∧ arvore.edgeFinset.card = 22 ∧ arvore.degree Sefirah.tiferet = 8 ∧
        postoCiclico = 13,
      ⟨arvore_conexa, num_arestas, grau_tiferet, postoCiclico_eq⟩⟩,
    ⟨"Cabala (gematria)", "a gematria é aditiva e não é injetiva",
      (∀ u v, gematria (u ++ v) = gematria u + gematria v) ∧ ¬ Function.Injective gematria,
      ⟨gematria_append, gematria_nao_injetiva⟩⟩,
    ⟨"I Ching (Leibniz, 1703)", "os 64 hexagramas são os números 0 a 63 em binário",
      Function.Injective IChing.valorBinario ∧ ∀ h, IChing.valorBinario h < 64,
      ⟨IChing.valorBinario_injetivo, IChing.valorBinario_lt⟩⟩,
    ⟨"Budismo (pratītyasamutpāda)", "os 12 elos formam um ciclo de período exato 12",
      (∀ n, Budismo.Nidana.proximo^[12] n = n),
      Budismo.Nidana.ciclo_12⟩,
    ⟨"Matemática", "Conjectura de Beal ⇒ Último Teorema de Fermat",
      ConjecturaDeBeal → FermatLastTheorem, beal_implica_fermat⟩ ]

/-- O invariante do repositório: toda ponte fechada está provada.
(É imediato porque o tipo `PonteFechada` não admite outra possibilidade.) -/
theorem pontes_fechadas_provadas : ∀ p ∈ pontesFechadas, p.enunciado :=
  fun p _ => p.prova

/-! ## Pontes abertas -/

def pontesAbertas : List PonteAberta :=
  [ ⟨"Física quântica", "Hilbert, Pólya; Montgomery e Dyson (1972)", .riemann,
      "Os zeros de ζ se distribuem como autovalores de matrizes hermitianas aleatórias. \
       Um operador hermitiano com esses autovalores provaria RH.", .programaDePesquisa⟩,
    ⟨"Filosofia / lógica", "Gödel; RH equivale a um enunciado Π₁", .riemann,
      "Se RH fosse independente da aritmética, seria verdadeira, porque um contraexemplo \
       seria verificável por cálculo finito. Isso não ajuda a provar RH.", .fatoConhecido⟩,
    ⟨"Cabala (gematria)", "mispar hechrechi", .riemann,
      "A gematria é aritmética de letras, mas não envolve primos nem zeros de ζ, \
       e não é injetiva (ver `gematria_nao_injetiva`).", .nenhuma⟩,
    ⟨"Cabala (Sefer Yetzirah)", "cap. 2 e 4: portões e casas", .pVsNp,
      "Espaços de busca combinatórios. A explosão n! está provada aqui, mas P vs NP \
       pergunta se existe atalho, e o texto não trata disso.", .metafora⟩,
    ⟨"I Ching", "Leibniz, Explication de l'Arithmétique Binaire (1703)", .pVsNp,
      "Codificação binária, base histórica real da computação. Não diz nada sobre \
       classes de complexidade.", .metafora⟩,
    ⟨"Cabala luriânica", "Etz Chaim (Chaim Vital): Shevirat ha-Kelim", .navierStokes,
      "Vasos que se rompem por não conter a luz ↔ explosão (blow-up) em tempo finito.",
      .metafora⟩,
    ⟨"Cabala luriânica", "Etz Chaim (Chaim Vital): Tzimtzum", .yangMills,
      "Contração que abre um espaço vazio ↔ lacuna de massa acima do vácuo.", .metafora⟩,
    ⟨"Cabala", "os quatro mundos (Atzilut → Assiah)", .hodge,
      "Níveis de realização do abstrato no concreto ↔ classes topológicas \
       realizadas por ciclos algébricos.", .metafora⟩,
    ⟨"—", "—", .bsd, "Nenhuma analogia identificada.", .nenhuma⟩ ]

/-! ## Armadilha numerológica -/

/-- ⚠️ **Armadilha numerológica, verificada e desarmada pelo kernel.**

As igualdades são verdadeiras: o posto cíclico da Árvore é 13, אחד ("um") vale 13
e אהבה ("amor") vale 13. Mas isto **não** é uma ponte. Pelo teorema
`gematria_nao_injetiva`, valores iguais não implicam palavras iguais, e menos ainda
conceitos ligados. Igualdade numérica sem um mecanismo que a explique é coincidência.
Ela fica registrada aqui como exemplo do que não conta como evidência. -/
theorem armadilha_13 :
    postoCiclico = gematria echad ∧ gematria echad = gematria ahavah :=
  ⟨by rw [postoCiclico_eq, gematria_echad], gematria_echad.trans gematria_ahavah.symm⟩

end BeitHamikdash
