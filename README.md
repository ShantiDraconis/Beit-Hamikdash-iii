# Beit-Hamikdash-iii

Formalização em **Lean 4 + Mathlib** das estruturas simbólicas de tradições
religiosas (Cabala, I Ching, Budismo…) e das suas pontes possíveis com os sete
problemas do programa ATK/M-Core. É o "Terceiro Templo" do ATK.

## A regra

O kernel do Lean não aceita símbolo como prova. Por isso o repositório separa
três coisas:

| Camada | O que é | Status |
|---|---|---|
| **Estruturas** | Sefirot, Árvore da Vida, letras, portões, gematria, hexagramas, nidanas | Provadas: CLOSED_MATH |
| **Pontes fechadas** | Enunciado preciso + prova completa (`PonteFechada`) | Provadas: CLOSED_MATH |
| **Pontes abertas** | Analogias registradas (`PonteAberta`), sem prova | OPEN_MATH |

O tipo `PonteFechada` exige o campo `prova`. Não há como marcar uma ponte como
fechada sem prová-la, e o kernel garante isso. O CI ainda bloqueia `sorry`,
`admit`, `native_decide` e declarações de `axiom`, e audita que os teoremas só
usem `propext`, `Classical.choice` e `Quot.sound`.

## Estrutura

```
BeitHamikdash/
  Cabala/
    Sefirot.lean        10 sefirot, 3 pilares, espelho direita↔esquerda, 4 mundos
    Arvore.lean         Árvore de Kircher como grafo: 22 arestas, conexa,
                        Tiferet único de grau 8, tríade superior, posto cíclico 13
    Espectral.lean      energia = ⟨f, Lf⟩ ≥ 0; energia 0 ⇔ f constante;
                        núcleo do laplaciano de dimensão 1 (λ₂ > 0)
    SeferYetzirah.lean  22 letras (3+7+12), 32 caminhos, 231 portões = C(22,2),
                        6 famílias (3+21+66+21+36+84), n pedras → n! casas,
                        busca exaustiva > 2^n
    Gematria.lean       valores, aditividade, gematria NÃO injetiva, YHWH e os 4 mundos
    LetrasMaes.lean     א, מ, ש como matrizes 2×2 (escolha do projeto):
                        relações de quatérnios divididos e comutadores fechados
  Tradicoes/
    IChing.lean         64 hexagramas = 0..63 em binário (Leibniz, 1703)
    IChingCorrecao.lean correção de Hamming: cada passo desce 1; alvo em ≤ 6 passos;
                        exemplo 101100 → 111001 em 3 passos
    Budismo.lean        12 elos da originação dependente: ciclo de período exato 12
  Nucleo/
    Descida.lean        correção finita: defeito natural que desce chega a 0
    Contracao.lean      invariância + contração ⇒ defeito já é 0 (alerta de circularidade);
                        contração iterada qⁿ; convergência a 0; transporte entre sistemas
  Milenio/
    Problemas.lean      os 7 problemas, ledger 0/7, Beal, e Beal ⇒ Fermat (provado)
    Riemann.lean        enunciado oficial do Mathlib (`RiemannHypothesis`), sem prova
  Pontes.lean           pontes fechadas e abertas; armadilha numerológica do 13
  Auditoria.lean        #print axioms dos teoremas principais
scripts/
  verificar_honestidade.py  bloqueia sorry/admit/native_decide/axiom (ignora comentários)
  auditar_axiomas.sh        falha se aparecer axioma fora do padrão
  anotar_erros.py           erros do Lean viram anotações no GitHub
  espectro_arvore.py        autovalores do laplaciano em ponto flutuante (não certificado)
```

## Status dos problemas

Certificados terminais: **0/7** (teorema `certificados_terminais`).

| Problema | Enunciado no Mathlib v4.35 | Status |
|---|---|---|
| Riemann | sim (`RiemannHypothesis`) | OPEN_MATH |
| Beal | sim (`ConjecturaDeBeal`) | OPEN_MATH |
| P vs NP | não (faltam as classes P e NP) | OPEN_MATH |
| Navier–Stokes | não | OPEN_MATH |
| Yang–Mills | não | OPEN_MATH |
| Hodge | não | OPEN_MATH |
| BSD | não | OPEN_MATH |

A única ponte fechada que toca um dos sete é `beal_implica_fermat`, e ela é
matemática comum, não mística: mostra o formato que uma ponte precisa ter.

## O que os resultados novos dizem, e o que não dizem

* **Espectro da Árvore.** O kernel certifica que o núcleo do laplaciano tem
  dimensão 1, ou seja, λ₂ > 0. Numericamente, λ₂ ≈ 1,2805 e λ_max ≈ 9,0771
  (`scripts/espectro_arvore.py`, não certificado). Todo grafo finito conexo tem
  gap positivo, então isso não toca o gap de massa de Yang–Mills, que exige a
  teoria contínua em 4D.
* **Invariância + contração.** Se um defeito ≥ 0 é preservado *e* contraído
  estritamente, ele já era zero. Esse par de hipóteses não serve como fonte de
  prova para uma conjectura: prová-lo já exige saber a conclusão.
* **Rota de contração para Riemann.** Aproximações com erro `C·qⁿ` no critério de
  Nyman–Beurling dariam D∞ = 0, mas o piso logarítmico `D_N ≳ c/log N`
  (Burnol, 2002; em FinalRoot entra como hipótese) bloqueia a contração
  uniforme `D_{2N} ≤ q·D_N`. Ver `rota_contracao_morta` em
  M-Core (`atk-kernel/ATK/FinalRoot.lean`). Fica registrada como `bloqueada`.
* **Letras mães como matrizes.** As relações valem para a representação escolhida,
  não para as letras em si. Outra escolha daria outras relações.
* **Tabela letra ↔ problema.** Não entra como ponte: é atribuição livre, sem
  enunciado que se possa provar ou refutar.

## Como acrescentar uma tradição

1. Crie `BeitHamikdash/Tradicoes/<Nome>.lean` com a estrutura como tipo finito,
   grafo, permutação etc., citando a fonte textual no docstring. Use
   `Fintype.ofList` em vez de `deriving Fintype`, que falha nesta versão do Mathlib.
2. Prove os fatos estruturais (contagens, simetrias, ciclos) sem `sorry`.
3. Se um fato gerar um enunciado preciso, registre-o em `pontesFechadas` com a prova.
   Se for só analogia, registre-o em `pontesAbertas` com a `Natureza` correta.
4. Importe o arquivo em `BeitHamikdash.lean` e acrescente os `#print axioms` em
   `Auditoria.lean`.

## Build

```bash
lake exe cache get   # baixa o Mathlib pré-compilado
lake build
python3 scripts/verificar_honestidade.py
bash scripts/auditar_axiomas.sh
python3 scripts/espectro_arvore.py
```

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.
