# Beit-Hamikdash-iii

Formalização em **Lean 4 + Mathlib** das estruturas simbólicas de tradições
religiosas (Cabala, I Ching, Budismo…) e das suas pontes possíveis com os sete
problemas do programa ATK/M-Core.

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
    SeferYetzirah.lean  22 letras (3+7+12), 32 caminhos, 231 portões = C(22,2),
                        n pedras → n! casas, busca exaustiva > 2^n
    Gematria.lean       valores, aditividade, gematria NÃO injetiva, YHWH e os 4 mundos
  Tradicoes/
    IChing.lean         64 hexagramas = 0..63 em binário (Leibniz, 1703)
    Budismo.lean        12 elos da originação dependente: ciclo de período exato 12
  Milenio/
    Problemas.lean      os 7 problemas, ledger 0/7, Beal, e Beal ⇒ Fermat (provado)
    Riemann.lean        enunciado oficial do Mathlib (`RiemannHypothesis`), sem prova
  Pontes.lean           pontes fechadas e abertas; armadilha numerológica do 13
  Auditoria.lean        #print axioms dos teoremas principais
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

## Como acrescentar uma tradição

1. Crie `BeitHamikdash/Tradicoes/<Nome>.lean` com a estrutura como tipo finito,
   grafo, permutação etc., citando a fonte textual no docstring.
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
```

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.
