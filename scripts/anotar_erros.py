#!/usr/bin/env python3
"""Converte erros e avisos do `lake build` em anotações do GitHub Actions."""
import re
import sys

INICIO = re.compile(r"^(error|warning): (?:\./)?(\S+\.lean):(\d+):(\d+): ?(.*)$")
FIM = re.compile(r"^(✔|✖|⚠|error:|warning:|info:|Some required|Build completed|trace:)")


def escapar(texto: str) -> str:
    return texto.replace("%", "%25").replace("\r", "").replace("\n", "%0A")


def main(caminho: str) -> None:
    atual = None
    mensagens = []
    for linha in open(caminho, encoding="utf-8", errors="replace"):
        linha = linha.rstrip("\n")
        m = INICIO.match(linha)
        if m:
            if atual:
                mensagens.append(atual)
            nivel, arq, lin, col, msg = m.groups()
            atual = [nivel, arq, lin, col, [msg]]
        elif atual and FIM.match(linha):
            mensagens.append(atual)
            atual = None
        elif atual:
            atual[4].append(linha)
    if atual:
        mensagens.append(atual)
    for nivel, arq, lin, col, corpo in mensagens:
        texto = escapar("\n".join(corpo).strip()[:1500])
        print(f"::{nivel} file={arq},line={lin},col={col}::{texto}")


if __name__ == "__main__":
    main(sys.argv[1])
