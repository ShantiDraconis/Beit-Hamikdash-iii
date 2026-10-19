#!/usr/bin/env python3
"""Falha se algum arquivo .lean usar sorry, admit, native_decide ou declarar axiomas.

Comentários (-- e /- ... -/, inclusive aninhados) e strings são ignorados, para que
a documentação possa citar essas palavras sem disparar o alarme.
"""
import pathlib
import re
import sys

PROIBIDOS = re.compile(r"(?<![\w.])(sorry|admit|native_decide|axiom)(?![\w.])")


def sem_comentarios(src: str) -> str:
    out, i, prof, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            prof += 1
            i += 2
        elif prof and src.startswith("-/", i):
            prof -= 1
            i += 2
        elif prof:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append('""')
            i = j + 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def main() -> int:
    raiz = pathlib.Path(__file__).resolve().parent.parent
    arquivos = [raiz / "BeitHamikdash.lean", *sorted((raiz / "BeitHamikdash").rglob("*.lean"))]
    achados = []
    for arq in arquivos:
        codigo = sem_comentarios(arq.read_text(encoding="utf-8"))
        for num, linha in enumerate(codigo.splitlines(), 1):
            if linha.lstrip().startswith("#print axioms"):
                continue
            for m in PROIBIDOS.finditer(linha):
                achados.append(f"{arq.relative_to(raiz)}:{num}: {m.group(1)}")
    if achados:
        print("Proibido no código (sorry/admit/native_decide/axiom):")
        print("\n".join(achados))
        return 1
    print(f"OK: {len(arquivos)} arquivos sem sorry, admit, native_decide ou axiomas novos.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
