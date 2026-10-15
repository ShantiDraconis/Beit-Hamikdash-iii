#!/usr/bin/env python3
"""Espectro do laplaciano da Árvore da Vida (disposição de Kircher), em ponto flutuante.

Cálculo numérico, NÃO certificado pelo kernel do Lean. O que o Lean certifica está em
BeitHamikdash/Cabala/Espectral.lean: o núcleo do laplaciano tem dimensão 1, o que
equivale a λ₂ > 0. O valor de λ₂ abaixo é só uma aproximação.

Usa o método de Jacobi para matrizes simétricas, sem dependências externas.
"""
import math

SEFIROT = ["keter", "chokhmah", "binah", "chesed", "gevurah", "tiferet",
           "netzach", "hod", "yesod", "malkhut"]

CAMINHOS = [
    ("keter", "chokhmah"), ("keter", "binah"), ("keter", "tiferet"),
    ("chokhmah", "binah"), ("chokhmah", "tiferet"), ("chokhmah", "chesed"),
    ("binah", "tiferet"), ("binah", "gevurah"),
    ("chesed", "gevurah"), ("chesed", "tiferet"), ("chesed", "netzach"),
    ("gevurah", "tiferet"), ("gevurah", "hod"),
    ("tiferet", "netzach"), ("tiferet", "yesod"), ("tiferet", "hod"),
    ("netzach", "hod"), ("netzach", "yesod"), ("netzach", "malkhut"),
    ("hod", "yesod"), ("hod", "malkhut"),
    ("yesod", "malkhut"),
]


def laplaciano():
    n = len(SEFIROT)
    idx = {s: i for i, s in enumerate(SEFIROT)}
    L = [[0.0] * n for _ in range(n)]
    for a, b in CAMINHOS:
        i, j = idx[a], idx[b]
        L[i][j] -= 1
        L[j][i] -= 1
        L[i][i] += 1
        L[j][j] += 1
    return L


def jacobi(A, tol=1e-14, max_iter=10_000):
    n = len(A)
    A = [row[:] for row in A]
    for _ in range(max_iter):
        p, q, maior = 0, 1, 0.0
        for i in range(n):
            for j in range(i + 1, n):
                if abs(A[i][j]) > maior:
                    p, q, maior = i, j, abs(A[i][j])
        if maior < tol:
            break
        theta = (A[q][q] - A[p][p]) / (2 * A[p][q])
        t = math.copysign(1.0, theta) / (abs(theta) + math.sqrt(theta * theta + 1))
        c = 1 / math.sqrt(t * t + 1)
        s = t * c
        for k in range(n):
            akp, akq = A[k][p], A[k][q]
            A[k][p], A[k][q] = c * akp - s * akq, s * akp + c * akq
        for k in range(n):
            apk, aqk = A[p][k], A[q][k]
            A[p][k], A[q][k] = c * apk - s * aqk, s * apk + c * aqk
    return sorted(A[i][i] for i in range(n))


def main():
    L = laplaciano()
    assert len(CAMINHOS) == 22
    assert sum(L[i][i] for i in range(10)) == 44  # soma dos graus = 2 · 22
    autovalores = jacobi(L)
    print("Autovalores do laplaciano da Árvore (ponto flutuante, não certificado):")
    for k, lam in enumerate(autovalores):
        print(f"  λ{k + 1} = {lam:+.6f}")
    print(f"Conectividade algébrica λ₂ ≈ {autovalores[1]:.6f}")
    print(f"Maior autovalor λ₁₀ ≈ {autovalores[-1]:.6f}")
    print(f"Soma = {sum(autovalores):.6f} (deve ser 44, o traço)")


if __name__ == "__main__":
    main()
