import BeitHamikdash.Cabala.Sefirot
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Sefer Yetzirah: letras, caminhos, portões e "casas"

O *Sefer Yetzirah* é um dos textos mais antigos com combinatória explícita.
Este arquivo formaliza três passagens:

* cap. 1: 10 sefirot + 22 letras = **32 caminhos** da sabedoria;
* cap. 2: as letras combinadas duas a duas formam os **231 portões**,
  ou seja, C(22, 2);
* cap. 4: "duas pedras constroem duas casas, três constroem seis, quatro 24,
  cinco 120, seis 720, sete 5040". São os fatoriais: n pedras admitem n! ordens.

A numeração exata dos versículos varia entre as recensões do texto.
-/

namespace BeitHamikdash.Cabala

/-- As 22 letras do alfabeto hebraico. -/
inductive Letra
  | alef | bet | gimel | dalet | he | vav | zayin | chet | tet | yod
  | kaf | lamed | mem | nun | samekh | ayin | pe | tsadi | qof | resh | shin | tav
  deriving DecidableEq, Repr, Fintype

namespace Letra

theorem card_eq : Fintype.card Letra = 22 := by decide

/-- A classificação do *Sefer Yetzirah*: 3 mães, 7 duplas, 12 simples. -/
inductive Classe
  | mae     -- *imot*: א מ ש
  | dupla   -- *kfulot*: ב ג ד כ פ ר ת
  | simples -- *peshutot*: as 12 restantes
  deriving DecidableEq, Repr, Fintype

def classe : Letra → Classe
  | alef | mem | shin => .mae
  | bet | gimel | dalet | kaf | pe | resh | tav => .dupla
  | he | vav | zayin | chet | tet | yod | lamed | nun | samekh | ayin | tsadi | qof => .simples

theorem tamanho_classes :
    (Finset.univ.filter (classe · = .mae)).card = 3 ∧
    (Finset.univ.filter (classe · = .dupla)).card = 7 ∧
    (Finset.univ.filter (classe · = .simples)).card = 12 := by
  decide

end Letra

/-- Os 32 caminhos da sabedoria: as sefirot e as letras, lado a lado. -/
abbrev Caminho := Sefirah ⊕ Letra

theorem card_caminhos : Fintype.card Caminho = 32 := by
  rw [Fintype.card_sum, Sefirah.card_eq_dez, Letra.card_eq]

/-- Os portões: pares não ordenados de letras distintas. -/
def portoes : Finset (Finset Letra) := Finset.univ.powersetCard 2

/-- São 231 portões, isto é, C(22, 2). -/
theorem card_portoes : portoes.card = 231 := by
  rw [portoes, Finset.card_powersetCard, Finset.card_univ, Letra.card_eq]
  decide

/-- Lidos com "frente e verso" (pares ordenados), os portões são 462 = 22 · 21. -/
theorem card_portoes_ordenados :
    Fintype.card {p : Letra × Letra // p.1 ≠ p.2} = 462 := by
  decide

/-- As "casas" construídas por `n` pedras: as ordenações das pedras. -/
abbrev Casas (n : ℕ) := Equiv.Perm (Fin n)

/-- `n` pedras constroem `n!` casas. -/
theorem card_casas (n : ℕ) : Fintype.card (Casas n) = n.factorial := by
  rw [Fintype.card_perm, Fintype.card_fin]

/-- Os números exatos do texto, de 2 a 7 pedras. -/
theorem casas_do_texto :
    Fintype.card (Casas 2) = 2 ∧ Fintype.card (Casas 3) = 6 ∧
    Fintype.card (Casas 4) = 24 ∧ Fintype.card (Casas 5) = 120 ∧
    Fintype.card (Casas 6) = 720 ∧ Fintype.card (Casas 7) = 5040 := by
  simp only [card_casas]
  decide

/-- "Daqui em diante, sai e pensa o que a boca não pode falar": a partir de 4 pedras,
as casas crescem mais rápido que qualquer potência de 2.

É por isso que testar todas as ordens de n objetos, a busca exaustiva, fica
inviável. Note que isso não diz nada sobre a existência de um método esperto que
evite a busca. Essa pergunta, para uma classe enorme de problemas, é P vs NP. -/
theorem dois_pow_lt_casas {n : ℕ} (hn : 4 ≤ n) : 2 ^ n < Fintype.card (Casas n) := by
  rw [card_casas]
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [Nat.pow_succ, Nat.factorial_succ]
    calc 2 ^ n * 2 < n.factorial * 2 := by omega
      _ ≤ n.factorial * (n + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (n + 1) * n.factorial := Nat.mul_comm _ _

end BeitHamikdash.Cabala
