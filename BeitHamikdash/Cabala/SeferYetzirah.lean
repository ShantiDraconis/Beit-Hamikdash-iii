import BeitHamikdash.Cabala.Sefirot
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
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
  deriving DecidableEq, Repr

instance : Fintype Letra :=
  Fintype.ofList [.alef, .bet, .gimel, .dalet, .he, .vav, .zayin, .chet, .tet, .yod,
    .kaf, .lamed, .mem, .nun, .samekh, .ayin, .pe, .tsadi, .qof, .resh, .shin, .tav]
    (fun x => by cases x <;> decide)

namespace Letra

theorem card_eq : Fintype.card Letra = 22 := by decide

/-- A classificação do *Sefer Yetzirah*: 3 mães, 7 duplas, 12 simples. -/
inductive Classe
  | mae     -- *imot*: א מ ש
  | dupla   -- *kfulot*: ב ג ד כ פ ר ת
  | simples -- *peshutot*: as 12 restantes
  deriving DecidableEq, Repr

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
  decide +kernel

/-- Ordem alfabética: alef = 0, …, tav = 21. -/
def Letra.indice : Letra → ℕ
  | .alef => 0 | .bet => 1 | .gimel => 2 | .dalet => 3 | .he => 4 | .vav => 5
  | .zayin => 6 | .chet => 7 | .tet => 8 | .yod => 9 | .kaf => 10 | .lamed => 11
  | .mem => 12 | .nun => 13 | .samekh => 14 | .ayin => 15 | .pe => 16 | .tsadi => 17
  | .qof => 18 | .resh => 19 | .shin => 20 | .tav => 21

/-- Os portões na enumeração tradicional: cada letra junto com as que vêm depois
dela no alfabeto (alef com as 21 seguintes, bet com as 20 seguintes, …). -/
def portoesAlfabeticos : Finset (Letra × Letra) :=
  Finset.univ.filter fun p => p.1.indice < p.2.indice

/-- A enumeração alfabética também dá 231, o mesmo número de `portoes`. -/
theorem card_portoesAlfabeticos : portoesAlfabeticos.card = portoes.card := by
  rw [card_portoes]; decide +kernel

/-- Perfil de um portão: quantas mães, duplas e simples ele contém. -/
def perfil (p : Letra × Letra) : ℕ × ℕ × ℕ :=
  let conta (c : Letra.Classe) : ℕ :=
    (if p.1.classe = c then 1 else 0) + (if p.2.classe = c then 1 else 0)
  (conta .mae, conta .dupla, conta .simples)

/-- Os 231 portões se dividem exatamente em 6 famílias:
mãe–mãe 3, dupla–dupla 21, simples–simples 66, mãe–dupla 21, mãe–simples 36,
dupla–simples 84. -/
theorem portoes_por_familia :
    (portoesAlfabeticos.filter (perfil · = (2, 0, 0))).card = 3 ∧
    (portoesAlfabeticos.filter (perfil · = (0, 2, 0))).card = 21 ∧
    (portoesAlfabeticos.filter (perfil · = (0, 0, 2))).card = 66 ∧
    (portoesAlfabeticos.filter (perfil · = (1, 1, 0))).card = 21 ∧
    (portoesAlfabeticos.filter (perfil · = (1, 0, 1))).card = 36 ∧
    (portoesAlfabeticos.filter (perfil · = (0, 1, 1))).card = 84 := by
  decide +kernel

/-- Não há outra família: todo portão tem um dos 6 perfis. -/
theorem familias_esgotam :
    ∀ p ∈ portoesAlfabeticos, perfil p ∈
      [(2, 0, 0), (0, 2, 0), (0, 0, 2), (1, 1, 0), (1, 0, 1), (0, 1, 1)] := by
  decide +kernel

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
