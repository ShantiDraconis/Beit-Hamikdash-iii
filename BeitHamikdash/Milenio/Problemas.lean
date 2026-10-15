import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Tactic.Ring

/-!
# Os sete problemas do programa ATK e seu status honesto

A lista segue o programa ATK/M-Core: os seis problemas Clay em aberto e, no lugar
da Conjectura de Poincaré (resolvida por Perelman em 2003), a Conjectura de Beal.
Beal não é um problema Clay; é o Prêmio Beal, administrado pela AMS.

**Regra:** um problema só passa a `closedMath` com um termo do seu enunciado
verificado pelo kernel, sem `sorry`, sem `admit` e sem axiomas novos.
Hoje nenhum tem esse certificado, e o ledger abaixo diz isso.
-/

namespace BeitHamikdash.Milenio

inductive Problema
  | riemann | pVsNp | navierStokes | yangMills | bsd | hodge | beal
  deriving DecidableEq, Repr, Fintype

inductive Status
  | openMath   -- OPEN_MATH = true
  | closedMath -- CLOSED_MATH = true, só com prova no kernel
  deriving DecidableEq, Repr

/-- Status atual. Mudar uma entrada para `closedMath` exige, no mesmo commit, o
teorema correspondente neste repositório. -/
def status : Problema → Status := fun _ => .openMath

/-- Certificados terminais: 0 de 7. -/
theorem certificados_terminais :
    (Finset.univ.filter (status · = .closedMath)).card = 0 := by
  decide

/-- Há enunciado formal fiel no Mathlib v4.35 hoje?
* Riemann: sim, `RiemannHypothesis` (ver `Milenio/Riemann.lean`).
* Beal: sim, enunciado elementar, logo abaixo.
* P vs NP: não. O Mathlib tem máquinas de Turing e computabilidade em tempo
  polinomial, mas não as classes P e NP como na formulação Clay.
* Navier–Stokes, Yang–Mills, Hodge, BSD: não. Faltam a teoria das soluções suaves
  em ℝ³, as QFTs quânticas axiomáticas, os ciclos algébricos e a função L de curvas
  elípticas com a generalidade necessária. -/
def enunciavelNoMathlib : Problema → Bool
  | .riemann | .beal => true
  | _ => false

/-- A Conjectura de Beal: se `A^x + B^y = C^z` com expoentes maiores que 2,
então `A`, `B` e `C` têm um fator primo comum. -/
def ConjecturaDeBeal : Prop :=
  ∀ A B C x y z : ℕ, 0 < A → 0 < B → 0 < C → 2 < x → 2 < y → 2 < z →
    A ^ x + B ^ y = C ^ z → ∃ p, p.Prime ∧ p ∣ A ∧ p ∣ B ∧ p ∣ C

/-- A hipótese do fator comum não é vazia: existem soluções, e elas têm fator comum. -/
example : 3 ^ 3 + 6 ^ 3 = 3 ^ 5 := rfl
example : 2 ^ 3 + 2 ^ 3 = 2 ^ 4 := rfl

/-- **Ponte real (provada):** a Conjectura de Beal implica o Último Teorema de Fermat,
no enunciado oficial do Mathlib.

Este é o modelo do que conta como ponte no repositório: um enunciado preciso,
uma prova completa e nenhum axioma além dos padrões do Lean. -/
theorem beal_implica_fermat (hBeal : ConjecturaDeBeal) : FermatLastTheorem := by
  intro n hn a b c ha hb hc heq
  have hn0 : n ≠ 0 := by omega
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ha)
  obtain ⟨g, a', b', hg0, hcop, rfl, rfl⟩ := Nat.exists_coprime' hg
  have hgc : g ∣ c := by
    rw [← Nat.pow_dvd_pow_iff hn0, ← heq, Nat.mul_pow, Nat.mul_pow]
    exact Nat.dvd_add (Nat.dvd_mul_left _ _) (Nat.dvd_mul_left _ _)
  obtain ⟨c', rfl⟩ := hgc
  have key : g ^ n * (a' ^ n + b' ^ n) = g ^ n * c' ^ n :=
    calc g ^ n * (a' ^ n + b' ^ n) = (a' * g) ^ n + (b' * g) ^ n := by ring
      _ = (g * c') ^ n := heq
      _ = g ^ n * c' ^ n := by ring
  have heq' := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (pow_ne_zero n hg0.ne')) key
  obtain ⟨p, hp, hpa, hpb, -⟩ :=
    hBeal a' b' c' n n n
      (Nat.pos_of_ne_zero (left_ne_zero_of_mul ha))
      (Nat.pos_of_ne_zero (left_ne_zero_of_mul hb))
      (Nat.pos_of_ne_zero (right_ne_zero_of_mul hc))
      (by omega) (by omega) (by omega) heq'
  exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpa hpb hcop

end BeitHamikdash.Milenio
