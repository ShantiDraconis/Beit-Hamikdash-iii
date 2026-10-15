import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Invariância, contração e transporte de defeitos

Quatro teoremas gerais da série "Terceiro Templo", agora verificados pelo kernel.

1. **Alerta de circularidade.** Se uma transformação preserva um defeito não negativo
   *e* o contrai estritamente, o defeito já era zero. Logo esse par de propriedades
   não pode ser a fonte de uma prova: provar ambas para o defeito de uma conjectura
   exige já saber que ele é zero.
2. **Contração iterada.** `d (T^[n] x) ≤ q^n · d x`.
3. **Convergência.** Com `0 ≤ q < 1`, o defeito iterado tende a zero.
4. **Transporte.** Uma correção contrativa num sistema `B` passa para `A` se a
   tradução `F : A → B` preserva o defeito e comuta com as correções.
-/

namespace BeitHamikdash.Nucleo

open Filter Topology

variable {X : Type*}

/-- **Invariância + contração estrita ⇒ o defeito já é zero.** -/
theorem defeito_zero_de_invariancia_e_contracao (d : X → ℝ) (T : X → X) {q : ℝ}
    (hq : q < 1) (hpos : ∀ x, 0 ≤ d x) (hinv : ∀ x, d (T x) = d x)
    (hcon : ∀ x, d (T x) ≤ q * d x) (x : X) : d x = 0 := by
  have h1 : d x ≤ q * d x := hinv x ▸ hcon x
  by_contra hne
  have hp : 0 < d x := lt_of_le_of_ne (hpos x) (Ne.symm hne)
  have : q * d x < 1 * d x := mul_lt_mul_of_pos_right hq hp
  linarith

/-- Contração iterada. -/
theorem contracao_iterada (d : X → ℝ) (T : X → X) {q : ℝ} (hq0 : 0 ≤ q)
    (hcon : ∀ x, d (T x) ≤ q * d x) (x : X) (n : ℕ) :
    d (T^[n] x) ≤ q ^ n * d x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    calc d (T (T^[n] x)) ≤ q * d (T^[n] x) := hcon _
      _ ≤ q * (q ^ n * d x) := mul_le_mul_of_nonneg_left ih hq0
      _ = q ^ n * q * d x := by ring

/-- Com `0 ≤ q < 1`, o defeito iterado tende a zero. -/
theorem contracao_tende_a_zero (d : X → ℝ) (T : X → X) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hpos : ∀ x, 0 ≤ d x) (hcon : ∀ x, d (T x) ≤ q * d x) (x : X) :
    Tendsto (fun n => d (T^[n] x)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => q ^ n * d x) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (d x)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => hpos _) (fun n => contracao_iterada d T hq0 hcon x n)

/-- Transporte de uma correção contrativa entre dois sistemas. -/
theorem transporte_de_contracao {A B : Type*} (eA : A → ℝ) (eB : B → ℝ) (F : A → B)
    (CA : A → A) (CB : B → B) {q : ℝ}
    (hpres : ∀ a, eB (F a) = eA a) (hcomut : ∀ a, F (CA a) = CB (F a))
    (hcon : ∀ b, eB (CB b) ≤ q * eB b) (a : A) :
    eA (CA a) ≤ q * eA a := by
  rw [← hpres (CA a), hcomut, ← hpres a]
  exact hcon _

end BeitHamikdash.Nucleo
