import Mathlib

/-!
# Foundations — symbolic invariants and preservation

Generic, religion-independent lemmas about invariants preserved under transformations. These
facts do not depend on any symbolic or religious interpretation; the "symbolic" framing in
`TerceiroTemplo.Traditions.*` only chooses *which* set and function to plug in here.

Status: `FORMAL`, `PROVED`, `CERTIFIED` by the kernel's own axiom check. No `sorry`, no custom
`axiom`.
-/

namespace TerceiroTemplo

universe u v

/-- An invariant assigns a value (of type `β`) to every state (of type `α`). -/
structure SymbolicInvariant (α : Type u) (β : Type v) where
  value : α → β

/-- A transformation `f : α → α` preserves an invariant `I` iff `I` takes the same value before
and after applying `f`. -/
def Preserves {α : Type u} {β : Type v} (I : SymbolicInvariant α β) (f : α → α) : Prop :=
  ∀ x, I.value (f x) = I.value x

/-- Composition of invariant-preserving transformations preserves the invariant. -/
theorem preserves_comp {α : Type u} {β : Type v} (I : SymbolicInvariant α β) (f g : α → α)
    (hf : Preserves I f) (hg : Preserves I g) : Preserves I (f ∘ g) := by
  intro x
  calc I.value ((f ∘ g) x) = I.value (g x) := hf (g x)
    _ = I.value x := hg x

/-- The identity transformation preserves every invariant. -/
theorem preserves_id {α : Type u} {β : Type v} (I : SymbolicInvariant α β) :
    Preserves I id := by
  intro x
  rfl

/-- **Positivity of a sum-of-squared-norms quadratic form.**

For any finite family of continuous linear operators `T e : H →L[ℂ] H` on a complex normed
space, the quantity `Σₑ ‖T e x‖²` is always nonnegative. This is the precise mathematical
content behind "an operator built as a sum of path-operators is positive semidefinite": no
positivity *gap* (a strictly positive lower bound, i.e. a spectral gap) follows from this alone —
that would need an extra, separately proved inequality, exactly as already noted for the
religious-symbolism source material this module formalizes. -/
noncomputable def pathQuadForm {ι : Type*} [Fintype ι] {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (T : ι → H →L[ℂ] H) (x : H) : ℝ :=
  ∑ e, ‖T e x‖ ^ 2

theorem pathQuadForm_nonneg {ι : Type*} [Fintype ι] {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (T : ι → H →L[ℂ] H) (x : H) : 0 ≤ pathQuadForm T x :=
  Finset.sum_nonneg fun e _ => sq_nonneg _

end TerceiroTemplo

#print axioms TerceiroTemplo.preserves_comp
#print axioms TerceiroTemplo.preserves_id
#print axioms TerceiroTemplo.pathQuadForm_nonneg
