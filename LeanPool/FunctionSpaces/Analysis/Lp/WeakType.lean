/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

/-
Modified for Lean Pool: module names and imports adapted.

Definitions and lemma statements from the Carleson project (L. Becker, M. I. de Frutos-Fernández,
L. Diedering, F. van Doorn, S. Gouëzel, E. Karunus, E. van de Meent, P. Monticone, J. Mulder-Sohn,
J. Portegies, J. Roos, M. Rothgang, J. Sundstrom, J. Tan), Apache 2.0.
-/

/-!
# Weak `L_p` norms and operators of weak and strong type

These are the definitions of the Carleson project (`https://github.com/fpvandoorn/carleson`,
commit `12fb202`, files `Carleson/ToMathlib/WeakType.lean` and
`Carleson/ToMathlib/RealInterpolation/Main.lean`, Apache 2.0), with the same names and
statements, together with the lemmas `wnorm_ne_top`, `wnorm'_le_eLpNorm'`, `wnorm_le_eLpNorm`,
`MemLp.memWLp`, `HasWeakType.memWLp`, `HasStrongType.memLp` and `HasStrongType.hasWeakType` of
the first file; the distribution function is the Carleson project's `μ {x | t < ‖f x‖ₑ}`. They
are intended for Mathlib; when Mathlib has them, this file is replaced by the Mathlib import.
The proofs and docstrings are adapted to Mathlib v4.35.0 and to this project's conventions.
For a function `f : α → ε` into a type with an extended norm `‖·‖ₑ`, such as `ℂ` or `[0, ∞]`:

* the distribution function `MeasureTheory.distribution f t μ = μ {x | t < ‖f x‖ₑ}`, with its
  monotonicity, the distribution of a sum (`MeasureTheory.distribution_add_le_of_enorm`) and
  Chebyshev's inequality (`MeasureTheory.distribution_le_inv_rpow_mul_eLpNorm_rpow`; its
  lintegral form `MeasureTheory.measure_lt_le_inv_rpow_mul_lintegral` is in
  `FunctionSpaces.Analysis.Lp.Marcinkiewicz`, next to the level-set lemmas that use it);
* the weak `L_p` norm `MeasureTheory.wnorm f p μ = sup_t t μ{‖f‖ > t}^{1/p}` (the essential
  supremum for `p = ∞`), bounded by the `L_p` norm (`MeasureTheory.wnorm_le_eLpNorm`), and
  weak `L_p` (`MeasureTheory.MemWLp`);
* operators of weak type and of strong type `(p, q)` (`MeasureTheory.HasWeakType`,
  `MeasureTheory.HasStrongType`), with strong type implying weak type
  (`MeasureTheory.HasStrongType.hasWeakType`), and almost everywhere subadditive operators
  (`MeasureTheory.AESubadditiveOn`).
-/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace MeasureTheory

variable {α α' ε ε₁ ε₂ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' : ℝ≥0∞} {c : ℝ≥0∞} {μ : Measure α} {ν : Measure α'} {t s : ℝ≥0∞}

section ENorm

variable [ENorm ε] {f : α → ε}

/-- The **distribution function** of `f`: the measure `μ {x | ‖f x‖ > t}` of the set where the
extended norm of `f` exceeds the level `t ∈ [0, ∞]`. -/
def distribution (f : α → ε) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  μ {x | t < ‖f x‖ₑ}

/-- No extended norm exceeds `∞`, so the distribution function vanishes at the level `∞`. -/
@[simp]
lemma distribution_top (f : α → ε) (μ : Measure α) : distribution f ∞ μ = 0 := by
  simp [distribution]

/-- **Monotonicity in the function**: if `‖f‖ ≤ ‖g‖` almost everywhere, then the distribution
function of `f` is at most that of `g` at every level. -/
lemma distribution_mono_left {ε' : Type*} [ENorm ε'] {g : α → ε'}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) : distribution f t μ ≤ distribution g t μ :=
  measure_mono_ae (h.mono fun _ hx hxt => lt_of_lt_of_le hxt hx)

/-- **Antitonicity in the level**: the distribution function decreases as the level grows. -/
lemma distribution_mono_right (h : t ≤ s) : distribution f s μ ≤ distribution f t μ :=
  measure_mono fun _ hx => lt_of_le_of_lt h hx

/-- **The distribution of a sum**: if `‖f‖ ≤ c (‖g₁‖ + ‖g₂‖)` almost everywhere, then
`μ{‖f‖ > c (t + s)} ≤ μ{‖g₁‖ > t} + μ{‖g₂‖ > s}`, since `‖g₁‖ ≤ t` and `‖g₂‖ ≤ s` force
`‖f‖ ≤ c (t + s)`. -/
lemma distribution_add_le_of_enorm {ε' ε'' : Type*} [ENorm ε'] [ENorm ε''] {g₁ : α → ε'}
    {g₂ : α → ε''} (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ)) :
    distribution f (c * (t + s)) μ ≤ distribution g₁ t μ + distribution g₂ s μ := by
  unfold distribution
  refine (measure_mono_ae (h.mono fun x hx hxt => ?_)).trans (measure_union_le _ _)
  by_contra hnot
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hnot
  have : c * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ) ≤ c * (t + s) := mul_le_mul_right (add_le_add hnot.1 hnot.2) c
  exact absurd (lt_of_lt_of_le hxt (hx.trans this)) (lt_irrefl _)

/-- The **weak `L_p` norm** for a real exponent: `sup_{t ≥ 0} t μ{‖f‖ > t}^{1/p}`. -/
def wnorm' (f : α → ε) (p : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, t * distribution f t μ ^ (p : ℝ)⁻¹

/-- The **weak `L_p` norm**: `sup_{t ≥ 0} t μ{‖f‖ > t}^{1/p}` for `p < ∞`, and the essential
supremum of `‖f‖` for `p = ∞`. -/
def wnorm (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = ∞ then eLpNormEssSup f μ else wnorm' f (p.toReal) μ

/-- For a finite exponent the weak `L_p` norm is the supremum of `t μ{‖f‖ > t}^{1/p}`. -/
lemma wnorm_ne_top (h : p ≠ ⊤) : wnorm f p μ = wnorm' f p.toReal μ := by simp [wnorm, h]

/-- **The weak `L_1` norm bounds every level**: `t μ{‖f‖ > t} ≤ ‖f‖_{1,∞}` for every
`t ∈ [0, ∞]`. -/
lemma mul_distribution_le_wnorm_one (f : α → ε) (t : ℝ≥0∞) :
    t * distribution f t μ ≤ wnorm f 1 μ := by
  rcases eq_or_ne t ∞ with rfl | ht
  · simp
  rw [wnorm_ne_top ENNReal.one_ne_top, ENNReal.toReal_one, wnorm', ← ENNReal.coe_toNNReal ht]
  refine le_trans (le_of_eq ?_) (le_iSup _ t.toNNReal)
  rw [inv_one, ENNReal.rpow_one]

/-- A function is in **weak `L_p`** if it is almost everywhere strongly measurable and has finite
weak `L_p` norm. -/
def MemWLp [TopologicalSpace ε] (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ wnorm f p μ < ∞

end ENorm

section ContinuousENorm

variable [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε}

/-- **Chebyshev's inequality** for the distribution function: for `0 < p < ∞` and `t ≠ 0`,
`μ{‖f‖ > t} ≤ t^{-p} ‖f‖_p^p`. -/
lemma distribution_le_inv_rpow_mul_eLpNorm_rpow (hp0 : p ≠ 0) (hp : p ≠ ∞) (ht : t ≠ 0) :
    distribution f t μ ≤ t⁻¹ ^ p.toReal * eLpNorm f p μ ^ p.toReal := by
  rcases eq_or_ne t ∞ with rfl | htop
  · rw [distribution_top]
    exact zero_le
  calc distribution f t μ ≤ μ {x | t ≤ ‖f x‖ₑ} :=
      measure_mono fun x (hx : t < ‖f x‖ₑ) => show t ≤ ‖f x‖ₑ from hx.le
    _ ≤ _ := meas_ge_le_mul_pow_eLpNorm_eNorm μ hp0 hp ht fun h => absurd h htop

/-- The weak `L_p` norm is at most the `L_p` norm, for a real exponent `p > 0`: Chebyshev's
inequality `t^p μ{‖f‖ > t} ≤ ∫ ‖f‖^p` at every level `t`. -/
lemma wnorm'_le_eLpNorm' (hf : AEStronglyMeasurable f μ) {p : ℝ} (p0 : 0 < p) :
    wnorm' f p μ ≤ eLpNorm' f p μ := by
  refine iSup_le (fun t ↦ ?_)
  simp_rw [distribution, eLpNorm']
  have p0' : 0 ≤ 1 / p := (div_pos one_pos p0).le
  have set_eq : {x | (t : ℝ≥0∞) < ‖f x‖ₑ} = {x | (t : ℝ≥0∞) ^ p < ‖f x‖ₑ ^ p} := by
    simp [ENNReal.rpow_lt_rpow_iff p0]
  have : (t : ℝ≥0∞) = ((t : ℝ≥0∞) ^ p) ^ (1 / p) := by simp [p0.ne']
  nth_rewrite 1 [inv_eq_one_div p, this, ← ENNReal.mul_rpow_of_nonneg _ _ p0', set_eq]
  refine ENNReal.rpow_le_rpow ?_ p0'
  refine le_trans ?_ <| mul_meas_ge_le_lintegral₀ (hf.eNorm.pow_const p) ((t : ℝ≥0∞) ^ p)
  gcongr
  exact fun x ↦ le_of_lt x

/-- The **weak `L_p` norm is at most the `L_p` norm**, for every exponent `p > 0`. -/
lemma wnorm_le_eLpNorm (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 0 < p) :
    wnorm f p μ ≤ eLpNorm f p μ := by
  by_cases h : p = ⊤
  · simp only [h, wnorm, ↓reduceIte]
    rw [eLpNorm_exponent_top hf]
  · rw [wnorm_ne_top h, eLpNorm_eq_eLpNorm' hp.ne' h hf]
    exact wnorm'_le_eLpNorm' hf (ENNReal.toReal_pos hp.ne' h)

/-- Every function in `L_p`, `p > 0`, lies in weak `L_p`. -/
lemma MemLp.memWLp (hp : 0 < p) (hf : MemLp f p μ) : MemWLp f p μ :=
  ⟨hf.aestronglyMeasurable, wnorm_le_eLpNorm hf.aestronglyMeasurable hp |>.trans_lt hf⟩

end ContinuousENorm

section Defs

variable [ENorm ε₁] [ENorm ε₂] [TopologicalSpace ε₁] [TopologicalSpace ε₂]

/-- An operator has **weak type `(p, q)`** if it is bounded as a map from `L^p` to weak `L^q`.
`HasWeakType T p p' μ ν c` means that `T` has weak type `(p, p')` w.r.t. measures `μ`, `ν`
and constant `c`. -/
def HasWeakType (T : (α → ε₁) → (α' → ε₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * eLpNorm f p μ

/-- An operator has **strong type `(p, q)`** if it is bounded as an operator on `L^p → L^q`.
`HasStrongType T p p' μ ν c` means that `T` has strong type (p, p') w.r.t. measures `μ`, `ν`
and constant `c`. -/
def HasStrongType {α α' : Type*}
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ

end Defs

section TypeLemmas

variable [TopologicalSpace ε₁] [ContinuousENorm ε₁] [TopologicalSpace ε₂] [ContinuousENorm ε₂]
  {T : (α → ε₁) → (α' → ε₂)} {f₁ : α → ε₁}

/-- An operator of weak type `(p, q)` with a finite constant maps `L_p` into weak `L_q`. -/
lemma HasWeakType.memWLp (h : HasWeakType T p p' μ ν c) (hf₁ : MemLp f₁ p μ)
    (hc : c < ⊤ := by finiteness) : MemWLp (T f₁) p' ν :=
  ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| ENNReal.mul_lt_top hc hf₁⟩

/-- An operator of strong type `(p, q)` with a finite constant maps `L_p` into `L_q`. -/
lemma HasStrongType.memLp (h : HasStrongType T p p' μ ν c) (hf₁ : MemLp f₁ p μ)
    (hc : c < ⊤ := by finiteness) : MemLp (T f₁) p' ν :=
  h f₁ hf₁ |>.2.trans_lt <| ENNReal.mul_lt_top hc hf₁

/-- **Strong type implies weak type** with the same constant, for a target exponent `q > 0`,
since the weak `L_q` norm is at most the `L_q` norm. -/
lemma HasStrongType.hasWeakType (hp' : 0 < p')
    (h : HasStrongType T p p' μ ν c) : HasWeakType T p p' μ ν c :=
  fun f hf ↦ ⟨(h f hf).1, wnorm_le_eLpNorm (h f hf).1 hp' |>.trans (h f hf).2⟩

end TypeLemmas

variable [TopologicalSpace ε₁] [ESeminormedAddMonoid ε₁] in
/-- The operator is **almost everywhere subadditive** on the functions satisfying `P` with
constant `A`: `‖T(f + g)‖ ≤ A (‖T f‖ + ‖T g‖)` almost everywhere for all `f, g` satisfying `P`
(this is almost vacuous if `A = ⊤`). -/
def AESubadditiveOn [ENorm ε] (T : (α → ε₁) → α' → ε) (P : (α → ε₁) → Prop) (A : ℝ≥0∞)
    (ν : Measure α') : Prop :=
  ∀ (f g : α → ε₁), P f → P g → ∀ᵐ x ∂ν, ‖T (f + g) x‖ₑ ≤ A * (‖T f x‖ₑ + ‖T g x‖ₑ)

end MeasureTheory
