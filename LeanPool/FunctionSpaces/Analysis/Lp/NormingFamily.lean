/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Lp.MixedNorms
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# `L_p(ℓ_2)` norms by duality: the norming family

For `1 < p < ∞` with conjugate exponent `p'`, the `L_p(ℓ_2)` norm of a family
`u = (u_j)_{j ∈ ℕ}` of complex functions in `L_p` that vanishes outside a finite set is bounded
by every `A ∈ [0, ∞]` that bounds all pairings `|∑_j ∫ u_j conj g_j|` by
`A ‖ ‖(g_j)_j‖_{ℓ_2} ‖_{p'}` (`MeasureTheory.eLpNorm_lqNorm_le_of_forall_enorm_sum_integral_le`),
and the `L_p` norm of one function in `L_p` likewise
(`MeasureTheory.eLpNorm_le_of_forall_enorm_integral_mul_conj_le`). The proof tests the pairing
on the **norming family** `u_j ‖(u_i)_i‖_{ℓ_2}^{p-2}` (`MeasureTheory.normingFamily`), which lies
in `L_{p'}(ℓ_2)` (`MeasureTheory.eLpNorm_lqNorm_normingFamily`,
`MeasureTheory.memLp_normingFamily`) and pairs with `u` to `∫ ‖(u_i)_i‖_{ℓ_2}^p`
(`MeasureTheory.enorm_sum_integral_mul_conj_normingFamily`), and cancels a power in Hölder's
inequality with `ENNReal.le_rpow_mul_of_le_mul_rpow` from `FunctionSpaces.Analysis.Lp.MixedNorms`.

The file also has Hölder's inequality for functions with values in `[0, ∞]` in `L_p` norms
(`MeasureTheory.lintegral_mul_le_eLpNorm_mul_eLpNorm`), the finiteness of the `L_p(ℓ_2)` norm of
a family in `L_p` that vanishes outside a finite set
(`MeasureTheory.eLpNorm_lqNorm_ne_top_of_finite`), and membership in `L_p` of each member of a
family whose pointwise `ℓ_2` norm has finite `p`-th power integral
(`MeasureTheory.memLp_of_lintegral_lqNorm_rpow_ne_top`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal ComplexConjugate
open ENNReal (lqNorm)

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### Hölder's inequality and families vanishing outside a finite set -/

/-- **Hölder's inequality for functions with values in `[0, ∞]`, in `L_p` norms**: for
conjugate exponents `1 < p, q < ∞` and almost everywhere measurable `F, G`,
`∫ F G ≤ ‖F‖_p ‖G‖_q`. This is Mathlib's `ENNReal.lintegral_mul_le_Lp_mul_Lq`, which writes the
right side with the integrals `(∫ F^p)^(1/p) (∫ G^q)^(1/q)` and real exponents. -/
theorem lintegral_mul_le_eLpNorm_mul_eLpNorm {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : p ≠ ∞)
    (hq : q ≠ ∞) {F G : α → ℝ≥0∞} (hF : AEMeasurable F μ) (hG : AEMeasurable G μ) :
    ∫⁻ x, F x * G x ∂μ ≤ eLpNorm F p μ * eLpNorm G q μ := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.HolderConjugate.ne_zero p q) hp
      hF.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.HolderConjugate.ne_zero q p) hq
      hG.aestronglyMeasurable]
  simp only [eNorm_eq_self]
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ (ENNReal.HolderConjugate.toReal_of_ne_top hp hq) hF hG

omit [MeasurableSpace α] in
/-- A family of complex functions that vanishes outside a finite set `s` has finite pointwise
`ℓ_2` norm: `‖(u_j(x))_j‖_{ℓ_2} ≤ ∑_{j ∈ s} |u_j(x)| < ∞` (`ENNReal.lqNorm_le_sum_of_eq_zero`). -/
theorem lqNorm_enorm_ne_top_of_finite (s : Finset ℕ) {u : ℕ → α → ℂ} (hus : ∀ j ∉ s, u j = 0)
    (x : α) : lqNorm 2 (fun j => ‖u j x‖ₑ) ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.sum_lt_top.2 fun j (_ : j ∈ s) => eNorm_lt_top).ne
    (ENNReal.lqNorm_le_sum_of_eq_zero one_le_two s fun j hj => by simp [hus j hj])

/-- **A family in `L_p` that vanishes outside a finite set lies in `L_p(ℓ_2)`**: if
`u_j ∈ L_p(μ)` for every `j`, `p ≥ 1`, and `u_j = 0` for `j` outside a finite set `s`, then
`‖ ‖(u_j)_j‖_{ℓ_2} ‖_p < ∞`, since `‖(u_j(x))_j‖_{ℓ_2} ≤ ∑_{j ∈ s} |u_j(x)|` and Minkowski's
inequality bounds the right side by `∑_{j ∈ s} ‖u_j‖_p`. -/
theorem eLpNorm_lqNorm_ne_top_of_finite {p : ℝ≥0∞} (hp1 : 1 ≤ p) (s : Finset ℕ)
    {u : ℕ → α → ℂ} (hu : ∀ j, MemLp (u j) p μ) (hus : ∀ j ∉ s, u j = 0) :
    eLpNorm (fun x => lqNorm 2 fun j => ‖u j x‖ₑ) p μ ≠ ∞ := by
  have hm : AEMeasurable (fun x => lqNorm 2 fun j => ‖u j x‖ₑ) μ :=
    aemeasurable_lqNorm_comp (fun j => (hu j).aestronglyMeasurable.eNorm) 2
  have hsum : eLpNorm (fun x => ∑ j ∈ s, ‖u j x‖ₑ) p μ ≤ ∑ j ∈ s, eLpNorm (u j) p μ := by
    calc eLpNorm (fun x => ∑ j ∈ s, ‖u j x‖ₑ) p μ
        = eLpNorm (∑ j ∈ s, fun x => ‖u j x‖ₑ) p μ := by
          congr 1
          funext x
          simp [Finset.sum_apply]
      _ ≤ ∑ j ∈ s, eLpNorm (fun x => ‖u j x‖ₑ) p μ := eLpNorm_sum_le hp1
      _ = ∑ j ∈ s, eLpNorm (u j) p μ :=
          Finset.sum_congr rfl fun j _ => eLpNorm_eNorm _ (hu j).aestronglyMeasurable
  refine ne_top_of_le_ne_top ?_ ((eLpNorm_mono_eNorm hm.aestronglyMeasurable fun x => ?_).trans
    hsum)
  · exact (ENNReal.sum_lt_top.2 fun j _ => (hu j).eLpNorm_lt_top).ne
  · simpa only [eNorm_eq_self] using
      ENNReal.lqNorm_le_sum_of_eq_zero one_le_two s fun j hj => by simp [hus j hj]

/-- A member of a family lies in `L_p` if the pointwise `ℓ_2` norm of the family has finite
`p`-th power integral, `0 < p < ∞`, since `|g_j| ≤ ‖(g_i)_i‖_{ℓ_2}`; the member is assumed
almost everywhere strongly measurable. -/
theorem memLp_of_lintegral_lqNorm_rpow_ne_top {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {g : ℕ → α → ℂ} {j : ℕ} (hg : AEStronglyMeasurable (g j) μ)
    (hG : ∫⁻ x, (lqNorm 2 fun i => ‖g i x‖ₑ) ^ p.toReal ∂μ ≠ ∞) : MemLp (g j) p μ :=
  memLp_iff.2 ((eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top hp0 hp hg).2 (lt_of_le_of_lt
    (lintegral_mono fun x => ENNReal.rpow_le_rpow
      (ENNReal.le_lqNorm two_ne_zero (fun i => ‖g i x‖ₑ) j) ENNReal.toReal_nonneg) hG.lt_top))

/-- A family in `L_p`, `1 ≤ p < ∞`, that vanishes outside a finite set `s` has
`∫ ‖(u_j)_j‖_{ℓ_2}^p dμ < ∞` (`MeasureTheory.eLpNorm_lqNorm_ne_top_of_finite`). -/
theorem lintegral_lqNorm_rpow_ne_top_of_finite {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    (s : Finset ℕ) {u : ℕ → α → ℂ} (hu : ∀ j, MemLp (u j) p μ) (hus : ∀ j ∉ s, u j = 0) :
    ∫⁻ x, (lqNorm 2 fun j => ‖u j x‖ₑ) ^ p.toReal ∂μ ≠ ∞ := by
  rw [← eLpNorm_rpow_eq_lintegral (zero_lt_one.trans_le hp1).ne' hp
    (aemeasurable_lqNorm_comp (fun j => (hu j).aestronglyMeasurable.eNorm) 2)]
  exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
    (eLpNorm_lqNorm_ne_top_of_finite hp1 s hu hus)

/-! ### The norming family -/

/-- The **norming family** of a family `u = (u_j)_{j ∈ ℕ}` of functions `α → ℂ` for the real
exponent `p`: `N_j(x) = u_j(x) ‖(u_i(x))_i‖_{ℓ_2}^{p-2}`. For `u` in `L_p(ℓ_2)` vanishing
outside a finite set it lies in `L_{p'}(ℓ_2)`, `p'` the conjugate exponent, and its pairing
with `u` is `∫ ‖(u_i)_i‖_{ℓ_2}^p`, so it realises the `L_p(ℓ_2)` norm by duality. -/
noncomputable def normingFamily (p : ℝ) (u : ℕ → α → ℂ) (j : ℕ) (x : α) : ℂ :=
  u j x * (((lqNorm 2 fun i => ‖u i x‖ₑ).toReal ^ (p - 2) : ℝ) : ℂ)

/-- The members of the norming family are almost everywhere strongly measurable if the members
of `u` are. -/
theorem aestronglyMeasurable_normingFamily {u : ℕ → α → ℂ}
    (hu : ∀ j, AEStronglyMeasurable (u j) μ) (p : ℝ) (j : ℕ) :
    AEStronglyMeasurable (normingFamily p u j) μ :=
  (hu j).mul (Complex.measurable_ofReal.comp_aemeasurable
    ((ENNReal.measurable_toReal.comp_aemeasurable
      (aemeasurable_lqNorm_comp (fun i => (hu i).eNorm) 2)).pow_const _)).aestronglyMeasurable

omit [MeasurableSpace α] in
/-- **The size of the norming family**: for `p > 1` and every point `x` with
`‖(u_i(x))_i‖_{ℓ_2} < ∞`, `‖(N_j(x))_j‖_{ℓ_2} = ‖(u_i(x))_i‖_{ℓ_2}^{p-1}`, since every member
is multiplied by `‖(u_i(x))_i‖_{ℓ_2}^{p-2}`. -/
theorem lqNorm_normingFamily {p : ℝ} (hp : 1 < p) (u : ℕ → α → ℂ) {x : α}
    (hx : lqNorm 2 (fun i => ‖u i x‖ₑ) ≠ ∞) :
    lqNorm 2 (fun j => ‖normingFamily p u j x‖ₑ) = lqNorm 2 (fun i => ‖u i x‖ₑ) ^ (p - 1) := by
  have h1 : ∀ j, ‖normingFamily p u j x‖ₑ =
      ENNReal.ofReal ((lqNorm 2 fun i => ‖u i x‖ₑ).toReal ^ (p - 2)) * ‖u j x‖ₑ := fun j => by
    rw [normingFamily, eNorm_mul, mul_comm]
    congr 1
    rw [← ofReal_norm, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
  simp_rw [h1]
  rw [ENNReal.lqNorm_const_mul]
  generalize lqNorm 2 (fun i => ‖u i x‖ₑ) = U at hx ⊢
  rcases eq_or_ne U 0 with rfl | h0
  · rw [mul_zero, ENNReal.zero_rpow_of_pos (by linarith)]
  rw [ENNReal.toReal_rpow, ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_ne_zero h0 hx)]
  calc U ^ (p - 2) * U = U ^ (p - 2) * U ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
    _ = U ^ (p - 2 + 1) := (ENNReal.rpow_add _ _ h0 hx).symm
    _ = U ^ (p - 1) := by ring_nf

omit [MeasurableSpace α] in
/-- **The pairing of a family with its norming family**: if `u_j(x) = 0` for every `j` outside a
finite set `s`, then `∑_{j ∈ s} u_j(x) conj N_j(x) = ‖(u_i(x))_i‖_{ℓ_2}^p` for every `p > 0`,
since `u_j conj u_j = |u_j|²` and `∑_{j ∈ s} |u_j(x)|² = ‖(u_i(x))_i‖_{ℓ_2}²`. -/
theorem sum_mul_conj_normingFamily {p : ℝ} (hp : 0 < p) (s : Finset ℕ) (u : ℕ → α → ℂ)
    {x : α} (hus : ∀ j ∉ s, u j x = 0) :
    ∑ j ∈ s, u j x * conj (normingFamily p u j x) =
      (((lqNorm 2 fun i => ‖u i x‖ₑ).toReal ^ p : ℝ) : ℂ) := by
  have hsq : (lqNorm 2 fun i => ‖u i x‖ₑ).toReal ^ 2 = ∑ j ∈ s, ‖u j x‖ ^ 2 := by
    have h := ENNReal.lqNorm_two_sq (fun i => ‖u i x‖ₑ)
    rw [tsum_eq_sum (s := s) fun j hj => by simp [hus j hj]] at h
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_pow, ENNReal.toReal_sum fun j _ => by finiteness] at h'
    simpa only [ENNReal.toReal_pow, toReal_eNorm] using h'
  have hr : 0 ≤ (lqNorm 2 fun i => ‖u i x‖ₑ).toReal := ENNReal.toReal_nonneg
  simp only [normingFamily]
  generalize (lqNorm 2 fun i => ‖u i x‖ₑ).toReal = r at hr hsq ⊢
  have hterm : ∀ j, u j x * conj (u j x * ((r ^ (p - 2) : ℝ) : ℂ)) =
      ((‖u j x‖ ^ 2 * r ^ (p - 2) : ℝ) : ℂ) := fun j => by
    rw [map_mul, Complex.conj_ofReal, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Complex.ofReal_sum, ← Finset.sum_mul, ← hsq,
    ← Real.rpow_two, ← Real.rpow_add' hr (by linarith : (0 : ℝ) < 2 + (p - 2)).ne',
    show (2 : ℝ) + (p - 2) = p by ring]

/-- **The `L_q(ℓ_2)` norm of the norming family**: let `1 < p < ∞` with conjugate exponent `q`,
and let the `u_j` be almost everywhere strongly measurable with `‖(u_j(x))_j‖_{ℓ_2} < ∞` at
every point. Then `‖ ‖(N_j)_j‖_{ℓ_2} ‖_q = (∫ ‖(u_j)_j‖_{ℓ_2}^p)^{1/q}`, by
`MeasureTheory.lqNorm_normingFamily` and `(p - 1) q = p`. -/
theorem eLpNorm_lqNorm_normingFamily {p q : ℝ≥0∞} [p.HolderConjugate q] (hp1 : 1 < p)
    (hp : p ≠ ∞) {u : ℕ → α → ℂ} (hu : ∀ j, AEStronglyMeasurable (u j) μ)
    (hfin : ∀ x, lqNorm 2 (fun j => ‖u j x‖ₑ) ≠ ∞) :
    eLpNorm (fun x => lqNorm 2 fun j => ‖normingFamily p.toReal u j x‖ₑ) q μ =
      (∫⁻ x, (lqNorm 2 fun j => ‖u j x‖ₑ) ^ p.toReal ∂μ) ^ (1 / q.toReal) := by
  have hq : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2 hp1).ne
  have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hGm : AEMeasurable (fun x => lqNorm 2 fun j => ‖normingFamily p.toReal u j x‖ₑ) μ :=
    aemeasurable_lqNorm_comp (fun j => (aestronglyMeasurable_normingFamily hu _ j).eNorm) 2
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.HolderConjugate.ne_zero q p) hq
    hGm.aestronglyMeasurable]
  simp only [eNorm_eq_self, lqNorm_normingFamily (ENNReal.one_lt_toReal hp1 hp) u (hfin _)]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.rpow_mul, hpq.sub_one_mul_conj]

/-- **The norming family lies in `L_q`**: let `1 < p < ∞` with conjugate exponent `q`, and let
`u_j ∈ L_p(μ)` for every `j` with `u_j = 0` for `j` outside a finite set `s`. Then every member
`N_j` of the norming family lies in `L_q(μ)`, since `|N_j| ≤ ‖(N_i)_i‖_{ℓ_2}`. -/
theorem memLp_normingFamily {p q : ℝ≥0∞} [p.HolderConjugate q] (hp1 : 1 < p) (hp : p ≠ ∞)
    (s : Finset ℕ) {u : ℕ → α → ℂ} (hu : ∀ j, MemLp (u j) p μ) (hus : ∀ j ∉ s, u j = 0)
    (j : ℕ) : MemLp (normingFamily p.toReal u j) q μ := by
  have hgm := aestronglyMeasurable_normingFamily (fun i => (hu i).aestronglyMeasurable) p.toReal
  refine memLp_iff.2 (lt_of_le_of_lt (eLpNorm_mono_eNorm (hgm j)
    (g := fun x => lqNorm 2 fun i => ‖normingFamily p.toReal u i x‖ₑ) fun x => ?_) ?_)
  · rw [eNorm_eq_self]
    exact ENNReal.le_lqNorm two_ne_zero (fun i => ‖normingFamily p.toReal u i x‖ₑ) j
  · rw [eLpNorm_lqNorm_normingFamily hp1 hp (fun i => (hu i).aestronglyMeasurable)
      (lqNorm_enorm_ne_top_of_finite s hus)]
    exact (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (lintegral_lqNorm_rpow_ne_top_of_finite hp1.le hp s hu hus)).lt_top

/-- **The pairing with the norming family**: let `1 < p < ∞` with conjugate exponent `q`, and
let `u_j ∈ L_p(μ)` for every `j` with `u_j = 0` for `j` outside a finite set `s`. Then
`|∑_{j ∈ s} ∫ u_j conj N_j dμ| = ∫ ‖(u_j)_j‖_{ℓ_2}^p dμ`, the integral of the pointwise
identity `MeasureTheory.sum_mul_conj_normingFamily`, a nonnegative real function. -/
theorem enorm_sum_integral_mul_conj_normingFamily {p q : ℝ≥0∞} [p.HolderConjugate q]
    (hp1 : 1 < p) (hp : p ≠ ∞) (s : Finset ℕ) {u : ℕ → α → ℂ} (hu : ∀ j, MemLp (u j) p μ)
    (hus : ∀ j ∉ s, u j = 0) :
    ‖∑ j ∈ s, ∫ x, u j x * conj (normingFamily p.toReal u j x) ∂μ‖ₑ =
      ∫⁻ x, (lqNorm 2 fun j => ‖u j x‖ₑ) ^ p.toReal ∂μ := by
  have hUm : AEMeasurable (fun x => lqNorm 2 fun j => ‖u j x‖ₑ) μ :=
    aemeasurable_lqNorm_comp (fun j => (hu j).aestronglyMeasurable.eNorm) 2
  rw [← integral_finsetSum (f := fun j x => u j x * conj (normingFamily p.toReal u j x)) s
    fun j _ => (hu j).integrable_mul (memLp_normingFamily (q := q) hp1 hp s hu hus j).star]
  have hpt : ∀ x, ∑ j ∈ s, u j x * conj (normingFamily p.toReal u j x) =
      ((((lqNorm 2 fun j => ‖u j x‖ₑ) ^ p.toReal).toReal : ℝ) : ℂ) := fun x => by
    rw [sum_mul_conj_normingFamily (by linarith [ENNReal.one_lt_toReal hp1 hp]) s u
      fun j hj => by rw [hus j hj]; rfl, ENNReal.toReal_rpow]
  simp_rw [hpt]
  rw [integral_complex_ofReal, integral_toReal (hUm.pow_const _)
    (ae_of_all _ fun x => (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
      (lqNorm_enorm_ne_top_of_finite s hus x)).lt_top),
    ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (lintegral_lqNorm_rpow_ne_top_of_finite hp1.le hp s hu hus)]

/-! ### `L_p` norms by duality -/

/-- **The `L_p(ℓ_2)` norm by duality**: let `1 < p < ∞` with conjugate exponent `q`, let
`u_j ∈ L_p(μ)` for every `j` with `u_j = 0` for `j` outside a finite set `s`, and let
`A ∈ [0, ∞]`. If `|∑_{j ∈ s} ∫ u_j conj g_j dμ| ≤ A ‖ ‖(g_j)_j‖_{ℓ_2} ‖_q` for every family of
`g_j ∈ L_q(μ)`, then `‖ ‖(u_j)_j‖_{ℓ_2} ‖_p ≤ A`. The norming family gives `X ≤ A X^{1/q}` for
`X = ∫ ‖(u_j)_j‖_{ℓ_2}^p < ∞`, so `X^{1/p} ≤ A` (`ENNReal.le_rpow_mul_of_le_mul_rpow`). -/
theorem eLpNorm_lqNorm_le_of_forall_enorm_sum_integral_le {p q : ℝ≥0∞} [p.HolderConjugate q]
    (hp1 : 1 < p) (hp : p ≠ ∞) (s : Finset ℕ) {u : ℕ → α → ℂ} (hu : ∀ j, MemLp (u j) p μ)
    (hus : ∀ j ∉ s, u j = 0) {A : ℝ≥0∞}
    (hA : ∀ g : ℕ → α → ℂ, (∀ j, MemLp (g j) q μ) →
      ‖∑ j ∈ s, ∫ x, u j x * conj (g j x) ∂μ‖ₑ ≤
        A * eLpNorm (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) q μ) :
    eLpNorm (fun x => lqNorm 2 fun j => ‖u j x‖ₑ) p μ ≤ A := by
  have hq : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2 hp1).ne
  have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hP : 1 < p.toReal := ENNReal.one_lt_toReal hp1 hp
  have hUm : AEMeasurable (fun x => lqNorm 2 fun j => ‖u j x‖ₑ) μ :=
    aemeasurable_lqNorm_comp (fun j => (hu j).aestronglyMeasurable.eNorm) 2
  have hle := hA _ (memLp_normingFamily hp1 hp s hu hus)
  rw [enorm_sum_integral_mul_conj_normingFamily (q := q) hp1 hp s hu hus,
    eLpNorm_lqNorm_normingFamily hp1 hp (fun j => (hu j).aestronglyMeasurable)
      (lqNorm_enorm_ne_top_of_finite s hus)] at hle
  have hXle := ENNReal.le_rpow_mul_of_le_mul_rpow (K := A) (A := 1) hpq
    (lintegral_lqNorm_rpow_ne_top_of_finite hp1.le hp s hu hus)
    (by rwa [ENNReal.one_rpow, mul_one])
  rw [mul_one] at hXle
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.HolderConjugate.ne_zero p q) hp
    hUm.aestronglyMeasurable]
  simp only [eNorm_eq_self]
  calc (∫⁻ x, (lqNorm 2 fun j => ‖u j x‖ₑ) ^ p.toReal ∂μ) ^ (1 / p.toReal)
      ≤ (A ^ p.toReal) ^ (1 / p.toReal) := ENNReal.rpow_le_rpow hXle (by positivity)
    _ = A := by rw [one_div, ENNReal.rpow_rpow_inv (by linarith)]

/-- **The `L_p` norm by duality**: let `1 < p < ∞` with conjugate exponent `q`, `v ∈ L_p(μ)`
and `A ∈ [0, ∞]`. If `|∫ v conj g dμ| ≤ A ‖g‖_q` for every `g ∈ L_q(μ)`, then `‖v‖_p ≤ A`: the
case of one function in `MeasureTheory.eLpNorm_lqNorm_le_of_forall_enorm_sum_integral_le`,
where the norming function is `v |v|^{p-2}`; the `ℓ_2` norm of `(v(x), 0, 0, …)` is `|v(x)|`
(`ENNReal.lqNorm_ite_eq`). -/
theorem eLpNorm_le_of_forall_enorm_integral_mul_conj_le {p q : ℝ≥0∞} [p.HolderConjugate q]
    (hp1 : 1 < p) (hp : p ≠ ∞) {v : α → ℂ} (hv : MemLp v p μ) {A : ℝ≥0∞}
    (hA : ∀ g : α → ℂ, MemLp g q μ → ‖∫ x, v x * conj (g x) ∂μ‖ₑ ≤ A * eLpNorm g q μ) :
    eLpNorm v p μ ≤ A := by
  have hu : ∀ j, MemLp (fun x => if j = 0 then v x else 0) p μ := fun j => by
    by_cases hj : j = 0
    · simpa [hj] using hv
    · simp [hj]
  have h := eLpNorm_lqNorm_le_of_forall_enorm_sum_integral_le hp1 hp {0}
    (u := fun j x => if j = 0 then v x else 0) hu
    (fun j hj => by funext x; simp [Finset.mem_singleton.not.1 hj]) fun g hg => by
      simp only [Finset.sum_singleton, ↓reduceIte]
      refine (hA (g 0) (hg 0)).trans ?_
      gcongr
      exact eLpNorm_mono_eNorm (hg 0).aestronglyMeasurable fun x => by
        rw [eNorm_eq_self]
        exact ENNReal.le_lqNorm two_ne_zero (fun j => ‖g j x‖ₑ) 0
  have hpt : (fun x => lqNorm 2 fun j => ‖(if j = 0 then v x else 0)‖ₑ) = fun x => ‖v x‖ₑ := by
    funext x
    simp_rw [apply_ite (fun z : ℂ => ‖z‖ₑ), eNorm_zero]
    exact ENNReal.lqNorm_ite_eq two_ne_zero 0 _
  rwa [hpt, eLpNorm_eNorm _ hv.aestronglyMeasurable] at h

end MeasureTheory
