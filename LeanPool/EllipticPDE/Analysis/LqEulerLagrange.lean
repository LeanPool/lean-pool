/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Analysis.LqDerivative
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic


/-!
# Euler-Lagrange equation under an `L^q` constraint

A vector `U` minimising a nonnegative quadratic `Q` over `{W : ‖T W‖_{L^q} = 1}`, for a
continuous linear `T` into `L^q(μ)` with `q > 1`, satisfies

`L = Q U ∫ |TU|^{q-2} (TU) (TV)`,

where `L` is the coefficient of `2t` in `Q (U + tV)`. The multiplier is the minimum itself, so no
unknown constant survives.

Two instances follow. At `Q W = ‖W‖²` the coefficient is `⟪U, V⟫` and the equation reads
`⟪U, V⟫ = ‖U‖² ∫ |TU|^{q-2} (TU) (TV)`. At `Q W = B[W, W]` for a symmetric positive semidefinite
`B` it is `B[U, V] = B[U, U] ∫ |TU|^{q-2} (TU) (TV)`. On `H₀¹(Ω)` the first gives
`-Δu + u = λ|u|^{q-2}u`, since the graph inner product is `∫uv + ∫∇u·∇v`, and the second at the
bilinear form of the Laplacian gives `-Δu = λ|u|^{q-2}u`, which is the equation of Guo's Section
IX.1.

The argument is Fermat's theorem applied to `g(t) = Q (U + tV) - Q U ‖T(U + tV)‖²_{L^q}`, which
vanishes at `t = 0` and is nonnegative everywhere: rescaling `U + tV` to the constraint set is
admissible whenever its image is nonzero, and where the image vanishes the second term does too.
`EllipticPdes.Analysis.hasDerivAt_integral_abs_rpow` differentiates the constraint, and the chain
rule through `x ↦ x^{2/q}` turns that into the derivative of the squared `L^q` norm.

## Main declarations

* `EllipticPdes.Analysis.norm_lp_rpow_eq_integral`: `‖f‖^q = ∫ |f|^q`.
* `EllipticPdes.Analysis.euler_lagrange_of_quadratic_min`: the equation for a quadratic.
* `EllipticPdes.Analysis.euler_lagrange_of_bilin_min`: the equation for a bilinear form.
* `EllipticPdes.Analysis.euler_lagrange_of_norm_min`: the equation for the norm.

## References

Y. Guo, *Partial Differential Equations*, Section IX.1; L. C. Evans, *Partial Differential
Equations* (2nd ed.), §8.4.1.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Analysis

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **`L^q` norm to the `q`-th power as an integral.** -/
theorem norm_lp_rpow_eq_integral {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (f : Lp ℝ p μ) :
    ‖f‖ ^ p.toReal = ∫ x, ‖f x‖ ^ p.toReal ∂μ := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hint : 0 ≤ ∫ x, ‖f x‖ ^ p.toReal ∂μ :=
    integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm hp0 hptop,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hint _), ← Real.rpow_mul hint,
    inv_mul_cancel₀ hr.ne', Real.rpow_one]

/-- The real square is the real power at exponent two. -/
private lemma rpow_two_eq_sq (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-! ### The equation for a quadratic -/

section Quadratic

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **Euler-Lagrange equation of a quadratic minimiser under an `L^q` constraint.** Let `Q` be
nonnegative and homogeneous of degree two, and let `U` minimise `Q` over the vectors whose image
has unit `L^q` norm. If `Q (U + tV) = Q U + 2tL + t²S`, then

`L = Q U ∫ |TU|^{q-2} (TU) (TV)`.

The two hypotheses on `Q` are exactly what the rescaling argument uses: homogeneity returns
`U + tV` to the constraint set, and nonnegativity covers the vectors the constraint map kills. -/
theorem euler_lagrange_of_quadratic_min {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (hp1 : 1 < p.toReal) (T : H →L[ℝ] Lp ℝ p μ) {Q : H → ℝ} (hQnonneg : ∀ W : H, 0 ≤ Q W)
    (hQsmul : ∀ (c : ℝ) (W : H), Q (c • W) = c ^ 2 * Q W) {U V : H} {L S : ℝ}
    (hexp : ∀ t : ℝ, Q (U + t • V) = Q U + 2 * t * L + t ^ 2 * S) (hU : ‖T U‖ = 1)
    (hmin : ∀ W : H, ‖T W‖ = 1 → Q U ≤ Q W) :
    L = Q U * ∫ x, |(T U) x| ^ (p.toReal - 2) * (T U) x * (T V) x ∂μ := by
  simp only [← Real.norm_eq_abs]
  set r := p.toReal with hrdef
  have hr0 : (0 : ℝ) < r := by linarith
  set u := ⇑(T U) with hudef
  set v := ⇑(T V) with hvdef
  set I : ℝ := ∫ x, ‖u x‖ ^ (r - 2) * u x * v x ∂μ with hIdef
  -- The constraint along the line, and its derivative at the origin.
  set N : ℝ → ℝ := fun t => ∫ x, ‖u x + t * v x‖ ^ r ∂μ with hNdef
  have hNderiv : HasDerivAt N (∫ x, r * ‖u x‖ ^ (r - 2) * u x * v x ∂μ) 0 := by
    have := hasDerivAt_integral_abs_rpow (μ := μ) hp0 hptop hp1 (Lp.memLp (T U))
      (Lp.memLp (T V))
    simpa only [← Real.norm_eq_abs, hNdef, hudef, hvdef] using this
  have hIeq : (∫ x, r * ‖u x‖ ^ (r - 2) * u x * v x ∂μ) = r * I := by
    rw [hIdef, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall (fun x => by ring))
  rw [hIeq] at hNderiv
  -- The line's image is the line of the images.
  have hcoe : ∀ t : ℝ, ⇑(T (U + t • V)) =ᵐ[μ] fun x => u x + t * v x := by
    intro t
    have h0 : T (U + t • V) = T U + t • T V := by rw [map_add, map_smul]
    rw [h0]
    filter_upwards [Lp.coeFn_add (T U) (t • T V), Lp.coeFn_smul t (T V)] with x h1 h2
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, hudef, hvdef]
  have hNeq : ∀ t : ℝ, N t = ‖T (U + t • V)‖ ^ r := by
    intro t
    rw [norm_lp_rpow_eq_integral hp0 hptop]
    exact (integral_congr_ae (by filter_upwards [hcoe t] with x hx; rw [hx])).symm
  -- The squared `L^q` norm along the line.
  have hgN : ∀ t : ℝ, N t ^ (2 / r) = ‖T (U + t • V)‖ ^ 2 := by
    intro t
    rw [hNeq t, ← Real.rpow_mul (norm_nonneg _), show r * (2 / r) = 2 by field_simp,
      rpow_two_eq_sq _]
  have hN0 : N 0 = 1 := by rw [hNeq 0]; simp [hU]
  -- The function Fermat's theorem is applied to.
  set g : ℝ → ℝ := fun t => Q (U + t • V) - Q U * N t ^ (2 / r) with hgdef
  have hg0 : g 0 = 0 := by rw [hgdef]; simp [hN0]
  have hgnonneg : ∀ t : ℝ, 0 ≤ g t := by
    intro t
    rw [hgdef]
    simp only [hgN t]
    rcases eq_or_ne ‖T (U + t • V)‖ 0 with h0 | h0
    · rw [h0]
      simpa using hQnonneg (U + t • V)
    · have hpos : 0 < ‖T (U + t • V)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have hsphere : ‖T (‖T (U + t • V)‖⁻¹ • (U + t • V))‖ = 1 := by
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
        exact inv_mul_cancel₀ hpos.ne'
      have hle := hmin _ hsphere
      rw [hQsmul] at hle
      have hs2 : (0 : ℝ) < ‖T (U + t • V)‖ ^ 2 := by positivity
      refine sub_nonneg.mpr ?_
      calc Q U * ‖T (U + t • V)‖ ^ 2
          ≤ (‖T (U + t • V)‖⁻¹) ^ 2 * Q (U + t • V) * ‖T (U + t • V)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hle hs2.le
        _ = Q (U + t • V) := by field_simp
  -- Fermat's theorem at the global minimum.
  have hlocmin : IsLocalMin g 0 :=
    Eventually.of_forall (fun t => by rw [hg0]; exact hgnonneg t)
  have hgderiv : HasDerivAt g (2 * L - Q U * (r * I * (2 / r) * N 0 ^ (2 / r - 1))) 0 := by
    have hE : HasDerivAt (fun t : ℝ => Q (U + t • V)) (2 * L) 0 := by
      have hpoly : HasDerivAt (fun t : ℝ => Q U + 2 * t * L + t ^ 2 * S)
          (0 + 2 * 1 * L + 2 * 0 ^ 1 * S) 0 :=
        (((hasDerivAt_const (0 : ℝ) (Q U)).add
          (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const L)).add
          ((hasDerivAt_pow 2 (0 : ℝ)).mul_const S))
      have hpoly' : HasDerivAt (fun t : ℝ => Q U + 2 * t * L + t ^ 2 * S) (2 * L) 0 := by
        convert hpoly using 1
        norm_num
      exact hpoly'.congr_of_eventuallyEq (Eventually.of_forall (fun t => hexp t))
    have hNpow : HasDerivAt (fun t : ℝ => N t ^ (2 / r))
        (r * I * (2 / r) * N 0 ^ (2 / r - 1)) 0 :=
      hNderiv.rpow_const (Or.inl (by rw [hN0]; norm_num))
    exact hE.sub (hNpow.const_mul (Q U))
  have hzero := hlocmin.hasDerivAt_eq_zero hgderiv
  rw [hN0, Real.one_rpow, mul_one] at hzero
  have hcancel : r * I * (2 / r) = 2 * I := by field_simp
  rw [hcancel] at hzero
  linarith

/-- **Euler-Lagrange equation of a bilinear minimiser under an `L^q` constraint.** For a
symmetric positive semidefinite `B`, a minimiser of `B[·, ·]` on the unit `L^q` sphere satisfies

`B[U, V] = B[U, U] ∫ |TU|^{q-2} (TU) (TV)`.

At the bilinear form of the Laplacian on `H₀¹(Ω)` this is the weak form of `-Δu = λ|u|^{q-2}u`, with
`λ = ∫ |∇u|²`. -/
theorem euler_lagrange_of_bilin_min {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (hp1 : 1 < p.toReal) (T : H →L[ℝ] Lp ℝ p μ) (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hsymm : ∀ W Z : H, B W Z = B Z W) (hpsd : ∀ W : H, 0 ≤ B W W) {U : H} (hU : ‖T U‖ = 1)
    (hmin : ∀ W : H, ‖T W‖ = 1 → B U U ≤ B W W) (V : H) :
    B U V = B U U * ∫ x, |(T U) x| ^ (p.toReal - 2) * (T U) x * (T V) x ∂μ := by
  refine euler_lagrange_of_quadratic_min hp0 hptop hp1 T (Q := fun W => B W W) hpsd
    (fun c W => by
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
      ring)
    (L := B U V) (S := B V V) (fun t => ?_) hU hmin
  have h1 : B (U + t • V) = B U + t • B V := by rw [map_add, map_smul]
  simp only [h1, _root_.add_apply, _root_.smul_apply, map_add, map_smul,
    smul_eq_mul]
  rw [hsymm V U]
  ring

end Quadratic

/-! ### The equation for the norm -/

section Inner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Euler-Lagrange equation of a norm minimiser under an `L^q` constraint.** If `U`
minimises `‖·‖` over the vectors whose image has unit `L^q` norm, then for every `V`

`⟪U, V⟫ = ‖U‖² ∫ |TU|^{q-2} (TU) (TV)`.

The multiplier is the square of the minimum, so the equation names its own constant. -/
theorem euler_lagrange_of_norm_min {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (hp1 : 1 < p.toReal) (T : H →L[ℝ] Lp ℝ p μ) {U : H} (hU : ‖T U‖ = 1)
    (hmin : ∀ W : H, ‖T W‖ = 1 → ‖U‖ ≤ ‖W‖) (V : H) :
    ⟪U, V⟫ = ‖U‖ ^ 2 * ∫ x, |(T U) x| ^ (p.toReal - 2) * (T U) x * (T V) x ∂μ := by
  refine euler_lagrange_of_quadratic_min hp0 hptop hp1 T (Q := fun W => ‖W‖ ^ 2)
    (fun W => by positivity)
    (fun c W => by rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs])
    (L := ⟪U, V⟫) (S := ‖V‖ ^ 2) (fun t => ?_) hU
    (fun W hW => by nlinarith [hmin W hW, norm_nonneg U, norm_nonneg W])
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    real_inner_add_add_self, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right]
  ring

end Inner

end EllipticPdes.Analysis
