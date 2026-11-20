/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.HilleYosida.OperatorExp
public import LeanPool.FastDynamo.Dynamics.HilleYosida.YosidaApproximant
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The approximant semigroups of a Hille–Yosida generator

The Yosida approximant `A_r` of `YosidaApproximant.lean` is a bounded operator, so it
generates a one-parameter group `t ↦ exp (t A_r)` of bounded operators, the
*approximant semigroup*.  This module proves everything about that family that the
passage to the limit `r → ∞` consumes.

* **Semigroup law and smoothness.**  `approx_zero`, `approx_add`,
  `hasDerivAt_approx_apply`, `continuous_approx_apply` and
  `approx_sub_self_eq_integral`; the last is the integrated form
  `exp (t A_r) x - x = ∫₀ᵗ exp (s A_r) (A_r x) ds`, the identity that survives the limit
  and produces the derivative of the limit orbit at the endpoint `t = 0`.

* **The uniform bound.**  `norm_approx_le` is the sharp estimate
  `‖exp (t A_r)‖ ≤ exp (t M r / (r - M))` for `t ≥ 0`.  It is *not* obtained from
  `‖A_r‖`, which grows like `r`, but from the split `A_r = r ^ 2 R(r) - r` of the
  definition: the shift contributes the decaying factor `exp (-t r)` and the resolvent
  term only `exp (t r ^ 2 / (r - M))`, and the two combine into the finite limit
  `M r / (r - M) → M`.  `norm_approx_le_uniform` degrades it to the crude bound
  `exp (2 |M| T)` valid on `[0, T]` for every `r` past the threshold
  `max (2 |M|) 1 + 1` of `HilleYosidaRay.lt_of_le_threshold` — a bound uniform in `r`,
  which is what a convergence argument needs.

* **Commutation.**  `commute_approx_yosida` and `commute_approx_stateResolvent`: the
  approximant semigroups commute with every Yosida approximant and with every resolvent
  on the ray.  The first is what collapses the interpolation of the Cauchy estimate to a
  single operator applied to `A_r x - A_s x`.

* **The Cauchy estimate** `norm_approx_sub_approx_le`:
  `‖exp (t A_r) x - exp (t A_s) x‖ ≤ T exp (2 |M| T) ^ 2 ‖A_r x - A_s x‖` for
  `0 ≤ t ≤ T`.  Two approximant semigroups are compared by differentiating the
  interpolation `u ↦ exp ((t - u) A_s) (exp (u A_r) x)` — `hasDerivAt_conjugate` of
  `OperatorExp.lean` — collapsing the two resulting terms with the commutation lemmas,
  and integrating the derivative with the mean value inequality
  `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` over `[0, t]`.  On the domain the
  right-hand side tends to `0` by `tendsto_yosida_embedding`, so this is the estimate
  that makes the approximants a Cauchy family and produces the limit semigroup.

The time variable is real throughout and the operators stay complex-linear; the
statements are therefore about the real scalar action on `X →L[ℂ] X`, as in
`YosidaApproximant.lean`.
-/

@[expose] public section

namespace FastDynamo

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D}

/--
The approximant semigroup `exp (t A_r)` of the Yosida approximant at parameter `r`,
a bounded operator on the ambient space for every real time `t`.

The generator `A_r` is bounded, so the exponential series converges in operator norm and
the family is defined — and is a group — for all real `t`; only `t ≥ 0` is used
downstream, where the uniform bound `norm_approx_le` holds.
-/
noncomputable def HilleYosidaRay.approx {M : ℝ} (hy : HilleYosidaRay A M) (r t : ℝ) :
    X →L[ℂ] X :=
  NormedSpace.exp (t • hy.yosida r)

omit [CompleteSpace X] in
/-- The approximant semigroup starts at the identity.  Completeness of `X` is not
needed. -/
theorem approx_zero {M : ℝ} (hy : HilleYosidaRay A M) (r : ℝ) :
    hy.approx r 0 = ContinuousLinearMap.id ℂ X := by
  rw [HilleYosidaRay.approx, zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_def]

/-- The semigroup law of the approximants, `exp ((s + t) A_r) = exp (s A_r) exp (t A_r)`:
the two factors are exponentials of commuting operators, both real multiples of `A_r`. -/
theorem approx_add {M : ℝ} (hy : HilleYosidaRay A M) (r s t : ℝ) :
    hy.approx r (s + t) = (hy.approx r s).comp (hy.approx r t) := by
  simp only [HilleYosidaRay.approx]
  rw [HilleYosida.exp_add_smul, ContinuousLinearMap.mul_def]

/--
The sharp bound on the approximant semigroup:
`‖exp (t A_r)‖ ≤ exp (t M r / (r - M))` for `0 < r` to the right of `M` and `t ≥ 0`.

The proof never bounds `‖A_r‖` — that grows like `r` and would give a useless estimate.
Instead it splits the generator as `t A_r = (t r ^ 2) R(r) - (t r) 1` and applies
`HilleYosida.norm_exp_sub_smul_one_le`: the shift contributes `exp (-t r)` exactly, the
resolvent term contributes at most `exp (t r ^ 2 / (r - M))` by the Hille–Yosida bound,
and `-t r + t r ^ 2 / (r - M) = t M r / (r - M)`.  As `r → ∞` the exponent tends to
`t M`, which is the growth bound of the generated semigroup.
-/
theorem norm_approx_le {M : ℝ} (hy : HilleYosidaRay A M) {r t : ℝ} (hr : M < r) (h0 : 0 < r)
    (ht : 0 ≤ t) : ‖hy.approx r t‖ ≤ Real.exp (t * (M * r / (r - M))) := by
  have hrM : 0 < r - M := sub_pos.mpr hr
  have hne : r - M ≠ 0 := ne_of_gt hrM
  have hcoef : 0 ≤ t * r ^ 2 := mul_nonneg ht (pow_nonneg h0.le 2)
  have hsplit : t • hy.yosida r
      = (t * r ^ 2 : ℝ) • hy.resolvent.stateResolvent (r : ℂ)
        - (t * r : ℝ) • (1 : X →L[ℂ] X) := by
    simp only [HilleYosidaRay.yosida, smul_sub, smul_smul, ContinuousLinearMap.one_def]
  have hnorm : ‖(t * r ^ 2 : ℝ) • hy.resolvent.stateResolvent (r : ℂ)‖
      ≤ t * r ^ 2 / (r - M) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (hy.norm_stateResolvent_le r hr) hcoef
  rw [HilleYosidaRay.approx, hsplit]
  refine le_trans (HilleYosida.norm_exp_sub_smul_one_le _ (t * r)) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hnorm)
    (Real.exp_pos (-(t * r))).le) ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr (le_of_eq ?_)
  field_simp
  ring

/--
The crude bound that is uniform in the parameter: `‖exp (t A_r)‖ ≤ exp (2 |M| T)` for
`0 ≤ t ≤ T` and every `r` past the threshold `max (2 |M|) 1 + 1`.

Past that threshold `r / (r - M) ≤ 2` by `HilleYosidaRay.lt_of_le_threshold`, so the
sharp exponent `M r / (r - M)` of `norm_approx_le` is at most `2 |M|` — uniformly in
`r`, which is what every limit argument on the approximants needs.
-/
theorem norm_approx_le_uniform {M : ℝ} (hy : HilleYosidaRay A M) {r t T : ℝ}
    (hr : max (2 * |M|) 1 + 1 ≤ r) (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖hy.approx r t‖ ≤ Real.exp (2 * |M| * T) := by
  obtain ⟨hlt, hratio⟩ := HilleYosidaRay.lt_of_le_threshold hr
  have hone : (1 : ℝ) ≤ max (2 * |M|) 1 := le_max_right _ _
  have h0 : 0 < r := by linarith
  have hrM : 0 < r - M := sub_pos.mpr hlt
  have hq0 : 0 ≤ r / (r - M) := (div_pos h0 hrM).le
  have hMq : M * r / (r - M) ≤ 2 * |M| := by
    rw [mul_div_assoc]
    calc M * (r / (r - M))
        ≤ |M| * (r / (r - M)) := mul_le_mul_of_nonneg_right (le_abs_self M) hq0
      _ ≤ |M| * 2 := mul_le_mul_of_nonneg_left hratio (abs_nonneg M)
      _ = 2 * |M| := mul_comm _ _
  refine le_trans (norm_approx_le hy hlt h0 ht) (Real.exp_le_exp.mpr ?_)
  calc t * (M * r / (r - M))
      ≤ t * (2 * |M|) := mul_le_mul_of_nonneg_left hMq ht
    _ ≤ T * (2 * |M|) := mul_le_mul_of_nonneg_right htT (by positivity)
    _ = 2 * |M| * T := by ring

/-- The orbit `t ↦ exp (t A_r) x` of a vector solves the Cauchy problem of the bounded
generator `A_r`: it is differentiable at every real time with derivative
`exp (t A_r) (A_r x)`. -/
theorem hasDerivAt_approx_apply {M : ℝ} (hy : HilleYosidaRay A M) (r t : ℝ) (x : X) :
    HasDerivAt (fun u : ℝ ↦ hy.approx r u x) (hy.approx r t (hy.yosida r x)) t :=
  HilleYosida.hasDerivAt_exp_apply (hy.yosida r) t x

/-- The orbit of a vector under an approximant semigroup is continuous in time; this is
the continuity that the uniform limit `r → ∞` inherits. -/
theorem continuous_approx_apply {M : ℝ} (hy : HilleYosidaRay A M) (r : ℝ) (x : X) :
    Continuous fun t : ℝ ↦ hy.approx r t x :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_approx_apply hy r t x).continuousAt

/--
The integrated form of the Cauchy problem,
`exp (t A_r) x - x = ∫₀ᵗ exp (s A_r) (A_r x) ds`, by the fundamental theorem of calculus
applied to `hasDerivAt_approx_apply` (the integrand is continuous, hence interval
integrable).

This identity, and not the differential one, is what passes to the limit `r → ∞`: the
limit semigroup is only differentiable on the domain and only from the right at `t = 0`,
whereas the integrated identity holds for it verbatim.
-/
theorem approx_sub_self_eq_integral {M : ℝ} (hy : HilleYosidaRay A M) (r t : ℝ) (x : X) :
    hy.approx r t x - x = ∫ s in (0 : ℝ)..t, hy.approx r s (hy.yosida r x) := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun v : ℝ ↦ hy.approx r v x) (hy.approx r u (hy.yosida r x)) u :=
    fun u _ ↦ hasDerivAt_approx_apply hy r u x
  have hint : IntervalIntegrable (fun u : ℝ ↦ hy.approx r u (hy.yosida r x))
      MeasureTheory.volume 0 t :=
    (continuous_approx_apply hy r (hy.yosida r x)).intervalIntegrable 0 t
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, approx_zero hy r,
    ContinuousLinearMap.id_apply]

omit [CompleteSpace X] in
/-- An approximant semigroup commutes with every Yosida approximant on the ray, because
the two generators commute.  Completeness of `X` is not needed. -/
theorem commute_approx_yosida {M : ℝ} (hy : HilleYosidaRay A M) {r s : ℝ} (hr : M < r)
    (hs : M < s) (t : ℝ) : Commute (hy.approx r t) (hy.yosida s) :=
  HilleYosida.exp_commute (commute_yosida hy hr hs) t

omit [CompleteSpace X] in
/-- An approximant semigroup commutes with every resolvent on the ray.  This commutation
is preserved by the strong limit `r → ∞` and is what makes the limit semigroup leave the
domain invariant.  Completeness of `X` is not needed. -/
theorem commute_approx_stateResolvent {M : ℝ} (hy : HilleYosidaRay A M) {r s : ℝ}
    (hr : M < r) (hs : M < s) (t : ℝ) :
    Commute (hy.approx r t) (hy.resolvent.stateResolvent (s : ℂ)) :=
  HilleYosida.exp_commute (commute_yosida_stateResolvent hy hr hs) t

/--
The Cauchy estimate comparing two approximant semigroups on a single vector:
`‖exp (t A_r) x - exp (t A_s) x‖ ≤ T exp (2 |M| T) ^ 2 ‖A_r x - A_s x‖` for `0 ≤ t ≤ T`
and both parameters past the uniform threshold `max (2 |M|) 1 + 1`.

The interpolation `u ↦ exp ((t - u) A_s) (exp (u A_r) x)` joins `exp (t A_s) x` at
`u = 0` to `exp (t A_r) x` at `u = t`; its derivative, computed by
`HilleYosida.hasDerivAt_conjugate`, is
`exp ((t - u) A_s) (exp (u A_r) (A_r x - A_s x))` once the commutation
`commute_approx_yosida` has moved `A_s` across `exp (u A_r)`, so it is bounded by
`exp (2 |M| T) ^ 2 ‖A_r x - A_s x‖` uniformly on `[0, t]` by `norm_approx_le_uniform`.
The mean value inequality on the interval `[0, t]` then gives the claim, with the factor
`t ≤ T`.

On the range of the embedding the right-hand side tends to `0` as `r, s → ∞` by
`tendsto_yosida_embedding`; with the uniform bound and density this is what makes the
approximants converge.
-/
theorem norm_approx_sub_approx_le {M : ℝ} (hy : HilleYosidaRay A M) {t T : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) {r s : ℝ} (hr : max (2 * |M|) 1 + 1 ≤ r) (hs : max (2 * |M|) 1 + 1 ≤ s)
    (x : X) :
    ‖hy.approx r t x - hy.approx s t x‖
      ≤ T * Real.exp (2 * |M| * T) ^ 2 * ‖hy.yosida r x - hy.yosida s x‖ := by
  obtain ⟨hlr, -⟩ := HilleYosidaRay.lt_of_le_threshold hr
  obtain ⟨hls, -⟩ := HilleYosidaRay.lt_of_le_threshold hs
  have hbound : ∀ u ∈ Set.Icc (0 : ℝ) t,
      ‖-(NormedSpace.exp ((t - u) • hy.yosida s)
            (hy.yosida s (NormedSpace.exp (u • hy.yosida r) x)))
        + NormedSpace.exp ((t - u) • hy.yosida s)
            (NormedSpace.exp (u • hy.yosida r) (hy.yosida r x))‖
        ≤ Real.exp (2 * |M| * T) ^ 2 * ‖hy.yosida r x - hy.yosida s x‖ := by
    rintro u ⟨hu0, hut⟩
    have hcomm : NormedSpace.exp (u • hy.yosida r) (hy.yosida s x)
        = hy.yosida s (NormedSpace.exp (u • hy.yosida r) x) := by
      simpa [HilleYosidaRay.approx, mul_apply_eq_comp] using
        DFunLike.congr_fun (commute_approx_yosida hy hlr hls u) x
    have hrw : -(NormedSpace.exp ((t - u) • hy.yosida s)
            (hy.yosida s (NormedSpace.exp (u • hy.yosida r) x)))
        + NormedSpace.exp ((t - u) • hy.yosida s)
            (NormedSpace.exp (u • hy.yosida r) (hy.yosida r x))
        = hy.approx s (t - u) (hy.approx r u (hy.yosida r x - hy.yosida s x)) := by
      simp only [HilleYosidaRay.approx, map_sub, ← hcomm]
      abel
    rw [hrw]
    have h2 : ‖hy.approx r u (hy.yosida r x - hy.yosida s x)‖
        ≤ Real.exp (2 * |M| * T) * ‖hy.yosida r x - hy.yosida s x‖ :=
      le_trans (ContinuousLinearMap.le_opNorm _ _)
        (mul_le_mul_of_nonneg_right (norm_approx_le_uniform hy hr hu0 (by linarith))
          (norm_nonneg _))
    have h1 : ‖hy.approx s (t - u) (hy.approx r u (hy.yosida r x - hy.yosida s x))‖
        ≤ Real.exp (2 * |M| * T) * ‖hy.approx r u (hy.yosida r x - hy.yosida s x)‖ :=
      le_trans (ContinuousLinearMap.le_opNorm _ _)
        (mul_le_mul_of_nonneg_right
          (norm_approx_le_uniform hy hs (by linarith) (by linarith)) (norm_nonneg _))
    calc ‖hy.approx s (t - u) (hy.approx r u (hy.yosida r x - hy.yosida s x))‖
        ≤ Real.exp (2 * |M| * T)
            * (Real.exp (2 * |M| * T) * ‖hy.yosida r x - hy.yosida s x‖) :=
          le_trans h1 (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
      _ = Real.exp (2 * |M| * T) ^ 2 * ‖hy.yosida r x - hy.yosida s x‖ := by ring
  have hmain : ‖hy.approx r t x - hy.approx s t x‖
      ≤ Real.exp (2 * |M| * T) ^ 2 * ‖hy.yosida r x - hy.yosida s x‖ * ‖t - 0‖ := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u : ℝ ↦ HilleYosida.expR (hy.yosida s) (t - u)
        (NormedSpace.exp (u • hy.yosida r) x))
      (f' := fun u : ℝ ↦ -(NormedSpace.exp ((t - u) • hy.yosida s)
            (hy.yosida s (NormedSpace.exp (u • hy.yosida r) x)))
          + NormedSpace.exp ((t - u) • hy.yosida s)
            (NormedSpace.exp (u • hy.yosida r) (hy.yosida r x)))
      (fun u _ ↦ (HilleYosida.hasDerivAt_conjugate (hy.yosida r) (hy.yosida s) t x
        u).hasDerivWithinAt)
      hbound (convex_Icc 0 t) (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht)
    simpa [HilleYosida.expR, HilleYosidaRay.approx] using h
  calc ‖hy.approx r t x - hy.approx s t x‖
      ≤ Real.exp (2 * |M| * T) ^ 2 * ‖hy.yosida r x - hy.yosida s x‖ * ‖t - 0‖ := hmain
    _ = Real.exp (2 * |M| * T) ^ 2 * ‖hy.yosida r x - hy.yosida s x‖ * t := by
        rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg ht]
    _ ≤ Real.exp (2 * |M| * T) ^ 2 * ‖hy.yosida r x - hy.yosida s x‖ * T :=
        mul_le_mul_of_nonneg_left htT (by positivity)
    _ = T * Real.exp (2 * |M| * T) ^ 2 * ‖hy.yosida r x - hy.yosida s x‖ := by ring

end FastDynamo
