/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.LiteralTorusRepresentative

/-!
# Fourier coefficients of the partial derivatives of a test function on `T³`

This module supplies the analytic half of step (S1) — gradients of test functions are
orthogonal to `L²_σ(T³)`, `FastDynamo/Dynamics/Ideal/GradientOrthogonality.lean` — of the
solenoidality argument of `cor:ideal-growth` (the paragraph of its proof showing that the Cauchy
formula preserves the divergence constraint): the integration by parts

```
  ∫_{T³} (∂ⱼ w) · conj(e_m) = 2πi mⱼ ∫_{T³} w · conj(e_m)
```

for a test function `w` on the literal three-torus whose periodic lift to `ℝ³` is `C¹` — the
paper's own device, the periodic lift (proof of `cor:ideal-growth`).

`Torus 3` is not a normed space, so a derivative of `w` only makes sense on a lift.  The lift is
canonical: composing `w` with the quotient `literalTorusPoint : ℝ³ → T³`
(`FastDynamo/Analysis/LiteralThreeTorus.lean`) gives `torusLift w`, automatically `ℤ³`-periodic,
and
`torusGradient w x i` is the `i`-th partial derivative of `torusLift w`, read at the canonical
`(0,1]³` representative of `x`.  Periodicity makes the choice of representative irrelevant
(`torusGradient_literalTorusPoint`), and the representative is a *measurable* section of the
quotient, which is what makes `torusGradient w · i` a measurable function on the torus without
any quotient-topology argument.

The integration by parts itself is proved without Fubini and without a fundamental-domain
computation, by translating the argument of `w` along the `i`-th axis: the torus volume is
translation invariant, so

```
  J(s) := ∫ conj(e_m(x)) w(x + s eᵢ) dx = e^{2πi mᵢ s} J(0)
```

exactly, and differentiating this identity at `s = 0` — the difference quotients are dominated
by a constant, by the mean value inequality on a compact ball — gives the stated formula.

## Contents

* **Lifts and gradients.**  `torusLift`, `torusGradient`, `torusGradient_literalTorusPoint`,
  measurability and boundedness, `memLp` membership of `w` and of its partial derivatives.
* **Characters.**  `norm_mFourier_apply`, `mFourier_add_point`, `mFourier_literalTorusPoint`
  and the value of a character on an axis translation.
* **Integration by parts.**  `integral_conj_mFourier_mul_torusGradient`, and its form
  `integral_conj_mFourier_mul_torusGradient_of_increment` for differentiable lifts with bounded
  axis increments (Lipschitz lifts), used for the Lipschitz test fields of the weak form
  (`FastDynamo/Dynamics/Ideal/LipschitzTestFields.lean`).
* **The `L²` dictionary.**  `flatTorus3FourierBasis_eq_toLp`, `flatTorus3FourierBasis_coe_ae`
  and `inner_flatTorus3FourierBasis`, which turn the basis pairing into an integral.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-! ## Lifts of functions on the torus, and the torus gradient -/

/-- The canonical `ℤ³`-periodic lift to `ℝ³` of a function on the literal three-torus: compose
with the quotient.  Any lift in the sense of `hlift : ∀ a, w (literalTorusPoint a) = W a`
*is* this one. -/
def torusLift (w : Torus 3 → ℂ) : R3 → ℂ := fun a ↦ w (literalTorusPoint a)

/-- The lift read at the canonical representative returns the original function. -/
@[simp] theorem torusLift_literalIocRepresentative (w : Torus 3 → ℂ) (x : Torus 3) :
    torusLift w (literalIocRepresentative x) = w x := by
  rw [torusLift, literalTorusPoint_literalIocRepresentative]

/-- A function on the torus with a continuous lift is measurable: it is the composition of the
lift with the measurable section. -/
theorem measurable_of_continuous_torusLift {w : Torus 3 → ℂ}
    (hw : Continuous (torusLift w)) : Measurable w := by
  have h : w = fun x ↦ torusLift w (literalIocRepresentative x) := by
    funext x
    rw [torusLift_literalIocRepresentative]
  rw [h]
  exact hw.measurable.comp measurable_literalIocRepresentative

/-- The lift is invariant under every translation that the quotient kills. -/
theorem torusLift_add_of_literalTorusPoint_eq_zero (w : Torus 3 → ℂ) {v : R3}
    (hv : literalTorusPoint v = 0) (a : R3) :
    torusLift w (a + v) = torusLift w a := by
  rw [torusLift, torusLift, literalTorusPoint_add, hv, add_zero]

/-- The derivative of the lift only depends on the point of the torus: two representatives of
the same point give the same Fréchet derivative. -/
theorem fderiv_torusLift_congr (w : Torus 3 → ℂ) {a b : R3}
    (hab : literalTorusPoint a = literalTorusPoint b) :
    fderiv ℝ (torusLift w) a = fderiv ℝ (torusLift w) b := by
  have hv : literalTorusPoint (b - a) = 0 := by
    rw [sub_eq_add_neg, literalTorusPoint_add, literalTorusPoint_neg, hab, add_neg_cancel]
  have h1 : fderiv ℝ (fun x ↦ torusLift w (x + (b - a))) a
      = fderiv ℝ (torusLift w) (a + (b - a)) :=
    fderiv_comp_add_right (f := torusLift w) (x := a) (b - a)
  rw [add_sub_cancel] at h1
  rw [← h1]
  simp only [torusLift_add_of_literalTorusPoint_eq_zero w hv]

/-- **The `i`-th partial derivative of a function on the literal three-torus**, read on its
canonical periodic lift at the canonical `(0,1]³` representative of the point.  By
`torusGradient_literalTorusPoint` the representative may be replaced by any lift of the point. -/
def torusGradient (w : Torus 3 → ℂ) (x : Torus 3) (i : Fin 3) : ℂ :=
  fderiv ℝ (torusLift w) (literalIocRepresentative x) (EuclideanSpace.single i 1)

/-- The torus gradient at the class of `a` is the directional derivative of the lift at `a`:
the defining choice of representative is immaterial.  **This is the identity a consumer uses to
compute `torusGradient` from an explicit lift.** -/
theorem torusGradient_literalTorusPoint (w : Torus 3 → ℂ) (a : R3) (i : Fin 3) :
    torusGradient w (literalTorusPoint a) i =
      fderiv ℝ (torusLift w) a (EuclideanSpace.single i 1) := by
  rw [torusGradient,
    fderiv_torusLift_congr w
      (b := a) (literalTorusPoint_literalIocRepresentative (literalTorusPoint a))]

/-- If the lift is `C¹` then each partial derivative is a measurable function on the torus. -/
theorem measurable_torusGradient {w : Torus 3 → ℂ} (hw : ContDiff ℝ 1 (torusLift w))
    (i : Fin 3) : Measurable fun x ↦ torusGradient w x i := by
  have hcont : Continuous fun a : R3 ↦ fderiv ℝ (torusLift w) a (EuclideanSpace.single i 1) :=
    (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))).continuous.comp
      (hw.continuous_fderiv one_ne_zero)
  exact hcont.measurable.comp measurable_literalIocRepresentative

/-- If the lift is `C¹` then each partial derivative is bounded on the torus. -/
theorem exists_bound_torusGradient {w : Torus 3 → ℂ} (hw : ContDiff ℝ 1 (torusLift w))
    (i : Fin 3) : ∃ M : ℝ, ∀ x : Torus 3, ‖torusGradient w x i‖ ≤ M :=
  exists_bound_comp_literalIocRepresentative
    ((ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))).continuous.comp
      (hw.continuous_fderiv one_ne_zero))

/-- A bounded measurable function on the torus is integrable, the volume being finite. -/
theorem torusIntegrable_of_bound {g : Torus 3 → ℂ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ x, ‖g x‖ ≤ C) : Integrable g (volume : Measure (Torus 3)) :=
  (integrable_const C).mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- A bounded measurable function on the torus is square integrable. -/
theorem torusMemLp_of_bound {g : Torus 3 → ℂ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ x, ‖g x‖ ≤ C) : MemLp g 2 (volume : Measure (Torus 3)) :=
  MemLp.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-- A function on the torus with a continuous lift is square integrable. -/
theorem memLp_of_continuous_torusLift {w : Torus 3 → ℂ} (hw : Continuous (torusLift w)) :
    MemLp w 2 (volume : Measure (Torus 3)) := by
  obtain ⟨M, hM⟩ := exists_bound_comp_literalIocRepresentative hw
  refine torusMemLp_of_bound (measurable_of_continuous_torusLift hw) (C := M) fun x ↦ ?_
  simpa using hM x

/-- Each partial derivative of a test function with a `C¹` lift is square integrable. -/
theorem memLp_torusGradient {w : Torus 3 → ℂ} (hw : ContDiff ℝ 1 (torusLift w)) (i : Fin 3) :
    MemLp (fun x ↦ torusGradient w x i) 2 (volume : Measure (Torus 3)) := by
  obtain ⟨M, hM⟩ := exists_bound_torusGradient hw i
  exact torusMemLp_of_bound (measurable_torusGradient hw i) hM

/-! ## Characters of the literal three-torus -/

/-- Characters have unit modulus at every point. -/
theorem norm_mFourier_apply (m : Fin 3 → ℤ) (x : Torus 3) :
    ‖UnitAddTorus.mFourier m x‖ = 1 := by
  simp [UnitAddTorus.mFourier, norm_prod, Circle.norm_coe]

/-- A character is multiplicative in the point: `e_m(x + y) = e_m(x) e_m(y)`. -/
theorem mFourier_add_point (m : Fin 3 → ℤ) (x y : Torus 3) :
    UnitAddTorus.mFourier m (x + y) =
      UnitAddTorus.mFourier m x * UnitAddTorus.mFourier m y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp only [Pi.add_apply, fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- The value of a character at the class of a point of `ℝ³` is the exponential of the
corresponding linear form. -/
theorem mFourier_literalTorusPoint (m : Fin 3 → ℤ) (a : R3) :
    UnitAddTorus.mFourier m (literalTorusPoint a) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, (m j : ℂ) * (a j : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, literalTorusPoint, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  push_cast
  ring

/-! ## Translation along a coordinate axis -/

/-- Translation of the literal three-torus by `t` along the `i`-th coordinate axis. -/
def torusAxisShift (i : Fin 3) (t : ℝ) : Torus 3 :=
  literalTorusPoint (EuclideanSpace.single i t)

/-- The zero translation is the identity. -/
@[simp] theorem torusAxisShift_zero (i : Fin 3) : torusAxisShift i 0 = 0 := by
  rw [torusAxisShift, show (EuclideanSpace.single i (0 : ℝ) : R3) = 0 by ext j; simp,
    literalTorusPoint_zero]

/-- The quotient turns an axis translation of a lift into an axis translation of the torus. -/
theorem literalTorusPoint_add_single (a : R3) (i : Fin 3) (t : ℝ) :
    literalTorusPoint (a + EuclideanSpace.single i t) =
      literalTorusPoint a + torusAxisShift i t := by
  rw [literalTorusPoint_add, torusAxisShift]

/-- The value of a character on an axis translation. -/
theorem mFourier_torusAxisShift (m : Fin 3 → ℤ) (i : Fin 3) (t : ℝ) :
    UnitAddTorus.mFourier m (torusAxisShift i t) =
      Complex.exp (2 * Real.pi * Complex.I * (m i : ℂ) * (t : ℂ)) := by
  rw [torusAxisShift, mFourier_literalTorusPoint]
  congr 1
  rw [Finset.sum_eq_single i]
  · rw [show (EuclideanSpace.single i t : R3) i = t by simp]
    ring
  · intro j _ hj
    rw [show (EuclideanSpace.single i t : R3) j = 0 by simp [hj]]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ## The derivative of a test function along a coordinate axis -/

/-- Along the `i`-th axis the test function has, at the parameter value `0`, exactly the
derivative recorded by `torusGradient`. -/
theorem hasDerivAt_torusAxisShift {w : Torus 3 → ℂ} (hw : Differentiable ℝ (torusLift w))
    (x : Torus 3) (i : Fin 3) :
    HasDerivAt (fun t : ℝ ↦ w (x + torusAxisShift i t)) (torusGradient w x i) 0 := by
  set a : R3 := literalIocRepresentative x with ha
  have hax : literalTorusPoint a = x := literalTorusPoint_literalIocRepresentative x
  have hfun : (fun t : ℝ ↦ w (x + torusAxisShift i t))
      = fun t : ℝ ↦ torusLift w (a + t • (EuclideanSpace.single i (1 : ℝ) : R3)) := by
    funext t
    rw [show (t • (EuclideanSpace.single i (1 : ℝ) : R3)) = EuclideanSpace.single i t by
      ext j; by_cases h : j = i <;> simp [h]]
    rw [torusLift, literalTorusPoint_add_single, hax]
  rw [hfun, torusGradient, ← ha]
  have hv : HasDerivAt (fun t : ℝ ↦ a + t • (EuclideanSpace.single i (1 : ℝ) : R3))
      (EuclideanSpace.single i (1 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (EuclideanSpace.single i (1 : ℝ) : R3)).const_add a
  have hdiff := (hw (a + (0 : ℝ) • (EuclideanSpace.single i (1 : ℝ) : R3))).hasFDerivAt
  have h2 := hdiff.comp_hasDerivAt 0 hv
  rw [zero_smul, add_zero] at h2
  exact h2

/-- **A uniform Lipschitz bound along the coordinate axes.**  The canonical representatives all
lie in a fixed compact ball, so the mean value inequality on that ball bounds every small axis
increment of the test function. -/
theorem exists_axis_increment_bound {w : Torus 3 → ℂ} (hw : ContDiff ℝ 1 (torusLift w)) :
    ∃ C : ℝ, ∀ (x : Torus 3) (i : Fin 3) (t : ℝ), |t| ≤ 1 →
      ‖w (x + torusAxisShift i t) - w x‖ ≤ C * |t| := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : R3) 4).exists_bound_of_continuousOn
    (hw.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨C, fun x i t ht ↦ ?_⟩
  set a : R3 := literalIocRepresentative x with ha
  have hax : literalTorusPoint a = x := literalTorusPoint_literalIocRepresentative x
  have hanorm : ‖a‖ ≤ 2 := norm_literalIocRepresentative_le x
  have hmemK : a ∈ Metric.closedBall (0 : R3) 4 := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hsingle : ‖(EuclideanSpace.single i t : R3)‖ = |t| := by simp
  have hmemK' : a + (EuclideanSpace.single i t : R3) ∈ Metric.closedBall (0 : R3) 4 := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc ‖a + (EuclideanSpace.single i t : R3)‖
        ≤ ‖a‖ + ‖(EuclideanSpace.single i t : R3)‖ := norm_add_le _ _
      _ ≤ 2 + 1 := by rw [hsingle]; linarith
      _ ≤ 4 := by norm_num
  have hbound := (convex_closedBall (0 : R3) 4).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := torusLift w) (f' := fun y ↦ fderiv ℝ (torusLift w) y)
    (fun y _ ↦ (hw.differentiable one_ne_zero y).hasFDerivAt.hasFDerivWithinAt)
    (fun y hy ↦ hC y hy) hmemK hmemK'
  rw [add_sub_cancel_left, hsingle] at hbound
  have hleft : torusLift w (a + (EuclideanSpace.single i t : R3))
      = w (x + torusAxisShift i t) := by
    rw [torusLift, literalTorusPoint_add_single, hax]
  have hright : torusLift w a = w x := by rw [torusLift, hax]
  rw [hleft, hright] at hbound
  exact hbound

/-! ## Integration by parts along a coordinate axis -/

/-- The slope at the origin of a complex-valued function of a real variable. -/
theorem slope_zero_eq_div_complex (f : ℝ → ℂ) (s : ℝ) : slope f 0 s = (f s - f 0) / (s : ℂ) := by
  change (s - 0)⁻¹ • (f s - f 0) = _
  rw [sub_zero, Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]

/-- **Integration by parts along the `i`-th coordinate axis.**  If a bounded continuous weight
`F` of unit modulus satisfies the exact translation law `F x = e^{b s} F(x + s eᵢ)` for every
`s`, then testing the `i`-th partial derivative of a function `w` against `F` multiplies the
test of `w` itself by `b`.  The function `w` only needs an everywhere differentiable lift and axis
increments bounded by `C |t|` (as for a Lipschitz lift).

This is the abstract form of step (i) of the solenoidality argument of `cor:ideal-growth`
(divergence-constraint paragraph of its proof).  No fundamental-domain computation and no Fubini
theorem enters: the torus volume is translation invariant, so `s ↦ ∫ F · w(· + s eᵢ)` equals
`e^{b s}` times its value at `s = 0`, and differentiating that identity at the origin — the
difference quotients being dominated by a constant — is the assertion. -/
theorem integral_mul_torusGradient_of_translation_of_increment {w : Torus 3 → ℂ}
    (hw : Differentiable ℝ (torusLift w))
    (hinc : ∃ C : ℝ, ∀ (x : Torus 3) (i : Fin 3) (t : ℝ), |t| ≤ 1 →
      ‖w (x + torusAxisShift i t) - w x‖ ≤ C * |t|)
    (i : Fin 3) {F : Torus 3 → ℂ} (hFcont : Continuous F)
    (hFnorm : ∀ x, ‖F x‖ = 1) {b : ℂ}
    (hFtrans : ∀ (s : ℝ) (x : Torus 3),
      F x = Complex.exp (b * (s : ℂ)) * F (x + torusAxisShift i s)) :
    (∫ x : Torus 3, F x * torusGradient w x i) = b * ∫ x : Torus 3, F x * w x := by
  have hwcont : Continuous (torusLift w) := hw.continuous
  have hwmeas : Measurable w := measurable_of_continuous_torusLift hwcont
  obtain ⟨M, hM⟩ := exists_bound_comp_literalIocRepresentative hwcont
  have hMw : ∀ x, ‖w x‖ ≤ M := fun x ↦ by simpa using hM x
  obtain ⟨C, hC⟩ := hinc
  -- integrability of every translate
  have hInt : ∀ s : ℝ, Integrable (fun x : Torus 3 ↦ F x * w (x + torusAxisShift i s))
      (volume : Measure (Torus 3)) := by
    intro s
    refine torusIntegrable_of_bound (C := M)
      (hFcont.measurable.mul (hwmeas.comp (measurable_add_const _))) fun x ↦ ?_
    rw [norm_mul, hFnorm, one_mul]
    exact hMw _
  have hInt0 : Integrable (fun x : Torus 3 ↦ F x * w x) (volume : Measure (Torus 3)) := by
    refine torusIntegrable_of_bound (C := M) (hFcont.measurable.mul hwmeas) fun x ↦ ?_
    rw [norm_mul, hFnorm, one_mul]
    exact hMw _
  -- the exact translation law for the tested integral
  have hJ : ∀ s : ℝ, (∫ x : Torus 3, F x * w (x + torusAxisShift i s))
      = Complex.exp (b * (s : ℂ)) * ∫ x : Torus 3, F x * w x := by
    intro s
    have hshift : ∀ x : Torus 3, F x * w (x + torusAxisShift i s)
        = (fun y : Torus 3 ↦ Complex.exp (b * (s : ℂ)) * (F y * w y))
            (x + torusAxisShift i s) := by
      intro x
      change F x * w (x + torusAxisShift i s)
        = Complex.exp (b * (s : ℂ)) * (F (x + torusAxisShift i s) * w (x + torusAxisShift i s))
      rw [← mul_assoc, ← hFtrans s x]
    have htrans : (∫ x : Torus 3, Complex.exp (b * (s : ℂ)) *
        (F (x + torusAxisShift i s) * w (x + torusAxisShift i s)))
        = ∫ y : Torus 3, Complex.exp (b * (s : ℂ)) * (F y * w y) :=
      integral_add_right_eq_self
        (fun y : Torus 3 ↦ Complex.exp (b * (s : ℂ)) * (F y * w y)) (torusAxisShift i s)
    calc (∫ x : Torus 3, F x * w (x + torusAxisShift i s))
        = ∫ x : Torus 3, Complex.exp (b * (s : ℂ)) *
            (F (x + torusAxisShift i s) * w (x + torusAxisShift i s)) :=
          integral_congr_ae (Filter.Eventually.of_forall hshift)
      _ = ∫ y : Torus 3, Complex.exp (b * (s : ℂ)) * (F y * w y) := htrans
      _ = Complex.exp (b * (s : ℂ)) * ∫ x : Torus 3, F x * w x := integral_const_mul _ _
  have hJ0 : (∫ x : Torus 3, F x * w (x + torusAxisShift i 0))
      = ∫ x : Torus 3, F x * w x := by simp
  -- the derivative of the tested integral at the origin
  have hderiv : HasDerivAt (fun s : ℝ ↦ ∫ x : Torus 3, F x * w (x + torusAxisShift i s))
      (b * ∫ x : Torus 3, F x * w x) 0 := by
    rw [funext hJ]
    have h1 : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ ↦ b * (s : ℂ)) (b * 1) 0 := h1.const_mul b
    simpa using h2.cexp.mul_const (∫ x : Torus 3, F x * w x)
  -- a sequence of nonzero parameters tending to zero
  have hτpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n ↦ by positivity
  have hτle : ∀ n : ℕ, |1 / ((n : ℝ) + 1)| ≤ 1 := by
    intro n
    rw [abs_of_pos (hτpos n), div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hτne : Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_one_div_add_atTop_nhds_zero_nat
      (Filter.Eventually.of_forall fun n ↦ (hτpos n).ne')
  -- first limit: the slope of the tested integral
  have hlim1 : Filter.Tendsto
      (fun n : ℕ ↦ ((∫ x : Torus 3, F x * w (x + torusAxisShift i (1 / ((n : ℝ) + 1))))
          - ∫ x : Torus 3, F x * w x) / ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
      Filter.atTop (nhds (b * ∫ x : Torus 3, F x * w x)) := by
    refine ((hasDerivAt_iff_tendsto_slope.mp hderiv).comp hτne).congr fun n ↦ ?_
    rw [Function.comp_apply, slope_zero_eq_div_complex, hJ0]
  -- second limit: dominated convergence of the difference quotients
  have hlim2 : Filter.Tendsto
      (fun n : ℕ ↦ ∫ x : Torus 3, F x *
          ((w (x + torusAxisShift i (1 / ((n : ℝ) + 1))) - w x) /
            ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)))
      Filter.atTop (nhds (∫ x : Torus 3, F x * torusGradient w x i)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ ↦ C) (fun n ↦ ?_)
      (integrable_const C) (fun n ↦ ?_) ?_
    · exact ((hFcont.measurable.mul (((hwmeas.comp (measurable_add_const _)).sub
        hwmeas).div_const _))).aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul, hFnorm, one_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        div_le_iff₀ (abs_pos.mpr (hτpos n).ne')]
      exact hC x i _ (hτle n)
    · filter_upwards with x
      have hd := hasDerivAt_torusAxisShift hw x i
      refine Filter.Tendsto.const_mul (F x)
        (((hasDerivAt_iff_tendsto_slope.mp hd).comp hτne).congr fun n ↦ ?_)
      rw [Function.comp_apply, slope_zero_eq_div_complex]
      simp
  -- the two limits agree
  have hEq : ∀ n : ℕ, (∫ x : Torus 3, F x *
      ((w (x + torusAxisShift i (1 / ((n : ℝ) + 1))) - w x) /
        ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)))
      = ((∫ x : Torus 3, F x * w (x + torusAxisShift i (1 / ((n : ℝ) + 1))))
          - ∫ x : Torus 3, F x * w x) / ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by
    intro n
    rw [show (fun x : Torus 3 ↦ F x * ((w (x + torusAxisShift i (1 / ((n : ℝ) + 1))) - w x)
        / ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)))
        = fun x : Torus 3 ↦ (F x * w (x + torusAxisShift i (1 / ((n : ℝ) + 1))) - F x * w x)
          / ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) from funext fun x ↦ by ring,
      integral_div, integral_sub (hInt _) hInt0]
  exact tendsto_nhds_unique (hlim2.congr hEq) hlim1

/-- **Integration by parts against a character** on the literal three-torus: the `m`-th Fourier
coefficient of the `i`-th partial derivative of a function with everywhere differentiable lift and
axis increments bounded by `C |t|` (for instance a Lipschitz lift) is `2πi mᵢ` times the `m`-th
Fourier coefficient of the function itself. -/
theorem integral_conj_mFourier_mul_torusGradient_of_increment {w : Torus 3 → ℂ}
    (hw : Differentiable ℝ (torusLift w))
    (hinc : ∃ C : ℝ, ∀ (x : Torus 3) (i : Fin 3) (t : ℝ), |t| ≤ 1 →
      ‖w (x + torusAxisShift i t) - w x‖ ≤ C * |t|)
    (m : Fin 3 → ℤ) (i : Fin 3) :
    (∫ x : Torus 3, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) * torusGradient w x i) =
      2 * Real.pi * Complex.I * (m i : ℂ) *
        ∫ x : Torus 3, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) * w x := by
  refine integral_mul_torusGradient_of_translation_of_increment hw hinc i
    (F := fun x ↦ (starRingEnd ℂ) (UnitAddTorus.mFourier m x))
    (Complex.continuous_conj.comp (UnitAddTorus.mFourier m).continuous)
    (fun x ↦ by simpa using norm_mFourier_apply m x) ?_
  intro s x
  have hchar : UnitAddTorus.mFourier m (x + torusAxisShift i s) =
      UnitAddTorus.mFourier m x *
        Complex.exp (2 * Real.pi * Complex.I * (m i : ℂ) * (s : ℂ)) := by
    rw [mFourier_add_point, mFourier_torusAxisShift]
  have hconj : (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (m i : ℂ) * (s : ℂ))) =
      (Complex.exp (2 * Real.pi * Complex.I * (m i : ℂ) * (s : ℂ)))⁻¹ := by
    rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
    ring
  change (starRingEnd ℂ) (UnitAddTorus.mFourier m x) = _
  rw [hchar, map_mul, hconj]
  field_simp

/-- **Integration by parts against a character**, for a test function with a `C¹` lift.  This
is step (i) of the solenoidality argument of `cor:ideal-growth`. -/
theorem integral_conj_mFourier_mul_torusGradient {w : Torus 3 → ℂ}
    (hw : ContDiff ℝ 1 (torusLift w)) (m : Fin 3 → ℤ) (i : Fin 3) :
    (∫ x : Torus 3, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) * torusGradient w x i) =
      2 * Real.pi * Complex.I * (m i : ℂ) *
        ∫ x : Torus 3, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) * w x :=
  integral_conj_mFourier_mul_torusGradient_of_increment (hw.differentiable one_ne_zero)
    (exists_axis_increment_bound hw) m i

/-! ## The `L²` dictionary: characters, classes and the basis pairing -/

/-- The transported three-torus Fourier basis vector at frequency `m` is the `L²` class of the
character of frequency `m`.  (The same statement is proved for the product model, privately, in
`FastDynamo/Analysis/ProductFourier.lean`; it is restated here for the literal model, which is
where the test integrals live.) -/
theorem flatTorus3FourierBasis_eq_toLp (m : Fin 3 → ℤ) :
    flatTorus3FourierBasis m =
      ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ (UnitAddTorus.mFourier m) := by
  let _ : IsFiniteMeasure (torusHaarMeasure (Fin 3)) := by
    rw [← volume_unitAddTorus_eq_haar]
    infer_instance
  have h1 : flatTorus3FourierBasis m =
      cast (congrArg (fun ρ : Measure FlatTorus3 => ↥(Lp ℂ 2 ρ))
        (volume_unitAddTorus_eq_haar (d := Fin 3)).symm)
        (UnitAddTorus.mFourierBasis (d := Fin 3) m) := by
    apply eq_of_heq
    unfold flatTorus3FourierBasis
    exact heq_of_eq (castHilbertBasis_apply (volume_unitAddTorus_eq_haar (d := Fin 3))
      (UnitAddTorus.mFourierBasis (d := Fin 3)) m)
  rw [h1, UnitAddTorus.coe_mFourierBasis]
  exact castContinuousMapToLp (volume_unitAddTorus_eq_haar (d := Fin 3))
    (UnitAddTorus.mFourier m)

/-- The basis vector at frequency `m` is represented almost everywhere by the character of
frequency `m`. -/
theorem flatTorus3FourierBasis_coe_ae (m : Fin 3 → ℤ) :
    (flatTorus3FourierBasis m : Torus 3 → ℂ) =ᵐ[(volume : Measure (Torus 3))]
      UnitAddTorus.mFourier m := by
  rw [flatTorus3FourierBasis_eq_toLp]
  exact ContinuousMap.coeFn_toLp (volume : Measure (Torus 3)) (UnitAddTorus.mFourier m)

/-- Pairing an `L²` class with a basis vector is integration against the conjugate character. -/
theorem inner_flatTorus3FourierBasis (m : Fin 3 → ℤ) (f : FlatTorus3ScalarL2) :
    inner ℂ (flatTorus3FourierBasis m) f =
      ∫ x : Torus 3, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) * (f : Torus 3 → ℂ) x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [flatTorus3FourierBasis_coe_ae m] with x hx
  simp only [RCLike.inner_apply, hx]
  rw [mul_comm]

/-- The `L²` class of a test function with a continuous lift. -/
def torusTestL2 {w : Torus 3 → ℂ} (hw : Continuous (torusLift w)) : FlatTorus3ScalarL2 :=
  (memLp_of_continuous_torusLift hw).toLp w

/-- The `L²` class of the `i`-th partial derivative of a test function with a `C¹` lift. -/
def torusGradientL2 {w : Torus 3 → ℂ} (hw : ContDiff ℝ 1 (torusLift w)) (i : Fin 3) :
    FlatTorus3ScalarL2 :=
  (memLp_torusGradient hw i).toLp _

/-- The class of a test function is represented by the function. -/
theorem torusTestL2_coe_ae {w : Torus 3 → ℂ} (hw : Continuous (torusLift w)) :
    (torusTestL2 hw : Torus 3 → ℂ) =ᵐ[(volume : Measure (Torus 3))] w :=
  MemLp.coeFn_toLp _

/-- The class of a partial derivative is represented by that partial derivative. -/
theorem torusGradientL2_coe_ae {w : Torus 3 → ℂ} (hw : ContDiff ℝ 1 (torusLift w))
    (i : Fin 3) :
    (torusGradientL2 hw i : Torus 3 → ℂ) =ᵐ[(volume : Measure (Torus 3))]
      fun x ↦ torusGradient w x i :=
  MemLp.coeFn_toLp _

/-- **The Fourier coefficients of a partial derivative**, in the form consumed by Parseval: the
`m`-th coefficient of `∂ᵢ w` is `2πi mᵢ` times the `m`-th coefficient of `w`. -/
theorem inner_flatTorus3FourierBasis_torusGradientL2 {w : Torus 3 → ℂ}
    (hw : ContDiff ℝ 1 (torusLift w)) (m : Fin 3 → ℤ) (i : Fin 3) :
    inner ℂ (flatTorus3FourierBasis m) (torusGradientL2 hw i) =
      2 * Real.pi * Complex.I * (m i : ℂ) *
        inner ℂ (flatTorus3FourierBasis m) (torusTestL2 hw.continuous) := by
  have h1 : (∫ x : Torus 3, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) *
      (torusGradientL2 hw i : Torus 3 → ℂ) x) =
      ∫ x : Torus 3, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) * torusGradient w x i := by
    refine integral_congr_ae ?_
    filter_upwards [torusGradientL2_coe_ae hw i] with x hx
    rw [hx]
  have h2 : (∫ x : Torus 3, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) *
      (torusTestL2 hw.continuous : Torus 3 → ℂ) x) =
      ∫ x : Torus 3, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) * w x := by
    refine integral_congr_ae ?_
    filter_upwards [torusTestL2_coe_ae hw.continuous] with x hx
    rw [hx]
  rw [inner_flatTorus3FourierBasis, inner_flatTorus3FourierBasis, h1, h2]
  exact integral_conj_mFourier_mul_torusGradient hw m i

end

end FastDynamo
