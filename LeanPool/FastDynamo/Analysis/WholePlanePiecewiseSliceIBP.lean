/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneIntegralWeakDerivative
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integration by parts along slices with countably many exceptional points

This file records the measure-theoretic core of a coordinate-slice proof for weak derivatives
of a continuous field which is smooth away from an interface.  A coordinate line meets the unit
circle in at most two points, so the one-dimensional fundamental theorem of calculus off a
countable set applies on every slice.  Fubini then reassembles the slice identities.

The statements here are independent of the unit circle and of the Ponomarenko
field.  The geometric application, which identifies the exceptional points on each affine
coordinate line and proves the slice derivative and decay hypotheses, is carried out in
`WholePlaneUnitCircleSlices` and `WholePlaneTwoJumpIntegrationByParts`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Set Topology
open scoped LineDeriv SchwartzMap

/-- Put the coordinate selected by `j` in the second factor, so that Fubini integrates in that
coordinate on the inner integral. -/
def wholePlaneSliceEquiv (j : Fin 2) : (ℝ × ℝ) ≃ᵐ WholePlane :=
  if j = 0 then
    (MeasurableEquiv.prodComm : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ)).trans <|
      (@MeasurableEquiv.finTwoArrow ℝ _).symm.trans <|
        MeasurableEquiv.toLp 2 (Fin 2 → ℝ)
  else
    (@MeasurableEquiv.finTwoArrow ℝ _).symm.trans <|
      MeasurableEquiv.toLp 2 (Fin 2 → ℝ)

/-- For `j = 0` the slice parametrization swaps the two real factors, so the second factor
carries the coordinate `x₀` that Fubini integrates on the inner integral. -/
@[simp] theorem wholePlaneSliceEquiv_zero_apply (p : ℝ × ℝ) :
    wholePlaneSliceEquiv 0 p = !₂[p.2, p.1] := by
  rfl

/-- For `j = 1` the slice parametrization is the identification of `ℝ × ℝ` with the plane in the
given order, the second factor carrying the coordinate `x₁`. -/
@[simp] theorem wholePlaneSliceEquiv_one_apply (p : ℝ × ℝ) :
    wholePlaneSliceEquiv 1 p = !₂[p.1, p.2] := by
  rfl

/-- The coordinate-slice parametrizations preserve planar Lebesgue measure. -/
theorem measurePreserving_wholePlaneSliceEquiv (j : Fin 2) :
    MeasurePreserving (wholePlaneSliceEquiv j)
      ((volume : Measure ℝ).prod volume) volume := by
  fin_cases j
  · exact (PiLp.volume_preserving_toLp (Fin 2)).comp <|
      (volume_preserving_finTwoArrow ℝ).symm.comp Measure.measurePreserving_swap
  · exact (PiLp.volume_preserving_toLp (Fin 2)).comp
      (volume_preserving_finTwoArrow ℝ).symm

/-- A coordinate line meets a real circle in only finitely many points.  This algebraic form is
the only circle geometry needed by the slice argument: after expanding the squared Euclidean
norm, every fiber is contained in a two-point set. -/
theorem finite_setOf_sq_add_sq_eq (x c : ℝ) :
    Set.Finite {t : ℝ | x ^ 2 + t ^ 2 = c} := by
  let q := Real.sqrt (c - x ^ 2)
  refine ((Set.finite_singleton (-q)).insert q).subset ?_
  intro t ht
  change x ^ 2 + t ^ 2 = c at ht
  have hnonneg : 0 ≤ c - x ^ 2 := by nlinarith [sq_nonneg t]
  have hq : q ^ 2 = c - x ^ 2 := by
    simpa [q] using Real.sq_sqrt hnonneg
  have htq : t ^ 2 = q ^ 2 := by nlinarith
  rcases eq_or_eq_neg_of_sq_eq_sq t q htq with h | h
  · simp [h]
  · simp [h]

/-- The integral of an integrable derivative on the real line is the jump between its limits at
the two ends, even if the derivative identity fails on a countable set.

Continuity is essential here: in the application to a field with an interface it is exactly the
common-trace condition across that interface. -/
theorem integral_eq_sub_of_hasDerivAt_off_countable
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f f' : ℝ → F} {s : Set ℝ}
    (hs : s.Countable) (hc : Continuous f)
    (hd : ∀ x ∉ s, HasDerivAt f (f' x) x)
    (hi : Integrable f') {a b : F}
    (ha : Tendsto f atBot (𝓝 a)) (hb : Tendsto f atTop (𝓝 b)) :
    ∫ x : ℝ, f' x = b - a := by
  have hcover : AECover (volume : Measure ℝ) atTop
      (fun r : ℝ ↦ Ioc (-r) r) :=
    aecover_Ioc tendsto_neg_atTop_atBot tendsto_id
  apply hcover.integral_eq_of_tendsto (b - a) hi
  have hfinite :
      (fun r : ℝ ↦ ∫ x in Ioc (-r) r, f' x) =ᶠ[atTop]
        (fun r : ℝ ↦ f r - f (-r)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    have hle : -r ≤ r := by linarith
    rw [← intervalIntegral.integral_of_le hle]
    exact integral_eq_of_hasDerivAt_off_countable f f' hs hc.continuousOn
      (fun x hx ↦ hd x hx.2) hi.intervalIntegrable
  exact (hb.sub (ha.comp tendsto_neg_atTop_atBot)).congr' hfinite.symm

/-- Fubini reduction for a function on a product whose derivative identity may fail at a
countable, slice-dependent set of points.

This is the reusable analytic step behind the coordinate-slice route: once each slice is
continuous, decays at both ends, and has the proposed derivative away from its exceptional set,
the proposed derivative has integral zero over the whole product. -/
theorem integral_prod_eq_zero_of_fiberwise_hasDerivAt_off_countable
    {X F : Type*} [MeasurableSpace X]
    {μ : Measure X} [SigmaFinite μ]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f f' : X × ℝ → F}
    (hi : Integrable f' (μ.prod volume))
    (hc : ∀ x : X, Continuous (fun t : ℝ ↦ f (x, t)))
    (hd : ∀ x : X, ∃ s : Set ℝ, s.Countable ∧
      ∀ t ∉ s, HasDerivAt (fun u : ℝ ↦ f (x, u)) (f' (x, t)) t)
    (ha : ∀ x : X, Tendsto (fun t : ℝ ↦ f (x, t)) atBot (𝓝 0))
    (hb : ∀ x : X, Tendsto (fun t : ℝ ↦ f (x, t)) atTop (𝓝 0)) :
    ∫ p : X × ℝ, f' p ∂μ.prod volume = 0 := by
  rw [integral_prod _ hi]
  apply integral_eq_zero_of_ae
  filter_upwards [hi.prod_right_ae] with x hix
  obtain ⟨s, hs, hdx⟩ := hd x
  simpa using integral_eq_sub_of_hasDerivAt_off_countable hs (hc x) hdx hix (ha x) (hb x)

/-- The pointwise product of a Schwartz test function with an `L²` field is integrable over the
plane, by Cauchy–Schwarz; this is what lets Fubini be applied to the slice identities. -/
private theorem integrable_schwartz_smul_l2_slice
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (f : WholePlaneL2 F) (g : SchwartzMap WholePlane ℂ) :
    Integrable (fun x : WholePlane ↦ g x • (f x : F)) volume := by
  exact memLp_one_iff_integrable.mp <|
    (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] F →L[ℂ] F).memLp_of_bilin
      1 (g.memLp 2 volume) (Lp.memLp f)

/-- Turn fiberwise integration by parts for `φ • f` into the repository's exact whole-plane
weak-derivative identity.

The hypotheses expose only the geometric part of the slice argument.  For every
Schwartz test function and every transverse coordinate, the product must be continuous, tend to
zero at both ends of the slice, and have the classical product-rule derivative away from a
countable exceptional set.  Integrability of both product-rule terms and the Fubini/change-of-
coordinates steps are discharged here. -/
theorem hasWholePlaneIntegralWeakDerivative_of_ae_fiberwise_product
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (u du : WholePlane → F) (f df : WholePlaneL2 F) (j : Fin 2)
    (hu : u =ᵐ[volume] fun y ↦ (f y : F))
    (hdu : du =ᵐ[volume] fun y ↦ (df y : F))
    (hc : ∀ (φ : SchwartzMap WholePlane ℂ) (x : ℝ),
      Continuous (fun t : ℝ ↦
        φ (wholePlaneSliceEquiv j (x, t)) •
          u (wholePlaneSliceEquiv j (x, t))))
    (hd : ∀ (φ : SchwartzMap WholePlane ℂ) (x : ℝ),
      ∃ s : Set ℝ, s.Countable ∧ ∀ t ∉ s,
        HasDerivAt
          (fun v : ℝ ↦
            φ (wholePlaneSliceEquiv j (x, v)) •
              u (wholePlaneSliceEquiv j (x, v)))
          (((∂_{wholePlaneBasis j} φ) (wholePlaneSliceEquiv j (x, t))) •
              u (wholePlaneSliceEquiv j (x, t)) +
            φ (wholePlaneSliceEquiv j (x, t)) •
              du (wholePlaneSliceEquiv j (x, t))) t)
    (ha : ∀ (φ : SchwartzMap WholePlane ℂ) (x : ℝ),
      Tendsto
        (fun t : ℝ ↦
          φ (wholePlaneSliceEquiv j (x, t)) •
            u (wholePlaneSliceEquiv j (x, t)))
        atBot (𝓝 0))
    (hb : ∀ (φ : SchwartzMap WholePlane ℂ) (x : ℝ),
      Tendsto
        (fun t : ℝ ↦
          φ (wholePlaneSliceEquiv j (x, t)) •
            u (wholePlaneSliceEquiv j (x, t)))
        atTop (𝓝 0)) :
    HasWholePlaneIntegralWeakDerivative f df j := by
  intro φ
  let q : WholePlane → F := fun y ↦
    ((∂_{wholePlaneBasis j} φ) y) • u y + φ y • du y
  have hleft_l2 : Integrable
      (fun y : WholePlane ↦ ((∂_{wholePlaneBasis j} φ) y) • (f y : F)) volume :=
    integrable_schwartz_smul_l2_slice f (∂_{wholePlaneBasis j} φ)
  have hright_l2 : Integrable
      (fun y : WholePlane ↦ φ y • (df y : F)) volume :=
    integrable_schwartz_smul_l2_slice df φ
  have hleft : Integrable
      (fun y : WholePlane ↦ ((∂_{wholePlaneBasis j} φ) y) • u y) volume :=
    hleft_l2.congr <| hu.symm.mono fun y hy ↦ by
      simpa using congrArg (fun z : F ↦ ((∂_{wholePlaneBasis j} φ) y) • z) hy
  have hright : Integrable
      (fun y : WholePlane ↦ φ y • du y) volume :=
    hright_l2.congr <| hdu.symm.mono fun y hy ↦ by
      simpa using congrArg (fun z : F ↦ φ y • z) hy
  have hq : Integrable q volume := hleft.add hright
  have hq_pull : Integrable
      (q ∘ wholePlaneSliceEquiv j)
      ((volume : Measure ℝ).prod volume) :=
    (measurePreserving_wholePlaneSliceEquiv j).integrable_comp_of_integrable hq
  have hzero_pull :
      ∫ p : ℝ × ℝ, q (wholePlaneSliceEquiv j p)
          ∂((volume : Measure ℝ).prod volume) = 0 := by
    apply integral_prod_eq_zero_of_fiberwise_hasDerivAt_off_countable
      (f := fun p : ℝ × ℝ ↦
        φ (wholePlaneSliceEquiv j p) • u (wholePlaneSliceEquiv j p))
      (f' := q ∘ wholePlaneSliceEquiv j) hq_pull
    · exact hc φ
    · intro x
      simpa [q] using hd φ x
    · exact ha φ
    · exact hb φ
  have hzero : ∫ y : WholePlane, q y = 0 := by
    rw [← (measurePreserving_wholePlaneSliceEquiv j).integral_comp' q]
    exact hzero_pull
  have hconcrete :
      (∫ y : WholePlane,
          ((-∂_{wholePlaneBasis j} φ) y) • u y ∂volume) =
        ∫ y : WholePlane, φ y • du y ∂volume := by
    rw [show (fun y : WholePlane ↦
        ((-∂_{wholePlaneBasis j} φ) y) • u y) =
        fun y : WholePlane ↦
          -(((∂_{wholePlaneBasis j} φ) y) • u y) by
        funext y
        simp]
    rw [integral_neg]
    rw [show q = fun y : WholePlane ↦
        ((∂_{wholePlaneBasis j} φ) y) • u y +
          φ y • du y by rfl, integral_add hleft hright] at hzero
    apply neg_eq_of_add_eq_zero_left
    simpa [add_comm] using hzero
  calc
    (∫ y : WholePlane,
        ((-∂_{wholePlaneBasis j} φ) y) • (f y : F) ∂volume) =
        ∫ y : WholePlane,
          ((-∂_{wholePlaneBasis j} φ) y) • u y ∂volume := by
      apply integral_congr_ae
      exact hu.symm.mono fun y hy ↦ by
        simpa using congrArg (fun z : F ↦ ((-∂_{wholePlaneBasis j} φ) y) • z) hy
    _ = ∫ y : WholePlane, φ y • du y ∂volume := hconcrete
    _ = ∫ y : WholePlane, φ y • (df y : F) ∂volume := by
      apply integral_congr_ae
      exact hdu.mono fun y hy ↦ by
        simpa using congrArg (fun z : F ↦ φ y • z) hy

end

end FastDynamo
