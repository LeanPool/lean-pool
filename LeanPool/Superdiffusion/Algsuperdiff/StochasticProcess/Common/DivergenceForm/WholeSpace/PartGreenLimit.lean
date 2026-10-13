/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueIdentificationCarrier
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PartGreenPotential

/-!
# PartGreenLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The vanishing-shift limit of the zero-trace solutions on a bounded part domain

The Dirichlet resolvent of a bounded measurable datum on a bounded open convex domain is the
value component of a zero-trace carrier element, the solution of the shifted weak equation.  That
carrier element converges as the shift decreases to zero, and the value component of the limit is
the Green potential of `PartGreenPotential.lean`.

The convergence is an energy estimate.  Subtracting the weak equations at two shifts and testing
against the difference gives

  `nu * ‖grad (Z_s - Z_t)‖² ≤ t ⟪Z_t, Z_s - Z_t⟫ - s ⟪Z_s, Z_s - Z_t⟫`,

whose right-hand side is at most `(s + t)` times a constant, because the shift-uniform supremum
bound of the Dirichlet resolvents bounds every `Z_lam` in `L²` uniformly in the shift.  The
Poincare inequality on the carrier converts the gradient estimate into a carrier-norm estimate,
so the family is Cauchy as the shift decreases to zero and the carrier is complete.  The limit
solves the *unshifted* weak equation, because the term carrying the shift vanishes.

This is the statement of `ExitMeanValueIdentificationLimit.lean` with the exhaustion cube
replaced by an arbitrary bounded open convex domain.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open ZeroTraceSobolev
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The `L²` class of the datum agrees almost everywhere on the domain with the datum. -/
theorem partDatumL2_ae {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    ⇑(partDatumL2 hV hf hfD) =ᵐ[volumeMeasureOn V] f := by
  have hcoe : ⇑(partDatumL2 hV hf hfD) =ᵐ[volumeMeasureOn V]
      domainExtension (f ∘ Subtype.val) :=
    boundedMeasurableToScalarL2_coeFn hV (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)
  filter_upwards [hcoe, ae_restrict_mem hV.isOpen.measurableSet] with x hx hxmem
  rw [hx, domainExtension_of_mem hxmem]
  rfl

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-! ## The shift-indexed family on the carrier -/

/-- The zero-trace carrier solution of the shifted Dirichlet problem of a bounded part domain, as
a function of the shift; the value at a non-positive shift is zero. -/
def partShiftSolution {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (lam : ℝ) : ZeroTraceSobolev V :=
  if h : 0 < lam then
    alphaShiftedSolution A.a h A.hnu (partEllipticity A hV) (partDatumL2 hV hf hfD)
  else 0

theorem partShiftSolution_of_pos {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) {lam : ℝ}
    (hlam : 0 < lam) :
    A.partShiftSolution hV hf hfD lam =
      alphaShiftedSolution A.a hlam A.hnu (partEllipticity A hV) (partDatumL2 hV hf hfD) :=
  dite_eq_left hlam

/-- **The shifted weak equation of the carrier family.** -/
theorem isAlphaShiftedWeakSolution_partShiftSolution {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) {lam : ℝ} (hlam : 0 < lam) :
    IsAlphaShiftedWeakSolution A.a V lam (partDatumL2 hV hf hfD)
      (A.partShiftSolution hV hf hfD lam) := by
  rw [A.partShiftSolution_of_pos hV hf hfD hlam]
  exact alphaShiftedSolution_isAlphaShiftedWeakSolution A.a hlam A.hnu (partEllipticity A hV)
    (partDatumL2 hV hf hfD)

/-- The value component of the carrier family is the shift-indexed Dirichlet resolvent. -/
theorem toL2_partShiftSolution_ae {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (lam : ℝ) :
    ⇑(toL2 (A.partShiftSolution hV hf hfD lam)) =ᵐ[volumeMeasureOn V]
      A.partShiftResolvent hV f hf hfD lam := by
  by_cases hlam : 0 < lam
  · have hsol := A.partC0Resolvent_ae hV ⟨lam, hlam⟩ f hf hfD
    have hfun : A.partShiftResolvent hV f hf hfD lam =
        A.partC0Resolvent hV ⟨lam, hlam⟩ f hf hfD :=
      funext fun x ↦ A.partShiftResolvent_of_pos hV hf hfD hlam x
    rw [hfun, A.partShiftSolution_of_pos hV hf hfD hlam]
    exact hsol.symm
  · have hzero : A.partShiftSolution hV hf hfD lam = 0 := dite_eq_right hlam
    have hres : A.partShiftResolvent hV f hf hfD lam = fun _ ↦ (0 : ℝ) :=
      funext fun x ↦ by rw [partShiftResolvent, dite_eq_right hlam]
    rw [hzero, hres, map_zero]
    exact Lp.coeFn_zero ℝ 2 _

/-- The shift-uniform `L²` bound of the carrier family. -/
def partGreenL2Bound {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) (D : ℝ) : ℝ :=
  scalarL2Factor V * (D * A.partTorsionBound hV)

theorem partGreenL2Bound_nonneg {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) {D : ℝ}
    (hD : 0 ≤ D) : 0 ≤ A.partGreenL2Bound hV D :=
  mul_nonneg (scalarL2Factor_nonneg _) (mul_nonneg hD (A.partTorsionBound_nonneg hV))

theorem norm_toL2_partShiftSolution_le {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D)
    (lam : ℝ) :
    ‖toL2 (A.partShiftSolution hV hf hfD lam)‖ ≤ A.partGreenL2Bound hV D := by
  refine norm_scalarL2_le_of_ae_bound hV _ (mul_nonneg hD (A.partTorsionBound_nonneg hV)) ?_
  filter_upwards [A.toL2_partShiftSolution_ae hV hf hfD lam] with x hx
  rw [hx]
  exact A.abs_partShiftResolvent_le hV hf hD hfD lam x

/-! ## The energy estimate for two shifts -/

/-- **The energy of the difference of two shifts is controlled by the sum of the shifts.**
Subtracting the two weak equations and testing against the difference leaves only the two mass
terms, each carrying an explicit factor of its shift against the shift-uniform `L²` bound. -/
theorem nu_mul_norm_gradient_partShiftSolution_sub_sq_le {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    A.nu * ‖gradient (A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t)‖ ^ 2 ≤
      (s + t) * (2 * A.partGreenL2Bound hV D ^ 2) := by
  have hEll := partEllipticity A hV
  have hB0 : 0 ≤ A.partGreenL2Bound hV D := A.partGreenL2Bound_nonneg hV hD
  have hs' := A.isAlphaShiftedWeakSolution_partShiftSolution hV hf hfD hs
  have ht' := A.isAlphaShiftedWeakSolution_partShiftSolution hV hf hfD ht
  have hsplit : coefficientPairing A.a V
        (gradient (A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t))
        (gradient (A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t)) =
      coefficientPairing A.a V (gradient (A.partShiftSolution hV hf hfD s))
          (gradient (A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t)) -
        coefficientPairing A.a V (gradient (A.partShiftSolution hV hf hfD t))
          (gradient (A.partShiftSolution hV hf hfD s -
            A.partShiftSolution hV hf hfD t)) := by
    have hlin : (shiftedBilin hEll (0 : ℝ))
          (A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t) =
        (shiftedBilin hEll (0 : ℝ)) (A.partShiftSolution hV hf hfD s) -
          (shiftedBilin hEll (0 : ℝ)) (A.partShiftSolution hV hf hfD t) :=
      map_sub _ _ _
    rw [coefficientPairing_gradient_eq_shiftedBilin hEll,
      coefficientPairing_gradient_eq_shiftedBilin hEll,
      coefficientPairing_gradient_eq_shiftedBilin hEll, hlin,
      sub_apply]
  have hWB : ‖toL2 (A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t)‖ ≤
      2 * A.partGreenL2Bound hV D := by
    rw [show toL2 (A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t) =
        toL2 (A.partShiftSolution hV hf hfD s) - toL2 (A.partShiftSolution hV hf hfD t) from
      map_sub _ _ _]
    refine (norm_sub_le _ _).trans ?_
    have h1 := A.norm_toL2_partShiftSolution_le hV hf hD hfD s
    have h2 := A.norm_toL2_partShiftSolution_le hV hf hD hfD t
    linarith only [h1, h2]
  have hbound : ∀ lam : ℝ, 0 < lam →
      |lam * inner ℝ (toL2 (A.partShiftSolution hV hf hfD lam))
          (toL2 (A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t))| ≤
        lam * (A.partGreenL2Bound hV D * (2 * A.partGreenL2Bound hV D)) := by
    intro lam hlam
    rw [abs_mul, abs_of_pos hlam]
    refine mul_le_mul_of_nonneg_left ?_ hlam.le
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (A.norm_toL2_partShiftSolution_le hV hf hD hfD lam) hWB
      (norm_nonneg _) hB0
  have hs2 := hbound s hs
  have ht2 := hbound t ht
  have hpair : coefficientPairing A.a V
        (gradient (A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t))
        (gradient (A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t)) ≤
      (s + t) * (2 * A.partGreenL2Bound hV D ^ 2) := by
    have es := hs' (A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t)
    have et := ht' (A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t)
    have habs1 := (abs_le.mp hs2).1
    have habs2 := (abs_le.mp ht2).2
    have hring : t * (A.partGreenL2Bound hV D * (2 * A.partGreenL2Bound hV D)) +
        s * (A.partGreenL2Bound hV D * (2 * A.partGreenL2Bound hV D)) =
        (s + t) * (2 * A.partGreenL2Bound hV D ^ 2) := by ring
    rw [hsplit]
    linarith only [es, et, habs1, habs2, hring]
  exact le_trans (mul_norm_gradient_sq_le_coefficientPairing hEll _) hpair

/-! ## The vanishing-shift limit -/

/-- **The carrier family is Cauchy as the shift decreases to zero and therefore converges.** -/
theorem exists_tendsto_partShiftSolution {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    ∃ Z : ZeroTraceSobolev V,
      Tendsto (fun n : ℕ ↦ A.partShiftSolution hV hf hfD ((n : ℝ) + 1)⁻¹) atTop (𝓝 Z) := by
  obtain ⟨C, hC, hpoin⟩ := ZeroTraceSobolev.exists_poincare_constant hV
  have hB0 : 0 ≤ A.partGreenL2Bound hV D := A.partGreenL2Bound_nonneg hV hD
  set K : ℝ := (1 + C ^ 2) * (2 * A.partGreenL2Bound hV D ^ 2) / A.nu with hKdef
  have hK : 0 ≤ K := by
    rw [hKdef]
    exact div_nonneg (mul_nonneg (by positivity) (by positivity)) A.hnu.le
  have hstep : ∀ s t : ℝ, 0 < s → 0 < t →
      ‖A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t‖ ≤
        Real.sqrt (K * (s + t)) := by
    intro s t hs ht
    have hgrad := A.nu_mul_norm_gradient_partShiftSolution_sub_sq_le hV hf hD hfD hs ht
    have hg2 : ‖gradient (A.partShiftSolution hV hf hfD s -
        A.partShiftSolution hV hf hfD t)‖ ^ 2 ≤
        (s + t) * (2 * A.partGreenL2Bound hV D ^ 2) / A.nu := by
      rw [le_div_iff₀ A.hnu]
      linarith only [hgrad]
    have hv2 : ‖toL2 (A.partShiftSolution hV hf hfD s -
        A.partShiftSolution hV hf hfD t)‖ ^ 2 ≤
        C ^ 2 * ‖gradient (A.partShiftSolution hV hf hfD s -
          A.partShiftSolution hV hf hfD t)‖ ^ 2 := by
      have h := hpoin (A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t)
      calc
        ‖toL2 (A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t)‖ ^ 2 ≤
            (C * ‖gradient (A.partShiftSolution hV hf hfD s -
              A.partShiftSolution hV hf hfD t)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = C ^ 2 * ‖gradient (A.partShiftSolution hV hf hfD s -
              A.partShiftSolution hV hf hfD t)‖ ^ 2 := by ring
    have hsq : ‖A.partShiftSolution hV hf hfD s - A.partShiftSolution hV hf hfD t‖ ^ 2 ≤
        K * (s + t) := by
      rw [ZeroTraceSobolev.norm_sq_eq]
      have h2 : (1 + C ^ 2) * ‖gradient (A.partShiftSolution hV hf hfD s -
            A.partShiftSolution hV hf hfD t)‖ ^ 2 ≤
          (1 + C ^ 2) * ((s + t) * (2 * A.partGreenL2Bound hV D ^ 2) / A.nu) :=
        mul_le_mul_of_nonneg_left hg2 (by positivity)
      have h3 : (1 + C ^ 2) * ((s + t) * (2 * A.partGreenL2Bound hV D ^ 2) / A.nu) =
          K * (s + t) := by
        rw [hKdef]
        ring
      linarith only [hv2, h2, h3]
    have hsqrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _)] at hsqrt
  refine cauchySeq_tendsto_of_complete ?_
  refine cauchySeq_of_le_tendsto_0
    (fun N : ℕ ↦ Real.sqrt (K * (2 * ((N : ℝ) + 1)⁻¹))) ?_ ?_
  · intro n m N hn hm
    have hmono : ∀ k : ℕ, N ≤ k → ((k : ℝ) + 1)⁻¹ ≤ ((N : ℝ) + 1)⁻¹ := by
      intro k hk
      have hcast : ((N : ℝ) + 1) ≤ ((k : ℝ) + 1) := by
        have hkc : (N : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
        linarith only [hkc]
      have hposN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      gcongr
    have hposn : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have hposm : (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := by positivity
    have h := hstep _ _ hposn hposm
    rw [dist_eq_norm]
    refine h.trans (Real.sqrt_le_sqrt ?_)
    have hn' := hmono n hn
    have hm' := hmono m hm
    refine mul_le_mul_of_nonneg_left ?_ hK
    linarith only [hn', hm']
  · have h1 : Tendsto (fun N : ℕ ↦ ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 : Tendsto (fun N : ℕ ↦ K * (2 * ((N : ℝ) + 1)⁻¹)) atTop (𝓝 (K * (2 * 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul h1)
    rw [mul_zero, mul_zero] at h2
    have h3 := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h2
    rw [Real.sqrt_zero] at h3
    exact h3

/-- **The Green solution on the zero-trace carrier of a bounded part domain**: the
vanishing-shift limit of the carrier solutions of the shifted Dirichlet problem. -/
def partGreenSolution {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) : ZeroTraceSobolev V :=
  Classical.choose (A.exists_tendsto_partShiftSolution hV hf hD hfD)

theorem tendsto_partShiftSolution_partGreenSolution {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    Tendsto (fun n : ℕ ↦ A.partShiftSolution hV hf hfD ((n : ℝ) + 1)⁻¹) atTop
      (𝓝 (A.partGreenSolution hV hf hD hfD)) :=
  Classical.choose_spec (A.exists_tendsto_partShiftSolution hV hf hD hfD)

/-- **The Green solution solves the unshifted zero-trace weak equation.** -/
theorem isAlphaShiftedWeakSolution_partGreenSolution {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    IsAlphaShiftedWeakSolution A.a V 0 (partDatumL2 hV hf hfD)
      (A.partGreenSolution hV hf hD hfD) := by
  intro w
  have hEll := partEllipticity A hV
  have htend := A.tendsto_partShiftSolution_partGreenSolution hV hf hD hfD
  have hpair : Tendsto (fun n : ℕ ↦ coefficientPairing A.a V
        (gradient (A.partShiftSolution hV hf hfD ((n : ℝ) + 1)⁻¹)) (gradient w)) atTop
      (𝓝 (coefficientPairing A.a V (gradient (A.partGreenSolution hV hf hD hfD))
        (gradient w))) := by
    have hcont := (((shiftedBilin hEll (0 : ℝ)).flip w).continuous.tendsto
      (A.partGreenSolution hV hf hD hfD)).comp htend
    simp only [Function.comp_def, ContinuousLinearMap.flip_apply] at hcont
    simpa only [coefficientPairing_gradient_eq_shiftedBilin hEll] using hcont
  have hmass : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ *
      inner ℝ (toL2 (A.partShiftSolution hV hf hfD ((n : ℝ) + 1)⁻¹)) (toL2 w)) atTop
      (𝓝 0) := by
    have hzero : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ *
        (A.partGreenL2Bound hV D * ‖toL2 w‖)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
        simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa only [zero_mul] using h1.mul tendsto_const_nhds
    refine squeeze_zero_norm (fun n ↦ ?_) hzero
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
    refine mul_le_mul_of_nonneg_left ?_ hpos.le
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right
      (A.norm_toL2_partShiftSolution_le hV hf hD hfD _) (norm_nonneg _)
  have hsum := hmass.add hpair
  have hconst : Tendsto (fun _ : ℕ ↦ inner ℝ (partDatumL2 hV hf hfD) (toL2 w)) atTop
      (𝓝 (inner ℝ (partDatumL2 hV hf hfD) (toL2 w))) := tendsto_const_nhds
  have heq : (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ *
        inner ℝ (toL2 (A.partShiftSolution hV hf hfD ((n : ℝ) + 1)⁻¹)) (toL2 w) +
      coefficientPairing A.a V
        (gradient (A.partShiftSolution hV hf hfD ((n : ℝ) + 1)⁻¹)) (gradient w)) =
      fun _ : ℕ ↦ inner ℝ (partDatumL2 hV hf hfD) (toL2 w) := by
    funext n
    exact A.isAlphaShiftedWeakSolution_partShiftSolution hV hf hfD
      (show (0 : ℝ) < ((n : ℝ) + 1)⁻¹ by positivity) w
  rw [heq] at hsum
  have hfinal := tendsto_nhds_unique hconst hsum
  rw [zero_mul, zero_add, hfinal, zero_add]

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
