/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearCounterexample.FactorDerivative
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedMildInitialData
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Reg Uniform Integration By Parts

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic
open scoped Topology ENNReal Convolution

noncomputable section

namespace CKN.Leray

theorem regUniform_continuousOn_pullback
    {F : ParabolicPoint → ℝ} {S : Set ParabolicPoint}
    {Sprod : Set (Vec3 × ℝ)}
    (hF : ContinuousOn F S)
    (hS : ∀ z ∈ Sprod,
      ((z.1, z.2) : ParabolicPoint) ∈ S) :
    ContinuousOn (fun z : Vec3 × ℝ =>
      F ((z.1, z.2) : ParabolicPoint)) Sprod := by
  have hmap : MapsTo parabolicHomeomorph.symm Sprod S := by
    intro z hz
    change ((z.1, z.2) : ParabolicPoint) ∈ S
    exact hS z hz
  apply ContinuousOn.congr
    (hF.comp parabolicHomeomorph.symm.continuous.continuousOn hmap)
  intro z hz
  rfl




local instance : Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure Vec3) (volume : Measure ℝ)

theorem regUniform_contDiffOn_spatialSlice_differentiableAt
    {S : Set (Vec3 × ℝ)} {F : Vec3 × ℝ → ℝ}
    (hS : IsOpen S) (hF : ContDiffOn ℝ 1 F S)
    {z : Vec3 × ℝ} (hz : z ∈ S) :
    DifferentiableAt ℝ (fun x : Vec3 => F (x, z.2)) z.1 := by
  have hFz : ContDiffAt ℝ 1 F z := hF.contDiffAt (hS.mem_nhds hz)
  have hmap : ContDiffAt ℝ 1 (fun x : Vec3 => (x, z.2)) z.1 := by
    fun_prop
  exact (hFz.comp z.1 hmap).differentiableAt (by norm_num)

theorem regUniform_contDiffOn_timeSlice_differentiableAt
    {S : Set (Vec3 × ℝ)} {F : Vec3 × ℝ → ℝ}
    (hS : IsOpen S) (hF : ContDiffOn ℝ 1 F S)
    {z : Vec3 × ℝ} (hz : z ∈ S) :
    DifferentiableAt ℝ (fun t : ℝ => F (z.1, t)) z.2 := by
  have hFz : ContDiffAt ℝ 1 F z := hF.contDiffAt (hS.mem_nhds hz)
  have hmap : ContDiffAt ℝ 1 (fun t : ℝ => (z.1, t)) z.2 := by
    fun_prop
  exact (hFz.comp z.2 hmap).differentiableAt (by norm_num)

private theorem continuous_mul_of_continuousOn_open_of_tsupport_subset
    {F G : Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)}
    (hS : IsOpen S) (hF : ContinuousOn F S) (hG : ContinuousOn G S)
    (hGs : tsupport G ⊆ S) : Continuous (fun z => F z * G z) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ S
  · exact (hF z hz).continuousAt (hS.mem_nhds hz) |>.mul
      ((hG z hz).continuousAt (hS.mem_nhds hz))
  · have hz' : z ∉ tsupport G := fun h => hz (hGs h)
    have hzero : G =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      rw [notMem_tsupport_iff_eventuallyEq] at hz'
      exact hz'
    have hprod : (fun y => F y * G y) =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
      hzero.mono fun y hy => by simp [hy]
    exact continuousAt_const.congr_of_eventuallyEq hprod

/-- A continuous product with compact support inside an open carrier is
integrable on the whole product space. -/
theorem regUniform_integrable_mul_of_tsupport_subset
    {F G : Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)}
    (hS : IsOpen S) (hF : ContinuousOn F S) (hG : ContinuousOn G S)
    (hGc : HasCompactSupport G) (hGs : tsupport G ⊆ S) :
    Integrable (fun z => F z * G z) volume := by
  exact (continuous_mul_of_continuousOn_open_of_tsupport_subset
    hS hF hG hGs).integrable_of_hasCompactSupport hGc.mul_left

private theorem regUniform_setIntegral_eq_integral_of_tsupport_subset
    {F : Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)}
    (hS : MeasurableSet S) (hFs : tsupport F ⊆ S) :
    (∫ z in S, F z ∂volume) = ∫ z, F z ∂volume := by
  rw [← MeasureTheory.integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ S
  · simp [hz]
  · have hzero : F z = 0 := by
      by_contra hne
      exact hz (hFs (subset_tsupport
        (f := F) (Function.mem_support.mpr hne)))
    simp [hz, hzero]
private theorem regularised_spatialPartial_hasLineDerivAt
    {F : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ} (i : Fin 3)
    (hF : DifferentiableAt ℝ (fun x : Vec3 => F (x, z.2)) z.1) :
    HasLineDerivAt ℝ F
      (spatialPartial (show ParabolicPoint → ℝ from F) i z)
      z (basisVec i, 0) := by
  let f : Vec3 → ℝ := fun x => F (x, z.2)
  have hF' : HasFDerivAt f (fderiv ℝ f z.1) z.1 := hF.hasFDerivAt
  have hcurve : HasDerivAt (fun t : ℝ => z.1 + t • basisVec i)
      (basisVec i) 0 := by
    convert ((hasDerivAt_const (x := 0) z.1).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (basisVec i))) using 1
    · funext t
      simp
    · simp
  have hcomp := hF'.comp_hasDerivAt_of_eq 0 hcurve (by simp)
  change HasDerivAt (fun t : ℝ => F (z + t • (basisVec i, 0)))
    (spatialPartial (show ParabolicPoint → ℝ from F) i z) 0
  convert hcomp using 1
  · funext t
    have hprod : z + t • (basisVec i, 0) =
        (z.1 + t • basisVec i, z.2) := by
      ext <;> simp
    rw [hprod]
    rfl
  · rfl

/-- Spatial integration by parts on an open carrier for a compactly supported
factor whose derivatives are controlled on that carrier. -/
theorem regUniform_integral_mul_spatialPartial_eq_neg
    {F G : Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)} (i : Fin 3)
    (hS : IsOpen S)
    (hFcont : ContinuousOn F S)
    (hFpartialCont : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial
        (show ParabolicPoint → ℝ from F) i
        ((z.1, z.2) : ParabolicPoint)) S)
    (hFdiff : ∀ z ∈ S,
      DifferentiableAt ℝ (fun x : Vec3 => F (x, z.2)) z.1)
    (hGcont : ContinuousOn G S)
    (hGpartialCont : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial
        (show ParabolicPoint → ℝ from G) i
        ((z.1, z.2) : ParabolicPoint)) S)
    (hGdiff : ∀ z ∈ S,
      DifferentiableAt ℝ (fun x : Vec3 => G (x, z.2)) z.1)
    (hGc : HasCompactSupport G) (hGs : tsupport G ⊆ S) :
    (∫ z in S, F z * spatialPartial
      (show ParabolicPoint → ℝ from G) i z ∂volume) =
    -∫ z in S, spatialPartial
      (show ParabolicPoint → ℝ from F) i z * G z ∂volume := by
  let G' : Vec3 × ℝ → ℝ := fun z =>
    spatialPartial (show ParabolicPoint → ℝ from G) i z
  have hG'compact : HasCompactSupport G' :=
    CKN.hasCompactSupport_spatialPartial hGc i
  have hG'support : tsupport G' ⊆ S :=
    (CKN.tsupport_spatialPartial_subset i).trans hGs
  have hIntF'G : Integrable
      (fun z : Vec3 × ℝ =>
        spatialPartial (show ParabolicPoint → ℝ from F) i z * G z) volume := by
    exact (continuous_mul_of_continuousOn_open_of_tsupport_subset
      hS hFpartialCont hGcont hGs).integrable_of_hasCompactSupport hGc.mul_left
  have hIntFG' : Integrable
      (fun z : Vec3 × ℝ => F z * G' z) volume := by
    exact (continuous_mul_of_continuousOn_open_of_tsupport_subset
      hS hFcont hGpartialCont hG'support).integrable_of_hasCompactSupport
        hG'compact.mul_left
  have hIntFG : Integrable (fun z : Vec3 × ℝ => F z * G z) volume := by
    exact (continuous_mul_of_continuousOn_open_of_tsupport_subset
      hS hFcont hGcont hGs).integrable_of_hasCompactSupport hGc.mul_left
  have hIBP := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (f := F) (f' := fun z => spatialPartial
      (show ParabolicPoint → ℝ from F) i z) (g := G) (g' := G')
    hIntF'G hIntFG' hIntFG
    (fun z hz => regularised_spatialPartial_hasLineDerivAt i
      (hFdiff z (hGs hz)))
    (fun z hz => by
      by_cases hzS : z ∈ S
      · exact regularised_spatialPartial_hasLineDerivAt i (hGdiff z hzS)
      · have hnot : z ∉ tsupport G := fun hmem => hzS (hGs hmem)
        have hzero : G =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
          rw [notMem_tsupport_iff_eventuallyEq] at hnot
          exact hnot
        have hG'zero : G' z = 0 := by
          exact spatialPartial_eq_zero_off_tsupport hnot i
        have hconst : HasLineDerivAt ℝ
            (fun _ : Vec3 × ℝ => (0 : ℝ)) 0 z (basisVec i, 0) := by
          simp [HasLineDerivAt, hasDerivAt_const]
        rw [hG'zero]
        exact hconst.congr_of_eventuallyEq hzero)
  have hleftSupport : tsupport
      (fun z : Vec3 × ℝ => F z * G' z) ⊆ S := by
    exact tsupport_mul_subset_right.trans hG'support
  have hrightSupport : tsupport
      (fun z : Vec3 × ℝ =>
        spatialPartial (show ParabolicPoint → ℝ from F) i z * G z) ⊆ S := by
    exact tsupport_mul_subset_right.trans hGs
  rw [regUniform_setIntegral_eq_integral_of_tsupport_subset
      hS.measurableSet hleftSupport,
    regUniform_setIntegral_eq_integral_of_tsupport_subset
      hS.measurableSet hrightSupport]
  simpa [G', mul_comm] using hIBP

private theorem regularised_timePartial_hasLineDerivAt
    {F : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hF : DifferentiableAt ℝ (fun t : ℝ => F (z.1, t)) z.2) :
    HasLineDerivAt ℝ F
      (timePartial (show ParabolicPoint → ℝ from F) z)
      z (0, 1) := by
  let f : ℝ → ℝ := fun t => F (z.1, t)
  have hF' : HasFDerivAt f (fderiv ℝ f z.2) z.2 := hF.hasFDerivAt
  have hcurve : HasDerivAt (fun t : ℝ => z.2 + t) 1 0 := by
    convert (hasDerivAt_const (x := 0) z.2).add
      ((hasDerivAt_id (0 : ℝ)).const_mul (1 : ℝ)) using 1
    · funext t
      simp
    · simp
  have hcomp := hF'.comp_hasDerivAt_of_eq 0 hcurve (by simp)
  change HasDerivAt (fun t : ℝ => F (z + t • (0, 1)))
    (timePartial (show ParabolicPoint → ℝ from F) z) 0
  convert hcomp using 1
  · funext t
    have hprod : z + t • (0, 1) = (z.1, z.2 + t) := by
      ext <;> simp
    rw [hprod]
    rfl
  · rfl

/-- Spatial product rule from differentiability of the two time slices. -/
theorem regUniform_spatialPartial_mul
    {F G : Vec3 × ℝ → ℝ} (x : Vec3) (t : ℝ) (j : Fin 3)
    (hF : DifferentiableAt ℝ (fun y : Vec3 => F (y, t)) x)
    (hG : DifferentiableAt ℝ (fun y : Vec3 => G (y, t)) x) :
    spatialPartial (show ParabolicPoint → ℝ from fun z => F z * G z) j (x, t) =
      F (x, t) * spatialPartial (show ParabolicPoint → ℝ from G) j (x, t) +
        G (x, t) * spatialPartial (show ParabolicPoint → ℝ from F) j (x, t) := by
  change (fderiv ℝ (fun y : Vec3 => F (y, t) * G (y, t)) x)
      (basisVec j) = _
  rw [fderiv_fun_mul hF hG]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change F (x, t) * spatialPartial (show ParabolicPoint → ℝ from G) j (x, t) +
      G (x, t) * spatialPartial (show ParabolicPoint → ℝ from F) j (x, t) = _
  ring

/-- Time product rule from differentiability of the two spatially fixed slices. -/
theorem regUniform_timePartial_mul
    {F G : Vec3 × ℝ → ℝ} (x : Vec3) (t : ℝ)
    (hF : DifferentiableAt ℝ (fun s : ℝ => F (x, s)) t)
    (hG : DifferentiableAt ℝ (fun s : ℝ => G (x, s)) t) :
    timePartial (show ParabolicPoint → ℝ from fun z => F z * G z) (x, t) =
      F (x, t) * timePartial (show ParabolicPoint → ℝ from G) (x, t) +
        G (x, t) * timePartial (show ParabolicPoint → ℝ from F) (x, t) := by
  change (fderiv ℝ (fun s : ℝ => F (x, s) * G (x, s)) t) 1 = _
  rw [fderiv_fun_mul hF hG]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change F (x, t) * timePartial (show ParabolicPoint → ℝ from G) (x, t) +
      G (x, t) * timePartial (show ParabolicPoint → ℝ from F) (x, t) = _
  ring

/-- Time integration by parts on an open carrier for a compactly supported
factor whose derivatives are controlled on that carrier. -/
theorem regUniform_integral_mul_timePartial_eq_neg
    {F G : Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)}
    (hS : IsOpen S)
    (hFcont : ContinuousOn F S)
    (hFtimeCont : ContinuousOn
      (fun z : Vec3 × ℝ => timePartial
        (show ParabolicPoint → ℝ from F) ((z.1, z.2) : ParabolicPoint)) S)
    (hFdiff : ∀ z ∈ S,
      DifferentiableAt ℝ (fun t : ℝ => F (z.1, t)) z.2)
    (hGcont : ContinuousOn G S)
    (hGtimeCont : ContinuousOn
      (fun z : Vec3 × ℝ => timePartial
        (show ParabolicPoint → ℝ from G) ((z.1, z.2) : ParabolicPoint)) S)
    (hGdiff : ∀ z ∈ S,
      DifferentiableAt ℝ (fun t : ℝ => G (z.1, t)) z.2)
    (hGc : HasCompactSupport G) (hGs : tsupport G ⊆ S) :
    (∫ z in S, F z * timePartial
      (show ParabolicPoint → ℝ from G) z ∂volume) =
    -∫ z in S, timePartial
      (show ParabolicPoint → ℝ from F) z * G z ∂volume := by
  let G' : Vec3 × ℝ → ℝ := fun z =>
    timePartial (show ParabolicPoint → ℝ from G) z
  have hG'compact : HasCompactSupport G' :=
    CKN.hasCompactSupport_timePartial hGc
  have hG'support : tsupport G' ⊆ S :=
    (CKN.tsupport_timePartial_subset G).trans hGs
  have hIntF'G : Integrable
      (fun z : Vec3 × ℝ =>
        timePartial (show ParabolicPoint → ℝ from F) z * G z) volume := by
    exact (continuous_mul_of_continuousOn_open_of_tsupport_subset
      hS hFtimeCont hGcont hGs).integrable_of_hasCompactSupport hGc.mul_left
  have hIntFG' : Integrable
      (fun z : Vec3 × ℝ => F z * G' z) volume := by
    exact (continuous_mul_of_continuousOn_open_of_tsupport_subset
      hS hFcont hGtimeCont hG'support).integrable_of_hasCompactSupport
        hG'compact.mul_left
  have hIntFG : Integrable (fun z : Vec3 × ℝ => F z * G z) volume := by
    exact (continuous_mul_of_continuousOn_open_of_tsupport_subset
      hS hFcont hGcont hGs).integrable_of_hasCompactSupport hGc.mul_left
  have hIBP := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (f := F) (f' := fun z => timePartial
      (show ParabolicPoint → ℝ from F) z) (g := G) (g' := G')
    hIntF'G hIntFG' hIntFG
    (fun z hz => regularised_timePartial_hasLineDerivAt
      (hFdiff z (hGs hz)))
    (fun z hz => by
      by_cases hzS : z ∈ S
      · exact regularised_timePartial_hasLineDerivAt (hGdiff z hzS)
      · have hnot : z ∉ tsupport G := fun hmem => hzS (hGs hmem)
        have hzero : G =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
          rw [notMem_tsupport_iff_eventuallyEq] at hnot
          exact hnot
        have hG'zero : G' z = 0 := by
          exact timePartial_eq_zero_off_tsupport hnot
        have hconst : HasLineDerivAt ℝ
            (fun _ : Vec3 × ℝ => (0 : ℝ)) 0 z (0, 1) := by
          simp [HasLineDerivAt, hasDerivAt_const]
        rw [hG'zero]
        exact hconst.congr_of_eventuallyEq hzero)
  have hleftSupport : tsupport
      (fun z : Vec3 × ℝ => F z * G' z) ⊆ S := by
    exact tsupport_mul_subset_right.trans hG'support
  have hrightSupport : tsupport
      (fun z : Vec3 × ℝ =>
        timePartial (show ParabolicPoint → ℝ from F) z * G z) ⊆ S := by
    exact tsupport_mul_subset_right.trans hGs
  rw [regUniform_setIntegral_eq_integral_of_tsupport_subset
      hS.measurableSet hleftSupport,
    regUniform_setIntegral_eq_integral_of_tsupport_subset
      hS.measurableSet hrightSupport]
  simpa [G', mul_comm] using hIBP

/-- A compactly supported spatial derivative has zero integral on an open
carrier containing its support. -/
theorem regUniform_integral_spatialPartial_eq_zero
    {G : Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)} (i : Fin 3)
    (hS : IsOpen S) (hGcont : ContinuousOn G S)
    (hGpartialCont : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial
        (show ParabolicPoint → ℝ from G) i
        ((z.1, z.2) : ParabolicPoint)) S)
    (hGdiff : ∀ z ∈ S,
      DifferentiableAt ℝ (fun x : Vec3 => G (x, z.2)) z.1)
    (hGc : HasCompactSupport G) (hGs : tsupport G ⊆ S) :
    (∫ z in S, spatialPartial (show ParabolicPoint → ℝ from G) i z
      ∂volume) = 0 := by
  have hFcont : ContinuousOn (fun _ : Vec3 × ℝ => (1 : ℝ)) S :=
    continuousOn_const
  have hFpartial : ContinuousOn
      (fun z : Vec3 × ℝ =>
        spatialPartial (fun _ : ParabolicPoint => (1 : ℝ)) i
          ((z.1, z.2) : ParabolicPoint)) S := by
    have heq : (fun z : Vec3 × ℝ => spatialPartial
        (fun _ : ParabolicPoint => (1 : ℝ)) i
          ((z.1, z.2) : ParabolicPoint)) = fun _ => (0 : ℝ) := by
      funext z
      simp [spatialPartial]
    rw [heq]
    exact continuousOn_const
  have h := regUniform_integral_mul_spatialPartial_eq_neg
    (F := fun _ => (1 : ℝ)) (G := G) i hS hFcont hFpartial
    (fun z hz => by fun_prop) hGcont hGpartialCont hGdiff hGc hGs
  simpa [spatialPartial] using h

/-- A compactly supported time derivative has zero integral on an open
carrier containing its support. -/
theorem regUniform_integral_timePartial_eq_zero
    {G : Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)}
    (hS : IsOpen S) (hGcont : ContinuousOn G S)
    (hGtimeCont : ContinuousOn
      (fun z : Vec3 × ℝ => timePartial
        (show ParabolicPoint → ℝ from G) ((z.1, z.2) : ParabolicPoint)) S)
    (hGdiff : ∀ z ∈ S,
      DifferentiableAt ℝ (fun t : ℝ => G (z.1, t)) z.2)
    (hGc : HasCompactSupport G) (hGs : tsupport G ⊆ S) :
    (∫ z in S, timePartial (show ParabolicPoint → ℝ from G) z
      ∂volume) = 0 := by
  have hFcont : ContinuousOn (fun _ : Vec3 × ℝ => (1 : ℝ)) S :=
    continuousOn_const
  have hFtime : ContinuousOn
      (fun z : Vec3 × ℝ =>
        timePartial (fun _ : ParabolicPoint => (1 : ℝ))
          ((z.1, z.2) : ParabolicPoint)) S := by
    have heq : (fun z : Vec3 × ℝ => timePartial
        (fun _ : ParabolicPoint => (1 : ℝ))
          ((z.1, z.2) : ParabolicPoint)) = fun _ => (0 : ℝ) := by
      funext z
      simp [timePartial]
    rw [heq]
    exact continuousOn_const
  have h := regUniform_integral_mul_timePartial_eq_neg
    (F := fun _ => (1 : ℝ)) (G := G) hS hFcont hFtime
    (fun z hz => by fun_prop) hGcont hGtimeCont hGdiff hGc hGs
  simpa [timePartial] using h

end CKN.Leray

end
