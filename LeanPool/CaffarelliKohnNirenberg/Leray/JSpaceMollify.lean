/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpace
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Spatial mollification of Leray data

These definitions and estimates prepare the smooth approximation step in
`lem:J-weak-div`.
-/

public section

open MeasureTheory
open Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Convolution Topology

noncomputable section

namespace CKN

/-- Componentwise spatial mollification of a three-dimensional vector field. -/
@[expose]
def spatialMollifyVec3 (a : Vec3 → Vec3) (ε : ℝ) (hε : 0 < ε) : Vec3 → Vec3 :=
  fun x i => CKN.mollify (fun y => a y i) ε hε x

/-- Spatial mollification makes every component smooth. -/
theorem spatialMollifyVec3_contDiff {a : Vec3 → Vec3} {ε : ℝ} (hε : 0 < ε)
    (ha : MemLp a (2 : ℝ≥0∞) volume) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialMollifyVec3 a ε hε) := by
  apply contDiff_pi.mpr
  intro i
  exact CKN.mollify_contDiff (d := 3) hε
    ((ha.eval i).locallyIntegrable (by norm_num))

/-- Spatial mollification preserves square integrability componentwise. -/
theorem spatialMollifyVec3_memLp {a : Vec3 → Vec3} {ε : ℝ} (hε : 0 < ε)
    (ha : MemLp a (2 : ℝ≥0∞) volume) :
    MemLp (spatialMollifyVec3 a ε hε) (2 : ℝ≥0∞) volume := by
  apply MemLp.of_eval
  intro i
  have hai : MemLp (fun x : Vec3 => a x i) (2 : ℝ≥0∞) volume := ha.eval i
  have hkernelCont : Continuous (CKN.mollifier (d := 3) ε hε) :=
    (CKN.mollifier_contDiff (d := 3) hε (n := 0)).continuous
  have hkernelCompact : HasCompactSupport (CKN.mollifier (d := 3) ε hε) :=
    CKN.mollifier_hasCompactSupport (d := 3) hε
  have hkernelInt : Integrable (CKN.mollifier (d := 3) ε hε) volume :=
    hkernelCont.integrable_of_hasCompactSupport hkernelCompact
  have hbound := CKN.young_convolution_nonneg_integral_one_of_aemeasurable
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    (CKN.mollifier_nonneg (d := 3) hε) hkernelInt
    (CKN.mollifier_integral_one (d := 3) hε)
    ((CKN.mollifier_contDiff (d := 3) hε (n := 0)).continuous.measurable)
    hai.aestronglyMeasurable.aemeasurable
  rw [memLp_iff]
  exact (show eLpNorm (fun x : Vec3 => spatialMollifyVec3 a ε hε x i)
      (2 : ℝ≥0∞) volume ≤ eLpNorm (fun x : Vec3 => a x i) 2 volume by
        simpa [spatialMollifyVec3, CKN.mollify, CKN.mollifier] using hbound).trans_lt
    hai.eLpNorm_lt_top

/-- Spatial mollification converges in `L²` for vector fields in `L²`. -/
theorem spatialMollifyVec3_tendsto_L2 {a : Vec3 → Vec3}
    (ha : MemLp a (2 : ℝ≥0∞) volume) :
    Tendsto
      (fun n : ℕ => eLpNorm
        (spatialMollifyVec3 a (1 / ((n + 1 : ℕ) : ℝ)) (by positivity) - a)
        (2 : ℝ≥0∞) volume)
      atTop (nhds 0) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
  have hdenom : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hε : Tendsto ε atTop (nhds 0) := by
    simpa [ε] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).div_atTop hdenom
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  let mollified : ℕ → Vec3 → Vec3 := fun n =>
    spatialMollifyVec3 a (ε n) (hεpos n)
  let coordError : ℕ → Fin 3 → Vec3 → ℝ := fun n i x => mollified n x i - a x i
  let major : ℕ → Vec3 → ℝ := fun n x => ∑ i : Fin 3, ‖coordError n i x‖
  have hcomponentLimit (i : Fin 3) :
      Tendsto (fun n : ℕ => eLpNorm (coordError n i) (2 : ℝ≥0∞) volume)
        atTop (nhds 0) := by
    have h := CKN.tendsto_eLpNorm_sub_zero_mollify
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      (ha.eval i) hε hεpos
    simpa [coordError, mollified, ε, spatialMollifyVec3] using h
  have hcoordMemLp (n : ℕ) (i : Fin 3) : MemLp (coordError n i) 2 volume := by
    exact (spatialMollifyVec3_memLp (hεpos n) ha).eval i |>.sub (ha.eval i)
  have hmajorMemLp (n : ℕ) : MemLp (major n) 2 volume := by
    have hsum := memLp_finsetSum (μ := volume) (p := (2 : ℝ≥0∞))
      (s := Finset.univ) (f := fun i x => ‖coordError n i x‖)
      (fun i hi => (hcoordMemLp n i).norm)
    simpa [major] using hsum
  have hmajorMeas (n : ℕ) : AEStronglyMeasurable (major n) volume :=
    (hmajorMemLp n).aestronglyMeasurable
  have hsumLimit : Tendsto
      (fun n : ℕ => ∑ i : Fin 3, eLpNorm (coordError n i) (2 : ℝ≥0∞) volume)
      atTop (nhds 0) := by
    have h := tendsto_finsetSum (s := Finset.univ)
      (fun i hi => hcomponentLimit i)
    simpa using h
  have hmajorLimit : Tendsto (fun n : ℕ => eLpNorm (major n) (2 : ℝ≥0∞) volume)
      atTop (nhds 0) := by
    have hbound (n : ℕ) : eLpNorm (major n) (2 : ℝ≥0∞) volume ≤
        ∑ i : Fin 3, eLpNorm (coordError n i) (2 : ℝ≥0∞) volume := by
      calc
        eLpNorm (major n) (2 : ℝ≥0∞) volume ≤
            ∑ i : Fin 3, eLpNorm (fun x => ‖coordError n i x‖) (2 : ℝ≥0∞) volume := by
              have hmajorEq : major n =
                  ∑ i : Fin 3, (fun x => ‖coordError n i x‖) := by
                funext x
                simp [major]
              rw [hmajorEq]
              simpa using (eLpNorm_sum_le (μ := volume) (p := (2 : ℝ≥0∞))
                (f := fun i x => ‖coordError n i x‖) (s := Finset.univ)
                (by norm_num : (1 : ℝ≥0∞) ≤ 2))
        _ = ∑ i : Fin 3, eLpNorm (coordError n i) (2 : ℝ≥0∞) volume := by
              apply Finset.sum_congr rfl
              intro i hi
              exact eLpNorm_norm (coordError n i) (hcoordMemLp n i).aestronglyMeasurable
    have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ eLpNorm (major n) (2 : ℝ≥0∞) volume :=
      Filter.Eventually.of_forall fun n => bot_le
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsumLimit
      hnonneg (Filter.Eventually.of_forall hbound)
  have herrorMeas (n : ℕ) :
      AEStronglyMeasurable (fun x : Vec3 => mollified n x - a x) volume := by
    exact (spatialMollifyVec3_contDiff (hεpos n) ha).continuous.aestronglyMeasurable.sub
      ha.aestronglyMeasurable
  have hpoint (n : ℕ) (x : Vec3) :
      ‖mollified n x - a x‖ ≤ ‖major n x‖ := by
    have hnonneg : 0 ≤ major n x := by
      exact Finset.sum_nonneg fun i _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    apply (pi_norm_le_iff_of_nonneg hnonneg).2
    intro i
    calc
      ‖(mollified n x - a x) i‖ ≤ ∑ j : Fin 3, ‖(mollified n x - a x) j‖ :=
        Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
      _ = major n x := by simp [major, coordError, mollified]
  have herrorBound (n : ℕ) :
      eLpNorm (mollified n - a) (2 : ℝ≥0∞) volume ≤ eLpNorm (major n) 2 volume :=
    eLpNorm_mono (herrorMeas n) (fun x => hpoint n x)
  have hlimMajor : Tendsto (fun n : ℕ => eLpNorm (mollified n - a) (2 : ℝ≥0∞) volume)
      atTop (nhds 0) := by
    have hnonneg : ∀ᶠ n : ℕ in atTop,
        0 ≤ eLpNorm (mollified n - a) (2 : ℝ≥0∞) volume :=
      Filter.Eventually.of_forall fun n => bot_le
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajorLimit
      hnonneg (Filter.Eventually.of_forall herrorBound)
  exact hlimMajor.congr' (Filter.Eventually.of_forall fun n => by
    simp [mollified, ε])

private theorem spatialMollifyVec3_component_fderiv_formula
    {a : Vec3 → Vec3} {ε : ℝ} (hε : 0 < ε)
    (ha : MemLp a (2 : ℝ≥0∞) volume) (i : Fin 3) (x : Vec3) :
    (fderiv ℝ (fun z => spatialMollifyVec3 a ε hε z i) x) (basisVec i) =
      ∫ t, (fderiv ℝ (CKN.mollifier (d := 3) ε hε) t) (basisVec i) *
        a (x - t) i ∂volume := by
  have hfd := (CKN.mollifier_hasCompactSupport (d := 3) hε).hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (CKN.mollifier_contDiff (d := 3) hε (n := 1))
    ((ha.eval i).locallyIntegrable (by norm_num)) x
  have hconv : ConvolutionExists (fderiv ℝ (CKN.mollifier (d := 3) ε hε))
      (fun y => a y i) ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Vec3) volume := by
    exact HasCompactSupport.convolutionExists_left
      (𝕜 := ℝ) (G := Vec3) (E := Vec3 →L[ℝ] ℝ) (E' := ℝ)
      (F := Vec3 →L[ℝ] ℝ) ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Vec3)
      ((CKN.mollifier_hasCompactSupport (d := 3) hε).fderiv (𝕜 := ℝ))
      ((CKN.mollifier_contDiff (d := 3) hε (n := 2)).continuous_fderiv (by simp))
      ((ha.eval i).locallyIntegrable (by norm_num))
  change (fderiv ℝ (CKN.mollify (fun y => a y i) ε hε) x) (basisVec i) = _
  rw [(by simpa [spatialMollifyVec3, CKN.mollify] using hfd.fderiv :
    fderiv ℝ (CKN.mollify (fun y => a y i) ε hε) x =
      (MeasureTheory.convolution (fderiv ℝ (CKN.mollifier (d := 3) ε hε))
        (fun y => a y i)
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Vec3) volume) x)]
  simp only [MeasureTheory.convolution]
  rw [ContinuousLinearMap.integral_apply (hconv x) (basisVec i)]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  simp only [smul_eq_mul]

/-- Spatial mollification preserves weak divergence-freeness pointwise. -/
theorem spatialMollifyVec3_divergence_eq_zero {a : Vec3 → Vec3}
    {ε : ℝ} (hε : 0 < ε) (ha : IsWeakDivFreeL2 a) (x : Vec3) :
    ∑ i : Fin 3, spatialDeriv
      (fun y => spatialMollifyVec3 a ε hε y i) i x = 0 := by
  let kernel : Vec3 → ℝ := CKN.mollifier (d := 3) ε hε
  have hkernel : ContDiff ℝ (⊤ : ℕ∞) kernel := CKN.mollifier_contDiff hε
  have hkernelCompact : HasCompactSupport kernel := CKN.mollifier_hasCompactSupport hε
  let ψ : WeakTestFunction (Set.univ : Set Vec3) :=
    ⟨fun y => kernel (x - y),
      hkernel.comp (contDiff_const.sub contDiff_id),
      hkernelCompact.comp_homeomorph (Homeomorph.subLeft x),
      Set.subset_univ _⟩
  have hψderiv (y : Vec3) (i : Fin 3) :
      ψ.partialDeriv i y = -(fderiv ℝ kernel (x - y)) (basisVec i) := by
    have hinner : HasFDerivAt (fun z : Vec3 => x - z)
        (-(1 : Vec3 →L[ℝ] Vec3)) y := (hasFDerivAt_id y).const_sub x
    have houter : HasFDerivAt kernel (fderiv ℝ kernel (x - y)) (x - y) :=
      (hkernel.differentiable (by simp) (x - y)).hasFDerivAt
    have hcomp := houter.comp y hinner
    change (fderiv ℝ (fun z => kernel (x - z)) y) (basisVec i) = _
    simpa [ContinuousLinearMap.comp_apply, Function.comp_def] using
      congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hcomp.fderiv
  have hgradCont (i : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => ψ.partialDeriv i y) :=
    CKN.contDiff_spatialDeriv_smooth ψ.contDiff i
  have hgradCompact (i : Fin 3) :
      HasCompactSupport (fun y : Vec3 => ψ.partialDeriv i y) := by
    change HasCompactSupport (fun y => (fderiv ℝ ψ.toFun y) (basisVec i))
    exact ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hgradLp (i : Fin 3) :
      MemLp (fun y : Vec3 => ψ.partialDeriv i y) (2 : ℝ≥0∞) volume :=
    (hgradCont i).continuous.memLp_of_hasCompactSupport (hgradCompact i)
  have hrealTriple : Real.HolderTriple 2 2 1 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  have htriple : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := by
    simpa using hrealTriple.ennrealOfReal
  have hpartsInt (i : Fin 3) :
      Integrable (fun y : Vec3 => a y i * ψ.partialDeriv i y) volume :=
    (ha.1.eval i).integrable_mul (hgradLp i)
  have hsumInt :
      ∫ y : Vec3, ∑ i : Fin 3, a y i * ψ.partialDeriv i y ∂volume =
        ∑ i : Fin 3, ∫ y : Vec3, a y i * ψ.partialDeriv i y ∂volume := by
    simpa using integral_finsetSum (μ := volume) Finset.univ
      (f := fun i y => a y i * ψ.partialDeriv i y)
      (by intro i hi; exact hpartsInt i)
  have hweakSum :
      ∑ i : Fin 3, ∫ y : Vec3, a y i * ψ.partialDeriv i y ∂volume = 0 := by
    rw [← hsumInt]
    exact ha.2 ψ
  have hchange (i : Fin 3) :
      ∫ y : Vec3, a y i * (fderiv ℝ kernel (x - y)) (basisVec i) ∂volume =
        ∫ t : Vec3, (fderiv ℝ kernel t) (basisVec i) * a (x - t) i ∂volume := by
    have h := (MeasureTheory.Measure.measurePreserving_sub_left volume x).integral_comp
      (Homeomorph.subLeft x).measurableEmbedding
      (fun y => a y i * (fderiv ℝ kernel (x - y)) (basisVec i))
    rw [← h]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [sub_sub_cancel]
    ring
  have hpart (i : Fin 3) :
      ∫ y : Vec3, a y i * ψ.partialDeriv i y ∂volume =
        -(∫ t : Vec3, (fderiv ℝ kernel t) (basisVec i) * a (x - t) i ∂volume) := by
    have hfun : (fun y : Vec3 => a y i * ψ.partialDeriv i y) =
        fun y => -(a y i * (fderiv ℝ kernel (x - y)) (basisVec i)) := by
      funext y
      rw [hψderiv]
      ring
    rw [hfun, integral_neg, hchange]
  have hsumKernel :
      ∑ i : Fin 3, ∫ t : Vec3,
        (fderiv ℝ kernel t) (basisVec i) * a (x - t) i ∂volume = 0 := by
    have hneg : -(∑ i : Fin 3, ∫ t : Vec3,
        (fderiv ℝ kernel t) (basisVec i) * a (x - t) i ∂volume) = 0 := by
      simpa [hpart, ← Finset.sum_neg_distrib] using hweakSum
    exact neg_eq_zero.mp hneg
  calc
    ∑ i : Fin 3, spatialDeriv
        (fun y => spatialMollifyVec3 a ε hε y i) i x =
      ∑ i : Fin 3, ∫ t : Vec3,
        (fderiv ℝ kernel t) (basisVec i) * a (x - t) i ∂volume := by
          apply Finset.sum_congr rfl
          intro i hi
          exact spatialMollifyVec3_component_fderiv_formula hε ha.1 i x
    _ = 0 := hsumKernel


end CKN

end
