/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.WitnessCubeSideGeometry
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.SobolevPublic
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.EuclideanGagliardoCoordinateBridgeP
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.CubeFractionalNormBridge

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.EnergyPrice.ForceBesovFromHsNormSq

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Gate R2-besov: `ForceBesovRegularity` from the Euclidean fractional carrier

The frozen clause supplies the datum's regularity as `hsNormSq U s₀ g₀.grad ≠ ⊤`
while the upstream Dirichlet energy package asks for
`ForceBesovRegularity`.  No producer of the latter from the former exists
anywhere in this development.

`HCPoly.Provider.PolynomialHomogenization.Root.BufferToCell.PositiveBesovContinuousComparison`
has a `private` bridge `forceSobolevRegularity_of_hsNormSq_lt_top` whose
`ForceBesovRegularity` premise is consumed **only** through `.memLp`, at two
sites, and whose `MemVectorL2` premise is consumed **only** through `.1`.  That
declaration is `private`, so the bridge and
its one `private` measurability helper are re-proved below with the premise
weakened to bare `MemLp` — the "one-hypothesis swap".  Composing with upstream
`ForceSobolevRegularity.toForceBesovRegularity` closes the gate.
-/

namespace HCPolySupport
namespace HighContrast
namespace EnergyPrice

open Book Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Re-proof of a private Gagliardo-kernel measurability helper. -/
theorem scalarGagliardoKernel_aestronglyMeasurable'
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d)
    (hFnorm : AEStronglyMeasurable F (normalizedCubeMeasure Q))
    (hFcube : AEStronglyMeasurable F (cubeMeasure Q)) (i : Fin d) :
    AEStronglyMeasurable
      (Gagliardo.gagliardoKernel s (2 : ℝ≥0∞) (fun x => F x i))
      (Gagliardo.gagliardoCubeMeasure Q) := by
  have : SFinite (cubeMeasure Q) := by
    unfold cubeMeasure
    infer_instance
  have hfirst : AEStronglyMeasurable (fun z : Vec d × Vec d => F z.1 i)
      ((normalizedCubeMeasure Q).prod (cubeMeasure Q)) :=
    ((continuous_apply i).comp_aestronglyMeasurable
      hFnorm).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst
  have hsecond : AEStronglyMeasurable (fun z : Vec d × Vec d => F z.2 i)
      ((normalizedCubeMeasure Q).prod (cubeMeasure Q)) :=
    ((continuous_apply i).comp_aestronglyMeasurable
      hFcube).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd
  have hdiff : AEStronglyMeasurable
      (fun z : Vec d × Vec d => F z.1 i - F z.2 i)
      ((normalizedCubeMeasure Q).prod (cubeMeasure Q)) :=
    hfirst.sub hsecond
  have hweight : StronglyMeasurable
      (fun z : Vec d × Vec d =>
        dist z.1 z.2 ^ (-Gagliardo.kernelExponent d s (2 : ℝ≥0∞))) :=
    ((continuous_fst.dist continuous_snd).measurable.pow
      measurable_const).stronglyMeasurable
  unfold Gagliardo.gagliardoKernel Gagliardo.gagliardoCubeMeasure
  exact hweight.aestronglyMeasurable.smul hdiff

/-- **The swapped bridge.**  The `ForceBesovRegularity` premise of the
private bridge is replaced by bare `MemLp`; the proof is otherwise unchanged. -/
theorem forceSobolevRegularity_of_hsNormSq_lt_top'
    [NeZero d] (Q : TriadicCube d) (sF : FractionalOrder)
    (F : Vec d → Vec d)
    (hmem : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hFcube : MemVectorL2 (openCubeSet Q) F)
    (hHs : hsNormSq (openCubeSet Q) sF.1 F < ⊤) :
    Legacy.ForceSobolevRegularity Q sF.1 F := by
  intro i
  have hmemi : MemLp (fun x => F x i) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hmem
  have hFcubeMeas : AEStronglyMeasurable F (cubeMeasure Q) := by
    simpa [cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
      hFcube.aestronglyMeasurable
  refine ⟨hmemi, ?_⟩
  rw [Gagliardo.memWsp_iff]
  constructor
  · exact scalarGagliardoKernel_aestronglyMeasurable' Q sF.1 F
      hmem.aestronglyMeasurable hFcubeMeas i
  · have hcoord :
        (Gagliardo.cubeGagliardoESeminorm Q sF.1 (2 : ℝ≥0∞)
          (fun x => F x i)) ^ (2 : ℝ) ≤
          cubeCoordinateGagliardoPowerEnergy Q sF FiniteLpExponent.two F := by
      unfold cubeCoordinateGagliardoPowerEnergy
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin d =>
          (Gagliardo.cubeGagliardoESeminorm Q sF.1 (2 : ℝ≥0∞)
            (fun x => F x j)) ^ (2 : ℝ))
        (fun _j _ => zero_le)
        (Finset.mem_univ i)
    have hamb := cubeCoordinateGagliardoPowerEnergy_le_dimension_mul_ambientHilbert
      Q sF FiniteLpExponent.two F
    have hK : AEStronglyMeasurable (cubeAmbientHilbertWspKernel sF FiniteLpExponent.two F)
        (Gagliardo.gagliardoCubeMeasure Q) := by
      have : SFinite (cubeMeasure Q) := by
        unfold cubeMeasure
        infer_instance
      have hfst := hmem.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_fst (ν := cubeMeasure Q))
      have hsnd := hFcubeMeas.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_snd (μ := normalizedCubeMeasure Q))
      exact ((continuous_fst.dist continuous_snd).measurable.pow
        measurable_const).aestronglyMeasurable.smul
          ((HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable (hfst.sub hsnd))
    have heuc := cubeAmbientHilbertWspESeminorm_rpow_le_metricComparisonConstant_mul
      Q sF FiniteLpExponent.two F hK
    have hfrac := cubeEuclideanWspESeminorm_two_sq_eq_fracSeminormSq
      Q sF F hFcube.aestronglyMeasurable
    have hfrac_le : fracSeminormSq (openCubeSet Q) sF.1 F ≤
        hsNormSq (openCubeSet Q) sF.1 F := by
      unfold hsNormSq
      exact le_add_left le_rfl
    have hright :
        (d : ℝ≥0∞) * cubeEuclideanWspMetricComparisonConstant d
            FiniteLpExponent.two *
          fracSeminormSq (openCubeSet Q) sF.1 F < ⊤ := by
      exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (by simp)
          (cubeEuclideanWspMetricComparisonConstant_lt_top d
            FiniteLpExponent.two))
        (lt_of_le_of_lt hfrac_le hHs)
    have hpow :
        (Gagliardo.cubeGagliardoESeminorm Q sF.1 (2 : ℝ≥0∞)
          (fun x => F x i)) ^ (2 : ℝ) < ⊤ := by
      refine lt_of_le_of_lt (hcoord.trans (hamb.trans ?_)) hright
      calc
        (d : ℝ≥0∞) *
            cubeAmbientHilbertWspESeminorm Q sF FiniteLpExponent.two F ^
              FiniteLpExponent.two.exponent.toReal ≤
          (d : ℝ≥0∞) *
            (cubeEuclideanWspMetricComparisonConstant d FiniteLpExponent.two *
              cubeEuclideanWspESeminorm Q sF FiniteLpExponent.two F ^
                FiniteLpExponent.two.exponent.toReal) :=
          mul_le_mul_right heuc _
        _ = (d : ℝ≥0∞) *
            cubeEuclideanWspMetricComparisonConstant d FiniteLpExponent.two *
              fracSeminormSq (openCubeSet Q) sF.1 F := by
          norm_num only [FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat]
          rw [ENNReal.rpow_two, hfrac]
          ring_nf
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp hpow

/-- **Gate R2-besov, closed.**  The Chapter 3 Besov regularity of a field
follows from its `MemLp` membership, its square integrability on the cube, and
the finiteness of HCPoly's Euclidean fractional carrier at the same order. -/
theorem forceBesovRegularity_of_hsNormSq_ne_top [NeZero d]
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (F : Vec d → Vec d)
    (hmem : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hFcube : MemVectorL2 (openCubeSet Q) F)
    (hHs : hsNormSq (openCubeSet Q) s F ≠ ⊤) :
    ForceBesovRegularity Q s F := by
  have hsob : Legacy.ForceSobolevRegularity Q s F :=
    forceSobolevRegularity_of_hsNormSq_lt_top' Q ⟨s, hs, hs1⟩ F hmem hFcube
      (lt_of_le_of_ne le_top hHs)
  exact hsob.toForceBesovRegularity hs hs1.le

end

end EnergyPrice
end HighContrast
end HCPolySupport
