/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WholePlaneCoefficientScaling

/-!
# Coordinates of vector-valued tempered distributions on the whole plane

This file defines the coordinate maps `wholePlaneCoordTempered i` from `C3`-valued to scalar
tempered distributions on `ℝ²` and proves that they commute with distributional line
differentiation (`wholePlaneCoordTempered_lineDeriv`) and with the embedding of `L²`
(`wholePlaneCoordTempered_l2`).  They are used to identify the coordinates of weak `H¹` and
`H²` fields.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped LineDeriv SchwartzMap

/-! ## Coordinate maps on vector-valued tempered distributions -/

/-- Extract the `i`-th coordinate of a `C3`-valued tempered distribution. -/
def wholePlaneCoordTempered (i : Fin 3) :
    TemperedDistribution WholePlane C3 →L[ℂ]
      TemperedDistribution WholePlane ℂ :=
  PointwiseConvergenceCLM.postcomp (SchwartzMap WholePlane ℂ)
    (EuclideanSpace.proj i)

/-- Coordinate extraction is applied after testing: the `i`-th coordinate distribution
evaluated on `f` is the `i`-th component of the vector value `T f`. -/
@[simp] theorem wholePlaneCoordTempered_apply_apply (i : Fin 3)
    (T : TemperedDistribution WholePlane C3)
    (f : SchwartzMap WholePlane ℂ) :
    wholePlaneCoordTempered i T f = (T f) i :=
  rfl

/-- Coordinate extraction commutes with distributional line differentiation. -/
theorem wholePlaneCoordTempered_lineDeriv (i : Fin 3)
    (e : WholePlane) (T : TemperedDistribution WholePlane C3) :
    wholePlaneCoordTempered i (∂_{e} T) =
      ∂_{e} (wholePlaneCoordTempered i T) := by
  ext f
  rfl

/-- Coordinate extraction commutes with the canonical `L² → tempered distribution`
embedding. -/
theorem wholePlaneCoordTempered_l2 (i : Fin 3) (b : WholePlaneC3L2) :
    wholePlaneCoordTempered i (wholePlaneL2ToTempered C3 b) =
      wholePlaneL2ToTempered ℂ (wholePlaneCoordL2 i b) := by
  ext f
  simp only [wholePlaneCoordTempered_apply_apply,
    wholePlaneL2ToTempered_apply, MeasureTheory.Lp.toTemperedDistribution_apply]
  have hint : Integrable (fun x : WholePlane ↦ f x • (b x : C3)) volume :=
    memLp_one_iff_integrable.mp <|
      (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] C3 →L[ℂ] C3).memLp_of_bilin
        1 (f.memLp 2 volume) (Lp.memLp b)
  calc
    (EuclideanSpace.proj i) (∫ x : WholePlane, f x • (b x : C3) ∂volume) =
        ∫ x : WholePlane, (EuclideanSpace.proj i) (f x • (b x : C3))
          ∂volume :=
      ((EuclideanSpace.proj i).integral_comp_comm hint).symm
    _ = ∫ x : WholePlane,
          f x • ((wholePlaneCoordL2 i b : WholePlane → ℂ) x)
          ∂volume := by
      apply integral_congr_ae
      filter_upwards [
        (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
          (p := 2) (μ := (volume : Measure WholePlane)) b] with x hx
      calc
        (EuclideanSpace.proj i) (f x • (b x : C3)) =
            f x • (EuclideanSpace.proj i) (b x : C3) := by simp
        _ = f x • ((wholePlaneCoordL2 i b : WholePlane → ℂ) x) := by
          simpa [wholePlaneCoordL2] using
            congrArg (fun z : ℂ ↦ f x • z) hx.symm

end

end FastDynamo
