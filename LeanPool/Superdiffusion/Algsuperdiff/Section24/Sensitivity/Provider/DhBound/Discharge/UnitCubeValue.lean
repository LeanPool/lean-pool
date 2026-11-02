/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.VectorPerturbation
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.UnitCube
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeSkewW2Infinity.ValueL2

/-!
# UnitCubeValue

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `L^∞` bookkeeping for the frozen unit-cube perturbation

The frozen `W^{1,∞}` norm

```
h.w1Infinity = max ‖∇h‖_{L^∞(□₀)} ‖h‖_{L^∞(□₀)}
```

dominates the entries of `h` itself, exactly as `gradientW1Infinity` dominates
the entries of `∇h`.  `Provider.DhBound.Lipschitz.UnitCube` records the
derivative half; this module records the value half and transports the frozen
`L^∞` memberships from the open-cube carrier to the normalized cube measure that
the Besov machinery integrates against.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Section24 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Transporting `L^∞` data to the normalized cube measure -/

/-- The frozen open-cube carrier is the open cube of the origin triadic cube. -/
theorem cubeDomain_originCube_coe (d : ℕ) :
    ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)) =
      openCubeSet (originCube d 0) := Ch02.cubeDomain_coe _

theorem memLp_normalizedCubeMeasure_of_memLp_frozen_carrier {E : Type*}
    [NormedAddCommGroup E] {q : ℝ≥0∞} {f : Vec d → E}
    (hf : MemLp f q
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))) :
    MemLp f q (normalizedCubeMeasure (originCube d 0)) := by
  rw [cubeDomain_originCube_coe] at hf
  have hcube : MemLp f q (cubeMeasure (originCube d 0)) := by
    rw [cubeMeasure, HCPolySupport.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact hf
  rw [normalizedCubeMeasure]
  exact hcube.smul_measure ENNReal.ofReal_ne_top

/-- Any a.e. property on the frozen open-cube carrier holds a.e. for the
normalized cube measure. -/
theorem ae_normalizedCubeMeasure_of_ae_frozen_carrier {P : Vec d → Prop}
    (h : ∀ᵐ x ∂volumeMeasureOn
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)), P x) :
    ∀ᵐ x ∂ normalizedCubeMeasure (originCube d 0), P x := by
  rw [cubeDomain_originCube_coe] at h
  have hcube : ∀ᵐ x ∂ cubeMeasure (originCube d 0), P x := by
    rw [cubeMeasure, HCPolySupport.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact h
  rw [normalizedCubeMeasure]
  exact MeasureTheory.Measure.ae_smul_measure hcube _

theorem ae_frozen_carrier_iff_normalizedCubeMeasure {E : Type*}
    {f g : Vec d → E}
    (h : f =ᵐ[volumeMeasureOn
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))] g) :
    f =ᵐ[normalizedCubeMeasure (originCube d 0)] g := by
  rw [cubeDomain_originCube_coe] at h
  have hcube : f =ᵐ[cubeMeasure (originCube d 0)] g := by
    rw [cubeMeasure, HCPolySupport.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact h
  rw [normalizedCubeMeasure]
  exact MeasureTheory.Measure.ae_smul_measure hcube _

/-! ## The value half of the frozen `W^{1,∞}` norm -/

theorem toReal_eLpNorm_matrixNorm_le_w1Infinity (h : UnitCubeSkewW2Infinity d) :
    ENNReal.toReal (eLpNorm (fun x => matrixNorm (h.toLInfSkewMatrixFieldOn.1.1 x)) ∞
        (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))) ≤
      h.w1Infinity := by
  simp only [UnitCubeSkewW2Infinity.w1Infinity]
  exact le_max_right _ _

/-- Every entry of the frozen matrix field is bounded a.e. by `w1Infinity`. -/
theorem ae_abs_value_le_w1Infinity (h : UnitCubeSkewW2Infinity d) (i j : Fin d) :
    ∀ᵐ x ∂volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)),
      |h.toLInfSkewMatrixFieldOn.1.1 x i j| ≤ h.w1Infinity := by
  classical
  set U : Set (Vec d) := ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)) with hU
  have hall : ∀ᵐ x ∂volumeMeasureOn U, ∀ i' j' : Fin d,
      |h.toLInfSkewMatrixFieldOn.1.1 x i' j'| ≤
        ENNReal.toReal (eLpNorm (fun y => h.toLInfSkewMatrixFieldOn.1.1 y i' j') ∞
          (volumeMeasureOn U)) := by
    rw [MeasureTheory.ae_all_iff]
    intro i'
    rw [MeasureTheory.ae_all_iff]
    intro j'
    exact ae_abs_le_toReal_eLpNorm_top
      (h.toLInfSkewMatrixFieldOn.1.2 i' j').eLpNorm_lt_top.ne
  have hbd : ∀ᵐ x ∂volumeMeasureOn U,
      |matrixNorm (h.toLInfSkewMatrixFieldOn.1.1 x)| ≤
        ∑ i' : Fin d, ∑ j' : Fin d,
          ENNReal.toReal (eLpNorm (fun y => h.toLInfSkewMatrixFieldOn.1.1 y i' j') ∞
            (volumeMeasureOn U)) := by
    filter_upwards [hall] with x hx
    rw [matrixNorm_eq_matrixOperatorNorm,
      abs_of_nonneg (matrixOperatorNorm_nonneg _)]
    refine ((matrixOperatorNorm_le_matrixFrobeniusNorm _).trans
      (matrixFrobeniusNorm_le_sum_abs_entries _)).trans ?_
    gcongr with i' _ j' _
    exact hx i' j'
  have hmeas : AEStronglyMeasurable
      (fun x => matrixNorm (h.toLInfSkewMatrixFieldOn.1.1 x)) (volumeMeasureOn U) :=
    Algsuperdiff.Section24.UnitCubeSkewW2Infinity.continuous_matrixNorm.comp_aestronglyMeasurable
      (Algsuperdiff.Section24.UnitCubeSkewW2Infinity.aestronglyMeasurable_of_entries fun i' j' =>
        (h.toLInfSkewMatrixFieldOn.1.2 i' j').aestronglyMeasurable)
  filter_upwards [ae_abs_le_toReal_eLpNorm_top (eLpNorm_top_ne_top_of_ae_abs_le hmeas hbd)]
    with x hx
  refine le_trans ?_ (hx.trans (toReal_eLpNorm_matrixNorm_le_w1Infinity h))
  rw [matrixNorm_eq_matrixOperatorNorm]
  exact (abs_entry_le_matrixOperatorNorm (h.toLInfSkewMatrixFieldOn.1.1 x) i j).trans
    (le_abs_self _)

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
