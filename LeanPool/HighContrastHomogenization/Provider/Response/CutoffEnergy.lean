/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffGradientScale
public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffOscillation

/-!
# High-contrast homogenization: Provider.Response.CutoffEnergy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cutoff-energy estimate

Inserting a mean-one cutoff into the parent energy changes it by two terms: the
childwise oscillation of the cutoff against the parent energy density, and the
mean defect of the cutoff against the childwise parent energies.  The first is
controlled by the cutoff's adapted-coordinate gradient alone, and the sharper
first-derivative coefficient of the adapted construction gives it the
dimensional size `32 d² K₀ 3^{-H}`, where `K₀` is the derivative bound of the
one-dimensional transition profile and `H` is the gap between the parent scale
and the child scale.

The identity below is exact and the oscillation bound is unconditional; the
mean-defect term is carried as an explicit bound, since controlling it is a
separate step of the localization argument.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

open MeasureTheory Book.Ch05.Section53.JUpperBoundWeakNorms

/-! ## The sharper oscillation of the adapted cutoff -/

/-- The sharp dimensional coefficient of the adapted cutoff's first
derivative is nonnegative. -/
theorem sharpCutoffCoefficient_nonneg (d : ℕ) :
    (0 : ℝ) ≤ 32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound := by
  have hK : 0 ≤ smoothTransitionProfile.derivBound :=
    smoothTransitionProfile.derivBound_nonneg
  have h1 : (0 : ℝ) ≤ 32 * (d : ℝ) ^ 2 := by positivity
  exact mul_nonneg h1 hK

/-- A dimension-only constant at least one that dominates the cutoff's
first-derivative coefficient.  This is the form in which the coefficient leaves
the analytic layer: it depends on the dimension alone, and it is selected before
any probability law, grid, scale, coefficient, centre, or load. -/
theorem exists_one_le_sharpCutoffConstant (d : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound ≤ C :=
  ⟨max 1 (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound),
    le_max_left _ _, le_max_right _ _⟩

/-- The scale-gap factor written with a natural exponent, as the mixed
extended-real assembly reads it, agrees with the integer-exponent form used by
the analytic estimates. -/
theorem rpow_neg_natCast_eq_zpow_neg (H : ℕ) :
    (3 : ℝ) ^ (-(H : ℝ)) = (3 : ℝ) ^ (-(H : ℤ)) := by
  rw [← Real.rpow_intCast (3 : ℝ) (-(H : ℤ))]
  norm_num

/-- On a scale-`s` reference child the physical cutoff pulled through the grid
matrix oscillates by at most the sharp dimensional coefficient times the scale
gap. -/
theorem adaptedPreYoungCutoff_pullback_oscillation_sharp {d : ℕ} [NeZero d]
    {q : Mat d} (hq : q.PosDef) {R : TriadicCube d} {s t H : ℤ}
    (hR : R.scale = s) (hH : H = t - s) {x y : Vec d}
    (hx : x ∈ cubeSet R) (hy : y ∈ cubeSet R) :
    ‖adaptedPreYoungCutoff q hq t (matVecMul q x) -
        adaptedPreYoungCutoff q hq t (matVecMul q y)‖ ≤
      32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound * (3 : ℝ) ^ (-H) := by
  have hlinear : ContDiff ℝ (⊤ : ℕ∞) (matVecMul q) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin q)).contDiff
  have hu : ContDiff ℝ (⊤ : ℕ∞)
      (fun z => adaptedPreYoungCutoff q hq t (matVecMul q z)) := by
    simpa only [Function.comp_def] using
      (adaptedPreYoungCutoff_smooth hq t).comp hlinear
  have hthree : (0 : ℝ) < (3 : ℝ) ^ (-t) := zpow_pos (by norm_num) _
  have hB : 0 ≤ 32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
      (3 : ℝ) ^ (-t) :=
    mul_nonneg (sharpCutoffCoefficient_nonneg d) hthree.le
  have hderiv : ∀ z ∈ cubeSet R,
      ‖fderiv ℝ (fun w => adaptedPreYoungCutoff q hq t (matVecMul q w)) z‖ ≤
        32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
          (3 : ℝ) ^ (-t) :=
    fun z _hz => adaptedPreYoungCutoff_pullback_fderiv_bound_sharp hq t z
  have hosc := norm_sub_le_cubeScaleFactor_mul_of_contDiff_bound R hu hB hderiv
    hx hy
  have hscale : cubeScaleFactor R = (3 : ℝ) ^ s := by
    unfold cubeScaleFactor
    rw [hR]
  calc
    ‖adaptedPreYoungCutoff q hq t (matVecMul q x) -
        adaptedPreYoungCutoff q hq t (matVecMul q y)‖ ≤
        cubeScaleFactor R *
          (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
            (3 : ℝ) ^ (-t)) := hosc
    _ = 32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound * (3 : ℝ) ^ s *
        ((3 : ℝ) ^ (-t) * 1) := by
      rw [hscale]
      ring
    _ = 32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
        (3 : ℝ) ^ (-H) * 1 :=
      cutoff_energy_coefficient
        (Cd := 32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound)
        (J := 1) hH
    _ = 32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
        (3 : ℝ) ^ (-H) := mul_one _

/-- The child average differs from the cutoff by the sharp scale-gap bound at
every point of the reference child. -/
theorem adaptedPreYoungCutoff_pullback_sub_cubeAverage_sharp {d : ℕ} [NeZero d]
    {q : Mat d} (hq : q.PosDef) {R : TriadicCube d} {s t H : ℤ}
    (hR : R.scale = s) (hH : H = t - s) {x : Vec d} (hx : x ∈ cubeSet R) :
    |cubeAverage R (fun z => adaptedPreYoungCutoff q hq t (matVecMul q z)) -
        adaptedPreYoungCutoff q hq t (matVecMul q x)| ≤
      32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound * (3 : ℝ) ^ (-H) := by
  set u : Vec d → ℝ :=
    fun z => adaptedPreYoungCutoff q hq t (matVecMul q z) with hu_def
  set C : ℝ := 32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
    (3 : ℝ) ^ (-H) with hC_def
  have hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u := by
    have hlinear : ContDiff ℝ (⊤ : ℕ∞) (matVecMul q) :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin q)).contDiff
    simpa only [hu_def, Function.comp_def] using
      (adaptedPreYoungCutoff_smooth hq t).comp hlinear
  have hu_bound : ∀ z, ‖u z‖ ≤ 2 := by
    intro z
    rw [hu_def]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact adaptedPreYoungCutoff_le_two hq t (matVecMul q z)
    · exact adaptedPreYoungCutoff_nonneg hq t (matVecMul q z)
  have hu_mem : MemLp u (⊤ : ENNReal) (normalizedCubeMeasure R) :=
    memLp_top_of_bound hu_smooth.continuous.aestronglyMeasurable 2
      (Filter.Eventually.of_forall hu_bound)
  have hthree : (0 : ℝ) < (3 : ℝ) ^ (-H) := zpow_pos (by norm_num) _
  have hC : 0 ≤ C :=
    mul_nonneg (sharpCutoffCoefficient_nonneg d) hthree.le
  have havg : ‖u x - cubeAverage R u‖ ≤
      cubeLpNorm R (⊤ : ENNReal) (fun y => u y - u x) :=
    norm_sub_cubeAverage_le_cubeLpNorm_infty_sub_const R u x hu_mem
  have hlinfty : cubeLpNorm R (⊤ : ENNReal) (fun y => u y - u x) ≤ C := by
    apply cubeLpNorm_infty_le_of_bound_on_cubeSet R
    · exact hC
    · intro y hy
      simpa only [hu_def, hC_def, norm_sub_rev] using
        adaptedPreYoungCutoff_pullback_oscillation_sharp hq hR hH hy hx
  have hnorm : ‖u x - cubeAverage R u‖ ≤ C := havg.trans hlinfty
  simpa only [hu_def, hC_def, Real.norm_eq_abs, abs_sub_comm] using hnorm

/-- The a.e. form of the sharp child-average oscillation bound. -/
theorem adaptedPreYoungCutoff_pullback_sub_cubeAverage_sharp_ae {d : ℕ}
    [NeZero d] {q : Mat d} (hq : q.PosDef) {R : TriadicCube d} {s t H : ℤ}
    (hR : R.scale = s) (hH : H = t - s) :
    ∀ᵐ x ∂volumeMeasureOn (cubeSet R),
      |cubeAverage R (fun z => adaptedPreYoungCutoff q hq t (matVecMul q z)) -
          adaptedPreYoungCutoff q hq t (matVecMul q x)| ≤
        32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
          (3 : ℝ) ^ (-H) := by
  apply (ae_restrict_iff' (μ := volume) (measurableSet_cubeSet R)).2
  exact Filter.Eventually.of_forall fun x hx =>
    adaptedPreYoungCutoff_pullback_sub_cubeAverage_sharp hq hR hH hx

/-- The cutoff-energy oscillation term carries the sharp dimensional
coefficient and the scale gap. -/
theorem abs_cutoffOscillationTermOnCubeAtDepth_adaptedPreYoungCutoff_le_sharp
    {d : ℕ} [NeZero d] {q : Mat d} (hq : q.PosDef)
    (Q : TriadicCube d) (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (j : ℕ) {s t H : ℤ} (hscale : Q.scale - (j : ℤ) = s)
    (hH : H = t - s) (p r : Vec d) :
    |cutoffOscillationTermOnCubeAtDepth Q a j
        (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) p r| ≤
      32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound * (3 : ℝ) ^ (-H) *
        Book.Ch02.responseJ (Book.Ch02.cubeDomain Q) a p r := by
  have hlinear : ContDiff ℝ (⊤ : ℕ∞) (matVecMul q) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin q)).contDiff
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) := by
    simpa only [Function.comp_def] using
      (adaptedPreYoungCutoff_smooth hq t).comp hlinear
  have hmeas : AEStronglyMeasurable
      (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y))
      (volumeMeasureOn (cubeSet Q)) :=
    hsmooth.continuous.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂volumeMeasureOn (cubeSet Q),
      ‖adaptedPreYoungCutoff q hq t (matVecMul q x)‖ ≤ 2 :=
    Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact adaptedPreYoungCutoff_le_two hq t (matVecMul q x)
      · exact adaptedPreYoungCutoff_nonneg hq t (matVecMul q x)
  have hosc : ∀ R ∈ descendantsAtDepth Q j,
      ∀ᵐ x ∂volumeMeasureOn (cubeSet R),
        |cubeAverage R
              (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) -
            adaptedPreYoungCutoff q hq t (matVecMul q x)| ≤
          32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
            (3 : ℝ) ^ (-H) := by
    intro R hR
    have hRscale : R.scale = s :=
      (scale_eq_sub_of_mem_descendantsAtDepth hR).trans hscale
    exact adaptedPreYoungCutoff_pullback_sub_cubeAverage_sharp_ae hq hRscale hH
  exact
    abs_cutoffOscillationTermOnCubeAtDepth_le_scale_mul_responseJOnCube_of_ae_bounded_cutoff
      Q a j p r hmeas hbound hosc

/-! ## The cutoff-energy split -/

/-- The parent energy density averages to the parent response. -/
theorem cubeAverage_topHalfEnergyDensityOnCube_eq_responseJ {d : ℕ}
    (Q : TriadicCube d) (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (p r : Vec d) :
    cubeAverage Q (topHalfEnergyDensityOnCube Q a p r) =
      Book.Ch02.responseJ (Book.Ch02.cubeDomain Q) a p r := by
  have hint : IntegrableOn (topHalfEnergyDensityOnCube Q a p r) (cubeSet Q)
      volume := topHalfEnergyDensityOnCube_integrableOn_cubeSet Q a p r
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    (Q := Q) (j := 0) (f := topHalfEnergyDensityOnCube Q a p r) hint]
  exact descendantsAverage_topHalfEnergy_eq_responseJ
    Q a 0 p r

/-- Descendant averages are additive. -/
theorem descendantsAverage_add {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F G : TriadicCube d → ℝ) :
    descendantsAverage Q j F + descendantsAverage Q j G =
      descendantsAverage Q j fun R => F R + G R := by
  unfold descendantsAverage
  show ((descendantsAtDepth Q j).card : ℝ)⁻¹ * (descendantsAtDepth Q j).sum F +
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ * (descendantsAtDepth Q j).sum G =
    ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      (descendantsAtDepth Q j).sum fun R => F R + G R
  rw [Finset.sum_add_distrib]
  ring

/-- **The cutoff-energy split.**  Inserting a cutoff into the parent energy
changes it by exactly the childwise oscillation term plus the mean-defect
term. -/
theorem cutoffOscillationTerm_add_meanDefectTopEnergyTerm_eq {d : ℕ}
    (Q : TriadicCube d) (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (j : ℕ) {φ : Vec d → ℝ}
    (hmeas : AEStronglyMeasurable φ (volumeMeasureOn (cubeSet Q)))
    (hbdd : ∀ᵐ x ∂volumeMeasureOn (cubeSet Q), ‖φ x‖ ≤ 2)
    (p r : Vec d) :
    cutoffOscillationTermOnCubeAtDepth Q a j φ p r +
        meanDefectTopEnergyTermOnCubeAtDepth Q a j φ p r =
      Book.Ch02.responseJ (Book.Ch02.cubeDomain Q) a p r -
        cubeAverage Q
          (fun x => φ x * topHalfEnergyDensityOnCube Q a p r x) := by
  classical
  set F : Vec d → ℝ := topHalfEnergyDensityOnCube Q a p r with hF_def
  have hF_int : IntegrableOn F (cubeSet Q) volume :=
    topHalfEnergyDensityOnCube_integrableOn_cubeSet Q a p r
  have hprod_int : IntegrableOn (fun x => φ x * F x) (cubeSet Q) volume :=
    hF_int.bdd_mul hmeas hbdd
  have hrem_int : IntegrableOn (fun x => (1 - φ x) * F x) (cubeSet Q) volume := by
    have hmeas' : AEStronglyMeasurable (fun x => 1 - φ x)
        (volumeMeasureOn (cubeSet Q)) := aestronglyMeasurable_const.sub hmeas
    have hbdd' : ∀ᵐ x ∂volumeMeasureOn (cubeSet Q), ‖1 - φ x‖ ≤ 3 := by
      filter_upwards [hbdd] with x hx
      calc ‖1 - φ x‖ ≤ ‖(1 : ℝ)‖ + ‖φ x‖ := norm_sub_le _ _
        _ ≤ 1 + 2 := by
          have : ‖(1 : ℝ)‖ = 1 := by norm_num
          linarith only [hx, this.le, this.ge]
        _ = 3 := by norm_num
    exact hF_int.bdd_mul hmeas' hbdd'
  have hchild_F : ∀ R ∈ descendantsAtDepth Q j,
      IntegrableOn F (cubeSet R) volume := fun R hR =>
    hF_int.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
  have hchild_osc : ∀ R ∈ descendantsAtDepth Q j,
      IntegrableOn (fun x => (cubeAverage R φ - φ x) * F x) (cubeSet R)
        volume := by
    intro R hR
    have hsubset : cubeSet R ⊆ cubeSet Q :=
      cubeSet_subset_of_mem_descendantsAtDepth hR
    have hle : volumeMeasureOn (cubeSet R) ≤ volumeMeasureOn (cubeSet Q) := by
      simpa [volumeMeasureOn] using
        MeasureTheory.Measure.restrict_mono_set volume hsubset
    have hmeasR : AEStronglyMeasurable (fun x => cubeAverage R φ - φ x)
        (volumeMeasureOn (cubeSet R)) :=
      aestronglyMeasurable_const.sub (hmeas.mono_measure hle)
    have hbddR : ∀ᵐ x ∂volumeMeasureOn (cubeSet R),
        ‖cubeAverage R φ - φ x‖ ≤ |cubeAverage R φ| + 2 := by
      filter_upwards [hbdd.filter_mono (MeasureTheory.ae_mono hle)] with x hx
      calc ‖cubeAverage R φ - φ x‖ ≤ ‖cubeAverage R φ‖ + ‖φ x‖ :=
            norm_sub_le _ _
        _ ≤ |cubeAverage R φ| + 2 := by
          have : ‖cubeAverage R φ‖ = |cubeAverage R φ| := rfl
          linarith only [hx, this.le, this.ge]
    exact (hF_int.mono_set hsubset).bdd_mul hmeasR hbddR
  have hsplit :=
    cubeAverage_one_sub_cutoff_mul_eq_descendantsAverage_cutoff_oscillation_add_mean_defect
      Q j φ F hrem_int hchild_osc hchild_F
  have hleft : cubeAverage Q (fun x => (1 - φ x) * F x) =
      Book.Ch02.responseJ (Book.Ch02.cubeDomain Q) a p r -
        cubeAverage Q (fun x => φ x * F x) := by
    have hcongr : (fun x => (1 - φ x) * F x) =
        fun x => F x + (-1 : ℝ) * (φ x * F x) := by
      funext x
      ring
    rw [hcongr, cubeAverage_add_of_integrableOn Q F
      (fun x => (-1 : ℝ) * (φ x * F x)) hF_int
      (hprod_int.const_mul (-1 : ℝ)), cubeAverage_const_mul Q (-1 : ℝ),
      cubeAverage_topHalfEnergyDensityOnCube_eq_responseJ Q a p r]
    ring
  have hgoal : cutoffOscillationTermOnCubeAtDepth Q a j φ p r +
        meanDefectTopEnergyTermOnCubeAtDepth Q a j φ p r =
      descendantsAverage Q j fun R =>
        cubeAverage R (fun x => (cubeAverage R φ - φ x) * F x) +
          (1 - cubeAverage R φ) * cubeAverage R F := by
    rw [← descendantsAverage_add]
    rfl
  rw [hgoal, ← hsplit, hleft]

end

end Response
end HighContrast
end HCPolySupport
