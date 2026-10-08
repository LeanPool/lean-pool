/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.MeanDefect
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.StationarityTransport

/-!
# High-contrast homogenization: Provider.Response.AnnealedVanishing

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed vanishing of the cutoff-weighted child responses

The cutoff-weighted child responses are the one term of the cutoff-energy
estimate that is not an estimate.  For a single coefficient sample they do not
vanish: the cutoff really does suppress the energy of the children near the
boundary of the parent.  They vanish only after averaging over a law that is
invariant under the integer translations, because then the annealed response of
a child depends on the child only through its scale, while the childwise cutoff
weights average to zero against a cutoff of mean one.

This module isolates that argument.  The measure-theoretic half is
unconditional.  The invariance half is reduced to one pathwise covariance
statement — that the response on a child is the response on the base child at a
translated sample — which is the shape the alignment of the grid supplies.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

open MeasureTheory Book.Ch05.Section53.JUpperBoundWeakNorms

variable {d : ℕ}

/-! ## The childwise cutoff weights average to zero -/

/-- A constant descendant average is that constant. -/
theorem descendantsAverage_const (Q : TriadicCube d) (j : ℕ) (c : ℝ) :
    descendantsAverage Q j (fun _ => c) = c := by
  have hcard : 0 < (descendantsAtDepth Q j).card :=
    Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j)
  have hcardR : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    positivity
  unfold descendantsAverage
  change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      (descendantsAtDepth Q j).sum (fun _ => c) = c
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- The childwise weights of a cutoff of mean one average to zero. -/
theorem descendantsAverage_one_sub_cubeAverage_eq_zero (Q : TriadicCube d)
    (j : ℕ) {φ : Vec d → ℝ} (hφ : IntegrableOn φ (cubeSet Q) volume)
    (hmean : cubeAverage Q φ = 1) :
    descendantsAverage Q j (fun R => 1 - cubeAverage R φ) = 0 := by
  have hsplit :
      descendantsAverage Q j (fun _ => (1 : ℝ)) +
          descendantsAverage Q j (fun R => (-1 : ℝ) * cubeAverage R φ) =
        descendantsAverage Q j (fun R => 1 - cubeAverage R φ) := by
    rw [descendantsAverage_add]
    exact descendantsAverage_congr_of_eq_on_descendants Q j
      (fun R _hR => by ring)
  rw [← hsplit, descendantsAverage_const, descendantsAverage_const_mul,
    ← cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j φ hφ,
    hmean]
  ring

/-! ## Integer translations preserve annealed quantities -/

/-- Under a stationary law, precomposing with an integer translation of the
coefficient space leaves the expectation unchanged. -/
theorem integral_comp_translateCoeff {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) (z : Fin d → ℤ)
    {g : CoeffSpace d → ℝ} (hg : Integrable g P) :
    ∫ a, g (translateCoeff z a) ∂P = ∫ a, g a ∂P := by
  have hmeas : AEStronglyMeasurable g (Measure.map (translateCoeff z) P) := by
    rw [hP z]
    exact hg.aestronglyMeasurable
  have hmap := integral_map (φ := translateCoeff z) (f := g)
    (measurable_translateCoeff z).aemeasurable hmeas
  rw [hP z] at hmap
  exact hmap.symm

/-- A quantity that is a fixed observable evaluated at a translated sample has
the same expectation as that observable. -/
theorem integral_eq_of_translateCoeff_covariance {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {f g : CoeffSpace d → ℝ}
    {z : Fin d → ℤ} (hcov : ∀ a, f a = g (translateCoeff z a))
    (hg : Integrable g P) :
    ∫ a, f a ∂P = ∫ a, g a ∂P := by
  calc
    ∫ a, f a ∂P = ∫ a, g (translateCoeff z a) ∂P := by
      exact integral_congr_ae (_root_.Filter.Eventually.of_forall hcov)
    _ = ∫ a, g a ∂P := integral_comp_translateCoeff hP z hg

/-! ## The annealed vanishing -/

/-- **The cutoff-weighted child responses vanish in the mean.**  Only two
inputs are used: the childwise expectations agree, and the cutoff has mean one
on the parent. -/
theorem integral_descendantsAverage_cutoffWeighted_eq_zero
    {P : Measure (CoeffSpace d)} (Q : TriadicCube d) (j : ℕ) {φ : Vec d → ℝ}
    (J : TriadicCube d → CoeffSpace d → ℝ)
    (hint : ∀ R ∈ descendantsAtDepth Q j, Integrable (J R) P)
    {c : ℝ} (hconst : ∀ R ∈ descendantsAtDepth Q j, ∫ a, J R a ∂P = c)
    (hφ : IntegrableOn φ (cubeSet Q) volume) (hmean : cubeAverage Q φ = 1) :
    ∫ a, descendantsAverage Q j
        (fun R => (1 - cubeAverage R φ) * J R a) ∂P = 0 := by
  classical
  have hswap :
      ∫ a, ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth Q j,
            (1 - cubeAverage R φ) * J R a ∂P =
        ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth Q j,
            (1 - cubeAverage R φ) * ∫ a, J R a ∂P := by
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum _ (fun R hR => ((hint R hR).const_mul _))]
    exact Finset.sum_congr rfl fun R hR => integral_const_mul _ _
  have hweights :
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth Q j, (1 - cubeAverage R φ) * c = 0 := by
    have hzero := descendantsAverage_one_sub_cubeAverage_eq_zero Q j hφ hmean
    have hmul : descendantsAverage Q j (fun R => (1 - cubeAverage R φ) * c) =
        0 := by
      have hcomm : descendantsAverage Q j
          (fun R => (1 - cubeAverage R φ) * c) =
            descendantsAverage Q j (fun R => c * (1 - cubeAverage R φ)) :=
        descendantsAverage_congr_of_eq_on_descendants Q j
          fun R _hR => by ring
      rw [hcomm, descendantsAverage_const_mul, hzero]
      ring
    unfold descendantsAverage at hmul
    exact hmul
  calc
    ∫ a, descendantsAverage Q j
        (fun R => (1 - cubeAverage R φ) * J R a) ∂P =
        ∫ a, ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth Q j,
            (1 - cubeAverage R φ) * J R a ∂P := rfl
    _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth Q j,
            (1 - cubeAverage R φ) * ∫ a, J R a ∂P := hswap
    _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth Q j, (1 - cubeAverage R φ) * c := by
      congr 1
      exact Finset.sum_congr rfl fun R hR => by rw [hconst R hR]
    _ = 0 := hweights

/-- **The annealed vanishing under stationarity.**  The pathwise covariance
`hcov` is the only geometric input: it says that the response on each child is
the response on the base child evaluated at an integer-translated sample. -/
theorem integral_descendantsAverage_cutoffWeighted_eq_zero_of_covariance
    {P : Measure (CoeffSpace d)} (hP : HCPoly.Frozen.IsStationaryLaw P)
    (Q : TriadicCube d) (j : ℕ) {φ : Vec d → ℝ}
    (J : TriadicCube d → CoeffSpace d → ℝ) (R₀ : TriadicCube d)
    (hint : ∀ R ∈ descendantsAtDepth Q j, Integrable (J R) P)
    (hbase : Integrable (J R₀) P)
    (hcov : ∀ R ∈ descendantsAtDepth Q j, ∃ z : Fin d → ℤ,
      ∀ a, J R a = J R₀ (translateCoeff z a))
    (hφ : IntegrableOn φ (cubeSet Q) volume) (hmean : cubeAverage Q φ = 1) :
    ∫ a, descendantsAverage Q j
        (fun R => (1 - cubeAverage R φ) * J R a) ∂P = 0 := by
  refine integral_descendantsAverage_cutoffWeighted_eq_zero Q j J hint
    (c := ∫ a, J R₀ a ∂P) ?_ hφ hmean
  intro R hR
  obtain ⟨z, hz⟩ := hcov R hR
  exact integral_eq_of_translateCoeff_covariance hP hz hbase

/-! ## The signed cutoff-energy estimate and its annealed form -/

/-- The signed form of the cutoff-energy estimate: the cutoff-weighted child
responses are kept on the left, so that a stationary average removes them. -/
theorem abs_cutoff_weighted_energy_sub_responseJ_add_cutoffWeightedChild_le
    [NeZero d] {q : Mat d} (hq : q.PosDef) (a : Book.Ch02.TriadicCoeffFamily d)
    (Q : TriadicCube d) (j : ℕ) {s t H : ℤ} (hscale : Q.scale - (j : ℤ) = s)
    (hH : H = t - s) (p r : Vec d)
    (hCoeff : ∀ R ∈ descendantsAtDepth Q j,
      (a.coeffOn Q).toCoeffField = (a.coeffOn R).toCoeffField) :
    |cubeAverage Q (fun x =>
          adaptedPreYoungCutoff q hq t (matVecMul q x) *
            topHalfEnergyDensityOnCube Q (a.coeffOn Q) p r x) -
        Book.Ch02.responseJ (Book.Ch02.cubeDomain Q) (a.coeffOn Q) p r +
        cutoffWeightedChildResponseJOnFamilyAtDepth a Q j
          (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) p r| ≤
      32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound * (3 : ℝ) ^ (-H) *
          Book.Ch02.responseJ (Book.Ch02.cubeDomain Q) (a.coeffOn Q) p r +
        Real.sqrt (descendantsAverage Q j fun R =>
            cubeAverage R
              (additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p r)) *
          Real.sqrt
            (4 * Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
                  (a.coeffOn Q) p r +
              2 * responseJPartitionDefectOnFamilyAtDepth a Q j p r) := by
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
  have hbdd : ∀ᵐ x ∂volumeMeasureOn (cubeSet Q),
      ‖adaptedPreYoungCutoff q hq t (matVecMul q x)‖ ≤ 2 :=
    _root_.Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact adaptedPreYoungCutoff_le_two hq t (matVecMul q x)
      · exact adaptedPreYoungCutoff_nonneg hq t (matVecMul q x)
  have hweight : ∀ R ∈ descendantsAtDepth Q j,
      |1 - cubeAverage R
          (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y))| ≤ 1 :=
    fun R _hR => abs_one_sub_cubeAverage_adaptedPreYoungCutoff_le_one hq t R
  have hsplit := cutoffOscillationTerm_add_meanDefectTopEnergyTerm_eq
    Q (a.coeffOn Q) j hmeas hbdd p r
  have hmean := meanDefectTopEnergyTermOnCubeAtDepth_eq_cross_add_cutoffWeightedChild
    a Q j (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) p r hCoeff
  have hosc := abs_cutoffOscillationTermOnCubeAtDepth_adaptedPreYoungCutoff_le_sharp
    hq Q (a.coeffOn Q) j hscale hH p r
  have hcross := abs_concreteAdditivityCrossTermOnFamilyAtDepth_le_sqrt_mul_sqrt
    a Q j (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) p r
    hCoeff hweight
  have hrewrite :
      cubeAverage Q (fun x =>
            adaptedPreYoungCutoff q hq t (matVecMul q x) *
              topHalfEnergyDensityOnCube Q (a.coeffOn Q) p r x) -
          Book.Ch02.responseJ (Book.Ch02.cubeDomain Q) (a.coeffOn Q) p r +
          cutoffWeightedChildResponseJOnFamilyAtDepth a Q j
            (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) p r =
        -(cutoffOscillationTermOnCubeAtDepth Q (a.coeffOn Q) j
              (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) p r +
            concreteAdditivityCrossTermOnFamilyAtDepth a Q j
              (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) p r) := by
    rw [hmean] at hsplit
    linarith only [hsplit]
  rw [hrewrite, abs_neg]
  exact (abs_add_le _ _).trans (add_le_add hosc hcross)

/-- Composing a pointwise bound with a mean-zero correction: the correction
disappears from the expectation. -/
theorem abs_integral_le_of_integral_eq_zero {P : Measure (CoeffSpace d)}
    {X W Y : CoeffSpace d → ℝ} (hX : Integrable X P) (hW : Integrable W P)
    (hY : Integrable Y P) (hbound : ∀ a, |X a + W a| ≤ Y a)
    (hzero : ∫ a, W a ∂P = 0) :
    |∫ a, X a ∂P| ≤ ∫ a, Y a ∂P := by
  have hsum : ∫ a, (X a + W a) ∂P = ∫ a, X a ∂P := by
    rw [integral_add hX hW, hzero, add_zero]
  calc
    |∫ a, X a ∂P| = |∫ a, (X a + W a) ∂P| := by rw [hsum]
    _ ≤ ∫ a, |X a + W a| ∂P :=
      abs_integral_le_integral_abs
    _ ≤ ∫ a, Y a ∂P :=
      integral_mono ((hX.add hW).abs) hY (fun a => hbound a)

end

end Response
end HighContrast
end HCPolySupport
