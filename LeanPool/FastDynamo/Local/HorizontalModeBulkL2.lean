/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.HorizontalModeBulkIdentity

/-!
# The bulk eigen-identity of the two-component Ponomarenko mode in `L²`

This module packages the pointwise bulk equation of `Local/HorizontalModeBulkIdentity.lean` as
an identity between `L²(ℝ²;ℂ²)` classes, in exactly the shape required by the hypothesis
`hbulk` of `horizontalModeDistributionalEquation_of_coordinate_sources`
(`Local/HorizontalModeSurface.lean`).

Three things are needed.

* `L²` membership of the glued bulk field `{∂_j D_j}`.  Inside the disk the regular branch is
  smooth through the origin, so the field is continuous on the compact closed disk; outside,
  the second derivatives of the decaying branches obey an `e^{-(Re κ)(r-1)}` envelope
  (`Local/HorizontalModeExteriorSecondDerivatives.lean`).
* Almost-everywhere representatives of the two pivot fields
  `horizontalWeakFormDerivativePivot` and `horizontalWeakFormMassPivot` of
  `Local/HorizontalModeWeakIdentity.lean`, obtained by pushing the `L∞`/`L²` multiplication and
  coordinate maps down to their pointwise formulas.
* The fact that the unit circle is a Lebesgue null set, which upgrades the pointwise identity
  off the circle to an identity of `L²` classes.

The final statement `horizontalModeBulk_add` is the bulk half of the weak eigenvalue equation
in the proof of `lem:jump-horizontal-mode`, in its Lean form (hypothesis 2 of the assembly
theorem).
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace HorizontalMode

open Complex Filter MeasureTheory Metric Set Topology
open HorizontalWeakForm
open PonomarenkoFreeOmegaInterface
open WholePlaneRadialExponential

/-! ## `L²` packaging of the bulk field -/

/-- Assembling the two coordinate insertions of a scalar multiple recovers the scalar multiple
of the vector: `Σ_i e_i (v_i c) = c v`. -/
theorem sum_scalarToVecPoint_mul (v : C2) (c : ℂ) :
    ∑ i : Fin 2, scalarToVecPoint (ι := Fin 2) i (v i * c) = c • v := by
  have h0 : (∑ i : Fin 2, scalarToVecPoint (ι := Fin 2) i (v i * c)) 0 = (c • v) 0 := by
    simp [Fin.sum_univ_two, scalarToVecPoint, mul_comm]
  have h1 : (∑ i : Fin 2, scalarToVecPoint (ι := Fin 2) i (v i * c)) 1 = (c • v) 1 := by
    simp [Fin.sum_univ_two, scalarToVecPoint, mul_comm]
  apply PiLp.ext
  intro a
  fin_cases a
  · exact h0
  · exact h1

/-- The interior bulk field is continuous on the whole plane: the regular branch is smooth
through the origin and the screw velocity is a polynomial. -/
theorem horizontalInteriorBulkField_continuous (Omega : ℝ) (kappa : ℂ) (j : Fin 2) :
    Continuous (horizontalInteriorBulkField Omega kappa j) := by
  have hfield : Continuous (fun y : WholePlane ↦ horizontalInteriorField kappa y j) :=
    (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp
      (horizontalInteriorField_continuous kappa)
  have hpart : Continuous
      (fun y : WholePlane ↦ horizontalInteriorPartialDerivative kappa j y j) :=
    (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp
      (horizontalInteriorPartialDerivative_continuous kappa j)
  have hvel : Continuous (horizontalInteriorTransverseVelocity Omega) :=
    (horizontalTransverseVelocityCLM Omega).continuous
  exact ((horizontalInteriorSecondPartialDerivative_continuous kappa j j).add
    (hpart.smul hvel)).add (hfield.smul continuous_const)

/-- The glued bulk field is square integrable on the plane: it is continuous on the compact
closed unit disk and exponentially small outside it. -/
theorem horizontalModeBulkField_memLp
    {kappa : ℂ} (hkappa : 0 < kappa.re) (Omega : ℝ) (j : Fin 2) :
    MemLp (horizontalModeBulkField Omega kappa j) 2 volume := by
  classical
  have hs : MeasurableSet (closedBall (0 : WholePlane) 1) := isClosed_closedBall.measurableSet
  have hinter : MemLp (horizontalInteriorBulkField Omega kappa j) 2
      (volume.restrict (closedBall (0 : WholePlane) 1)) := by
    apply (memLp_two_iff_integrable_sq_norm
      (horizontalInteriorBulkField_continuous Omega kappa j).aestronglyMeasurable).2
    exact (((horizontalInteriorBulkField_continuous Omega kappa j).norm.pow
      2).continuousOn).integrableOn_compact (isCompact_closedBall (0 : WholePlane) 1)
  have hsub : (closedBall (0 : WholePlane) 1)ᶜ ⊆ unitExterior := by
    intro y hy
    have hy' : ¬ ‖y‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hy
    exact le_of_lt (lt_of_not_ge hy')
  have hexterior : MemLp (horizontalExteriorBulkField kappa j) 2
      (volume.restrict (closedBall (0 : WholePlane) 1)ᶜ) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hsub)
      (horizontalExteriorSecondPartialDerivative_memLp_two_unitExterior hkappa j j)
  have hp : MemLp
      ((closedBall (0 : WholePlane) 1).piecewise
        (horizontalInteriorBulkField Omega kappa j)
        (horizontalExteriorBulkField kappa j)) 2 (volume : Measure WholePlane) :=
    MemLp.piecewise hs.nullMeasurableSet hinter hexterior
  apply hp.ae_eq
  filter_upwards with y
  by_cases hy : ‖y‖ ≤ 1
  · simp [horizontalModeBulkField, Set.piecewise, mem_closedBall, dist_zero_right, hy]
  · simp [horizontalModeBulkField, Set.piecewise, mem_closedBall, dist_zero_right, hy]

/-- The bulk field `{∂_j D_j}` as an element of `L²(ℝ²;ℂ²)`.  This is the `bulk j` of the
assembly theorem `horizontalModeDistributionalEquation_of_coordinate_sources`. -/
def horizontalModeBulkL2 (Omega : ℝ) (kappa : ℂ) (hkappa : 0 < kappa.re) (j : Fin 2) :
    WholePlaneC2L2 :=
  (horizontalModeBulkField_memLp hkappa Omega j).toLp (horizontalModeBulkField Omega kappa j)

/-- The bundled bulk field has the pointwise branchwise formula as a representative. -/
theorem horizontalModeBulkL2_coe_ae (Omega : ℝ) (kappa : ℂ) (hkappa : 0 < kappa.re)
    (j : Fin 2) :
    ((horizontalModeBulkL2 Omega kappa hkappa j : WholePlaneC2L2) : WholePlane → C2) =ᵐ[volume]
      horizontalModeBulkField Omega kappa j :=
  MemLp.coeFn_toLp _

/-! ## Almost-everywhere representatives -/

/-- A.e. representative of a coordinate of a whole-plane `L∞` three-vector field. -/
theorem wholePlaneCoordLInf_coe_ae (i : Fin 3) (w : WholePlaneC3LInf) :
    ((wholePlaneCoordLInf i w : WholePlaneScalarLInf) : WholePlane → ℂ) =ᵐ[volume]
      fun y ↦ (w : WholePlane → C3) y i :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL (p := ⊤)
    (μ := (volume : Measure WholePlane)) w

/-- A.e. representative of a coordinate of a whole-plane `L²` two-vector field. -/
theorem wholePlaneC2CoordL2_coe_ae (j : Fin 2) (f : WholePlaneC2L2) :
    ((wholePlaneC2CoordL2 j f : WholePlaneScalarL2) : WholePlane → ℂ) =ᵐ[volume]
      fun y ↦ (f : WholePlane → C2) y j :=
  (EuclideanSpace.proj (𝕜 := ℂ) j).coeFn_compLpL (p := 2)
    (μ := (volume : Measure WholePlane)) f

/-- A.e. representative of a coordinate insertion into a whole-plane `L²` two-vector field. -/
theorem wholePlaneScalarToC2CoordL2_coe_ae (i : Fin 2) (g : WholePlaneScalarL2) :
    ((wholePlaneScalarToC2CoordL2 i g : WholePlaneC2L2) : WholePlane → C2) =ᵐ[volume]
      fun y ↦ scalarToVecPoint (ι := Fin 2) i ((g : WholePlane → ℂ) y) :=
  (scalarToVecPoint (ι := Fin 2) i).coeFn_compLpL (p := 2)
    (μ := (volume : Measure WholePlane)) g

/-- A.e. representative of an `L∞`-scalar multiple inserted into one `ℂ²` coordinate. -/
theorem wholePlaneScalarToC2CoordL2_mul_coe_ae
    (i : Fin 2) (a : WholePlaneScalarLInf) (c : WholePlaneScalarL2) :
    ((wholePlaneScalarToC2CoordL2 i (scalarVectorMulL2 (E := ℂ) volume a c) :
        WholePlaneC2L2) : WholePlane → C2) =ᵐ[volume]
      fun y ↦ scalarToVecPoint (ι := Fin 2) i
        ((a : WholePlane → ℂ) y * (c : WholePlane → ℂ) y) := by
  filter_upwards [wholePlaneScalarToC2CoordL2_coe_ae i
      (scalarVectorMulL2 (E := ℂ) volume a c),
    scalarVectorMulL2_coe_ae (E := ℂ) volume a c] with y h1 h2
  rw [h1, h2]
  simp

/-- The transverse components of the jump representative, at an arbitrary index. -/
theorem horizontalJumpVelocity_apply_castSucc (Omega U : ℝ) (y : WholePlane) (i : Fin 2) :
    horizontalJumpVelocity Omega U y i.castSucc =
      horizontalTransverseVelocityField Omega y i := by
  fin_cases i
  · exact horizontalJumpVelocity_apply_zero Omega U y
  · exact horizontalJumpVelocity_apply_one Omega U y

/-- The certified velocity has the explicit glued screw field as an a.e. representative. -/
theorem horizontalModeVelocity_coe_ae (N Omega : ℝ) :
    ((horizontalModeVelocity N Omega : WholePlaneC3LInf) : WholePlane → C3) =ᵐ[volume]
      horizontalJumpVelocity Omega (jumpAxialSpeed N Omega) :=
  horizontalJumpVelocityLInf_coe_ae Omega (jumpAxialSpeed N Omega)

/-- A.e. representative of a transverse coordinate of the certified velocity. -/
theorem horizontalModeVelocity_transverseCoord_coe_ae (N Omega : ℝ) (i : Fin 2) :
    ((wholePlaneCoordLInf i.castSucc (horizontalModeVelocity N Omega) :
        WholePlaneScalarLInf) : WholePlane → ℂ) =ᵐ[volume]
      fun y ↦ horizontalTransverseVelocityField Omega y i := by
  filter_upwards [wholePlaneCoordLInf_coe_ae i.castSucc (horizontalModeVelocity N Omega),
    horizontalModeVelocity_coe_ae N Omega] with y h1 h2
  rw [h1, h2]
  exact horizontalJumpVelocity_apply_castSucc Omega (jumpAxialSpeed N Omega) y i

/-- A.e. representative of the axial coordinate of the certified velocity. -/
theorem horizontalModeVelocity_axialCoord_coe_ae (N Omega : ℝ) :
    ((wholePlaneCoordLInf (2 : Fin 3) (horizontalModeVelocity N Omega) :
        WholePlaneScalarLInf) : WholePlane → ℂ) =ᵐ[volume]
      horizontalAxialVelocityField N Omega := by
  filter_upwards [wholePlaneCoordLInf_coe_ae (2 : Fin 3) (horizontalModeVelocity N Omega),
    horizontalModeVelocity_coe_ae N Omega] with y h1 h2
  rw [h1, h2]
  exact horizontalJumpVelocity_apply_two N Omega y

/-- The derivative pivot `D_j = ∂_j b + w_⊥ b_j` of the certified mode has the pointwise
branchwise formula as an `L²` representative. -/
theorem horizontalWeakFormDerivativePivot_coe_ae
    (N Omega : ℝ) {kappa : ℂ} (hkappa : 0 < kappa.re) (j : Fin 2) :
    ((horizontalWeakFormDerivativePivot (horizontalModeVelocity N Omega)
        (horizontalModeH1 kappa hkappa) j : WholePlaneC2L2) : WholePlane → C2) =ᵐ[volume]
      horizontalModePivotField Omega kappa j := by
  have hexpand : horizontalWeakFormDerivativePivot (horizontalModeVelocity N Omega)
      (horizontalModeH1 kappa hkappa) j =
      horizontalModePartialDerivativeL2 kappa hkappa j +
        (wholePlaneScalarToC2CoordL2 0 (scalarVectorMulL2 (E := ℂ) volume
            (wholePlaneCoordLInf ((0 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
            (wholePlaneC2CoordL2 j (horizontalModeL2 kappa hkappa))) +
          wholePlaneScalarToC2CoordL2 1 (scalarVectorMulL2 (E := ℂ) volume
            (wholePlaneCoordLInf ((1 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
            (wholePlaneC2CoordL2 j (horizontalModeL2 kappa hkappa)))) := by
    simp only [horizontalWeakFormDerivativePivot, Fin.sum_univ_two,
      wholePlaneH1FirstDerivative_horizontalModeH1, wholePlaneH1Embedding_horizontalModeH1]
  rw [hexpand]
  filter_upwards [Lp.coeFn_add (horizontalModePartialDerivativeL2 kappa hkappa j)
      (wholePlaneScalarToC2CoordL2 0 (scalarVectorMulL2 (E := ℂ) volume
          (wholePlaneCoordLInf ((0 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
          (wholePlaneC2CoordL2 j (horizontalModeL2 kappa hkappa))) +
        wholePlaneScalarToC2CoordL2 1 (scalarVectorMulL2 (E := ℂ) volume
          (wholePlaneCoordLInf ((1 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
          (wholePlaneC2CoordL2 j (horizontalModeL2 kappa hkappa)))),
    Lp.coeFn_add
      (wholePlaneScalarToC2CoordL2 0 (scalarVectorMulL2 (E := ℂ) volume
          (wholePlaneCoordLInf ((0 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
          (wholePlaneC2CoordL2 j (horizontalModeL2 kappa hkappa))))
      (wholePlaneScalarToC2CoordL2 1 (scalarVectorMulL2 (E := ℂ) volume
          (wholePlaneCoordLInf ((1 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
          (wholePlaneC2CoordL2 j (horizontalModeL2 kappa hkappa)))),
    horizontalModePartialDerivativeL2_coe_ae kappa hkappa j,
    wholePlaneScalarToC2CoordL2_mul_coe_ae 0
      (wholePlaneCoordLInf ((0 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
      (wholePlaneC2CoordL2 j (horizontalModeL2 kappa hkappa)),
    wholePlaneScalarToC2CoordL2_mul_coe_ae 1
      (wholePlaneCoordLInf ((1 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
      (wholePlaneC2CoordL2 j (horizontalModeL2 kappa hkappa)),
    horizontalModeVelocity_transverseCoord_coe_ae N Omega 0,
    horizontalModeVelocity_transverseCoord_coe_ae N Omega 1,
    wholePlaneC2CoordL2_coe_ae j (horizontalModeL2 kappa hkappa),
    horizontalModeL2_coe_ae kappa hkappa] with y ha hb hd h0 h1 hv0 hv1 hcj hbf
  simp only [Pi.add_apply] at ha hb
  have hcy : ((wholePlaneC2CoordL2 j (horizontalModeL2 kappa hkappa) :
      WholePlaneScalarL2) : WholePlane → ℂ) y = horizontalModeField kappa y j := by
    rw [hcj, hbf]
  rw [ha, hb, hd, h0, h1, hv0, hv1, hcy, horizontalModePivotField,
    ← Fin.sum_univ_two (fun i : Fin 2 ↦ scalarToVecPoint (ι := Fin 2) i
      (horizontalTransverseVelocityField Omega y i * horizontalModeField kappa y j)),
    sum_scalarToVecPoint_mul]

/-- The transverse divergence of the certified mode has the pointwise branchwise formula as an
`L²` representative. -/
theorem horizontalDivergence_horizontalModeH1_coe_ae
    (kappa : ℂ) (hkappa : 0 < kappa.re) :
    ((horizontalDivergence (horizontalModeH1 kappa hkappa) : WholePlaneScalarL2) :
        WholePlane → ℂ) =ᵐ[volume] horizontalModeDivergenceField kappa := by
  have hexpand : horizontalDivergence (horizontalModeH1 kappa hkappa) =
      wholePlaneC2CoordL2 0 (horizontalModePartialDerivativeL2 kappa hkappa 0) +
        wholePlaneC2CoordL2 1 (horizontalModePartialDerivativeL2 kappa hkappa 1) := by
    simp only [horizontalDivergence, Fin.sum_univ_two, add_apply,
      ContinuousLinearMap.comp_apply, wholePlaneH1FirstDerivative_horizontalModeH1]
  rw [hexpand]
  filter_upwards [Lp.coeFn_add
      (wholePlaneC2CoordL2 0 (horizontalModePartialDerivativeL2 kappa hkappa 0))
      (wholePlaneC2CoordL2 1 (horizontalModePartialDerivativeL2 kappa hkappa 1)),
    wholePlaneC2CoordL2_coe_ae 0 (horizontalModePartialDerivativeL2 kappa hkappa 0),
    wholePlaneC2CoordL2_coe_ae 1 (horizontalModePartialDerivativeL2 kappa hkappa 1),
    horizontalModePartialDerivativeL2_coe_ae kappa hkappa 0,
    horizontalModePartialDerivativeL2_coe_ae kappa hkappa 1] with y ha h0 h1 hd0 hd1
  simp only [Pi.add_apply] at ha
  rw [ha, h0, h1, hd0, hd1, horizontalModeDivergenceField, Fin.sum_univ_two]

/-- The transport term `w_⊥·∇_⊥ b` of the mass pivot, pointwise. -/
theorem horizontalTransport_horizontalModeH1_coe_ae
    (N Omega : ℝ) {kappa : ℂ} (hkappa : 0 < kappa.re) :
    ((horizontalTransport (horizontalModeVelocity N Omega) (horizontalModeH1 kappa hkappa) :
        WholePlaneC2L2) : WholePlane → C2) =ᵐ[volume]
      fun y ↦ ∑ j : Fin 2, horizontalTransverseVelocityField Omega y j •
        horizontalModePartialDerivative kappa j y := by
  have hexpand : horizontalTransport (horizontalModeVelocity N Omega)
      (horizontalModeH1 kappa hkappa) =
      scalarVectorMulL2 (E := C2) volume
          (wholePlaneCoordLInf ((0 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
          (horizontalModePartialDerivativeL2 kappa hkappa 0) +
        scalarVectorMulL2 (E := C2) volume
          (wholePlaneCoordLInf ((1 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
          (horizontalModePartialDerivativeL2 kappa hkappa 1) := by
    simp only [horizontalTransport, Fin.sum_univ_two, add_apply,
      ContinuousLinearMap.comp_apply, wholePlaneH1FirstDerivative_horizontalModeH1]
  rw [hexpand]
  filter_upwards [Lp.coeFn_add
      (scalarVectorMulL2 (E := C2) volume
        (wholePlaneCoordLInf ((0 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
        (horizontalModePartialDerivativeL2 kappa hkappa 0))
      (scalarVectorMulL2 (E := C2) volume
        (wholePlaneCoordLInf ((1 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
        (horizontalModePartialDerivativeL2 kappa hkappa 1)),
    scalarVectorMulL2_coe_ae (E := C2) volume
      (wholePlaneCoordLInf ((0 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
      (horizontalModePartialDerivativeL2 kappa hkappa 0),
    scalarVectorMulL2_coe_ae (E := C2) volume
      (wholePlaneCoordLInf ((1 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
      (horizontalModePartialDerivativeL2 kappa hkappa 1),
    horizontalModeVelocity_transverseCoord_coe_ae N Omega 0,
    horizontalModeVelocity_transverseCoord_coe_ae N Omega 1,
    horizontalModePartialDerivativeL2_coe_ae kappa hkappa 0,
    horizontalModePartialDerivativeL2_coe_ae kappa hkappa 1] with y ha h0 h1 hv0 hv1 hd0 hd1
  simp only [Pi.add_apply] at ha
  rw [ha, h0, h1, hv0, hv1, hd0, hd1, Fin.sum_univ_two]

/-- The stretching-divergence term `w_⊥(Div_⊥ b)` of the mass pivot, pointwise. -/
theorem horizontalMassPivotDivergenceTerm_coe_ae
    (N Omega : ℝ) {kappa : ℂ} (hkappa : 0 < kappa.re) :
    (((wholePlaneScalarToC2CoordL2 0 (scalarVectorMulL2 (E := ℂ) volume
          (wholePlaneCoordLInf ((0 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
          (horizontalDivergence (horizontalModeH1 kappa hkappa))) +
        wholePlaneScalarToC2CoordL2 1 (scalarVectorMulL2 (E := ℂ) volume
          (wholePlaneCoordLInf ((1 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
          (horizontalDivergence (horizontalModeH1 kappa hkappa))) : WholePlaneC2L2)) :
          WholePlane → C2) =ᵐ[volume]
      fun y ↦ horizontalModeDivergenceField kappa y •
        horizontalTransverseVelocityField Omega y := by
  filter_upwards [Lp.coeFn_add
      (wholePlaneScalarToC2CoordL2 0 (scalarVectorMulL2 (E := ℂ) volume
        (wholePlaneCoordLInf ((0 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
        (horizontalDivergence (horizontalModeH1 kappa hkappa))))
      (wholePlaneScalarToC2CoordL2 1 (scalarVectorMulL2 (E := ℂ) volume
        (wholePlaneCoordLInf ((1 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
        (horizontalDivergence (horizontalModeH1 kappa hkappa)))),
    wholePlaneScalarToC2CoordL2_mul_coe_ae 0
      (wholePlaneCoordLInf ((0 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
      (horizontalDivergence (horizontalModeH1 kappa hkappa)),
    wholePlaneScalarToC2CoordL2_mul_coe_ae 1
      (wholePlaneCoordLInf ((1 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
      (horizontalDivergence (horizontalModeH1 kappa hkappa)),
    horizontalModeVelocity_transverseCoord_coe_ae N Omega 0,
    horizontalModeVelocity_transverseCoord_coe_ae N Omega 1,
    horizontalDivergence_horizontalModeH1_coe_ae kappa hkappa] with y ha h0 h1 hv0 hv1 hdiv
  simp only [Pi.add_apply] at ha
  rw [ha, h0, h1, hv0, hv1, hdiv,
    ← Fin.sum_univ_two (fun i : Fin 2 ↦ scalarToVecPoint (ι := Fin 2) i
      (horizontalTransverseVelocityField Omega y i * horizontalModeDivergenceField kappa y)),
    sum_scalarToVecPoint_mul]

/-- The mass pivot `M = N²b + w_⊥·∇_⊥b + iN w₃ b + w_⊥(Div_⊥ b)` of the certified mode has the
pointwise branchwise formula as an `L²` representative. -/
theorem horizontalWeakFormMassPivot_coe_ae
    (N Omega : ℝ) {kappa : ℂ} (hkappa : 0 < kappa.re) :
    ((horizontalWeakFormMassPivot N (horizontalModeVelocity N Omega)
        (horizontalModeH1 kappa hkappa) : WholePlaneC2L2) : WholePlane → C2) =ᵐ[volume]
      horizontalModeMassField N Omega kappa := by
  have hexpand : horizontalWeakFormMassPivot N (horizontalModeVelocity N Omega)
      (horizontalModeH1 kappa hkappa) =
      (((N : ℂ) ^ 2) • horizontalModeL2 kappa hkappa +
            horizontalTransport (horizontalModeVelocity N Omega)
              (horizontalModeH1 kappa hkappa) +
            (I * (N : ℂ)) • scalarVectorMulL2 (E := C2) volume
              (wholePlaneCoordLInf 2 (horizontalModeVelocity N Omega))
              (horizontalModeL2 kappa hkappa)) +
        (wholePlaneScalarToC2CoordL2 0 (scalarVectorMulL2 (E := ℂ) volume
            (wholePlaneCoordLInf ((0 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
            (horizontalDivergence (horizontalModeH1 kappa hkappa))) +
          wholePlaneScalarToC2CoordL2 1 (scalarVectorMulL2 (E := ℂ) volume
            (wholePlaneCoordLInf ((1 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
            (horizontalDivergence (horizontalModeH1 kappa hkappa)))) := by
    simp only [horizontalWeakFormMassPivot, Fin.sum_univ_two,
      wholePlaneH1Embedding_horizontalModeH1]
  rw [hexpand]
  filter_upwards [Lp.coeFn_add
      (((N : ℂ) ^ 2) • horizontalModeL2 kappa hkappa +
        horizontalTransport (horizontalModeVelocity N Omega) (horizontalModeH1 kappa hkappa) +
        (I * (N : ℂ)) • scalarVectorMulL2 (E := C2) volume
          (wholePlaneCoordLInf 2 (horizontalModeVelocity N Omega))
          (horizontalModeL2 kappa hkappa))
      (wholePlaneScalarToC2CoordL2 0 (scalarVectorMulL2 (E := ℂ) volume
          (wholePlaneCoordLInf ((0 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
          (horizontalDivergence (horizontalModeH1 kappa hkappa))) +
        wholePlaneScalarToC2CoordL2 1 (scalarVectorMulL2 (E := ℂ) volume
          (wholePlaneCoordLInf ((1 : Fin 2).castSucc) (horizontalModeVelocity N Omega))
          (horizontalDivergence (horizontalModeH1 kappa hkappa)))),
    Lp.coeFn_add
      (((N : ℂ) ^ 2) • horizontalModeL2 kappa hkappa +
        horizontalTransport (horizontalModeVelocity N Omega) (horizontalModeH1 kappa hkappa))
      ((I * (N : ℂ)) • scalarVectorMulL2 (E := C2) volume
        (wholePlaneCoordLInf 2 (horizontalModeVelocity N Omega))
        (horizontalModeL2 kappa hkappa)),
    Lp.coeFn_add (((N : ℂ) ^ 2) • horizontalModeL2 kappa hkappa)
      (horizontalTransport (horizontalModeVelocity N Omega) (horizontalModeH1 kappa hkappa)),
    Lp.coeFn_smul ((N : ℂ) ^ 2) (horizontalModeL2 kappa hkappa),
    horizontalModeL2_coe_ae kappa hkappa,
    horizontalTransport_horizontalModeH1_coe_ae N Omega hkappa,
    Lp.coeFn_smul (I * (N : ℂ)) (scalarVectorMulL2 (E := C2) volume
      (wholePlaneCoordLInf 2 (horizontalModeVelocity N Omega))
      (horizontalModeL2 kappa hkappa)),
    scalarVectorMulL2_coe_ae (E := C2) volume
      (wholePlaneCoordLInf 2 (horizontalModeVelocity N Omega))
      (horizontalModeL2 kappa hkappa),
    horizontalModeVelocity_axialCoord_coe_ae N Omega,
    horizontalMassPivotDivergenceTerm_coe_ae N Omega hkappa] with
    y ha hb hc hsm1 hmode htr hsm2 hax hvax hdiv
  simp only [Pi.add_apply, Pi.smul_apply] at ha hb hc hsm1 hsm2
  simp only [ha, hb, hc, hsm1, hsm2, hmode, htr, hax, hvax, hdiv,
    horizontalModeMassField]

/-! ## The `L²` bulk identity -/

/-- The unit circle is a Lebesgue null set of the plane, so a pointwise identity valid off it
is an identity of `L²` classes. -/
theorem volume_unitCircle_eq_zero : volume {y : WholePlane | ‖y‖ = 1} = 0 := by
  have h : {y : WholePlane | ‖y‖ = 1} = sphere (0 : WholePlane) 1 := by
    ext y
    simp
  rw [h]
  exact Measure.addHaar_sphere volume 0 1

/-- Almost every point of the plane is off the unit circle. -/
theorem ae_norm_ne_one : ∀ᵐ y : WholePlane, ‖y‖ ≠ 1 := by
  rw [ae_iff]
  simpa using volume_unitCircle_eq_zero

/-- **The bulk identity**, hypothesis 2 of
`horizontalModeDistributionalEquation_of_coordinate_sources`:

`bulk 0 + bulk 1 = M + λ_* b`   in `L²(ℝ²;ℂ²)`,

with `bulk j` the `L²` class of the pointwise `{∂_j D_j}`.  The `w_⊥(Div_⊥ b)` terms cancel by
Leibniz, `Δ_⊥ b = κ² b` by the radial Bessel system, and the transport-stretching terms cancel
by `NU = -Ω` at the angular index `j = 1`. -/
theorem horizontalModeBulkL2_add
    {N Omega : ℝ} (hN : N ≠ 0) {kappa : ℂ} (hkappa : 0 < kappa.re) :
    horizontalModeBulkL2 Omega kappa hkappa 0 + horizontalModeBulkL2 Omega kappa hkappa 1 =
      horizontalWeakFormMassPivot N (horizontalModeVelocity N Omega)
          (horizontalModeH1 kappa hkappa) +
        horizontalEigenvalue N kappa •
          wholePlaneH1Embedding C2 (horizontalModeH1 kappa hkappa) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (horizontalModeBulkL2 Omega kappa hkappa 0)
      (horizontalModeBulkL2 Omega kappa hkappa 1),
    horizontalModeBulkL2_coe_ae Omega kappa hkappa 0,
    horizontalModeBulkL2_coe_ae Omega kappa hkappa 1,
    Lp.coeFn_add (horizontalWeakFormMassPivot N (horizontalModeVelocity N Omega)
        (horizontalModeH1 kappa hkappa))
      (horizontalEigenvalue N kappa • horizontalModeL2 kappa hkappa),
    horizontalWeakFormMassPivot_coe_ae N Omega hkappa,
    Lp.coeFn_smul (horizontalEigenvalue N kappa) (horizontalModeL2 kappa hkappa),
    horizontalModeL2_coe_ae kappa hkappa,
    ae_norm_ne_one] with y ha hb0 hb1 hc hm hsm hmode hy
  simp only [Pi.add_apply, Pi.smul_apply] at ha hc hsm
  simp only [wholePlaneH1Embedding_horizontalModeH1, ha, hb0, hb1, hc, hm, hsm, hmode]
  exact horizontalModeBulkField_add hN hkappa hy

/-! ## The certified mode -/

section Certified

variable {N Omega : ℝ} {kappa : ℂ}

/-- The bulk field `{∂_j D_j}` of the certified mode, as an `L²` element. -/
def horizontalModeBulk (hd : CertifiedInterfaceData N Omega kappa) (j : Fin 2) :
    WholePlaneC2L2 :=
  horizontalModeBulkL2 Omega kappa hd.kappa_re_pos j

/-- **Obligation 2 of `lem:jump-horizontal-mode` for the certified data**: the bulk fields of
the two coordinate directions add up to the mass pivot plus the eigenvalue term.  This is
`hbulk` of `horizontalModeDistributionalEquation_of_coordinate_sources`, verbatim. -/
theorem horizontalModeBulk_add (hd : CertifiedInterfaceData N Omega kappa) :
    horizontalModeBulk hd 0 + horizontalModeBulk hd 1 =
      horizontalWeakFormMassPivot N (horizontalModeVelocity N Omega) (horizontalMode hd) +
        horizontalEigenvalue N kappa • wholePlaneH1Embedding C2 (horizontalMode hd) :=
  horizontalModeBulkL2_add (ne_of_gt hd.scale_pos) hd.kappa_re_pos

end Certified

end HorizontalMode
end FastDynamo
