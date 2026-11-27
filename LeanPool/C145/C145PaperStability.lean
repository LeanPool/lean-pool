/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145DRE8PhysicalStability

/-! Paper-facing Theorem E: the least measurement gain is an attained,
positive minimum derived from the actual grid and cyclic source overlaps.
The signatures below live in source vertex coordinates. Calibration is exact;
this result does not assert recovery from perturbed calibration or noisy jets. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
open C145.H2
variable {n : ℕ} {ρ : Type*} [Fintype ρ]

omit [Fintype ρ] in
/-- Modal coordinates of a source vertex signature reconstruct that very
signature under the actual orthonormal source frame. -/
theorem paper_signature_reconstruction
    (U : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U)
    (h : ρ → Fin (n + 1) → ℝ) :
    (fun r => (Matrix.of U).mulVec (C145.Pulse.modalOverlap U (h r))) = h := by
  funext r v
  have hr := congrFun
    (C145.UncalibratedSmallH2.spectralPort_modalOverlap U (h r) hU) v
  simpa only [Matrix.mulVec, dotProduct, Matrix.of_apply,
    C145CoordinatePermutation.spectralPort, mul_comm] using hr

/-- B_H is literally the Euclidean norm of the source vertex signature family;
moving the signatures into the modal tensor coordinates preserves it. -/
theorem paper_signatureNorm_modal
    (U : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U)
    (h : ρ → Fin (n + 1) → ℝ) :
    signatureNorm (fun r => C145.Pulse.modalOverlap U (h r)) = signatureNorm h := by
  have hr := signatureNorm_rotate (Matrix.of U) (columnOrthonormal_matrix U hU)
    (fun r => C145.Pulse.modalOverlap U (h r))
  rw [paper_signature_reconstruction U hU h] at hr
  exact hr.symm

/-- The measured vector contains the literal ideal H2 differences of the
actual two frames and their own actual ports. Its ambient norm is Euclidean.
Overlap weights remain inside T, never in the tensor Frobenius norm. -/
def paperH2SampleDifference
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ)
    (b b' rates : Fin (n + 1) → ℝ)
    (sNodes tNodes : Fin (2 * (n + 1) - 1) → ℝ) :
    EuclideanSpace ℝ (Fin (2 * (n + 1)-1) × Fin (2 * (n + 1)-1)) :=
  WithLp.toLp 2 (fun p =>
    H rates (C145PhysicalFrame.T V (C145.Pulse.modalOverlap V b'))
      (sNodes p.1) (tNodes p.2) -
    H rates (C145PhysicalFrame.T U (C145.Pulse.modalOverlap U b))
      (sNodes p.1) (tNodes p.2))

/-- Exact overlap calibration identifies the abstract grid vector with the
actual own-port second-transfer differences, without assuming H2 equality. -/
theorem paperH2SampleDifference_eq_grid
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ)
    (b b' rates : Fin (n + 1) → ℝ)
    (sNodes tNodes : Fin (2 * (n + 1) - 1) → ℝ)
    (hcalibration : C145.Pulse.modalOverlap V b' = C145.Pulse.modalOverlap U b) :
    paperH2SampleDifference U V b b' rates sNodes tNodes =
      positiveGridMap (C145.Pulse.modalOverlap U b) rates sNodes tNodes
        (fromTensor (C145PhysicalFrame.C V-C145PhysicalFrame.C U)) := by
  ext p
  change H rates (C145PhysicalFrame.T V (C145.Pulse.modalOverlap V b'))
      (sNodes p.1) (tNodes p.2) -
    H rates (C145PhysicalFrame.T U (C145.Pulse.modalOverlap U b))
      (sNodes p.1) (tNodes p.2) = _
  rw [hcalibration]
  exact (actual_grid_coordinate_physical_response
    (C145.Pulse.modalOverlap U b) rates sNodes tNodes U V p).symm

/-- Paper Theorem E with no caller-supplied singular gain or complement
nontriviality certificate. Here N=n+1≥3. Source/competitor frames are actual
orthonormal frames with the same constant signed ground column. Their rates
are common and positive, and their own port overlaps are exactly calibrated.

The positive separation lower bound delta, beta≥0, the universal kernel bundle
estimate and q<1 are precisely the remaining manuscript premises. The kernel
and its orthogonal complement are taken inside V0. The conclusion supplies a
positive attained least gain, its unit-sphere minimality, its homogeneous gain
bound, and the literal unweighted Frobenius/Euclidean physical stability bound.
No equality of the two H2 responses is required. -/
theorem paper_fixed_calibration_stability
    (hN : 3 ≤ n + 1)
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U)
    (hV : C145PhysicalFrame.ColumnOrthonormal V)
    (hGU : ∀ v, U v 0 = c) (hGV : ∀ v, V v 0 = c)
    (b b' rates : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < C145.Pulse.modalOverlap U b i)
    (hcalibration : C145.Pulse.modalOverlap V b' = C145.Pulse.modalOverlap U b)
    (hRates : ∀ i, 0 < rates i)
    (sNodes tNodes : Fin (2 * (n + 1) - 1) → ℝ)
    (hsNodes : Function.Injective sNodes) (htNodes : Function.Injective tNodes)
    (hsPos : ∀ i, 0 < sNodes i) (htPos : ∀ i, 0 < tNodes i)
    (h : ρ → Fin (n + 1) → ℝ) (delta beta : ℝ)
    (hd : 0 < delta) (hb : 0 ≤ beta)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤ signatureSq h j k)
    (hq : Real.sqrt ((n + 1 : ℕ) + 2) * beta / delta < 1)
    (hkernel : ∀ k : physicalDifferenceSpace n,
      k ∈ physicalH2Kernel (C145.Pulse.modalOverlap U b) rates →
      ‖physicalSliceBundle (fun r => C145.Pulse.modalOverlap U (h r)) k‖ ≤ beta * ‖k‖) :
    ∃ (sigma : ℝ) (u : (physicalH2Kernel (C145.Pulse.modalOverlap U b) rates)ᗮ),
      0 < sigma ∧ ‖u‖ = 1 ∧
      ‖physicalGridMap (C145.Pulse.modalOverlap U b) rates sNodes tNodes
        (u : physicalDifferenceSpace n)‖ = sigma ∧
      (∀ v : (physicalH2Kernel (C145.Pulse.modalOverlap U b) rates)ᗮ, ‖v‖ = 1 →
        sigma ≤ ‖physicalGridMap (C145.Pulse.modalOverlap U b) rates sNodes tNodes
          (v : physicalDifferenceSpace n)‖) ∧
      (∀ r : physicalDifferenceSpace n,
        r ∈ (physicalH2Kernel (C145.Pulse.modalOverlap U b) rates)ᗮ →
        sigma * ‖r‖ ≤ ‖physicalGridMap (C145.Pulse.modalOverlap U b) rates sNodes tNodes r‖) ∧
      Real.sqrt (tensorSq (C145PhysicalFrame.C V-C145PhysicalFrame.C U)) ≤
        (Real.sqrt ((n + 1 : ℕ) + 2) * signatureNorm h /
          (delta * (1-Real.sqrt ((n + 1 : ℕ) + 2) * beta / delta) * sigma)) *
          ‖paperH2SampleDifference U V b b' rates sNodes tNodes‖ := by
  let i : Fin (n + 1) := ⟨1, by omega⟩
  have hi : i ≠ 0 := by
    intro heq
    have hv := congrArg Fin.val heq
    norm_num [i] at hv
  obtain ⟨sigma, u, hsigma, hu, hvalue, hminimal, hgain⟩ :=
    physicalGrid_exists_least_gain_of_nonzero_overlap
      (C145.Pulse.modalOverlap U b) rates hRates sNodes tNodes
      hsNodes htNodes hsPos htPos i hi (ne_of_gt (ha i))
  refine ⟨sigma, u, hsigma, hu, hvalue, hminimal, hgain, ?_⟩
  have hmodalSep : ∀ j k, j ≠ k → delta ^ 2 ≤
      signatureSq (fun r => (Matrix.of U).mulVec (C145.Pulse.modalOverlap U (h r))) j k := by
    rw [paper_signature_reconstruction U hU h]
    exact hsep
  have hbound := actual_calibrated_grid_stability
    (C145.Pulse.modalOverlap U b) rates hRates sNodes tNodes
    hsNodes htNodes hsPos htPos U V c hU hV hGU hGV
    (fun r => C145.Pulse.modalOverlap U (h r)) delta beta sigma
    hd hb hsigma hmodalSep hq hgain hkernel
  rw [paper_signatureNorm_modal U hU h] at hbound
  rw [paperH2SampleDifference_eq_grid U V b b' rates sNodes tNodes hcalibration]
  have hFrob : Real.sqrt (tensorSq (C145PhysicalFrame.C V-C145PhysicalFrame.C U)) =
      ‖fromTensor (C145PhysicalFrame.C V-C145PhysicalFrame.C U)‖ := by
    rw [←norm_fromTensor_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [hFrob]
  exact hbound

end C145DRE8

end
