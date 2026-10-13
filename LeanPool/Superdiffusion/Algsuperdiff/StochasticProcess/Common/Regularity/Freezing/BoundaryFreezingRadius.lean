/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.LocalContrast
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.SectorReflectionBox

/-!
# BoundaryFreezingRadius

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Freezing at a point of a closed axis cube

At any point of the closed cube — a face, an edge or a corner included — the
coefficient frozen and normalized at that point equals the identity there.
Continuity on the closed cube therefore produces a radius on which it stays
uniformly close to the identity, and the finitely many coordinate gaps produce
a radius on which no unincident face is met.  Taking the smaller of the two
radii gives the scale at which the boundary sector is the intersection of a
ball with the cube and the frozen coefficient has small contrast.

A coefficient whose symmetric part is the scalar matrix `nu * I` is elliptic
with lower constant `nu`, and its upper constant is controlled by any bound on
the operator norm of its skew part; on a compact set continuity supplies such a
bound.  So continuity alone, with no restriction on the size of the skew part,
produces a full ellipticity certificate.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Freezing

open MeasureTheory HCPolySupport
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.StochasticProcess.Common.Regularity
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ}

/-! ## 1. Continuity of the distance to the identity -/

/-- The operator distance of a matrix from the identity is continuous. -/
theorem continuous_norm_applyMat_sub_one :
    Continuous fun A : Mat d => ‖HilbertVec.applyMat (A - (1 : Mat d))‖ := by
  have hop : Continuous fun A : Mat d =>
      (matrixToHilbertOperator (A - (1 : Mat d)) : HilbertVec d →L[ℝ] HilbertVec d) :=
    matrixToHilbertOperator.continuous.comp (continuous_id.sub continuous_const)
  exact hop.norm

/-! ## 2. Measurability of the frozen coefficient -/

theorem measurable_normalizedFrozenCoeff {nu : ℝ} {a : CoeffField d}
    (ha : Measurable a) (x₀ : Vec d) :
    Measurable (normalizedFrozenCoeff nu a x₀) := by
  refine (measurable_pi_iff).2 fun j => (measurable_pi_iff).2 fun k => ?_
  have hentry : Measurable fun y : Vec d => a y j k :=
    ((measurable_pi_iff).1 ((measurable_pi_iff).1 ha j)) k
  have hval : (fun y : Vec d => normalizedFrozenCoeff nu a x₀ y j k) =
      fun y : Vec d => nu⁻¹ * (a y j k - (a x₀ - nu • (1 : Mat d)) j k) := by
    funext y
    rfl
  rw [hval]
  exact (hentry.sub measurable_const).const_mul _

/-! ## 3. The freezing radius at a point of the closed cube -/

theorem normalizedFrozenCoeff_self {nu : ℝ} (hnu : 0 < nu) (a : CoeffField d)
    (x₀ : Vec d) : normalizedFrozenCoeff nu a x₀ x₀ = (1 : Mat d) := by
  have hval : normalizedFrozenCoeff nu a x₀ x₀ = nu⁻¹ • (nu • (1 : Mat d)) := by
    rw [normalizedFrozenCoeff]
    congr 1
    abel
  rw [hval, ← mul_smul, inv_mul_cancel₀ hnu.ne', one_smul]

private theorem exists_axisCubeFaceClearance_radius [NeZero d]
    (z : Vec d) {L : ℝ} (hL : 0 < L) {x₀ : Vec d}
    (hx₀ : MemAxisCubeClosure z L x₀) :
    ∃ R > 0, AxisCubeFaceClearance z L R x₀ := by
  classical
  have hcoordNonempty : Nonempty (Fin d) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  set gap : Fin d → ℝ := fun i =>
    min (if x₀ i = z i then L else x₀ i - z i)
      (if x₀ i = z i + L then L else z i + L - x₀ i) with hgap
  have hgapPos : ∀ i : Fin d, 0 < gap i := by
    intro i
    refine lt_min ?_ ?_
    · by_cases hi : x₀ i = z i
      · rw [ite_eq_left hi]
        exact hL
      · rw [ite_eq_right hi]
        have hle := (hx₀ i).1
        exact sub_pos.2 (lt_of_le_of_ne hle (Ne.symm hi))
    · by_cases hi : x₀ i = z i + L
      · rw [ite_eq_left hi]
        exact hL
      · rw [ite_eq_right hi]
        have hle := (hx₀ i).2
        exact sub_pos.2 (lt_of_le_of_ne hle hi)
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty
  refine ⟨Finset.univ.inf' hne gap, ?_, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff hne).2 fun i _ => hgapPos i
  · intro i hi
    have hle : Finset.univ.inf' hne gap ≤ gap i :=
      Finset.inf'_le gap (Finset.mem_univ i)
    have hstep : gap i ≤ x₀ i - z i := by
      refine le_trans (min_le_left _ _) ?_
      rw [ite_eq_right hi]
    exact hle.trans hstep
  · intro i hi
    have hle : Finset.univ.inf' hne gap ≤ gap i :=
      Finset.inf'_le gap (Finset.mem_univ i)
    have hstep : gap i ≤ z i + L - x₀ i := by
      refine le_trans (min_le_right _ _) ?_
      rw [ite_eq_right hi]
    exact hle.trans hstep

/-- A radius at a point of the closed cube on which no unincident face is met
and the frozen normalized coefficient is `delta`-close to the identity. -/
theorem exists_boundary_freezing_radius [NeZero d]
    (z : Vec d) {L : ℝ} (hL : 0 < L)
    {nu : ℝ} (hnu : 0 < nu) {a : CoeffField d}
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d))
      {x | MemAxisCubeClosure z L x})
    {x₀ : Vec d} (hx₀ : MemAxisCubeClosure z L x₀) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ R > 0, AxisCubeFaceClearance z L R x₀ ∧
      ∀ y ∈ euclideanBall x₀ R, MemAxisCubeClosure z L y →
        ‖HilbertVec.applyMat
          (normalizedFrozenCoeff nu a x₀ y - (1 : Mat d))‖ ≤ delta := by
  classical
  obtain ⟨R₀, hR₀, hclear⟩ := exists_axisCubeFaceClearance_radius z hL hx₀
  set K : Set (Vec d) := {x | MemAxisCubeClosure z L x} with hK
  have hcoeffCont : ContinuousOn (normalizedFrozenCoeff nu a x₀) K :=
    continuousOn_normalizedFrozenCoeff hcont x₀
  have hdistCont : ContinuousOn (fun y => ‖HilbertVec.applyMat
      (normalizedFrozenCoeff nu a x₀ y - (1 : Mat d))‖) K :=
    continuous_norm_applyMat_sub_one.comp_continuousOn hcoeffCont
  have hx₀K : x₀ ∈ K := hx₀
  have hvalue : ‖HilbertVec.applyMat
      (normalizedFrozenCoeff nu a x₀ x₀ - (1 : Mat d))‖ = 0 := by
    rw [normalizedFrozenCoeff_self hnu a x₀, sub_self, HilbertVec.applyMat_zero,
      norm_zero]
  obtain ⟨s, hs, hsbound⟩ :=
    Metric.continuousWithinAt_iff.mp (hdistCont x₀ hx₀K) delta hdelta
  refine ⟨min R₀ s, lt_min hR₀ hs, ?_, ?_⟩
  · constructor
    · intro i hi
      exact (min_le_left R₀ s).trans (hclear.1 i hi)
    · intro i hi
      exact (min_le_left R₀ s).trans (hclear.2 i hi)
  · intro y hy hyK
    have hydist : dist y x₀ < s :=
      (HCPolySupport.euclideanBall_subset_metricBall (lt_min hR₀ hs) hy).trans_le
        (min_le_right R₀ s)
    have hstep := hsbound hyK hydist
    rw [Real.dist_eq, hvalue, sub_zero] at hstep
    have habs : ‖HilbertVec.applyMat
        (normalizedFrozenCoeff nu a x₀ y - (1 : Mat d))‖ ≤
        |‖HilbertVec.applyMat
          (normalizedFrozenCoeff nu a x₀ y - (1 : Mat d))‖| := le_abs_self _
    exact habs.trans hstep.le

/-! ## 4. Ellipticity from a scalar symmetric part and a bounded skew part -/

private theorem matVecMul_smul_one_of_scalar (c : ℝ) (v : Vec d) :
    matVecMul (c • (1 : Mat d)) v = c • v := by
  rw [smul_matVecMul]
  funext i
  simp [matVecMul, Matrix.one_apply]

private theorem vecDot_matVecMul_self_of_symmPart_eq
    {nu : ℝ} {A : Mat d} (hsymm : symmPart A = nu • (1 : Mat d)) (xi : Vec d) :
    vecDot xi (matVecMul A xi) = nu * vecNormSq xi := by
  rw [← vecDot_matVecMul_symmPart A xi, hsymm, matVecMul_smul_one_of_scalar,
    vecDot_smul_right]
  rfl

private theorem continuousOn_of_continuousOn_sub_smul_one
    {K : Set (Vec d)} {nu : ℝ} {a : CoeffField d}
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d)) K) :
    ContinuousOn a K := by
  have heq : a = fun x => (a x - nu • (1 : Mat d)) + nu • (1 : Mat d) := by
    funext x
    abel
  rw [heq]
  exact hcont.add continuousOn_const

/-- **Ellipticity of a matrix with scalar symmetric part.**  If the symmetric
part of `A` is `nu * I` then the quadratic form of `A` is exactly `nu |xi|^2`,
and the skew part contributes nothing to it, so an operator-norm bound `M` on
the skew part gives the flux inequality with upper constant
`(nu ^ 2 + M ^ 2) / nu`.  No smallness of the skew part is required. -/
theorem isEllipticMatrix_of_symmPart_eq_of_opNorm_le
    {nu M : ℝ} (hnu : 0 < nu) {A : Mat d}
    (hsymm : symmPart A = nu • (1 : Mat d))
    (hM : ‖HilbertVec.applyMat (A - nu • (1 : Mat d))‖ ≤ M) :
    IsEllipticMatrix nu ((nu ^ 2 + M ^ 2) / nu) A := by
  have hskew := sub_scalar_one_isSkew_of_symmPart_eq hsymm
  have hquad : ∀ xi : Vec d, vecDot xi (matVecMul A xi) = nu * vecNormSq xi :=
    fun xi => vecDot_matVecMul_self_of_symmPart_eq hsymm xi
  rw [isEllipticMatrix_iff_isEllipticEntryLU]
  refine ⟨hnu, ?_, fun xi => ?_, fun eta => ?_⟩
  · rw [le_div_iff₀ hnu]
    have hsq : nu * nu = nu ^ 2 := by ring
    linarith only [sq_nonneg M, hsq]
  · rw [hquad xi]
  · set w : Vec d := matVecMul (A - nu • (1 : Mat d)) eta with hw
    have hcross : vecDot eta w = 0 := by
      rw [hw, vecDot_comm]
      exact vecDot_matVecMul_self_eq_zero_of_skew hskew eta
    have hsplit : matVecMul A eta = nu • eta + w := by
      rw [hw, sub_matVecMul, matVecMul_smul_one_of_scalar]
      abel
    have hexpand : vecNormSq (matVecMul A eta) =
        nu ^ 2 * vecNormSq eta + vecNormSq w := by
      rw [hsplit]
      show vecDot (nu • eta + w) (nu • eta + w) = _
      simp only [vecDot_add_left, vecDot_add_right, vecDot_smul_left,
        vecDot_smul_right, vecDot_comm w eta, hcross]
      simp only [show ∀ v : Vec d, vecNormSq v = vecDot v v from fun _ => rfl]
      ring
    have hnormsq : vecNormSq w ≤ M ^ 2 * vecNormSq eta := by
      refine le_trans (vecNormSq_matVecMul_le_applyMat_opNorm_sq_mul
        (A - nu • (1 : Mat d)) eta) ?_
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hM 2) (vecNormSq_nonneg eta)
    rw [hquad eta, hexpand]
    have hrhs : (nu ^ 2 + M ^ 2) / nu * (nu * vecNormSq eta) =
        (nu ^ 2 + M ^ 2) * vecNormSq eta := by
      field_simp
    rw [hrhs]
    linarith only [hnormsq]

/-- **Ellipticity of a continuous coefficient field with scalar symmetric
part.**  A bound `M` on the operator norm of the skew part over a set `K`
carrying the continuity gives the ellipticity certificate on every measurable
subset `W` of `K`, with constants `nu` and `(nu ^ 2 + M ^ 2) / nu`. -/
theorem isEllipticFieldOn_of_symmPart_eq_of_continuousOn
    {W K : Set (Vec d)} (hW : MeasurableSet W) (hWK : W ⊆ K)
    {nu M : ℝ} (hnu : 0 < nu) {a : CoeffField d}
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d)) K)
    (hM : ∀ y ∈ K, ‖HilbertVec.applyMat (a y - nu • (1 : Mat d))‖ ≤ M) :
    IsEllipticFieldOn nu ((nu ^ 2 + M ^ 2) / nu) W a := by
  classical
  refine ⟨?_, fun y hy => isEllipticMatrix_of_symmPart_eq_of_opNorm_le hnu
    (hsymm y) (hM y (hWK hy))⟩
  have ha : ContinuousOn a W :=
    (continuousOn_of_continuousOn_sub_smul_one hcont).mono hWK
  refine (measurable_pi_iff).2 fun i => (measurable_pi_iff).2 fun j => ?_
  have hij : ContinuousOn (fun x => a x i j) W :=
    continuousOn_pi.mp (continuousOn_pi.mp ha i) j
  exact hij.measurable_piecewise continuousOn_const hW

/-- **Ellipticity from compactness and continuity alone.**  On a compact set
the skew part is bounded, so a coefficient with scalar symmetric part and
continuous skew part of arbitrary size is elliptic on every measurable subset,
with constants that compactness supplies. -/
theorem exists_isEllipticFieldOn_of_symmPart_eq_of_isCompact
    {W K : Set (Vec d)} (hW : MeasurableSet W) (hK : IsCompact K) (hWK : W ⊆ K)
    {nu : ℝ} (hnu : 0 < nu) {a : CoeffField d}
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d)) K) :
    ∃ Lam : ℝ, IsEllipticFieldOn nu Lam W a := by
  have hop : ContinuousOn (fun y => (HilbertVec.applyMat
      (a y - nu • (1 : Mat d)) : HilbertVec d →L[ℝ] HilbertVec d)) K :=
    matrixToHilbertOperator.continuous.comp_continuousOn hcont
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hop
  exact ⟨(nu ^ 2 + M ^ 2) / nu,
    isEllipticFieldOn_of_symmPart_eq_of_continuousOn hW hWK hnu hsymm hcont hM⟩

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
