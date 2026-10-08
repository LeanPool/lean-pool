/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.DirichletDomain
public import LeanPool.HighContrastHomogenization.Geometry.CoarseSchurBridge
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.AffineCoeffFamily
public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseCoefficient
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewCoefficient
public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationLoads
public import LeanPool.HighContrastHomogenization.Provider.Selection.RoundedHops

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.NormalizedRootCoefficient

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Exact identity normalization of a coefficient sample

The symmetric part of the comparison coefficient is normalized by its exact
projective square root.  Before the affine pullback, the coefficient is
recentered by the comparison skew part and multiplied by the scalar used in
that square root.  The resulting constant comparison matrix is exactly the
identity; no rounded grid enters this identity.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

theorem isEllipticMatrix_positive_smul {lam Lam c : ℝ}
    {A : Mat d} (hc : 0 < c) (hA : IsEllipticMatrix lam Lam A) :
    IsEllipticMatrix (c * lam) (c * Lam) (c • A) := by
  rcases hA with ⟨hlam, hlamLam, hlower, hupper⟩
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hlamLam
  have hdet : IsUnit A.det :=
    isUnit_det_of_isEllipticMatrix ⟨hlam, hlamLam, hlower, hupper⟩
  refine ⟨mul_pos hc hlam, mul_le_mul_of_nonneg_left hlamLam hc.le, ?_, ?_⟩
  · intro ξ
    rw [smul_matVecMul, vecDot_smul_right]
    have h := mul_le_mul_of_nonneg_left (hlower ξ) hc.le
    nlinarith only [h]
  · intro ξ
    have hinv : ((c • A)⁻¹ : Mat d) = c⁻¹ • A⁻¹ := by
      rw [nonsing_inv_smul c hc.ne' hdet]
    rw [hinv, smul_matVecMul, vecDot_smul_right]
    have h := mul_le_mul_of_nonneg_left (hupper ξ) (inv_nonneg.mpr hc.le)
    have hleft :
        (c * Lam)⁻¹ * vecNormSq ξ = c⁻¹ * (Lam⁻¹ * vecNormSq ξ) := by
      field_simp [hc.ne', hLam.ne']
    rw [hleft]
    exact h

namespace CoeffSpace

/-- Positive scalar multiplication on the qualitative coefficient space. -/
@[expose]
def positiveScale (c : ℝ) (hc : 0 < c) (a : CoeffSpace d) : CoeffSpace d where
  val := c • a.1
  property := by
    intro R hR
    obtain ⟨lam, Lam, hlam, hle, hEll⟩ := a.2 R hR
    refine ⟨c * lam, c * Lam, mul_pos hc hlam,
      mul_le_mul_of_nonneg_left hle hc.le, ?_⟩
    filter_upwards [hEll, AEEqFun.coeFn_smul c a.1] with x hx hscale hxb
    rw [hscale]
    exact isEllipticMatrix_positive_smul hc (hx hxb)

/-- The positive scalar action has its expected pointwise representative. -/
theorem positiveScale_ae (c : ℝ) (hc : 0 < c) (a : CoeffSpace d) :
    (⇑(a.positiveScale c hc).1 : CoeffField d) =ᵐ[volume]
      fun x ↦ c • (a.1 x : Mat d) := by
  exact AEEqFun.coeFn_smul c a.1

/-- Restriction to a Chapter 2 domain is an a.e. scalar rescaling. -/
theorem coeffOn_positiveScale_AEScaled (c : ℝ) (hc : 0 < c)
    (a : CoeffSpace d) (U : Book.Ch02.Domain d) :
    Book.Ch02.CoeffOn.AEScaled c (a.coeffOn U)
      ((a.positiveScale c hc).coeffOn U) := by
  unfold Book.Ch02.CoeffOn.AEScaled
  simp only [CoeffSpace.coeffOn_toCoeffField]
  exact ae_restrict_of_ae (positiveScale_ae c hc a)

end CoeffSpace

/-- The scalar used by the exact normalized root is positive in positive
dimension. -/
theorem normalizedRootScale_pos [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) :
    0 < specBound ((symmPart abar)⁻¹) :=
  specBound_inv_symmPart_pos (Nat.pos_of_ne_zero (NeZero.ne d)) hS

/-- The exact normalized root is positive definite. -/
theorem normalizedRoot_posDef_of_posDef [NeZero d] {m : Mat d}
    (hm : m.PosDef) : (Selection.normalizedRoot m).PosDef := by
  refine (posDef_matSqrt hm).smul (Real.sqrt_pos.mpr ?_)
  rw [specBound_eq_norm hm.inv.posSemidef]
  have hne : (m⁻¹ : Mat d) ≠ 0 := hm.inv.isUnit.ne_zero
  exact (norm_pos_iff.mpr hne : 0 < ‖(m⁻¹ : Mat d)‖)

/-- The exact normalized root squares to the scalar-normalized matrix. -/
theorem normalizedRoot_mul_self {m : Mat d} (hm : m.PosDef) :
    Selection.normalizedRoot m * Selection.normalizedRoot m = specBound m⁻¹ • m := by
  rw [Selection.normalizedRoot_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt (specBound_nonneg _), (matSqrt_spec hm.posSemidef).2]

namespace Selection

private theorem norm_matSqrt_eq_sqrt_specBound {m : Mat d} (hm : m.PosDef) :
    ‖matSqrt m‖ = Real.sqrt (specBound m) := by
  have hherm : (matSqrt m)ᴴ = matSqrt m :=
    (matSqrt_spec hm.posSemidef).1.isHermitian
  have hsq : ‖matSqrt m‖ ^ 2 = specBound m := by
    rw [pow_two, ← CStarRing.norm_self_mul_star,
      Matrix.star_eq_conjTranspose, hherm,
      (matSqrt_spec hm.posSemidef).2,
      specBound_eq_norm hm.posSemidef]
  symm
  exact (Real.sqrt_eq_iff_eq_sq (specBound_nonneg m) (norm_nonneg _)).mpr
    hsq.symm

/-- The operator norm of the exact normalized root is its projective
eccentricity. -/
theorem norm_normalizedRoot_eq_witnessEccentricity {m : Mat d}
    (hm : m.PosDef) :
    ‖normalizedRoot m‖ = witnessEccentricity m := by
  rw [normalizedRoot, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    norm_matSqrt_eq_sqrt_specBound hm, witnessEccentricity,
    ← Real.sqrt_mul (specBound_nonneg m⁻¹), mul_comm]

/-- The inverse of the exact normalized root has operator norm at most one. -/
theorem normalizedRoot_inv_norm_le_one [NeZero d] {m : Mat d}
    (hm : m.PosDef) :
    ‖(normalizedRoot m)⁻¹‖ ≤ 1 := by
  have hroot : (normalizedRoot m).PosDef :=
    normalizedRoot_posDef_of_posDef hm
  have horder : (1 : Mat d) ≤ normalizedRoot m :=
    Recurrence.one_le_normalized_matSqrt hm
  have hinv : (normalizedRoot m)⁻¹ ≤ (1 : Mat d) := by
    simpa using inv_le_inv_of_le Matrix.PosDef.one hroot horder
  have hnorm :=
    norm_le_norm_of_le hroot.inv.posSemidef Matrix.PosSemidef.one hinv
  simpa using hnorm

end Selection

/-- The coefficient sample after skew recentering and exact scalar
normalization. -/
@[expose]
def normalizedCenteredCoeff [NeZero d] (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) : CoeffSpace d :=
  (a.subSkew (skewPart abar) (matTranspose_skewPart abar)).positiveScale
    (specBound ((symmPart abar)⁻¹)) (normalizedRootScale_pos hS)

/-- The exactly normalized coefficient produces a compatible reference-cube
family for every parent adapted domain. -/
theorem exists_normalizedReferenceCoeffFamily [NeZero d]
    (a : CoeffSpace d) (abar : Mat d) (hS : (symmPart abar).PosDef) (t : ℤ) :
    ∃ aRef : Book.Ch03.CoeffFamily d,
      ∀ Q : TriadicCube d,
        (aRef.coeffOn Q).toCoeffField =
          affineCoefficient (Selection.normalizedRoot (symmPart abar))
            ((Matrix.isUnit_iff_isUnit_det _).mp
              (normalizedRoot_posDef_of_posDef hS).isUnit)
            ((normalizedCenteredCoeff a abar hS).coeffOn
              (Response.adaptedDomain (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField := by
  exact exists_adaptedReferenceCoeffFamily
    (normalizedRoot_posDef_of_posDef hS) t (normalizedCenteredCoeff a abar hS)

end

end HighContrast
end HCPolySupport
