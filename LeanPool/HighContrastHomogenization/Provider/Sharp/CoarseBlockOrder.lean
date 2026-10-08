/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Sharp.ReflectionOrder
public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import LeanPool.HighContrastHomogenization.Setup.Response
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.AdjointSymmetry.BasicAdjoint
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.MuAdmissibility
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.MatrixExtraction

/-!
# High-contrast homogenization: Provider.Sharp.CoarseBlockOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The pathwise block bounds of the coarse response

The elementary bounds for the coarse block (`s.introduction`) assert the sharp
order `𝐀^♯(U) ≤ 𝐀(U)` along every realization of the coefficient field.  By the reduction of
`ReflectionOrder` this
is the pair of signed reflection bounds `±R ≤ 𝐀(U)`, that is, the pair of scalar
inequalities

  `± P₁ · P₂ ≤ ½ P · 𝐀(U) P`

over doubled vectors `P = (P₁, P₂)`.  Both are the same variational statement
about the coarse energy `μ(U; P)` whose Hessian `𝐀(U)` is: the pointwise Young
inequality on the doubled coefficient matrix bounds the block energy density
below by the pairing of the potential and flux fields, and that pairing averages
to `P₁ · P₂` because the potential correction is a gradient of zero trace and the
flux correction is solenoidal of zero normal trace — the div-curl cancellation.

Only the first sign has to be quoted: the second is the first read on the adjoint
field, since flipping the flux half of a doubled vector and transposing the
coefficient field leaves the coarse energy invariant and reverses the pairing.

The identification of `μ(U; ·)` with the quadratic form of the coarse block
matrix holds over every bounded open convex domain, not only over cubes; it comes
from the canonical recovery data of the variational problem, exactly as the
subadditivity of the response does.

The conclusion is unconditional along the coefficient space: the sample field
only enters through a measurable pointwise uniformly elliptic representative,
which every member of the class has, and the coarse response only sees the almost
everywhere class of the field.
-/

namespace HCPolySupport
namespace HighContrast
namespace Sharp

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Ellipticity of a pointwise representative -/

/-- A measurable field uniformly elliptic at every point of a measurable set is
elliptic on that set, in the sense the coarse energy consumes. -/
theorem isEllipticFieldOn_of_measurable {lam Lam : ℝ} {f : CoeffField d}
    (hf : Measurable f) {U : Set (Vec d)}
    (hell : ∀ x ∈ U, IsEllipticMatrix lam Lam (f x))
    (hU : MeasurableSet U) : IsEllipticFieldOn lam Lam U f := by
  classical
  refine ⟨?_, hell⟩
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  exact Measurable.ite hU
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hf)) measurable_const

/-! ## The coarse energy is the quadratic form of the coarse block -/

/-- **The coarse energy is half the quadratic form of the coarse block matrix**,
on every bounded open convex domain.  This is the identity that carries the
variational bounds of the coarse energy onto the block matrix of the variational
coarse block. -/
theorem mu_eq_half_blockQuadratic [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {lam Lam : ℝ} {f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U f) (hvol : 0 < (volume U).toReal) (P : BlockVec d) :
    Mu U P f = 1 / 2 * blockVecDot P (blockMatVecMul (coarseBlockMatrix U f) P) := by
  have : IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  obtain ⟨_R, _sigma0, _compat, hA, -, -, -, -, -⟩ :=
    Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
      hU hEll hvol
  exact Mu_eq_half_blockVecDot_coarseBlockMatrix ⟨_, hA⟩ P

/-! ## The two signed pairing bounds -/

/-- **The lower pairing bound** `P₁ · P₂ ≤ ½ P · 𝐀(U) P`: the div-curl form of
the first half of the elementary block bounds. -/
theorem pairing_le_half_blockQuadratic [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {lam Lam : ℝ} {f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U f) (hvol : 0 < (volume U).toReal) (P : BlockVec d) :
    vecDot P.1 P.2 ≤ 1 / 2 * blockVecDot P (blockMatVecMul (coarseBlockMatrix U f) P) := by
  have : IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  rw [← mu_eq_half_blockQuadratic hU hEll hvol]
  exact IsBlockMuAdmissible.mu_ge_vecDot_of_isEllipticFieldOn_of_isSobolevRegularDomain
    hU.isSobolevRegularDomain hEll hvol.ne'

/-- **The opposite pairing bound** `-P₁ · P₂ ≤ ½ P · 𝐀(U) P`, the second half of
the elementary block bounds: the lower bound read on the adjoint field, whose
coarse energy at the flux-flipped vector is the coarse energy of the field. -/
theorem neg_pairing_le_half_blockQuadratic [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {lam Lam : ℝ} {f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U f) (hvol : 0 < (volume U).toReal) (P : BlockVec d) :
    -vecDot P.1 P.2 ≤ 1 / 2 * blockVecDot P (blockMatVecMul (coarseBlockMatrix U f) P) := by
  have : IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  have hadj := IsBlockMuAdmissible.mu_ge_vecDot_of_isEllipticFieldOn_of_isSobolevRegularDomain
    (P := blockVecFlipFlux P) (a := adjointCoeffField f)
    hU.isSobolevRegularDomain (isEllipticFieldOn_adjointCoeffField hEll) hvol.ne'
  rw [Mu_adjointCoeffField_flipFlux] at hadj
  have hfst : (blockVecFlipFlux P).1 = P.1 := rfl
  have hsnd : (blockVecFlipFlux P).2 = -P.2 := rfl
  rw [hfst, hsnd, vecDot_neg_right] at hadj
  rw [← mu_eq_half_blockQuadratic hU hEll hvol]
  linarith only [hadj]

/-! ## The pathwise block bounds -/

/-- **The pathwise block bounds** for a field with a pointwise uniformly elliptic
representative, on a bounded open convex domain of positive volume. -/
theorem blockMatLoewnerLE_blockSharp_coarseBlockMatrix [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {lam Lam : ℝ} {f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U f) (hvol : 0 < (volume U).toReal) :
    BlockMatLoewnerLE (blockSharp (coarseBlockMatrix U f)) (coarseBlockMatrix U f) :=
  blockMatLoewnerLE_blockSharp_of_signed (isSymmetricBlockMat_coarseBlockMatrix U f)
    (pairing_le_half_blockQuadratic hU hEll hvol)
    (neg_pairing_le_half_blockQuadratic hU hEll hvol)

/-- **The pathwise block bounds on the coefficient space**: along every
realization the variational coarse block response dominates its own sharp, on
every bounded open convex domain of positive volume.  No positivity or invertibility of the response
is assumed, and no dimension is excluded. -/
theorem blockMatLoewnerLE_blockSharp_coarseBlock {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hvol : 0 < (volume U).toReal) (a : CoeffSpace d) :
    BlockMatLoewnerLE (blockSharp (coarseBlock U a)) (coarseBlock U a) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact blockMatLoewnerLE_of_dim_zero _ _
  · have : NeZero d := ⟨hd.ne'⟩
    obtain ⟨lam, Lam, f, -, -, hfm, hfp, hfa⟩ :=
      exists_pointwise_elliptic_representative a.2 hU.isBoundedDomain.isBounded
    have hEll : IsEllipticFieldOn lam Lam U f :=
      isEllipticFieldOn_of_measurable hfm hfp hU.isOpen.measurableSet
    rw [coarseBlock_eq_of_ae_eq a hfa]
    exact blockMatLoewnerLE_blockSharp_coarseBlockMatrix hU hEll hvol

/-- **The pathwise block bounds** on a nonempty bounded open convex domain: the
form in which the elementary block bounds are consumed, the positivity of the
volume being that of a nonempty open set. -/
theorem blockMatLoewnerLE_blockSharp_coarseBlock_of_nonempty {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) (a : CoeffSpace d) :
    BlockMatLoewnerLE (blockSharp (coarseBlock U a)) (coarseBlock U a) :=
  blockMatLoewnerLE_blockSharp_coarseBlock hU
    (ENNReal.toReal_pos (hU.isOpen.measure_pos volume hne).ne' hU.volume_lt_top.ne) a

end

end Sharp
end HighContrast
end HCPolySupport
