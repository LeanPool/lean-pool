/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.CG.Proofs.AdaptedDomainRecovery
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.OptimizerMeanIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SubcellCoefficientGluing
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CanonicalCutoffPairingMeasurability
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.PathwiseToAnnealedAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TerminalDeficitCarrierBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.BesovScaleSummationToolkit
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Setup.ProjectiveDistance
public import LeanPool.HighContrastHomogenization.Support.Ambient.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# High-contrast homogenization: Entry.Response.Pairing.CoarseBlockFenchelPairing

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Coarse-Block Toolkit for the Direct Fenchel Pairing

On a bounded open convex domain carrying a pointwise elliptic coefficient, the canonical coarse
block is the Hessian of an infimum of averages of a nonnegative density, hence positive
semidefinite, so its two diagonal quadratic forms are nonnegative, in particular for `a_∓ =
respCoeff∓ F a`; this file records their sample integrability with that of their crossed
product of square roots and the square of their sum. It records the pathwise mean identity of
AK.HC (2.32), computing the cell average of the doubled optimizer state as `x + R 𝐀(V) x`, and
shows every such average is measurable in the sample, since Chapter-2 gradient uniqueness
identifies each maximizer with the canonical selection. Combining these, it proves the direct
full-dual Fenchel pairing of AK.HC, Lemma A.1, (A.4): the cell average, paired against `Y = (P,
Q)`, is controlled by the square root of the cell's own coarse-block energy of `Y`.  This is the
coarse-block estimate consumed by `p.response.transfer`.
-/

section
/-!
## Sample integrability of the quadratic readouts of a coarse block

The cell half and the oscillation half of the cutoff-mean row of `p.response.transfer` read the
pathwise coarse block only through four scalars: the two diagonal quadratic forms against the
deterministic dual variable, their crossed product of square roots, and the square of their sum.
All four are integrable as soon as the entries of the block are, because the quadratic form is a
fixed real linear combination of the entries and the crossed product of square roots is dominated
by the arithmetic mean of the two forms.

This module records those four steps, together with the two bookkeeping facts the rows consume
about flat averages of integrable families and about domination by an absolute value.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

/-- **Domination by an integrable envelope.**  A measurable function whose modulus is bounded by an
integrable function is integrable. -/
theorem integrable_of_abs_le {α : Type*} [MeasurableSpace α] {P : Measure α} {f g : α → ℝ}
    (hmeas : AEStronglyMeasurable f P) (hg : Integrable g P) (h : ∀ a, |f a| ≤ g a) :
    Integrable f P := by
  refine hg.mono' hmeas ?_
  filter_upwards with a
  rw [Real.norm_eq_abs]
  exact h a

/-- **Integrability of a flat average of an integrable family.**  A normalized finite sum of
`P`-integrable functions is `P`-integrable. -/
theorem integrable_avsum {α ι : Type*} [MeasurableSpace α] {P : Measure α} (Z : Finset ι)
    (h : ι → α → ℝ) (hh : ∀ w ∈ Z, Integrable (h w) P) :
    Integrable (fun a => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, h w a) P :=
  (integrable_finsetSum Z hh).const_mul _

/-- **The crossed product of square roots of two nonnegative integrable functions is
integrable.**  The product is dominated by the arithmetic mean of the two functions, by the
nonnegativity of the square of the difference of the square roots. -/
theorem integrable_sqrt_mul_sqrt_gen {α : Type*} [MeasurableSpace α] {P : Measure α} {f g : α → ℝ}
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ a, 0 ≤ g a) (hf : Integrable f P) (hg : Integrable g P) :
    Integrable (fun a => Real.sqrt (f a) * Real.sqrt (g a)) P := by
  have hmeas : AEStronglyMeasurable (fun a => Real.sqrt (f a) * Real.sqrt (g a)) P :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.1).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hg.1)
  refine integrable_of_abs_le hmeas ((hf.add hg).const_mul (1 / 2 : ℝ)) ?_
  intro a
  have hsq : (Real.sqrt (f a) - Real.sqrt (g a)) ^ 2
      = f a - 2 * (Real.sqrt (f a) * Real.sqrt (g a)) + g a := by
    rw [sub_sq, Real.sq_sqrt (hf0 a), Real.sq_sqrt (hg0 a)]
    ring
  have hnn : 0 ≤ (Real.sqrt (f a) - Real.sqrt (g a)) ^ 2 := sq_nonneg _
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  simp only [Pi.add_apply]
  linarith only [hnn, hsq]

/-- **The crossed product of square roots is integrable without a sign hypothesis.**  The square
root of a negative number is zero, so the product is bounded by the crossed product of the square
roots of the moduli, and the previous domination applies to those. -/
theorem integrable_sqrt_mul_sqrt_of_integrable {α : Type*} [MeasurableSpace α] {P : Measure α}
  {f g : α → ℝ}
    (hf : Integrable f P) (hg : Integrable g P) :
    Integrable (fun a => Real.sqrt (f a) * Real.sqrt (g a)) P := by
  have habs := integrable_sqrt_mul_sqrt_gen (P := P) (f := fun a => |f a|) (g := fun a => |g a|)
    (fun a => abs_nonneg _) (fun a => abs_nonneg _) hf.abs hg.abs
  refine integrable_of_abs_le ?_ habs ?_
  · exact (Real.continuous_sqrt.comp_aestronglyMeasurable hf.1).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hg.1)
  · intro a
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact mul_le_mul (Real.sqrt_le_sqrt (le_abs_self _)) (Real.sqrt_le_sqrt (le_abs_self _))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- **The square of the sum of the two square roots is integrable.**  Expanding the square gives
the two functions plus twice their crossed product of square roots. -/
theorem integrable_sq_sqrt_add_sqrt_gen {α : Type*} [MeasurableSpace α] {P : Measure α}
    {f g : α → ℝ} (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ a, 0 ≤ g a)
    (hf : Integrable f P) (hg : Integrable g P) :
    Integrable (fun a => (Real.sqrt (f a) + Real.sqrt (g a)) ^ 2) P := by
  have hcross := integrable_sqrt_mul_sqrt_gen hf0 hg0 hf hg
  have hsum : Integrable (fun a => f a + 2 * (Real.sqrt (f a) * Real.sqrt (g a)) + g a) P :=
    (hf.add (hcross.const_mul 2)).add hg
  refine hsum.congr ?_
  filter_upwards with a
  rw [add_sq, Real.sq_sqrt (hf0 a), Real.sq_sqrt (hg0 a)]
  ring

/-- **The quadratic form of a matrix family against a fixed vector is integrable.**  The form is
the fixed real linear combination `∑ i ∑ k, Y i * M i k * Y k` of the entries. -/
theorem integrable_vecDot_matVecMul {d : ℕ} {α : Type*} [MeasurableSpace α] {P : Measure α}
    (M : α → Mat d) (Y : Vec d) (hM : ∀ i k : Fin d, Integrable (fun a => M a i k) P) :
    Integrable (fun a => vecDot Y (matVecMul (M a) Y)) P := by
  have hEq : (fun a => vecDot Y (matVecMul (M a) Y))
      = fun a => ∑ i : Fin d, ∑ k : Fin d, Y i * (M a i k * Y k) := by
    funext a
    simp only [vecDot, matVecMul, Finset.mul_sum]
  rw [hEq]
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => ?_
  exact ((hM i k).mul_const (Y k)).const_mul (Y i)

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Positive semidefiniteness of the coarse block of a cell

On a bounded open convex domain carrying a pointwise elliptic coefficient field, the canonical
coarse block matrix is the Hessian of the minimal block energy `Mu` with prescribed doubled mean.
That energy is an infimum of averages of a nonnegative density, hence nonnegative, so the block is
positive semidefinite. In particular its two diagonal blocks — the `b` and the `S_*^{-1}` appearing
in `e.response.cutoff.estimate` — are positive semidefinite, which are the side conditions of the
direct full-dual pairing.
-/

open HCPolySupport.HighContrast.CG

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The coarse block of a cell is positive semidefinite: for every doubled vector `X` the
quadratic form `X · (blockMatVecMul (coarseBlockMatrix V b) X)` is nonnegative. -/
theorem zero_le_blockVecDot_coarseBlockMatrix {d : ℕ} [NeZero d] {V : Set (Vec d)}
    {lam Lam : ℝ} {b : CoeffField d} (hConv : IsOpenBoundedConvexDomain V)
    (hEll : IsEllipticFieldOn lam Lam V b) (hvol : 0 < (volume V).toReal) (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul (coarseBlockMatrix V b) X) := by
  have hMu_nonneg : 0 ≤ Mu V X b := by
    refine le_Mu_of_forall_isBlockMuAdmissible fun Y _ => ?_
    unfold volumeAverage
    refine mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) ?_
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem hConv.isOpen.measurableSet] with x hx
    have hco := blockMatrixOfCoeff_coercive_of_isEllipticMatrix (hEll.2 x hx) (Y.eval x)
    have hZ : 0 ≤ blockVecDot (Y.eval x) (Y.eval x) := blockVecDot_nonneg (Y.eval x)
    have hc : 0 ≤ lam / (1 + 2 * Lam ^ 2) :=
      div_nonneg (hEll.2 x hx).1.le (by positivity)
    have hmain : 0 ≤ blockVecDot (Y.eval x)
        (blockMatVecMul (blockMatrixOfCoeff (b x)) (Y.eval x)) :=
      le_trans (mul_nonneg hc hZ) hco
    unfold blockEnergyDensity blockCoeffField
    exact mul_nonneg (by norm_num) hmain
  have hMu_eq : Mu V X b =
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (coarseBlockMatrix V b) X) :=
    (isCoarseBlockMatrix_of_isOpenBoundedConvexDomain hConv hEll hvol).2 X
  rw [hMu_eq] at hMu_nonneg
  linarith only [hMu_nonneg]

/-- The upper-left diagonal block of the coarse block matrix is positive semidefinite: the block
quadratic form of `(p, 0)` is `p · (upperLeft p)`. -/
theorem zero_le_vecDot_coarseBlockMatrix_upperLeft {d : ℕ} [NeZero d] {V : Set (Vec d)}
    {lam Lam : ℝ} {b : CoeffField d} (hConv : IsOpenBoundedConvexDomain V)
    (hEll : IsEllipticFieldOn lam Lam V b) (hvol : 0 < (volume V).toReal) (p : Vec d) :
    0 ≤ vecDot p (matVecMul (coarseBlockMatrix V b).upperLeft p) := by
  have h := zero_le_blockVecDot_coarseBlockMatrix hConv hEll hvol (p, 0)
  have hquad : blockVecDot (p, 0) (blockMatVecMul (coarseBlockMatrix V b) (p, 0))
      = vecDot p (matVecMul (coarseBlockMatrix V b).upperLeft p) := by
    simp [blockVecDot, matVecMul_zero, vecDot_zero_left]
  rwa [hquad] at h

/-- The lower-right diagonal block of the coarse block matrix is positive semidefinite: the block
quadratic form of `(0, r)` is `r · (lowerRight r)`. -/
theorem zero_le_vecDot_coarseBlockMatrix_lowerRight {d : ℕ} [NeZero d] {V : Set (Vec d)}
    {lam Lam : ℝ} {b : CoeffField d} (hConv : IsOpenBoundedConvexDomain V)
    (hEll : IsEllipticFieldOn lam Lam V b) (hvol : 0 < (volume V).toReal) (r : Vec d) :
    0 ≤ vecDot r (matVecMul (coarseBlockMatrix V b).lowerRight r) := by
  have h := zero_le_blockVecDot_coarseBlockMatrix hConv hEll hvol (0, r)
  have hquad : blockVecDot (0, r) (blockMatVecMul (coarseBlockMatrix V b) (0, r))
      = vecDot r (matVecMul (coarseBlockMatrix V b).lowerRight r) := by
    simp [blockVecDot, matVecMul_zero, vecDot_zero_left]
  rwa [hquad] at h

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Nonnegativity of the two diagonal coarse-block forms of the recentred families

The source-load head of `p.response.transfer` is the sum of the square roots of the two diagonal
coarse-block quadratic forms of the recentred coefficient on an aligned cell.  Both forms are
nonnegative because the coarse block of an elliptic coefficient is positive semidefinite.  The
recentred coefficients `a_∓ = respCoeff∓ F a` are elliptic only almost everywhere, so each
statement is proved at a pointwise elliptic representative on the aligned cell and transported
back, the coarse block being unchanged by an almost-everywhere replacement of the coefficient.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The two diagonal coarse-block forms of `a_- = a - g` are nonnegative on every aligned
cell.**  Both entries of the source-load head of `p.response.transfer` are well defined on every
aligned cell of the response grid. -/
theorem zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (k : ℤ) (a : CoeffSpace d) (Y : BlockVec d)
    (W : Fin d → ℤ) :
    0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) k W)
            (respCoeffMinus F a)).upperLeft Y.1)
      ∧ 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) k W)
            (respCoeffMinus F a)).lowerRight Y.2) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinusAt (respGrid jStar F) hq k W F a
  have hC : coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k W) f =
      coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k W) (respCoeffMinus F a) :=
    (HCPolySupport.coarseBlockMatrix_congr_of_ae_eq hae).symm
  constructor
  · have h := zero_le_vecDot_coarseBlockMatrix_upperLeft
      (isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq k W) hEll
      (volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq k W) Y.1
    simpa only [hC] using h
  · have h := zero_le_vecDot_coarseBlockMatrix_lowerRight
      (isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq k W) hEll
      (volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq k W) Y.2
    simpa only [hC] using h

/-- **The two diagonal coarse-block forms of `a_+ = aᵀ + g` are nonnegative on every aligned
cell.**  The adjoint twin of
`zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter`. -/
theorem zero_le_vecDot_coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (k : ℤ) (a : CoeffSpace d) (Y : BlockVec d)
    (W : Fin d → ℤ) :
    0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) k W)
            (respCoeffPlus F a)).upperLeft Y.1)
      ∧ 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) k W)
            (respCoeffPlus F a)).lowerRight Y.2) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlusAt (respGrid jStar F) hq k W F a
  have hC : coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k W) f =
      coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k W) (respCoeffPlus F a) :=
    (HCPolySupport.coarseBlockMatrix_congr_of_ae_eq hae).symm
  constructor
  · have h := zero_le_vecDot_coarseBlockMatrix_upperLeft
      (isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq k W) hEll
      (volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq k W) Y.1
    simpa only [hC] using h
  · have h := zero_le_vecDot_coarseBlockMatrix_lowerRight
      (isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq k W) hEll
      (volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq k W) Y.2
    simpa only [hC] using h

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The optimizer mean identity on an aligned subcell at an almost-everywhere elliptic coefficient

The pathwise mean identity `AK.HC (2.32)` computes the cell mean of the doubled optimizer state of
a response maximizer as `x + R 𝐀(V) x` with `x = (-p, r)` and `𝐀(V)` the coarse block of the cell.
The response coefficients of `p.response.transfer` are elliptic only almost everywhere, while the
identity is available at a pointwise elliptic coefficient.  Carrying the harmonic field along an
almost everywhere elliptic representative preserves the maximizer property and the optimizer field
up to a null set, so the identity transfers verbatim to the aligned subcell.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The optimizer mean identity `AK.HC (2.32)` on an aligned adapted subcell `adaptedCellAtCenter
q j w`,
at a coefficient `b` that agrees almost everywhere there with a pointwise elliptic representative
`f`: the cell average of the doubled optimizer field of any response maximizer is
`(-p, r) + R 𝐀(adaptedCellAtCenter q j w; b) (-p, r)`. -/
theorem cellAverage_optimizerField_adaptedCellAtCenter_eq_blockResponseMean {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ) {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q j w) f)
    (hae : b =ᵐ[volumeMeasureOn (adaptedCellAtCenter q j w)] f)
    (p r : Vec d) (v : AHarmonicFunction b (adaptedCellAtCenter q j w))
    (hv : IsResponseMaximizer (adaptedCellAtCenter q j w) p r b v) :
    cellAverage (adaptedCellAtCenter q j w) (optimizerField b v)
      = blockResponseMean (coarseBlockMatrix (adaptedCellAtCenter q j w) b) (-p, r) := by
  exact cellAverage_optimizerField_eq_blockResponseMean_of_aeEq
    (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq j w)
    (volume_adaptedCellAtCenter_toReal_pos q hq j w) hEll hae p r v hv

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Cell averages of the doubled optimizer field are measurable in the sample

The doubled optimizer field of a response maximizer for the recentred coefficients `a_-` and
`a_+` is determined, up to a null set of the response cell, by the coefficient sample alone:
Chapter-2 almost-everywhere gradient uniqueness identifies every response maximizer with the
canonical selection.  Consequently every coordinate of the cell average of the doubled optimizer
field over a measurable subcell is a measurable function of the sample, for an arbitrary family of
maximizers.  These are the subcell averages entering the weak quantity of
`e.response.weak.estimate`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The full block vector of a cell average is the volume average of the full block vector of the
field. -/
private theorem toFullBlockVec_cellAverage {d : ℕ} (V : Set (Vec d)) (X : Vec d → BlockVec d)
    (alpha : BlockCoord d) :
    toFullBlockVec (cellAverage V X) alpha =
      volumeAverage V (fun x => toFullBlockVec (X x) alpha) := by
  cases alpha <;> rfl

/-- The canonical doubled optimizer state depends on the coefficient only through its
almost-everywhere class on the domain. -/
private theorem canonicalOptimizerBlockState_congr_ae {d : ℕ} {U : Book.Ch02.Domain d}
    {A B : Book.Ch02.CoeffOn U} (hAB : Book.Ch02.CoeffOn.AEEq A B) (p r : Vec d) :
    canonicalOptimizerBlockState U A p r
      =ᵐ[volumeMeasureOn (U : Set (Vec d))] canonicalOptimizerBlockState U B p r := by
  have hgrad : (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory U A) p r).toSolution.toH1.grad
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory U B) p r).toSolution.toH1.grad := by
    simpa only [Book.Ch02.Solution.SameGradientAE, Book.Ch02.Solution.toH1_ofAEEq] using
      (Book.Ch02.canonicalMaximizer_sameGradientAE_ofAEEq hAB p r)
  filter_upwards [hgrad, hAB] with x hgradx hcoeffx
  simp only [canonicalOptimizerBlockState]
  rw [hgradx, hcoeffx]

/-- The cell average of the doubled optimizer field of an arbitrary response maximizer for a
coefficient agreeing almost everywhere with an elliptic field equals the cell average of the
canonical doubled optimizer state for that field. -/
private theorem cellAverage_optimizerField_eq_canonicalBlockState {d : ℕ}
    {U : Book.Ch02.Domain d} {V : Set (Vec d)} (hVU : V ⊆ (U : Set (Vec d)))
    {b f : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) f)
    (hbf : b =ᵐ[volumeMeasureOn (U : Set (Vec d))] f) (p q : Vec d)
    (u : AHarmonicFunction b (U : Set (Vec d)))
    (hu : IsResponseMaximizer (U : Set (Vec d)) p q b u)
    (aU : Book.Ch02.CoeffOn U)
    (hA : Book.Ch02.CoeffOn.AEEq (coeffOnOfIsEllipticFieldOn (U := U) hlam hle hEll) aU) :
    cellAverage V (optimizerField b u)
      = cellAverage V (canonicalOptimizerBlockState U aU p q) := by
  calc cellAverage V (optimizerField b u)
      = cellAverage V (optimizerField f
          (canonicalAHarmonicFunctionOfCoeffOn
            (coeffOnOfIsEllipticFieldOn (U := U) hlam hle hEll) p q)) :=
        cellAverage_optimizerField_eq_canonical (U := U) hVU hlam hle hEll hbf p q u hu
    _ = cellAverage V (canonicalOptimizerBlockState U
          (coeffOnOfIsEllipticFieldOn (U := U) hlam hle hEll) p q) := by
        apply congrArg (cellAverage V)
        funext x
        rfl
    _ = cellAverage V (canonicalOptimizerBlockState U aU p q) :=
        cellAverage_congr_ae hVU (canonicalOptimizerBlockState_congr_ae hA p q)

/-- The minus bridge at an invertible grid: the cell average of the doubled optimizer field of an
arbitrary response maximizer for `a_-` equals the cell average of the canonical state for `a_-`. -/
private theorem cellAverage_optimizerField_respCoeffMinus_eq_canonical {d : ℕ}
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffMinus F a) u)
    {V : Set (Vec d)} (hVU : V ⊆ HighContrast.adaptedCell q t) :
    cellAverage V (optimizerField (respCoeffMinus F a) u)
      = cellAverage V (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  exact cellAverage_optimizerField_eq_canonicalBlockState (U := adaptedDomain q hq t)
    hVU hlam hle hEll hbf p r u hu (canonicalRespCoeffMinusOn q hq t F a) (by
      filter_upwards [hbf.symm] with x hx
      simpa only [canonicalRespCoeffMinusOn_toFun] using! hx)

/-- The plus bridge at an invertible grid: the cell average of the doubled optimizer field of an
arbitrary response maximizer for `a_+` equals the cell average of the canonical state for `a_+`. -/
private theorem cellAverage_optimizerField_respCoeffPlus_eq_canonical {d : ℕ}
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffPlus F a) u)
    {V : Set (Vec d)} (hVU : V ⊆ HighContrast.adaptedCell q t) :
    cellAverage V (optimizerField (respCoeffPlus F a) u)
      = cellAverage V (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  exact cellAverage_optimizerField_eq_canonicalBlockState (U := adaptedDomain q hq t)
    hVU hlam hle hEll hbf p r u hu (canonicalRespCoeffPlusOn q hq t F a) (by
      filter_upwards [hbf.symm] with x hx
      simpa only [canonicalRespCoeffPlusOn_toFun] using! hx)

/-- Each coordinate of the cell average of the doubled optimizer field of an arbitrary family of
response maximizers for the recentred coefficient `a_-` is measurable in the coefficient sample.
The field need not be measurable in the sample, but its cell average is determined by the
measurable canonical selection through Chapter-2 a.e. gradient uniqueness, so the subcell average
entering the weak quantity of `e.response.weak.estimate` is measurable. -/
theorem measurable_cellAverage_optimizerField_respCoeffMinus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d) (alpha : BlockCoord d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t) :
    Measurable fun a : CoeffSpace d =>
      toFullBlockVec (cellAverage V (optimizerField (respCoeffMinus F a) (uM a))) alpha := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d =>
      toFullBlockVec (cellAverage V (optimizerField (respCoeffMinus F a) (uM a))) alpha)
      = fun a : CoeffSpace d => volumeAverage V (fun x => toFullBlockVec
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x) alpha) := by
    funext a
    rw [show cellAverage V (optimizerField (respCoeffMinus F a) (uM a)) = _ from
      cellAverage_optimizerField_respCoeffMinus_eq_canonical (q := respGrid jStar F) hq t F a
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a) (hmax a) hVU]
    rw [toFullBlockVec_cellAverage]
  rw [hEq]
  exact measurable_cellAverage_canonicalRespCoeffMinus (respGrid jStar F) hq t F
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) alpha hV hVU

/-- Each coordinate of the cell average of the doubled optimizer field of an arbitrary family of
response maximizers for the recentred coefficient `a_+` is measurable in the coefficient sample.
This is the plus twin of `measurable_cellAverage_optimizerField_respCoeffMinus`. -/
theorem measurable_cellAverage_optimizerField_respCoeffPlus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d) (alpha : BlockCoord d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t) :
    Measurable fun a : CoeffSpace d =>
      toFullBlockVec (cellAverage V (optimizerField (respCoeffPlus F a) (uP a))) alpha := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d =>
      toFullBlockVec (cellAverage V (optimizerField (respCoeffPlus F a) (uP a))) alpha)
      = fun a : CoeffSpace d => volumeAverage V (fun x => toFullBlockVec
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x) alpha) := by
    funext a
    rw [show cellAverage V (optimizerField (respCoeffPlus F a) (uP a)) = _ from
      cellAverage_optimizerField_respCoeffPlus_eq_canonical (q := respGrid jStar F) hq t F a
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a) (hmax a) hVU]
    rw [toFullBlockVec_cellAverage]
  rw [hEq]
  exact measurable_cellAverage_canonicalRespCoeffPlus (respGrid jStar F) hq t F
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) alpha hV hVU

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The direct full-dual pairing of a cell average against a state

The direct Fenchel pairing of AK.HC, Lemma A.1, display (A.4): the cell average of the doubled
optimizer field, paired across its two slots with a state `Y = (P, Q)`, is controlled by the square
root of the cell's own coarse-block energy of `Y` — read through the two diagonal blocks of the
coarse block, `b` in the gradient slot and `S_*^{-1}` in the flux slot, exactly the two blocks from
which the source load `L_s^{±}` is built — times the square root of the pathwise symmetric energy of
the field.  The pairing is `Y.2` against the cell-average gradient plus `Y.1` against the
cell-average flux, the full-dual form consumed by the cutoff-mean rows.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The quadratic form of a componentwise sum of doubled blocks is the sum of their quadratic
forms on a common doubled probe. -/
private theorem blockVecDot_blockMatVecMul_ofFullBlockMat_add {d : ℕ} (A B : BlockMat d)
    (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul (ofFullBlockMat (toFullBlockMat A + toFullBlockMat B)) X) =
      blockVecDot X (blockMatVecMul A X) + blockVecDot X (blockMatVecMul B X) := by
  rw [← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec,
    toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul,
    toFullBlockMat_ofFullBlockMat, Matrix.add_mulVec, dotProduct_add]

/-- The quadratic form of a doubled block with a vanishing first slot: only the lower-right
block acts, on the second slot. -/
private theorem blockVecDot_fstZero_blockMatVecMul {d : ℕ} (C : BlockMat d) (y : Vec d) :
    blockVecDot (0, y) (blockMatVecMul C (0, y)) =
      vecDot y (matVecMul C.lowerRight y) := by
  change vecDot 0 (matVecMul C.upperLeft 0 + matVecMul C.upperRight y) +
      vecDot y (matVecMul C.lowerLeft 0 + matVecMul C.lowerRight y) =
    vecDot y (matVecMul C.lowerRight y)
  simp only [matVecMul_zero, zero_add, vecDot_zero_left]

/-- The quadratic form of a doubled block with a vanishing second slot: only the upper-left
block acts, on the first slot. -/
private theorem blockVecDot_sndZero_blockMatVecMul {d : ℕ} (C : BlockMat d) (y : Vec d) :
    blockVecDot (y, 0) (blockMatVecMul C (y, 0)) =
      vecDot y (matVecMul C.upperLeft y) := by
  change vecDot y (matVecMul C.upperLeft y + matVecMul C.upperRight 0) +
      vecDot 0 (matVecMul C.lowerLeft y + matVecMul C.lowerRight 0) =
    vecDot y (matVecMul C.upperLeft y)
  simp only [matVecMul_zero, add_zero, vecDot_zero_left]

/-- Pairing a doubled vector whose first slot is zero with the slot-swapped image of `Z` leaves
only the first slot of `Z`, tested against the second slot of the probe. -/
private theorem blockVecDot_fstZero_blockSwap {d : ℕ} (y : Vec d) (Z : BlockVec d) :
    blockVecDot (0, y) (blockMatVecMul (blockSwap d) Z) = vecDot y Z.1 := by
  change vecDot 0 (blockMatVecMul (blockSwap d) Z).1 +
      vecDot y (blockMatVecMul (blockSwap d) Z).2 = vecDot y Z.1
  rw [blockMatVecMul_blockSwap_fst, blockMatVecMul_blockSwap_snd, vecDot_zero_left, zero_add]

/-- Pairing a doubled vector whose second slot is zero with the slot-swapped image of `Z` leaves
only the second slot of `Z`, tested against the first slot of the probe. -/
private theorem blockVecDot_sndZero_blockSwap {d : ℕ} (y : Vec d) (Z : BlockVec d) :
    blockVecDot (y, 0) (blockMatVecMul (blockSwap d) Z) = vecDot y Z.2 := by
  change vecDot y (blockMatVecMul (blockSwap d) Z).1 +
      vecDot 0 (blockMatVecMul (blockSwap d) Z).2 = vecDot y Z.2
  rw [blockMatVecMul_blockSwap_fst, blockMatVecMul_blockSwap_snd, vecDot_zero_left, add_zero]

/-- The swap block contributes nothing to the quadratic form of a doubled vector whose first
slot vanishes. -/
private theorem blockVecDot_fstZero_blockSwap_self {d : ℕ} (y : Vec d) :
    blockVecDot (0, y) (blockMatVecMul (blockSwap d) (0, y)) = 0 := by
  have h : ((0 : Vec d), y).1 = 0 := rfl
  rw [blockVecDot_fstZero_blockSwap, h, vecDot_zero_right]

/-- The swap block contributes nothing to the quadratic form of a doubled vector whose second
slot vanishes. -/
private theorem blockVecDot_sndZero_blockSwap_self {d : ℕ} (y : Vec d) :
    blockVecDot (y, 0) (blockMatVecMul (blockSwap d) (y, 0)) = 0 := by
  have h : (y, (0 : Vec d)).2 = 0 := rfl
  rw [blockVecDot_sndZero_blockSwap, h, vecDot_zero_right]

/-- The quadratic form of a scalar dilation of a matrix: `(c x) · A (c x) = c^2 (x · A x)`. -/
private theorem vecDot_smul_matVecMul_smul {d : ℕ} (c : ℝ) (A : Mat d) (x : Vec d) :
    vecDot (c • x) (matVecMul A (c • x)) = c ^ 2 * vecDot x (matVecMul A x) := by
  rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  ring

/-- The quadratic form of the coarse block augmented by the swap block, with the probe's first
slot vanishing, is the lower-right block form of the coarse block on the second slot. -/
private theorem qform_fstZero_add_swap {d : ℕ} (C : BlockMat d) (y : Vec d) :
    blockVecDot (0, y)
        (blockMatVecMul (ofFullBlockMat (toFullBlockMat C + toFullBlockMat (blockSwap d)))
          (0, y)) =
      vecDot y (matVecMul C.lowerRight y) := by
  rw [blockVecDot_blockMatVecMul_ofFullBlockMat_add, blockVecDot_fstZero_blockMatVecMul,
    blockVecDot_fstZero_blockSwap_self, add_zero]

/-- The quadratic form of the coarse block augmented by the swap block, with the probe's second
slot vanishing, is the upper-left block form of the coarse block on the first slot. -/
private theorem qform_sndZero_add_swap {d : ℕ} (C : BlockMat d) (y : Vec d) :
    blockVecDot (y, 0)
        (blockMatVecMul (ofFullBlockMat (toFullBlockMat C + toFullBlockMat (blockSwap d)))
          (y, 0)) =
      vecDot y (matVecMul C.upperLeft y) := by
  rw [blockVecDot_blockMatVecMul_ofFullBlockMat_add, blockVecDot_sndZero_blockMatVecMul,
    blockVecDot_sndZero_blockSwap_self, add_zero]

/-- Scaled form of `qform_fstZero_add_swap`. -/
private theorem qform_fstZero_add_swap_smul {d : ℕ} (C : BlockMat d) (c : ℝ) (y : Vec d) :
    blockVecDot (0, c • y)
        (blockMatVecMul (ofFullBlockMat (toFullBlockMat C + toFullBlockMat (blockSwap d)))
          (0, c • y)) =
      c ^ 2 * vecDot y (matVecMul C.lowerRight y) := by
  rw [qform_fstZero_add_swap, vecDot_smul_matVecMul_smul]

/-- Scaled form of `qform_sndZero_add_swap`. -/
private theorem qform_sndZero_add_swap_smul {d : ℕ} (C : BlockMat d) (c : ℝ) (y : Vec d) :
    blockVecDot (c • y, 0)
        (blockMatVecMul (ofFullBlockMat (toFullBlockMat C + toFullBlockMat (blockSwap d)))
          (c • y, 0)) =
      c ^ 2 * vecDot y (matVecMul C.upperLeft y) := by
  rw [qform_sndZero_add_swap, vecDot_smul_matVecMul_smul]

/-- Algebraic core of the full-dual pairing AK.HC (A.4): a real number `X` satisfying the Fenchel
inequality `lam * X ≤ lam^2 A / 2 + E / 2` for every real `lam`, with `A ≥ 0`, obeys
`X^2 ≤ A E`. -/
theorem sq_le_mul_of_forall_quadratic_le {X A E : ℝ} (hA : 0 ≤ A)
    (h : ∀ lam : ℝ, lam * X ≤ (lam ^ 2 / 2) * A + E / 2) :
    X ^ 2 ≤ A * E := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hX : X = 0 := by
      by_contra hXne
      have h1 := h ((E / 2 + 1) / X)
      have h2 : ((E / 2 + 1) / X) * X = E / 2 + 1 :=
        div_mul_cancel₀ (E / 2 + 1) hXne
      rw [h2] at h1
      rw [← hA0] at h1
      linarith only [h1]
    rw [hX, ← hA0]
    norm_num
  · have h1 := h (X / A)
    have hAne : A ≠ 0 := ne_of_gt hApos
    have h2A : (0 : ℝ) ≤ 2 * A := by positivity
    have hmul := mul_le_mul_of_nonneg_left h1 h2A
    have hL : (2 * A) * ((X / A) * X) = 2 * X ^ 2 := by
      field_simp
    have hR : (2 * A) * (((X / A) ^ 2 / 2) * A + E / 2) = X ^ 2 + A * E := by
      field_simp
    rw [hL, hR] at hmul
    linarith only [hmul]

/-- Square-root form of `sq_le_mul_of_forall_quadratic_le`: the same Fenchel hypothesis yields
`|X| ≤ sqrt A * sqrt E`. -/
theorem abs_le_sqrt_mul_sqrt_of_forall_quadratic_le {X A E : ℝ} (hA : 0 ≤ A)
    (h : ∀ lam : ℝ, lam * X ≤ (lam ^ 2 / 2) * A + E / 2) :
    |X| ≤ Real.sqrt A * Real.sqrt E := by
  have h1 : X ^ 2 ≤ A * E := sq_le_mul_of_forall_quadratic_le hA h
  calc
    |X| = Real.sqrt (X ^ 2) := (Real.sqrt_sq_eq_abs X).symm
    _ ≤ Real.sqrt (A * E) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt A * Real.sqrt E := Real.sqrt_mul hA E

/-- Gradient half of the direct full-dual pairing AK.HC (A.4): the cell average of the gradient of
a `b`-harmonic field, tested against `r`, is bounded by the square root of the lower-right coarse
block form of `r` times the square root of the pathwise symmetric energy of the field. -/
theorem abs_vecDot_cellAverage_grad_le {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {lam Lam : ℝ} {b : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain V) (hEll : IsEllipticFieldOn lam Lam V b)
    (hvol : 0 < (volume V).toReal) (v : AHarmonicFunction b V) (r : Vec d)
    (hA : 0 ≤ vecDot r (matVecMul (coarseBlockMatrix V b).lowerRight r)) :
    |vecDot r (cellAverage V (optimizerField b v)).1|
      ≤ Real.sqrt (vecDot r (matVecMul (coarseBlockMatrix V b).lowerRight r))
        * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) := by
  have hvar := forall_blockVecDot_cellAverage_optimizerField_le hConv hEll hvol v
  have hquad : ∀ t : ℝ,
      t * vecDot r (cellAverage V (optimizerField b v)).1 ≤
        (t ^ 2 / 2) * vecDot r (matVecMul (coarseBlockMatrix V b).lowerRight r)
          + volumeAverage V (scalarVariationEnergyIntegrand b v) / 2 := by
    intro t
    have h := hvar (0, t • r)
    rw [blockVecDot_fstZero_blockSwap, vecDot_smul_left, qform_fstZero_add_swap_smul] at h
    linarith only [h]
  exact abs_le_sqrt_mul_sqrt_of_forall_quadratic_le hA hquad

/-- Flux half of the direct full-dual pairing AK.HC (A.4): the cell average of the flux of a
`b`-harmonic field, tested against `p`, is bounded by the square root of the upper-left coarse
block form of `p` times the square root of the pathwise symmetric energy of the field. -/
theorem abs_vecDot_cellAverage_flux_le {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {lam Lam : ℝ} {b : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain V) (hEll : IsEllipticFieldOn lam Lam V b)
    (hvol : 0 < (volume V).toReal) (v : AHarmonicFunction b V) (p : Vec d)
    (hA : 0 ≤ vecDot p (matVecMul (coarseBlockMatrix V b).upperLeft p)) :
    |vecDot p (cellAverage V (optimizerField b v)).2|
      ≤ Real.sqrt (vecDot p (matVecMul (coarseBlockMatrix V b).upperLeft p))
        * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) := by
  have hvar := forall_blockVecDot_cellAverage_optimizerField_le hConv hEll hvol v
  have hquad : ∀ t : ℝ,
      t * vecDot p (cellAverage V (optimizerField b v)).2 ≤
        (t ^ 2 / 2) * vecDot p (matVecMul (coarseBlockMatrix V b).upperLeft p)
          + volumeAverage V (scalarVariationEnergyIntegrand b v) / 2 := by
    intro t
    have h := hvar (t • p, 0)
    rw [blockVecDot_sndZero_blockSwap, vecDot_smul_left, qform_sndZero_add_swap_smul] at h
    linarith only [h]
  exact abs_le_sqrt_mul_sqrt_of_forall_quadratic_le hA hquad

/-- The direct full-dual pairing AK.HC (A.4): the cell average of the doubled optimizer field,
paired across the two slots with a state `Y = (P, Q)`, is bounded by the sum of the square roots
of the two diagonal coarse-block forms of `Y` times the square root of the pathwise symmetric
energy of the field. -/
theorem abs_dualPairing_cellAverage_le {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {lam Lam : ℝ} {b : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain V) (hEll : IsEllipticFieldOn lam Lam V b)
    (hvol : 0 < (volume V).toReal) (v : AHarmonicFunction b V) (Y : BlockVec d)
    (hA1 : 0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
    (hA2 : 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)) :
    |vecDot Y.2 (cellAverage V (optimizerField b v)).1
        + vecDot Y.1 (cellAverage V (optimizerField b v)).2|
      ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
        * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) := by
  have hgrad := abs_vecDot_cellAverage_grad_le hConv hEll hvol v Y.2 hA2
  have hflux := abs_vecDot_cellAverage_flux_le hConv hEll hvol v Y.1 hA1
  calc
    |vecDot Y.2 (cellAverage V (optimizerField b v)).1
        + vecDot Y.1 (cellAverage V (optimizerField b v)).2|
        ≤ |vecDot Y.2 (cellAverage V (optimizerField b v)).1|
            + |vecDot Y.1 (cellAverage V (optimizerField b v)).2| := abs_add_le _ _
    _ ≤ Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2))
            * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v))
          + Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
            * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) :=
        add_le_add hgrad hflux
    _ = (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
        * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) := by ring

end

end HCPolySupport.HighContrast.Multiscale
end
