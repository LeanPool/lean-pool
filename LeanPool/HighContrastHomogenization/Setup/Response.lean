/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.Geometry
public import LeanPool.HighContrastHomogenization.Setup.LocalSigmaFields
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockMatrixProperties
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.CoarseBounds

/-!
# High-contrast homogenization: Setup.Response

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coarse block response and the annealed block

The coarse block response `𝐀(U; a)` taken from HC is CoarseGraining's canonical
variational coarse block matrix of the sample field.
This file fixes it, its annealed expectation, the intrinsic annealed contrast
`Θ_m` of `e.Theta.m`, and the two well-formedness predicates the
annealed block needs; and it records the facts that make the encoding honest:
the response depends only on the almost everywhere class of the field, its
entries are the variational quantities, it is symmetric, and its diagonal
entries and basis-sum quadratic forms are nonnegative.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The coarse response -/

/-- The coarse block response `𝐀(U; a)` of the paper
(the variational definition of the coarse block), encoded by CoarseGraining's canonical
variational coarse block matrix of the sample field. -/
@[expose]
def coarseBlock (U : Set (Vec d)) (a : CoeffSpace d) : BlockMat d :=
  coarseBlockMatrix U ⇑a.1

/-- The deterministic annealed block `𝐀_bar(U) = E[𝐀(U; ·)]`, entrywise. -/
@[expose]
def annealedBlock (P : Measure (CoeffSpace d)) (U : Set (Vec d)) : BlockMat d :=
  { upperLeft := Matrix.of fun i j => ∫ a, (coarseBlock U a).upperLeft i j ∂P
    upperRight := Matrix.of fun i j => ∫ a, (coarseBlock U a).upperRight i j ∂P
    lowerLeft := Matrix.of fun i j => ∫ a, (coarseBlock U a).lowerLeft i j ∂P
    lowerRight := Matrix.of fun i j => ∫ a, (coarseBlock U a).lowerRight i j ∂P }

/-- Integrability of the coarse response over the law: every entry of
`𝐀(U; ·)` is `P`-integrable, so that `annealedBlock P U` is the expectation
`E[𝐀(U; ·)]` of `e.Theta.m`. -/
@[expose]
def HasIntegrableCoarseBlock (P : Measure (CoeffSpace d)) (U : Set (Vec d)) :
    Prop :=
  ∀ α β : BlockCoord d,
    Integrable (fun a => blockMatEntry (coarseBlock U a) α β) P

/-- Measurability of the coarse response over the law: every entry of
`𝐀(U; ·)` is almost surely strongly measurable for the law. -/
@[expose]
def HasMeasurableCoarseBlock (P : Measure (CoeffSpace d)) (U : Set (Vec d)) :
    Prop :=
  ∀ α β : BlockCoord d,
    AEStronglyMeasurable (fun a => blockMatEntry (coarseBlock U a) α β) P

/-- The Euclidean annealed contrast `Θ_m` (`e.Theta.m`): the
intrinsic contrast of the annealed block of the centered cube `□_m`. -/
@[expose]
def annealedContrast (P : Measure (CoeffSpace d)) (m : ℤ) : ℝ :=
  blockContrast (annealedBlock P (centeredCube d m))

/-! ## The response depends only on the almost everywhere class -/

/-- The coarse response only sees the almost everywhere class of the field: its
value at any representative of the sample is the same. -/
theorem coarseBlock_eq_of_ae_eq {U : Set (Vec d)} (a : CoeffSpace d)
    {f : CoeffField d} (hf : (⇑a.1 : Vec d → Mat d) =ᵐ[volume] f) :
    coarseBlock U a = coarseBlockMatrix U f :=
  coarseBlockMatrix_congr_of_ae_eq (ae_restrict_of_ae hf)

/-- The variational quantity only sees the almost everywhere class of the
field. -/
theorem Mu_congr_ae {U : Set (Vec d)} {f h : CoeffField d}
    (hfh : f =ᵐ[volume] h) (Q : BlockVec d) : Mu U Q f = Mu U Q h :=
  Mu_congr_of_ae_eq (ae_restrict_of_ae hfh) Q

/-! ## Entries, symmetry, nonnegativity -/

/-- The entries of the coarse block response, in terms of the variational
quantity. -/
theorem blockMatEntry_coarseBlockMatrix (U : Set (Vec d)) (a : CoeffField d)
    (α β : BlockCoord d) :
    blockMatEntry (coarseBlockMatrix U a) α β =
      if α = β then 2 * Mu U (blockBasis α) a
      else
        Mu U (blockBasis α + blockBasis β) a - Mu U (blockBasis α) a -
          Mu U (blockBasis β) a := by
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simpa [blockMatEntry, blockBasis, Sum.inl.injEq] using
            coarseBlockMatrix_upperLeft_apply U a i j
      | inr j =>
          simpa [blockMatEntry, blockBasis] using
            coarseBlockMatrix_upperRight_apply U a i j
  | inr i =>
      cases β with
      | inl j =>
          simpa [blockMatEntry, blockBasis] using
            coarseBlockMatrix_lowerLeft_apply U a i j
      | inr j =>
          simpa [blockMatEntry, blockBasis, Sum.inr.injEq] using
            coarseBlockMatrix_lowerRight_apply U a i j

/-- The coarse block response is a symmetric doubled matrix. -/
theorem isSymmetricBlockMat_coarseBlockMatrix (U : Set (Vec d)) (a : CoeffField d) :
    IsSymmetricBlockMat (coarseBlockMatrix U a) := by
  intro α β
  rw [blockMatEntry_coarseBlockMatrix, blockMatEntry_coarseBlockMatrix]
  by_cases h : α = β
  · rw [h]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), add_comm (blockBasis α) (blockBasis β)]
    ring

/-- On the coefficient space the variational quantity of the coarse block
problem is nonnegative: every admissible competitor has nonnegative energy, so
the infimum is nonnegative even where the Bochner integral is a junk value. -/
theorem zero_le_Mu_coeffSpace (U : Set (Vec d)) (Q : BlockVec d) (a : CoeffSpace d) :
    0 ≤ Mu U Q (⇑a.1) := by
  refine le_Mu_of_forall_isBlockMuAdmissible ?_
  intro X _
  have hell := a.2.ae_exists_isEllipticMatrix
  have hnn : (0 : ℝ) ≤ ∫ x in U, blockEnergyDensity (⇑a.1) X x ∂volume := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_of_ae hell] with x hx
    obtain ⟨lam, Lam, -, -, hx⟩ := hx
    have h := blockMatrixOfCoeff_quadratic_nonneg hx (X.eval x)
    have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) *
        blockVecDot (X.eval x)
          (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : Vec d → Mat d) x)) (X.eval x)) := by
      positivity
    simpa [blockEnergyDensity, blockCoeffField] using h2
  have hvol : (0 : ℝ) ≤ (volume U).toReal⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
  simpa [volumeAverage] using mul_nonneg hvol hnn

/-- Diagonal entries of the coarse response are nonnegative. -/
theorem zero_le_blockMatEntry_coarseBlock_diag (U : Set (Vec d)) (a : CoeffSpace d)
    (γ : BlockCoord d) : 0 ≤ blockMatEntry (coarseBlock U a) γ γ := by
  rw [coarseBlock, blockMatEntry_coarseBlockMatrix, ite_eq_left rfl]
  have := zero_le_Mu_coeffSpace U (blockBasis γ) a
  linarith only [this]

/-- The doubled quadratic form of the coarse response is nonnegative on the sums
of two basis vectors, these being the vectors that control its entries. -/
theorem zero_le_blockVecDot_coarseBlock_blockBasis_add (U : Set (Vec d))
    (a : CoeffSpace d) (α β : BlockCoord d) :
    0 ≤ blockVecDot (blockBasis α + blockBasis β)
      (blockMatVecMul (coarseBlock U a) (blockBasis α + blockBasis β)) := by
  rw [blockBasis_sum_pairing]
  by_cases h : α = β
  · subst h
    have h1 := zero_le_blockMatEntry_coarseBlock_diag U a α
    linarith only [h1]
  · rw [coarseBlock] at *
    rw [blockMatEntry_coarseBlockMatrix, blockMatEntry_coarseBlockMatrix,
      blockMatEntry_coarseBlockMatrix, blockMatEntry_coarseBlockMatrix,
      ite_eq_left rfl, ite_eq_left rfl, ite_eq_right h, ite_eq_right (Ne.symm h),
      add_comm (blockBasis β) (blockBasis α)]
    have := zero_le_Mu_coeffSpace U (blockBasis α + blockBasis β) a
    linarith only [this]

/-! ## The annealed block is the entrywise expectation -/

/-- Entries of the annealed block are the expectations of the entries of the
coarse response. -/
theorem blockMatEntry_annealedBlock (P : Measure (CoeffSpace d)) (U : Set (Vec d))
    (α β : BlockCoord d) :
    blockMatEntry (annealedBlock P U) α β =
      ∫ a, blockMatEntry (coarseBlock U a) α β ∂P := by
  cases α <;> cases β <;> rfl

/-- **The annealed quadratic form is the expectation of the sample quadratic
form**, at every doubled vector, whenever the coarse response is integrable over
the law.  This is the identity that pins `annealedBlock` to `E[𝐀(U; ·)]`. -/
theorem blockVecDot_blockMatVecMul_annealedBlock
    {P : Measure (CoeffSpace d)} {U : Set (Vec d)}
    (hint : HasIntegrableCoarseBlock P U) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (annealedBlock P U) X) =
      ∫ a, blockVecDot X (blockMatVecMul (coarseBlock U a) X) ∂P := by
  have hterm : ∀ α β : BlockCoord d,
      Integrable (fun a => toFullBlockVec X α *
        (blockMatEntry (coarseBlock U a) α β * toFullBlockVec X β)) P :=
    fun α β => ((hint α β).mul_const (toFullBlockVec X β)).const_mul _
  have hrow : ∀ α : BlockCoord d,
      Integrable (fun a => ∑ β : BlockCoord d, toFullBlockVec X α *
        (blockMatEntry (coarseBlock U a) α β * toFullBlockVec X β)) P :=
    fun α => integrable_finsetSum _ fun β _ => hterm α β
  calc blockVecDot X (blockMatVecMul (annealedBlock P U) X)
      = ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          toFullBlockVec X α *
            ((∫ a, blockMatEntry (coarseBlock U a) α β ∂P) * toFullBlockVec X β) := by
        rw [blockVecDot_blockMatVecMul_eq_sum]
        simp only [blockMatEntry_annealedBlock]
    _ = ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          ∫ a, toFullBlockVec X α *
            (blockMatEntry (coarseBlock U a) α β * toFullBlockVec X β) ∂P := by
        refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
        rw [integral_const_mul, integral_mul_const]
    _ = ∫ a, ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          toFullBlockVec X α *
            (blockMatEntry (coarseBlock U a) α β * toFullBlockVec X β) ∂P := by
        rw [integral_finsetSum _ fun α _ => hrow α]
        exact Finset.sum_congr rfl fun α _ =>
          (integral_finsetSum _ fun β _ => hterm α β).symm
    _ = ∫ a, blockVecDot X (blockMatVecMul (coarseBlock U a) X) ∂P :=
        integral_congr_ae (_root_.Filter.Eventually.of_forall fun a =>
          (blockVecDot_blockMatVecMul_eq_sum (coarseBlock U a) X).symm)

/-- **The positivity of the annealed block.**  The expectation of an integrable
family of positive definite coarse responses is positive definite: this is the
well-formedness that `e.Theta.m` presupposes for `Θ_m`. -/
theorem blockPosDef_annealedBlock
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {U : Set (Vec d)}
    (hint : HasIntegrableCoarseBlock P U)
    (hpos : ∀ a : CoeffSpace d, Book.Ch02.BlockPosDef (coarseBlock U a)) :
    Book.Ch02.BlockPosDef (annealedBlock P U) := by
  intro X hX
  rw [blockVecDot_blockMatVecMul_annealedBlock hint]
  set f : CoeffSpace d → ℝ :=
    fun a => blockVecDot X (blockMatVecMul (coarseBlock U a) X) with hf
  have hfpos : ∀ a, 0 < f a := fun a => hpos a X hX
  have hfint : Integrable f P := by
    have hterm : ∀ α β : BlockCoord d,
        Integrable (fun a => toFullBlockVec X α *
          (blockMatEntry (coarseBlock U a) α β * toFullBlockVec X β)) P :=
      fun α β => ((hint α β).mul_const (toFullBlockVec X β)).const_mul _
    have hsum := integrable_finsetSum (μ := P) Finset.univ
      fun α (_ : α ∈ (Finset.univ : Finset (BlockCoord d))) =>
        integrable_finsetSum (μ := P) Finset.univ fun β _ => hterm α β
    refine hsum.congr (_root_.Filter.Eventually.of_forall fun a => ?_)
    rw [hf]
    exact (blockVecDot_blockMatVecMul_eq_sum _ X).symm
  have hsupp : Function.support f = Set.univ :=
    Set.eq_univ_of_forall fun a => ne_of_gt (hfpos a)
  refine (integral_pos_iff_support_of_nonneg_ae
    (_root_.Filter.Eventually.of_forall fun a => (hfpos a).le) hfint).2 ?_
  rw [hsupp]
  simp [measure_univ]

end

end HighContrast
end HCPolySupport
