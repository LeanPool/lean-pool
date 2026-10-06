/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.AnnealedSharpOrder
public import LeanPool.HighContrastHomogenization.Geometry.BlockBridge
public import LeanPool.HighContrastHomogenization.Annealed.Contrast

/-!
# High-contrast homogenization: Geometry.AnnealedBlockBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed sharp order on the coarse block response

The annealed primal-adjoint order is proved on the flattened carrier, for an
abstract random positive definite doubled matrix.  The paper's own random matrix
is the variational coarse block `𝐀(U; a)` of `s.introduction`, whose average
`𝐀_bar(U)` is defined one scalar Bochner integral per entry.  This file transports
the abstract statement onto that carrier.

Two facts do the transporting.  The first is that the entrywise definition of
`𝐀_bar(U)` really is the Bochner integral of the matrix-valued map: a matrix over a
finite index type is the finite sum `∑ i, ∑ j, M i j • single i j 1` of scalar
multiples of fixed single-entry matrices, so entrywise integrability is
integrability, and the vector-valued integral is computed entrywise.  The second
is the bridge of the two block dialects, which carries the sharp involution, the
Loewner order and positive definiteness across.

The integrability of the pathwise sharp is not an extra assumption.  The
reference proof observes that the elementary bounds for the coarse block
sandwich `0 < 𝐀^♯(U) ≤ 𝐀(U)`, so the spectral norm of the sharp is dominated
by the spectral norm of the response itself and no inverse moment is needed.
What that argument still requires is measurability of the sharp, which is
supplied here from measurability of the entries of the response: the entries of
the inverse are the adjugate entries divided by the determinant, and both are
polynomial in the entries.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix
open MeasureTheory

noncomputable section

/-! ## Matrix-valued integrals from scalar entries

Everything in this section is generic: a matrix over a finite index type is a
finite sum of scalar multiples of fixed single-entry matrices, so every entrywise
hypothesis propagates to the matrix-valued map. -/

section Entries

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A matrix is the finite sum of its entries against the single-entry
matrices. -/
theorem matrix_eq_sum_smul_single (M : Matrix n n ℝ) :
    M = ∑ i : n, ∑ j : n, M i j • Matrix.single i j (1 : ℝ) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

omit [DecidableEq n] in
/-- **Entrywise integrability is integrability.**  Read through the generic
finite-product API at the coordinatewise presentation of `Matrix n n ℝ`, which
agrees with the ambient one: a matrix over a finite index type carries the same
topology and continuous extended norm as the finite product it is under the
hood, which instance search does not unfold to on its own. -/
theorem integrable_of_entries {F : Ω → Matrix n n ℝ}
    (h : ∀ i j, Integrable (fun a => F a i j) μ) : Integrable F μ := by
  have hpi : Integrable (fun a => (F a : n → n → ℝ)) μ :=
    Integrable.of_eval fun i => Integrable.of_eval fun j => h i j
  convert hpi using 1

/-- Entrywise measurability is measurability. -/
theorem aestronglyMeasurable_of_entries {F : Ω → Matrix n n ℝ}
    (h : ∀ i j, AEStronglyMeasurable (fun a => F a i j) μ) :
    AEStronglyMeasurable F μ := by
  have hEq : F = fun a => ∑ i : n, ∑ j : n, F a i j • Matrix.single i j (1 : ℝ) :=
    funext fun a => matrix_eq_sum_smul_single (F a)
  rw [hEq]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
      (h i j).smul_const (Matrix.single i j (1 : ℝ))

omit [DecidableEq n] in
/-- Entries of a product are finite sums of products of entries. -/
theorem aestronglyMeasurable_entry_mul {F G : Ω → Matrix n n ℝ}
    (hF : ∀ i j, AEStronglyMeasurable (fun a => F a i j) μ)
    (hG : ∀ i j, AEStronglyMeasurable (fun a => G a i j) μ) (i j : n) :
    AEStronglyMeasurable (fun a => (F a * G a) i j) μ := by
  simp only [Matrix.mul_apply]
  exact Finset.aestronglyMeasurable_fun_sum _ fun k _ => (hF i k).mul (hG k j)

/-- The determinant is a polynomial in the entries. -/
theorem aestronglyMeasurable_det_of_entries {F : Ω → Matrix n n ℝ}
    (h : ∀ i j, AEStronglyMeasurable (fun a => F a i j) μ) :
    AEStronglyMeasurable (fun a => (F a).det) μ := by
  simp only [Matrix.det_apply']
  exact Finset.aestronglyMeasurable_fun_sum _ fun σ _ =>
    aestronglyMeasurable_const.mul
      (Finset.aestronglyMeasurable_fun_prod _ fun i _ => h (σ i) i)

/-- Each adjugate entry is a determinant of a matrix whose entries are entries of
the original one and constants. -/
theorem aestronglyMeasurable_adjugate_of_entries {F : Ω → Matrix n n ℝ}
    (h : ∀ i j, AEStronglyMeasurable (fun a => F a i j) μ) (i j : n) :
    AEStronglyMeasurable (fun a => (F a).adjugate i j) μ := by
  simp only [Matrix.adjugate_apply]
  refine aestronglyMeasurable_det_of_entries fun p q => ?_
  simp only [Matrix.updateRow_apply]
  by_cases hpj : p = j
  · simp only [ite_eq_left hpj]
    exact aestronglyMeasurable_const
  · simp only [ite_eq_right hpj]
    exact h p q

/-- **The entries of the inverse are measurable** as soon as the entries are:
they are the adjugate entries divided by the determinant, and division on the
reals is measurable even at zero. -/
theorem aestronglyMeasurable_inv_of_entries {F : Ω → Matrix n n ℝ}
    (h : ∀ i j, AEStronglyMeasurable (fun a => F a i j) μ) (i j : n) :
    AEStronglyMeasurable (fun a => (F a)⁻¹ i j) μ := by
  have hdet : AEStronglyMeasurable (fun a => ((F a).det)⁻¹) μ :=
    aestronglyMeasurable_iff_aemeasurable.mpr
      (aestronglyMeasurable_det_of_entries h).aemeasurable.inv
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact hdet.mul (aestronglyMeasurable_adjugate_of_entries h i j)

/-- A two-sided constant conjugate of the inverse is measurable. -/
theorem aestronglyMeasurable_conj_inv_of_entries (L R : Matrix n n ℝ)
    {F : Ω → Matrix n n ℝ} (h : ∀ i j, AEStronglyMeasurable (fun a => F a i j) μ) :
    AEStronglyMeasurable (fun a => L * (F a)⁻¹ * R) μ := by
  have hL : ∀ i j, AEStronglyMeasurable (fun _ : Ω => L i j) μ :=
    fun _ _ => aestronglyMeasurable_const
  have hR : ∀ i j, AEStronglyMeasurable (fun _ : Ω => R i j) μ :=
    fun _ _ => aestronglyMeasurable_const
  have hinv : ∀ i j, AEStronglyMeasurable (fun a => (F a)⁻¹ i j) μ :=
    aestronglyMeasurable_inv_of_entries h
  have hLinv : ∀ i j, AEStronglyMeasurable (fun a => (L * (F a)⁻¹) i j) μ :=
    aestronglyMeasurable_entry_mul (F := fun _ => L) (G := fun a => (F a)⁻¹) hL hinv
  exact aestronglyMeasurable_of_entries
    (aestronglyMeasurable_entry_mul (F := fun a => L * (F a)⁻¹) (G := fun _ => R) hLinv hR)

end Entries

/-! ## The structural sharp of a symmetric positive block -/

variable {d : ℕ}

/-- The sharp of a symmetric positive definite doubled block is symmetric: on the
flattened carrier it is positive definite, hence Hermitian. -/
theorem isSymmetricBlockMat_blockSharp {H : BlockMat d} (hsymm : IsSymmetricBlockMat H)
    (hpd : Book.Ch02.BlockPosDef H) : IsSymmetricBlockMat (blockSharp H) := by
  have hsymmFull : (toFullBlockMat (blockSharp H)).IsSymm := by
    rw [toFullBlockMat_blockSharp]
    exact isSymm_of_isHermitian
      (posDef_fullBlockSharp (posDef_toFullBlockMat hsymm hpd)).isHermitian
  intro p q
  rw [blockMatEntry_eq_toFullBlockMat, blockMatEntry_eq_toFullBlockMat]
  exact hsymmFull.apply q p

/-- The pathwise block order of the coarse block, transported to the flattened
carrier. -/
theorem fullBlockSharp_le_of_blockMatLoewnerLE {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpd : Book.Ch02.BlockPosDef H)
    (h : BlockMatLoewnerLE (blockSharp H) H) :
    fullBlockSharp (toFullBlockMat H) ≤ toFullBlockMat H := by
  rw [← toFullBlockMat_blockSharp]
  exact le_of_blockMatLoewnerLE (isSymmetricBlockMat_blockSharp hsymm hpd) hsymm h

/-- The diagonal entries of a Loewner-ordered pair of doubled blocks inherit the
order. -/
theorem apply_le_apply_of_le {M N : FullBlockMat d} (h : M ≤ N) (p : BlockCoord d) :
    M p p ≤ N p p := by
  have hnn : 0 ≤ (N - M) p p := (Matrix.le_iff.mp h).diag_nonneg
  rw [Matrix.sub_apply] at hnn
  linarith only [hnn]

/-- **A positive semidefinite doubled block is entrywise dominated by half the
sum of its diagonal entries.**  The Cauchy-Schwarz inequality for the quadratic
form the matrix defines, read off its `2 × 2` principal minor. -/
theorem abs_apply_le_half_add_diag {M : FullBlockMat d} (hM : M.PosSemidef)
    (p q : BlockCoord d) : |M p q| ≤ (M p p + M q q) / 2 := by
  have hpp : 0 ≤ M p p := hM.diag_nonneg
  have hqq : 0 ≤ M q q := hM.diag_nonneg
  have hsymm : M q p = M p q := by simpa using hM.isHermitian.apply p q
  have hdet : 0 ≤ (M.submatrix ![p, q] ![p, q]).det := (hM.submatrix ![p, q]).det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  rw [hsymm] at hdet
  refine abs_le_of_sq_le_sq ?_ (by linarith only [hpp, hqq])
  nlinarith [hdet, sq_nonneg (M p p - M q q)]

/-! ## The annealed block is the Bochner integral of the response -/

variable {P : Measure (CoeffSpace d)} {U : Set (Vec d)}

/-- The coarse block response is symmetric at every sample. -/
theorem isSymmetricBlockMat_coarseBlock (U : Set (Vec d)) (a : CoeffSpace d) :
    IsSymmetricBlockMat (coarseBlock U a) :=
  isSymmetricBlockMat_coarseBlockMatrix U _

/-- **The flattened coarse response is Bochner integrable** as soon as its
entries are, which is what `HasIntegrableCoarseBlock` records. -/
theorem integrable_toFullBlockMat (hint : HasIntegrableCoarseBlock P U) :
    Integrable (fun a => toFullBlockMat (coarseBlock U a)) P := by
  refine integrable_of_entries fun p q => ?_
  simpa only [toFullBlockMat_eq_blockMatEntry] using hint p q

/-- **The entrywise annealed block is the Bochner integral** of the flattened
coarse response.  This is the identity that lets the abstract form of the
annealed primal-adjoint order be read on the paper's own carrier. -/
theorem toFullBlockMat_annealedBlock (hint : HasIntegrableCoarseBlock P U) :
    toFullBlockMat (annealedBlock P U) = ∫ a, toFullBlockMat (coarseBlock U a) ∂P := by
  ext p q
  rw [toFullBlockMat_eq_blockMatEntry, blockMatEntry_annealedBlock,
    entry_integral (integrable_toFullBlockMat hint) p q]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a =>
    (toFullBlockMat_eq_blockMatEntry (coarseBlock U a) p q).symm)

/-- **The pathwise sharp is integrable**, with no assumption beyond the ones the
reference text already makes.  The elementary bounds for the coarse block
sandwich the sharp between zero and the response,
so its spectral norm is dominated by that of the response; measurability comes
from measurability of the entries of the response, which integrability
supplies. -/
theorem integrable_fullBlockSharp_toFullBlockMat (hint : HasIntegrableCoarseBlock P U)
    (hpos : ∀ a, Book.Ch02.BlockPosDef (coarseBlock U a))
    (hsharp : ∀ a, BlockMatLoewnerLE (blockSharp (coarseBlock U a)) (coarseBlock U a)) :
    Integrable (fun a => fullBlockSharp (toFullBlockMat (coarseBlock U a))) P := by
  have hentry : ∀ p q,
      AEStronglyMeasurable (fun a => toFullBlockMat (coarseBlock U a) p q) P := by
    intro p q
    simpa only [toFullBlockMat_eq_blockMatEntry] using (hint p q).aestronglyMeasurable
  have hrefl : ∀ p q : BlockCoord d,
      AEStronglyMeasurable (fun _ : CoeffSpace d => fullBlockRefl d p q) P :=
    fun _ _ => aestronglyMeasurable_const
  have hinv : ∀ p q : BlockCoord d,
      AEStronglyMeasurable (fun a => (toFullBlockMat (coarseBlock U a))⁻¹ p q) P :=
    aestronglyMeasurable_inv_of_entries hentry
  have hLinv : ∀ p q : BlockCoord d,
      AEStronglyMeasurable
        (fun a => (fullBlockRefl d * (toFullBlockMat (coarseBlock U a))⁻¹) p q) P :=
    aestronglyMeasurable_entry_mul (F := fun _ => fullBlockRefl d)
      (G := fun a => (toFullBlockMat (coarseBlock U a))⁻¹) hrefl hinv
  have hsharpMeas : ∀ p q : BlockCoord d,
      AEStronglyMeasurable
        (fun a => fullBlockSharp (toFullBlockMat (coarseBlock U a)) p q) P := by
    simp only [fullBlockSharp]
    exact aestronglyMeasurable_entry_mul
      (F := fun a => fullBlockRefl d * (toFullBlockMat (coarseBlock U a))⁻¹)
      (G := fun _ => fullBlockRefl d) hLinv hrefl
  -- The entrywise route around the ambient `FullBlockMat d` norm: the pathwise
  -- sandwich `0 ≤ sharp ≤ response` bounds each entry of the sharp by half the
  -- sum of two diagonal entries of the response, which `hint` makes integrable,
  -- so no combinator ever has to compare two `ContinuousENorm` instances on the
  -- matrix type itself.
  refine integrable_of_entries fun p q => ?_
  have hg : Integrable
      (fun a => (toFullBlockMat (coarseBlock U a) p p +
        toFullBlockMat (coarseBlock U a) q q) / 2) P := by
    have h1 : Integrable (fun a => toFullBlockMat (coarseBlock U a) p p) P := by
      simpa only [toFullBlockMat_eq_blockMatEntry] using hint p p
    have h2 : Integrable (fun a => toFullBlockMat (coarseBlock U a) q q) P := by
      simpa only [toFullBlockMat_eq_blockMatEntry] using hint q q
    exact (h1.add h2).div_const 2
  refine Integrable.mono' hg (hsharpMeas p q) (.of_forall fun a => ?_)
  rw [Real.norm_eq_abs]
  have hpd : (toFullBlockMat (coarseBlock U a)).PosDef :=
    posDef_toFullBlockMat (isSymmetricBlockMat_coarseBlock U a) (hpos a)
  have hle : fullBlockSharp (toFullBlockMat (coarseBlock U a)) ≤
      toFullBlockMat (coarseBlock U a) :=
    fullBlockSharp_le_of_blockMatLoewnerLE (isSymmetricBlockMat_coarseBlock U a)
      (hpos a) (hsharp a)
  have hbound := abs_apply_le_half_add_diag (posDef_fullBlockSharp hpd).posSemidef p q
  have hpp := apply_le_apply_of_le hle p
  have hqq := apply_le_apply_of_le hle q
  calc |fullBlockSharp (toFullBlockMat (coarseBlock U a)) p q|
      ≤ (fullBlockSharp (toFullBlockMat (coarseBlock U a)) p p +
          fullBlockSharp (toFullBlockMat (coarseBlock U a)) q q) / 2 := hbound
    _ ≤ (toFullBlockMat (coarseBlock U a) p p + toFullBlockMat (coarseBlock U a) q q) / 2 := by
        linarith only [hpp, hqq]

/-- **The annealed primal-adjoint order**, on the coarse block of the paper: the
annealed block dominates its own sharp.

The two hypotheses on the sample are properties of the variational coarse block
that `s.introduction` takes from HC, and are not proved in this repository:
`hpos` is positive definiteness of the coarse response along every realization,
and `hsharp` is its pathwise block order.  The remaining
hypothesis `hint` is the printed integrability assumption `E|𝐀(U)| < ∞`.
Symmetry of the response and of the annealed block, positive definiteness of the
annealed block, and integrability of the pathwise sharp are all consequences and
are not assumed. -/
theorem blockSharp_annealedBlock_le [IsProbabilityMeasure P]
    (hint : HasIntegrableCoarseBlock P U)
    (hpos : ∀ a, Book.Ch02.BlockPosDef (coarseBlock U a))
    (hsharp : ∀ a, BlockMatLoewnerLE (blockSharp (coarseBlock U a)) (coarseBlock U a)) :
    BlockMatLoewnerLE (blockSharp (annealedBlock P U)) (annealedBlock P U) := by
  have hmean : toFullBlockMat (annealedBlock P U) =
      ∫ a, toFullBlockMat (coarseBlock U a) ∂P := toFullBlockMat_annealedBlock hint
  have hEpos : (toFullBlockMat (annealedBlock P U)).PosDef :=
    posDef_toFullBlockMat (isSymmetricBlockMat_annealedBlock P U)
      (blockPosDef_annealedBlock hint hpos)
  have hkey := fullBlockSharp_integral_le_integral (μ := P)
    (A := fun a => toFullBlockMat (coarseBlock U a))
    (fun a => posDef_toFullBlockMat (isSymmetricBlockMat_coarseBlock U a) (hpos a))
    (fun a => fullBlockSharp_le_of_blockMatLoewnerLE (isSymmetricBlockMat_coarseBlock U a)
      (hpos a) (hsharp a))
    (integrable_toFullBlockMat hint)
    (integrable_fullBlockSharp_toFullBlockMat hint hpos hsharp)
    (by rw [← hmean]; exact hEpos)
  rw [← hmean] at hkey
  refine blockMatLoewnerLE_of_le ?_
  rwa [toFullBlockMat_blockSharp]

end

end HighContrast
end HCPolySupport
