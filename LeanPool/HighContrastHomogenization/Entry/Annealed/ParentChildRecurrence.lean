/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenCongruence
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedCellFoundations
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AveragingTransport
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AnnealedBlockOrder
public import LeanPool.HighContrastHomogenization.Entry.MatrixAveraging
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.DriftAdvance
public import LeanPool.HighContrastHomogenization.Entry.PositiveGap
public import LeanPool.HighContrastHomogenization.Entry.Source.BoundedWindowFiniteness
public import LeanPool.HighContrastHomogenization.Setup.TransportObjects
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# High-contrast homogenization: Entry.Annealed.ParentChildRecurrence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Parent Child Recurrence

The parent-child recurrence for the annealed block, the result of
`p.fixed.geometry.parent.child.recurrence`: the parent cell is partitioned into aligned
children, the matrix-square-root congruence bound is transported to each of them, the
bounded-window estimate supplies the children's moment membership, and the two printed
coefficients of the recurrence are assembled.
-/

section
/-!
## The aligned children of a parent adapted cell

The paper partitions the parent adapted cell `⋄_{j+h}^q` into
`3^{dh}` aligned children `z + ⋄_j^q`, `z` ranging over the physical centres
`3^j q w ∈ 3^j q ℤ^d` whose standard-cell counterpart lies in the parent's centred cube.
`HCPoly.Entry.Annealed.AlignedSubdivision`/`MeanOrder` build this over the *index* `w : Fin d → ℤ`
(via `alignedCenterSet_finite_card`, `coarseBlock_aligned_parent_le`); this file re-indexes it
over the physical *centre* `z : Vec d` as a `Finset (Vec d)`, in the literal shape the averaging
statement's left-hand side takes after `normalizedBlock` is pulled through the finite sum.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter adaptedMean annealedBlock
  blockMatEntry_annealedBlock coarseBlock isSymmetricBlockMat_coarseBlockMatrix
  toFullBlockMat_eq_blockMatEntry)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate centeredCube
  standardCellCenter)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory Geometry Set

noncomputable section

variable {d : ℕ}

/-- The `Finset` of physical centres of the scale-`j` children inside `⋄_{j+hn}^q`:
the image, under the aligned centre map `adaptedCellCenter q j`, of the (finite) index set of
`HCPoly.Entry.Annealed.AlignedSubdivision.alignedCenterSet_finite_card`. -/
@[expose]
def alignedChildren (q : Mat d) (j : ℤ) (hn : ℕ) : Finset (Vec d) :=
  (alignedCenterSet_finite_card d j hn).1.toFinset.image (adaptedCellCenter q j)

/-- The aligned children set has the printed cardinality `3^{dh}`. -/
theorem alignedChildren_card (q : Mat d) (hq : IsUnit q) (j : ℤ) (hn : ℕ) :
    (alignedChildren q j hn).card = 3 ^ (d * hn) := by
  unfold alignedChildren
  rw [Finset.card_image_of_injective _ (adaptedCellCenter_injective q j hq)]
  let := (alignedCenterSet_finite_card d j hn).1.fintype
  rw [Set.Finite.card_toFinset, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  exact (alignedCenterSet_finite_card d j hn).2

/-- The aligned children set is nonempty: the index `w = 0` is always aligned. -/
theorem alignedChildren_nonempty (q : Mat d) (j : ℤ) (hn : ℕ) :
    (alignedChildren q j hn).Nonempty := by
  refine ⟨adaptedCellCenter q j 0, Finset.mem_image.mpr ⟨0, ?_, rfl⟩⟩
  rw [Set.Finite.mem_toFinset]
  show standardCellCenter j (0 : Fin d → ℤ) ∈ centeredCube d (j + (hn : ℤ))
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (j + (hn : ℤ)) := by positivity
  rw [Recurrence.mem_centeredCube_iff]
  intro i
  have hz : standardCellCenter j (0 : Fin d → ℤ) i = 0 := by simp [standardCellCenter]
  rw [hz]
  constructor
  · exact mul_neg_of_neg_of_pos (by norm_num : -((1 : ℝ) / 2) < 0) hpos
  · exact mul_pos (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) hpos

/-- Every aligned child's centre lies in the aligned lattice `3^j q ℤ^d`. -/
theorem alignedChildren_subset_lattice (q : Mat d) (j : ℤ) (hn : ℕ) :
    (alignedChildren q j hn : Set (Vec d)) ⊆ adaptedLatticeAtScale q j := by
  intro z hz
  simp only [alignedChildren, Finset.coe_image] at hz
  obtain ⟨w, -, rfl⟩ := hz
  exact ⟨w, rfl⟩

/-- The re-indexed pathwise aligned parent/child order: the majorant is literally the
`(Z.card)⁻¹`-weighted average of the children's coarse response over the physical `Finset`
`alignedChildren q j hn`, matching the averaging statement's left-hand side shape after
`normalizedBlock` is pulled through the finite sum. -/
theorem coarseBlock_aligned_children_le [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (hn : ℕ)
    (a : CoeffSpace d) :
    BlockMatLoewnerLE (coarseBlock (adaptedCell q (j + hn)) a)
      (ofFullBlockMat (((alignedChildren q j hn).card : ℝ)⁻¹ •
        ∑ z ∈ alignedChildren q j hn,
          toFullBlockMat (coarseBlock (adaptedCellTranslate q j z) a))) := by
  rw [alignedChildren_card q hq j hn, Nat.cast_pow, Nat.cast_ofNat, Finset.smul_sum]
  have hp := coarseBlock_aligned_parent_le q hq j hn a
  let := (alignedCenterSet_finite_card d j hn).1.fintype
  dsimp only at hp
  have hsum : ∑ z ∈ alignedChildren q j hn,
      ((3 : ℝ) ^ (d * hn))⁻¹ • toFullBlockMat (coarseBlock (adaptedCellTranslate q j z) a) =
        ∑ w : ↥{w : Fin d → ℤ | standardCellCenter j w ∈ centeredCube d (j + (hn : ℤ))},
          ((3 : ℝ) ^ (d * hn))⁻¹ • toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w.1) a) := by
    unfold alignedChildren
    rw [Finset.sum_image (fun w1 _ w2 _ h => adaptedCellCenter_injective q j hq h)]
    exact Finset.sum_subtype (alignedCenterSet_finite_card d j hn).1.toFinset
      (fun x => (alignedCenterSet_finite_card d j hn).1.mem_toFinset)
      (fun w => ((3 : ℝ) ^ (d * hn))⁻¹ • toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a))
  rw [hsum]
  exact hp

/-- Every point of the coarse response of an adapted cell is pathwise positive semidefinite
(entrywise CG block positive-definiteness, `Book.Ch02.BlockPosDef`, transported through
`posDef_toFullBlockMat`): the a.e. positive-semidefiniteness the positive-gap argument needs
of its `F`. -/
theorem coarseBlock_adaptedCell_posSemidef [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ)
    (a : CoeffSpace d) :
    (toFullBlockMat (coarseBlock (adaptedCell q j) a)).PosSemidef := by
  have hsymm : IsSymmetricBlockMat (coarseBlock (adaptedCell q j) a) :=
    isSymmetricBlockMat_coarseBlockMatrix (adaptedCell q j) (⇑a.1)
  have hpos : Book.Ch02.BlockPosDef (coarseBlock (adaptedCellTranslate q j 0) a) :=
    blockPosDef_coarseBlock_adapted q hq j 0 a
  rw [adaptedCellTranslate_zero] at hpos
  exact (posDef_toFullBlockMat hsymm hpos).posSemidef

/-- The annealed identity: every aligned child, at any generation at or above `jStar`, has the
same annealed matrix as its parent's own generation-`j` adapted mean. -/
theorem annealedBlock_alignedChildren {P : Measure (CoeffSpace d)} (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    {j : ℤ} (hj : (jStar : ℤ) ≤ j) (hn : ℕ) [NeZero d] {z : Vec d}
    (hz : z ∈ alignedChildren (Geometry.explicitRoundedGrid jStar m) j hn) :
    annealedBlock P (adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j z) =
      adaptedMean P (Geometry.explicitRoundedGrid jStar m) j := by
  simp only [alignedChildren, Finset.mem_image, Set.Finite.mem_toFinset] at hz
  obtain ⟨w, -, rfl⟩ := hz
  exact annealedBlock_adaptedCellAtCenter P hstat jStar hjStar m hm j hj w

/-- The aligned-children equal-weight average is in `L^N(S_N)`: the "bounded-window estimate
gives the required integrability" sentence of `p.fixed.geometry.parent.child.recurrence`
(`e.source.adapted.bound`), applied
to each child and combined by `Source.memLqSchatten_finset_sum`. No membership premise is added
to any consumer; this is finiteness only. -/
theorem memLqSchatten_alignedChildren_average (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (j : ℤ) (hn : ℕ) (N : ℝ) (hN : 1 ≤ N) :
    SchattenMemLp P N (fun a => ofFullBlockMat
      (((alignedChildren (Geometry.explicitRoundedGrid jStar m) j hn).card : ℝ)⁻¹ •
        ∑ z ∈ alignedChildren (Geometry.explicitRoundedGrid jStar m) j hn,
          toFullBlockMat (coarseBlock
            (adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j z) a))) :=
  by
    have h := Source.memLqSchatten_finset_sum hN
      (alignedChildren (Geometry.explicitRoundedGrid jStar m) j hn)
      (fun _ => ((alignedChildren (Geometry.explicitRoundedGrid jStar m) j hn).card : ℝ)⁻¹)
      (fun z a => coarseBlock (adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j z) a)
      (fun z _ => Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag
        jStar hjStar m hm j z N hN)
    simpa only [Finset.smul_sum] using h

/-- The entrywise expectation of the actual aligned average is the child-scale mean. -/
theorem integral_alignedChildren_average (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (j : ℤ) (hn : ℕ) (hj : (jStar : ℤ) ≤ j) :
    ofFullBlockMat (fun α β => ∫ a, blockMatEntry
      (ofFullBlockMat (((alignedChildren (explicitRoundedGrid jStar m) j hn).card : ℝ)⁻¹ •
        ∑ z ∈ alignedChildren (explicitRoundedGrid jStar m) j hn,
          toFullBlockMat (coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar m) j z) a)))
      α β ∂P) = adaptedMean P (explicitRoundedGrid jStar m) j := by
  let : NeZero d := ⟨by omega⟩
  let q := explicitRoundedGrid jStar m
  let Z := alignedChildren q j hn
  have hc (z : Vec d) := hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S
    hstat hdag jStar hjStar m hm j z
  have hcard : (Z.card : ℝ) ≠ 0 := by
    exact_mod_cast (alignedChildren_nonempty q j hn).card_pos.ne'
  rw [← ofFullBlockMat_toFullBlockMat (adaptedMean P q j)]
  congr 1
  funext α β
  have he (z : Vec d) (hz : z ∈ Z) :
      (∫ a, blockMatEntry (coarseBlock (adaptedCellTranslate q j z) a) α β ∂P) =
        blockMatEntry (adaptedMean P q j) α β := by
    rw [← blockMatEntry_annealedBlock,
      annealedBlock_alignedChildren hstat jStar hjStar m hm hj hn hz]
  change (∫ a, blockMatEntry (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
    ∑ z ∈ Z, toFullBlockMat (coarseBlock (adaptedCellTranslate q j z) a))) α β ∂P) = _
  simp only [blockMatEntry_ofFullBlockMat, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, toFullBlockMat_eq_blockMatEntry]
  rw [integral_const_mul, integral_finsetSum _ (fun z _ => hc z α β)]
  rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end

end HCPolySupport.HighContrast.Annealed
end

section
/-!
## Normalization transport

`p.fixed.geometry.parent.child.recurrence`: the transport matrix is the product of the
child mean square root and the parent mean inverse square root. Its squared
L2 operator norm is exactly the normalized mean operator norm. The sharp
Schatten congruence bound and the actual mean order give the exponential
loss bound. Both means are proved positive definite before cancellation;
no integrability, positivity, or order premise is added to the recurrence.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean matSqrt matSqrt_spec normalizedBlock)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory Geometry Set
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## Reproved matSqrt cancellation, generalized to any finite real carrier

`HCPoly.Entry.Geometry.GeometryUpdateBounds.matSqrt_mul_matSqrt_inv`/`matSqrt_inv_mul_matSqrt` are
`private` and specific to `Mat d`; the congruence identity below needs both directions at
`FullBlockMat d = Matrix (BlockCoord d) (BlockCoord d) ℝ`, a different carrier. Reproved here,
generalized to any finite index type, rather than reaching into that file's private
namespace. -/

private theorem posDef_sqrt_full {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Matrix ι ι ℝ}
    (hm : m.PosDef) : (CFC.sqrt m).PosDef :=
  Matrix.IsStrictlyPositive.posDef
    (IsStrictlyPositive.sqrt m (Matrix.isStrictlyPositive_iff_posDef.mpr hm))

private theorem cfc_sqrt_inv_full {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Matrix ι ι ℝ}
    (hm : m.PosDef) : (CFC.sqrt m)⁻¹ = CFC.sqrt m⁻¹ := by
  rw [eq_comm,
    CFC.sqrt_eq_iff _ _ hm.inv.posSemidef.nonneg
      (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg m)).inv.nonneg,
    ← sq, Matrix.inv_pow', CFC.sq_sqrt m]

/-! ## Group 3 item 1: the deterministic congruence identity -/

/-- The change-of-normalization congruence identity, for every block `X`, given both adapted
means positive definite: a deterministic matrix identity, no probabilistic hypothesis. -/
theorem normalizedBlock_transport_congr {Aj Ajh : BlockMat d}
    (hAj : (toFullBlockMat Aj).PosDef) (hAjh : (toFullBlockMat Ajh).PosDef) (X : BlockMat d) :
    toFullBlockMat (normalizedBlock X Ajh) =
      (bridgeMap Aj Ajh)ᵀ * toFullBlockMat (normalizedBlock X Aj) * bridgeMap Aj Ajh := by
  have hT : (bridgeMap Aj Ajh)ᵀ =
      matSqrt (toFullBlockMat Ajh)⁻¹ * matSqrt (toFullBlockMat Aj) := by
    unfold bridgeMap
    rw [Matrix.transpose_mul,
      ← Matrix.conjTranspose_eq_transpose_of_trivial (matSqrt (toFullBlockMat Ajh)⁻¹),
      ← Matrix.conjTranspose_eq_transpose_of_trivial (matSqrt (toFullBlockMat Aj)),
      (Multiscale.matSqrt_inv_posDef_full hAjh).isHermitian.eq,
      (matSqrt_eq_cfc_sqrt hAj.posSemidef ▸ posDef_sqrt_full hAj : (matSqrt (toFullBlockMat Aj)).PosDef).isHermitian.eq]
  rw [show toFullBlockMat (normalizedBlock X Ajh) =
      matSqrt (toFullBlockMat Ajh)⁻¹ * toFullBlockMat X * matSqrt (toFullBlockMat Ajh)⁻¹ from
    by rw [normalizedBlock, toFullBlockMat_ofFullBlockMat],
    hT,
    show toFullBlockMat (normalizedBlock X Aj) =
      matSqrt (toFullBlockMat Aj)⁻¹ * toFullBlockMat X * matSqrt (toFullBlockMat Aj)⁻¹ from
    by rw [normalizedBlock, toFullBlockMat_ofFullBlockMat],
    show bridgeMap Aj Ajh = matSqrt (toFullBlockMat Aj) * matSqrt (toFullBlockMat Ajh)⁻¹
      from rfl]
  have hassoc : matSqrt (toFullBlockMat Ajh)⁻¹ * matSqrt (toFullBlockMat Aj) *
        (matSqrt (toFullBlockMat Aj)⁻¹ * toFullBlockMat X * matSqrt (toFullBlockMat Aj)⁻¹) *
        (matSqrt (toFullBlockMat Aj) * matSqrt (toFullBlockMat Ajh)⁻¹) =
      matSqrt (toFullBlockMat Ajh)⁻¹ *
        ((matSqrt (toFullBlockMat Aj) * matSqrt (toFullBlockMat Aj)⁻¹) * toFullBlockMat X *
          (matSqrt (toFullBlockMat Aj)⁻¹ * matSqrt (toFullBlockMat Aj))) *
        matSqrt (toFullBlockMat Ajh)⁻¹ := by
    noncomm_ring
  rw [hassoc, matSqrt_mul_matSqrt_inv hAj, matSqrt_inv_mul_matSqrt hAj]
  simp only [one_mul, mul_one]

/-! ## Group 3 item 2: the operator-norm identity -/

/-- `‖B‖² = |P^q_{j,j+h}|`: the square of the transport matrix's operator norm is exactly the
operator norm of the transported normalized mean, via the C⋆-identity `‖BᵀB‖ = ‖B‖²` (an
**equality**, not merely the fallback inequality). -/
theorem transportMatrix_sq_opNorm_eq (P : Measure (CoeffSpace d)) (q : Mat d) (j h : ℤ)
    (hAj : (toFullBlockMat (adaptedMean P q j)).PosDef)
    (hAjh : (toFullBlockMat (adaptedMean P q (j + h))).PosDef) :
    ‖bridgeMap (adaptedMean P q j) (adaptedMean P q (j + h))‖ ^ 2 =
      blockOpNorm (relMean P q j (j + h)) := by
  set Aj := adaptedMean P q j
  set Ajh := adaptedMean P q (j + h)
  set B := bridgeMap Aj Ajh with hB
  have hBtB : Bᵀ * B = toFullBlockMat (relMean P q j (j + h)) := by
    have hT : Bᵀ = matSqrt (toFullBlockMat Ajh)⁻¹ * matSqrt (toFullBlockMat Aj) := by
      rw [hB]; unfold bridgeMap
      rw [Matrix.transpose_mul,
        ← Matrix.conjTranspose_eq_transpose_of_trivial (matSqrt (toFullBlockMat Ajh)⁻¹),
        ← Matrix.conjTranspose_eq_transpose_of_trivial (matSqrt (toFullBlockMat Aj)),
        (Multiscale.matSqrt_inv_posDef_full hAjh).isHermitian.eq,
      (matSqrt_eq_cfc_sqrt hAj.posSemidef ▸ posDef_sqrt_full hAj : (matSqrt (toFullBlockMat Aj)).PosDef).isHermitian.eq]
    rw [hT, hB]
    unfold bridgeMap relMean normalizedBlock
    rw [toFullBlockMat_ofFullBlockMat]
    have hassoc : matSqrt (toFullBlockMat Ajh)⁻¹ * matSqrt (toFullBlockMat Aj) *
          (matSqrt (toFullBlockMat Aj) * matSqrt (toFullBlockMat Ajh)⁻¹) =
        matSqrt (toFullBlockMat Ajh)⁻¹ *
          (matSqrt (toFullBlockMat Aj) * matSqrt (toFullBlockMat Aj)) *
          matSqrt (toFullBlockMat Ajh)⁻¹ := by
      noncomm_ring
    rw [hassoc, (matSqrt_spec hAj.posSemidef).2]
  have hnorm : ‖Bᵀ * B‖ = ‖B‖ ^ 2 := by
    have h := CStarRing.norm_star_mul_self (x := B)
    rw [show (star B : FullBlockMat d) = Bᵀ from rfl] at h
    rw [h]; ring
  rw [← hnorm, hBtB]
  rfl

/-- Change normalization using the exact operator norm of the transport matrix. -/
theorem lqSchattenNorm_normalizedBlock_congr_le {d : ℕ}
    {P : Measure (CoeffSpace d)} {N : ℝ} (hN : 1 ≤ N)
    {Aj Ak : BlockMat d} (hAj : (toFullBlockMat Aj).PosDef)
    (hAk : (toFullBlockMat Ak).PosDef) (X : CoeffSpace d → BlockMat d)
    (hX : SchattenMemLp P N (fun a => normalizedBlock (X a) Aj)) :
    lqSchattenNorm P N (fun a => normalizedBlock (X a) Ak) ≤
      ‖bridgeMap Aj Ak‖ ^ 2 * lqSchattenNorm P N (fun a => normalizedBlock (X a) Aj) := by
  have heq (a : CoeffSpace d) : normalizedBlock (X a) Ak =
      ofFullBlockMat ((bridgeMap Aj Ak)ᵀ *
        toFullBlockMat (normalizedBlock (X a) Aj) * bridgeMap Aj Ak) := by
    rw [← normalizedBlock_transport_congr hAj hAk, ofFullBlockMat_toFullBlockMat]
  simp_rw [heq]
  exact Analysis.lqSchattenNorm_congr_le hN hX _

/-- Transport between ordered actual means costs at most the exponential determinant loss. -/
theorem lqSchattenNorm_normalizedBlock_transport_le (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (j : ℤ) (hn : ℕ) (hj : (jStar : ℤ) ≤ j) {N : ℝ} (hN : 1 ≤ N)
    (X : CoeffSpace d → BlockMat d)
    (hX : SchattenMemLp P N (fun a => normalizedBlock (X a)
      (adaptedMean P (explicitRoundedGrid jStar m) j))) :
    lqSchattenNorm P N (fun a => normalizedBlock (X a)
        (adaptedMean P (explicitRoundedGrid jStar m) (j + hn))) ≤
      Real.exp (detIncrement P (explicitRoundedGrid jStar m) j (j + hn)) *
        lqSchattenNorm P N (fun a => normalizedBlock (X a)
          (adaptedMean P (explicitRoundedGrid jStar m) j)) := by
  have hAj := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm j
  have hAk := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm (j + hn)
  obtain ⟨_, _, _, hnorm, _, _⟩ := adaptedMean_order_consequences d hd P γ E Ψ K S
    hstat hdag jStar hjStar m hm j (j + hn) hj (by omega)
  have hnn : 0 ≤ lqSchattenNorm P N (fun a =>
      normalizedBlock (X a) (adaptedMean P (explicitRoundedGrid jStar m) j)) := by
    rw [(hX.lqSchattenNorm_eq_eLpNorm_toReal hN).2.2]
    exact ENNReal.toReal_nonneg
  calc
    _ ≤ ‖bridgeMap (adaptedMean P (explicitRoundedGrid jStar m) j)
        (adaptedMean P (explicitRoundedGrid jStar m) (j + hn))‖ ^ 2 *
        lqSchattenNorm P N (fun a => normalizedBlock (X a)
          (adaptedMean P (explicitRoundedGrid jStar m) j)) :=
      lqSchattenNorm_normalizedBlock_congr_le hN hAj hAk X hX
    _ ≤ _ := by
      rw [transportMatrix_sq_opNorm_eq P (explicitRoundedGrid jStar m) j hn hAj hAk]
      exact mul_le_mul_of_nonneg_right hnorm hnn

end

end HCPolySupport.HighContrast.Annealed
end

section
/-!
## The parent–child recurrence

Near `p.fixed.geometry.parent.child.recurrence`. The aligned children supply the actual average,
its expectation and order. Matrix averaging at the child normalization,
sharp normalization transport, and the positive-gap estimate give
the recurrence with the two printed coefficients. The ordered-mean
analysis supplies the full trace/determinant estimate and nonnegative loss.

All moment membership and both mean positive-definiteness proofs are derived
from the standing law. The helper with an averaging premise is discharged
by the ordinary endpoint here and by the exact averaging result.
The latter returns the very same source constant and passes
its threshold premise straight through.

-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean blockPosDef_annealedBlock blockSub
  blockTrace coarseBlock isSymmetricBlockMat_coarseBlockMatrix matSqrt normalizedBlock)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate)
namespace HCPolySupport.HighContrast.Annealed
open MeasureTheory Geometry Analysis
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
noncomputable section

variable {d : ℕ}

/-- Full coordinates preserve block subtraction. -/
theorem toFullBlockMat_blockSub_annealed (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext α β
  cases α <;> cases β <;> rfl

/-- Deterministic normalization is linear in the matrix being normalized. -/
theorem normalizedBlock_blockSub (A B R : BlockMat d) :
    normalizedBlock (blockSub A B) R =
      blockSub (normalizedBlock A R) (normalizedBlock B R) := by
  unfold normalizedBlock
  rw [toFullBlockMat_blockSub_annealed, mul_sub, sub_mul]
  rfl

/-- Centering commutes with a nonempty equal-weight full-matrix average. -/
theorem fullBlock_average_sub {ι : Type*} (Z : Finset ι) (hZ : Z.Nonempty)
    (A : ι → FullBlockMat d) (C : FullBlockMat d) :
    (Z.card : ℝ)⁻¹ • ∑ z ∈ Z, (A z - C) =
      (Z.card : ℝ)⁻¹ • ∑ z ∈ Z, A z - C := by
  have hcard : (Z.card : ℝ) ≠ 0 := by exact_mod_cast hZ.card_pos.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_sub, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- Pull normalization and centering through the actual finite average. -/
theorem normalizedBlock_average_sub {ι : Type*} (Z : Finset ι) (hZ : Z.Nonempty)
    (A : ι → BlockMat d) (C R : BlockMat d) :
    ofFullBlockMat ((Z.card : ℝ)⁻¹ •
      ∑ z ∈ Z, toFullBlockMat (normalizedBlock (blockSub (A z) C) R)) =
    normalizedBlock (blockSub
      (ofFullBlockMat ((Z.card : ℝ)⁻¹ • ∑ z ∈ Z, toFullBlockMat (A z))) C) R := by
  simp only [normalizedBlock, toFullBlockMat_ofFullBlockMat, toFullBlockMat_blockSub_annealed]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  simp_rw [Matrix.mul_sub, Matrix.sub_mul]
  exact fullBlock_average_sub Z hZ _ _

/-- Actual expectation commutes with normalization when every entry is integrable. -/
theorem integral_normalizedBlock {P : Measure (CoeffSpace d)}
    {X : CoeffSpace d → BlockMat d}
    (hX : ∀ α β, Integrable (fun a => blockMatEntry (X a) α β) P) (R : BlockMat d) :
    ofFullBlockMat (fun α β => ∫ a,
      blockMatEntry (normalizedBlock (X a) R) α β ∂P) =
    normalizedBlock (ofFullBlockMat (fun α β => ∫ a, blockMatEntry (X a) α β ∂P)) R := by
  simp only [normalizedBlock, blockMatEntry_ofFullBlockMat]
  rw [integral_fullBlock_mul hX,
    toFullBlockMat_ofFullBlockMat (fun α β => ∫ a, blockMatEntry (X a) α β ∂P)]
  rfl

/-- The parent-normalized mean trace gap is bounded by the printed exponential term. -/
theorem recurrence_gap_term_le (d : ℕ) {N Δ : ℝ} (hN : 2 ≤ N) (hΔ : 0 ≤ Δ)
    (M : BlockMat d) (hM : IsSymmetricBlockMat M)
    (hIM : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) M)
    (hnorm : blockOpNorm M ≤ Real.exp Δ)
    (htrace : blockTrace (blockSub M (Book.Ch02.blockIdentity d)) ≤ Real.exp Δ - 1) :
    2 * (1 + (d : ℝ) ^ (1 - N⁻¹)) * blockOpNorm M ^ (1 - N⁻¹) *
      blockTrace (blockSub M (Book.Ch02.blockIdentity d)) ^ N⁻¹ ≤
    2 * (1 + (d : ℝ) ^ (1 - N⁻¹)) * Real.exp ((1 - N⁻¹) * Δ) *
      (Real.exp Δ - 1) ^ N⁻¹ := by
  have hN1 : (1 : ℝ) ≤ N := (by norm_num : (1 : ℝ) ≤ 2).trans hN
  have hNi : 0 ≤ N⁻¹ := inv_nonneg.mpr (zero_le_one.trans hN1)
  have hNi1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
  have htrace0 := blockTrace_identity_sub_nonneg M hM hIM
  have hgain : 0 ≤ Real.exp Δ - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hΔ)
  have hc : 0 ≤ 2 * (1 + (d : ℝ) ^ (1 - N⁻¹)) :=
    mul_nonneg (by norm_num) (add_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hop : blockOpNorm M ^ (1 - N⁻¹) ≤ Real.exp ((1 - N⁻¹) * Δ) := by
    calc
      _ ≤ (Real.exp Δ) ^ (1 - N⁻¹) :=
        Real.rpow_le_rpow (norm_nonneg _) hnorm (sub_nonneg.mpr hNi1)
      _ = _ := by rw [← Real.exp_mul, mul_comm Δ]
  calc
    _ ≤ 2 * (1 + (d : ℝ) ^ (1 - N⁻¹)) * blockOpNorm M ^ (1 - N⁻¹) *
        (Real.exp Δ - 1) ^ N⁻¹ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow htrace0 htrace hNi)
        (mul_nonneg hc (Real.rpow_nonneg (norm_nonneg _) _))
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hop hc)
      (Real.rpow_nonneg hgain _)

/-- The aligned cardinality produces exactly the printed real-power decay. -/
theorem alignedChildren_card_decay {d : ℕ} (q : Mat d) (hq : IsUnit q) (j h : ℤ)
    (hh : 0 ≤ h) :
    ((alignedChildren q j h.toNat).card : ℝ) ^ ((1 : ℝ) / 2) =
      ((3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ)))⁻¹ := by
  rw [alignedChildren_card q hq, Nat.cast_pow, Nat.cast_ofNat,
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  rw [Nat.cast_mul]
  have hcast : (h.toNat : ℝ) = (h : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hh : (h.toNat : ℤ) = h)
  rw [hcast]
  ring

/-- Normalization preserves the block order, with a genuine positive normalizer. -/
theorem normalizedBlock_loewnerLE {A B R : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B)
    (hR : (toFullBlockMat R).PosDef) (hAB : BlockMatLoewnerLE A B) :
    BlockMatLoewnerLE (normalizedBlock A R) (normalizedBlock B R) := by
  have hs : (matSqrt (toFullBlockMat R)⁻¹).IsHermitian :=
    (Multiscale.matSqrt_inv_posDef_full hR).isHermitian
  have hst : (matSqrt (toFullBlockMat R)⁻¹)ᵀ = matSqrt (toFullBlockMat R)⁻¹ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, hs.eq]
  have ht := blockMatLoewnerLE_congr_le hA hB hAB (matSqrt (toFullBlockMat R)⁻¹)
  rw [hst] at ht
  exact ht

/-- Normalization preserves positive semidefiniteness in the block order. -/
theorem normalizedBlock_nonneg {A R : BlockMat d}
    (hA : (toFullBlockMat A).PosSemidef) (hR : (toFullBlockMat R).PosDef) :
    BlockMatLoewnerLE (ofFullBlockMat 0) (normalizedBlock A R) := by
  have hs : (matSqrt (toFullBlockMat R)⁻¹).IsHermitian :=
    (Multiscale.matSqrt_inv_posDef_full hR).isHermitian
  have hp := hA.conjTranspose_mul_mul_same (matSqrt (toFullBlockMat R)⁻¹)
  rw [hs.eq] at hp
  refine HCPolySupport.HighContrast.blockMatLoewnerLE_of_le ?_
  simp only [normalizedBlock, toFullBlockMat_ofFullBlockMat]
  exact hp.nonneg

/-- Assemble the recurrence from the actual averaging inequality on the aligned children.
The averaging input is discharged by the ordinary endpoint below and by the exact
averaging result. -/
theorem parent_child_recurrence_of_averaging (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) (hP : IsProbabilityMeasure P)
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (N : ℕ) (hN : 2 ≤ N)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (j h : ℤ) (hjgen : (jStar : ℤ) ≤ j) (hh : 1 ≤ h)
    (havg : let q := explicitRoundedGrid jStar m
      let Z := alignedChildren q j h.toNat
      ∀ (R : BlockMat d), IsSymmetricBlockMat R → Book.Ch02.BlockPosDef R →
        lqSchattenNorm P (N : ℝ) (fun a => ofFullBlockMat ((Z.card : ℝ)⁻¹ •
          ∑ z ∈ Z, toFullBlockMat (normalizedBlock
            (blockSub (coarseBlock (adaptedCellTranslate q j z) a) (adaptedMean P q j)) R))) ≤
          (N : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) / (Z.card : ℝ) ^ ((1 : ℝ) / 2) *
            lqSchattenNorm P (N : ℝ) (fun a => normalizedBlock
              (blockSub (coarseBlock (adaptedCell q j) a) (adaptedMean P q j)) R)) :
    lqSchattenNorm P (N : ℝ)
        (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar m) (j + h)) ≤
      (N : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * (1 + (2 * (d : ℝ)) ^ ((N : ℝ))⁻¹) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ)) *
            Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar m) j (j + h)) *
          lqSchattenNorm P (N : ℝ)
            (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar m) j) +
        2 * (1 + (d : ℝ) ^ (1 - ((N : ℝ))⁻¹)) *
            Real.exp
              ((1 - ((N : ℝ))⁻¹) *
                detIncrement P (Geometry.explicitRoundedGrid jStar m) j (j + h)) *
            (Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar m) j (j + h)) - 1) ^
              ((N : ℝ))⁻¹ := by
  let : IsProbabilityMeasure P := hP
  let : NeZero d := ⟨by omega⟩
  let q := explicitRoundedGrid jStar m
  let Z := alignedChildren q j h.toNat
  let Aj := adaptedMean P q j
  let Ak := adaptedMean P q (j + h)
  let G : CoeffSpace d → BlockMat d := fun a => ofFullBlockMat
    ((Z.card : ℝ)⁻¹ • ∑ z ∈ Z, toFullBlockMat (coarseBlock (adaptedCellTranslate q j z) a))
  let Fnorm : CoeffSpace d → BlockMat d := fun a =>
    normalizedBlock (coarseBlock (adaptedCell q (j + h)) a) Ak
  let Gnorm : CoeffSpace d → BlockMat d := fun a => normalizedBlock (G a) Ak
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := (by norm_num : (1 : ℝ) ≤ 2).trans hNR
  have hhn : (h.toNat : ℤ) = h := Int.toNat_of_nonneg (by omega)
  have hq : IsUnit q := isUnit_roundedGrid hj hm
  have hZne : Z.Nonempty := alignedChildren_nonempty q j h.toNat
  have hAj := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm j
  have hAk := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm (j + h)
  obtain ⟨hIM, hΔ, _, hop, htrace, _⟩ := adaptedMean_order_consequences
    d hd P γ E Ψ K S hstat hdag jStar hj m hm j (j + h) hjgen (by omega)
  have hG : SchattenMemLp P (N : ℝ) G :=
    memLqSchatten_alignedChildren_average hd P γ E Ψ K S hstat hdag
      jStar hj m hm j h.toNat N hN1
  have hAconst : SchattenMemLp P (N : ℝ) (fun _ => Aj) :=
    memLqSchatten_const P hN1 Aj (isSymmetricBlockMat_annealedBlock P _)
  have hX := Source.memLqSchatten_normalizedBlock (hG.sub hAconst hN1) hN1 Aj
  have hFraw : SchattenMemLp P (N : ℝ)
      (fun a => coarseBlock (adaptedCell q (j + h)) a) := by
    simpa only [adaptedCellTranslate_zero] using
      Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag
        jStar hj m hm (j + h) 0 N hN1
  have hFmem : SchattenMemLp P (N : ℝ) Fnorm :=
    Source.memLqSchatten_normalizedBlock hFraw hN1 Ak
  have hGmem : SchattenMemLp P (N : ℝ) Gnorm :=
    Source.memLqSchatten_normalizedBlock hG hN1 Ak
  have hAjblock : Book.Ch02.BlockPosDef Aj := by
    have hb := blockPosDef_annealedBlock
      (hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag jStar hj m hm j 0)
      (fun a => blockPosDef_coarseBlock_adapted q hq j 0 a)
    simpa only [adaptedCellTranslate_zero] using! hb
  have hV (r : ℤ) : (fun a => normalizedBlock
      (blockSub (coarseBlock (adaptedCell q r) a) (adaptedMean P q r))
      (adaptedMean P q r)) = normalizedFluctuationSelf P q r := by
    funext a
    simp only [normalizedFluctuationSelf, normalizedFluctuation, adaptedCellTranslate_zero]
  have havg' := havg Aj (isSymmetricBlockMat_annealedBlock P _) hAjblock
  change lqSchattenNorm P (N : ℝ) (fun a => ofFullBlockMat ((Z.card : ℝ)⁻¹ •
      ∑ z ∈ Z, toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (adaptedCellTranslate q j z) a) Aj) Aj))) ≤ _ at havg'
  simp_rw [normalizedBlock_average_sub Z hZne] at havg'
  rw [hV j] at havg'
  rw [alignedChildren_card_decay q hq j h (by omega)] at havg'
  simp only [div_eq_mul_inv, inv_inv] at havg'
  have htransport := lqSchattenNorm_normalizedBlock_transport_le d hd P γ E Ψ K S
    hstat hdag jStar hj m hm j h.toNat hjgen hN1 (fun a => blockSub (G a) Aj) hX
  rw [hhn] at htransport
  have hGbound := htransport.trans (mul_le_mul_of_nonneg_left havg'
    (Real.exp_pos (detIncrement P q j (j + h))).le)
  have hEF : ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (Fnorm a) α β ∂P) = Book.Ch02.blockIdentity d :=
    integral_normalizedBlock_self d hd P γ E Ψ K S hstat hdag jStar hj m hm (j + h)
  have hEG : ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (Gnorm a) α β ∂P) = relMean P q j (j + h) := by
    change ofFullBlockMat (fun α β => ∫ a, blockMatEntry (normalizedBlock (G a) Ak) α β ∂P) = _
    rw [integral_normalizedBlock (hG.integrable_entry hN1)]
    have hmean := integral_alignedChildren_average d hd P γ E Ψ K S hstat hdag
      jStar hj m hm j h.toNat hjgen
    change ofFullBlockMat (fun α β => ∫ a, blockMatEntry (G a) α β ∂P) = Aj at hmean
    rw [hmean]
    rfl
  have hFcenter : (fun a => blockSub (Fnorm a) (Book.Ch02.blockIdentity d)) =
      normalizedFluctuationSelf P q (j + h) := by
    rw [← normalizedMean_self d hd P γ E Ψ K S hstat hdag jStar hj m hm (j + h)]
    change (fun a => blockSub (normalizedBlock _ Ak) (normalizedBlock Ak Ak)) = _
    simp_rw [← normalizedBlock_blockSub]
    exact hV (j + h)
  have hGcenter : (fun a => blockSub (Gnorm a) (relMean P q j (j + h))) =
      (fun a => normalizedBlock (blockSub (G a) Aj) Ak) := by
    funext a
    exact (normalizedBlock_blockSub (G a) Aj Ak).symm
  have hFG : ∀ᵐ a ∂P, BlockMatLoewnerLE (Fnorm a) (Gnorm a) := by
    filter_upwards [hG.symmetric] with a hGa
    have hc := coarseBlock_aligned_children_le q hq j h.toNat a
    rw [hhn] at hc
    exact normalizedBlock_loewnerLE
      (isSymmetricBlockMat_coarseBlockMatrix _ (⇑a.1)) hGa hAk hc
  have hFpos : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (Fnorm a) :=
    ae_of_all P fun a => normalizedBlock_nonneg
      (coarseBlock_adaptedCell_posSemidef q hq (j + h) a) hAk
  have hGpos : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (Gnorm a) := by
    filter_upwards [hFpos, hFG] with a hFa hFGa
    intro x
    exact (hFa x).trans (hFGa x)
  have hgap := Entry.fixed_geometry_positive_gap d hd N hNR P hP
    Fnorm Gnorm hFmem hGmem hFpos hGpos hFG
  rw [hEF, hEG, hFcenter, hGcenter] at hgap
  have hM : IsSymmetricBlockMat (relMean P q j (j + h)) :=
    (toFullBlockMat_isHermitian_iff _).1 (normalizedBlock_posDef Aj Ak hAj hAk).isHermitian
  have hgain := recurrence_gap_term_le d hNR hΔ _ hM hIM hop htrace
  have hcoef : 0 ≤ 1 + (2 * (d : ℝ)) ^ ((N : ℝ))⁻¹ :=
    add_nonneg zero_le_one (Real.rpow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) _)
  refine hgap.trans ((add_le_add (mul_le_mul_of_nonneg_left hGbound hcoef) hgain).trans_eq ?_)
  dsimp only [q]
  simp only [div_eq_mul_inv]
  ac_rfl

end
end HCPolySupport.HighContrast.Annealed
end
