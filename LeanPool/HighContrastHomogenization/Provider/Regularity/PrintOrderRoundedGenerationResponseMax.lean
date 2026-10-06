/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationGeometry

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedGenerationResponseMax

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Spatial response rows at a selected rounded generation

The physical doubled response is maximized on cells of one admissible rounded
grid.  Its complete depth row is controlled by the same normalized-root weak
error used by the quantitative certificate.
-/

namespace HCPolySupport
namespace HighContrast
open scoped BigOperators Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The physical doubled response on one cell of a selected rounded grid,
maximized over normalized primal and dual loads. -/
@[expose]
def roundedNormalizedDoubledResponseMaxAtGeneration [NeZero d]
    (l : ℤ) (a : CoeffSpace d) (abar : Mat d)
    (_hS : (symmPart abar).PosDef) (k : ℤ) (w : Fin d → ℤ) : ℝ :=
  sSup {r : ℝ | ∃ e : FullBlockVec d, ∃ P Q : BlockVec d,
    Book.Ch02.fullBlockVecNormSq e = 1 ∧
      normalizedReferencePrimalLoad abar P = ofFullBlockVec e ∧
      normalizedReferenceDualLoad abar Q = ofFullBlockVec e ∧
      r = Transport.coeffSpaceDoubledResponse
        (adaptedCellAt (roundedGrid l (symmPart abar)) k w) a P Q}

private theorem constantFullBlockMatrixSqrt_one [NeZero d] :
    Book.Ch02.constantFullBlockMatrixSqrt (1 : Mat d) = 1 := by
  have hone : (1 : Mat d) = scalarMatrix (d := d) 1 := by
    ext i j
    simp [scalarMatrix, Matrix.one_apply]
  have hblock : Book.Ch02.constantBlockMatrix (1 : Mat d) =
      Book.Ch02.blockIdentity d := by
    rw [hone, Book.Ch02.constantBlockMatrix_scalarMatrix one_pos]
    apply blockMat_ext <;>
      simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, scalarMatrix]
  unfold Book.Ch02.constantFullBlockMatrixSqrt
  rw [show Book.Ch02.constantFullBlockMatrix (1 : Mat d) = 1 by
    unfold Book.Ch02.constantFullBlockMatrix
    rw [hblock]
    exact toFullBlockMat_blockIdentity]
  exact CFC.sqrt_one

private theorem normalizedRootCell_response_le_of_loads [NeZero d]
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (t : ℤ)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ R : TriadicCube d,
      (aRef.coeffOn R).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain
              (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField)
    (e : FullBlockVec d) (he : Book.Ch02.fullBlockVecNormSq e = 1)
    (P Q : BlockVec d)
    (hP : normalizedReferencePrimalLoad abar P = ofFullBlockVec e)
    (hQ : normalizedReferenceDualLoad abar Q = ofFullBlockVec e)
    (k : ℤ) (w : Fin d → ℤ) :
    Book.Ch02.doubledResponseJ
        (Response.adaptedDomainAt (normalizedRoot_posDef_of_posDef hS) k w)
        (a.coeffOn
          (Response.adaptedDomainAt (normalizedRoot_posDef_of_posDef hS) k w)) P Q ≤
      Book.Ch02.normalizedBlockResponseMax
        (translateCube w (originCube d k)) aRef (1 : Mat d) := by
  let X : BlockVec d := ofFullBlockVec e
  let R : TriadicCube d := translateCube w (originCube d k)
  have hcov := doubledResponseJ_normalizedReferenceCell
    a abar hS t k w aRef haRef P Q
  rw [hP, hQ] at hcov
  have hloadInv :
      ofFullBlockVec
          (Matrix.mulVec
            (Book.Ch02.constantFullBlockMatrixInvSqrt (1 : Mat d)) e) = X := by
    simp only [Book.Ch02.constantFullBlockMatrixInvSqrt,
      constantFullBlockMatrixSqrt_one, inv_one, Matrix.one_mulVec, X]
  have hloadSqrt :
      ofFullBlockVec
          (Matrix.mulVec
            (Book.Ch02.constantFullBlockMatrixSqrt (1 : Mat d)) e) = X := by
    simp only [constantFullBlockMatrixSqrt_one, Matrix.one_mulVec, X]
  have hmem :
      Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R)
          (aRef.coeffOn R) X X ∈
        Book.Ch02.normalizedBlockResponseValueSet R aRef (1 : Mat d) := by
    refine ⟨e, he, ?_⟩
    rw [hloadInv, hloadSqrt]
  have hRself : R ∈ descendantsAtScale R R.scale := by
    simp only [descendantsAtScale_self, Finset.mem_singleton]
  have hbdd : BddAbove
      (Book.Ch02.normalizedBlockResponseValueSet R aRef (1 : Mat d)) :=
    Book.Ch02.normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
      aRef (1 : Mat d) hRself
  calc
    Book.Ch02.doubledResponseJ
        (Response.adaptedDomainAt (normalizedRoot_posDef_of_posDef hS) k w)
        (a.coeffOn
          (Response.adaptedDomainAt (normalizedRoot_posDef_of_posDef hS) k w)) P Q =
        Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R)
          (aRef.coeffOn R) X X := by
            simpa only [R, X] using hcov.symm
    _ ≤ Book.Ch02.normalizedBlockResponseMax R aRef (1 : Mat d) := by
      unfold Book.Ch02.normalizedBlockResponseMax
      exact le_csSup hbdd hmem

private theorem roundedResponseValueSetAtGeneration_nonempty [NeZero d]
    {l : ℤ}
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (t : ℤ)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ R : TriadicCube d,
      (aRef.coeffOn R).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain
              (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField)
    (k : ℤ) (w : Fin d → ℤ) :
    {r : ℝ | ∃ e : FullBlockVec d, ∃ P Q : BlockVec d,
      Book.Ch02.fullBlockVecNormSq e = 1 ∧
        normalizedReferencePrimalLoad abar P = ofFullBlockVec e ∧
        normalizedReferenceDualLoad abar Q = ofFullBlockVec e ∧
        r = Transport.coeffSpaceDoubledResponse
          (adaptedCellAt (roundedGrid l (symmPart abar)) k w) a P Q}.Nonempty := by
  obtain ⟨_, e, he, _⟩ :=
    Book.Ch02.normalizedBlockResponseValueSet_nonempty
      (originCube d k) aRef (1 : Mat d)
  obtain ⟨P, Q, hP, hQ, _⟩ :=
    exists_normalizedRootCell_doubledResponseJ_le_normalizedBlockResponseMax
      a abar hS t aRef haRef e he
  exact ⟨Transport.coeffSpaceDoubledResponse
      (adaptedCellAt (roundedGrid l (symmPart abar)) k w) a P Q,
    e, P, Q, he, hP, hQ, rfl⟩

private theorem roundedNormalizedDoubledResponseMaxAtGeneration_nonneg
    [NeZero d] {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (k : ℤ) (w : Fin d → ℤ) :
    0 ≤ roundedNormalizedDoubledResponseMaxAtGeneration
      l a abar hS k w := by
  unfold roundedNormalizedDoubledResponseMaxAtGeneration
  apply Real.sSup_nonneg
  rintro _ ⟨e, P, Q, _he, _hP, _hQ, rfl⟩
  let U : Book.Ch02.Domain d :=
    ⟨adaptedCellAt (roundedGrid l (symmPart abar)) k w,
      Recurrence.isOpenBoundedConvexDomain_adaptedCellAt
        (Recurrence.posDef_roundedGrid hl hS) k w,
      Recurrence.adaptedCellAt_nonempty (roundedGrid l (symmPart abar)) k w⟩
  have hresponse := Book.Ch02.doubledResponseJ_nonneg U (a.coeffOn U) P Q
  rw [show adaptedCellAt (roundedGrid l (symmPart abar)) k w =
      (U : Set (Vec d)) by rfl,
    Transport.coeffSpaceDoubledResponse_eq_doubledResponseJ U a P Q]
  exact hresponse

private theorem summable_truncatedBoundaryMajorant
    (j : ℤ) (u G : ℕ) {rawBoundary : ℝ} (hrawBoundary0 : 0 ≤ rawBoundary)
    (A : ℕ → ℝ) (B : ℤ → ℝ) (hA0 : ∀ n, 0 ≤ A n) (hB0 : ∀ r, 0 ≤ B r)
    (hBA : ∀ v : ℕ, B (j - (v : ℤ)) = A (G + (u + v)))
    (hmajor : Summable (fun v : ℕ ↦
      (max 1 rawBoundary * (3 : ℝ) ^ (-(v : ℤ))) * A (G + (u + v)))) :
    let raw := fun v : ℕ ↦
      (if v = 0 then 1 else rawBoundary * (3 : ℝ) ^ ((j - (v : ℤ)) - j)) *
        B (j - (v : ℤ))
    Summable raw ∧ (∑' v : ℕ, raw v) ≤
      ∑' v : ℕ, (max 1 rawBoundary * (3 : ℝ) ^ (-(v : ℤ))) * A (G + (u + v)) := by
  let C : ℝ := max 1 rawBoundary
  let raw : ℕ → ℝ := fun v ↦
    (if v = 0 then 1 else rawBoundary * (3 : ℝ) ^ ((j - (v : ℤ)) - j)) *
      B (j - (v : ℤ))
  let major : ℕ → ℝ := fun v ↦
    (C * (3 : ℝ) ^ (-(v : ℤ))) * A (G + (u + v))
  have hrawBoundaryC : rawBoundary ≤ C := le_max_right _ _
  have hraw0 : ∀ v, 0 ≤ raw v := by
    intro v
    dsimp only [raw]
    apply mul_nonneg
    · split
      · exact zero_le_one
      · exact mul_nonneg hrawBoundary0 (zpow_nonneg (by norm_num) _)
    · exact hB0 (j - (v : ℤ))
  have hrawMajor : ∀ v, raw v ≤ major v := by
    intro v
    have hcoefficient :
        (if v = 0 then 1 else
          rawBoundary * (3 : ℝ) ^ ((j - (v : ℤ)) - j)) ≤
          C * (3 : ℝ) ^ (-(v : ℤ)) := by
      by_cases hv : v = 0
      · subst v
        simpa only [ite_eq_left, Nat.cast_zero, Int.ofNat_zero, neg_zero,
          zpow_zero, mul_one] using le_max_left (1 : ℝ) rawBoundary
      · rw [ite_eq_right hv]
        have hexponent : (j - (v : ℤ)) - j = -(v : ℤ) := by ring
        rw [hexponent]
        exact mul_le_mul_of_nonneg_right hrawBoundaryC
          (zpow_nonneg (by norm_num) _)
    dsimp only [raw, major]
    rw [hBA v]
    exact mul_le_mul_of_nonneg_right hcoefficient (hA0 (G + (u + v)))
  have hrawSummable : Summable raw :=
    Summable.of_nonneg_of_le hraw0 hrawMajor hmajor
  exact ⟨hrawSummable, hrawSummable.tsum_le_tsum hrawMajor hmajor⟩

private theorem summable_weightedFiniteSupremum_of_majorant
    {ι : Type*} (Z : ℕ → Finset ι) (values : ℕ → ι → ℝ)
    (weight majorant : ℕ → ℝ)
    (hZ : ∀ u, (Z u).Nonempty) (hvalues : ∀ u i, 0 ≤ values u i)
    (hweight : ∀ u, 0 ≤ weight u)
    (hbound : ∀ u i, i ∈ Z u → values u i ≤ majorant u)
    (hmajorant : Summable (fun u ↦ weight u * majorant u)) :
    Summable (fun u ↦ weight u * Book.Ch02.finsetSupReal (Z u) (values u)) ∧
      (∑' u, weight u * Book.Ch02.finsetSupReal (Z u) (values u)) ≤
        ∑' u, weight u * majorant u := by
  have hsup : ∀ u, Book.Ch02.finsetSupReal (Z u) (values u) ≤ majorant u :=
    fun u ↦ Book.Ch02.finsetSupReal_le (Z u) (hZ u) (hbound u)
  have hnonnegative : ∀ u, 0 ≤ weight u * Book.Ch02.finsetSupReal (Z u) (values u) :=
    fun u ↦ mul_nonneg (hweight u)
      (Book.Ch02.finsetSupReal_nonneg (Z u) _ fun i _ ↦ hvalues u i)
  have hmajor : ∀ u,
      weight u * Book.Ch02.finsetSupReal (Z u) (values u) ≤ weight u * majorant u :=
    fun u ↦ mul_le_mul_of_nonneg_left (hsup u) (hweight u)
  have hsummable := Summable.of_nonneg_of_le hnonnegative hmajor hmajorant
  exact ⟨hsummable, hsummable.tsum_le_tsum hmajor hmajorant⟩

/-- A selected rounded spatial row is controlled by one enclosing
normalized-root weak error. -/
theorem exists_summable_roundedGenerationResponseMaxRow_le_scalarIdentityWeakError_sq
    [NeZero d] {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (t : ℤ)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ R : TriadicCube d,
      (aRef.coeffOn R).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain
              (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField)
    {s : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2) (M : ℤ) :
    ∃ G : ℕ, ∃ Z : ℕ → Finset (Fin d → ℤ),
      (3 : ℝ) ^ (G : ℤ) ≤
          1 + 3 * ((100 / 99 : ℝ) *
            witnessEccentricity (symmPart abar) * Real.sqrt d) ∧
      (∀ u : ℕ,
        ↑(Z u) = {w : Fin d → ℤ |
          adaptedCellCenter (roundedGrid l (symmPart abar))
              (M - (u : ℤ)) w ∈
            adaptedCell (roundedGrid l (symmPart abar)) M}) ∧
      (∀ u : ℕ, (Z u).card = 3 ^ (d * u)) ∧
      Summable (fun u : ℕ ↦
        Book.Ch02.geometricWeight s 2 u *
          Book.Ch02.finsetSupReal (Z u) (fun w ↦
            roundedNormalizedDoubledResponseMaxAtGeneration
              l a abar hS (M - (u : ℤ)) w)) ∧
      (∑' u : ℕ,
          Book.Ch02.geometricWeight s 2 u *
            Book.Ch02.finsetSupReal (Z u) (fun w ↦
              roundedNormalizedDoubledResponseMaxAtGeneration
                l a abar hS (M - (u : ℤ)) w)) ≤
        (max 1
            (6 * (d : ℝ) * Real.sqrt d *
              ((101 / 100 : ℝ) * witnessEccentricity (symmPart abar))) *
            (Book.Ch02.geometricDiscount (1 - 2 * s) 1)⁻¹) *
          Real.rpow 3 (2 * s * (G : ℝ)) *
            scalarIdentityWeakError aRef s (M + (G : ℤ)) ^ 2 := by
  classical
  obtain ⟨G, Z, hG, hZ, hcard, hEnclose⟩ :=
    exists_outerCellIndices_enclosed_by_normalizedRoot_at_generation hl hS M
  refine ⟨G, Z, hG, hZ, hcard, ?_⟩
  let parentScale : ℤ := M + (G : ℤ)
  let q : Mat d := Selection.normalizedRoot (symmPart abar)
  let parent : TriadicCube d := originCube d parentScale
  let rawBoundary : ℝ :=
    6 * (d : ℝ) * Real.sqrt d *
      ((101 / 100 : ℝ) * witnessEccentricity (symmPart abar))
  let C : ℝ := max 1 rawBoundary
  let A : ℕ → ℝ := fun n ↦
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
      parent (parentScale - (n : ℤ)) aRef (1 : Mat d)
  let B : ℤ → ℝ := fun r ↦
    if r ≤ parentScale then
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
        parent r aRef (1 : Mat d)
    else 0
  have hq : q.PosDef := by
    simpa only [q] using normalizedRoot_posDef_of_posDef hS
  have hrawBoundary0 : 0 ≤ rawBoundary := by
    have hecc0 : 0 ≤ witnessEccentricity (symmPart abar) :=
      (Transport.zero_lt_witnessEccentricity hS).le
    dsimp only [rawBoundary]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6)
        (Nat.cast_nonneg d)) (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 101 / 100) hecc0)
  have hC0 : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
  have hrawBoundaryC : rawBoundary ≤ C := le_max_right _ _
  have hA0 : ∀ n, 0 ≤ A n := by
    intro n
    dsimp only [A, parent]
    exact Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg
      (originCube d parentScale) (by
        change parentScale - (n : ℤ) ≤ parentScale
        omega) aRef (1 : Mat d)
  have hA : Summable (fun n : ℕ ↦
      Book.Ch02.geometricWeight s 2 n * A n) := by
    simpa only [A, parent, originCube] using
      (Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        (originCube d parentScale) aRef (1 : Mat d) hs)
  have hB0 : ∀ r, 0 ≤ B r := by
    intro r
    by_cases hr : r ≤ parentScale
    · rw [show B r =
          Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
            parent r aRef (1 : Mat d) by simp only [B, ite_eq_left hr]]
      exact Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg
        parent (by simpa only [parent, originCube] using hr) aRef (1 : Mat d)
    · simp only [B, ite_eq_right hr, le_rfl]
  obtain ⟨hinner, houter, hconvolution⟩ :=
    Transport.summable_boundaryConvolution_shift_and_tsum_le
      hs hsHalf hC0 G A hA0 hA
  have hresponse : ∀ (u : ℕ) (w : Fin d → ℤ), w ∈ Z u →
      ∀ (e : FullBlockVec d), Book.Ch02.fullBlockVecNormSq e = 1 →
      ∀ P Q : BlockVec d,
        normalizedReferencePrimalLoad abar P = ofFullBlockVec e →
        normalizedReferenceDualLoad abar Q = ofFullBlockVec e →
        Transport.coeffSpaceDoubledResponse
            (adaptedCellAt (roundedGrid l (symmPart abar))
              (M - (u : ℤ)) w) a P Q ≤
          ∑' v : ℕ,
            (C * (3 : ℝ) ^ (-(v : ℤ))) * A (G + (u + v)) := by
    intro u w hw e he P Q hP hQ
    let j : ℤ := M - (u : ℤ)
    let y : Vec d :=
      adaptedCellCenter (roundedGrid l (symmPart abar)) j w
    have hjParent : j ≤ parentScale := by
      dsimp only [j, parentScale]
      omega
    obtain ⟨Zfill, hZfill, haggregate⟩ :=
      exists_coeffSpaceDoubledResponse_roundedGrid_le_rowMajorant
        hl hS j j y a P Q
    have hcellB : ∀ (v : ℕ) (z : Fin d → ℤ),
        z ∈ Zfill (j - (v : ℤ)) →
        Book.Ch02.doubledResponseJ
            (Response.adaptedDomainAt hq (j - (v : ℤ)) z)
            (a.coeffOn (Response.adaptedDomainAt hq
              (j - (v : ℤ)) z)) P Q ≤ B (j - (v : ℤ)) := by
      intro v z hz
      have hrParent : j - (v : ℤ) ≤ parentScale := by omega
      have htargetEnclose :
          adaptedCellTranslate (roundedGrid l (symmPart abar)) j y ⊆
            adaptedCell (Selection.normalizedRoot (symmPart abar)) parentScale := by
        simpa only [j, y, parentScale] using hEnclose u w hw
      have hdesc : translateCube z (originCube d (j - (v : ℤ))) ∈
          descendantsAtScale parent (j - (v : ℤ)) := by
        simpa only [parent, q] using
          (translateCube_mem_descendants_of_generation_filling
            hS hjParent hZfill htargetEnclose hz)
      have hcell := normalizedRootCell_response_le_of_loads
        a abar hS t aRef haRef e he P Q hP hQ (j - (v : ℤ)) z
      have hmax :=
        Book.Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
          aRef (1 : Mat d) hdesc
      exact hcell.trans (by
        simpa only [B, ite_eq_left hrParent, parent] using hmax)
    let raw : ℕ → ℝ := fun v ↦
      (if v = 0 then 1 else
        rawBoundary * (3 : ℝ) ^ ((j - (v : ℤ)) - j)) *
          B (j - (v : ℤ))
    let major : ℕ → ℝ := fun v ↦
      (C * (3 : ℝ) ^ (-(v : ℤ))) * A (G + (u + v))
    have hBA : ∀ v : ℕ, B (j - (v : ℤ)) = A (G + (u + v)) := by
      intro v
      have hrParent : j - (v : ℤ) ≤ parentScale := by omega
      have hscale : j - (v : ℤ) =
          parentScale - ((G + (u + v) : ℕ) : ℤ) := by
        dsimp only [j, parentScale]
        push_cast
        omega
      dsimp only [B, A, parent]
      rw [ite_eq_left hrParent, hscale]
    obtain ⟨hrawSummable, hrawTsum⟩ :=
      summable_truncatedBoundaryMajorant j u G hrawBoundary0 A B hA0 hB0 hBA
        (by simpa only [C, major] using hinner u)
    have haggregate' := haggregate B hB0 hcellB (by
      simpa only [raw] using hrawSummable)
    calc
      Transport.coeffSpaceDoubledResponse
          (adaptedCellAt (roundedGrid l (symmPart abar))
            (M - (u : ℤ)) w) a P Q ≤ ∑' v : ℕ, raw v := by
        simpa only [j, y, raw, adaptedCellAt_eq_adaptedCellTranslate] using
          haggregate'
      _ ≤ ∑' v : ℕ, major v := hrawTsum
      _ = _ := by rfl
  have hmax : ∀ (u : ℕ) (w : Fin d → ℤ), w ∈ Z u →
      roundedNormalizedDoubledResponseMaxAtGeneration
          l a abar hS (M - (u : ℤ)) w ≤
        ∑' v : ℕ,
          (C * (3 : ℝ) ^ (-(v : ℤ))) * A (G + (u + v)) := by
    intro u w hw
    unfold roundedNormalizedDoubledResponseMaxAtGeneration
    refine csSup_le
      (roundedResponseValueSetAtGeneration_nonempty
        a abar hS t aRef haRef (M - (u : ℤ)) w) ?_
    rintro _ ⟨e, P, Q, he, hP, hQ, rfl⟩
    exact hresponse u w hw e he P Q hP hQ
  have hZne : ∀ u : ℕ, (Z u).Nonempty := by
    intro u
    apply Finset.card_pos.mp
    rw [hcard u]
    positivity
  have hweight0 : ∀ u, 0 ≤ Book.Ch02.geometricWeight s 2 u := by
    intro u
    simpa only [Book.Ch02.geometricWeight_eq_old] using
      (HCPolySupport.geometricWeight_nonneg u
        (mul_nonneg hs.le (by norm_num : (0 : ℝ) ≤ 2)))
  obtain ⟨hphysical, hphysicalTsum⟩ := summable_weightedFiniteSupremum_of_majorant Z
    (fun u w ↦ roundedNormalizedDoubledResponseMaxAtGeneration
      l a abar hS (M - (u : ℤ)) w)
    (Book.Ch02.geometricWeight s 2)
    (fun u ↦ ∑' v : ℕ, (C * (3 : ℝ) ^ (-(v : ℤ))) * A (G + (u + v)))
    hZne (fun u w ↦ roundedNormalizedDoubledResponseMaxAtGeneration_nonneg
      hl a abar hS (M - (u : ℤ)) w) hweight0 hmax
    (by simpa only [C, A, add_assoc] using houter)
  refine ⟨hphysical, ?_⟩
  have hparent :
      (∑' n : ℕ, Book.Ch02.geometricWeight s 2 n * A n) =
        scalarIdentityWeakError aRef s parentScale ^ 2 := by
    simpa only [A, parent, originCube, scalarIdentityWeakError] using
      (Book.Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum
        (originCube d parentScale) hs aRef (1 : Mat d)).symm
  calc
    (∑' u : ℕ,
        Book.Ch02.geometricWeight s 2 u *
          Book.Ch02.finsetSupReal (Z u) (fun w ↦
            roundedNormalizedDoubledResponseMaxAtGeneration
              l a abar hS (M - (u : ℤ)) w)) ≤
        ∑' u : ℕ, Book.Ch02.geometricWeight s 2 u *
          ∑' v : ℕ, (C * (3 : ℝ) ^ (-(v : ℤ))) * A (G + (u + v)) :=
      hphysicalTsum
    _ ≤ (C * (Book.Ch02.geometricDiscount (1 - 2 * s) 1)⁻¹) *
          Real.rpow 3 (2 * s * (G : ℝ)) *
            ∑' n : ℕ, Book.Ch02.geometricWeight s 2 n * A n := hconvolution
    _ = _ := by rw [hparent]

end

end HighContrast
end HCPolySupport
