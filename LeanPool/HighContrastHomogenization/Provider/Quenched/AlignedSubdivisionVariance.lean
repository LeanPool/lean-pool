/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterCellBounds
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AlignedSubdivision
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.FiniteRangeAveraging
public import LeanPool.HighContrastHomogenization.Provider.Transport.CenteredSplit

/-!
# High-contrast homogenization: Provider.Quenched.AlignedSubdivisionVariance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite-range variance on an aligned adapted subdivision

For a unit-range law, the centred responses of aligned adapted cells split into
finitely many independent colour classes.  Applied to the exact subdivision of
one adapted parent, this gives the square-root cardinality gain without passing
through a Euclidean grouping of cell centres.

The normalizing block is arbitrary.  In particular, the result can be read in
the fixed reference normalization used by the small-contrast response estimate.
The sole integrability input needed by the averaging theorem, finiteness of the
adapted mean, follows from coarse ellipticity.  The single-cell mixed norm is
allowed to be infinite; that branch is handled in the extended-nonnegative
carrier rather than introduced as a premise.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The mixed Schatten norm of a centred aligned cell is independent of its
aligned centre under stationarity. -/
private theorem lqSchattenSize_adaptedCellAt_eq
    {P : Measure (CoeffSpace d)} (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q) {j : ℤ} (hlj : l ≤ j)
    (E F : BlockMat d) (hE : IsSymmetricBlockMat E) (w : Fin d → ℤ) :
    lqSchattenSize P 2
        (fun a ↦ blockSub (coarseBlock (adaptedCellAt q j w) a) E) F =
      lqSchattenSize P 2
        (fun a ↦ blockSub (coarseBlock (adaptedCell q j) a) E) F := by
  obtain ⟨z, hz⟩ := Recurrence.exists_intVec_adaptedCellCenter hq hlj w
  have hblock : ∀ a : CoeffSpace d,
      coarseBlock (adaptedCellAt q j w) a =
        coarseBlock (adaptedCell q j) (translateCoeff z a) :=
    fun a ↦ Recurrence.adaptedResponse_eq_coarseBlock_translateCoeff hz a
  let X : CoeffSpace d → BlockMat d :=
    fun a ↦ blockSub (coarseBlock (adaptedCell q j) a) E
  have hfun :
      (fun a : CoeffSpace d ↦
          schattenSize 2
            (blockSub (coarseBlock (adaptedCellAt q j w) a) E) F) =
        (fun a : CoeffSpace d ↦ schattenSize 2 (X a) F) ∘ translateCoeff z := by
    funext a
    simp only [Function.comp_apply, X, hblock a]
  have hXsymm : ∀ a, IsSymmetricBlockMat (X a) := fun a ↦
    isSymmetricBlockMat_blockSub
      (isSymmetricBlockMat_coarseBlock (adaptedCell q j) a) hE
  have hXmeas : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun a ↦ toFullBlockMat (X a) α β) P := by
    intro α β
    have hmA : AEStronglyMeasurable
        (fun a : CoeffSpace d ↦
          toFullBlockMat (coarseBlock (adaptedCell q j) a) α β) P := by
      exact Recurrence.hasMeasurableCoarseBlock_adaptedCell P
        (Recurrence.posDef_of_isRoundedGrid hq) j α β
    have hmE : AEStronglyMeasurable
        (fun _ : CoeffSpace d ↦ toFullBlockMat E α β) P :=
      aestronglyMeasurable_const
    have hm := hmA.sub hmE
    simpa only [X, Recurrence.toFullBlockMat_blockSub_apply] using! hm
  have hmeas : AEStronglyMeasurable
      (fun a : CoeffSpace d ↦ schattenSize 2 (X a) F) P :=
    Transport.aestronglyMeasurable_schattenSize (P := P) (A := X) (F := F)
      (by exact even_two) hXsymm hXmeas
  rw [lqSchattenSize, lqSchattenSize, hfun]
  exact eLpNorm_comp_measurePreserving hmeas
    (Recurrence.measurePreserving_translateCoeff hstat z)

/-- There is a dimension-only constant for the `L²(S₂)` fluctuation of
the exact aligned subdivision.  The constant is selected before the law,
coarse-ellipticity data, grid, scales, and normalizer.

The right side is the single-cell fluctuation in the same arbitrary
normalization `F`.  Thus `F` may be the fixed reference block used in the
small-contrast response estimate. -/
theorem exists_alignedSubdivisionVarianceConstant (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (g : ℝ) (E : BlockMat d)
        (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ (l : ℤ) (q : Mat d), IsRoundedGrid l q →
          ∀ (j p : ℤ), l ≤ j → j ≤ p → ∀ F : BlockMat d,
            ∃ Z : Finset (Fin d → ℤ),
              (↑Z : Set (Fin d → ℤ)) =
                  {w | adaptedCellCenter q j w ∈ adaptedCell q p} ∧
                Z.card = 3 ^ (d * (p - j).toNat) ∧ Z.Nonempty ∧
                lqSchattenSize P 2
                    (fun a ↦ blockSub
                      (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
                        ∑ w ∈ Z,
                          toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
                      (adaptedMean P q j)) F ≤
                  ENNReal.ofReal
                      (C * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹)) *
                    lqSchattenSize P 2
                      (fun a ↦ blockSub (coarseBlock (adaptedCell q j) a)
                        (adaptedMean P q j)) F := by
  obtain ⟨C, hC, haverage⟩ :=
    Recurrence.finite_range_matrix_averaging d (by omega) (Q := 2) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro P g E Ψ K S hP hstat hunit hdag l q hq j p hlj hjp F
  let : IsProbabilityMeasure P := hP
  let : NeZero d := ⟨by omega⟩
  have hqpd : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hzero : adaptedCellTranslate q j 0 = adaptedCell q j := by
    simp [adaptedCellTranslate]
  have hmeas : HasMeasurableCoarseBlock P (adaptedCellTranslate q j 0) := by
    rw [hzero]
    exact Recurrence.hasMeasurableCoarseBlock_adaptedCell P hqpd j
  have hint : HasFiniteAdaptedMean P q j := by
    have h := Entry.hasIntegrableCoarseBlock_adaptedCellTranslate_of_dagger
      hdag hqpd hmeas
    rwa [hzero] at h
  obtain ⟨Z, hZ, hZcard⟩ := Recurrence.exists_finset_adaptedCellCenter_mem hqpd hjp
  have hZne : Z.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hZe
    rw [hZe, Finset.card_empty] at hZcard
    have : 0 < 3 ^ (d * (p - j).toNat) := pow_pos (by omega) _
    omega
  refine ⟨Z, hZ, hZcard, hZne, ?_⟩
  let v : ℝ≥0∞ := lqSchattenSize P 2
    (fun a ↦ blockSub (coarseBlock (adaptedCell q j) a)
      (adaptedMean P q j)) F
  have hcell : ∀ w ∈ Z,
      lqSchattenSize P 2
          (fun a ↦ blockSub (coarseBlock (adaptedCellAt q j w) a)
            (adaptedMean P q j)) F ≤ v := by
    intro w _hw
    exact le_of_eq (lqSchattenSize_adaptedCellAt_eq hstat hq hlj
      (adaptedMean P q j) F (Recurrence.isSymmetricBlockMat_adaptedMean P q j) w)
  simpa only [v] using
    haverage P hP hstat hunit l q hq j hlj hint F v Z hZne hcell

end

end Quenched
end HighContrast
end HCPolySupport
