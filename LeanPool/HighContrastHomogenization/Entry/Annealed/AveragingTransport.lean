/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.ColourClasses
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedCellFoundations
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AnnealedBlockOrder
public import LeanPool.HighContrastHomogenization.Entry.Annealed.Normalization
public import LeanPool.HighContrastHomogenization.Entry.Source.BoundedWindowFiniteness
public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormIntegrability

/-!
# High-contrast homogenization: Entry.Annealed.AveragingTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Integrability, lattice centering, and stationarity transport

For the cell `q = Geometry.explicitRoundedGrid jStar m`, deterministic centre `A`, conjugator `R`
and
`Y y = fun a => normalizedBlock (blockSub (coarseBlock (adaptedCellTranslate q j y) a) A) R`,
the normalized recentred block `Y y` lies in `L^N(S_N)` for every real `N ≥ 1`, every generation
`j` and every centre `y`, with no membership premise beyond the standing law; at a lattice centre
`adaptedCellCenter q j w` of generation `j_* ≤ j` its entrywise mean vanishes; and the lattice
translation that moves the centre to the origin leaves its block-valued mixed norm unchanged,
`‖Y z‖_{L^N(S_N)} = ‖Y 0‖_{L^N(S_N)}`, with `A` and `R` held fixed.  These centering, moment and
stationarity facts serve the finite-range matrix averaging lemma
`l.fixed.geometry.matrix.averaging` and the mean and profile estimates of the two-grid transport
`p.two.grid.transport`.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  adaptedMean annealedBlock blockSub coarseBlock measurable_translateCoeff normalizedBlock
  translateCoeff)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory

open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The cell at the origin -/

/-- `adaptedCellTranslate q j 0 = adaptedCell q j`.  The right-hand side is
the untranslated cell; the lattice picture writes it as the translate by `0`. -/
theorem adaptedCellTranslate_zero (q : Mat d) (j : ℤ) :
    HighContrast.adaptedCellTranslate q j 0 = HighContrast.adaptedCell q j := by
  ext x
  simp [HighContrast.adaptedCellTranslate]

/-! ## Integrability receipts -/

/-- **The integrability receipt.**  `Y y` lies in `L^N(S_N)` for every real `N ≥ 1`, every
generation `j` and every centre `y`.  No membership premise is added to any statement; this is
derived from the standing law. -/
theorem memLqSchatten_normalizedCentered (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjS : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (j : ℤ) (y : Vec d) (R : BlockMat d) (N : ℝ) (hN : 1 ≤ N) :
    SchattenMemLp P N (fun a => normalizedBlock
      (blockSub (coarseBlock
        (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y) a)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j)) R) := by
  have hcoarse : SchattenMemLp P N
      (fun a => coarseBlock
        (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y) a) :=
    Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag jStar hjS m hm j y N hN
  have hconst : SchattenMemLp P N
      (fun _ => adaptedMean P (Geometry.explicitRoundedGrid jStar m) j) :=
    Analysis.memLqSchatten_const P hN _
      (isSymmetricBlockMat_annealedBlock P
        (HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) j))
  exact Source.memLqSchatten_normalizedBlock (hcoarse.sub hconst hN) hN R

/-- The full normalized average lies in `L^N(S_N)` as well, through
`memLqSchatten_finset_sum` in the shape the class average uses. -/
theorem memLqSchatten_normalizedCentered_sum (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjS : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (j : ℤ) (R : BlockMat d) (N : ℝ) (hN : 1 ≤ N)
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (y : ι → Vec d) :
    SchattenMemLp P N (fun a => ofFullBlockMat (∑ i ∈ s, w i • toFullBlockMat
      (normalizedBlock (blockSub (coarseBlock
        (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j (y i)) a)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j)) R))) :=
  Source.memLqSchatten_finset_sum hN s w _ fun i _ =>
    memLqSchatten_normalizedCentered d hd P γ E Ψ K S hstat hdag jStar hjS m hm j (y i) R N hN

/-! ## Centering at a lattice cell -/

/-- The annealed block of a cell centred at a lattice point of the same generation is the
adapted mean.  `annealedBlock_adaptedCellAtCenter`, moved to the `adaptedCellTranslate`
picture. -/
theorem annealedBlock_adaptedCellTranslate_lattice
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjS : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    {j : ℤ} (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ) :
    annealedBlock P (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j
        (adaptedCellCenter (Geometry.explicitRoundedGrid jStar m) j w))
      = adaptedMean P (Geometry.explicitRoundedGrid jStar m) j :=
  annealedBlock_adaptedCellAtCenter P hstat jStar hjS m hm j hj w

/-- **Centering.**  For a cell centred at a lattice point of generation `j ≥ j_*` the entrywise
mean of `Y z` vanishes.  This is the `hcent` premise, in the
`Matrix.of fun α β => ∫ …` shape that premise uses; the same object is stated as
`fun α β => ∫ …`, and the two are bridged here rather than left to coincide. -/
theorem integral_normalizedCentered_lattice_eq_zero (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjS : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    {j : ℤ} (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ) (R : BlockMat d) :
    ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry
      (normalizedBlock (blockSub (coarseBlock
        (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j
          (adaptedCellCenter (Geometry.explicitRoundedGrid jStar m) j w)) a)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j)) R) α β ∂P)
      = ofFullBlockMat (0 : FullBlockMat d) := by
  have hU : HasIntegrableCoarseBlock P
      (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j
        (adaptedCellCenter (Geometry.explicitRoundedGrid jStar m) j w)) :=
    hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag jStar hjS m hm j _
  have hmean := annealedBlock_adaptedCellTranslate_lattice P hstat jStar hjS m hm hj w
  have hzero := integral_centered_normalized_coarseBlock hU R
  rw [hmean] at hzero
  exact hzero

/-! ## Stationarity transport of the block-valued mixed norm -/

/-- The block at a lattice-centred cell is the block at the origin precomposed with the integer
translation of the coefficient field.  `A` and `R` are deterministic and do not move. -/
theorem normalizedCentered_lattice_eq_comp_translateCoeff
    (jStar : ℕ) (m : Mat d) {j : ℤ} (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (A R : BlockMat d) :
    ∃ v : Fin d → ℤ,
      (fun a => normalizedBlock (blockSub (coarseBlock
        (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j
          (adaptedCellCenter (Geometry.explicitRoundedGrid jStar m) j w)) a) A) R)
      = (fun a => normalizedBlock (blockSub (coarseBlock
          (HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) j) a) A) R) ∘
            translateCoeff v := by
  obtain ⟨v, hv⟩ := adaptedCellCenter_eq_intTranslation jStar m hj w
  refine ⟨v, ?_⟩
  funext a
  have hstep := coarseBlock_adapted_translateCoeff (Geometry.explicitRoundedGrid jStar m) j 0 v a
  rw [adaptedCellTranslate_zero, zero_add] at hstep
  simp only [Function.comp_apply, hv]
  rw [← hstep]

/-- **Stationarity transport.**  `‖Y z‖_{L^N(S_N)} = ‖Y 0‖_{L^N(S_N)}` for every lattice centre
`z = adaptedCellCenter q j w` with `j_* ≤ j`.

Route: `adaptedCellCenter_eq_intTranslation` writes the centre as an integer translation;
`coarseBlock_adapted_translateCoeff` turns the shifted cell into a precomposition with
`translateCoeff v`; `IsStationaryLaw` says `Measure.map (translateCoeff v) P = P`; and the
scalar integrand is `AEStronglyMeasurable`, so the change of variables for the Bochner integral
applies.  This is the block-valued transport, at the block level rather than
merely entrywise. -/
theorem lqSchattenNorm_normalizedCentered_transport
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P)
    (jStar : ℕ) (m : Mat d) {j : ℤ} (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (A R : BlockMat d) {N : ℝ} (hN : 1 ≤ N)
    (hmem : SchattenMemLp P N (fun a => normalizedBlock (blockSub
      (coarseBlock (HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) j) a) A) R)) :
    lqSchattenNorm P N (fun a => normalizedBlock (blockSub (coarseBlock
        (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j
          (adaptedCellCenter (Geometry.explicitRoundedGrid jStar m) j w)) a) A) R)
      = lqSchattenNorm P N (fun a => normalizedBlock (blockSub
          (coarseBlock (HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) j) a) A)
            R) := by
  obtain ⟨v, hcomp⟩ :=
    normalizedCentered_lattice_eq_comp_translateCoeff jStar m hj w A R
  set F : CoeffSpace d → BlockMat d := fun a => normalizedBlock (blockSub
    (coarseBlock (HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) j) a) A) R with hF
  have hmap : Measure.map (translateCoeff v) P = P := hstat v
  have hg : AEStronglyMeasurable (fun b => absSchattenNorm N (F b) ^ N) P := by
    refine ((Analysis.aestronglyMeasurable_absSchattenNorm hmem.measurable
      hN).aemeasurable.pow_const
      N).aestronglyMeasurable
  have hint : ∫ a, absSchattenNorm N (F (translateCoeff v a)) ^ N ∂P
      = ∫ b, absSchattenNorm N (F b) ^ N ∂P := by
    have h := integral_map (μ := P) (φ := translateCoeff v)
      (measurable_translateCoeff v).aemeasurable
      (f := fun b => absSchattenNorm N (F b) ^ N) (by rw [hmap]; exact hg)
    rw [hmap] at h
    exact h.symm
  unfold lqSchattenNorm
  rw [hcomp]
  simp only [Function.comp_apply]
  rw [hint]

end

end HCPolySupport.HighContrast.Annealed
