/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormVariance

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormCellEnergy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Cell energies for the diagonal weak estimate

The parent optimizer restricts to every aligned child after transport to one
everywhere-elliptic representative.  This permits the coarse energy map to be
applied on each child without changing the canonical optimizer state.  The
child energies then average exactly to twice the squared parent energy.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The metric square of the canonical state's average on one child is
controlled by the child's response size and the actual state energy there. -/
theorem metricBlockNormSq_blockCellAverage_diagonalWeakState_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (a : CoeffSpace d) (p r : Vec d) {m : Mat d} (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) :
    metricBlockNormSq m
        (blockCellAverage (adaptedCellAt q k w)
          (diagonalWeakState hq t a p r)) ≤
      diagonalWeakMetricFactor m E ^ 2 *
        blockSize (adaptedResponse q k w a) E *
          Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
            blockVecDot (diagonalWeakState hq t a p r x)
              (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
                (diagonalWeakState hq t a p r x))) := by
  obtain ⟨f, hae, hfamily⟩ :=
    CoeffSpace.exists_pointwise_coeffOn_family_aeeq a
  obtain ⟨b, _blam, _bLam, hbf, _hblam, _hbLam, _hbEll, hba⟩ :=
    hfamily (adaptedDomain hq t)
  obtain ⟨c, _clam, _cLam, hcf, hclam, hcLam, hcEll, hca⟩ :=
    hfamily (adaptedDomainAt hq k w)
  let u := diagonalWeakOptimizer hq t a p r
  let ub : Solution (adaptedDomain hq t) b := Solution.ofAEEq hba u
  have hmem : adaptedCellCenter q k w ∈ adaptedCell q t := by
    have hset : w ∈ (↑(alignedIndex q k t) : Set (Fin d → ℤ)) := hw
    rwa [coe_alignedIndex hq hkt] at hset
  have hrep : c.toCoeffField = b.toCoeffField := by rw [hcf, hbf]
  obtain ⟨z, hz⟩ := exists_restrict_solution_adaptedCellAt hq hkt hmem
    hrep (by rw [hcf]; exact hcEll) ub
  let Y : DoubledField d :=
    { potential := z.toH1.grad
      flux := fun x => matVecMul (c.toCoeffField x) (z.toH1.grad x) }
  have hEllC : IsEllipticFieldOn c.lam c.Lam (adaptedCellAt q k w)
      c.toCoeffField := by
    rw [hcf, hclam, hcLam]
    exact hcEll
  have hY : IsDoubledResponseField (adaptedDomainAt hq k w) c Y :=
    isDoubledResponseField_gradFlux hEllC z
  have hcblock : Book.Ch02.coarseBlockMatrix (adaptedDomainAt hq k w) c =
      adaptedResponse q k w a := by
    calc
      Book.Ch02.coarseBlockMatrix (adaptedDomainAt hq k w) c =
          Book.Ch02.coarseBlockMatrix (adaptedDomainAt hq k w)
            (a.coeffOn (adaptedDomainAt hq k w)) :=
        (Book.Ch02.coarseBlockMatrix_eq_ofAEEq hca).symm
      _ = coarseBlock (adaptedCellAt q k w) a :=
        (coarseBlock_eq_coarseBlockMatrix a (adaptedDomainAt hq k w)).symm
      _ = adaptedResponse q k w a := rfl
  have hpot : Book.Ch02.averageVec (adaptedDomainAt hq k w) Y.potential =
      (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t a p r)).1 := by
    apply Book.Ch02.averageVec_eq_of_ae_eq
    filter_upwards with x
    change z.toH1.grad x = u.toH1.grad x
    exact congrFun hz x
  have hflux : Book.Ch02.averageVec (adaptedDomainAt hq k w) Y.flux =
      (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t a p r)).2 := by
    apply Book.Ch02.averageVec_eq_of_ae_eq
    filter_upwards [ae_restrict_of_ae hae] with x hx
    change matVecMul (c.toCoeffField x) (z.toH1.grad x) =
      matVecMul ((a.coeffOn (adaptedDomain hq t)).toCoeffField x)
        (u.toH1.grad x)
    rw [hz, show ub.toH1.grad = u.toH1.grad from rfl, hcf]
    change matVecMul (f x) (u.toH1.grad x) =
      matVecMul ((⇑a.1 : CoeffField d) x) (u.toH1.grad x)
    rw [hx]
  have henergy :
      Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
        blockVecDot (Y.eval x)
          (blockMatVecMul (blockMatrixField c x) (Y.eval x))) =
      Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
        blockVecDot (diagonalWeakState hq t a p r x)
          (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
            (diagonalWeakState hq t a p r x))) := by
    apply Book.Ch02.average_eq_of_ae_eq
    filter_upwards [ae_restrict_of_ae hae] with x hx
    change blockVecDot
        ((z.toH1.grad x, matVecMul (c.toCoeffField x) (z.toH1.grad x)) : BlockVec d)
        (blockMatVecMul (blockMatrixOfCoeff (c.toCoeffField x))
          ((z.toH1.grad x, matVecMul (c.toCoeffField x) (z.toH1.grad x)) : BlockVec d)) = _
    rw [hz, show ub.toH1.grad = u.toH1.grad from rfl, hcf]
    have hstate : diagonalWeakState hq t a p r x =
        ((u.toH1.grad x, matVecMul (f x) (u.toH1.grad x)) : BlockVec d) := by
      change
        ((u.toH1.grad x,
          matVecMul ((⇑a.1 : CoeffField d) x) (u.toH1.grad x)) : BlockVec d) = _
      rw [hx]
    rw [hstate, hx]
  have hmap := metricBlockNormSq_average_le_adaptedCellAt hq k w
    hcblock (by rw [hcf]; exact hcEll) hY hm hE hEpd
  rw [hpot, hflux, henergy] at hmap
  exact hmap

/-- The normalized average of the canonical state energies on an aligned
subdivision is exactly twice the squared parent energy. -/
theorem avsum_diagonalWeakState_energy_eq
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    (a : CoeffSpace d) (p r : Vec d) :
    avsum (alignedIndex q k t) (fun w =>
        Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
          blockVecDot (diagonalWeakState hq t a p r x)
            (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
              (diagonalWeakState hq t a p r x)))) =
      2 * diagonalWeakEnergy hq t a p r ^ 2 := by
  let F := diagonalWeakState hq t a p r
  let X : BlockState d :=
    { potential := fun x => (F x).1
      flux := fun x => (F x).2 }
  obtain ⟨f, hae, hfamily⟩ :=
    CoeffSpace.exists_pointwise_coeffOn_family_aeeq a
  obtain ⟨_b, _blam, _bLam, _hbf, _hblam, _hbLam, hbEll, _hba⟩ :=
    hfamily (adaptedDomain hq t)
  obtain ⟨hpot, hflux⟩ := diagonalWeakState_memVectorL2 hq t a p r
  let : IsFiniteMeasure (volumeMeasureOn (adaptedCell q t)) :=
    (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isFiniteMeasure_restrict_volume
  have hX : MemBlockL2 (adaptedCell q t) X.eval :=
    memBlockL2_blockField hpot hflux
  have hintf : IntegrableOn (blockEnergyDensity f X) (adaptedCell q t) volume :=
    blockEnergyDensity_integrableOn_of_memBlockL2_of_isEllipticFieldOn hX hbEll
  have henergyAE : blockEnergyDensity f X =ᵐ[volumeMeasureOn (adaptedCell q t)]
      blockEnergyDensity (⇑a.1 : CoeffField d) X := by
    filter_upwards [ae_restrict_of_ae hae] with x hx
    simp [blockEnergyDensity, blockCoeffField, hx]
  have hinta : IntegrableOn (blockEnergyDensity (⇑a.1 : CoeffField d) X)
      (adaptedCell q t) volume := hintf.congr henergyAE
  have hG : IntegrableOn (fun x =>
      blockVecDot (F x)
        (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x)) (F x)))
      (adaptedCell q t) volume := by
    refine (hinta.const_mul 2).congr ?_
    filter_upwards with x
    change 2 * ((1 / 2 : ℝ) *
        blockVecDot (F x)
          (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x)) (F x))) = _
    ring
  have hpartition := avsum_volumeAverage_adaptedCellAt_eq hq hkt hG
  have hparent := average_block_energy_eq
    (a.coeffOn (adaptedDomain hq t)) (diagonalWeakOptimizer hq t a p r)
  have hparent' : Book.Ch02.average (adaptedDomain hq t) (fun x =>
      blockVecDot (F x)
        (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x)) (F x))) =
      2 * variationEnergyValue (adaptedDomain hq t)
        (a.coeffOn (adaptedDomain hq t)) (diagonalWeakOptimizer hq t a p r) := by
    simpa only [F, diagonalWeakState,
      CoeffSpace.coeffOn_toCoeffField] using! hparent
  change avsum (alignedIndex q k t) (fun w =>
      volumeAverage (adaptedCellAt q k w) (fun x =>
        blockVecDot (F x)
          (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x)) (F x)))) = _
  rw [hpartition]
  change Book.Ch02.average (adaptedDomain hq t) (fun x =>
      blockVecDot (F x)
        (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x)) (F x))) = _
  rw [hparent', ← sq_diagonalWeakEnergy]

/-- Every child contribution in the canonical state-energy partition is
nonnegative. -/
theorem diagonalWeakState_cellEnergy_nonneg {q : Mat d} (hq : q.PosDef)
    (k t : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d) (p r : Vec d) :
    0 ≤ Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
      blockVecDot (diagonalWeakState hq t a p r x)
        (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
          (diagonalWeakState hq t a p r x))) := by
  let F := diagonalWeakState hq t a p r
  obtain ⟨f, hae, hfamily⟩ :=
    CoeffSpace.exists_pointwise_coeffOn_family_aeeq a
  obtain ⟨_c, _clam, _cLam, _hcf, _hclam, _hcLam, hcEll, _hca⟩ :=
    hfamily (adaptedDomainAt hq k w)
  have havg : Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
      blockVecDot (F x)
        (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x)) (F x))) =
      Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
        blockVecDot (F x) (blockMatVecMul (blockMatrixOfCoeff (f x)) (F x))) := by
    apply Book.Ch02.average_eq_of_ae_eq
    filter_upwards [ae_restrict_of_ae hae] with x hx
    rw [hx]
  change 0 ≤ Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
      blockVecDot (F x)
        (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x)) (F x)))
  rw [havg]
  change 0 ≤ volumeAverage (adaptedCellAt q k w) (fun x =>
    blockVecDot (F x) (blockMatVecMul (blockMatrixOfCoeff (f x)) (F x)))
  refine volumeAverage_nonneg_of_nonneg_on
    (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq k w).isOpen.measurableSet ?_
  intro x hx
  exact blockMatrixOfCoeff_quadratic_nonneg (hcEll.2 x hx) (F x)

end

end Response
end HighContrast
end HCPolySupport
