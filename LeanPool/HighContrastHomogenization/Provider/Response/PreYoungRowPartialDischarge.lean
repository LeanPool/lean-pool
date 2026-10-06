/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungRowClosingAssembly
public import LeanPool.HighContrastHomogenization.Provider.Response.RowCellEnergyBound
public import LeanPool.HighContrastHomogenization.Provider.Response.RowCellPairingProducer
public import LeanPool.HighContrastHomogenization.Provider.Response.OptimizerEnergyMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Response.LocalizedOptimizerObservables
public import LeanPool.HighContrastHomogenization.Provider.Response.RecentDifferenceEnergyMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedCutoffGradientField
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileEnergyMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungCenteredDecomposition
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.StationarityTransport
public import LeanPool.HighContrastHomogenization.Provider.Response.NestedAlignedGeometry
public import LeanPool.HighContrastHomogenization.Provider.Response.RowPairingAnnealed

/-!
# High-contrast homogenization: Provider.Response.PreYoungRowPartialDischarge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Partial discharge of the pre-Young response rows

The terminal row energy is a localized weighted optimizer energy.  Its
measurability therefore follows from measurable selection for the canonical
optimizer, leaving only a finite-integral domination premise.  This closes the
per-scale energy input of the primal and adjoint row estimates.

The cell-pairing bridge is insensitive to the chosen representative of the
coefficient field.  The pointwise estimates below select an everywhere
elliptic representative internally and transport the doubled response field,
coarse block, and energy average along almost-everywhere equality.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Measurability and integrability of the row energy -/

/-- A child quarter-energy is a fixed multiple of the terminal optimizer
energy localized to that child. -/
theorem cellQuarterEnergy_eq_weightedOptimizerEnergy [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (a : CoeffSpace d) (p r : Vec d) :
    cellQuarterEnergy hq k t w a p r =
      (volume (adaptedCell q t)).toReal *
        (volume (adaptedCellAt q k w)).toReal⁻¹ *
          Selection.weightedOptimizerEnergy (adaptedDomain hq t)
            (a.coeffOn (adaptedDomain hq t)) p r
            (Set.indicator (adaptedCellAt q k w) fun _ ↦ (1 : ℝ)) := by
  let U := adaptedDomain hq t
  let V := adaptedDomainAt hq k w
  have hVU : (V : Set (Vec d)) ⊆ (U : Set (Vec d)) :=
    adaptedCellAt_subset_of_mem_alignedIndex hq hkt hw
  have hVmeas : MeasurableSet (V : Set (Vec d)) :=
    (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq k w).isOpen.measurableSet
  have hquad : ∀ᵐ x ∂volumeMeasureOn (V : Set (Vec d)),
      blockVecDot (diagonalWeakState hq t a p r x)
          (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
            (diagonalWeakState hq t a p r x)) =
        2 * vecDot (Selection.optimizerBlockState U (a.coeffOn U) p r x).1
          (matVecMul ((a.coeffOn U).toCoeffField x)
            (Selection.optimizerBlockState U (a.coeffOn U) p r x).1) := by
    filter_upwards [Selection.ae_of_subset hVmeas hVU (a.coeffOn U).aeElliptic] with x hx
    rw [Selection.diagonalWeakState_eq_optimizerBlockState hq t a p r]
    change blockVecDot (Selection.optimizerBlockState U (a.coeffOn U) p r x)
        (blockMatVecMul (blockMatrixOfCoeff ((a.coeffOn U).toCoeffField x))
          (Selection.optimizerBlockState U (a.coeffOn U) p r x)) = _
    have hstate : Selection.optimizerBlockState U (a.coeffOn U) p r x =
        ((Selection.optimizerBlockState U (a.coeffOn U) p r x).1,
          matVecMul ((a.coeffOn U).toCoeffField x)
            (Selection.optimizerBlockState U (a.coeffOn U) p r x).1) := by
      apply Prod.ext
      · rfl
      · exact Selection.optimizerBlockState_snd U (a.coeffOn U) p r x
    rw [hstate, blockMatVecMul_blockMatrixOfCoeff_primal_of_isEllipticMatrix hx]
    simp only [blockVecDot]
    rw [vecDot_comm]
    ring
  rw [cellQuarterEnergy, Book.Ch02.average_eq_of_ae_eq hquad]
  rw [Selection.weightedOptimizerEnergy, Book.Ch02.average, Book.Ch02.average]
  have hInt :
      ∫ x in adaptedCell q t, Set.indicator (adaptedCellAt q k w)
          (fun _ ↦ (1 : ℝ)) x *
          ((1 / 2 : ℝ) * vecDot (Selection.optimizerBlockState U (a.coeffOn U) p r x).1
            (matVecMul ((a.coeffOn U).toCoeffField x)
              (Selection.optimizerBlockState U (a.coeffOn U) p r x).1)) ∂volume =
        ∫ x in adaptedCellAt q k w, (1 : ℝ) *
          ((1 / 2 : ℝ) * vecDot (Selection.optimizerBlockState U (a.coeffOn U) p r x).1
            (matVecMul ((a.coeffOn U).toCoeffField x)
              (Selection.optimizerBlockState U (a.coeffOn U) p r x).1)) ∂volume :=
    Selection.setIntegral_indicator_mul
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq k w).isOpen.measurableSet
      (adaptedCellAt_subset_of_mem_alignedIndex hq hkt hw) _ _
  dsimp only [U, V] at hInt hquad ⊢
  simp only [adaptedDomain_carrier, adaptedDomainAt_carrier] at hInt ⊢
  rw [hInt]
  simp only [one_mul]
  have hscale :
      (∫ x in adaptedCellAt q k w,
        (2 : ℝ) * vecDot
          (Selection.optimizerBlockState (adaptedDomain hq t)
            (a.coeffOn (adaptedDomain hq t)) p r x).1
          (matVecMul ((a.coeffOn (adaptedDomain hq t)).toCoeffField x)
            (Selection.optimizerBlockState (adaptedDomain hq t)
              (a.coeffOn (adaptedDomain hq t)) p r x).1) ∂volume) =
        4 * ∫ x in adaptedCellAt q k w,
          (1 / 2 : ℝ) * vecDot
            (Selection.optimizerBlockState (adaptedDomain hq t)
              (a.coeffOn (adaptedDomain hq t)) p r x).1
            (matVecMul ((a.coeffOn (adaptedDomain hq t)).toCoeffField x)
              (Selection.optimizerBlockState (adaptedDomain hq t)
                (a.coeffOn (adaptedDomain hq t)) p r x).1) ∂volume := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    ring
  rw [hscale]
  have hUvol : (volume (adaptedCell q t)).toReal ≠ 0 :=
    ne_of_gt (Recurrence.toReal_volume_adaptedCell_pos hq t)
  field_simp

/-- The child quarter-energy is measurable on coefficient space. -/
theorem measurable_cellQuarterEnergy [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t) (p r : Vec d) :
    Measurable fun a : CoeffSpace d ↦ cellQuarterEnergy hq k t w a p r := by
  have hVmeas : Measurable (Set.indicator (adaptedCellAt q k w)
      fun _ ↦ (1 : ℝ)) :=
    measurable_const.indicator
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq k w).isOpen.measurableSet
  have hweighted := Selection.measurable_weightedOptimizerEnergy_coeffSpace
    (U := adaptedDomain hq t)
    (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isOpen
    (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isBoundedDomain
    (by simpa only [adaptedDomain_carrier] using
      Recurrence.toReal_volume_adaptedCell_pos hq t) p r hVmeas zero_le_one
    (fun x ↦ by by_cases hx : x ∈ adaptedCellAt q k w <;>
      simp [Set.indicator, hx])
  have heq : (fun a : CoeffSpace d ↦ cellQuarterEnergy hq k t w a p r) =
      fun a ↦ (volume (adaptedCell q t)).toReal *
        (volume (adaptedCellAt q k w)).toReal⁻¹ *
          Selection.weightedOptimizerEnergy (adaptedDomain hq t)
            (a.coeffOn (adaptedDomain hq t)) p r
            (Set.indicator (adaptedCellAt q k w) fun _ ↦ (1 : ℝ)) := by
    funext a
    exact cellQuarterEnergy_eq_weightedOptimizerEnergy hq hkt hw a p r
  rw [heq]
  exact hweighted.const_mul _

/-- A single cell energy is bounded by the subdivision cardinality times the
terminal response. -/
theorem cellQuarterEnergy_le_card_mul_responseJ [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (a : CoeffSpace d) (p r : Vec d) :
    cellQuarterEnergy hq k t w a p r ≤
      ((alignedIndex q k t).card : ℝ) *
        responseJ (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t)) p r := by
  let Z := alignedIndex q k t
  have hZ : Z.Nonempty := alignedIndex_nonempty hq hkt
  have hcard : (0 : ℝ) < (Z.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hZ
  have hnonneg : ∀ z ∈ Z, 0 ≤ cellQuarterEnergy hq k t z a p r := by
    intro z _hz
    exact mul_nonneg (by norm_num)
      (diagonalWeakState_cellEnergy_nonneg hq k t z a p r)
  have hone : cellQuarterEnergy hq k t w a p r ≤
      ∑ z ∈ Z, cellQuarterEnergy hq k t z a p r :=
    Finset.single_le_sum (fun z hz ↦ hnonneg z hz) hw
  have hav := avsum_cellQuarterEnergy_eq_responseJ hq hkt a p r
  calc
    cellQuarterEnergy hq k t w a p r ≤
        ∑ z ∈ Z, cellQuarterEnergy hq k t z a p r := hone
    _ = (Z.card : ℝ) * avsum Z
          (fun z ↦ cellQuarterEnergy hq k t z a p r) := by
      rw [avsum_eq]
      field_simp
    _ = (Z.card : ℝ) *
          responseJ (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t)) p r := by
      rw [hav]

/-- Integrability of the terminal response controls every measurable child
quarter-energy. -/
theorem integrable_cellQuarterEnergy_of_integrable_responseJ [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    {k t : ℤ} (hkt : k ≤ t) {w : Fin d → ℤ}
    (hw : w ∈ alignedIndex q k t) (sample : CoeffSpace d → CoeffSpace d)
    (hsample : Measurable sample) (p r : Vec d)
    (hintJ : Integrable (fun a ↦ responseJ (adaptedDomain hq t)
      ((sample a).coeffOn (adaptedDomain hq t)) p r) P) :
    Integrable (fun a ↦ cellQuarterEnergy hq k t w (sample a) p r) P := by
  let card : ℝ := ((alignedIndex q k t).card : ℝ)
  refine (hintJ.const_mul card).mono'
    ((measurable_cellQuarterEnergy hq hkt hw p r).comp hsample).aestronglyMeasurable
    (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  have henergy : 0 ≤ cellQuarterEnergy hq k t w (sample a) p r :=
    mul_nonneg (by norm_num)
      (diagonalWeakState_cellEnergy_nonneg hq k t w (sample a) p r)
  have hJ : 0 ≤ responseJ (adaptedDomain hq t)
      ((sample a).coeffOn (adaptedDomain hq t)) p r := responseJ_nonneg _ _ _ _
  have hcard : 0 ≤ card := Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg henergy,
    abs_of_nonneg (mul_nonneg hcard hJ), card] using
      cellQuarterEnergy_le_card_mul_responseJ hq hkt hw (sample a) p r

/-- A finite adapted mean makes every constant-skew primal child energy
integrable. -/
theorem integrable_cellQuarterEnergy_subSkew_of_finiteAdaptedMean
    [NeZero d] {P : Measure (CoeffSpace d)} [IsFiniteMeasure P]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    Integrable (fun a ↦ cellQuarterEnergy hq k t w (a.subSkew g hg) p r) P :=
  integrable_cellQuarterEnergy_of_integrable_responseJ
    hq hkt hw (fun a ↦ a.subSkew g hg) (Selection.measurable_subSkew g hg) p r
      (integrable_responseJ_subSkew_of_finiteAdaptedMean hq t hint g hg p r)

/-- A finite adapted mean independently controls the coefficient-transpose
child energy. -/
theorem integrable_cellQuarterEnergy_adjointSubSkew_of_finiteAdaptedMean
    [NeZero d] {P : Measure (CoeffSpace d)} [IsFiniteMeasure P]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    Integrable (fun a ↦
      cellQuarterEnergy hq k t w ((a.subSkew g hg).transpose) p r) P :=
  integrable_cellQuarterEnergy_of_integrable_responseJ
    hq hkt hw (fun a ↦ (a.subSkew g hg).transpose)
      (Selection.measurable_transpose.comp (Selection.measurable_subSkew g hg)) p r
      (integrable_responseJ_adjointSubSkew_of_finiteAdaptedMean
        hq t hint g hg p r)

/-- Annealed child energies are nonnegative without an additional law premise. -/
theorem profileAnnealedCellEnergySq_nonneg
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : q.PosDef)
    (k t : ℤ) (w : Fin d → ℤ) (sample : CoeffSpace d → CoeffSpace d)
    (p r : Vec d) :
    0 ≤ profileAnnealedCellEnergySq P hq k t w sample p r := by
  exact integral_nonneg fun a ↦ mul_nonneg (by norm_num)
    (diagonalWeakState_cellEnergy_nonneg hq k t w (sample a) p r)

/-! ## Representative-independent cell pairings -/

/-- The potential-slot cell pairing for a coefficient-space sample, with the
everywhere-elliptic representative selected internally. -/
theorem abs_vecDot_averageVec_potential_coeffSpace_le
    (U : Domain d) (a : CoeffSpace d)
    (hpsd : (Book.Ch02.coarseBlockMatrix U (a.coeffOn U)).lowerRight.PosSemidef)
    (hdet : IsUnit (Book.Ch02.coarseBlockMatrix U (a.coeffOn U)).lowerRight.det)
    {Y : DoubledField d} (hY : IsDoubledResponseField U (a.coeffOn U) Y)
    (Qcen : Vec d) :
    |vecDot Qcen (Book.Ch02.averageVec U Y.potential)| ≤
      Real.sqrt (Book.Ch02.average U (fun x ↦
          blockVecDot (Y.eval x)
            (blockMatVecMul (blockMatrixField (a.coeffOn U) x) (Y.eval x)))) *
        profileSchurLoadFlux (Book.Ch02.coarseBlockMatrix U (a.coeffOn U)) Qcen := by
  obtain ⟨_f, _hae, hfamily⟩ :=
    CoeffSpace.exists_pointwise_coeffOn_family_aeeq a
  obtain ⟨c, _clam, _cLam, hcf, hclam, hcLam, hcEll, hca⟩ := hfamily U
  have hcEll' : IsEllipticFieldOn c.lam c.Lam (U : Set (Vec d))
      c.toCoeffField := by
    rw [hcf, hclam, hcLam]
    exact hcEll
  have hpsdc : (Book.Ch02.coarseBlockMatrix U c).lowerRight.PosSemidef := by
    rw [← Book.Ch02.coarseBlockMatrix_eq_ofAEEq hca]
    exact hpsd
  have hdetc : IsUnit (Book.Ch02.coarseBlockMatrix U c).lowerRight.det := by
    rw [← Book.Ch02.coarseBlockMatrix_eq_ofAEEq hca]
    exact hdet
  have hbase := abs_vecDot_averageVec_potential_le c hcEll' hpsdc hdetc
    (hY.ofAEEq hca) Qcen
  have henergy :
      Book.Ch02.average U (fun x ↦ blockVecDot (Y.eval x)
          (blockMatVecMul (blockMatrixField (a.coeffOn U) x) (Y.eval x))) =
        Book.Ch02.average U (fun x ↦ blockVecDot (Y.eval x)
          (blockMatVecMul (blockMatrixField c x) (Y.eval x))) := by
    apply Book.Ch02.average_eq_of_ae_eq
    filter_upwards [Book.Ch02.blockMatrixField_ae_eq_ofAEEq hca] with x hx
    rw [hx]
  rwa [← Book.Ch02.coarseBlockMatrix_eq_ofAEEq hca, ← henergy] at hbase

/-- The flux-slot cell pairing for a coefficient-space sample, with the
everywhere-elliptic representative selected internally. -/
theorem abs_vecDot_averageVec_flux_coeffSpace_le
    (U : Domain d) (a : CoeffSpace d)
    (hpsd : (Book.Ch02.coarseBlockMatrix U (a.coeffOn U)).upperLeft.PosSemidef)
    {Y : DoubledField d} (hY : IsDoubledResponseField U (a.coeffOn U) Y)
    (Pcen : Vec d) :
    |vecDot Pcen (Book.Ch02.averageVec U Y.flux)| ≤
      Real.sqrt (Book.Ch02.average U (fun x ↦
          blockVecDot (Y.eval x)
            (blockMatVecMul (blockMatrixField (a.coeffOn U) x) (Y.eval x)))) *
        profileSchurLoadGradient (Book.Ch02.coarseBlockMatrix U (a.coeffOn U)) Pcen := by
  obtain ⟨_f, _hae, hfamily⟩ :=
    CoeffSpace.exists_pointwise_coeffOn_family_aeeq a
  obtain ⟨c, _clam, _cLam, hcf, hclam, hcLam, hcEll, hca⟩ := hfamily U
  have hcEll' : IsEllipticFieldOn c.lam c.Lam (U : Set (Vec d))
      c.toCoeffField := by
    rw [hcf, hclam, hcLam]
    exact hcEll
  have hpsdc : (Book.Ch02.coarseBlockMatrix U c).upperLeft.PosSemidef := by
    rw [← Book.Ch02.coarseBlockMatrix_eq_ofAEEq hca]
    exact hpsd
  have hbase := abs_vecDot_averageVec_flux_le c hcEll' hpsdc
    (hY.ofAEEq hca) Pcen
  have henergy :
      Book.Ch02.average U (fun x ↦ blockVecDot (Y.eval x)
          (blockMatVecMul (blockMatrixField (a.coeffOn U) x) (Y.eval x))) =
        Book.Ch02.average U (fun x ↦ blockVecDot (Y.eval x)
          (blockMatVecMul (blockMatrixField c x) (Y.eval x))) := by
    apply Book.Ch02.average_eq_of_ae_eq
    filter_upwards [Book.Ch02.blockMatrixField_ae_eq_ofAEEq hca] with x hx
    rw [hx]
  rwa [← Book.Ch02.coarseBlockMatrix_eq_ofAEEq hca, ← henergy] at hbase

/-- The two cell-average pairings for the restricted diagonal optimizer.  The
pointwise elliptic representative is selected inside the proof, so the result
applies directly to a coefficient-space sample and to its transpose. -/
theorem abs_vecDot_blockCellAverage_diagonalWeakState_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (a : CoeffSpace d) (p r Pcen Qcen : Vec d) :
    |vecDot Qcen (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t a p r)).1| ≤
        2 * Real.sqrt (cellQuarterEnergy hq k t w a p r) *
          profileSchurLoadFlux (coarseBlock (adaptedCellAt q k w) a) Qcen ∧
      |vecDot Pcen (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t a p r)).2| ≤
        2 * Real.sqrt (cellQuarterEnergy hq k t w a p r) *
          profileSchurLoadGradient (coarseBlock (adaptedCellAt q k w) a) Pcen := by
  let U := adaptedDomainAt hq k w
  obtain ⟨u, hu⟩ := exists_diagonalWeakOptimizer_restrict_child
    hq hkt hw a p r
  obtain ⟨_f, hae, hfamily⟩ :=
    CoeffSpace.exists_pointwise_coeffOn_family_aeeq a
  obtain ⟨c, _clam, _cLam, hcf, hclam, hcLam, hcEll, hca⟩ := hfamily U
  let uc : Solution U c := Solution.ofAEEq hca u
  let Y : DoubledField d :=
    { potential := uc.toH1.grad
      flux := fun x ↦ matVecMul (c.toCoeffField x) (uc.toH1.grad x) }
  have hcEll' : IsEllipticFieldOn c.lam c.Lam (U : Set (Vec d))
      c.toCoeffField := by
    rw [hcf, hclam, hcLam]
    exact hcEll
  have hYc : IsDoubledResponseField U c Y :=
    isDoubledResponseField_gradFlux hcEll' uc
  have hY : IsDoubledResponseField U (a.coeffOn U) Y :=
    hYc.ofAEEq hca.symm
  have hsymm := Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix U (a.coeffOn U)
  have hpos := (Book.Ch02.blockCoarseMatrixTheory U
    (a.coeffOn U)).block_matrix_posDef
  have hpsdLower :
      (Book.Ch02.coarseBlockMatrix U (a.coeffOn U)).lowerRight.PosSemidef :=
    posSemidef_lowerRight hsymm hpos
  have hdet : IsUnit
      (Book.Ch02.coarseBlockMatrix U (a.coeffOn U)).lowerRight.det :=
    isUnit_det_lowerRight hpos
  have hpsdUpper :
      (Book.Ch02.coarseBlockMatrix U (a.coeffOn U)).upperLeft.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      simpa only [Matrix.conjTranspose, RCLike.star_def, Matrix.map_apply,
        Matrix.transpose_apply, conj_trivial, blockMatEntry] using
          hsymm (Sum.inl j) (Sum.inl i)
    · intro x
      by_cases hx : x = 0
      · subst hx
        simp only [Matrix.mulVec_zero, dotProduct_zero, le_refl]
      · have hX : ((x, 0) : BlockVec d) ≠ 0 := by
          intro hzero
          exact hx (congrArg Prod.fst hzero)
        have hquad := (hpos ((x, 0) : BlockVec d) hX).le
        simpa only [star_trivial, ge_iff_le, blockVecDot, blockMatVecMul,
          matVecMul_zero, add_zero, vecDot_zero_left] using! hquad
  have hpot : Book.Ch02.averageVec U Y.potential =
      (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t a p r)).1 := by
    apply Book.Ch02.averageVec_eq_of_ae_eq
    filter_upwards with x
    change uc.toH1.grad x = (diagonalWeakOptimizer hq t a p r).toH1.grad x
    simpa only [uc, Solution.toH1_ofAEEq] using congrFun hu x
  have hflux : Book.Ch02.averageVec U Y.flux =
      (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t a p r)).2 := by
    apply Book.Ch02.averageVec_eq_of_ae_eq
    filter_upwards [hca] with x hx
    change matVecMul (c.toCoeffField x) (uc.toH1.grad x) =
      matVecMul ((a.coeffOn U).toCoeffField x)
        ((diagonalWeakOptimizer hq t a p r).toH1.grad x)
    rw [show uc.toH1.grad = u.toH1.grad from rfl, hu, hx]
  have henergyEq : Book.Ch02.average U (fun x ↦
      blockVecDot (Y.eval x)
        (blockMatVecMul (blockMatrixField (a.coeffOn U) x) (Y.eval x))) =
      Book.Ch02.average U (fun x ↦
        blockVecDot (diagonalWeakState hq t a p r x)
          (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
            (diagonalWeakState hq t a p r x))) := by
    apply Book.Ch02.average_eq_of_ae_eq
    filter_upwards [hca, ae_restrict_of_ae hae] with x hxca hx
    change blockVecDot
        ((uc.toH1.grad x, matVecMul (c.toCoeffField x) (uc.toH1.grad x)) : BlockVec d)
        (blockMatVecMul (blockMatrixOfCoeff ((a.coeffOn U).toCoeffField x))
          ((uc.toH1.grad x, matVecMul (c.toCoeffField x) (uc.toH1.grad x)) : BlockVec d)) =
      blockVecDot (diagonalWeakState hq t a p r x)
        (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
          (diagonalWeakState hq t a p r x))
    have hstate : diagonalWeakState hq t a p r x =
        (((diagonalWeakOptimizer hq t a p r).toH1.grad x,
          matVecMul (_f x)
            ((diagonalWeakOptimizer hq t a p r).toH1.grad x)) : BlockVec d) := by
      change
        (((diagonalWeakOptimizer hq t a p r).toH1.grad x,
          matVecMul ((⇑a.1 : CoeffField d) x)
            ((diagonalWeakOptimizer hq t a p r).toH1.grad x)) : BlockVec d) = _
      rw [hx]
    rw [show uc.toH1.grad = u.toH1.grad from rfl, hu, hxca, hcf, hx]
    rw [hstate]
  have henergy : Book.Ch02.average U (fun x ↦
      blockVecDot (Y.eval x)
        (blockMatVecMul (blockMatrixField (a.coeffOn U) x) (Y.eval x))) =
      4 * cellQuarterEnergy hq k t w a p r := by
    rw [henergyEq, cellQuarterEnergy]
    ring
  have hsqrt : Real.sqrt (4 * cellQuarterEnergy hq k t w a p r) =
      2 * Real.sqrt (cellQuarterEnergy hq k t w a p r) := by
    have hfour : Real.sqrt (4 : ℝ) = 2 := by
      have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4)
      have hnonneg := Real.sqrt_nonneg (4 : ℝ)
      nlinarith only [hsq, hnonneg]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hfour]
  have hbasePot := abs_vecDot_averageVec_potential_coeffSpace_le
    U a hpsdLower hdet hY Qcen
  have hbaseFlux := abs_vecDot_averageVec_flux_coeffSpace_le
    U a hpsdUpper hY Pcen
  rw [hpot, henergy, hsqrt,
    ← coarseBlock_eq_coarseBlockMatrix a U] at hbasePot
  rw [hflux, henergy, hsqrt,
    ← coarseBlock_eq_coarseBlockMatrix a U] at hbaseFlux
  exact ⟨hbasePot, hbaseFlux⟩

/-! ## Annealed cell pairings -/

private theorem profileSchurLoadFlux_profileAdjointBlock
    (H : BlockMat d) (Qcen : Vec d) :
    profileSchurLoadFlux (profileAdjointBlock H) Qcen =
      profileSchurLoadFlux H Qcen := by
  rw [profileSchurLoadFlux, profileAdjointBlock,
    blockMatMul_blockDiag_one_neg_one]
  rfl

private theorem profileSchurLoadGradient_profileAdjointBlock
    (H : BlockMat d) (Pcen : Vec d) :
    profileSchurLoadGradient (profileAdjointBlock H) Pcen =
      profileSchurLoadGradient H Pcen := by
  rw [profileSchurLoadGradient, profileAdjointBlock,
    blockMatMul_blockDiag_one_neg_one]
  rfl

private theorem aestronglyMeasurable_abs_vecDot_potential
    {P : Measure (CoeffSpace d)} [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t) :
    AEStronglyMeasurable (fun a : CoeffSpace d ↦
      |vecDot Qcen (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t (a.subSkew g hg) p r)).1|) P := by
  have hsum : AEStronglyMeasurable (fun a : CoeffSpace d ↦
      ∑ i, Qcen i * (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t (a.subSkew g hg) p r)).1 i) P :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ ↦ by
      simpa only [toFullBlockVec] using
        (Selection.aestronglyMeasurable_blockCellAverage_diagonalWeakState_subSkew_alignedIndex
          hq hkt P g hg p r hw (Sum.inl i)).const_mul (Qcen i)
  simpa only [vecDot, Real.norm_eq_abs] using hsum.norm

private theorem aestronglyMeasurable_abs_vecDot_flux
    {P : Measure (CoeffSpace d)} [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t) :
    AEStronglyMeasurable (fun a : CoeffSpace d ↦
      |vecDot Pcen (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t (a.subSkew g hg) p r)).2|) P := by
  have hsum : AEStronglyMeasurable (fun a : CoeffSpace d ↦
      ∑ i, Pcen i * (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t (a.subSkew g hg) p r)).2 i) P :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ ↦ by
      simpa only [toFullBlockVec] using
        (Selection.aestronglyMeasurable_blockCellAverage_diagonalWeakState_subSkew_alignedIndex
          hq hkt P g hg p r hw (Sum.inr i)).const_mul (Pcen i)
  simpa only [vecDot, Real.norm_eq_abs] using hsum.norm

private theorem aestronglyMeasurable_abs_vecDot_potential_adjoint
    {P : Measure (CoeffSpace d)} [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t) :
    AEStronglyMeasurable (fun a : CoeffSpace d ↦
      |vecDot Qcen (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)).1|) P := by
  have hsum : AEStronglyMeasurable (fun a : CoeffSpace d ↦
      ∑ i, Qcen i * (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)).1 i) P :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ ↦ by
      simpa only [toFullBlockVec] using
        (Selection.aestronglyMeasurable_alignedCellAverage_diagonalAdjointState
          hq hkt P g hg p r hw (Sum.inl i)).const_mul (Qcen i)
  simpa only [vecDot, Real.norm_eq_abs] using hsum.norm

private theorem aestronglyMeasurable_abs_vecDot_flux_adjoint
    {P : Measure (CoeffSpace d)} [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t) :
    AEStronglyMeasurable (fun a : CoeffSpace d ↦
      |vecDot Pcen (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)).2|) P := by
  have hsum : AEStronglyMeasurable (fun a : CoeffSpace d ↦
      ∑ i, Pcen i * (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)).2 i) P :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ ↦ by
      simpa only [toFullBlockVec] using
        (Selection.aestronglyMeasurable_alignedCellAverage_diagonalAdjointState
          hq hkt P g hg p r hw (Sum.inr i)).const_mul (Pcen i)
  simpa only [vecDot, Real.norm_eq_abs] using hsum.norm

private theorem half_integral_pairing_le
    {P : Measure (CoeffSpace d)}
    (pair energy load : CoeffSpace d → ℝ) (annealedLoad : ℝ)
    (hpair : ∀ a, 0 ≤ pair a) (henergy : ∀ a, 0 ≤ energy a)
    (hload : ∀ a, 0 ≤ load a)
    (hannealedLoad : 0 ≤ annealedLoad)
    (hpoint : ∀ a, pair a ≤ 2 * Real.sqrt (energy a) * load a)
    (hmeasPair : AEStronglyMeasurable pair P)
    (hintEnergy : Integrable energy P)
    (hintLoadSq : Integrable (fun a ↦ load a ^ 2) P)
    (hloadIntegral : ∫ a, load a ^ 2 ∂P = annealedLoad ^ 2) :
    (1 / 2 : ℝ) * ∫ a, pair a ∂P ≤
      Real.sqrt (∫ a, energy a ∂P) * annealedLoad := by
  have hmeasLoad : AEStronglyMeasurable load P := by
    apply AEStronglyMeasurable.congr
      hintLoadSq.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
    exact _root_.Filter.Eventually.of_forall fun a ↦ Real.sqrt_sq (hload a)
  have hrootMeas : AEStronglyMeasurable
      (fun a ↦ Real.sqrt (energy a)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hintEnergy.aestronglyMeasurable
  have hrootSq : (fun a ↦ Real.sqrt (energy a) ^ (2 : ℕ)) =ᵐ[P] energy :=
    _root_.Filter.Eventually.of_forall fun a ↦ Real.sq_sqrt (henergy a)
  have hrootL2 : MemLp (fun a ↦ Real.sqrt (energy a)) 2 P :=
    (memLp_two_iff_integrable_sq hrootMeas).2 (hintEnergy.congr hrootSq.symm)
  have hloadL2 : MemLp load 2 P :=
    (memLp_two_iff_integrable_sq hmeasLoad).2 hintLoadSq
  have hintProd : Integrable (fun a ↦ Real.sqrt (energy a) * load a) P :=
    hrootL2.integrable_mul hloadL2
  have hintPair : Integrable pair P := by
    refine Integrable.mono' (hintProd.const_mul 2) hmeasPair
      (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hpair a), abs_of_nonneg
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
        (mul_nonneg (Real.sqrt_nonneg _) (hload a))), mul_assoc] using hpoint a
  have hsqE : ∀ a, Real.sqrt (energy a) ^ 2 = energy a :=
    fun a ↦ Real.sq_sqrt (henergy a)
  have hintSqE : Integrable (fun a ↦ Real.sqrt (energy a) ^ 2) P := by
    refine hintEnergy.congr ?_
    exact _root_.Filter.Eventually.of_forall fun a ↦ (hsqE a).symm
  have hcs := integral_mul_le_sqrt_mul_sqrt hintSqE hintLoadSq hintProd
  have hEint : ∫ a, Real.sqrt (energy a) ^ 2 ∂P = ∫ a, energy a ∂P :=
    integral_congr_ae (_root_.Filter.Eventually.of_forall hsqE)
  rw [hEint, hloadIntegral, Real.sqrt_sq hannealedLoad] at hcs
  have hmono : ∫ a, pair a ∂P ≤
      ∫ a, 2 * (Real.sqrt (energy a) * load a) ∂P := by
    refine integral_mono hintPair (hintProd.const_mul 2) fun a ↦ ?_
    simpa only [mul_assoc] using hpoint a
  calc
    (1 / 2 : ℝ) * ∫ a, pair a ∂P ≤
        (1 / 2 : ℝ) * ∫ a, 2 * (Real.sqrt (energy a) * load a) ∂P :=
      mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = ∫ a, Real.sqrt (energy a) * load a ∂P := by
      rw [integral_const_mul]
      ring
    _ ≤ Real.sqrt (∫ a, energy a ∂P) * annealedLoad := hcs

private theorem upperLeft_posSemidef {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpos : BlockPosDef H) :
    H.upperLeft.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simpa only [Matrix.conjTranspose, RCLike.star_def, Matrix.map_apply,
      Matrix.transpose_apply, conj_trivial, blockMatEntry] using
        hsymm (Sum.inl j) (Sum.inl i)
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp only [Matrix.mulVec_zero, dotProduct_zero, le_rfl]
    · have hX : ((x, 0) : BlockVec d) ≠ 0 := by
        intro hzero
        exact hx (congrArg Prod.fst hzero)
      have hquad := (hpos ((x, 0) : BlockVec d) hX).le
      simpa only [star_trivial, ge_iff_le, blockVecDot, blockMatVecMul,
        matVecMul_zero, add_zero, vecDot_zero_left] using! hquad

private theorem integrable_sq_profileSchurLoadFlux_hatted
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (k : ℤ) (w : Fin d → ℤ) (g : Mat d) (Qcen : Vec d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAt q k w)) :
    Integrable (fun a : CoeffSpace d ↦
      profileSchurLoadFlux
        (profileHattedBlock g (coarseBlock (adaptedCellAt q k w) a)) Qcen ^ 2) P := by
  refine (integrable_coarseBlock_quadratic hint
    ((0, Qcen) : BlockVec d)).congr
      (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  have hsymm := isSymmetricBlockMat_skewBlockCongr (g := g)
    (Recurrence.isSymmetricBlockMat_coarseBlock_adaptedCellAt q k w a)
  have hpos := blockPosDef_skewBlockCongr (g := g)
    (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq k w a)
  exact (sq_profileSchurLoadFlux_hatted_eq_blockQuadratic g _
    (posSemidef_lowerRight hsymm hpos) (isUnit_det_lowerRight hpos) Qcen).symm

private theorem integrable_sq_profileSchurLoadGradient_hatted
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (k : ℤ) (w : Fin d → ℤ) (g : Mat d) (Pcen : Vec d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAt q k w)) :
    Integrable (fun a : CoeffSpace d ↦
      profileSchurLoadGradient
        (profileHattedBlock g (coarseBlock (adaptedCellAt q k w) a)) Pcen ^ 2) P := by
  refine (integrable_coarseBlock_quadratic hint
    ((Pcen, matVecMul g Pcen) : BlockVec d)).congr
      (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  have hsymm := isSymmetricBlockMat_skewBlockCongr (g := g)
    (Recurrence.isSymmetricBlockMat_coarseBlock_adaptedCellAt q k w a)
  have hpos := blockPosDef_skewBlockCongr (g := g)
    (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq k w a)
  exact (sq_profileSchurLoadGradient_hatted_eq_blockQuadratic g _
    (upperLeft_posSemidef hsymm hpos) Pcen).symm

private theorem integral_sq_profileSchurLoadFlux_hatted_adaptedCellAt_eq
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ)
    (g : Mat d) (Qcen : Vec d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAt q k w)) :
    ∫ a, profileSchurLoadFlux
        (profileHattedBlock g (coarseBlock (adaptedCellAt q k w) a)) Qcen ^ 2 ∂P =
      profileSchurLoadFlux
        (profileHattedBlock g (annealedBlock P (adaptedCellAt q k w))) Qcen ^ 2 := by
  have hsymmA := isSymmetricBlockMat_skewBlockCongr (g := g)
    (Recurrence.isSymmetricBlockMat_annealedBlock P (adaptedCellAt q k w))
  have hposA := blockPosDef_skewBlockCongr (g := g)
    (Recurrence.blockPosDef_annealedBlock_adaptedCellAt hq k w hint)
  exact (integral_sq_profileSchurLoadFlux_hatted_eq hint g Qcen
    (posSemidef_lowerRight hsymmA hposA) (isUnit_det_lowerRight hposA)
    (fun a ↦ posSemidef_lowerRight
      (isSymmetricBlockMat_skewBlockCongr (g := g)
        (Recurrence.isSymmetricBlockMat_coarseBlock_adaptedCellAt q k w a))
      (blockPosDef_skewBlockCongr (g := g)
        (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq k w a)))
    (fun a ↦ isUnit_det_lowerRight (blockPosDef_skewBlockCongr (g := g)
      (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq k w a)))).symm

private theorem integral_sq_profileSchurLoadGradient_hatted_adaptedCellAt_eq
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ)
    (g : Mat d) (Pcen : Vec d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAt q k w)) :
    ∫ a, profileSchurLoadGradient
        (profileHattedBlock g (coarseBlock (adaptedCellAt q k w) a)) Pcen ^ 2 ∂P =
      profileSchurLoadGradient
        (profileHattedBlock g (annealedBlock P (adaptedCellAt q k w))) Pcen ^ 2 := by
  have hsymmA := isSymmetricBlockMat_skewBlockCongr (g := g)
    (Recurrence.isSymmetricBlockMat_annealedBlock P (adaptedCellAt q k w))
  have hposA := blockPosDef_skewBlockCongr (g := g)
    (Recurrence.blockPosDef_annealedBlock_adaptedCellAt hq k w hint)
  exact (integral_sq_profileSchurLoadGradient_hatted_eq hint g Pcen
    (upperLeft_posSemidef hsymmA hposA)
    (fun a ↦ upperLeft_posSemidef
      (isSymmetricBlockMat_skewBlockCongr (g := g)
        (Recurrence.isSymmetricBlockMat_coarseBlock_adaptedCellAt q k w a))
      (blockPosDef_skewBlockCongr (g := g)
        (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq k w a)))).symm

/-- Annealed primal cell pairings are controlled by the square root of the
localized optimizer energy and the corresponding annealed Schur loads. -/
theorem half_integral_cellPairings_primal_le_of_integrable_energy
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAt q k w))
    (hintEnergy : Integrable (fun a : CoeffSpace d ↦
      cellQuarterEnergy hq k t w (a.subSkew g hg) p r) P) :
    (1 / 2 : ℝ) * ∫ a, |vecDot Qcen
          (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakState hq t (a.subSkew g hg) p r)).1| ∂P ≤
        Real.sqrt (profileAnnealedCellEnergySq P hq k t w
          (fun a ↦ a.subSkew g hg) p r) *
          profileSchurLoadFlux
            (profileHattedBlock g
              (annealedBlock P (adaptedCellAt q k w))) Qcen ∧
      (1 / 2 : ℝ) * ∫ a, |vecDot Pcen
          (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakState hq t (a.subSkew g hg) p r)).2| ∂P ≤
        Real.sqrt (profileAnnealedCellEnergySq P hq k t w
          (fun a ↦ a.subSkew g hg) p r) *
          profileSchurLoadGradient
            (profileHattedBlock g
              (annealedBlock P (adaptedCellAt q k w))) Pcen := by
  let energy : CoeffSpace d → ℝ := fun a ↦
    cellQuarterEnergy hq k t w (a.subSkew g hg) p r
  let loadFlux : CoeffSpace d → ℝ := fun a ↦
    profileSchurLoadFlux
      (profileHattedBlock g (coarseBlock (adaptedCellAt q k w) a)) Qcen
  let loadGradient : CoeffSpace d → ℝ := fun a ↦
    profileSchurLoadGradient
      (profileHattedBlock g (coarseBlock (adaptedCellAt q k w) a)) Pcen
  have henergy : ∀ a, 0 ≤ energy a := fun a ↦ by
    exact mul_nonneg (by norm_num) (diagonalWeakState_cellEnergy_nonneg
      hq k t w (a.subSkew g hg) p r)
  have hpoint : ∀ a : CoeffSpace d,
      |vecDot Qcen (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t (a.subSkew g hg) p r)).1| ≤
        2 * Real.sqrt (energy a) * loadFlux a ∧
      |vecDot Pcen (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t (a.subSkew g hg) p r)).2| ≤
        2 * Real.sqrt (energy a) * loadGradient a := by
    intro a
    have hbase := abs_vecDot_blockCellAverage_diagonalWeakState_le
      hq hkt hw (a.subSkew g hg) p r Pcen Qcen
    have hcov := adaptedResponse_subSkew hq k w a g hg
    change coarseBlock (adaptedCellAt q k w) (a.subSkew g hg) =
      profileHattedBlock g (coarseBlock (adaptedCellAt q k w) a) at hcov
    rw [hcov] at hbase
    exact hbase
  have hintLoadFlux : Integrable (fun a ↦ loadFlux a ^ 2) P :=
    integrable_sq_profileSchurLoadFlux_hatted hq k w g Qcen hint
  have hintLoadGradient : Integrable (fun a ↦ loadGradient a ^ 2) P :=
    integrable_sq_profileSchurLoadGradient_hatted hq k w g Pcen hint
  have hloadFluxIntegral : ∫ a, loadFlux a ^ 2 ∂P =
      profileSchurLoadFlux
        (profileHattedBlock g (annealedBlock P (adaptedCellAt q k w))) Qcen ^ 2 :=
    integral_sq_profileSchurLoadFlux_hatted_adaptedCellAt_eq hq k w g Qcen hint
  have hloadGradientIntegral : ∫ a, loadGradient a ^ 2 ∂P =
      profileSchurLoadGradient
        (profileHattedBlock g (annealedBlock P (adaptedCellAt q k w))) Pcen ^ 2 :=
    integral_sq_profileSchurLoadGradient_hatted_adaptedCellAt_eq hq k w g Pcen hint
  constructor
  · simpa only [energy, loadFlux, profileAnnealedCellEnergySq] using
      half_integral_pairing_le
        (fun a : CoeffSpace d ↦ |vecDot Qcen
          (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakState hq t (a.subSkew g hg) p r)).1|)
        energy loadFlux
        (profileSchurLoadFlux
          (profileHattedBlock g (annealedBlock P (adaptedCellAt q k w))) Qcen)
        (fun a ↦ abs_nonneg _) henergy (fun a ↦ profileSchurLoadFlux_nonneg _ _)
        (profileSchurLoadFlux_nonneg _ _) (fun a ↦ (hpoint a).1)
        (aestronglyMeasurable_abs_vecDot_potential hq hkt g hg p r Qcen hw)
        hintEnergy hintLoadFlux hloadFluxIntegral
  · simpa only [energy, loadGradient, profileAnnealedCellEnergySq] using
      half_integral_pairing_le
        (fun a : CoeffSpace d ↦ |vecDot Pcen
          (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakState hq t (a.subSkew g hg) p r)).2|)
        energy loadGradient
        (profileSchurLoadGradient
          (profileHattedBlock g (annealedBlock P (adaptedCellAt q k w))) Pcen)
        (fun a ↦ abs_nonneg _) henergy (fun a ↦ profileSchurLoadGradient_nonneg _ _)
        (profileSchurLoadGradient_nonneg _ _) (fun a ↦ (hpoint a).2)
        (aestronglyMeasurable_abs_vecDot_flux hq hkt g hg p r Pcen hw)
        hintEnergy hintLoadGradient hloadGradientIntegral

/-- Annealed adjoint cell pairings obey the same estimate after transporting
the transposed coefficient response through the hatted adjoint block. -/
theorem half_integral_cellPairings_adjoint_le_of_integrable_energy
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAt q k w))
    (hintEnergy : Integrable (fun a : CoeffSpace d ↦
      cellQuarterEnergy hq k t w ((a.subSkew g hg).transpose) p r) P) :
    (1 / 2 : ℝ) * ∫ a, |vecDot Qcen
          (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)).1| ∂P ≤
        Real.sqrt (profileAnnealedCellEnergySq P hq k t w
          (fun a ↦ (a.subSkew g hg).transpose) p r) *
          profileSchurLoadFlux
            (profileHattedAdjointBlock g
              (annealedBlock P (adaptedCellAt q k w))) Qcen ∧
      (1 / 2 : ℝ) * ∫ a, |vecDot Pcen
          (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)).2| ∂P ≤
        Real.sqrt (profileAnnealedCellEnergySq P hq k t w
          (fun a ↦ (a.subSkew g hg).transpose) p r) *
          profileSchurLoadGradient
            (profileHattedAdjointBlock g
              (annealedBlock P (adaptedCellAt q k w))) Pcen := by
  let energy : CoeffSpace d → ℝ := fun a ↦
    cellQuarterEnergy hq k t w ((a.subSkew g hg).transpose) p r
  let loadFlux : CoeffSpace d → ℝ := fun a ↦
    profileSchurLoadFlux
      (profileHattedAdjointBlock g (coarseBlock (adaptedCellAt q k w) a)) Qcen
  let loadGradient : CoeffSpace d → ℝ := fun a ↦
    profileSchurLoadGradient
      (profileHattedAdjointBlock g (coarseBlock (adaptedCellAt q k w) a)) Pcen
  have henergy : ∀ a, 0 ≤ energy a := fun a ↦ by
    exact mul_nonneg (by norm_num) (diagonalWeakState_cellEnergy_nonneg
      hq k t w ((a.subSkew g hg).transpose) p r)
  have hpoint : ∀ a : CoeffSpace d,
      |vecDot Qcen (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)).1| ≤
        2 * Real.sqrt (energy a) * loadFlux a ∧
      |vecDot Pcen (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)).2| ≤
        2 * Real.sqrt (energy a) * loadGradient a := by
    intro a
    have hbase := abs_vecDot_blockCellAverage_diagonalWeakState_le
      hq hkt hw ((a.subSkew g hg).transpose) p r Pcen Qcen
    have htrans := adaptedResponse_transpose hq k w (a.subSkew g hg)
    change coarseBlock (adaptedCellAt q k w) ((a.subSkew g hg).transpose) =
      profileAdjointBlock
        (coarseBlock (adaptedCellAt q k w) (a.subSkew g hg)) at htrans
    have hsub := adaptedResponse_subSkew hq k w a g hg
    change coarseBlock (adaptedCellAt q k w) (a.subSkew g hg) =
      profileHattedBlock g (coarseBlock (adaptedCellAt q k w) a) at hsub
    rw [htrans, hsub] at hbase
    exact hbase
  have hintLoadFlux : Integrable (fun a ↦ loadFlux a ^ 2) P := by
    simpa only [loadFlux, profileHattedAdjointBlock,
      profileSchurLoadFlux_profileAdjointBlock] using
        integrable_sq_profileSchurLoadFlux_hatted hq k w g Qcen hint
  have hintLoadGradient : Integrable (fun a ↦ loadGradient a ^ 2) P := by
    simpa only [loadGradient, profileHattedAdjointBlock,
      profileSchurLoadGradient_profileAdjointBlock] using
        integrable_sq_profileSchurLoadGradient_hatted hq k w g Pcen hint
  have hloadFluxIntegral : ∫ a, loadFlux a ^ 2 ∂P =
      profileSchurLoadFlux
        (profileHattedAdjointBlock g
          (annealedBlock P (adaptedCellAt q k w))) Qcen ^ 2 := by
    simpa only [loadFlux, profileHattedAdjointBlock,
      profileSchurLoadFlux_profileAdjointBlock] using
        integral_sq_profileSchurLoadFlux_hatted_adaptedCellAt_eq
          hq k w g Qcen hint
  have hloadGradientIntegral : ∫ a, loadGradient a ^ 2 ∂P =
      profileSchurLoadGradient
        (profileHattedAdjointBlock g
          (annealedBlock P (adaptedCellAt q k w))) Pcen ^ 2 := by
    simpa only [loadGradient, profileHattedAdjointBlock,
      profileSchurLoadGradient_profileAdjointBlock] using
        integral_sq_profileSchurLoadGradient_hatted_adaptedCellAt_eq
          hq k w g Pcen hint
  constructor
  · simpa only [energy, loadFlux, profileAnnealedCellEnergySq] using
      half_integral_pairing_le
        (fun a : CoeffSpace d ↦ |vecDot Qcen
          (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)).1|)
        energy loadFlux
        (profileSchurLoadFlux
          (profileHattedAdjointBlock g
            (annealedBlock P (adaptedCellAt q k w))) Qcen)
        (fun a ↦ abs_nonneg _) henergy (fun a ↦ profileSchurLoadFlux_nonneg _ _)
        (profileSchurLoadFlux_nonneg _ _) (fun a ↦ (hpoint a).1)
        (aestronglyMeasurable_abs_vecDot_potential_adjoint
          hq hkt g hg p r Qcen hw)
        hintEnergy hintLoadFlux hloadFluxIntegral
  · simpa only [energy, loadGradient, profileAnnealedCellEnergySq] using
      half_integral_pairing_le
        (fun a : CoeffSpace d ↦ |vecDot Pcen
          (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)).2|)
        energy loadGradient
        (profileSchurLoadGradient
          (profileHattedAdjointBlock g
            (annealedBlock P (adaptedCellAt q k w))) Pcen)
        (fun a ↦ abs_nonneg _) henergy (fun a ↦ profileSchurLoadGradient_nonneg _ _)
        (profileSchurLoadGradient_nonneg _ _) (fun a ↦ (hpoint a).2)
        (aestronglyMeasurable_abs_vecDot_flux_adjoint
          hq hkt g hg p r Pcen hw)
        hintEnergy hintLoadGradient hloadGradientIntegral

/-- Averaging the cellwise Cauchy bounds over a finite row preserves the
root-mean-square energy and a stationary common load. -/
theorem avsum_cellPair_le_sqrt_avsum_energy_mul_load
    {ι : Type*} {Z : Finset ι} (hZ : Z.Nonempty)
    (cellPair energy pathLoad : ι → ℝ) (load : ℝ)
    (henergy : ∀ z ∈ Z, 0 ≤ energy z)
    (hload : 0 ≤ load)
    (hpath : ∀ z ∈ Z, pathLoad z = load)
    (hcell : ∀ z ∈ Z,
      cellPair z ≤ Real.sqrt (energy z) * pathLoad z) :
    avsum Z cellPair ≤ Real.sqrt (avsum Z energy) * load := by
  have hterm : ∀ z ∈ Z, cellPair z ≤ load * Real.sqrt (energy z) := by
    intro z hz
    rw [← hpath z hz, mul_comm]
    exact hcell z hz
  calc
    avsum Z cellPair ≤
        avsum Z (fun z ↦ load * Real.sqrt (energy z)) :=
      avsum_le_avsum hterm
    _ = load * avsum Z (fun z ↦ Real.sqrt (energy z)) :=
      avsum_const_mul Z load _
    _ ≤ load * Real.sqrt (avsum Z energy) :=
      mul_le_mul_of_nonneg_left (avsum_sqrt_le_sqrt_avsum hZ henergy) hload
    _ = Real.sqrt (avsum Z energy) * load := mul_comm _ _

private theorem six_mul_sharp_le_common_aux
    {D K M : ℝ} (hD : 1 ≤ D) (hKM : K ≤ M) (hM : 1 ≤ M) :
    6 * (32 * D ^ 2 * K) ≤ 1024 * D ^ 4 * M ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hDpow : D ^ 2 ≤ D ^ 4 := by
    have hDsq : 1 ≤ D ^ 2 := by nlinarith only [hD]
    nlinarith only [sq_nonneg (D ^ 2 - 1), hDsq]
  have hMpow : M ≤ M ^ 2 := by nlinarith only [hM]
  calc
    6 * (32 * D ^ 2 * K) = 192 * D ^ 2 * K := by ring
    _ ≤ 192 * D ^ 2 * M :=
      mul_le_mul_of_nonneg_left hKM (by positivity)
    _ ≤ 192 * D ^ 4 * M :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hDpow (by norm_num)) hM0
    _ ≤ 192 * D ^ 4 * M ^ 2 :=
      mul_le_mul_of_nonneg_left hMpow (by positivity)
    _ ≤ 1024 * D ^ 4 * M ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
        (by positivity)

/-- The common adapted derivative coefficient absorbs the scale conversion
and the half-energy normalization of the sharp cutoff oscillation bound. -/
theorem six_mul_sharpCutoffCoefficient_le_adaptedCutoffDerivativeCoeff
    [NeZero d] :
    6 * (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound) ≤
      adaptedCutoffDerivativeCoeff d := by
  rw [adaptedCutoffDerivativeCoeff_eq]
  apply six_mul_sharp_le_common_aux
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_max_left _ _

/-! ## Closed primal and adjoint row estimates -/

end

end HCPolySupport.HighContrast.Response
