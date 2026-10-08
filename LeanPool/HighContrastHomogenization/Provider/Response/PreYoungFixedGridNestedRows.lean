/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungAllScaleNestedStationarity
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridCells

/-!
# High-contrast homogenization: Provider.Response.PreYoungFixedGridNestedRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Nested row pairings at every fine scale, fixed grid

The nested row pairings at every fine scale on a fixed rounded grid: the grid
stays rounded at the fixed
alignment `l` while the generation window `{s, t}` moves, the aligned-cell
integrability coming from the `AlignedCellsIntegrable` carrier instead of the
window multiplier's carrier equality.  The proof is unchanged apart from the
window bundle replaced by the carrier.
-/

namespace HCPolySupport.HighContrast.Response.FixedGrid

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The primal nested row pairing remains valid at every fine scale.  Above
the starting scale it uses stationary finite means; below that scale it uses
the source-window enclosure and the parent-aligned stationarity relation. -/
theorem nestedAnnealedCellPairings_primal_le_of_cells
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d}
    (hgrid : IsRoundedGrid l q)
    {s t : ℤ} (hls : l ≤ s) (hst : s ≤ t)
    (hcells : AlignedCellsIntegrable P q s t)
    (hblocks : ∀ k : ℤ, l ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    {k : ℤ} (hks : k ≤ s)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k s)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d) :
    avsum (alignedIndex q s t) (fun z ↦
        (1 / 2 : ℝ) * ∫ a, |vecDot Qcen
          (blockCellAverage
            (adaptedCellAt q k (nestedLabel k s z w))
            (diagonalWeakState (Recurrence.posDef_of_isRoundedGrid hgrid) t
              (a.subSkew g hg) p r)).1| ∂P) ≤
        profileRowCellEnergy P (Recurrence.posDef_of_isRoundedGrid hgrid) k s t w
            (fun a ↦ a.subSkew g hg) p r *
          profileSchurLoadFlux
            (profileHattedBlock g
              (annealedBlock P (adaptedCellAt q k w))) Qcen ∧
      avsum (alignedIndex q s t) (fun z ↦
        (1 / 2 : ℝ) * ∫ a, |vecDot Pcen
          (blockCellAverage
            (adaptedCellAt q k (nestedLabel k s z w))
            (diagonalWeakState (Recurrence.posDef_of_isRoundedGrid hgrid) t
              (a.subSkew g hg) p r)).2| ∂P) ≤
        profileRowCellEnergy P (Recurrence.posDef_of_isRoundedGrid hgrid) k s t w
            (fun a ↦ a.subSkew g hg) p r *
          profileSchurLoadGradient
            (profileHattedBlock g
              (annealedBlock P (adaptedCellAt q k w))) Pcen := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let Z := alignedIndex q s t
  let energy : (Fin d → ℤ) → ℝ := fun z ↦
    profileAnnealedCellEnergySq P hq k t
      (nestedLabel k s z w) (fun a ↦ a.subSkew g hg) p r
  let loadFlux : (Fin d → ℤ) → ℝ := fun z ↦
    profileSchurLoadFlux
      (profileHattedBlock g
        (annealedBlock P (adaptedCellAt q k (nestedLabel k s z w)))) Qcen
  let loadGradient : (Fin d → ℤ) → ℝ := fun z ↦
    profileSchurLoadGradient
      (profileHattedBlock g
        (annealedBlock P (adaptedCellAt q k (nestedLabel k s z w)))) Pcen
  let pairFlux : (Fin d → ℤ) → ℝ := fun z ↦
    (1 / 2 : ℝ) * ∫ a, |vecDot Qcen
      (blockCellAverage (adaptedCellAt q k (nestedLabel k s z w))
        (diagonalWeakState hq t (a.subSkew g hg) p r)).1| ∂P
  let pairGradient : (Fin d → ℤ) → ℝ := fun z ↦
    (1 / 2 : ℝ) * ∫ a, |vecDot Pcen
      (blockCellAverage (adaptedCellAt q k (nestedLabel k s z w))
        (diagonalWeakState hq t (a.subSkew g hg) p r)).2| ∂P
  have hintRef : HasIntegrableCoarseBlock P (adaptedCellAt q k w) :=
    hcells hks hst (Or.inl rfl) hw
  have hmeasRef : HasMeasurableCoarseBlock P (adaptedCellAt q k w) :=
    fun i j ↦ (hintRef i j).aestronglyMeasurable
  have hmem : ∀ z ∈ Z,
      nestedLabel k s z w ∈ alignedIndex q k t := by
    intro z hz
    exact nestedLabel_mem_alignedIndex hq hks hst hw hz
  have henergy : ∀ z ∈ Z, 0 ≤ energy z := by
    intro z hz
    exact profileAnnealedCellEnergySq_nonneg P hq k t
      (nestedLabel k s z w) (fun a ↦ a.subSkew g hg) p r
  have hpathFlux : ∀ z ∈ Z, loadFlux z =
      profileSchurLoadFlux
        (profileHattedBlock g
          (annealedBlock P (adaptedCellAt q k w))) Qcen := by
    intro z hz
    exact profileSchurLoadFlux_nestedLabel_eq_of_parent_aligned
      hstat hgrid hks hls z w hmeasRef g Qcen
  have hpathGradient : ∀ z ∈ Z, loadGradient z =
      profileSchurLoadGradient
        (profileHattedBlock g
          (annealedBlock P (adaptedCellAt q k w))) Pcen := by
    intro z hz
    exact profileSchurLoadGradient_nestedLabel_eq_of_parent_aligned
      hstat hgrid hks hls z w hmeasRef g Pcen
  have hintt : HasFiniteAdaptedMean P q t :=
    (hblocks t (hls.trans hst) le_rfl).1
  have hcell : ∀ z ∈ Z,
      pairFlux z ≤ Real.sqrt (energy z) * loadFlux z ∧
      pairGradient z ≤ Real.sqrt (energy z) * loadGradient z := by
    intro z hz
    have hintNested : HasIntegrableCoarseBlock P
        (adaptedCellAt q k (nestedLabel k s z w)) :=
      hcells (hks.trans hst) le_rfl
          (Or.inr rfl) (hmem z hz)
    exact half_integral_cellPairings_primal_le_of_integrable_energy
      hq (hks.trans hst) (hmem z hz) g hg p r Pcen Qcen hintNested
      (integrable_cellQuarterEnergy_subSkew_of_finiteAdaptedMean
        hq (hks.trans hst) (hmem z hz) hintt g hg p r)
  constructor
  · simpa only [hq, Z, pairFlux, energy, loadFlux,
      profileRowCellEnergy] using
      avsum_cellPair_le_sqrt_avsum_energy_mul_load
        (alignedIndex_nonempty hq hst) pairFlux energy loadFlux
        (profileSchurLoadFlux
          (profileHattedBlock g
            (annealedBlock P (adaptedCellAt q k w))) Qcen)
        henergy (profileSchurLoadFlux_nonneg _ _) hpathFlux
        (fun z hz ↦ (hcell z hz).1)
  · simpa only [hq, Z, pairGradient, energy, loadGradient,
      profileRowCellEnergy] using
      avsum_cellPair_le_sqrt_avsum_energy_mul_load
        (alignedIndex_nonempty hq hst) pairGradient energy loadGradient
        (profileSchurLoadGradient
          (profileHattedBlock g
            (annealedBlock P (adaptedCellAt q k w))) Pcen)
        henergy (profileSchurLoadGradient_nonneg _ _) hpathGradient
        (fun z hz ↦ (hcell z hz).2)

/-- The adjoint nested row pairing remains valid at every fine scale allowed
by the source-window telescope. -/
theorem nestedAnnealedCellPairings_adjoint_le_of_cells
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d}
    (hgrid : IsRoundedGrid l q)
    {s t : ℤ} (hls : l ≤ s) (hst : s ≤ t)
    (hcells : AlignedCellsIntegrable P q s t)
    (hblocks : ∀ k : ℤ, l ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    {k : ℤ} (hks : k ≤ s)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k s)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d) :
    avsum (alignedIndex q s t) (fun z ↦
        (1 / 2 : ℝ) * ∫ a, |vecDot Qcen
          (blockCellAverage
            (adaptedCellAt q k (nestedLabel k s z w))
            (diagonalWeakAdjointState
              (Recurrence.posDef_of_isRoundedGrid hgrid) t
              (a.subSkew g hg) p r)).1| ∂P) ≤
        profileRowCellEnergy P (Recurrence.posDef_of_isRoundedGrid hgrid) k s t w
            (fun a ↦ (a.subSkew g hg).transpose) p r *
          profileSchurLoadFlux
            (profileHattedAdjointBlock g
              (annealedBlock P (adaptedCellAt q k w))) Qcen ∧
      avsum (alignedIndex q s t) (fun z ↦
        (1 / 2 : ℝ) * ∫ a, |vecDot Pcen
          (blockCellAverage
            (adaptedCellAt q k (nestedLabel k s z w))
            (diagonalWeakAdjointState
              (Recurrence.posDef_of_isRoundedGrid hgrid) t
              (a.subSkew g hg) p r)).2| ∂P) ≤
        profileRowCellEnergy P (Recurrence.posDef_of_isRoundedGrid hgrid) k s t w
            (fun a ↦ (a.subSkew g hg).transpose) p r *
          profileSchurLoadGradient
            (profileHattedAdjointBlock g
              (annealedBlock P (adaptedCellAt q k w))) Pcen := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let Z := alignedIndex q s t
  let energy : (Fin d → ℤ) → ℝ := fun z ↦
    profileAnnealedCellEnergySq P hq k t
      (nestedLabel k s z w) (fun a ↦ (a.subSkew g hg).transpose) p r
  let loadFlux : (Fin d → ℤ) → ℝ := fun z ↦
    profileSchurLoadFlux
      (profileHattedAdjointBlock g
        (annealedBlock P (adaptedCellAt q k (nestedLabel k s z w)))) Qcen
  let loadGradient : (Fin d → ℤ) → ℝ := fun z ↦
    profileSchurLoadGradient
      (profileHattedAdjointBlock g
        (annealedBlock P (adaptedCellAt q k (nestedLabel k s z w)))) Pcen
  let pairFlux : (Fin d → ℤ) → ℝ := fun z ↦
    (1 / 2 : ℝ) * ∫ a, |vecDot Qcen
      (blockCellAverage (adaptedCellAt q k (nestedLabel k s z w))
        (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)).1| ∂P
  let pairGradient : (Fin d → ℤ) → ℝ := fun z ↦
    (1 / 2 : ℝ) * ∫ a, |vecDot Pcen
      (blockCellAverage (adaptedCellAt q k (nestedLabel k s z w))
        (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)).2| ∂P
  have hintRef : HasIntegrableCoarseBlock P (adaptedCellAt q k w) :=
    hcells hks hst (Or.inl rfl) hw
  have hmeasRef : HasMeasurableCoarseBlock P (adaptedCellAt q k w) :=
    fun i j ↦ (hintRef i j).aestronglyMeasurable
  have hmem : ∀ z ∈ Z,
      nestedLabel k s z w ∈ alignedIndex q k t := by
    intro z hz
    exact nestedLabel_mem_alignedIndex hq hks hst hw hz
  have henergy : ∀ z ∈ Z, 0 ≤ energy z := by
    intro z hz
    exact profileAnnealedCellEnergySq_nonneg P hq k t
      (nestedLabel k s z w) (fun a ↦ (a.subSkew g hg).transpose) p r
  have hpathFlux : ∀ z ∈ Z, loadFlux z =
      profileSchurLoadFlux
        (profileHattedAdjointBlock g
          (annealedBlock P (adaptedCellAt q k w))) Qcen := by
    intro z hz
    exact profileSchurLoadFlux_adjoint_nestedLabel_eq_of_parent_aligned
      hstat hgrid hks hls z w hmeasRef g Qcen
  have hpathGradient : ∀ z ∈ Z, loadGradient z =
      profileSchurLoadGradient
        (profileHattedAdjointBlock g
          (annealedBlock P (adaptedCellAt q k w))) Pcen := by
    intro z hz
    exact profileSchurLoadGradient_adjoint_nestedLabel_eq_of_parent_aligned
      hstat hgrid hks hls z w hmeasRef g Pcen
  have hintt : HasFiniteAdaptedMean P q t :=
    (hblocks t (hls.trans hst) le_rfl).1
  have hcell : ∀ z ∈ Z,
      pairFlux z ≤ Real.sqrt (energy z) * loadFlux z ∧
      pairGradient z ≤ Real.sqrt (energy z) * loadGradient z := by
    intro z hz
    have hintNested : HasIntegrableCoarseBlock P
        (adaptedCellAt q k (nestedLabel k s z w)) :=
      hcells (hks.trans hst) le_rfl
          (Or.inr rfl) (hmem z hz)
    exact half_integral_cellPairings_adjoint_le_of_integrable_energy
      hq (hks.trans hst) (hmem z hz) g hg p r Pcen Qcen hintNested
      (integrable_cellQuarterEnergy_adjointSubSkew_of_finiteAdaptedMean
        hq (hks.trans hst) (hmem z hz) hintt g hg p r)
  constructor
  · simpa only [hq, Z, pairFlux, energy, loadFlux,
      profileRowCellEnergy] using
      avsum_cellPair_le_sqrt_avsum_energy_mul_load
        (alignedIndex_nonempty hq hst) pairFlux energy loadFlux
        (profileSchurLoadFlux
          (profileHattedAdjointBlock g
            (annealedBlock P (adaptedCellAt q k w))) Qcen)
        henergy (profileSchurLoadFlux_nonneg _ _) hpathFlux
        (fun z hz ↦ (hcell z hz).1)
  · simpa only [hq, Z, pairGradient, energy, loadGradient,
      profileRowCellEnergy] using
      avsum_cellPair_le_sqrt_avsum_energy_mul_load
        (alignedIndex_nonempty hq hst) pairGradient energy loadGradient
        (profileSchurLoadGradient
          (profileHattedAdjointBlock g
            (annealedBlock P (adaptedCellAt q k w))) Pcen)
        henergy (profileSchurLoadGradient_nonneg _ _) hpathGradient
        (fun z hz ↦ (hcell z hz).2)

end

end HCPolySupport.HighContrast.Response.FixedGrid
