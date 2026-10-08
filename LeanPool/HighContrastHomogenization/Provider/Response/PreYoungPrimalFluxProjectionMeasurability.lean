/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalFluxProjectionGeometry
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalProjectionMeasurability

/-!
# High-contrast homogenization: Provider.Response.PreYoungPrimalFluxProjectionMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Measurability of projected primal flux pairings

Finite cube projections of the cutoff pull back to bounded scalar weights on
each adapted parent cell.  The measurable-selection API for the optimizer
therefore makes the projected scalar flux pairing measurable in the
coefficient sample.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A projected scalar flux pairing is its weighted physical-cell average. -/
theorem cutoff_projected_primal_flux_pairing_eq_weighted_average
    [NeZero d] {q : Mat d} (hq : q.PosDef) (s t : ℤ)
    (z : Fin d → ℤ) (F : Vec d → BlockVec d) (Pcen : Vec d)
    (N : ℕ)
    (hGInt : IntegrableOn (fun y ↦ vecDot Pcen (F (matVecMul q y)).2)
      (cubeSet (translateCube z (originCube d s))) volume) :
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let G : Vec d → ℝ := fun y ↦ vecDot Pcen (F (matVecMul q y)).2
    let eta : Vec d → ℝ := fun x ↦ cubeProjection R N f (matVecMul q⁻¹ x)
    cubeBesovPairing R f (cubeProjection R N G) =
      volumeAverage (adaptedCellAt q s z)
        (fun x ↦ eta x * vecDot Pcen (F x).2) := by
  simpa only using
    (cutoff_projected_primal_pairing_eq_weighted_average hq s t z
      (fun x ↦ ((F x).2, (F x).1)) Pcen N hGInt)

/-- A weighted primal flux average over an aligned cell is measurable in the
coefficient sample. -/
theorem measurable_volumeAverage_weighted_vecDot_primal_flux
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {z : Fin d → ℤ} (hz : z ∈ alignedIndex q s t)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d)
    {eta : Vec d → ℝ}
    (heta : MemScalarL2 (adaptedCell q t)
      (Set.indicator (adaptedCellAt q s z) eta)) :
    Measurable fun a : CoeffSpace d ↦
      volumeAverage (adaptedCellAt q s z) (fun x ↦
        eta x * vecDot Pcen
          (diagonalWeakState hq t (a.subSkew g hg) p r x).2) := by
  let V : Set (Vec d) := adaptedCellAt q s z
  let X : CoeffSpace d → Vec d → BlockVec d := fun a ↦
    diagonalWeakState hq t (a.subSkew g hg) p r
  have hVU : V ⊆ adaptedCell q t :=
    adaptedCellAt_subset_of_mem_alignedIndex hq hst hz
  have hcoordMeas : ∀ i : Fin d, Measurable fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ eta x * (X a x).2 i) := by
    intro i
    simpa only [V, X, toFullBlockVec] using
      Selection.measurable_volumeAverage_weighted_diagonalWeakState_subSkew
        hq t g hg p r (Sum.inr i)
        (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s z).isOpen.measurableSet
        hVU heta
  have hcoordInt : ∀ a : CoeffSpace d, ∀ i : Fin d,
      IntegrableOn (fun x ↦ eta x * (X a x).2 i) V volume := by
    intro a i
    obtain ⟨_hgrad, hflux⟩ :=
      diagonalWeakState_memVectorL2 hq t (a.subSkew g hg) p r
    have hprod : Integrable
        (fun x ↦ Set.indicator V eta x * (X a x).2 i)
        (volumeMeasureOn (adaptedCell q t)) :=
      MemLp.integrable_mul heta (by simpa only [X] using hflux.eval i)
    have hprodV := hprod.mono_measure
      (Measure.restrict_mono hVU le_rfl)
    change Integrable (fun x ↦ eta x * (X a x).2 i)
      (volume.restrict V)
    refine hprodV.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s z).isOpen.measurableSet]
      with x hx
    simp only [Set.indicator_of_mem hx]
  have hrewrite : (fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ eta x * vecDot Pcen (X a x).2)) =
      fun a ↦ vecDot Pcen
        (fun i ↦ volumeAverage V (fun x ↦ eta x * (X a x).2 i)) := by
    funext a
    calc
      volumeAverage V (fun x ↦ eta x * vecDot Pcen (X a x).2) =
          volumeAverage V (fun x ↦
            vecDot Pcen (fun i ↦ eta x * (X a x).2 i)) := by
        apply congrArg (volumeAverage V)
        funext x
        simp only [vecDot, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = vecDot Pcen
          (fun i ↦ volumeAverage V (fun x ↦ eta x * (X a x).2 i)) :=
        volumeAverage_vecDot_left (U := V) Pcen
          (fun x i ↦ eta x * (X a x).2 i) (hcoordInt a)
  rw [show (fun a : CoeffSpace d ↦
      volumeAverage (adaptedCellAt q s z) (fun x ↦
        eta x * vecDot Pcen
          (diagonalWeakState hq t (a.subSkew g hg) p r x).2)) =
      fun a ↦ volumeAverage V
        (fun x ↦ eta x * vecDot Pcen (X a x).2) by rfl]
  rw [hrewrite]
  unfold vecDot
  exact Finset.measurable_sum _ fun i _ ↦
    measurable_const.mul (hcoordMeas i)

/-- The finite-depth primal flux pairing is strongly measurable in the
coefficient sample. -/
theorem aestronglyMeasurable_cutoff_projected_primal_flux_pairing_subSkew
    [NeZero d] {P : Measure (CoeffSpace d)}
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {z : Fin d → ℤ} (hz : z ∈ alignedIndex q s t)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d) (N : ℕ) :
    AEStronglyMeasurable (fun a : CoeffSpace d ↦
      let R : TriadicCube d := translateCube z (originCube d s)
      let phi : Vec d → ℝ := fun y ↦
        adaptedPreYoungCutoff q hq t (matVecMul q y)
      let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
      let F : Vec d → BlockVec d :=
        diagonalWeakState hq t (a.subSkew g hg) p r
      let G : Vec d → ℝ := fun y ↦ vecDot Pcen (F (matVecMul q y)).2
      cubeBesovPairing R f (cubeProjection R N G)) P := by
  let R : TriadicCube d := translateCube z (originCube d s)
  let phi : Vec d → ℝ := fun y ↦
    adaptedPreYoungCutoff q hq t (matVecMul q y)
  let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
  let eta : Vec d → ℝ := fun x ↦ cubeProjection R N f (matVecMul q⁻¹ x)
  have heta : MemScalarL2 (adaptedCell q t)
      (Set.indicator (adaptedCellAt q s z) eta) := by
    simpa only [R, phi, f, eta] using
      memScalarL2_indicator_pulled_cubeProjection_cutoff hq z N
  have hweighted : Measurable fun a : CoeffSpace d ↦
      volumeAverage (adaptedCellAt q s z) (fun x ↦
        eta x * vecDot Pcen
          (diagonalWeakState hq t (a.subSkew g hg) p r x).2) :=
    measurable_volumeAverage_weighted_vecDot_primal_flux
      hq hst hz g hg p r Pcen heta
  have heq : (fun a : CoeffSpace d ↦
      let R : TriadicCube d := translateCube z (originCube d s)
      let phi : Vec d → ℝ := fun y ↦
        adaptedPreYoungCutoff q hq t (matVecMul q y)
      let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
      let F : Vec d → BlockVec d :=
        diagonalWeakState hq t (a.subSkew g hg) p r
      let G : Vec d → ℝ := fun y ↦ vecDot Pcen (F (matVecMul q y)).2
      cubeBesovPairing R f (cubeProjection R N G)) =
      fun a ↦ volumeAverage (adaptedCellAt q s z) (fun x ↦
        eta x * vecDot Pcen
          (diagonalWeakState hq t (a.subSkew g hg) p r x).2) := by
    funext a
    have hGInt := integrableOn_vecDot_diagonalWeakState_flux_pullback
      hq hst hz (a.subSkew g hg) p r Pcen
    simpa only [R, phi, f, eta] using
      cutoff_projected_primal_flux_pairing_eq_weighted_average
        hq s t z (diagonalWeakState hq t (a.subSkew g hg) p r)
          Pcen N hGInt
  rw [heq]
  exact hweighted.aestronglyMeasurable

end

end HCPolySupport.HighContrast.Response
