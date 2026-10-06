/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungAdjointProjectionGeometry
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalFluxProjectionMeasurability

/-!
# High-contrast homogenization: Provider.Response.PreYoungAdjointProjectionMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Measurability of projected adjoint pairings

The pulled-back finite cutoff projection is a bounded scalar weight.  Applying
the adjoint measurable-selection readout on each coordinate and recombining
the finite coordinate sum proves strong measurability of both scalar adjoint
pairings.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A weighted adjoint gradient average is strongly measurable in the
coefficient sample. -/
theorem aestronglyMeasurable_volumeAverage_weighted_vecDot_adjoint_gradient
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    {s t : ℤ} (hst : s ≤ t) {z : Fin d → ℤ}
    (hz : z ∈ alignedIndex q s t)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d)
    {eta : Vec d → ℝ}
    (heta : MemScalarL2 (adaptedCell q t)
      (Set.indicator (adaptedCellAt q s z) eta)) :
    AEStronglyMeasurable (fun a : CoeffSpace d ↦
      volumeAverage (adaptedCellAt q s z) (fun x ↦
        eta x * vecDot Qcen
          (diagonalWeakAdjointState hq t (a.subSkew g hg) p r x).1)) P := by
  let V : Set (Vec d) := adaptedCellAt q s z
  let X : CoeffSpace d → Vec d → BlockVec d := fun a ↦
    diagonalWeakAdjointState hq t (a.subSkew g hg) p r
  have hcoordMeas : ∀ i : Fin d, AEStronglyMeasurable
      (fun a : CoeffSpace d ↦
        volumeAverage V (fun x ↦ eta x * (X a x).1 i)) P := by
    intro i
    simpa only [V, X, toFullBlockVec] using
      Selection.aestronglyMeasurable_weightedCellAverage_diagonalAdjointState
        hq hst P g hg p r hz (Sum.inl i) heta
  have hVU : V ⊆ adaptedCell q t :=
    adaptedCellAt_subset_of_mem_alignedIndex hq hst hz
  have hcoordInt : ∀ a : CoeffSpace d, ∀ i : Fin d,
      IntegrableOn (fun x ↦ eta x * (X a x).1 i) V volume := by
    intro a i
    obtain ⟨hgrad, _hflux⟩ := diagonalWeakState_memVectorL2 hq t
      ((a.subSkew g hg).transpose) p r
    have hprod : Integrable
        (fun x ↦ Set.indicator V eta x * (X a x).1 i)
        (volumeMeasureOn (adaptedCell q t)) :=
      MemLp.integrable_mul heta (by
        simpa only [X, diagonalWeakAdjointState] using hgrad.eval i)
    have hprodV := hprod.mono_measure
      (Measure.restrict_mono hVU le_rfl)
    change Integrable (fun x ↦ eta x * (X a x).1 i)
      (volume.restrict V)
    refine hprodV.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s z).isOpen.measurableSet]
      with x hx
    simp only [Set.indicator_of_mem hx]
  have heq : (fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ eta x * vecDot Qcen (X a x).1)) =
      fun a ↦ vecDot Qcen
        (fun i ↦ volumeAverage V (fun x ↦ eta x * (X a x).1 i)) := by
    funext a
    calc
      volumeAverage V (fun x ↦ eta x * vecDot Qcen (X a x).1) =
          volumeAverage V (fun x ↦
            vecDot Qcen (fun i ↦ eta x * (X a x).1 i)) := by
        apply congrArg (volumeAverage V)
        funext x
        simp only [vecDot, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = vecDot Qcen
          (fun i ↦ volumeAverage V (fun x ↦ eta x * (X a x).1 i)) :=
        volumeAverage_vecDot_left (U := V) Qcen
          (fun x i ↦ eta x * (X a x).1 i) (hcoordInt a)
  rw [show (fun a : CoeffSpace d ↦
      volumeAverage (adaptedCellAt q s z) (fun x ↦
        eta x * vecDot Qcen
          (diagonalWeakAdjointState hq t (a.subSkew g hg) p r x).1)) =
      fun a ↦ volumeAverage V
        (fun x ↦ eta x * vecDot Qcen (X a x).1) by rfl]
  rw [heq]
  unfold vecDot
  exact Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ ↦
    (hcoordMeas i).const_mul (Qcen i)

/-- A weighted adjoint flux average is strongly measurable in the coefficient
sample. -/
theorem aestronglyMeasurable_volumeAverage_weighted_vecDot_adjoint_flux
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    {s t : ℤ} (hst : s ≤ t) {z : Fin d → ℤ}
    (hz : z ∈ alignedIndex q s t)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d)
    {eta : Vec d → ℝ}
    (heta : MemScalarL2 (adaptedCell q t)
      (Set.indicator (adaptedCellAt q s z) eta)) :
    AEStronglyMeasurable (fun a : CoeffSpace d ↦
      volumeAverage (adaptedCellAt q s z) (fun x ↦
        eta x * vecDot Pcen
          (diagonalWeakAdjointState hq t (a.subSkew g hg) p r x).2)) P := by
  let V : Set (Vec d) := adaptedCellAt q s z
  let X : CoeffSpace d → Vec d → BlockVec d := fun a ↦
    diagonalWeakAdjointState hq t (a.subSkew g hg) p r
  have hcoordMeas : ∀ i : Fin d, AEStronglyMeasurable
      (fun a : CoeffSpace d ↦
        volumeAverage V (fun x ↦ eta x * (X a x).2 i)) P := by
    intro i
    simpa only [V, X, toFullBlockVec] using
      Selection.aestronglyMeasurable_weightedCellAverage_diagonalAdjointState
        hq hst P g hg p r hz (Sum.inr i) heta
  have hVU : V ⊆ adaptedCell q t :=
    adaptedCellAt_subset_of_mem_alignedIndex hq hst hz
  have hcoordInt : ∀ a : CoeffSpace d, ∀ i : Fin d,
      IntegrableOn (fun x ↦ eta x * (X a x).2 i) V volume := by
    intro a i
    obtain ⟨_hgrad, hflux⟩ := diagonalWeakState_memVectorL2 hq t
      ((a.subSkew g hg).transpose) p r
    have hprod : Integrable
        (fun x ↦ Set.indicator V eta x * (X a x).2 i)
        (volumeMeasureOn (adaptedCell q t)) :=
      MemLp.integrable_mul heta (by
        simpa only [X, diagonalWeakAdjointState] using hflux.eval i)
    have hprodV := hprod.mono_measure
      (Measure.restrict_mono hVU le_rfl)
    change Integrable (fun x ↦ eta x * (X a x).2 i)
      (volume.restrict V)
    refine hprodV.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s z).isOpen.measurableSet]
      with x hx
    simp only [Set.indicator_of_mem hx]
  have heq : (fun a : CoeffSpace d ↦
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
          (diagonalWeakAdjointState hq t (a.subSkew g hg) p r x).2)) =
      fun a ↦ volumeAverage V
        (fun x ↦ eta x * vecDot Pcen (X a x).2) by rfl]
  rw [heq]
  unfold vecDot
  exact Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ ↦
    (hcoordMeas i).const_mul (Pcen i)

/-- The finite-depth adjoint gradient pairing is strongly measurable in the
coefficient sample. -/
theorem aestronglyMeasurable_cutoff_projected_adjoint_gradient_pairing_subSkew
    [NeZero d] {P : Measure (CoeffSpace d)}
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {z : Fin d → ℤ} (hz : z ∈ alignedIndex q s t)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d) (N : ℕ) :
    AEStronglyMeasurable (fun a : CoeffSpace d ↦
      let R : TriadicCube d := translateCube z (originCube d s)
      let phi : Vec d → ℝ := fun y ↦
        adaptedPreYoungCutoff q hq t (matVecMul q y)
      let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
      let F : Vec d → BlockVec d :=
        diagonalWeakAdjointState hq t (a.subSkew g hg) p r
      let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
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
  have hweighted :=
    aestronglyMeasurable_volumeAverage_weighted_vecDot_adjoint_gradient
      (P := P) hq hst hz g hg p r Qcen heta
  have heq : (fun a : CoeffSpace d ↦
      let R : TriadicCube d := translateCube z (originCube d s)
      let phi : Vec d → ℝ := fun y ↦
        adaptedPreYoungCutoff q hq t (matVecMul q y)
      let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
      let F : Vec d → BlockVec d :=
        diagonalWeakAdjointState hq t (a.subSkew g hg) p r
      let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
      cubeBesovPairing R f (cubeProjection R N G)) =
      fun a ↦ volumeAverage (adaptedCellAt q s z) (fun x ↦
        eta x * vecDot Qcen
          (diagonalWeakAdjointState hq t (a.subSkew g hg) p r x).1) := by
    funext a
    have hGInt := integrableOn_vecDot_diagonalWeakAdjointState_pullback
      hq hst hz (a.subSkew g hg) p r Qcen
    simpa only [R, phi, f, eta] using
      cutoff_projected_primal_pairing_eq_weighted_average hq s t z
        (diagonalWeakAdjointState hq t (a.subSkew g hg) p r) Qcen N hGInt
  rw [heq]
  exact hweighted

/-- The finite-depth adjoint flux pairing is strongly measurable in the
coefficient sample. -/
theorem aestronglyMeasurable_cutoff_projected_adjoint_flux_pairing_subSkew
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
        diagonalWeakAdjointState hq t (a.subSkew g hg) p r
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
  have hweighted :=
    aestronglyMeasurable_volumeAverage_weighted_vecDot_adjoint_flux
      (P := P) hq hst hz g hg p r Pcen heta
  have heq : (fun a : CoeffSpace d ↦
      let R : TriadicCube d := translateCube z (originCube d s)
      let phi : Vec d → ℝ := fun y ↦
        adaptedPreYoungCutoff q hq t (matVecMul q y)
      let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
      let F : Vec d → BlockVec d :=
        diagonalWeakAdjointState hq t (a.subSkew g hg) p r
      let G : Vec d → ℝ := fun y ↦ vecDot Pcen (F (matVecMul q y)).2
      cubeBesovPairing R f (cubeProjection R N G)) =
      fun a ↦ volumeAverage (adaptedCellAt q s z) (fun x ↦
        eta x * vecDot Pcen
          (diagonalWeakAdjointState hq t (a.subSkew g hg) p r x).2) := by
    funext a
    have hGInt := integrableOn_vecDot_diagonalWeakAdjointState_flux_pullback
      hq hst hz (a.subSkew g hg) p r Pcen
    simpa only [R, phi, f, eta] using
      cutoff_projected_primal_flux_pairing_eq_weighted_average hq s t z
        (diagonalWeakAdjointState hq t (a.subSkew g hg) p r) Pcen N hGInt
  rw [heq]
  exact hweighted

end

end HCPolySupport.HighContrast.Response
