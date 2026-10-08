/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedLinearOscillation
public import LeanPool.HighContrastHomogenization.Provider.Response.LinearOscillationDuality
public import LeanPool.HighContrastHomogenization.Provider.Response.LocalizedOptimizerObservables
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalProjectionGeometry

/-!
# High-contrast homogenization: Provider.Response.PreYoungPrimalProjectionMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

theorem measurable_cubeProjection (Q : TriadicCube d) (N : ℕ)
    (f : Vec d → ℝ) : Measurable (cubeProjection Q N f) := by
  classical
  unfold cubeProjection
  exact Finset.measurable_sum _ fun R _ ↦
    Measurable.ite (measurableSet_cubeSet R) measurable_const measurable_const

theorem memScalarL2_indicator_pulled_cubeProjection_cutoff
    [NeZero d] {q : Mat d} (hq : q.PosDef) {s t : ℤ}
    (z : Fin d → ℤ) (N : ℕ) :
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let eta : Vec d → ℝ := fun x ↦ cubeProjection R N f (matVecMul q⁻¹ x)
    MemScalarL2 (adaptedCell q t)
      (Set.indicator (adaptedCellAt q s z) eta) := by
  dsimp only
  let R : TriadicCube d := translateCube z (originCube d s)
  let phi : Vec d → ℝ := fun y ↦
    adaptedPreYoungCutoff q hq t (matVecMul q y)
  let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
  let eta : Vec d → ℝ := fun x ↦ cubeProjection R N f (matVecMul q⁻¹ x)
  have hphiCont : Continuous phi :=
    (adaptedPreYoungCutoff_smooth hq t).continuous.comp (continuous_matVecMul q)
  have hphiInt : IntegrableOn phi (cubeSet R) volume :=
    (hphiCont.continuousOn.integrableOn_compact
      (isBounded_cubeSet R).isCompact_closure).mono_set subset_closure
  have hphiAvg0 : 0 ≤ cubeAverage R phi :=
    le_cubeAverage_of_le R hphiInt
      (fun y ↦ adaptedPreYoungCutoff_nonneg hq t _)
  have hphiAvg2 : cubeAverage R phi ≤ 2 :=
    cubeAverage_le_of_le R hphiInt
      (fun y ↦ adaptedPreYoungCutoff_le_two hq t _)
  have hfBound : ∀ y ∈ cubeSet R, |f y| ≤ 2 := by
    intro y hy
    dsimp only [f, phi]
    rw [abs_le]
    constructor <;>
      linarith only [adaptedPreYoungCutoff_nonneg hq t (matVecMul q y),
        adaptedPreYoungCutoff_le_two hq t (matVecMul q y),
        hphiAvg0, hphiAvg2]
  have hprojBound : ∀ y, |cubeProjection R N f y| ≤ 2 := by
    intro y
    by_cases hy : y ∈ cubeSet R
    · exact cubeProjection_abs_le_of_abs_le_on_cubeSet R N f 2 hfBound y hy
    · rw [cubeProjection_eq_zero_of_not_mem_cubeSet R N f hy, abs_zero]
      norm_num
  have hetaMeas : Measurable eta :=
    (measurable_cubeProjection R N f).comp
      (continuous_matVecMul q⁻¹).measurable
  let : IsFiniteMeasure (volumeMeasureOn (adaptedCell q t)) :=
    (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isFiniteMeasure_restrict_volume
  refine MemLp.of_bound
    (hetaMeas.aestronglyMeasurable.indicator
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s z).isOpen.measurableSet)
    2 (_root_.Filter.Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ adaptedCellAt q s z
  · simpa only [Set.indicator_of_mem hx, Real.norm_eq_abs, eta] using
      hprojBound (matVecMul q⁻¹ x)
  · simp only [Set.indicator_of_notMem hx, norm_zero]
    norm_num

theorem cutoff_projected_primal_pairing_eq_weighted_average
    [NeZero d] {q : Mat d} (hq : q.PosDef) (s t : ℤ)
    (z : Fin d → ℤ) (F : Vec d → BlockVec d) (Qcen : Vec d)
    (N : ℕ)
    (hGInt : IntegrableOn (fun y ↦ vecDot Qcen (F (matVecMul q y)).1)
      (cubeSet (translateCube z (originCube d s))) volume) :
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
    let eta : Vec d → ℝ := fun x ↦ cubeProjection R N f (matVecMul q⁻¹ x)
    cubeBesovPairing R f (cubeProjection R N G) =
      volumeAverage (adaptedCellAt q s z)
        (fun x ↦ eta x * vecDot Qcen (F x).1) := by
  dsimp only
  let R : TriadicCube d := translateCube z (originCube d s)
  let phi : Vec d → ℝ := fun y ↦
    adaptedPreYoungCutoff q hq t (matVecMul q y)
  let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
  let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
  let eta : Vec d → ℝ := fun x ↦ cubeProjection R N f (matVecMul q⁻¹ x)
  have hphiCont : Continuous phi :=
    (adaptedPreYoungCutoff_smooth hq t).continuous.comp (continuous_matVecMul q)
  have hfInt : IntegrableOn f (cubeSet R) volume := by
    exact ((hphiCont.continuousOn.integrableOn_compact
      (isBounded_cubeSet R).isCompact_closure).mono_set subset_closure).sub
        (integrableOn_const (volume_cubeSet_lt_top R).ne)
  rw [volumeAverage_adaptedCellAt_eq_cubeAverage_pullback hq]
  rw [← cubeBesovPairing_projection_comm R N f G hfInt hGInt]
  unfold cubeBesovPairing
  apply congrArg (cubeAverage R)
  funext y
  dsimp only [eta, G]
  have hdet : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  rw [matVecMul_mul, Matrix.nonsing_inv_mul q hdet, matVecMul_one]

theorem measurable_volumeAverage_weighted_vecDot_primal
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {z : Fin d → ℤ} (hz : z ∈ alignedIndex q s t)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d)
    {eta : Vec d → ℝ}
    (heta : MemScalarL2 (adaptedCell q t)
      (Set.indicator (adaptedCellAt q s z) eta)) :
    Measurable fun a : CoeffSpace d ↦
      volumeAverage (adaptedCellAt q s z) (fun x ↦
        eta x * vecDot Qcen
          (diagonalWeakState hq t (a.subSkew g hg) p r x).1) := by
  let V : Set (Vec d) := adaptedCellAt q s z
  let X : CoeffSpace d → Vec d → BlockVec d := fun a ↦
    diagonalWeakState hq t (a.subSkew g hg) p r
  have hVU : V ⊆ adaptedCell q t :=
    adaptedCellAt_subset_of_mem_alignedIndex hq hst hz
  have hcoordMeas : ∀ i : Fin d, Measurable fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ eta x * (X a x).1 i) := by
    intro i
    simpa only [V, X, toFullBlockVec] using
      Selection.measurable_volumeAverage_weighted_diagonalWeakState_subSkew
        hq t g hg p r (Sum.inl i)
        (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s z).isOpen.measurableSet
        hVU heta
  have hcoordInt : ∀ a : CoeffSpace d, ∀ i : Fin d,
      IntegrableOn (fun x ↦ eta x * (X a x).1 i) V volume := by
    intro a i
    obtain ⟨hgrad, _hflux⟩ :=
      diagonalWeakState_memVectorL2 hq t (a.subSkew g hg) p r
    have hprod : Integrable
        (fun x ↦ Set.indicator V eta x * (X a x).1 i)
        (volumeMeasureOn (adaptedCell q t)) :=
      MemLp.integrable_mul heta (by
        simpa only [X] using hgrad.eval i)
    have hprodV := hprod.mono_measure
      (Measure.restrict_mono hVU le_rfl)
    change Integrable (fun x ↦ eta x * (X a x).1 i)
      (volume.restrict V)
    refine hprodV.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s z).isOpen.measurableSet]
      with x hx
    simp only [Set.indicator_of_mem hx]
  have hrewrite : (fun a : CoeffSpace d ↦
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
        intro i hi
        ring
      _ = vecDot Qcen
          (fun i ↦ volumeAverage V (fun x ↦ eta x * (X a x).1 i)) :=
        volumeAverage_vecDot_left (U := V) Qcen
          (fun x i ↦ eta x * (X a x).1 i) (hcoordInt a)
  rw [show (fun a : CoeffSpace d ↦
      volumeAverage (adaptedCellAt q s z) (fun x ↦
        eta x * vecDot Qcen
          (diagonalWeakState hq t (a.subSkew g hg) p r x).1)) =
      fun a ↦ volumeAverage V
        (fun x ↦ eta x * vecDot Qcen (X a x).1) by rfl]
  rw [hrewrite]
  unfold vecDot
  exact Finset.measurable_sum _ fun i _ ↦
    measurable_const.mul (hcoordMeas i)

theorem aestronglyMeasurable_cutoff_projected_primal_pairing_subSkew
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
        diagonalWeakState hq t (a.subSkew g hg) p r
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
  have hweighted : Measurable fun a : CoeffSpace d ↦
      volumeAverage (adaptedCellAt q s z) (fun x ↦
        eta x * vecDot Qcen
          (diagonalWeakState hq t (a.subSkew g hg) p r x).1) :=
    measurable_volumeAverage_weighted_vecDot_primal
      hq hst hz g hg p r Qcen heta
  have heq : (fun a : CoeffSpace d ↦
      let R : TriadicCube d := translateCube z (originCube d s)
      let phi : Vec d → ℝ := fun y ↦
        adaptedPreYoungCutoff q hq t (matVecMul q y)
      let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
      let F : Vec d → BlockVec d :=
        diagonalWeakState hq t (a.subSkew g hg) p r
      let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
      cubeBesovPairing R f (cubeProjection R N G)) =
      fun a ↦ volumeAverage (adaptedCellAt q s z) (fun x ↦
        eta x * vecDot Qcen
          (diagonalWeakState hq t (a.subSkew g hg) p r x).1) := by
    funext a
    have hGInt : IntegrableOn (fun y ↦ vecDot Qcen
        (diagonalWeakState hq t (a.subSkew g hg) p r (matVecMul q y)).1)
        (cubeSet R) volume := by
      obtain ⟨hgrad, _hflux⟩ :=
        diagonalWeakState_memVectorL2 hq t (a.subSkew g hg) p r
      have hsub := adaptedCellAt_subset_of_mem_alignedIndex hq hst hz
      have hqdet : IsUnit q.det :=
        (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
      have hU : MeasurableSet (adaptedCellAt q s z) :=
        (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s z).isOpen.measurableSet
      have hpull := memVectorL2_affinePullback hqdet hU
        (memVectorL2_mono hsub hgrad)
      rw [matImage_inv_adaptedCellAt_eq hq s z] at hpull
      have hidentityCell : adaptedCellAt (1 : Mat d) s z = openCubeSet R := by
        dsimp only [R]
        rw [Recurrence.adaptedCellAt_eq_image]
        have hone : matVecMul (1 : Mat d) = id :=
          funext fun x ↦ matVecMul_one x
        rw [hone, Set.image_id]
        rfl
      have hi : ∀ i, IntegrableOn (fun y ↦
          (diagonalWeakState hq t (a.subSkew g hg) p r (matVecMul q y)).1 i)
          (cubeSet R) volume := by
        intro i
        have hiOpen := integrableOn_component
          (U := adaptedDomainAt Matrix.PosDef.one s z) hpull i
        change Integrable (fun y ↦
          (diagonalWeakState hq t (a.subSkew g hg) p r (matVecMul q y)).1 i)
          (volume.restrict (cubeSet R))
        rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
        simpa only [adaptedDomainAt_carrier, hidentityCell] using! hiOpen
      simpa only [vecDot] using! integrable_finsetSum
        (s := (Finset.univ : Finset (Fin d)))
        (fun i hiMem ↦ (hi i).const_mul (Qcen i))
    simpa only [R, phi, f, eta] using
      cutoff_projected_primal_pairing_eq_weighted_average
        hq s t z
        (diagonalWeakState hq t (a.subSkew g hg) p r) Qcen N hGInt
  rw [heq]
  exact hweighted.aestronglyMeasurable

end

end HCPolySupport.HighContrast.Response
