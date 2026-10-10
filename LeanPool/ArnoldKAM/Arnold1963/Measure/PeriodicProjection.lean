/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.RealCover
public import LeanPool.ArnoldKAM.Arnold1963.Basic.Measure
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
Physical quotient volume with angle Haar mass 2 * pi. Countably many half-open cells
transfer covering-space volume to the quotient for sets on which projection is injective.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Function
open scoped ENNReal
namespace KamProject.Arnold1963
local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- All real actions paired with one half-open fundamental angle cell. -/
def phaseCell (n : ℕ) : Set (RealPhaseCover n) :=
  univ ×ˢ realAngleCell n (2 * Real.pi)

theorem measurableSet_phaseCell (n : ℕ) : MeasurableSet (phaseCell n) :=
  MeasurableSet.univ.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)

theorem continuous_torusProjection {n : ℕ} : Continuous (@torusProjection n) := by
  unfold torusProjection
  fun_prop

theorem torusProjection_injOn_cell {n : ℕ} : InjOn (@torusProjection n) (phaseCell n) := by
  intro x hx y hy he
  apply Prod.ext (show x.1 = y.1 from congrArg (fun z : RealPhaseSpace n => z.1) he)
  funext j
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ioc (p := 2 * Real.pi) (a := 0)
    (by simpa using hx.2 j (mem_univ j))
    (by simpa using hy.2 j (mem_univ j))).mp
  exact congrArg (fun z : RealPhaseSpace n => z.2 j) he

theorem torusRepresentative_mem_cell {n : ℕ} (x : RealPhaseSpace n) :
    torusRepresentative x ∈ phaseCell n := by
  refine ⟨mem_univ _, fun j _ => ?_⟩
  simpa [torusRepresentative] using (AddCircle.equivIoc (2 * Real.pi) 0 (x.2 j)).property

theorem torusProjection_measurePreserving (n : ℕ) :
    MeasurePreserving (@torusProjection n) (volume.restrict (phaseCell n)) volume := by
  have ha := measurePreserving_pi
    (fun _ : Fin n => (volume : Measure ℝ).restrict (Ioc 0 (2 * Real.pi)))
    (fun _ : Fin n => (volume : Measure (AddCircle (2 * Real.pi))))
    (fun _ => by simpa using AddCircle.measurePreserving_mk (2 * Real.pi) 0)
  rw [← Measure.restrict_pi_pi] at ha
  have hi : MeasurePreserving (id : RealSpace n → RealSpace n)
      (volume.restrict univ) volume := by simpa using MeasurePreserving.id volume
  have hh := hi.prod ha
  rw [Measure.prod_restrict] at hh
  exact hh

theorem realPhaseShift_eq_add {n : ℕ} (k : FourierIndex n) (x : RealPhaseCover n) :
    realPhaseShift k x = x + (0, realAngleShift k) := by
  ext <;> simp [realPhaseShift]

/-- The measurable equivalence translating unwrapped phase space by an integer angle-period
shift. -/
def phaseShiftEquiv {n : ℕ} (k : FourierIndex n) : RealPhaseCover n ≃ᵐ RealPhaseCover n :=
  MeasurableEquiv.addRight (0, realAngleShift k)

@[simp] theorem phaseShiftEquiv_apply {n : ℕ} (k : FourierIndex n) (x : RealPhaseCover n) :
    phaseShiftEquiv k x = realPhaseShift k x := (realPhaseShift_eq_add k x).symm

theorem phaseShift_measurePreserving {n : ℕ} (k : FourierIndex n) :
    MeasurePreserving (phaseShiftEquiv k) volume volume := by
  let : (volume : Measure (RealPhaseCover n)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  exact measurePreserving_add_right volume _

/-- The translated fundamental phase cell associated with an integer angle-period shift. -/
def translatedPhaseCell {n : ℕ} (k : FourierIndex n) : Set (RealPhaseCover n) :=
  phaseShiftEquiv k '' phaseCell n

theorem measurableSet_translatedPhaseCell {n : ℕ} (k : FourierIndex n) :
    MeasurableSet (translatedPhaseCell k) :=
  (phaseShiftEquiv k).measurableEmbedding.measurableSet_image.mpr (measurableSet_phaseCell n)

theorem translatedPhaseCell_cover (n : ℕ) :
    ⋃ k : FourierIndex n, translatedPhaseCell k = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨k, hk⟩ := (torusProjection_eq_iff x (torusRepresentative (torusProjection x))).mp
    (torusProjection_representative _).symm
  exact mem_iUnion.mpr ⟨k, torusRepresentative (torusProjection x),
    torusRepresentative_mem_cell _, by simpa using hk.symm⟩

theorem translatedPhaseCell_disjoint (n : ℕ) :
    Pairwise (Disjoint on (translatedPhaseCell (n := n))) := by
  intro k l hkl
  apply disjoint_left.mpr
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
  have hxy : y = x := torusProjection_injOn_cell hy hx (by
    simpa using congrArg torusProjection he)
  subst y
  apply hkl
  funext j
  have hj := congrArg (fun v : RealPhaseCover n => v.2 j) he
  simp only [phaseShiftEquiv_apply, realPhaseShift, Pi.add_apply, realAngleShift] at hj
  have hc : (l j : ℝ) = (k j : ℝ) := (mul_left_cancel₀
    (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))) (add_left_cancel hj)
  exact (Int.cast_injective hc).symm

theorem torusProjection_translated_measurePreserving {n : ℕ} (k : FourierIndex n) :
    MeasurePreserving (@torusProjection n) (volume.restrict (translatedPhaseCell k)) volume := by
  have he := (phaseShift_measurePreserving k).restrict_image_emb
    (phaseShiftEquiv k).measurableEmbedding (phaseCell n)
  apply (he.comp_right_iff).mp
  simpa only [Function.comp_def, phaseShiftEquiv_apply, torusProjection_shift] using
    torusProjection_measurePreserving n

theorem torusProjection_injOn_translated {n : ℕ} (k : FourierIndex n) :
    InjOn (@torusProjection n) (translatedPhaseCell k) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
  have hh := torusProjection_injOn_cell hx hy (by simpa using he)
  rw [hh]

theorem torusProjection_volume_piece {n : ℕ} {A : Set (RealPhaseCover n)}
    (hA : MeasurableSet A) (k : FourierIndex n) (hsub : A ⊆ translatedPhaseCell k) :
    volume (torusProjection '' A) = volume A := by
  have hi := torusProjection_injOn_translated k
  have hm := hA.image_of_continuousOn_injOn continuous_torusProjection.continuousOn (hi.mono hsub)
  have he := (torusProjection_translated_measurePreserving k).measure_preimage hm.nullMeasurableSet
  rw [Measure.restrict_apply (continuous_torusProjection.measurable hm)] at he
  have hs : torusProjection ⁻¹' (torusProjection '' A) ∩ translatedPhaseCell k = A := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, he⟩, hx⟩
      rwa [← hi (hsub hy) hx he]
    · intro hx
      exact ⟨mem_image_of_mem _ hx, hsub hx⟩
  rw [hs] at he
  exact he.symm

theorem torusProjection_volume {n : ℕ} {A : Set (RealPhaseCover n)}
    (hA : MeasurableSet A) (hi : InjOn torusProjection A) :
    volume (torusProjection '' A) = volume A := by
  let B := fun k : FourierIndex n => A ∩ translatedPhaseCell k
  have hB k : MeasurableSet (B k) := hA.inter (measurableSet_translatedPhaseCell k)
  have hu : ⋃ k, B k = A := by
    simp only [B, ← inter_iUnion, translatedPhaseCell_cover, inter_univ]
  have hd : Pairwise (Disjoint on B) := fun k l hkl =>
    (translatedPhaseCell_disjoint n hkl).mono inter_subset_right inter_subset_right
  have hdi : Pairwise (Disjoint on fun k => torusProjection '' B k) := by
    intro k l hkl
    apply disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    have hh := hi hy.1 hx.1 he
    exact disjoint_left.mp (hd hkl) hx (hh ▸ hy)
  rw [← hu, image_iUnion, measure_iUnion hdi]
  · rw [measure_iUnion hd hB]
    congr 1
    funext k
    exact torusProjection_volume_piece (hB k) k inter_subset_right
  · intro k
    exact (hB k).image_of_continuousOn_injOn continuous_torusProjection.continuousOn
      (hi.mono inter_subset_left)

theorem torusProjection_lipschitz {n : ℕ} : LipschitzWith 1 (@torusProjection n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, torusProjection, Prod.dist_eq]
  apply max_le (le_max_left _ _)
  apply (dist_pi_le_iff (le_trans dist_nonneg (le_max_right _ _))).mpr
  intro j
  have hh : dist (x.2 j : AddCircle (2 * Real.pi)) (y.2 j) ≤ dist (x.2 j) (y.2 j) := by
    simpa only [dist_eq_norm, ← AddCircle.coe_sub] using
      (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (2 * Real.pi))
        (m := x.2 j - y.2 j))
  exact hh.trans ((dist_le_pi_dist x.2 y.2 j).trans (le_max_right _ _))

end KamProject.Arnold1963
