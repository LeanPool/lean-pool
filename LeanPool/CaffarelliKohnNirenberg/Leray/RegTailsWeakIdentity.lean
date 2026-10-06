/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsTimeIdentity
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure

/-!
# The localized weak time identity for a compact spatial weight
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

local instance regTailsWeakIdentityNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance regTailsWeakIdentityNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

local instance (priority := 10000) regTailsWeakIdentityTopologicalSpace : TopologicalSpace ParabolicPoint :=
  instTopologicalSpaceProd

local instance regTailsWeakIdentityOpensMeasurableSpace : OpensMeasurableSpace ParabolicPoint :=
  inferInstanceAs (OpensMeasurableSpace (Vec3 × ℝ))

local instance regTailsWeakIdentityProductVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure Vec3) (volume : Measure ℝ)

private theorem regTails_compact_time_factor_integrable
    (F : ℝ → ℝ) (hF : ContinuousOn F (Ioi (0 : ℝ)))
    (χ : ℝ → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχI : tsupport χ ⊆ Ioi (0 : ℝ)) :
    Integrable (fun t : ℝ => F t * χ t) volume := by
  have hGlobal : Continuous (fun t : ℝ => F t * χ t) := by
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : 0 < t
    · exact (hF t ht).continuousAt (isOpen_Ioi.mem_nhds ht) |>.mul
        (hχ.continuousAt)
    · have htNot : t ∉ tsupport χ := by
        intro htχ
        exact (not_lt_of_ge (le_of_not_gt ht)) (hχI htχ)
      have hχzero : ∀ᶠ s : ℝ in 𝓝 t, χ s = 0 := by
        rw [notMem_tsupport_iff_eventuallyEq] at htNot
        exact htNot
      have hzero : ∀ᶠ s : ℝ in 𝓝 t, F s * χ s = 0 := by
        filter_upwards [hχzero] with s hs
        simp [hs]
      exact continuousAt_const.congr_of_eventuallyEq hzero
  have hSupport : Function.support (fun t : ℝ => F t * χ t) ⊆ tsupport χ := by
    intro t ht
    by_contra htn
    have hχt : χ t = 0 := by
      by_contra hne
      exact htn (subset_tsupport χ (Function.mem_support.mpr hne))
    exact (Function.mem_support.mp ht) (by simp [hχt])
  have hCompact : HasCompactSupport (fun t : ℝ => F t * χ t) :=
    hχc.of_isClosed_subset (isClosed_tsupport (f := fun t : ℝ => F t * χ t))
      (closure_minimal hSupport hχc.isCompact.isClosed)
  exact hGlobal.integrable_of_hasCompactSupport hCompact

/-- The compactly localized energy identity gives a distributional time
derivative for every smooth compact spatial weight. -/
theorem regTails_localized_weak_time_identity
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (J : ParabolicPoint → Vec3)
    (hLE : ∀ (ψ : ParabolicPoint → ℝ),
      ψ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioi 0) →
      2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          spatialGradientSq u
            (fun z i j => spatialPartial (fun y => u y i) j z) z * ψ z =
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          (vec3EuclideanNorm (u z)) ^ (2 : ℕ) *
              (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
            ∑ i : Fin 3,
              ((vec3EuclideanNorm (u z)) ^ (2 : ℕ) * J z i +
                2 * p z * u z i) * spatialPartial ψ i z)
    (hUcont : ∀ i : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => u (z.1, z.2) i)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hDcont : ∀ i j : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (fun y : ParabolicPoint => u y i) j z)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hPcont : ContinuousOn (fun z : Vec3 × ℝ => p (z.1, z.2))
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hJcont : ∀ i : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => J (z.1, z.2) i)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hUdiff : ∀ i : Fin 3, ContDiffOn ℝ 1
      (fun z : Vec3 × ℝ => u (z.1, z.2) i)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (q : Vec3 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqc : HasCompactSupport q)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηI : tsupport η ⊆ Ioi (0 : ℝ)) :
    (∫ t : ℝ, regTailsEnergyWeight u q t * deriv η t ∂volume) =
      -∫ t : ℝ,
        (∫ x : Vec3, regTailsLocalizedSource u
          (fun z i j => spatialPartial (fun y : ParabolicPoint => u y i) j z)
          p J q (x, t) ∂volume) * η t ∂volume := by
  classical
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
  let K : Set Vec3 := tsupport q
  let qj : Fin 3 → Vec3 → ℝ := fun j x => (fderiv ℝ q x) (basisVec j)
  let qjj : Fin 3 → Vec3 → ℝ := fun j x => (fderiv ℝ (qj j) x) (basisVec j)
  let qST : ParabolicPoint → ℝ := fun z => q z.1
  let Du : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
    spatialPartial (fun y : ParabolicPoint => u y i) j z
  let E : Vec3 × ℝ → ℝ := fun z =>
    (vec3EuclideanNorm (u (z.1, z.2))) ^ (2 : ℕ) * q z.1
  let H : Vec3 × ℝ → ℝ := fun z =>
    regTailsLocalizedSource u Du p J q (z.1, z.2)
  let F : ℝ → ℝ := regTailsEnergyWeight u q
  let G : ℝ → ℝ := fun t => ∫ x : Vec3, regTailsLocalizedSource u Du p J q (x, t)
  let B : Vec3 × ℝ → ℝ := fun z =>
    (vec3EuclideanNorm (u (z.1, z.2))) ^ (2 : ℕ) *
      ∑ j : Fin 3,
        spatialSecondPartial (fun y : ParabolicPoint => q y.1) j j (z.1, z.2)
  let V : Vec3 × ℝ → ℝ := fun z =>
    ∑ j : Fin 3,
      ((vec3EuclideanNorm (u (z.1, z.2))) ^ (2 : ℕ) *
          J (z.1, z.2) j +
        2 * p (z.1, z.2) * u (z.1, z.2) j) *
      spatialPartial (fun y : ParabolicPoint => q y.1) j (z.1, z.2)
  let Q : Vec3 × ℝ → ℝ := fun z =>
    spatialGradientSq u Du (z.1, z.2) * q z.1
  let C : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      u (z.1, z.2) i * Du (z.1, z.2) i j *
        spatialPartial (fun y : ParabolicPoint => q y.1) j (z.1, z.2)
  have hS : IsOpen S := isOpen_univ.prod isOpen_Ioi
  have hSmeas : MeasurableSet S := hS.measurableSet
  have hqST : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => q z.1) := by
    exact hq.comp (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff
  have hqjSmooth (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (qj j) := by
    change ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv q j)
    exact contDiff_spatialDeriv_smooth hq j
  have hqjjSmooth (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (qjj j) := by
    change ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv (qj j) j)
    exact contDiff_spatialDeriv_smooth (hqjSmooth j) j
  have hqjEq (j : Fin 3) (z : Vec3 × ℝ) :
      spatialPartial (fun y : ParabolicPoint => q y.1) j z = qj j z.1 := rfl
  have hqjjEq (j : Fin 3) (z : Vec3 × ℝ) :
      spatialSecondPartial (fun y : ParabolicPoint => q y.1) j j z =
        qjj j z.1 := rfl
  have hqjSupport (j : Fin 3) : tsupport (qj j) ⊆ K := by
    exact tsupport_fderiv_apply_subset ℝ (basisVec j)
  have hqpartial (j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial qST j (z.1, z.2)) S := by
    have hj : Continuous (qj j) := (hqjSmooth j).continuous
    have heq : (fun z : Vec3 × ℝ => spatialPartial qST j (z.1, z.2)) =
        fun z => qj j z.1 := by
      funext z
      rfl
    rw [heq]
    exact (hj.comp continuous_fst).continuousOn
  have hqZero (x : Vec3) (hx : x ∉ K) : q x = 0 := by
    by_contra hne
    exact hx (subset_tsupport q (Function.mem_support.mpr hne))
  have hqjZero (j : Fin 3) (x : Vec3) (hx : x ∉ K) : qj j x = 0 := by
    by_contra hne
    exact hx ((hqjSupport j) (subset_tsupport _ (Function.mem_support.mpr hne)))
  have hηd : ContDiff ℝ (⊤ : ℕ∞) (deriv η) := by
    exact (contDiff_infty_iff_deriv.mp hη).2
  have hηdCompact : HasCompactSupport (deriv η) := by
    have hfd := hηc.fderiv_apply (𝕜 := ℝ) (1 : ℝ)
    change HasCompactSupport (fun t : ℝ => fderiv ℝ η t (1 : ℝ))
    exact hfd
  have hηdI : tsupport (deriv η) ⊆ Ioi (0 : ℝ) :=
    (tsupport_deriv_subset (f := η)).trans hηI
  have hsourceContinuous : ContinuousOn H S := by
    have hUprod : ContinuousOn (fun z : Vec3 × ℝ =>
        u (z.1, z.2)) S := by
      apply continuousOn_pi.mpr
      intro i
      exact hUcont i
    have hDprod : ContinuousOn (fun z : Vec3 × ℝ =>
        Du (z.1, z.2)) S := by
      apply continuousOn_pi.mpr
      intro i
      apply continuousOn_pi.mpr
      intro j
      simpa [Du] using hDcont i j
    have hPprod : ContinuousOn (fun z : Vec3 × ℝ =>
        p (z.1, z.2)) S := hPcont
    have hJprod : ContinuousOn (fun z : Vec3 × ℝ =>
        J (z.1, z.2)) S := by
      apply continuousOn_pi.mpr
      intro i
      exact hJcont i
    unfold H regTailsLocalizedSource
    have hnorm : ContinuousOn
        (fun z : Vec3 × ℝ => vec3EuclideanNorm (u (z.1, z.2))) S :=
      (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.continuousOn).comp hUprod
        (fun z hz => Set.mem_univ (u (z.1, z.2)))
    have hqbase : ContinuousOn (fun z : Vec3 × ℝ => q z.1) S :=
      (hq.continuous.comp continuous_fst).continuousOn
    have hgrad : ContinuousOn
        (fun z : Vec3 × ℝ => spatialGradientSq u Du (z.1, z.2)) S := by
      unfold spatialGradientSq
      apply continuousOn_finsetSum
      intro i hi
      apply continuousOn_finsetSum
      intro j hj
      have hDij : ContinuousOn
          (fun z : Vec3 × ℝ => Du (z.1, z.2) i j) S := by
        simpa [Du] using hDcont i j
      exact hDij.pow 2
    have hfirst : ContinuousOn
        (fun z : Vec3 × ℝ => -2 * spatialGradientSq u Du (z.1, z.2) * q z.1) S := by
      exact (continuousOn_const.mul hgrad).mul hqbase
    have hsecondSum : ContinuousOn
        (fun z : Vec3 × ℝ => ∑ i : Fin 3, ∑ j : Fin 3,
          u (z.1, z.2) i * Du (z.1, z.2) i j *
            spatialPartial qST j (z.1, z.2)) S := by
      apply continuousOn_finsetSum
      intro i hi
      apply continuousOn_finsetSum
      intro j hj
      have hDij : ContinuousOn
          (fun z : Vec3 × ℝ => Du (z.1, z.2) i j) S := by
        simpa [Du] using hDcont i j
      exact ((hUcont i).mul hDij).mul (hqpartial j)
    have hsecond : ContinuousOn
        (fun z : Vec3 × ℝ => -(2 * ∑ i : Fin 3, ∑ j : Fin 3,
          u (z.1, z.2) i * Du (z.1, z.2) i j *
            spatialPartial qST j (z.1, z.2))) S :=
      (continuousOn_const.mul hsecondSum).neg
    have hthird : ContinuousOn
        (fun z : Vec3 × ℝ => ∑ j : Fin 3,
          (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * J (z.1, z.2) j +
            2 * p (z.1, z.2) * u (z.1, z.2) j) *
              spatialPartial qST j (z.1, z.2)) S := by
      apply continuousOn_finsetSum
      intro j hj
      exact ((hnorm.pow 2).mul (hJcont j)).add
        ((continuousOn_const.mul hPcont).mul (hUcont j)) |>.mul (hqpartial j)
    change ContinuousOn (fun z : Vec3 × ℝ =>
      -2 * spatialGradientSq u Du (z.1, z.2) * q z.1 -
        (2 * ∑ i : Fin 3, ∑ j : Fin 3,
          u (z.1, z.2) i * Du (z.1, z.2) i j *
            spatialPartial qST j (z.1, z.2)) +
        ∑ j : Fin 3,
          (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * J (z.1, z.2) j +
            2 * p (z.1, z.2) * u (z.1, z.2) j) *
              spatialPartial qST j (z.1, z.2)) S
    exact (hfirst.add hsecond).add hthird
  have hEcontinuous : ContinuousOn E S := by
    have hUprod : ContinuousOn (fun z : Vec3 × ℝ =>
        u (z.1, z.2)) S := by
      apply continuousOn_pi.mpr
      intro i
      exact hUcont i
    have hnorm : ContinuousOn (fun z : Vec3 × ℝ =>
        vec3EuclideanNorm (u (z.1, z.2))) S :=
      (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.continuousOn).comp hUprod
        (fun z hz => Set.mem_univ (u (z.1, z.2)))
    have hqprod : ContinuousOn (fun z : Vec3 × ℝ => q z.1) S :=
      (hq.continuous.comp continuous_fst).continuousOn
    exact hnorm.pow 2 |>.mul hqprod
  have hEzero : ∀ z : Vec3 × ℝ, 0 < z.2 → z.1 ∉ K → E z = 0 := by
    intro z ht hx
    simp [E, hqZero z.1 hx]
  have hHzero : ∀ z : Vec3 × ℝ, 0 < z.2 → z.1 ∉ K → H z = 0 := by
    intro z ht hx
    have hqpart (j : Fin 3) :
        spatialPartial (fun y : ParabolicPoint => q y.1) j (z.1, z.2) = 0 := by
      change qj j z.1 = 0
      exact hqjZero j z.1 hx
    simp [H, Du, regTailsLocalizedSource, hqZero z.1 hx, hqpart]
  have hEnergyInt : Integrable (fun z : Vec3 × ℝ => E z * deriv η z.2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    apply regTails_integrable_timeFactor_of_spatial_support E K hS hEcontinuous
      hqc.isCompact hEzero (deriv η) hηd hηdCompact hηdI
  have hSourceInt : Integrable (fun z : Vec3 × ℝ => H z * η z.2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    apply regTails_integrable_timeFactor_of_spatial_support H K hS hsourceContinuous
      hqc.isCompact hHzero η hη hηc hηI
  have hMeasure :
      (volume : Measure (Vec3 × ℝ)).restrict S =
        (volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))) := by
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict S = _
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Ioi (0 : ℝ))]
    simp [Measure.restrict_univ]
  have hUprod : ContinuousOn (fun z : Vec3 × ℝ => u (z.1, z.2)) S := by
    apply continuousOn_pi.mpr
    intro i
    exact hUcont i
  have hDprod : ContinuousOn (fun z : Vec3 × ℝ => Du (z.1, z.2)) S := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    simpa [Du] using hDcont i j
  have hPprod : ContinuousOn (fun z : Vec3 × ℝ => p (z.1, z.2)) S := hPcont
  have hJprod : ContinuousOn (fun z : Vec3 × ℝ => J (z.1, z.2)) S := by
    apply continuousOn_pi.mpr
    intro i
    exact hJcont i
  have hqjCont (j : Fin 3) :
      ContinuousOn (fun z : Vec3 × ℝ => qj j z.1) S := by
    have hj : Continuous (qj j) := (hqjSmooth j).continuous
    exact (hj.comp continuous_fst).continuousOn
  have hqjjCont (j : Fin 3) :
      ContinuousOn (fun z : Vec3 × ℝ => qjj j z.1) S := by
    have hj : Continuous (qjj j) := (hqjjSmooth j).continuous
    exact (hj.comp continuous_fst).continuousOn
  have hBcont : ContinuousOn B S := by
    unfold B
    have hnorm : ContinuousOn (fun z : Vec3 × ℝ =>
        vec3EuclideanNorm (u (z.1, z.2))) S :=
      (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.continuousOn).comp hUprod
        (fun z hz => Set.mem_univ (u (z.1, z.2)))
    have hsum : ContinuousOn (fun z : Vec3 × ℝ =>
        ∑ j : Fin 3,
          spatialSecondPartial (fun y : ParabolicPoint => q y.1) j j
            (z.1, z.2)) S := by
      apply continuousOn_finsetSum
      intro j hj
      exact (hqjjCont j).congr fun z hz => (hqjjEq j z).symm
    exact (hnorm.pow 2).mul hsum
  have hVcont : ContinuousOn V S := by
    unfold V
    apply continuousOn_finsetSum
    intro j hj
    have hnorm : ContinuousOn (fun z : Vec3 × ℝ =>
        vec3EuclideanNorm (u (z.1, z.2))) S :=
      (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.continuousOn).comp hUprod
        (fun z hz => Set.mem_univ (u (z.1, z.2)))
    have hcoord : ContinuousOn (fun z : Vec3 × ℝ =>
        (vec3EuclideanNorm (u (z.1, z.2))) ^ (2 : ℕ) *
            J (z.1, z.2) j +
          2 * p (z.1, z.2) * u (z.1, z.2) j) S := by
      exact ((hnorm.pow 2).mul (hJcont j)).add
        ((continuousOn_const.mul hPcont).mul (hUcont j))
    exact hcoord.mul (hqpartial j)
  have hQcont : ContinuousOn Q S := by
    unfold Q spatialGradientSq
    have hsum : ContinuousOn (fun z : Vec3 × ℝ =>
        ∑ i : Fin 3, ∑ j : Fin 3, (Du (z.1, z.2) i j) ^ (2 : ℕ)) S := by
      apply continuousOn_finsetSum
      intro i hi
      apply continuousOn_finsetSum
      intro j hj
      have hDij : ContinuousOn
          (fun z : Vec3 × ℝ => Du (z.1, z.2) i j) S := by
        simpa [Du] using hDcont i j
      exact hDij.pow 2
    exact hsum.mul ((hq.continuous.comp continuous_fst).continuousOn)
  have hCcont : ContinuousOn C S := by
    unfold C
    apply continuousOn_finsetSum
    intro i hi
    apply continuousOn_finsetSum
    intro j hj
    have hUi : ContinuousOn (fun z : Vec3 × ℝ => u (z.1, z.2) i) S := by
      exact continuous_apply i |>.comp_continuousOn hUprod
    have hDij : ContinuousOn (fun z : Vec3 × ℝ => Du (z.1, z.2) i j) S := by
      simpa [Du] using hDcont i j
    exact (hUi.mul hDij).mul (hqpartial j)
  have hqjjSupport (j : Fin 3) : tsupport (qjj j) ⊆ K := by
    exact (tsupport_fderiv_apply_subset ℝ (basisVec j)).trans (hqjSupport j)
  have hqjjZero (j : Fin 3) (x : Vec3) (hx : x ∉ K) : qjj j x = 0 := by
    by_contra hne
    exact hx (hqjjSupport j (subset_tsupport _ (Function.mem_support.mpr hne)))
  have hBzero : ∀ z : Vec3 × ℝ, 0 < z.2 → z.1 ∉ K → B z = 0 := by
    intro z ht hx
    have hsum : (∑ j : Fin 3,
        spatialSecondPartial (fun y : ParabolicPoint => q y.1) j j
          (z.1, z.2)) = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hqjjEq]; exact hqjjZero j z.1 hx
    simp [B, hsum]
  have hVzero : ∀ z : Vec3 × ℝ, 0 < z.2 → z.1 ∉ K → V z = 0 := by
    intro z ht hx
    have hsum : (∑ j : Fin 3,
        (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * J (z.1, z.2) j +
          2 * p (z.1, z.2) * u (z.1, z.2) j) *
            spatialPartial (fun y : ParabolicPoint => q y.1) j (z.1, z.2)) = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hqjEq]; simp [hqjZero j z.1 hx]
    simpa [V] using hsum
  have hQzero : ∀ z : Vec3 × ℝ, 0 < z.2 → z.1 ∉ K → Q z = 0 := by
    intro z ht hx
    simp [Q, hqZero z.1 hx]
  have hCzero : ∀ z : Vec3 × ℝ, 0 < z.2 → z.1 ∉ K → C z = 0 := by
    intro z ht hx
    have hsum : (∑ i : Fin 3, ∑ j : Fin 3,
        u (z.1, z.2) i * Du (z.1, z.2) i j *
          spatialPartial (fun y : ParabolicPoint => q y.1) j (z.1, z.2)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      rw [hqjEq]
      simp [hqjZero j z.1 hx]
    simpa [C] using hsum
  have hBIntProd : Integrable (fun z : Vec3 × ℝ => B z * η z.2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    regTails_integrable_timeFactor_of_spatial_support B K hS hBcont
      hqc.isCompact hBzero η hη hηc hηI
  have hVIntProd : Integrable (fun z : Vec3 × ℝ => V z * η z.2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    regTails_integrable_timeFactor_of_spatial_support V K hS hVcont
      hqc.isCompact hVzero η hη hηc hηI
  have hQIntProd : Integrable (fun z : Vec3 × ℝ => Q z * η z.2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    regTails_integrable_timeFactor_of_spatial_support Q K hS hQcont
      hqc.isCompact hQzero η hη hηc hηI
  have hCIntProd : Integrable (fun z : Vec3 × ℝ => C z * η z.2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    regTails_integrable_timeFactor_of_spatial_support C K hS hCcont
      hqc.isCompact hCzero η hη hηc hηI
  have hEInt : Integrable (fun z : Vec3 × ℝ => E z * deriv η z.2)
      ((volume : Measure (Vec3 × ℝ)).restrict S) := by
    rw [hMeasure]
    exact hEnergyInt
  have hBInt : Integrable (fun z : Vec3 × ℝ => B z * η z.2)
      ((volume : Measure (Vec3 × ℝ)).restrict S) := by
    rw [hMeasure]
    exact hBIntProd
  have hVInt : Integrable (fun z : Vec3 × ℝ => V z * η z.2)
      ((volume : Measure (Vec3 × ℝ)).restrict S) := by
    rw [hMeasure]
    exact hVIntProd
  have hQInt : Integrable (fun z : Vec3 × ℝ => Q z * η z.2)
      ((volume : Measure (Vec3 × ℝ)).restrict S) := by
    rw [hMeasure]
    exact hQIntProd
  have hCInt : Integrable (fun z : Vec3 × ℝ => C z * η z.2)
      ((volume : Measure (Vec3 × ℝ)).restrict S) := by
    rw [hMeasure]
    exact hCIntProd
  obtain ⟨hFcont, hGcont⟩ := regTails_localized_profiles_continuous
    u Du p J q hq hqc hUcont hDcont hPcont hJcont
  have hETime := regTails_timeFactor_integral E (deriv η) hEnergyInt
  have hHTime := regTails_timeFactor_integral H η hSourceInt
  have hFubiniE : (∫ t : ℝ, F t * deriv η t ∂volume) =
      ∫ t in Ioi (0 : ℝ), F t * deriv η t ∂volume := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hzero : deriv η t = 0 := by
      by_contra hne
      exact ht (hηdI (subset_tsupport _ (Function.mem_support.mpr hne)))
    simp [hzero]
  have hFubiniH : (∫ t : ℝ, G t * η t ∂volume) =
      ∫ t in Ioi (0 : ℝ), G t * η t ∂volume := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hzero : η t = 0 := by
      by_contra hne
      exact ht (hηI (subset_tsupport _ (Function.mem_support.mpr hne)))
    simp [hzero]
  have hTimeE : (∫ z in S, E z * deriv η z.2
      ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ t in Ioi (0 : ℝ), F t * deriv η t ∂volume := by
    simpa [E, F, regTailsEnergyWeight] using hETime
  have hTimeH : (∫ z in S, H z * η z.2
      ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ t in Ioi (0 : ℝ), G t * η t ∂volume := by
    simpa [H, G] using hHTime
  have hlocalP := regTails_localEnergy_product_test
    u p J hLE q hq hqc η hη hηc hηI
  simp_rw [CKN.setIntegral_parabolic_to_product] at hlocalP
  simp only [parabolicHomeomorph_symm_apply] at hlocalP
  have hLap := regTails_laplacian_ibp_sum u q η hq hqc hη hηc hηI
    hUcont hDcont hUdiff
  have hweakProduct :
      (∫ z in S, E z * deriv η z.2
        ∂(volume : Measure (Vec3 × ℝ))) =
      -(∫ z in S, H z * η z.2
        ∂(volume : Measure (Vec3 × ℝ))) := by
    have hBVInt : Integrable (fun z : Vec3 × ℝ => (B z + V z) * η z.2)
        ((volume : Measure (Vec3 × ℝ)).restrict S) := by
      apply (hBInt.add hVInt).congr
      filter_upwards [] with z
      change B z * η z.2 + V z * η z.2 = (B z + V z) * η z.2
      ring
    have hlocalExpanded :
        2 * (∫ z in S, Q z * η z.2
          ∂(volume : Measure (Vec3 × ℝ))) =
        (∫ z in S, E z * deriv η z.2 ∂(volume : Measure (Vec3 × ℝ))) +
          (∫ z in S, (B z + V z) * η z.2
            ∂(volume : Measure (Vec3 × ℝ))) := by
      have hlocalP' := hlocalP
      rw [integral_add hEInt hBVInt] at hlocalP'
      exact hlocalP'
    have hlocalSplit :
        2 * (∫ z in S, Q z * η z.2
          ∂(volume : Measure (Vec3 × ℝ))) =
        (∫ z in S, E z * deriv η z.2 ∂(volume : Measure (Vec3 × ℝ))) +
          (∫ z in S, B z * η z.2 ∂(volume : Measure (Vec3 × ℝ))) +
          (∫ z in S, V z * η z.2 ∂(volume : Measure (Vec3 × ℝ))) := by
      calc
        _ = (∫ z in S, E z * deriv η z.2
              ∂(volume : Measure (Vec3 × ℝ))) +
            (∫ z in S, (B z + V z) * η z.2
              ∂(volume : Measure (Vec3 × ℝ))) := hlocalExpanded
        _ = (∫ z in S, E z * deriv η z.2
              ∂(volume : Measure (Vec3 × ℝ))) +
            (∫ z in S, B z * η z.2 + V z * η z.2
              ∂(volume : Measure (Vec3 × ℝ))) := by
                congr 1
                apply setIntegral_congr_fun hSmeas
                intro z hz
                ring
        _ = _ := by
          rw [integral_add hBInt hVInt]
          ring
    have hLap := regTails_laplacian_ibp_sum u q η hq hqc hη hηc hηI
      hUcont hDcont hUdiff
    have hLapConverted :
        (∫ z in S, B z * η z.2 ∂(volume : Measure (Vec3 × ℝ))) =
          -2 * (∫ z in S, C z * η z.2 ∂(volume : Measure (Vec3 × ℝ))) := by
      simp_rw [CKN.setIntegral_parabolic_to_product] at hLap
      simpa [S, B, C, Du, qST, qj, qjj] using hLap
    have hSourcePoint (z : Vec3 × ℝ) :
        H z = -2 * Q z - 2 * C z + V z := by
      dsimp [H, Q, C, V, Du, regTailsLocalizedSource]
      ring
    have hScaledQ : Integrable (fun z : Vec3 × ℝ => (-2 : ℝ) * (Q z * η z.2))
        ((volume : Measure (Vec3 × ℝ)).restrict S) := hQInt.const_mul _
    have hScaledC : Integrable (fun z : Vec3 × ℝ => (-2 : ℝ) * (C z * η z.2))
        ((volume : Measure (Vec3 × ℝ)).restrict S) := hCInt.const_mul _
    have hScaledSum : Integrable
        (fun z : Vec3 × ℝ => (-2 : ℝ) * (Q z * η z.2) +
          (-2 : ℝ) * (C z * η z.2))
        ((volume : Measure (Vec3 × ℝ)).restrict S) :=
      hScaledQ.add hScaledC
    have hSourceSplit :
        (∫ z in S, H z * η z.2 ∂(volume : Measure (Vec3 × ℝ))) =
          -2 * (∫ z in S, Q z * η z.2 ∂(volume : Measure (Vec3 × ℝ))) -
          2 * (∫ z in S, C z * η z.2 ∂(volume : Measure (Vec3 × ℝ))) +
          (∫ z in S, V z * η z.2 ∂(volume : Measure (Vec3 × ℝ))) := by
      calc
        _ = ∫ z in S, (-2 : ℝ) * (Q z * η z.2) +
              (-2 : ℝ) * (C z * η z.2) + V z * η z.2
              ∂(volume : Measure (Vec3 × ℝ)) := by
                apply setIntegral_congr_fun hSmeas
                intro z hz
                change H z * η z.2 = _
                rw [hSourcePoint z]
                ring
        _ = _ := by
          rw [integral_add hScaledSum hVInt,
            integral_add hScaledQ hScaledC,
            integral_const_mul, integral_const_mul]
          ring
    rw [hSourceSplit]
    rw [hLapConverted] at hlocalSplit
    linarith only [hlocalSplit]
  rw [hTimeE, hTimeH] at hweakProduct
  calc
    _ = ∫ t in Ioi (0 : ℝ), F t * deriv η t ∂volume := hFubiniE
    _ = -∫ t in Ioi (0 : ℝ), G t * η t ∂volume := hweakProduct
    _ = _ := by rw [← hFubiniH]

end CKN.Leray

end
