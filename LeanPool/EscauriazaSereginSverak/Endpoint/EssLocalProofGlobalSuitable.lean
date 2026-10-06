/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MainTheorems
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem essLocal_test_support_in_ball
    {I : Set ℝ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ψ : Vec3 × ℝ → V}
    (hψ : ψ ∈ spaceTimeTestFunction (V := V) Set.univ I) :
    ∃ R : ℝ, 0 < R ∧
      tsupport ψ ⊆ spaceTimeSet (vec3Ball 0 R) I := by
  have hproj : IsCompact (Prod.fst '' tsupport ψ) :=
    hψ.2.1.isCompact.image continuous_fst
  obtain ⟨S, hS⟩ := hproj.isBounded.subset_ball (0 : Vec3)
  let R : ℝ := Real.sqrt 3 * (max S 0 + 1)
  have hR : 0 < R := by
    dsimp [R]
    positivity
  refine ⟨R, hR, ?_⟩
  intro z hz
  rcases z with ⟨x, t⟩
  have hzI : (x, t) ∈ spaceTimeSet Set.univ I := hψ.2.2 hz
  have hxproj : x ∈ Prod.fst '' tsupport ψ := ⟨(x, t), hz, rfl⟩
  have hxS : ‖x‖ < S := by simpa using hS hxproj
  have hxR : ‖x‖ < max S 0 + 1 := by
    have hSmax : S ≤ max S 0 := le_max_left _ _
    linarith only [hxS, hSmax]
  have hxnorm : vec3EuclideanNorm (x - 0) < R := by
    simpa only [sub_zero] using
      (vec3EuclideanNorm_le_sqrt_three_mul_norm x).trans_lt
        (mul_lt_mul_of_pos_left hxR (by positivity))
  exact ⟨hxnorm, hzI.2⟩

/-- Local suitability on every origin-centred past cylinder yields the global
CKN suitable-solution predicate on any finite past interval. -/
theorem essLocal_globalSuitable_of_local
    (U : ParabolicPoint → Vec3)
    (DU : ParabolicPoint → Fin 3 → Vec3)
    (q : ParabolicPoint → ℝ)
    (hlocal : ∀ (R a : ℝ), 0 < R → a < 0 →
      IsSuitableWeakSolution (vec3Ball 0 R) (Ioo a 0) 3 U DU q
        (0 : ParabolicPoint → Vec3))
    (a : ℝ) (ha : a < 0) :
    IsSuitableWeakSolution Set.univ (Ioo a 0) 3 U DU q
      (0 : ParabolicPoint → Vec3) := by
  let I : Set ℝ := Ioo a 0
  have hdata : CKN.IsSuitableWeakSolutionData Set.univ I 3 U DU q
      (0 : ParabolicPoint → Vec3) := by
    refine ⟨isOpen_univ, isOpen_Ioo, ordConnected_Ioo, by norm_num, ?_, ?_⟩
    · intro Ω' J hbox i
      simp only [CKN.localLp]
      exact MemLp.zero
    · intro Ω' J hbox
      obtain ⟨S, hS⟩ := hbox.2.1.isBounded.subset_ball (0 : Vec3)
      let R : ℝ := Real.sqrt 3 * (max S 0 + 1)
      have hR : 0 < R := by
        dsimp [R]
        positivity
      have hΩ : closure Ω' ⊆ vec3Ball 0 R := by
        intro x hx
        have hxS : ‖x‖ < S := by simpa using hS hx
        have hxR : ‖x‖ < max S 0 + 1 := by
          have hSmax : S ≤ max S 0 := le_max_left _ _
          linarith only [hxS, hSmax]
        change vec3EuclideanNorm (x - 0) < R
        simpa only [sub_zero] using
          (vec3EuclideanNorm_le_sqrt_three_mul_norm x).trans_lt
            (mul_lt_mul_of_pos_left hxR (by positivity))
      have hbox' : CKN.localBox (vec3Ball 0 R) (Ioo a 0) Ω' J :=
        ⟨hbox.1, hbox.2.1, hΩ, hbox.2.2.2.1,
          hbox.2.2.2.2.1, hbox.2.2.2.2.2⟩
      exact ((CKN.isSuitableWeakSolution_iff_integrable.mp
        (hlocal R a hR ha)).toData).2.2.2.2.2 Ω' J hbox'
  have hdiv : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ I →
      ∫ z in spaceTimeSet Set.univ I,
        ∑ i : Fin 3, U z i * spatialPartial ψ i z = 0 := by
    intro ψ hψ
    obtain ⟨R, hR, hsupport⟩ := essLocal_test_support_in_ball hψ
    have hψlocal : ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball 0 R) (Ioo a 0) := by
      exact ⟨hψ.1, hψ.2.1, by simpa [I] using hsupport⟩
    have hsol := hlocal R a hR ha
    have hsolInt := CKN.isSuitableWeakSolution_iff_integrable.mp hsol
    have hid := hsolInt.2.2.2.2.2.2.1 ψ hψlocal
    have hsmall : spaceTimeSet (vec3Ball 0 R) I ⊆
        spaceTimeSet Set.univ I := by
      intro z hz
      exact ⟨Set.mem_univ z.1, hz.2⟩
    have hbigmeas : MeasurableSet (spaceTimeSet Set.univ I) := by
      change MeasurableSet (Set.univ ×ˢ I)
      exact MeasurableSet.univ.prod measurableSet_Ioo
    have hts : tsupport (show ParabolicPoint → ℝ from ψ) =
        tsupport (show Vec3 × ℝ → ℝ from ψ) :=
      CKN.tsupport_parabolic_eq (show Vec3 × ℝ → ℝ from ψ)
    have hzero (z : ParabolicPoint)
        (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ)) :
        (∑ i : Fin 3, U z i * spatialPartial ψ i z) = 0 := by
      have hzprod : z ∉ tsupport (show Vec3 × ℝ → ℝ from ψ) := by
        rw [← hts]
        exact hz
      have hsp (i : Fin 3) : spatialPartial ψ i z = 0 :=
        spatialPartial_eq_zero_off_tsupport
          (ψ := show Vec3 × ℝ → ℝ from ψ) hzprod i
      simp [hsp]
    have hinter : (∫ z in spaceTimeSet Set.univ I,
        ∑ i : Fin 3, U z i * spatialPartial ψ i z) =
        ∫ z in spaceTimeSet (vec3Ball 0 R) I,
          ∑ i : Fin 3, U z i * spatialPartial ψ i z := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hbigmeas hsmall
      intro z hz
      apply hzero z
      intro hzψ
      have hzprod : z ∈ tsupport (show Vec3 × ℝ → ℝ from ψ) := by
        rw [← hts]
        exact hzψ
      have hmem := hsupport hzprod
      have hmemPar : z ∈ spaceTimeSet (vec3Ball 0 R) I :=
        ⟨hmem.1, hmem.2⟩
      exact hz.2 hmemPar
    rw [hinter]
    simpa [I] using hid.2
  have hmom : ∀ φ : Vec3 × ℝ → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) Set.univ I →
      ∫ z in spaceTimeSet Set.univ I,
        (-(∑ i : Fin 3, U z i * timePartial (fun w => φ w i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              U z i * U z j * spatialPartial (fun w => φ w i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              DU z i j * spatialPartial (fun w => φ w i) j z
          - q z * ∑ i : Fin 3,
              spatialPartial (fun w => φ w i) i z) = 0 := by
    intro φ hφ
    obtain ⟨R, hR, hsupport⟩ := essLocal_test_support_in_ball hφ
    have hφlocal : φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball 0 R) (Ioo a 0) := by
      exact ⟨hφ.1, hφ.2.1, by simpa [I] using hsupport⟩
    have hsol := hlocal R a hR ha
    have hsolInt := CKN.isSuitableWeakSolution_iff_integrable.mp hsol
    have hid := hsolInt.2.2.2.2.2.2.2.1 φ hφlocal
    have hsmall : spaceTimeSet (vec3Ball 0 R) I ⊆
        spaceTimeSet Set.univ I := by
      intro z hz
      exact ⟨Set.mem_univ z.1, hz.2⟩
    have hbigmeas : MeasurableSet (spaceTimeSet Set.univ I) := by
      change MeasurableSet (Set.univ ×ˢ I)
      exact MeasurableSet.univ.prod measurableSet_Ioo
    have hts : tsupport (show ParabolicPoint → Vec3 from φ) =
        tsupport (show Vec3 × ℝ → Vec3 from φ) :=
      CKN.tsupport_parabolic_eq (show Vec3 × ℝ → Vec3 from φ)
    have hcomponent (i : Fin 3) :
        tsupport (fun w : Vec3 × ℝ => φ w i) ⊆ tsupport φ := by
      apply closure_minimal
      · intro z hz
        by_contra hnot
        apply hz
        have hval : φ z = 0 := image_eq_zero_of_notMem_tsupport hnot
        simp [hval]
      · exact isClosed_tsupport φ
    have hzero (z : ParabolicPoint)
        (hz : z ∉ tsupport (show ParabolicPoint → Vec3 from φ)) :
        (-(∑ i : Fin 3, U z i * timePartial (fun w => φ w i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              U z i * U z j * spatialPartial (fun w => φ w i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              DU z i j * spatialPartial (fun w => φ w i) j z
          - q z * ∑ i : Fin 3,
              spatialPartial (fun w => φ w i) i z) = 0 := by
      have hzprod : z ∉ tsupport (show Vec3 × ℝ → Vec3 from φ) := by
        rw [← hts]
        exact hz
      have hnot (i : Fin 3) :
          z ∉ tsupport (fun w : Vec3 × ℝ => φ w i) := by
        intro hmem
        exact hzprod (hcomponent i hmem)
      have htime (i : Fin 3) : timePartial (fun w => φ w i) z = 0 := by
        change timePartial (fun w : Vec3 × ℝ => φ w i) (z.1, z.2) = 0
        exact timePartial_eq_zero_off_tsupport
          (ψ := fun w : Vec3 × ℝ => φ w i) (hnot i)
      have hsp (i j : Fin 3) : spatialPartial (fun w => φ w i) j z = 0 := by
        change spatialPartial (fun w : Vec3 × ℝ => φ w i) j (z.1, z.2) = 0
        exact spatialPartial_eq_zero_off_tsupport
          (ψ := fun w : Vec3 × ℝ => φ w i) (hnot i) j
      have htimeSum :
          ∑ i : Fin 3, U z i * timePartial (fun w => φ w i) z = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [htime i]
        simp
      have hnonlinearSum :
          ∑ i : Fin 3, ∑ j : Fin 3,
            U z i * U z j * spatialPartial (fun w => φ w i) j z = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro j hj
        rw [hsp i j]
        simp
      have hviscousSum :
          ∑ i : Fin 3, ∑ j : Fin 3,
            DU z i j * spatialPartial (fun w => φ w i) j z = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro j hj
        rw [hsp i j]
        simp
      have hpressureSum :
          ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hsp i i]
      rw [htimeSum, hnonlinearSum, hviscousSum, hpressureSum]
      ring
    have hinter : (∫ z in spaceTimeSet Set.univ I,
        (-(∑ i : Fin 3, U z i * timePartial (fun w => φ w i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              U z i * U z j * spatialPartial (fun w => φ w i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              DU z i j * spatialPartial (fun w => φ w i) j z
          - q z * ∑ i : Fin 3,
              spatialPartial (fun w => φ w i) i z)) =
        ∫ z in spaceTimeSet (vec3Ball 0 R) I,
        (-(∑ i : Fin 3, U z i * timePartial (fun w => φ w i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              U z i * U z j * spatialPartial (fun w => φ w i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              DU z i j * spatialPartial (fun w => φ w i) j z
          - q z * ∑ i : Fin 3,
              spatialPartial (fun w => φ w i) i z) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hbigmeas hsmall
      intro z hz
      apply hzero z
      intro hzφ
      have hzprod : z ∈ tsupport (show Vec3 × ℝ → Vec3 from φ) := by
        rw [← hts]
        exact hzφ
      have hmem := hsupport hzprod
      have hmemPar : z ∈ spaceTimeSet (vec3Ball 0 R) I :=
        ⟨hmem.1, hmem.2⟩
      exact hz.2 hmemPar
    rw [hinter]
    simpa [I] using hid.2
  have hlei : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ I →
      (∀ z, 0 ≤ ψ z) →
      2 * ∫ z in spaceTimeSet Set.univ I, spatialGradientSq U DU z * ψ z ≤
        ∫ z in spaceTimeSet Set.univ I,
          (vec3EuclideanNorm (U z)) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + ((vec3EuclideanNorm (U z)) ^ 2 + 2 * q z) *
                ∑ i, U z i * spatialPartial ψ i z := by
    intro ψ hψ hnonneg
    obtain ⟨R, hR, hsupport⟩ := essLocal_test_support_in_ball hψ
    have hψlocal : ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball 0 R) (Ioo a 0) := by
      exact ⟨hψ.1, hψ.2.1, by simpa [I] using hsupport⟩
    have hsol := hlocal R a hR ha
    have hsolInt := CKN.isSuitableWeakSolution_iff_integrable.mp hsol
    have hid := hsolInt.2.2.2.2.2.2.2.2 ψ hψlocal hnonneg
    have hsmall : spaceTimeSet (vec3Ball 0 R) I ⊆
        spaceTimeSet Set.univ I := by
      intro z hz
      exact ⟨Set.mem_univ z.1, hz.2⟩
    have hbigmeas : MeasurableSet (spaceTimeSet Set.univ I) := by
      change MeasurableSet (Set.univ ×ˢ I)
      exact MeasurableSet.univ.prod measurableSet_Ioo
    have hts : tsupport (show ParabolicPoint → ℝ from ψ) =
        tsupport (show Vec3 × ℝ → ℝ from ψ) :=
      CKN.tsupport_parabolic_eq (show Vec3 × ℝ → ℝ from ψ)
    have hleftzero (z : ParabolicPoint)
        (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ)) :
        spatialGradientSq U DU z * ψ z = 0 := by
      have hzprod : z ∉ tsupport (show Vec3 × ℝ → ℝ from ψ) := by
        rw [← hts]
        exact hz
      have hzero : ψ (z.1, z.2) = 0 := by
        change (show Vec3 × ℝ → ℝ from ψ) (z.1, z.2) = 0
        exact image_eq_zero_of_notMem_tsupport hzprod
      have hzeroP : ψ z = 0 := by
        change ψ (z.1, z.2) = 0
        exact hzero
      simp [hzeroP]
    have hrightzero (z : ParabolicPoint)
        (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ)) :
        (vec3EuclideanNorm (U z)) ^ 2 *
            (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
          + ((vec3EuclideanNorm (U z)) ^ 2 + 2 * q z) *
              ∑ i, U z i * spatialPartial ψ i z = 0 := by
      have hzprod : z ∉ tsupport (show Vec3 × ℝ → ℝ from ψ) := by
        rw [← hts]
        exact hz
      have htime : timePartial ψ z = 0 :=
        timePartial_eq_zero_off_tsupport (ψ := ψ) hzprod
      have hsp (i : Fin 3) : spatialPartial ψ i z = 0 :=
        spatialPartial_eq_zero_off_tsupport (ψ := ψ) hzprod i
      have hsecond (i j : Fin 3) : spatialSecondPartial ψ i j z = 0 :=
        spatialSecondPartial_eq_zero_off_tsupport (ψ := ψ) hzprod i j
      simp [htime, hsp, hsecond]
    have hleft : (∫ z in spaceTimeSet Set.univ I,
        spatialGradientSq U DU z * ψ z) =
        ∫ z in spaceTimeSet (vec3Ball 0 R) I,
          spatialGradientSq U DU z * ψ z := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hbigmeas hsmall
      intro z hz
      apply hleftzero z
      intro hzψ
      have hzprod : z ∈ tsupport (show Vec3 × ℝ → ℝ from ψ) := by
        rw [← hts]
        exact hzψ
      have hmem := hsupport hzprod
      have hmemPar : z ∈ spaceTimeSet (vec3Ball 0 R) I :=
        ⟨hmem.1, hmem.2⟩
      exact hz.2 hmemPar
    have hright : (∫ z in spaceTimeSet Set.univ I,
        (vec3EuclideanNorm (U z)) ^ 2 *
            (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
          + ((vec3EuclideanNorm (U z)) ^ 2 + 2 * q z) *
              ∑ i, U z i * spatialPartial ψ i z) =
        ∫ z in spaceTimeSet (vec3Ball 0 R) I,
        (vec3EuclideanNorm (U z)) ^ 2 *
            (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
          + ((vec3EuclideanNorm (U z)) ^ 2 + 2 * q z) *
              ∑ i, U z i * spatialPartial ψ i z := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hbigmeas hsmall
      intro z hz
      apply hrightzero z
      intro hzψ
      have hzprod : z ∈ tsupport (show Vec3 × ℝ → ℝ from ψ) := by
        rw [← hts]
        exact hzψ
      have hmem := hsupport hzprod
      have hmemPar : z ∈ spaceTimeSet (vec3Ball 0 R) I :=
        ⟨hmem.1, hmem.2⟩
      exact hz.2 hmemPar
    rw [hleft, hright]
    simpa [I] using hid.2.2
  have hglobalInt := CKN.isSuitableWeakSolutionIntegrable_of_identities
    hdata hdiv (by intro φ hφ; simpa using hmom φ hφ)
    (by intro ψ hψ hnonneg; simpa using hlei ψ hψ hnonneg)
  simpa [I] using CKN.isSuitableWeakSolution_iff_integrable.mpr hglobalInt

end ESS
