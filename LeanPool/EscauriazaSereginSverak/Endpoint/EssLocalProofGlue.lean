/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsOpenGlue

/-!
# Ess Local Proof Glue

Local endpoint regularity through vorticity estimates and backward uniqueness.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A common Hölder representative on the closed target cylinder restricts
to the original velocity almost everywhere on the past cylinder. -/
theorem essLocal_holder_of_all_good
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {ε₀ γ₀ : ℝ} (hγ₀ : 0 < γ₀) (hγ₀le : γ₀ ≤ 1)
    (hglue : ∀ {K : Set ParabolicPoint}, IsCompact K →
      K ⊆ {z : ParabolicPoint |
        vec3EuclideanNorm (z.1 - 0) ≤ 1 / 2 ∧
          z.2 ∈ Icc (-(1 / 4 : ℝ)) 0} →
      (∀ z ∈ K, IsGoodPoint ε₀ u p z) →
      ∃ N : Set ParabolicPoint, ∃ w : ParabolicPoint → Vec3,
        K ⊆ N ∧ N ⊆ goodPointClosedTopDomain ∧
          IsOpen {z : {q : ParabolicPoint // q ∈ goodPointClosedTopDomain} |
            z.1 ∈ N} ∧
          w =ᵐ[volume.restrict (N ∩ goodPointDomain)] u ∧
          ParabolicHolderVecOn K w γ₀)
    (hgood : ∀ z ∈
      closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ)),
        IsGoodPoint ε₀ u p z) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ w : ParabolicPoint → Vec3,
        w =ᵐ[volume.restrict (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))] u ∧
        ParabolicHolderVecOn
          (closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))) w γ := by
  let K : Set ParabolicPoint :=
    closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))
  have hKcompact : IsCompact K := by
    change IsCompact (closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ)))
    let P : Set (Vec3 × ℝ) :=
      {y : Vec3 | vec3EuclideanNorm (y - 0) ≤ 1 / 2} ×ˢ
        Icc (0 - (1 / 2 : ℝ) ^ 2) 0
    have hPcompact : IsCompact P := by
      have hBcompact : IsCompact {y : Vec3 | vec3EuclideanNorm (y - 0) ≤ 1 / 2} := by
        simpa only [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] using
          (isCompact_closure_vec3Ball (x := (0 : Vec3))
            (by norm_num : (0 : ℝ) < 1 / 2))
      dsimp [P]
      exact hBcompact.prod
        (isCompact_Icc : IsCompact (Icc (0 - (1 / 2 : ℝ) ^ 2) 0))
    rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1 / 2)]
    rw [← parabolicHomeomorph_preimage
      ({y : Vec3 | vec3EuclideanNorm (y - 0) ≤ 1 / 2} ×ˢ
        Icc (0 - (1 / 2 : ℝ) ^ 2) 0)]
    exact parabolicHomeomorph.isCompact_preimage.mpr
      (by simpa only [P] using hPcompact)
  have hKregion : K ⊆ {z : ParabolicPoint |
      vec3EuclideanNorm (z.1 - 0) ≤ 1 / 2 ∧
        z.2 ∈ Icc (-(1 / 4 : ℝ)) 0} := by
    intro z hz
    change z ∈ closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ)) at hz
    rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1 / 2)] at hz
    rw [← parabolicHomeomorph_preimage
      ({y : Vec3 | vec3EuclideanNorm (y - 0) ≤ 1 / 2} ×ˢ
        Icc (0 - (1 / 2 : ℝ) ^ 2) 0)] at hz
    rcases Set.mem_preimage.mp hz with ⟨hx, ht⟩
    refine ⟨?_, ?_⟩
    · exact hx
    rcases ht with ⟨htlo, htup⟩
    refine ⟨?_, htup⟩
    calc
      -(1 / 4 : ℝ) ≤ 0 - (1 / 2 : ℝ) ^ 2 := by norm_num
      _ ≤ z.2 := htlo
  obtain ⟨N, w, hKN, _hNdomain, _hNopen, hWAE, hHolder⟩ :=
    hglue hKcompact hKregion (by simpa only [K] using hgood)
  have hSsubset :
      spaceTimeSet (vec3Ball (0 : Vec3) (1 / 2 : ℝ)) (Ico (-(1 / 4 : ℝ)) 0) ⊆
        N ∩ goodPointDomain := by
    intro z hz
    change z.1 ∈ vec3Ball (0 : Vec3) (1 / 2 : ℝ) ∧
      z.2 ∈ Ico (-(1 / 4 : ℝ)) 0 at hz
    rcases hz with ⟨hx, ht⟩
    have hzK : z ∈ K := by
      change z ∈ closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))
      rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1 / 2)]
      rw [← parabolicHomeomorph_preimage
        ({y : Vec3 | vec3EuclideanNorm (y - 0) ≤ 1 / 2} ×ˢ
          Icc (0 - (1 / 2 : ℝ) ^ 2) 0)]
      change parabolicHomeomorph z ∈
        ({y : Vec3 | vec3EuclideanNorm (y - 0) ≤ 1 / 2} ×ˢ
          Icc (0 - (1 / 2 : ℝ) ^ 2) 0)
      change vec3EuclideanNorm (z.1 - 0) ≤ 1 / 2 ∧
        z.2 ∈ Icc (0 - (1 / 2 : ℝ) ^ 2) 0
      refine ⟨(mem_vec3Ball.mp hx).le, ?_⟩
      have htlo : 0 - (1 / 2 : ℝ) ^ 2 ≤ z.2 := by
        calc
          0 - (1 / 2 : ℝ) ^ 2 = -(1 / 4 : ℝ) := by norm_num
          _ ≤ z.2 := ht.1
      exact ⟨htlo, le_of_lt ht.2⟩
    refine ⟨hKN hzK, ?_⟩
    exact ⟨by
      calc
        vec3EuclideanNorm (z.1 - 0) < 1 / 2 := mem_vec3Ball.mp hx
        _ < 1 := by norm_num,
      ⟨by linarith only [ht.1], ht.2⟩⟩
  have hSopenMeas : MeasurableSet
      (spaceTimeSet (vec3Ball (0 : Vec3) (1 / 2 : ℝ)) (Ico (-(1 / 4 : ℝ)) 0)) := by
    rw [CKN.spaceTimeSet]
    exact (isOpen_vec3Ball _ _).measurableSet.prod measurableSet_Ico
  have hSae : ∀ᵐ z : ParabolicPoint ∂(volume.restrict
      (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))),
      z ∈ spaceTimeSet (vec3Ball (0 : Vec3) (1 / 2 : ℝ)) (Ico (-(1 / 4 : ℝ)) 0) := by
    rw [ae_restrict_iff' (measurableSet_parabolicCylinder _ _ _)]
    rw [ae_iff]
    have hboundary : volume
        (spaceTimeSet (vec3Ball (0 : Vec3) (1 / 2 : ℝ)) ({0} : Set ℝ)) = 0 := by
      change (volume : Measure (Vec3 × ℝ))
        (vec3Ball (0 : Vec3) (1 / 2 : ℝ) ×ˢ ({0} : Set ℝ)) = 0
      rw [Measure.volume_eq_prod Vec3 ℝ, Measure.prod_prod]
      simp
    have hdiff : parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ) \
        spaceTimeSet (vec3Ball (0 : Vec3) (1 / 2 : ℝ)) (Ico (-(1 / 4 : ℝ)) 0) ⊆
          spaceTimeSet (vec3Ball (0 : Vec3) (1 / 2 : ℝ)) ({0} : Set ℝ) := by
      intro z hz
      rcases z with ⟨x, t⟩
      change (x, t) ∈ parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ) ∧
        (x, t) ∉ spaceTimeSet (vec3Ball (0 : Vec3) (1 / 2 : ℝ))
          (Ico (-(1 / 4 : ℝ)) 0) at hz
      rcases (mem_parabolicCylinder.mp hz.1) with ⟨hx, htlo, htup⟩
      have hnot := hz.2
      change ¬ (x ∈ vec3Ball (0 : Vec3) (1 / 2 : ℝ) ∧
        t ∈ Ico (-(1 / 4 : ℝ)) 0) at hnot
      have htnot : t ∉ Ico (-(1 / 4 : ℝ)) 0 := by
        intro ht
        exact hnot ⟨hx, ht⟩
      simp only [Set.mem_Ico] at htnot
      change x ∈ vec3Ball (0 : Vec3) (1 / 2 : ℝ) ∧ t = 0
      refine ⟨hx, ?_⟩
      rcases not_and_or.mp htnot with hlow | hhigh
      · have htlo' : -(1 / 4 : ℝ) < t := by
          calc
            -(1 / 4 : ℝ) = 0 - (1 / 2 : ℝ) ^ 2 := by norm_num
            _ < t := htlo
        exact False.elim (hlow (le_of_lt htlo'))
      · exact le_antisymm htup (le_of_not_gt hhigh)
    have hnull : volume
        (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ) \
          spaceTimeSet (vec3Ball (0 : Vec3) (1 / 2 : ℝ)) (Ico (-(1 / 4 : ℝ)) 0)) = 0 :=
      measure_mono_null hdiff hboundary
    have hset :
        {a : ParabolicPoint | ¬ (a ∈ parabolicCylinder (0 : Vec3) 0
          (1 / 2 : ℝ) →
            a ∈ spaceTimeSet (vec3Ball (0 : Vec3) (1 / 2 : ℝ))
              (Ico (-(1 / 4 : ℝ)) 0))} =
          parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ) \
            spaceTimeSet (vec3Ball (0 : Vec3) (1 / 2 : ℝ))
              (Ico (-(1 / 4 : ℝ)) 0) := by
      ext a
      simp only [Set.mem_ofPred_eq, not_imp, Set.mem_sdiff]
    rw [hset]
    exact hnull
  have hWAEsmall : w =ᵐ[volume.restrict
      (spaceTimeSet (vec3Ball (0 : Vec3) (1 / 2 : ℝ))
        (Ico (-(1 / 4 : ℝ)) 0))] u :=
    Eventually.filter_mono
      (ae_mono (Measure.restrict_mono_set volume hSsubset)) hWAE
  have hWAEbase : ∀ᵐ z ∂volume,
      z ∈ spaceTimeSet (vec3Ball (0 : Vec3) (1 / 2 : ℝ)) (Ico (-(1 / 4 : ℝ)) 0) →
        w z = u z :=
    (ae_restrict_iff' hSopenMeas).mp hWAEsmall
  have hWAEtarget : w =ᵐ[volume.restrict
      (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))] u := by
    filter_upwards
      [ae_mono Measure.restrict_le_self hWAEbase, hSae] with z hz hzS
    exact hz hzS
  exact ⟨γ₀, hγ₀, hγ₀le, w, hWAEtarget, hHolder⟩

private theorem essLocal_test_support_inner_ball
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      tsupport ψ ⊆ vec3Ball (0 : Vec3) r ×ˢ Ioo (-1) 0 := by
  let S : Set Vec3 := Prod.fst '' tsupport ψ
  have hScompact : IsCompact S := hψ.2.1.image continuous_fst
  have hf : Continuous (fun y : Vec3 => vec3EuclideanNorm (y - 0)) :=
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp
      (continuous_id.sub continuous_const)
  have hSsub : S ⊆ vec3Ball (0 : Vec3) 1 := by
    rintro x ⟨z, hz, rfl⟩
    exact (hψ.2.2 hz).1
  by_cases hSne : S.Nonempty
  · obtain ⟨x, hxS, hmax⟩ := hScompact.exists_isMaxOn hSne hf.continuousOn
    have hmaxlt : vec3EuclideanNorm (x - 0) < 1 := hSsub hxS
    let r : ℝ := (vec3EuclideanNorm (x - 0) + 1) / 2
    have hrpos : 0 < r := by
      dsimp [r]
      linarith only [vec3EuclideanNorm_nonneg (x - 0)]
    have hr1 : r < 1 := by dsimp [r]; linarith only [hmaxlt]
    refine ⟨r, hrpos, hr1, ?_⟩
    intro z hz
    rcases z with ⟨x', t⟩
    have hx'S : x' ∈ S := ⟨(x', t), hz, rfl⟩
    have hbound : vec3EuclideanNorm (x' - 0) ≤ vec3EuclideanNorm (x - 0) := by
      simpa only [Set.mem_ofPred_eq] using hmax hx'S
    have hx'r : x' ∈ vec3Ball (0 : Vec3) r := by
      apply mem_vec3Ball.mpr
      dsimp [r]
      linarith only [hbound, hmaxlt]
    exact ⟨hx'r, (hψ.2.2 hz).2⟩
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro z hz
    have hxS : z.1 ∈ S := ⟨z, hz, rfl⟩
    exact False.elim (hSne ⟨z.1, hxS⟩)

/-- Local energy equalities on all smaller concentric cylinders assemble into
the local energy inequality on the unit cylinder. Compact support keeps each
test inside one such smaller cylinder. -/
theorem essLocal_suitable_of_localEnergyEqualities
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hdata : CKN.IsSuitableWeakSolutionData
      (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) 3 u Du p (0 : ParabolicPoint → Vec3))
    (hdiv : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
    (hmom : ∀ φ : Vec3 × ℝ → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0)
    (henergy : ∀ r : ℝ, 0 < r → r < 1 →
      ∀ ψ : Vec3 × ℝ → ℝ,
        ψ ∈ spaceTimeTestFunction (V := ℝ)
          (vec3Ball (0 : Vec3) r) (Ioo (-1) 0) →
        2 * ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
            spatialGradientSq u Du z * ψ z =
          ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
            (vec3EuclideanNorm (u z)) ^ 2 *
                (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
              + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                  ∑ i, u z i * spatialPartial ψ i z) :
    IsSuitableWeakSolution (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) 3
      u Du p (0 : ParabolicPoint → Vec3) := by
  have hlei : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      (∀ z, 0 ≤ ψ z) →
      2 * ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          spatialGradientSq u Du z * ψ z ≤
        ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          (vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψ i z := by
    intro ψ hψ _hψnn
    obtain ⟨r, hrpos, hr1, hsupport⟩ := essLocal_test_support_inner_ball hψ
    have hψr : ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) r) (Ioo (-1) 0) := by
      exact ⟨hψ.1, hψ.2.1, hsupport⟩
    have hid := henergy r hrpos hr1 ψ hψr
    let Qr : Set ParabolicPoint :=
      spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0)
    let Q1 : Set ParabolicPoint :=
      spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0)
    let K : Set ParabolicPoint :=
      tsupport (show ParabolicPoint → ℝ from ψ)
    let ψP : ParabolicPoint → ℝ := show ParabolicPoint → ℝ from ψ
    have hKsmall : K ⊆ Qr := by
      intro z hz
      have hsupport : z ∈ tsupport (show ParabolicPoint → ℝ from ψ) ↔
          parabolicHomeomorph z ∈ tsupport ψ := by
        rw [tsupport_parabolic_eq]
        rcases z with ⟨x, t⟩
        rfl
      exact hψr.2.2 (hsupport.mp hz)
    have hQrQ1 : Qr ⊆ Q1 := by
      intro z hz
      rcases hz with ⟨hx, ht⟩
      refine ⟨?_, ht⟩
      apply mem_vec3Ball.mpr
      calc
        vec3EuclideanNorm (z.1 - 0) < r := mem_vec3Ball.mp hx
        _ < 1 := hr1
    have hQrm : MeasurableSet Qr := by
      change MeasurableSet
        (vec3Ball (0 : Vec3) r ×ˢ Ioo (-1) 0)
      exact (vec3Ball_measurable _ _).prod measurableSet_Ioo
    have hQ1m : MeasurableSet Q1 := by
      change MeasurableSet
        (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0)
      exact (vec3Ball_measurable _ _).prod measurableSet_Ioo
    have hleft :
        (∫ z in Q1, spatialGradientSq u Du z * ψP z ∂
          (volume : Measure ParabolicPoint)) =
          ∫ z in Qr, spatialGradientSq u Du z * ψP z ∂
            (volume : Measure ParabolicPoint) := by
      have hzero : ∀ z, z ∉ K → spatialGradientSq u Du z * ψP z = 0 := by
        intro z hz
        have hsupport : z ∈ tsupport (show ParabolicPoint → ℝ from ψ) ↔
            parabolicHomeomorph z ∈ tsupport ψ := by
          rw [tsupport_parabolic_eq]
          rcases z with ⟨x, t⟩
          rfl
        have hzprod : parabolicHomeomorph z ∉ tsupport ψ := by
          intro hzmem
          apply hz
          exact hsupport.mpr hzmem
        have hψzero : ψ (parabolicHomeomorph z) = 0 :=
          image_eq_zero_of_notMem_tsupport hzprod
        change spatialGradientSq u Du z * ψ (parabolicHomeomorph z) = 0
        rw [hψzero, mul_zero]
      have hindicator : Q1.indicator
          (fun z => spatialGradientSq u Du z * ψP z) =ᵐ[volume]
          Qr.indicator (fun z => spatialGradientSq u Du z * ψP z) := by
        filter_upwards [] with z
        by_cases hzK : z ∈ K
        · simp [hQrQ1 (hKsmall hzK), hKsmall hzK]
        · have hz0 := hzero z hzK
          by_cases hzQr : z ∈ Qr
          · simp [hQrQ1 hzQr, hzQr, hz0]
          · simp [hzQr, hz0]
      calc
        _ = ∫ z, Q1.indicator
            (fun z => spatialGradientSq u Du z * ψP z) z ∂
              (volume : Measure ParabolicPoint) :=
          (integral_indicator hQ1m).symm
        _ = ∫ z, Qr.indicator
            (fun z => spatialGradientSq u Du z * ψP z) z ∂
              (volume : Measure ParabolicPoint) := integral_congr_ae hindicator
        _ = _ := integral_indicator hQrm
    have hright :
        (∫ z in Q1,
          (vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψP z + ∑ i, spatialSecondPartial ψP i i z) +
            ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
              ∑ i, u z i * spatialPartial ψP i z ∂
          (volume : Measure ParabolicPoint)) =
          ∫ z in Qr,
            (vec3EuclideanNorm (u z)) ^ 2 *
                (timePartial ψP z + ∑ i, spatialSecondPartial ψP i i z) +
              ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψP i z ∂
            (volume : Measure ParabolicPoint) := by
      let f : ParabolicPoint → ℝ := fun z =>
        (vec3EuclideanNorm (u z)) ^ 2 *
            (timePartial ψP z + ∑ i, spatialSecondPartial ψP i i z) +
          ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
            ∑ i, u z i * spatialPartial ψP i z
      have hzero : ∀ z, z ∉ K → f z = 0 := by
        intro z hz
        have hsupport : z ∈ tsupport (show ParabolicPoint → ℝ from ψ) ↔
            parabolicHomeomorph z ∈ tsupport ψ := by
          rw [tsupport_parabolic_eq]
          rcases z with ⟨x, t⟩
          rfl
        have hzprod : parabolicHomeomorph z ∉ tsupport ψ := by
          intro hzmem
          apply hz
          exact hsupport.mpr hzmem
        have hztime : timePartial ψP z = 0 :=
          timePartial_eq_zero_off_tsupport hzprod
        have hzsecond (i : Fin 3) : spatialSecondPartial ψP i i z = 0 :=
          spatialSecondPartial_eq_zero_off_tsupport hzprod i i
        have hzspace (i : Fin 3) : spatialPartial ψP i z = 0 :=
          spatialPartial_eq_zero_off_tsupport hzprod i
        simp [f, hztime, hzsecond, hzspace]
      have hindicator : Q1.indicator f =ᵐ[volume] Qr.indicator f := by
        filter_upwards [] with z
        by_cases hzK : z ∈ K
        · simp [hQrQ1 (hKsmall hzK), hKsmall hzK]
        · have hz0 := hzero z hzK
          by_cases hzQr : z ∈ Qr
          · simp [hQrQ1 hzQr, hzQr, hz0]
          · simp [hzQr, hz0]
      calc
        _ = ∫ z, Q1.indicator f z ∂(volume : Measure ParabolicPoint) :=
          (integral_indicator hQ1m).symm
        _ = ∫ z, Qr.indicator f z ∂(volume : Measure ParabolicPoint) :=
          integral_congr_ae hindicator
        _ = _ := integral_indicator hQrm
    rw [hleft, hright]
    exact le_of_eq hid
  have hintergrable := CKN.isSuitableWeakSolutionIntegrable_of_identities
    hdata hdiv hmom (by
      simpa only [Pi.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
        using hlei)
  exact (CKN.isSuitableWeakSolution_iff_integrable).2 hintergrable

/-- The hypotheses of `thm:ess-local` supply the local data clauses of CKN
suitability on the full open unit cylinder. -/
theorem essLocal_suitableData_of_inputs
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hp : AEStronglyMeasurable p
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL2 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i)) :
    CKN.IsSuitableWeakSolutionData
      (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) 3 u Du p (0 : ParabolicPoint → Vec3) := by
  have hL2top := hL2
  refine ⟨isOpen_vec3Ball _ _, isOpen_Ioo, ordConnected_Ioo, by norm_num, ?_, ?_⟩
  · intro Ω' J hbox i
    change MemLp (fun z : ParabolicPoint => (0 : Vec3) i)
      (ENNReal.ofReal 3) (volume.restrict (spaceTimeSet Ω' J))
    simp
  · intro Ω' J hbox
    have hΩ'B : Ω' ⊆ vec3Ball (0 : Vec3) 1 :=
      subset_closure.trans hbox.2.2.1
    have hJ : J ⊆ Ioo (-1 : ℝ) 0 := subset_closure.trans hbox.2.2.2.2.2
    have hsub : spaceTimeSet Ω' J ⊆
        spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) :=
      Set.prod_mono hΩ'B hJ
    have hmeasure : volume.restrict (spaceTimeSet Ω' J) ≤
        volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0)) :=
      Measure.restrict_mono hsub le_rfl
    have henergy' : (∫⁻ z in spaceTimeSet Ω' J,
        ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ :=
      (lintegral_mono_set hsub).trans_lt henergy
    let A : ℝ≥0∞ := essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1) 0))
    have hAtop : A < ⊤ := by simpa only [A] using hL2top
    have hL2ae : ∀ᵐ t ∂(volume.restrict J),
        ∫⁻ x in Ω', ‖u (x, t)‖ₑ ^ (2 : ℝ) ≤ A := by
      have hglobal := ENNReal.ae_le_essSup (μ := volume.restrict (Ioo (-1) 0))
        (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
      have hglobalJ := hglobal.filter_mono
        (ae_mono (Measure.restrict_mono hJ le_rfl))
      filter_upwards [hglobalJ] with t ht
      exact (lintegral_mono_set hΩ'B).trans (by simpa only [A] using ht)
    have hL2' : essSup (fun t => ∫⁻ x in Ω', ‖u (x, t)‖ₑ ^ (2 : ℝ))
        (volume.restrict J) < ⊤ :=
      (essSup_le_of_ae_le A hL2ae).trans_lt hAtop
    have hgrad' : ∀ i : Fin 3, ∀ᵐ t ∂(volume.restrict J),
        HasWeakGradientOn Ω' (fun x => u (x, t) i) (fun x => Du (x, t) i) := by
      have hgradJ := hgrad.filter_mono
        (ae_mono (Measure.restrict_mono hJ le_rfl))
      intro i
      filter_upwards [hgradJ] with t ht
      exact (ht i).restrict hbox.1 hΩ'B
    exact ⟨hu.mono_measure hmeasure, hDu.mono_measure hmeasure,
      hp.mono_measure hmeasure, aestronglyMeasurable_const,
      hL2', henergy', hpLp.mono_measure hmeasure, by simp, hgrad'⟩

end ESS
