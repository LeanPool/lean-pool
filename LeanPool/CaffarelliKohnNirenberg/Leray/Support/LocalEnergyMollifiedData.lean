/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyMollifiedMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyWeakGradient
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearCounterexample.FactorDerivative

/-!
# Local Energy Mollified Data

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CKN

/-- Transfer a space-time MemLp bound from the parabolic coordinate carrier to the product
coordinate carrier. -/
theorem localEnergy_memLp_parabolic_to_product
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ParabolicPoint → E} {p : ℝ≥0∞}
    (hf : MemLp f p
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0)))) :
    MemLp (fun z : Vec3 × ℝ => f z) p
      ((volume : Measure (Vec3 × ℝ)).restrict
        (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0)) := by
  have hparaMeas : MeasurableSet
      (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0)) := by
    exact (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball (0 : Vec3) 1) isOpen_Ioo).measurableSet
  have hpre : parabolicHomeomorph.symm ⁻¹'
      spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) =
        vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0 := by
    ext z
    rfl
  have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hparaMeas
  rw [hpre] at hmp
  have h := hf.comp_measurePreserving hmp
  change MemLp (fun z : Vec3 × ℝ => f (parabolicHomeomorph.symm z)) p _ at h
  have hfun : (fun z : Vec3 × ℝ => f (parabolicHomeomorph.symm z)) =
      (fun z => f z) := by
    funext z
    cases z
    rfl
  rw [hfun] at h
  exact h

/-- The E1 momentum identity, extended by zero, remains a global weak identity for compactly
supported tests in the unit cylinder. -/
theorem essLocal_mollifiedMomentumWeak_of_essLocalData
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hS3 : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z = 0)
    (φ : Vec3 × ℝ → Vec3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0) :
    ∫ z, mollifiedMomentumWeakIntegrand
      (fun y => (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator u y)
      (fun y i j => (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
        (fun q => u q i * u q j) y)
      (fun y i j => (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
        (fun q => Du q i j) y)
      (fun y => (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator p y)
      φ z ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
  let B : Set Vec3 := vec3Ball (0 : Vec3) 1
  let J : Set ℝ := Ioo (-1) 0
  let U : Set (Vec3 × ℝ) := B ×ˢ J
  have hUmeas : MeasurableSet U := by
    dsimp [U, B, J]
    exact (isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod measurableSet_Ioo
  have hBclosure : IsCompact (closure B) := by
    simpa [B] using (isCompact_closure_vec3Ball
      (x := (0 : Vec3)) (r := (1 : ℝ)) (by norm_num))
  have hKcompact : IsCompact (closure B ×ˢ Set.Icc (-1 : ℝ) 0) :=
    hBclosure.prod isCompact_Icc
  have hUK : U ⊆ closure B ×ˢ Set.Icc (-1 : ℝ) 0 := by
    exact Set.prod_mono subset_closure (by
      intro t ht
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  have hUfinite : (volume : Measure (Vec3 × ℝ)) U < ⊤ :=
    lt_of_le_of_lt (measure_mono hUK) hKcompact.measure_lt_top
  let _ : IsFiniteMeasure ((volume : Measure (Vec3 × ℝ)).restrict U) := ⟨by
    rw [Measure.restrict_apply_univ U]
    exact hUfinite
  ⟩
  have hφi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 × ℝ => φ y i) :=
    (contDiff_apply ℝ ℝ i).comp hφ
  have hpoint (z : Vec3 × ℝ) :
      mollifiedMomentumWeakIntegrand
        (fun y => U.indicator u y)
        (fun y i j => U.indicator (fun q => u q i * u q j) y)
        (fun y i j => U.indicator (fun q => Du q i j) y)
        (fun y => U.indicator p y) φ z =
      U.indicator (fun q : Vec3 × ℝ =>
        (-(∑ i : Fin 3, u q i * timePartial (fun y => φ y i) q))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u q i * u q j * spatialPartial (fun y => φ y i) j q
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du q i j * spatialPartial (fun y => φ y i) j q
          - p q * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i q) z := by
    by_cases hz : z ∈ U
    · have huInd : U.indicator u z = u z := Set.indicator_of_mem hz u
      have hpInd : U.indicator p z = p z := Set.indicator_of_mem hz p
      have hFInd (i j : Fin 3) :
          U.indicator (fun q => u q i * u q j) z = u z i * u z j :=
        Set.indicator_of_mem hz _
      have hGInd (i j : Fin 3) :
          U.indicator (fun q => Du q i j) z = Du z i j :=
        Set.indicator_of_mem hz _
      have hRInd : U.indicator (fun q : Vec3 × ℝ =>
          (-(∑ i : Fin 3, u q i * timePartial (fun y => φ y i) q))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u q i * u q j * spatialPartial (fun y => φ y i) j q
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du q i j * spatialPartial (fun y => φ y i) j q
            - p q * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i q) z =
          (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u z i * u z j * spatialPartial (fun y => φ y i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du z i j * spatialPartial (fun y => φ y i) j z
            - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z :=
        Set.indicator_of_mem hz _
      dsimp [mollifiedMomentumWeakIntegrand, energyDirDeriv, energyTimeDir,
        energySpatialDir]
      simp_rw [← CKN.timePartial_eq_joint_fderiv (hφi _) z,
        ← CKN.spatialPartial_eq_joint_fderiv (hφi _) z]
      rw [huInd, hpInd]
      simp_rw [hFInd, hGInd, hRInd]
      rfl
    · have huInd : U.indicator u z = 0 := Set.indicator_of_notMem hz u
      have hpInd : U.indicator p z = 0 := Set.indicator_of_notMem hz p
      have hFInd (i j : Fin 3) : U.indicator (fun q => u q i * u q j) z = 0 :=
        Set.indicator_of_notMem hz _
      have hGInd (i j : Fin 3) : U.indicator (fun q => Du q i j) z = 0 :=
        Set.indicator_of_notMem hz _
      have hRInd : U.indicator (fun q : Vec3 × ℝ =>
          (-(∑ i : Fin 3, u q i * timePartial (fun y => φ y i) q))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u q i * u q j * spatialPartial (fun y => φ y i) j q
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du q i j * spatialPartial (fun y => φ y i) j q
            - p q * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i q) z = 0 :=
        Set.indicator_of_notMem hz _
      simp [mollifiedMomentumWeakIntegrand, energyDirDeriv,
        energyTimeDir, energySpatialDir, huInd, hpInd, hFInd, hGInd, hRInd]
  have htest : (show ParabolicPoint → Vec3 from φ) ∈
      spaceTimeTestFunction (V := Vec3) B J := by
    refine ⟨hφ, hφc, ?_⟩
    simpa [B, J, spaceTimeSet] using hφU
  calc
    _ = ∫ z, U.indicator (fun q : Vec3 × ℝ =>
          ((-(∑ i : Fin 3, u q i * timePartial (fun y => φ y i) q))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u q i * u q j * spatialPartial (fun y => φ y i) j q
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du q i j * spatialPartial (fun y => φ y i) j q
            - p q * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i q)) z
          ∂(volume : Measure (Vec3 × ℝ)) := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact hpoint z
    _ = ∫ z in U,
          (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u z i * u z j * spatialPartial (fun y => φ y i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du z i j * spatialPartial (fun y => φ y i) j z
            - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          ∂(volume : Measure (Vec3 × ℝ)) := integral_indicator hUmeas
    _ = 0 := by
        have hmpre : parabolicHomeomorph.symm ⁻¹'
            spaceTimeSet B J = U := by
          ext z
          rfl
        have hparaMeas : MeasurableSet (spaceTimeSet B J) := by
          exact (isOpen_spaceTimeSet B J (isOpen_vec3Ball (0 : Vec3) 1)
            isOpen_Ioo).measurableSet
        have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hparaMeas
        rw [hmpre] at hmp
        have hconvert :
            (∫ z in U,
              (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
                - ∑ i : Fin 3, ∑ j : Fin 3,
                    u z i * u z j * spatialPartial (fun y => φ y i) j z
                + ∑ i : Fin 3, ∑ j : Fin 3,
                    Du z i j * spatialPartial (fun y => φ y i) j z
                - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
              ∂(volume : Measure (Vec3 × ℝ))) =
            ∫ z in spaceTimeSet B J,
              (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
                - ∑ i : Fin 3, ∑ j : Fin 3,
                    u z i * u z j * spatialPartial (fun y => φ y i) j z
                + ∑ i : Fin 3, ∑ j : Fin 3,
                    Du z i j * spatialPartial (fun y => φ y i) j z
                - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
              ∂(volume : Measure ParabolicPoint) := by
          have hcomp := hmp.integral_comp parabolicHomeomorph.symm.measurableEmbedding
            (fun z : ParabolicPoint =>
              (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
                - ∑ i : Fin 3, ∑ j : Fin 3,
                    u z i * u z j * spatialPartial (fun y => φ y i) j z
                + ∑ i : Fin 3, ∑ j : Fin 3,
                    Du z i j * spatialPartial (fun y => φ y i) j z
                - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
          simpa [U, B, J, spaceTimeSet, parabolicHomeomorph_symm_apply] using hcomp
        rw [hconvert]
        exact hS3 (show ParabolicPoint → Vec3 from φ) (by
          simpa [B, J, spaceTimeSet] using htest)

/-- The E1 divergence identity, extended by zero, remains a global weak identity for compactly
supported tests in the unit cylinder. -/
theorem essLocal_mollifiedDivergenceWeak_of_essLocalData
    {u : ParabolicPoint → Vec3}
    (hS2 : ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0) :
    ∫ z, ∑ i : Fin 3,
      (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator u z i *
        (fderiv ℝ ψ z) (energySpatialDir i)
      ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
  let B : Set Vec3 := vec3Ball (0 : Vec3) 1
  let J : Set ℝ := Ioo (-1) 0
  let U : Set (Vec3 × ℝ) := B ×ˢ J
  have hUmeas : MeasurableSet U := by
    dsimp [U, B, J]
    exact (isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod measurableSet_Ioo
  have hpoint (z : Vec3 × ℝ) :
      (∑ i : Fin 3, U.indicator u z i * (fderiv ℝ ψ z) (energySpatialDir i)) =
        U.indicator (fun q : Vec3 × ℝ =>
          ∑ i : Fin 3, u q i * spatialPartial (show ParabolicPoint → ℝ from ψ) i q) z := by
    by_cases hz : z ∈ U
    · have huInd : U.indicator u z = u z := Set.indicator_of_mem hz u
      have hRInd : U.indicator (fun q : Vec3 × ℝ =>
          ∑ i : Fin 3, u q i * spatialPartial (show ParabolicPoint → ℝ from ψ) i q) z =
          ∑ i : Fin 3, u z i * spatialPartial (show ParabolicPoint → ℝ from ψ) i z :=
        Set.indicator_of_mem hz _
      rw [huInd]
      have hpartial (i : Fin 3) :
          (fderiv ℝ ψ z) (energySpatialDir i) =
            spatialPartial (show ParabolicPoint → ℝ from ψ) i z := by
        rw [CKN.spatialPartial_eq_joint_fderiv hψ z i]
        rfl
      simp_rw [hpartial]
      rw [hRInd]
    · have huInd : U.indicator u z = 0 := Set.indicator_of_notMem hz u
      have hRInd : U.indicator (fun q : Vec3 × ℝ =>
          ∑ i : Fin 3, u q i * spatialPartial (show ParabolicPoint → ℝ from ψ) i q) z = 0 :=
        Set.indicator_of_notMem hz _
      rw [huInd]
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, hRInd]
  have htest : (show ParabolicPoint → ℝ from ψ) ∈
      spaceTimeTestFunction (V := ℝ) B J := by
    refine ⟨hψ, hψc, ?_⟩
    simpa [B, J, spaceTimeSet] using hψU
  calc
    _ = ∫ z, U.indicator (fun q : Vec3 × ℝ =>
          ∑ i : Fin 3, u q i * spatialPartial
            (show ParabolicPoint → ℝ from ψ) i q) z
          ∂(volume : Measure (Vec3 × ℝ)) := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact hpoint z
    _ = ∫ z in U, ∑ i : Fin 3, u z i * spatialPartial
          (show ParabolicPoint → ℝ from ψ) i z
          ∂(volume : Measure (Vec3 × ℝ)) := integral_indicator hUmeas
    _ = 0 := by
        have hparaMeas : MeasurableSet (spaceTimeSet B J) := by
          exact (isOpen_spaceTimeSet B J (isOpen_vec3Ball (0 : Vec3) 1)
            isOpen_Ioo).measurableSet
        have hpre : parabolicHomeomorph.symm ⁻¹' spaceTimeSet B J = U := by
          ext z
          rfl
        have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hparaMeas
        rw [hpre] at hmp
        have hconvert :
            (∫ z in U, ∑ i : Fin 3, u z i * spatialPartial
                (show ParabolicPoint → ℝ from ψ) i z
                ∂(volume : Measure (Vec3 × ℝ))) =
              ∫ z in spaceTimeSet B J, ∑ i : Fin 3,
                u z i * spatialPartial (show ParabolicPoint → ℝ from ψ) i z
                ∂(volume : Measure ParabolicPoint) := by
          have hcomp := hmp.integral_comp parabolicHomeomorph.symm.measurableEmbedding
            (fun z : ParabolicPoint =>
              ∑ i : Fin 3, u z i * spatialPartial
                (show ParabolicPoint → ℝ from ψ) i z)
          simpa [U, B, J, spaceTimeSet, parabolicHomeomorph_symm_apply] using hcomp
        rw [hconvert]
        exact hS2 (show ParabolicPoint → ℝ from ψ) (by
          simpa [B, J, spaceTimeSet] using htest)

/-- The E1 momentum identity gives the pointwise equation for local mollifications of the
zero-extended fields. -/
theorem essLocal_mollifiedMomentumEquation_of_essLocalData
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hS2 : ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
    (hS3 : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z = 0)
    {δ : ℝ} (hδ : 0 < δ) {z : Vec3 × ℝ}
    (hz : Metric.closedBall z δ ⊆ vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0) :
    (∀ i : Fin 3,
      (fderiv ℝ (spaceTimeMollify
        (fun y : Vec3 × ℝ =>
          (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator u y i) δ hδ) z)
          energyTimeDir
        + ∑ j : Fin 3,
            (fderiv ℝ (spaceTimeMollify
              (fun y : Vec3 × ℝ =>
                (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
                  (fun q => u q i * u q j) y) δ hδ) z) (energySpatialDir j)
        - ∑ j : Fin 3,
            (fderiv ℝ (spaceTimeMollify
              (fun y : Vec3 × ℝ =>
                (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
                  (fun q => Du q i j) y) δ hδ) z) (energySpatialDir j)
        + (fderiv ℝ (spaceTimeMollify
            (fun y : Vec3 × ℝ =>
              (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator p y) δ hδ) z)
            (energySpatialDir i) = 0) ∧
      ∑ i : Fin 3,
        (fderiv ℝ (spaceTimeMollify
          (fun y : Vec3 × ℝ =>
            (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator u y i) δ hδ) z)
          (energySpatialDir i) = 0 := by
  let B : Set Vec3 := vec3Ball (0 : Vec3) 1
  let J : Set ℝ := Ioo (-1) 0
  let U : Set (Vec3 × ℝ) := B ×ˢ J
  let uExt : Vec3 × ℝ → Vec3 := U.indicator u
  let FExt : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun y i j =>
    U.indicator (fun q => u q i * u q j) y
  let GExt : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun y i j =>
    U.indicator (fun q => Du q i j) y
  let pExt : Vec3 × ℝ → ℝ := U.indicator p
  have hUmeas : MeasurableSet U := by
    dsimp [U, B, J]
    exact (isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod measurableSet_Ioo
  have hL2 := energyL2_components_memLp hu hDu henergy
  have hBclosure : IsCompact (closure B) := by
    simpa [B] using (isCompact_closure_vec3Ball
      (x := (0 : Vec3)) (r := (1 : ℝ)) (by norm_num))
  have hKcompact : IsCompact (closure B ×ˢ Set.Icc (-1 : ℝ) 0) :=
    hBclosure.prod isCompact_Icc
  have hUK : U ⊆ closure B ×ˢ Set.Icc (-1 : ℝ) 0 := by
    exact Set.prod_mono subset_closure (by
      intro t ht
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  have hUfinite : (volume : Measure (Vec3 × ℝ)) U < ⊤ :=
    lt_of_le_of_lt (measure_mono hUK) hKcompact.measure_lt_top
  let _ : IsFiniteMeasure ((volume : Measure (Vec3 × ℝ)).restrict U) := ⟨by
    rw [Measure.restrict_apply_univ U]
    exact hUfinite
  ⟩
  have hu2 (i : Fin 3) : MemLp (fun y : Vec3 × ℝ => u y i) 2
      ((volume : Measure (Vec3 × ℝ)).restrict U) := by
    have h := localEnergy_memLp_parabolic_to_product ((memLp_pi_iff.mp hL2.1) i)
    simpa [B, J] using h
  have hDu2 (i j : Fin 3) : MemLp (fun y : Vec3 × ℝ => Du y i j) 2
      ((volume : Measure (Vec3 × ℝ)).restrict U) := by
    have h := localEnergy_memLp_parabolic_to_product
      ((memLp_pi_iff.mp ((memLp_pi_iff.mp hL2.2) i)) j)
    simpa [B, J] using h
  have hF1 (i j : Fin 3) : MemLp (fun y : Vec3 × ℝ => u y i * u y j) 1
      ((volume : Measure (Vec3 × ℝ)).restrict U) := by
    exact (hu2 i).mul (hu2 j)
  have huLoc (i : Fin 3) : LocallyIntegrable (fun y : Vec3 × ℝ => uExt y i)
      (volume : Measure (Vec3 × ℝ)) := by
    have hInt : Integrable (U.indicator (fun y : Vec3 × ℝ => u y i))
        (volume : Measure (Vec3 × ℝ)) :=
      (integrable_indicator_iff hUmeas).2 ((hu2 i).integrable (by norm_num))
    have hfun : (fun y : Vec3 × ℝ => uExt y i) = U.indicator (fun q => u q i) := by
      funext y
      by_cases hy : y ∈ U <;> simp [uExt, Set.indicator, hy]
    rw [hfun]
    exact hInt.locallyIntegrable
  have hFLoc (i j : Fin 3) : LocallyIntegrable (fun y : Vec3 × ℝ => FExt y i j)
      (volume : Measure (Vec3 × ℝ)) := by
    have hInt : Integrable
        (U.indicator (fun y : Vec3 × ℝ => u y i * u y j))
        (volume : Measure (Vec3 × ℝ)) :=
      (integrable_indicator_iff hUmeas).2 ((hF1 i j).integrable (by norm_num))
    simpa [FExt] using hInt.locallyIntegrable
  have hGLoc (i j : Fin 3) : LocallyIntegrable (fun y : Vec3 × ℝ => GExt y i j)
      (volume : Measure (Vec3 × ℝ)) := by
    have hInt : Integrable (U.indicator (fun y : Vec3 × ℝ => Du y i j))
        (volume : Measure (Vec3 × ℝ)) :=
      (integrable_indicator_iff hUmeas).2 ((hDu2 i j).integrable (by norm_num))
    simpa [GExt] using hInt.locallyIntegrable
  have hpProd : MemLp (fun y : Vec3 × ℝ => p y) (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict U) := by
    have h := localEnergy_memLp_parabolic_to_product hpLp
    simpa [B, J, U] using h
  have hpLoc : LocallyIntegrable pExt (volume : Measure (Vec3 × ℝ)) := by
    have hInt : Integrable (U.indicator p) (volume : Measure (Vec3 × ℝ)) :=
      (integrable_indicator_iff hUmeas).2 (hpProd.integrable (by norm_num))
    simpa [pExt] using hInt.locallyIntegrable
  have hweak : ∀ φ : Vec3 × ℝ → Vec3, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ y, mollifiedMomentumWeakIntegrand uExt FExt GExt pExt φ y
        ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
    intro φ hφ hφc hφsupport
    simpa [uExt, FExt, GExt, pExt, U, B, J] using
      essLocal_mollifiedMomentumWeak_of_essLocalData hS3 φ hφ hφc hφsupport
  have hPDE := spaceTimeMollify_momentum_fderiv_of_weak hweak huLoc hFLoc hGLoc hpLoc
    hδ (by simpa [U, B, J] using hz)
  have hPDE' := by simpa [uExt, FExt, GExt, pExt, U, B, J] using hPDE
  have hdivweak : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ y, ∑ i : Fin 3, uExt y i *
        (fderiv ℝ ψ y) (energySpatialDir i)
        ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
    intro ψ hψ hψc hψsupport
    simpa [uExt, U, B, J] using
      essLocal_mollifiedDivergenceWeak_of_essLocalData hS2 ψ hψ hψc hψsupport
  have hdiv := spaceTimeMollify_divergence_eq_zero_of_weak hdivweak huLoc hδ
    (by simpa [U, B, J] using hz)
  have hdiv' := by simpa [uExt, U, B, J] using hdiv
  exact ⟨by simpa [uExt, FExt, GExt, pExt, U, B, J] using hPDE',
    by simpa [uExt, U, B, J] using hdiv'⟩

end CKN
