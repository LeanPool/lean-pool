/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegEquicontinuityMain
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitTenThirds
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegPressureBound
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSlices
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegPressureL2
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMollified
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureLocalBound
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitMeasurability
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSpaceTime
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegEquicontinuityInputsData

/-!
# Reg Equicontinuity Inputs

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem regUniformPositiveTimeMeasure_eq_productSlab :
    regUniformPositiveTimeMeasure =
      (volume : Measure (Vec3 × ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) := by
  rfl

private theorem regEquicontinuity_pressure_bound_from_inputs
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hUc : ∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hC1 : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
         (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hU : ∀ j : Fin 3,
      MemLp (fun z : ParabolicPoint => u z j)
        (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure)
    (BU : ℝ) (hBU : 0 ≤ BU)
    (hUbound : ∀ j : Fin 3,
      eLpNorm (fun z : ParabolicPoint => u z j)
        (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure ≤
          ENNReal.ofReal BU)
    (hpc : ContinuousOn p (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hR4 : ∀ t : ℝ, 0 < t →
      ∃ hF : ∀ i j : Fin 3, MemLp
          (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
            u (x, t) j) (ENNReal.ofReal 2) volume,
        (fun x : Vec3 => p (x, t)) =ᵐ[volume]
          rieszPressureSliceRepresentative 2 (by norm_num)
            (fun i j => (hF i j).toLp
              (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j))) :
    MemLp p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure ∧
      eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure ≤
        ENNReal.ofReal
          (9 * rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) *
            ((3 * BU) * BU)) := by
  classical
  let q : ℝ≥0∞ := ENNReal.ofReal (10 / 3 : ℝ)
  let S : Set (Vec3 × ℝ) := Set.univ ×ˢ Ioi (0 : ℝ)
  let U : Vec3 × ℝ → Vec3 := fun z => u (z.1, z.2)
  let J : Vec3 × ℝ → Vec3 := fun z =>
    regUniformMollifiedVelocity ρ ε hε u (z.1, z.2)
  let Ubar : Vec3 × ℝ → Vec3 := S.indicator U
  let Jbar : Vec3 × ℝ → Vec3 := S.indicator J
  let F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
    regPressureSpaceTimeTensor Jbar Ubar
  have hSmeas : MeasurableSet S := by
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  have hPositiveTimeMeasure : regUniformPositiveTimeMeasure =
      (volume : Measure (Vec3 × ℝ)).restrict S := by
    simpa [S] using regUniformPositiveTimeMeasure_eq_productSlab
  have hJpositive := regEquicontinuity_mollified_velocity_tenThirds_bound
    ρ ε hε u hSlice hUc hC1 hU BU hBU hUbound
  have hUbarCompEq (j : Fin 3) :
      (fun z : Vec3 × ℝ => Ubar z j) =
        S.indicator (fun z : Vec3 × ℝ => U z j) := by
    funext z
    by_cases hz : z ∈ S <;> simp [Ubar, Set.indicator, hz]
  have hJbarCompEq (i : Fin 3) :
      (fun z : Vec3 × ℝ => Jbar z i) =
        S.indicator (fun z : Vec3 × ℝ => J z i) := by
    funext z
    by_cases hz : z ∈ S <;> simp [Jbar, Set.indicator, hz]
  have hUbarMem (j : Fin 3) :
      MemLp (fun z : Vec3 × ℝ => Ubar z j) q volume := by
    rw [hUbarCompEq j, memLp_indicator_iff_restrict hSmeas]
    have hpos := hU j
    rw [hPositiveTimeMeasure] at hpos
    change MemLp (fun z : Vec3 × ℝ => U z j) q (volume.restrict S) at hpos
    simpa [q] using hpos
  have hUbarBound (j : Fin 3) :
      eLpNorm (fun z : Vec3 × ℝ => Ubar z j) q volume ≤ ENNReal.ofReal BU := by
    rw [hUbarCompEq j, eLpNorm_indicator_eq_eLpNorm_restrict hSmeas]
    have hpos := hUbound j
    rw [hPositiveTimeMeasure] at hpos
    change eLpNorm (fun z : Vec3 × ℝ => U z j) q
      (volume.restrict S) ≤ ENNReal.ofReal BU at hpos
    simpa [q] using hpos
  have hJbarMem (i : Fin 3) :
      MemLp (fun z : Vec3 × ℝ => Jbar z i) q volume := by
    rw [hJbarCompEq i, memLp_indicator_iff_restrict hSmeas]
    have hpos := (hJpositive i).1
    rw [hPositiveTimeMeasure] at hpos
    change MemLp (fun z : Vec3 × ℝ => J z i) q (volume.restrict S) at hpos
    simpa [q] using hpos
  have hJbarBound (i : Fin 3) :
      eLpNorm (fun z : Vec3 × ℝ => Jbar z i) q volume ≤
        ENNReal.ofReal (3 * BU) := by
    rw [hJbarCompEq i, eLpNorm_indicator_eq_eLpNorm_restrict hSmeas]
    have hpos := (hJpositive i).2
    rw [hPositiveTimeMeasure] at hpos
    change eLpNorm (fun z : Vec3 × ℝ => J z i) q
      (volume.restrict S) ≤ ENNReal.ofReal (3 * BU) at hpos
    simpa [q] using hpos
  have hBJ : 0 ≤ 3 * BU := mul_nonneg (by norm_num) hBU
  obtain ⟨hF, _⟩ := regPressure_regularized_fiveThirds_bound
    Jbar Ubar hJbarMem hUbarMem (3 * BU) BU hBJ hBU hJbarBound hUbarBound
  have hFbound (i j : Fin 3) :
      eLpNorm (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
        (volume : Measure (Vec3 × ℝ)) ≤ ENNReal.ofReal ((3 * BU) * BU) := by
    have : ENNReal.HolderTriple (ENNReal.ofReal (10 / 3 : ℝ))
        (ENNReal.ofReal (10 / 3 : ℝ)) (ENNReal.ofReal (5 / 3 : ℝ)) := by
      have h : (10 / 3 : ℝ).HolderTriple (10 / 3 : ℝ) (5 / 3 : ℝ) :=
        ⟨by norm_num, by norm_num, by norm_num⟩
      exact h.ennrealOfReal
    have hHolder := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (p := ENNReal.ofReal (10 / 3 : ℝ))
      (q := ENNReal.ofReal (10 / 3 : ℝ))
      (r := ENNReal.ofReal (5 / 3 : ℝ))
      (fun a b : ℝ => a * b) 1 continuous_mul
      (hJbarMem i).aestronglyMeasurable (hUbarMem j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simp [Real.norm_eq_abs])
    calc
      eLpNorm (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
          (volume : Measure (Vec3 × ℝ)) ≤
        eLpNorm (fun z : Vec3 × ℝ => Jbar z i) (ENNReal.ofReal (10 / 3 : ℝ))
          (volume : Measure (Vec3 × ℝ)) *
        eLpNorm (fun z : Vec3 × ℝ => Ubar z j) (ENNReal.ofReal (10 / 3 : ℝ))
          (volume : Measure (Vec3 × ℝ)) := by
        change eLpNorm (fun z : Vec3 × ℝ => Jbar z i * Ubar z j)
          (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure (Vec3 × ℝ)) ≤ _
        simpa [ENNReal.smul_def, one_mul] using hHolder
      _ ≤ ENNReal.ofReal (3 * BU) * ENNReal.ofReal BU :=
        mul_le_mul (hJbarBound i) (hUbarBound j) (by positivity) (by positivity)
      _ = ENNReal.ofReal ((3 * BU) * BU) := by
        rw [← ENNReal.ofReal_mul hBJ]
  let Spara : Set ParabolicPoint := spaceTimeSet Set.univ (Ioi (0 : ℝ))
  let pbar : ParabolicPoint → ℝ := Spara.piecewise p (fun _ => 0)
  have hSparaMeas : MeasurableSet Spara := by
    change MeasurableSet (Set.univ ×ˢ Ioi (0 : ℝ))
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  have hpbarMeas : Measurable pbar := by
    simpa [pbar] using lerayLimit_measurableOn_extension Spara hSparaMeas
      p (fun _ => 0) hpc continuousOn_const
  have hR4bridge : ∀ t : ℝ, 0 < t → ∃ hFt : ∀ i j,
      MemLp (fun x : Vec3 => F i j (x, t)) (ENNReal.ofReal (2 : ℝ)) volume,
      (fun x : Vec3 => pbar (x, t)) =ᵐ[volume]
        rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
          (fun i j => (hFt i j).toLp (fun x : Vec3 => F i j (x, t))) := by
    intro t ht
    obtain ⟨hF2, hpEq⟩ := hR4 t ht
    have hFsliceEq (i j : Fin 3) (x : Vec3) :
        F i j (x, t) =
          regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j := by
      have hz : (x, t) ∈ S := by
        exact ⟨Set.mem_univ _, ht⟩
      simp [F, regPressureSpaceTimeTensor, Ubar, Jbar, U, J, hz]
    have hFt (i j : Fin 3) :
        MemLp (fun x : Vec3 => F i j (x, t)) (ENNReal.ofReal (2 : ℝ)) volume := by
      apply (memLp_congr_ae (Filter.Eventually.of_forall (hFsliceEq i j))).2
      exact hF2 i j
    have hclass (i j : Fin 3) :
        (hFt i j).toLp (fun x : Vec3 => F i j (x, t)) =
          (hF2 i j).toLp
            (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u
              (x, t) i * u (x, t) j) := by
      apply Lp.ext
      filter_upwards [(hFt i j).coeFn_toLp, (hF2 i j).coeFn_toLp]
        with x hleft hright
      exact hleft.trans ((hFsliceEq i j x).trans hright.symm)
    have hrep :
        rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
          (fun i j => (hFt i j).toLp (fun x : Vec3 => F i j (x, t))) =
        rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
          (fun i j => (hF2 i j).toLp
            (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u
              (x, t) i * u (x, t) j)) := by
      congr 1
      funext i j
      exact hclass i j
    refine ⟨hFt, ?_⟩
    filter_upwards [hpEq] with x hx
    have hpbarSlice : pbar (x, t) = p (x, t) := by
      have hxt : ((x, t) : ParabolicPoint) ∈ Spara := by
        exact ⟨Set.mem_univ _, ht⟩
      change Spara.piecewise p (fun _ => 0) (x, t) = p (x, t)
      exact Set.piecewise_eq_of_mem _ _ _ hxt
    rw [hpbarSlice, hrep]
    exact hx
  obtain ⟨hpbar, hPressureNorm⟩ := regEquicontinuity_pressure_memLp_fiveThirds
    F hF ((3 * BU) * BU) (mul_nonneg hBJ hBU) hFbound pbar hpbarMeas hR4bridge
  have hOp : 0 ≤ rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) := by
    exact le_trans (norm_nonneg _) <|
      rieszPressureSpaceTimeComponent_norm_le (5 / 3 : ℝ) (by norm_num)
        (0 : Fin 3) (0 : Fin 3)
  let P : ℝ :=
    9 * rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) * ((3 * BU) * BU)
  have hPnonneg : 0 ≤ P := by positivity
  have : Fact (1 ≤ ENNReal.ofReal (5 / 3 : ℝ)) := ⟨by norm_num⟩
  have hNormId : eLpNorm pbar (ENNReal.ofReal (5 / 3 : ℝ))
        regUniformPositiveTimeMeasure = ENNReal.ofReal ‖hpbar.toLp pbar‖ := by
    rw [← ENNReal.ofReal_toReal hpbar.eLpNorm_ne_top, Lp.norm_toLp pbar hpbar]
  have hpbarBound :
      eLpNorm pbar (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure ≤
        ENNReal.ofReal P := by
    rw [hNormId]
    apply ENNReal.ofReal_le_ofReal
    simpa [P] using hPressureNorm
  have hPressureEq : p =ᵐ[regUniformPositiveTimeMeasure] pbar := by
    filter_upwards [ae_restrict_mem hSparaMeas] with z hz
    change p z = Spara.piecewise p (fun _ => 0) z
    exact (Set.piecewise_eq_of_mem _ _ _ hz).symm
  constructor
  · exact (memLp_congr_ae hPressureEq).2 hpbar
  · rw [eLpNorm_congr_ae hPressureEq]
    exact hpbarBound

/-- The time-pairing modulus in `lem:compactness` follows from the regularized
solution contract and the pressure representation. -/
theorem regEquicontinuity_modulus_of_regularised_contract
    (ρ : RegMollifierProfile)
    (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
    (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)
    (hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
      (hε : 0 < ε),
      let u := uε a ha ε
      let p := pε a ha ε
      let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
        spatialPartial (fun y => u y i) j z
      let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
        spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
      let Dt : ParabolicPoint → Vec3 := fun z i => timePartial (fun y => u y i) z
      let Dp : ParabolicPoint → Vec3 := fun z i => spatialPartial (fun y => p y) i z
      (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
        Continuous (fun t : Set.Ici (0 : ℝ) =>
          realVectorL2OfCoordinateFunction
            (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
        (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
          regUniformMollifiedInitial ρ ε hε a ∧
        ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2 (fun x => u (x, t))) ∧
      (∀ i : Fin 3, ContinuousOn (fun z => u z i)
        (spaceTimeSet Set.univ (Ioi 0))) ∧
      (∀ i j, ContinuousOn (fun z => D z i j)
        (spaceTimeSet Set.univ (Ioi 0))) ∧
      (∀ i j k, ContinuousOn (fun z => DD z i j k)
        (spaceTimeSet Set.univ (Ioi 0))) ∧
      (∀ i, ContinuousOn (fun z => Dt z i)
        (spaceTimeSet Set.univ (Ioi 0))) ∧
      ContinuousOn p (spaceTimeSet Set.univ (Ioi 0)) ∧
      (∀ i, ContinuousOn (fun z => Dp z i)
        (spaceTimeSet Set.univ (Ioi 0))) ∧
      (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
         (spaceTimeSet Set.univ (Ioi 0))) ∧
      (∀ z ∈ spaceTimeSet Set.univ (Ioi 0), ∀ i j,
        DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
      (∀ z ∈ spaceTimeSet Set.univ (Ioi 0),
        DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T →
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ z ∈ spaceTimeSet Set.univ (Icc δ T),
            vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
            (∀ i j, |D z i j| ≤ C) ∧
            (∀ i j k, |DD z i j k| ≤ C) ∧
            (∀ i, |Dt z i| ≤ C) ∧ (∀ i, |Dp z i| ≤ C)) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T →
        (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
        (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
        (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
        (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
        MemLp p 2 (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
      (∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
        Dt z i - (∑ j : Fin 3, DD z i j j) +
          (∑ j : Fin 3,
            regUniformMollifiedVelocity ρ ε hε u z j * D z i j) + Dp z i = 0) ∧
      (∀ t : ℝ, 0 < t →
        ∃ hF : ∀ i j : Fin 3, MemLp
            (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
              u (x, t) j) (ENNReal.ofReal 2) volume,
          (fun x : Vec3 => p (x, t)) =ᵐ[volume]
            rieszPressureSliceRepresentative 2 (by norm_num)
              (fun i j => (hF i j).toLp
                (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                  u (x, t) j)) ∧
          ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
            (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
              -∑ i : Fin 3, ∑ j : Fin 3,
                ∫ x : Vec3,
                  regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                    u (x, t) j * mixedSecond ψ i j x) ∧
      (∀ t : ℝ, 0 ≤ t →
        eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
          2 * regUniformDissipation u D t =
        eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
          2 volume ^ (2 : ℕ))) :
    ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (_hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (C : Set Vec3) (_hC : IsCompact C)
      (_hCU : C ⊆ (Set.univ : Set Vec3))
      (s₀ s₁ : ℝ) (_hs₀s₁ : Icc s₀ s₁ ⊆ Ioi (0 : ℝ))
      (w : Vec3 → L2Vec3) (_hw : ContDiff ℝ (⊤ : ℕ∞) w)
      (_hwc : HasCompactSupport w) (_hws : tsupport w ⊆ C),
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n s t, s ∈ Icc s₀ s₁ → t ∈ Icc s₀ s₁ →
          |(∫ x : Vec3, ∑ i : Fin 3,
              uε a ha (εseq n) (x, t) i * w x i ∂volume) -
            (∫ x : Vec3, ∑ i : Fin 3,
              uε a ha (εseq n) (x, s) i * w x i ∂volume)| ≤
            A * dist t s + B * (dist t s) ^ θ := by
  let hregData := regEquicontinuity_data_of_regularised_contract
    ρ uε pε hregularised
  have hregPressureBound :
      ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
        (εseq : ℕ → ℝ) (_hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1),
        ∃ P : ℝ, 0 ≤ P ∧ ∀ n,
          MemLp (pε a ha (εseq n)) (ENNReal.ofReal (5 / 3 : ℝ))
            regUniformPositiveTimeMeasure ∧
          eLpNorm (pε a ha (εseq n)) (ENNReal.ofReal (5 / 3 : ℝ))
            regUniformPositiveTimeMeasure ≤ ENNReal.ofReal P := by
    intro a ha εseq hseq
    obtain ⟨B, hB, hUBounds⟩ :=
      regEquicontinuity_regularized_velocity_tenThirds_bound
        ρ uε pε hregularised a ha εseq hseq
    let P : ℝ := 9 * rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) *
      ((3 * B) * B)
    have hOp : 0 ≤ rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) := by
      exact le_trans (norm_nonneg _) <|
        rieszPressureSpaceTimeComponent_norm_le (5 / 3 : ℝ) (by norm_num)
          (0 : Fin 3) (0 : Fin 3)
    have hP0 : 0 ≤ P := by positivity
    refine ⟨P, hP0, ?_⟩
    intro n
    rcases hregData a ha εseq hseq with
      ⟨hSlice, _, hUc, _, _, _, _, _, hC1, _, _, _, _, _⟩
    rcases hregularised a ha (εseq n) (hseq n).1 with
      ⟨_, _, _, _, _, hpc, _, _, _, _, _, _, _, hR4full, _⟩
    have hR4small : ∀ t : ℝ, 0 < t →
        ∃ hF : ∀ i j : Fin 3, MemLp
            (fun x : Vec3 => regUniformMollifiedVelocity ρ (εseq n)
              (hseq n).1 (uε a ha (εseq n)) (x, t) i *
              uε a ha (εseq n) (x, t) j) (ENNReal.ofReal 2) volume,
          (fun x : Vec3 => pε a ha (εseq n) (x, t)) =ᵐ[volume]
            rieszPressureSliceRepresentative 2 (by norm_num)
              (fun i j => (hF i j).toLp
                (fun x : Vec3 => regUniformMollifiedVelocity ρ (εseq n)
                  (hseq n).1 (uε a ha (εseq n)) (x, t) i *
                  uε a ha (εseq n) (x, t) j)) := by
      intro t ht
      obtain ⟨hF, hpEq, _⟩ := hR4full t ht
      exact ⟨hF, hpEq⟩
    have hbound := regEquicontinuity_pressure_bound_from_inputs
      ρ (εseq n) (hseq n).1 (uε a ha (εseq n)) (pε a ha (εseq n))
      (hSlice n) (fun i => hUc n i) (hC1 n)
      (fun j => (hUBounds n j).1) B hB (fun j => (hUBounds n j).2)
      hpc hR4small
    simpa [P] using hbound
  exact regEquicontinuity_modulus ρ uε pε hregData hregPressureBound

end CKN.Leray

end
