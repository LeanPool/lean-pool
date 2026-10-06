/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayAssemblyContracts
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessMain
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropMollifier
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitConvergence
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitMeasurability
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitSliceBridge
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitTailLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessEnergyLower
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Mathlib.Topology.MetricSpace.Bounded
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitSpaceTime
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitTightness
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMollified
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformSlices
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformTenThirds
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedMildInitialData

/-!
# Leray Limit Main

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

theorem lerayLimit_eLpNorm_two_sq_eq_lintegral
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (2 : ℝ≥0∞) μ ^ (2 : ℝ) =
      ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_mul]
  norm_num

theorem lerayLimit_contDiff_spatial_slices
    (u : ParabolicPoint → Vec3)
    (P : Set ParabolicPoint)
    (hC1 :
      (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i) P))
    (hP : ∀ t : ℝ, 0 < t → ∀ x : Vec3, (x, t) ∈ P) :
    ∀ t : ℝ, 0 < t → ∀ i : Fin 3,
      ContDiff ℝ 1 (fun x : Vec3 => u (x, t) i) := by
  intro t ht i
  let : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
  let : NormedAddCommGroup ParabolicPoint :=
    inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
  let : NormedSpace ℝ ParabolicPoint :=
    inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
  have hC1i : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z i) P := by
    change ContDiffOn ℝ 1 (fun z : ParabolicPoint => u z i) P
    exact hC1 i
  have hmap : ContDiff ℝ 1
      (fun x : Vec3 => ((x, t) : ParabolicPoint)) := by
    fun_prop
  have hcomp : ContDiff ℝ 1
      ((fun z : Vec3 × ℝ => u z i) ∘ fun x : Vec3 => (x, t)) :=
    hC1i.comp_contDiff hmap (hP t ht)
  change ContDiff ℝ 1 (fun x : Vec3 => u (x, t) i) at hcomp
  exact hcomp

private theorem lerayLimit_iterated_positiveTime_gradient_eq
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3) :
    (hDensity : Measurable (fun z : ParabolicPoint =>
      ENNReal.ofReal (spatialGradientSq u D z))) →
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
      ENNReal.ofReal (spatialGradientSq u D (x, t)) ∂volume ∂volume) =
      ∫⁻ z, ENNReal.ofReal (spatialGradientSq u D z)
        ∂regUniformPositiveTimeMeasure := by
  intro hDensity
  let μt : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hMeasure : regUniformPositiveTimeMeasure =
      (volume : Measure Vec3).prod μt := by
    unfold regUniformPositiveTimeMeasure
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Ioi (0 : ℝ)) = _
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Ioi (0 : ℝ))]
    simp [μt, Measure.restrict_univ]
  have hProductDensity : AEMeasurable
      (fun z : Vec3 × ℝ => ENNReal.ofReal (spatialGradientSq u D z))
      ((volume : Measure Vec3).prod μt) := by
    exact hDensity.aemeasurable
  have hUncurriedDensity : AEMeasurable
      (Function.uncurry (fun x t => ENNReal.ofReal
        (spatialGradientSq u D ((x, t) : ParabolicPoint))))
      ((volume : Measure Vec3).prod μt) := by
    have hEq : (fun z : Vec3 × ℝ =>
        ENNReal.ofReal (spatialGradientSq u D z)) =
        Function.uncurry (fun x t => ENNReal.ofReal
          (spatialGradientSq u D ((x, t) : ParabolicPoint))) := by
      funext z
      rcases z with ⟨x, t⟩
      rfl
    exact hProductDensity.congr
      (Filter.Eventually.of_forall fun z => congrFun hEq z)
  calc
    _ = ∫⁻ t : ℝ, ∫⁻ x : Vec3,
        ENNReal.ofReal (spatialGradientSq u D (x, t)) ∂volume ∂μt := by
      rfl
    _ = ∫⁻ x : Vec3, ∫⁻ t : ℝ,
      ENNReal.ofReal (spatialGradientSq u D (x, t)) ∂μt ∂volume :=
      (MeasureTheory.lintegral_lintegral_swap
        (μ := (volume : Measure Vec3)) (ν := μt)
        (f := fun x t => ENNReal.ofReal
          (spatialGradientSq u D ((x, t) : ParabolicPoint)))
        hUncurriedDensity).symm
    _ = ∫⁻ z, ENNReal.ofReal (spatialGradientSq u D z)
        ∂regUniformPositiveTimeMeasure := by
      rw [hMeasure]
      exact (MeasureTheory.lintegral_prod _ hProductDensity).symm

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)


variable (hregTails : ∃ C : ℝ, 0 ≤ C ∧
  ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε)
    (_hεone : ε ≤ 1),
    (∀ R1 R2 t : ℝ, 0 < R1 → R1 < R2 → 0 ≤ t →
      (∫ x in {x : Vec3 | R2 < vec3EuclideanNorm x},
        (vec3EuclideanNorm (uε a ha ε (x, t))) ^ (2 : ℕ)) ≤
        (∫ x in {x : Vec3 | R1 < vec3EuclideanNorm x},
          (vec3EuclideanNorm
            (regUniformMollifiedInitial ρ ε hε a x)) ^ (2 : ℕ)) +
          C * (((eLpNorm a 2 volume).toReal) ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) +
            ((eLpNorm a 2 volume).toReal) ^ (3 : ℕ) * t ^ (1 / 4 : ℝ)) /
            (R2 - R1)) ∧
    (∀ R1 : ℝ, 0 < R1 →
      (∫ x in {x : Vec3 | R1 < vec3EuclideanNorm x},
        (vec3EuclideanNorm (regUniformMollifiedInitial ρ ε hε a x)) ^
          (2 : ℕ)) ≤
        ∫ x in {x : Vec3 | R1 - 1 < vec3EuclideanNorm x},
          (vec3EuclideanNorm (a x)) ^ (2 : ℕ)))

variable (hregEquicontinuity : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
  (εseq : ℕ → ℝ) (_hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
  (C : Set Vec3) (_hC : IsCompact C) (_hCU : C ⊆ (Set.univ : Set Vec3))
  (s₀ s₁ : ℝ) (_hs₀s₁ : Icc s₀ s₁ ⊆ Ioi (0 : ℝ))
  (w : Vec3 → L2Vec3) (_hw : ContDiff ℝ (⊤ : ℕ∞) w)
  (_hwc : HasCompactSupport w) (_hws : tsupport w ⊆ C),
  ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
    ∀ n s t, s ∈ Icc s₀ s₁ → t ∈ Icc s₀ s₁ →
      |(∫ x : Vec3, ∑ i : Fin 3,
          uε a ha (εseq n) (x, t) i * w x i ∂volume) -
        (∫ x : Vec3, ∑ i : Fin 3,
          uε a ha (εseq n) (x, s) i * w x i ∂volume)| ≤
        A * dist t s + B * (dist t s) ^ θ)

theorem lerayLimit_regularised_basic_data
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
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j, ContinuousOn (fun z => D z i j)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j k, ContinuousOn (fun z => DD z i j k)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i, ContinuousOn (fun z => Dt z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) ∧
    (∀ i, ContinuousOn (fun z => Dp z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
     letI : NormedAddCommGroup ParabolicPoint :=
       inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
     letI : NormedSpace ℝ ParabolicPoint :=
       inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
     ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
       (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j,
      DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
          vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
          (∀ i j, |D z i j| ≤ C) ∧
          (∀ i j k, |DD z i j k| ≤ C) ∧
          (∀ i, |Dt z i| ≤ C) ∧ (∀ i, |Dp z i| ≤ C)) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      MemLp p 2 (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
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
              (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u
                (x, t) i * u (x, t) j)) ∧
        ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
            -∑ i : Fin 3, ∑ j : Fin 3,
              ∫ x : Vec3, regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j * mixedSecond ψ i j x) ∧
    (∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u D t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
            2 volume ^ (2 : ℕ)))
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε) :
    (∀ t : ℝ, 0 ≤ t →
      MemLp (fun x : Vec3 => uε a ha ε (x, t)) 2 volume) ∧
    (∀ i : Fin 3, ContinuousOn (fun z => uε a ha ε z i)
      (spaceTimeSet Set.univ (Ioi 0))) ∧
    (∀ i j, ContinuousOn
      (fun z => spatialPartial (fun y => uε a ha ε y i) j z)
      (spaceTimeSet Set.univ (Ioi 0))) ∧
    (let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
      spatialPartial (fun y => uε a ha ε y i) j z
     ∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice (uε a ha ε) t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation (uε a ha ε) D t =
          eLpNorm (regMollifyVector ρ ε hε
            (regUniformSpatialField a)) 2 volume ^ (2 : ℕ)) := by
  rcases hregularised a ha ε hε with
    ⟨hFirst, hUcont, hDcont, _, _, _, _, _, _, _, _, _, _, _, hEnergy⟩
  rcases hFirst with ⟨hSlice, _, _, _⟩
  exact ⟨hSlice, hUcont, hDcont, by simpa using hEnergy⟩

/-- A piecewise field with the classical membership decision made explicit. -/
@[expose]
noncomputable def lerayLimitPiecewise {α β : Type*} [Zero β]
    (s : Set α) (f g : α → β) : α → β := by
  classical
  exact s.piecewise f g

/-- The regularized energy identity gives uniform slice and dissipation bounds
on positive time, after extending the fields measurably outside their source
domain. This is the energy input to `prop:leray-limit`. -/
theorem lerayLimit_regularised_energy_bounds
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (ε : ℝ) (hε : 0 < ε) (u : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3)
    (hucont : ∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDcont : ∀ i j, ContinuousOn (fun z => D z i j)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (henergy : ∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u D t =
          eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
            2 volume ^ (2 : ℕ)) :
    (∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice
        (lerayLimitPiecewise
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))
          u (fun z => regUniformMollifiedInitial ρ ε hε a z.1)) t)
        2 volume ^ (2 : ℕ) ≤
        eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ)) ∧
      2 * (∫⁻ z, ENNReal.ofReal (spatialGradientSq
        (lerayLimitPiecewise
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))
          u (fun z => regUniformMollifiedInitial ρ ε hε a z.1))
        (lerayLimitPiecewise
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) D (fun _ => 0))
        z) ∂regUniformPositiveTimeMeasure) ≤
          eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) ∧
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
        ENNReal.ofReal (spatialGradientSq
          (lerayLimitPiecewise
            (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))
            u (fun z => regUniformMollifiedInitial ρ ε hε a z.1))
          (lerayLimitPiecewise
            (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) D (fun _ => 0))
          (x, t)) ∂volume ∂volume) ≤
        eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) := by
  classical
  let P : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)
  let u₀ : ParabolicPoint → Vec3 := u
  let D₀ : ParabolicPoint → Fin 3 → Vec3 := D
  let ubar : ParabolicPoint → Vec3 :=
    P.piecewise u₀ (fun z => regUniformMollifiedInitial ρ ε hε a z.1)
  let Dbar : ParabolicPoint → Fin 3 → Vec3 :=
    P.piecewise D₀ (fun _ => 0)
  have hPmeas : MeasurableSet P := by
    change MeasurableSet (Set.univ ×ˢ Ioi (0 : ℝ))
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  have hucont' : ContinuousOn u₀ P := by
    apply continuousOn_pi.mpr
    intro i
    simpa [u₀, P] using hucont i
  have hinitialCont : Continuous
      (fun z : ParabolicPoint => regUniformMollifiedInitial ρ ε hε a z.1) := by
    exact (regUniformMollifiedInitial_contDiff ρ ε hε ha).continuous.comp
      continuous_fst_parabolicPoint
  have hDcont' : ContinuousOn D₀ P := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    simpa [D₀, u₀, P] using hDcont i j
  have hUbar : Measurable ubar := by
    dsimp [ubar]
    exact lerayLimit_measurableOn_extension P hPmeas u₀
      (fun z => regUniformMollifiedInitial ρ ε hε a z.1) hucont'
      (hinitialCont.continuousOn.mono (Set.subset_univ (Pᶜ)))
  have hDbar : Measurable Dbar := by
    exact lerayLimit_measurableOn_extension P hPmeas D₀ (fun _ => 0)
      hDcont' continuousOn_const
  have hDissZero : regUniformDissipation ubar Dbar 0 = 0 := by
    rw [regUniformDissipation]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem
      (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi)] with z hz
    have hzpos : 0 < z.2 := by
      change z.1 ∈ Set.univ ∧ 0 < z.2 at hz
      exact hz.2
    simp [not_lt_of_ge (le_of_lt hzpos)]
  have hDissEq (t : ℝ) (ht : 0 < t) :
      regUniformDissipation ubar Dbar t = regUniformDissipation u₀ D₀ t := by
    rw [regUniformDissipation, regUniformDissipation]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem
      (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi)] with z hz
    have hzpos : 0 < z.2 := by
      change z.1 ∈ Set.univ ∧ 0 < z.2 at hz
      exact hz.2
    have hzP : z ∈ P := by
      change z.1 ∈ Set.univ ∧ 0 < z.2
      exact ⟨Set.mem_univ _, hzpos⟩
    have hD : Dbar z = D₀ z := by
      dsimp [Dbar]
      rw [Set.piecewise_eq_of_mem P D₀ (fun _ => 0) hzP]
    have hsq : spatialGradientSq ubar Dbar z = spatialGradientSq u₀ D₀ z := by
      unfold spatialGradientSq
      rw [hD]
    simp only [hsq]
  have hsliceZero :
      eLpNorm (regUniformVelocitySlice ubar 0) 2 volume =
        eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a)) 2 volume := by
    congr 1
    funext x
    have hxnot : (WithLp.ofLp x, 0) ∉ P := by
      change ¬ (WithLp.ofLp x ∈ Set.univ ∧ 0 < (0 : ℝ))
      simp
    change WithLp.toLp 2 (ubar (WithLp.ofLp x, 0)) =
      regMollifyVector ρ ε hε (regUniformSpatialField a) (WithLp.toLp 2 x)
    rw [show ubar (WithLp.ofLp x, 0) =
      regUniformMollifiedInitial ρ ε hε a (WithLp.ofLp x) by
        dsimp [ubar]
        rw [Set.piecewise_eq_of_notMem P u₀
          (fun z => regUniformMollifiedInitial ρ ε hε a z.1) hxnot]]
    simp [regUniformMollifiedInitial]
  have hR5bar : ∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice ubar t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation ubar Dbar t =
          eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
            2 volume ^ (2 : ℕ) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      rw [hDissZero, hsliceZero]
      simp
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hslice : regUniformVelocitySlice ubar t =
          regUniformVelocitySlice u₀ t := by
        funext x
        change WithLp.toLp 2 (ubar (WithLp.ofLp x, t)) =
          WithLp.toLp 2 (u₀ (WithLp.ofLp x, t))
        have hxP : (WithLp.ofLp x, t) ∈ P := by
          change WithLp.ofLp x ∈ Set.univ ∧ 0 < t
          exact ⟨Set.mem_univ _, htpos⟩
        dsimp [ubar]
        rw [Set.piecewise_eq_of_mem P u₀
          (fun z => regUniformMollifiedInitial ρ ε hε a z.1) hxP]
      rw [hslice, hDissEq t htpos]
      exact henergy t ht
  have haL2 : MemLp (regUniformSpatialField a) 2 volume := by
    have hcoord : MemLp (fun x : L2Vec3 => a (WithLp.ofLp x))
        (2 : ℝ≥0∞) volume :=
      ha.1.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hDensityMeasurable : Measurable
      (fun z : ParabolicPoint =>
        ENNReal.ofReal (spatialGradientSq ubar Dbar z)) := by
    apply ENNReal.measurable_ofReal.comp
    unfold spatialGradientSq
    fun_prop
  have hbase := regUniform_energy_bounds ρ ε hε a ubar Dbar haL2 hR5bar hDbar
  refine ⟨?_, ?_, ?_⟩
  · simpa [lerayLimitPiecewise, P, ubar, D₀, Dbar] using hbase.1
  · simpa [lerayLimitPiecewise, P, ubar, D₀, Dbar] using hbase.2
  · have hiter := lerayLimit_iterated_positiveTime_gradient_eq
      ubar Dbar hDensityMeasurable
    have hiterBound :
        (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
          ENNReal.ofReal (spatialGradientSq ubar Dbar (x, t))
            ∂volume ∂volume) ≤
          eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) := by
      calc
        (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
            ENNReal.ofReal (spatialGradientSq ubar Dbar (x, t))
              ∂volume ∂volume) =
            ∫⁻ z, ENNReal.ofReal (spatialGradientSq ubar Dbar z)
              ∂regUniformPositiveTimeMeasure := hiter
        _ ≤ 2 * (∫⁻ z, ENNReal.ofReal (spatialGradientSq ubar Dbar z)
              ∂regUniformPositiveTimeMeasure) := by
          calc
            _ = 1 * (∫⁻ z, ENNReal.ofReal (spatialGradientSq ubar Dbar z)
                ∂regUniformPositiveTimeMeasure) := by simp
            _ ≤ 2 * (∫⁻ z, ENNReal.ofReal (spatialGradientSq ubar Dbar z)
                ∂regUniformPositiveTimeMeasure) := by
              gcongr
              norm_num
        _ ≤ eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) := hbase.2
    simpa [lerayLimitPiecewise, P, ubar, D₀, Dbar] using hiterBound

theorem lerayLimit_regularised_h1_slices
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
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j, ContinuousOn (fun z => D z i j)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j k, ContinuousOn (fun z => DD z i j k)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i, ContinuousOn (fun z => Dt z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) ∧
    (∀ i, ContinuousOn (fun z => Dp z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
     letI : NormedAddCommGroup ParabolicPoint :=
       inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
     letI : NormedSpace ℝ ParabolicPoint :=
       inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
     ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
       (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j,
      DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
          vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
          (∀ i j, |D z i j| ≤ C) ∧
          (∀ i j k, |DD z i j k| ≤ C) ∧
          (∀ i, |Dt z i| ≤ C) ∧ (∀ i, |Dp z i| ≤ C)) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      MemLp p 2 (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
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
              (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u
                (x, t) i * u (x, t) j)) ∧
        ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
            -∑ i : Fin 3, ∑ j : Fin 3,
              ∫ x : Vec3, regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j * mixedSecond ψ i j x) ∧
    (∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u D t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
            2 volume ^ (2 : ℕ)))
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∃ h : ∀ _i : Fin 3, CKN.H1Function (Set.univ : Set Vec3),
        (∀ i x, (h i).toFun x = uε a ha ε (x, t) i) ∧
        (∀ i x j, (h i).grad x j =
          spatialPartial (fun y => uε a ha ε y i) j (x, t)) := by
  classical
  let U : ParabolicPoint → Vec3 := uε a ha ε
  let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
    spatialPartial (fun y => U y i) j z
  let P : Set ParabolicPoint := spaceTimeSet Set.univ (Ioi 0)
  let Ubar : ParabolicPoint → Vec3 :=
    P.piecewise U (fun z => regUniformMollifiedInitial ρ ε hε a z.1)
  let Dbar : ParabolicPoint → Fin 3 → Vec3 := P.piecewise D (fun _ => 0)
  have hPosMem (x : Vec3) (t : ℝ) (ht : 0 < t) : (x, t) ∈ P := by
    change x ∈ Set.univ ∧ 0 < t
    exact ⟨Set.mem_univ _, ht⟩
  have hUbarPos (x : Vec3) (t : ℝ) (ht : 0 < t) :
      Ubar (x, t) = U (x, t) := by
    change P.piecewise U
      (fun z => regUniformMollifiedInitial ρ ε hε a z.1) (x, t) = U (x, t)
    rw [Set.piecewise_eq_of_mem P U
      (fun z => regUniformMollifiedInitial ρ ε hε a z.1) (hPosMem x t ht)]
  have hDbarPos (x : Vec3) (t : ℝ) (ht : 0 < t) (i j : Fin 3) :
      Dbar (x, t) i j = D (x, t) i j := by
    change P.piecewise D (fun _ => 0) (x, t) i j = D (x, t) i j
    rw [Set.piecewise_eq_of_mem P D (fun _ => 0) (hPosMem x t ht)]
  have hUbarZero (x : Vec3) :
      Ubar (x, 0) = regUniformMollifiedInitial ρ ε hε a x := by
    change P.piecewise U
      (fun z => regUniformMollifiedInitial ρ ε hε a z.1) (x, 0) = _
    have hxnot : (x, (0 : ℝ)) ∉ P := by
      change ¬ (x ∈ Set.univ ∧ 0 < (0 : ℝ))
      simp
    rw [Set.piecewise_eq_of_notMem P U
      (fun z => regUniformMollifiedInitial ρ ε hε a z.1) hxnot]
  have hData := lerayLimit_regularised_basic_data
    (ρ := ρ) (uε := uε) (pε := pε)
    (hregularised := hregularised) a ha ε hε
  have hSlice := hData.1
  have hUcont := hData.2.1
  have hDcont := hData.2.2.1
  have hEnergy := hData.2.2.2
  have hR := hregularised a ha ε hε
  have hC1 := hR.2.2.2.2.2.2.2.1
  have hSpatialC1 : ∀ t : ℝ, 0 < t → ∀ i : Fin 3,
      ContDiff ℝ 1 (fun x : Vec3 => U (x, t) i) := by
    apply lerayLimit_contDiff_spatial_slices U P hC1
    intro t ht x
    change x ∈ Set.univ ∧ 0 < t
    exact ⟨Set.mem_univ _, ht⟩
  have hInitialMem : MemLp
      (regUniformMollifiedInitial ρ ε hε a) 2 volume :=
    (regMollifiedInitial_isInJ ρ ε hε ha).1
  have hUbarSlice : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x : Vec3 => Ubar (x, t)) 2 volume := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      have hEq : (fun x : Vec3 => Ubar (x, 0)) =ᵐ[volume]
          regUniformMollifiedInitial ρ ε hε a := by
        filter_upwards [] with x
        exact hUbarZero x
      exact (memLp_congr_ae hEq).2 hInitialMem
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hEq : (fun x : Vec3 => Ubar (x, t)) = fun x => U (x, t) := by
        funext x
        exact hUbarPos x t htpos
      rw [hEq]
      exact hSlice t ht
  have hPmeas : MeasurableSet P := by
    change MeasurableSet (Set.univ ×ˢ Ioi (0 : ℝ))
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  have hDcont' : ContinuousOn D P := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    simpa [D, U] using hDcont i j
  have hDbarMeas : Measurable Dbar := by
    exact lerayLimit_measurableOn_extension P hPmeas D
      (fun _ => 0) hDcont' continuousOn_const
  have hEnergyBounds := lerayLimit_regularised_energy_bounds
    ρ a ha ε hε U D hUcont hDcont hEnergy
  have hInitialVecMem : MemLp (regUniformSpatialField a) 2 volume :=
    lerayHopfLimit_initialField_memLp a ha.1
  have hEnergyTop :
      eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) < ⊤ := by
    finiteness
  have hGradientEnergyFinite :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
        ENNReal.ofReal (spatialGradientSq Ubar Dbar (x, t))
          ∂volume ∂volume) < ⊤ := by
    exact lt_of_le_of_lt (hEnergyBounds.2.2) hEnergyTop
  have hGradientEnergyFinite' :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x in (Set.univ : Set Vec3),
        ENNReal.ofReal (spatialGradientSq Ubar Dbar (x, t))
          ∂volume ∂volume) < ⊤ := by
    simpa [Measure.restrict_univ] using hGradientEnergyFinite
  have hSpatialC1bar : ∀ t : ℝ, 0 < t → ∀ i : Fin 3,
      ContDiff ℝ 1 (fun x : Vec3 => Ubar (x, t) i) := by
    intro t ht i
    have hEq : (fun x : Vec3 => Ubar (x, t) i) = fun x => U (x, t) i := by
      funext x
      exact congrArg (fun v : Vec3 => v i) (hUbarPos x t ht)
    rw [hEq]
    exact hSpatialC1 t ht i
  have hDerivative : ∀ t : ℝ, 0 < t → ∀ x i j,
      (fderiv ℝ (fun y : Vec3 => Ubar (y, t) i) x) (basisVec j) =
        Dbar (x, t) i j := by
    intro t ht x i j
    have hUeq : (fun y : Vec3 => Ubar (y, t) i) =
        fun y => U (y, t) i := by
      funext y
      exact congrArg (fun v : Vec3 => v i) (hUbarPos y t ht)
    have hDeq : Dbar (x, t) i j = D (x, t) i j := by
      exact hDbarPos x t ht i j
    rw [hUeq, hDeq]
    rfl
  have hSlices := regUniform_velocity_h1_slices Ubar Dbar hUbarSlice
    hDbarMeas hGradientEnergyFinite' hSpatialC1bar hDerivative
  filter_upwards [hSlices, ae_restrict_mem measurableSet_Ioi]
    with t hSliceH1 htmem
  have ht : 0 < t := htmem
  rcases hSliceH1 with ⟨h, hvalue, hgradient⟩
  refine ⟨h, ?_, ?_⟩
  · intro i x
    calc
      (h i).toFun x = Ubar (x, t) i := hvalue i x
      _ = U (x, t) i := congrArg (fun v : Vec3 => v i) (hUbarPos x t ht)
  · intro i x j
    calc
      (h i).grad x j = Dbar (x, t) i j := hgradient i x j
      _ = spatialPartial (fun y => U y i) j (x, t) := by
        rw [hDbarPos x t ht i j]

end CKN.Leray

end
