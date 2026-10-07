/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsFinalCore
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitTailsContinuity

/-!
# The exterior energy estimate `eq:reg-tails`

The compact-weight bound of `CKN.Leray.RegTailsFinalCore` is sent to the
initial time by the `L²` continuity of the slices, and the compact cutoffs
exhaust the exterior of the ball of radius (R2) (lem:reg-tails). Together with
the initial mollifier tail this is the hypothesis `hregTails` of
`prop:leray-limit`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

section

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)



/-- The compact-weight bound of `lem:reg-tails` from the initial time: for
`t ≥ 0` the localized energy at time `t` is at most the one at time `0` plus
`18 M B² t^{1/2} + Q M B³ t^{1/4}`. -/
theorem regTailsFinal_compact_weight_bound_initial
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
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε)
    (q : Vec3 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hqc : HasCompactSupport q)
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∀ x, q x ≤ 1) {M : ℝ} (hM : 0 ≤ M)
    (hDq : ∀ x : Vec3, ∀ j : Fin 3, |spatialDeriv q j x| ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    regTailsEnergyWeight (uε a ha ε) q t ≤
      regTailsEnergyWeight (uε a ha ε) q 0 +
        (18 * M * (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ (2 : ℕ) *
            t ^ (1 / 2 : ℝ) +
          regTailsFluxConstant * M *
            (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ (3 : ℕ) *
            t ^ (1 / 4 : ℝ)) := by
  set c : ℝ :=
    18 * M * (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ (2 : ℕ) *
        t ^ (1 / 2 : ℝ) +
      regTailsFluxConstant * M *
        (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ (3 : ℕ) *
        t ^ (1 / 4 : ℝ) with hc_def
  have hB : 0 ≤ (eLpNorm (regUniformSpatialField a) 2 volume).toReal :=
    ENNReal.toReal_nonneg
  have ht2 : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht _
  have ht4 : 0 ≤ t ^ (1 / 4 : ℝ) := Real.rpow_nonneg ht _
  have hQ := regTailsFluxConstant_nonneg
  have hc : 0 ≤ c := by positivity
  rcases ht.eq_or_lt with h0 | htpos
  · rw [← h0]
    exact le_add_of_nonneg_right hc
  obtain ⟨⟨hSlice, hSliceCont, _hInit, _hDiv⟩, _hRest⟩ := hregularised a ha ε hε
  have hcont := forcedTails_weightedEnergy_continuousOn (uε a ha ε) hSlice hSliceCont
    hq.continuous.measurable (C := 1)
    (fun x => abs_le.2 ⟨by linarith only [hq0 x], hq1 x⟩)
  have hT : Tendsto (regTailsEnergyWeight (uε a ha ε) q) (𝓝[>] (0 : ℝ))
      (𝓝 (regTailsEnergyWeight (uε a ha ε) q 0)) :=
    ((hcont 0 (Set.mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self).tendsto
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      regTailsEnergyWeight (uε a ha ε) q t ≤
        regTailsEnergyWeight (uε a ha ε) q s + c := by
    filter_upwards [Ioo_mem_nhdsGT htpos] with s hs
    exact regTailsFinal_compact_weight_bound ρ uε pε hregularised a ha ε hε
      q hq hqc hq0 hM hDq hs.1 hs.2
  exact ge_of_tendsto (hT.add_const c) hev

private theorem regTails_integrable_mul_unit_interval
    {v q : Vec3 → ℝ} (hv : Integrable v volume) (hvnn : ∀ x, 0 ≤ v x)
    (hqc : Continuous q) (hq01 : ∀ x, 0 ≤ q x ∧ q x ≤ 1) :
    Integrable (fun x => v x * q x) volume := by
  refine hv.mono'
    (hv.aestronglyMeasurable.mul hqc.aestronglyMeasurable) ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hvnn x),
    abs_of_nonneg (hq01 x).1]
  exact mul_le_of_le_one_right (hvnn x) (hq01 x).2

private theorem regTails_exterior_exhaustion_limit
    {R2 : ℝ} (hR2 : 0 < R2) (v : Vec3 → ℝ) (hv : Integrable v volume) :
    Tendsto (fun n : ℕ => ∫ x in
      {x : Vec3 | R2 < vec3EuclideanNorm x} ∩
        {x : Vec3 | vec3EuclideanNorm x < R2 + (n : ℝ) + 1}, v x)
      atTop (𝓝 (∫ x in {x : Vec3 | R2 < vec3EuclideanNorm x}, v x)) := by
  have hnm : Measurable (fun x : Vec3 => vec3EuclideanNorm x) :=
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable
  let Sout : Set Vec3 := {x : Vec3 | R2 < vec3EuclideanNorm x}
  let Sn : ℕ → Set Vec3 := fun n =>
    Sout ∩ {x : Vec3 | vec3EuclideanNorm x < R2 + (n : ℝ) + 1}
  have hSout : MeasurableSet Sout := measurableSet_lt measurable_const hnm
  have hmono : Monotone Sn := by
    intro m n hmn x hx
    have hxm : vec3EuclideanNorm x < R2 + (m : ℝ) + 1 := hx.2
    have hmn' : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    refine ⟨hx.1, ?_⟩
    change vec3EuclideanNorm x < R2 + (n : ℝ) + 1
    linarith only [hxm, hmn']
  have hUnion : (⋃ n, Sn n) = Sout := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      exact hn.1
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt (vec3EuclideanNorm x)
      refine ⟨n, hx, ?_⟩
      change vec3EuclideanNorm x < R2 + (n : ℝ) + 1
      linarith only [hn, hR2]
  have hSnm : ∀ n, MeasurableSet (Sn n) := fun n =>
    hSout.inter (measurableSet_lt hnm measurable_const)
  have hlim := tendsto_setIntegral_of_monotone (μ := volume) (f := v) hSnm hmono
    hv.integrableOn
  simpa only [hUnion] using hlim

/-- The exterior energy estimate of `lem:reg-tails` for one regularized
solution, with the Euclidean `L²` norm `B` of the datum. -/
theorem regTailsFinal_exterior_bound
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
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε)
    {R1 R2 t : ℝ} (hR1 : 0 < R1) (hR12 : R1 < R2) (ht : 0 ≤ t) :
    (∫ x in {x : Vec3 | R2 < vec3EuclideanNorm x},
        (vec3EuclideanNorm (uε a ha ε (x, t))) ^ (2 : ℕ)) ≤
      (∫ x in {x : Vec3 | R1 < vec3EuclideanNorm x},
          (vec3EuclideanNorm (regUniformMollifiedInitial ρ ε hε a x)) ^ (2 : ℕ)) +
        64 / (R2 - R1) *
          (18 * (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ (2 : ℕ) *
              t ^ (1 / 2 : ℝ) +
            regTailsFluxConstant *
              (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ (3 : ℕ) *
              t ^ (1 / 4 : ℝ)) := by
  obtain ⟨⟨hSlice, _hSliceCont, hInit, _hDiv⟩, _hRest⟩ := hregularised a ha ε hε
  set u : ParabolicPoint → Vec3 := uε a ha ε with hu_def
  set B : ℝ := (eLpNorm (regUniformSpatialField a) 2 volume).toReal with hB_def
  set K : ℝ := 18 * B ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) +
    regTailsFluxConstant * B ^ (3 : ℕ) * t ^ (1 / 4 : ℝ) with hK_def
  have hDpos : 0 < R2 - R1 := sub_pos.2 hR12
  have hnm : Measurable (fun x : Vec3 => vec3EuclideanNorm x) :=
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable
  let V : ℝ → Vec3 → ℝ := fun τ x => vec3EuclideanNorm (u (x, τ)) ^ (2 : ℕ)
  have hVint : ∀ τ : ℝ, 0 ≤ τ → Integrable (V τ) volume := fun τ hτ =>
    (regTailsFinal_euclideanNorm_memLp (hSlice τ hτ)).integrable_sq
  have hVnn : ∀ τ x, 0 ≤ V τ x := fun _ _ => sq_nonneg _
  have hVq : ∀ τ : ℝ, 0 ≤ τ → ∀ q : Vec3 → ℝ, Continuous q →
      (∀ x, 0 ≤ q x ∧ q x ≤ 1) → Integrable (fun x => V τ x * q x) volume :=
    fun τ hτ q hqc hq01 =>
      regTails_integrable_mul_unit_interval (hVint τ hτ) (hVnn τ) hqc hq01
  let Sout : Set Vec3 := {x : Vec3 | R2 < vec3EuclideanNorm x}
  let Sin : Set Vec3 := {x : Vec3 | R1 < vec3EuclideanNorm x}
  have hSin : MeasurableSet Sin := measurableSet_lt measurable_const hnm
  have hSout : MeasurableSet Sout := measurableSet_lt measurable_const hnm
  -- the initial exterior energy
  have hI0 : (∫ x in Sin, V 0 x) =
      ∫ x in Sin, (vec3EuclideanNorm (regUniformMollifiedInitial ρ ε hε a x)) ^ (2 : ℕ) := by
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hInit] with x hx
    change vec3EuclideanNorm (u (x, 0)) ^ (2 : ℕ) = _
    rw [hx]
  obtain ⟨f, _hf, hf01, hfin, hfout, hfD, hcut⟩ :=
    regTails_compact_exterior_cutoffs hR1 hR12
  let N : ℕ → ℝ := fun n => R2 + (n : ℝ) + 1
  have hN : ∀ n, R2 < N n := fun n => by
    have := Nat.cast_nonneg (α := ℝ) n
    dsimp only [N]
    linarith only [this]
  let Sn : ℕ → Set Vec3 := fun n => Sout ∩ {x : Vec3 | vec3EuclideanNorm x < N n}
  have hstep : ∀ n : ℕ, (∫ x in Sn n, V t x) ≤
      (∫ x in Sin, V 0 x) + (64 / (R2 - R1) + 32 / N n) * K := by
    intro n
    have hNpos : 0 < N n := (hR1.trans hR12).trans (hN n)
    obtain ⟨q, hqs, hqc, hq01, hqf, hqD, hχD⟩ := hcut (N n) (hN n).le
    set M : ℝ := 64 / (R2 - R1) + 32 / N n with hM_def
    have hM : 0 ≤ M := add_nonneg (div_nonneg (by norm_num) hDpos.le)
      (div_nonneg (by norm_num) hNpos.le)
    have hDq : ∀ x : Vec3, ∀ j : Fin 3, |spatialDeriv q j x| ≤ M := by
      intro x j
      rw [hqD x j]
      have hχ := regularisedEnergyCutoff_mem_unitInterval (N n) x
      calc
        _ ≤ |spatialDeriv f j x * regularisedEnergyCutoff (N n) x| +
            |f x * spatialDeriv (regularisedEnergyCutoff (N n)) j x| := abs_add_le _ _
        _ = |spatialDeriv f j x| * regularisedEnergyCutoff (N n) x +
            f x * |spatialDeriv (regularisedEnergyCutoff (N n)) j x| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hχ.1, abs_of_nonneg (hf01 x).1]
        _ ≤ 64 / (R2 - R1) * 1 + 1 * (32 / N n) :=
          add_le_add
            (mul_le_mul (hfD x j) hχ.2 hχ.1 (div_nonneg (by norm_num) hDpos.le))
            (mul_le_mul (hf01 x).2 (hχD x j) (abs_nonneg _) zero_le_one)
        _ = M := by rw [mul_one, one_mul]
    have hE := regTailsFinal_compact_weight_bound_initial ρ uε pε hregularised
      a ha ε hε q hqs hqc (fun x => (hq01 x).1) (fun x => (hq01 x).2) hM hDq ht
    have hlow : (∫ x in Sn n, V t x) ≤ regTailsEnergyWeight u q t := by
      have hSnm : MeasurableSet (Sn n) :=
        hSout.inter (measurableSet_lt hnm measurable_const)
      rw [← integral_indicator hSnm]
      refine integral_mono ((hVint t ht).indicator hSnm)
        (hVq t ht q hqs.continuous hq01) (fun x => ?_)
      by_cases hx : x ∈ Sn n
      · rw [indicator_of_mem hx]
        have hq1 : q x = 1 := by
          rw [hqf x hx.2]
          exact hfout x (le_of_lt hx.1)
        change V t x ≤ V t x * q x
        rw [hq1, mul_one]
      · rw [indicator_of_notMem hx]
        exact mul_nonneg (hVnn t x) (hq01 x).1
    have hup : regTailsEnergyWeight u q 0 ≤ ∫ x in Sin, V 0 x := by
      rw [← integral_indicator hSin]
      refine integral_mono (hVq 0 le_rfl q hqs.continuous hq01)
        ((hVint 0 le_rfl).indicator hSin) (fun x => ?_)
      by_cases hx : x ∈ Sin
      · rw [indicator_of_mem hx]
        exact mul_le_of_le_one_right (hVnn 0 x) (hq01 x).2
      · rw [indicator_of_notMem hx]
        have hxle : vec3EuclideanNorm x ≤ R1 := not_lt.1 hx
        have hq0 : q x = 0 := by
          rw [hqf x (lt_of_le_of_lt hxle (hR12.trans (hN n)))]
          exact hfin x hxle
        change V 0 x * q x ≤ 0
        rw [hq0, mul_zero]
    have hMK : 18 * M * B ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) +
        regTailsFluxConstant * M * B ^ (3 : ℕ) * t ^ (1 / 4 : ℝ) = M * K := by
      rw [hK_def]
      ring
    rw [hMK] at hE
    linarith only [hlow, hE, hup]
  have hlim : Tendsto (fun n => ∫ x in Sn n, V t x) atTop
      (𝓝 (∫ x in Sout, V t x)) :=
    regTails_exterior_exhaustion_limit (hR1.trans hR12) (V t) (hVint t ht)
  have hNtop : Tendsto N atTop atTop :=
    tendsto_atTop_add_const_right _ 1
      (tendsto_atTop_add_const_left _ R2 tendsto_natCast_atTop_atTop)
  have hRHS : Tendsto (fun n => (∫ x in Sin, V 0 x) + (64 / (R2 - R1) + 32 / N n) * K)
      atTop (𝓝 ((∫ x in Sin, V 0 x) + (64 / (R2 - R1) + 0) * K)) :=
    tendsto_const_nhds.add
      ((tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hNtop)).mul_const K)
  have hfinal := le_of_tendsto_of_tendsto' hlim hRHS hstep
  rw [add_zero, hI0] at hfinal
  exact hfinal

/-- The regularized exterior energy estimate `eq:reg-tails` together with the
initial mollifier tail (lem:reg-tails): this is the hypothesis `hregTails` of
`prop:leray-limit`, with one constant for every datum in `J` and every
`ε ∈ (0, 1]`. -/
theorem regTails_of_regularised
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
    :
    ∃ C : ℝ, 0 ≤ C ∧
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
              (vec3EuclideanNorm (a x)) ^ (2 : ℕ)) := by
  have hQ := regTailsFluxConstant_nonneg
  refine ⟨64 * (54 + 6 * regTailsFluxConstant), by positivity, ?_⟩
  intro a ha ε hε hε1
  refine ⟨?_, fun R1 _ => forcedLerayLimit_initialTail ρ ε hε hε1 a ha.1 R1⟩
  intro R1 R2 t hR1 hR12 ht
  have hext := regTailsFinal_exterior_bound ρ uε pε hregularised a ha ε hε hR1 hR12 ht
  set Bs : ℝ := (eLpNorm a 2 volume).toReal with hBs_def
  set BE : ℝ := (eLpNorm (regUniformSpatialField a) 2 volume).toReal with hBE_def
  have hBs : 0 ≤ Bs := ENNReal.toReal_nonneg
  have hBE0 : 0 ≤ BE := ENNReal.toReal_nonneg
  have ht2 : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht _
  have ht4 : 0 ≤ t ^ (1 / 4 : ℝ) := Real.rpow_nonneg ht _
  have hDpos : 0 < R2 - R1 := sub_pos.2 hR12
  -- the Euclidean and the sup-norm `L²` norms of the datum
  have hBE : BE ≤ Real.sqrt 3 * Bs := by
    have hfield := regTails_eLpNorm_euclidean_eq_spatialField a ha.1
    have hle : eLpNorm (fun x : Vec3 => vec3EuclideanNorm (a x)) 2 volume ≤
        ENNReal.ofReal (Real.sqrt 3) * eLpNorm a 2 volume := by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
          ha.1.aestronglyMeasurable) ?_ 2
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      exact vec3EuclideanNorm_le_sqrt_three_mul_norm _
    have hfin : ENNReal.ofReal (Real.sqrt 3) * eLpNorm a 2 volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha.1.eLpNorm_ne_top
    rw [hBE_def, ← hfield]
    calc
      _ ≤ (ENNReal.ofReal (Real.sqrt 3) * eLpNorm a 2 volume).toReal :=
        ENNReal.toReal_mono hfin hle
      _ = Real.sqrt 3 * Bs := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have hs3 : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsq : Real.sqrt 3 ^ (2 : ℕ) = 3 := Real.sq_sqrt (by norm_num)
  have h2 : BE ^ (2 : ℕ) ≤ 3 * Bs ^ (2 : ℕ) := by
    calc
      BE ^ (2 : ℕ) ≤ (Real.sqrt 3 * Bs) ^ (2 : ℕ) := pow_le_pow_left₀ hBE0 hBE 2
      _ = 3 * Bs ^ (2 : ℕ) := by rw [mul_pow, hsq]
  have h3 : BE ^ (3 : ℕ) ≤ 6 * Bs ^ (3 : ℕ) := by
    calc
      BE ^ (3 : ℕ) ≤ (Real.sqrt 3 * Bs) ^ (3 : ℕ) := pow_le_pow_left₀ hBE0 hBE 3
      _ = Real.sqrt 3 ^ (2 : ℕ) * Real.sqrt 3 * Bs ^ (3 : ℕ) := by ring
      _ = 3 * Real.sqrt 3 * Bs ^ (3 : ℕ) := by rw [hsq]
      _ ≤ 3 * 2 * Bs ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs3 (by norm_num))
          (pow_nonneg hBs 3)
      _ = 6 * Bs ^ (3 : ℕ) := by norm_num
  have hK : 18 * BE ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) +
      regTailsFluxConstant * BE ^ (3 : ℕ) * t ^ (1 / 4 : ℝ) ≤
      (54 + 6 * regTailsFluxConstant) *
        (Bs ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) + Bs ^ (3 : ℕ) * t ^ (1 / 4 : ℝ)) := by
    have hA : 18 * BE ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) ≤
        54 * (Bs ^ (2 : ℕ) * t ^ (1 / 2 : ℝ)) := by
      calc
        _ ≤ 18 * (3 * Bs ^ (2 : ℕ)) * t ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num)) ht2
        _ = _ := by ring
    have hB' : regTailsFluxConstant * BE ^ (3 : ℕ) * t ^ (1 / 4 : ℝ) ≤
        6 * regTailsFluxConstant * (Bs ^ (3 : ℕ) * t ^ (1 / 4 : ℝ)) := by
      calc
        _ ≤ regTailsFluxConstant * (6 * Bs ^ (3 : ℕ)) * t ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hQ) ht4
        _ = _ := by ring
    have hX2 : 0 ≤ Bs ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) := mul_nonneg (pow_nonneg hBs 2) ht2
    have hX3 : 0 ≤ Bs ^ (3 : ℕ) * t ^ (1 / 4 : ℝ) := mul_nonneg (pow_nonneg hBs 3) ht4
    have hc1 : 0 ≤ 54 * (Bs ^ (3 : ℕ) * t ^ (1 / 4 : ℝ)) := mul_nonneg (by norm_num) hX3
    have hc2 : 0 ≤ 6 * regTailsFluxConstant * (Bs ^ (2 : ℕ) * t ^ (1 / 2 : ℝ)) :=
      mul_nonneg (mul_nonneg (by norm_num) hQ) hX2
    have hexpand : (54 + 6 * regTailsFluxConstant) *
        (Bs ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) + Bs ^ (3 : ℕ) * t ^ (1 / 4 : ℝ)) =
        54 * (Bs ^ (2 : ℕ) * t ^ (1 / 2 : ℝ)) +
          6 * regTailsFluxConstant * (Bs ^ (3 : ℕ) * t ^ (1 / 4 : ℝ)) +
          54 * (Bs ^ (3 : ℕ) * t ^ (1 / 4 : ℝ)) +
          6 * regTailsFluxConstant * (Bs ^ (2 : ℕ) * t ^ (1 / 2 : ℝ)) := by ring
    rw [hexpand]
    linarith only [hA, hB', hc1, hc2]
  have hscale : 64 / (R2 - R1) *
      (18 * BE ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) +
        regTailsFluxConstant * BE ^ (3 : ℕ) * t ^ (1 / 4 : ℝ)) ≤
      64 * (54 + 6 * regTailsFluxConstant) *
        (Bs ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) + Bs ^ (3 : ℕ) * t ^ (1 / 4 : ℝ)) /
        (R2 - R1) := by
    calc
      _ ≤ 64 / (R2 - R1) * ((54 + 6 * regTailsFluxConstant) *
          (Bs ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) + Bs ^ (3 : ℕ) * t ^ (1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hK (div_nonneg (by norm_num) hDpos.le)
      _ = _ := by
        field_simp
  linarith only [hext, hscale]

end

end CKN.Leray

end
