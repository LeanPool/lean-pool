/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyPressureLimit
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupEnergyScaling
public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsOpenGlue

/-!
# Two clauses of the blow-up limit

Two clauses of `prop:blowup-limit` that do not depend on the compactness
passage.

* The assembled limit pressure is the whole-space pressure `P[u ⊗ u]` of
  `def:riesz-pressure`: at almost every negative time its slice is the sum of
  the nine double Riesz transforms of the slice tensor. It vanishes on every
  past slab on which the limit velocity vanishes.
* At a point that is not good, the rescaled unit-cylinder energy is at least
  `ε₀ / 8` for every scale whose open-top cylinder lies in the unit cylinder
  (`eq:bad-point-lower-bound` after the Navier–Stokes scaling).
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS


/-- At almost every negative time the slice of the assembled limit pressure is
the spatial whole-space pressure `P[U(·,t) ⊗ U(·,t)]` of `def:riesz-pressure`
(`prop:blowup-limit`, clause (d)). -/
theorem blowupLimitClauses_pressure_slice_eq
    (U : Vec3 × ℝ → Vec3)
    (hG : ∀ n i j, MemLp (blowupLimitAssemblyPressureWindowTensor U n i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume) :
    ∀ᵐ t ∂(volume.restrict (Iio (0 : ℝ))),
      ∃ hUt : ∀ i j, MemLp (fun x : Vec3 => U (x, t) i * U (x, t) j)
          (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure Vec3),
        (fun x : Vec3 => blowupLimitAssemblyPressureLimit U hG (x, t)) =ᵐ[volume]
          fun x => CKN.Leray.rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
            (fun i j => (hUt i j).toLp (fun y : Vec3 => U (y, t) i * U (y, t) j)) x := by
  have hall : ∀ᵐ t ∂(volume : Measure ℝ), ∀ n : ℕ,
      ∃ hFt : ∀ i j, MemLp
          (fun x : Vec3 => blowupLimitAssemblyPressureWindowTensor U n i j (x, t))
          (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure Vec3),
        (fun x : Vec3 => CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
            (blowupLimitAssemblyPressureWindowTensor U n) (hG n) (x, t)) =ᵐ[volume]
          fun x => CKN.Leray.rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
            (fun i j => (hFt i j).toLp
              (fun y : Vec3 => blowupLimitAssemblyPressureWindowTensor U n i j (y, t))) x := by
    rw [ae_all_iff]
    intro n
    exact CKN.Leray.rieszPressureSpaceTime_slice_ae_eq (3 / 2 : ℝ) (by norm_num)
      (blowupLimitAssemblyPressureWindowTensor U n) (hG n)
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Iio] with t ht htneg
  set m : ℕ := ⌈-t⌉₊ with hmdef
  obtain ⟨hFt, hslice⟩ := ht m
  have hwin : ∀ y : Vec3, (y, t) ∈ (Set.univ : Set Vec3) ×ˢ Ioo (-((m : ℝ) + 1)) 0 := by
    intro y
    refine ⟨mem_univ _, ?_, htneg⟩
    have hle : -t ≤ (m : ℝ) := Nat.le_ceil _
    linarith only [hle]
  have hfun : ∀ i j, (fun x : Vec3 => blowupLimitAssemblyPressureWindowTensor U m i j (x, t)) =
      fun x : Vec3 => U (x, t) i * U (x, t) j := by
    intro i j
    funext x
    simp only [blowupLimitAssemblyPressureWindowTensor]
    rw [Set.indicator_of_mem (hwin x)]
  have hUt : ∀ i j, MemLp (fun x : Vec3 => U (x, t) i * U (x, t) j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure Vec3) := by
    intro i j
    rw [← hfun i j]
    exact hFt i j
  refine ⟨hUt, ?_⟩
  have hinput : (fun i j => (hFt i j).toLp
      (fun y : Vec3 => blowupLimitAssemblyPressureWindowTensor U m i j (y, t))) =
      fun i j => (hUt i j).toLp (fun y : Vec3 => U (y, t) i * U (y, t) j) := by
    funext i j
    apply MemLp.toLp_congr
    exact Eventually.of_forall fun x => congrFun (hfun i j) x
  have hpoint : (fun x : Vec3 => blowupLimitAssemblyPressureLimit U hG (x, t)) =
      fun x : Vec3 => CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
        (blowupLimitAssemblyPressureWindowTensor U m) (hG m) (x, t) := rfl
  rw [hpoint, ← hinput]
  exact hslice

/-- The assembled limit pressure vanishes almost everywhere on every past slab
on which the limit velocity vanishes (`prop:blowup-limit`, clauses (d) and (f)). -/
theorem blowupLimitClauses_pressure_zero_of_velocity_zero
    (U : Vec3 × ℝ → Vec3)
    (hG : ∀ n i j, MemLp (blowupLimitAssemblyPressureWindowTensor U n i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    {T : ℝ} (hU0 : U =ᵐ[volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo (-T) 0)] 0) :
    blowupLimitAssemblyPressureLimit U hG =ᵐ[volume.restrict
      ((Set.univ : Set Vec3) ×ˢ Ioo (-T) 0)] 0 := by
  set m : ℕ := ⌈T⌉₊
  set J : Set ℝ := Ioo (-T) 0
  have hJ : MeasurableSet J := measurableSet_Ioo
  set S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ J
  have hS : MeasurableSet S := MeasurableSet.univ.prod hJ
  have hwin := blowupLimitAssemblyPressureLimit_ae_eq U hG T
  have hloc := blowup_rieszPressureSpaceTime_time_indicator_ae
    (blowupLimitAssemblyPressureWindowTensor U m) (hG m) J hJ
  have hU0' := (ae_restrict_iff' hS).1 hU0
  have htensor0 : ∀ i j, (fun z => S.indicator
      (blowupLimitAssemblyPressureWindowTensor U m i j) z) =ᵐ[volume] 0 := by
    intro i j
    filter_upwards [hU0'] with z hz
    by_cases hzS : z ∈ S
    · rw [Set.indicator_of_mem hzS]
      have hz' : U z = 0 := hz hzS
      simp only [blowupLimitAssemblyPressureWindowTensor, Pi.zero_apply]
      by_cases hzw : z ∈ (Set.univ : Set Vec3) ×ˢ Ioo (-((m : ℝ) + 1)) 0
      · rw [Set.indicator_of_mem hzw, hz']
        simp
      · rw [Set.indicator_of_notMem hzw]
    · rw [Set.indicator_of_notMem hzS]
      rfl
  have hP0 := blowupLimitAssemblyPressure_rieszPressure_ae_zero
    (fun i j => (hG m i j).indicator hS) htensor0
  filter_upwards [hwin, ae_restrict_of_ae hloc, ae_restrict_of_ae hP0,
    ae_restrict_mem hS] with z hz hzl hz0 hzS
  have hzl' := hzl
  rw [Set.indicator_of_mem hzS, Set.indicator_of_mem hzS] at hzl'
  rw [hz, hzl']
  exact hz0

/-- At a point that is not good, every rescaled unit-cylinder energy whose
open-top source cylinder lies in the unit cylinder is at least `ε₀ / 8`
(`prop:blowup-limit`, clause (f), from `eq:bad-point-lower-bound`). -/
theorem blowupLimitClauses_bad_point_lower_bound
    {ε₀ : ℝ} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {x₀ : Vec3} {t₀ : ℝ}
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hbad : ¬ IsGoodPoint ε₀ u p (x₀, t₀))
    {R : ℝ} (hR : 0 < R)
    (hRdomain : goodPointPastCylinder x₀ t₀ R ⊆ goodPointDomain) :
    ENNReal.ofReal (ε₀ / 8) ≤
      goodPointEnergy (blowupVelocity x₀ t₀ R u) (blowupPressure x₀ t₀ R p) 0 0 1 := by
  have hxnorm : vec3EuclideanNorm (x₀ - 0) ≤ 1 / 2 := by
    rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] at hx₀
    simpa only [Set.mem_ofPred_eq] using hx₀
  rw [blowupEnergy_rescale_of_admissible u p x₀ t₀ R hR hRdomain]
  exact goodPoint_badPoint_lower_bound_closed (z := (x₀, t₀)) ⟨hxnorm, ht₀⟩ hR
    hRdomain hbad

end ESS

end
