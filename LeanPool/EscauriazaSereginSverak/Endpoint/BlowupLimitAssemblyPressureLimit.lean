/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyPressureRiesz
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszTimeLocal
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszLinear
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszFarTensor
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The whole-space pressure of the blow-up limit

The limit velocity of `prop:blowup-limit` has bounded L³ slices for all
negative times, so its tensor is in space-time L^(3/2) on every finite
past window. The pressure P[u ⊗ u] of the limit is assembled from the
Riesz pressures of these time-truncated tensors, which agree on common
windows.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS


/-- The velocity tensor of a field, truncated to the past window
(-(n + 1), 0). -/
@[expose] def blowupLimitAssemblyPressureWindowTensor (U : Vec3 × ℝ → Vec3) (n : ℕ) :
    Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
  fun i j => (Set.univ ×ˢ Ioo (-((n : ℝ) + 1)) 0).indicator (fun z => U z i * U z j)

/-- The whole-space pressure of a field with truncated tensors in
L^(3/2): at time t < 0 it is the Riesz pressure of the tensor truncated
to the window (-(⌈-t⌉ + 1), 0). -/
@[expose] def blowupLimitAssemblyPressureLimit (U : Vec3 × ℝ → Vec3)
    (hG : ∀ n i j, MemLp (blowupLimitAssemblyPressureWindowTensor U n i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume) : Vec3 × ℝ → ℝ :=
  fun z => CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
    (blowupLimitAssemblyPressureWindowTensor U ⌈-z.2⌉₊) (hG ⌈-z.2⌉₊) z

/-- A field in L³ of a set has its tensor, truncated to that set, in
whole-space L^(3/2). -/
theorem blowupLimitAssemblyPressure_tensor_memLp_of_restrict
    {U : Vec3 × ℝ → Vec3} {S : Set (Vec3 × ℝ)} (hS : MeasurableSet S)
    (hU : MemLp U 3 (volume.restrict S)) (i j : Fin 3) :
    MemLp (S.indicator (fun z => U z i * U z j)) (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
  have hw : MemLp (S.indicator U) 3 volume := (memLp_indicator_iff_restrict hS).2 hU
  have h := blowup_velocity_tensor_memLp (S.indicator U) hw i j
  have heq : (fun z => S.indicator U z i * S.indicator U z j) =
      S.indicator (fun z => U z i * U z j) := by
    funext z
    by_cases hz : z ∈ S
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  rw [heq] at h
  exact h

/-- Riesz pressures of truncations to nested windows agree on the smaller
window. -/
theorem blowupLimitAssemblyPressure_window_agree
    (U : Vec3 × ℝ → Vec3)
    (hG : ∀ n i j, MemLp (blowupLimitAssemblyPressureWindowTensor U n i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    {n m : ℕ} (hnm : n ≤ m) :
    ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      z ∈ Set.univ ×ˢ Ioo (-((n : ℝ) + 1)) 0 →
        CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
          (blowupLimitAssemblyPressureWindowTensor U m) (hG m) z =
        CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
          (blowupLimitAssemblyPressureWindowTensor U n) (hG n) z := by
  set J : Set ℝ := Ioo (-((n : ℝ) + 1)) 0
  have hJ : MeasurableSet J := measurableSet_Ioo
  have hloc := blowup_rieszPressureSpaceTime_time_indicator_ae
    (blowupLimitAssemblyPressureWindowTensor U m) (hG m) J hJ
  have hsub : ((Set.univ : Set Vec3) ×ˢ J) ⊆
      (Set.univ : Set Vec3) ×ˢ Ioo (-((m : ℝ) + 1)) 0 := by
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    rintro z ⟨_, hz⟩
    exact ⟨mem_univ _, ⟨by linarith only [hz.1, hnm'], hz.2⟩⟩
  have htensor : (fun i j => ((Set.univ : Set Vec3) ×ˢ J).indicator
      (blowupLimitAssemblyPressureWindowTensor U m i j)) =
      blowupLimitAssemblyPressureWindowTensor U n := by
    funext i j
    simp only [blowupLimitAssemblyPressureWindowTensor]
    rw [Set.indicator_indicator, Set.inter_eq_left.mpr hsub]
  have hcongr := blowup_rieszPressureSpaceTime_congr
    (fun i j => (hG m i j).indicator (MeasurableSet.univ.prod hJ)) (hG n) htensor
  filter_upwards [hloc] with z hz hzS
  have h := hz
  simp only [Set.indicator_of_mem hzS] at h
  rw [h]
  exact congrFun hcongr z

/-- The assembled limit pressure is measurable. -/
theorem measurable_blowupLimitAssemblyPressureLimit (U : Vec3 × ℝ → Vec3)
    (hG : ∀ n i j, MemLp (blowupLimitAssemblyPressureWindowTensor U n i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume) :
    Measurable (blowupLimitAssemblyPressureLimit U hG) := by
  let f : (Vec3 × ℝ) × ℕ → ℝ := fun p =>
    CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
      (blowupLimitAssemblyPressureWindowTensor U p.2) (hG p.2) p.1
  have hf : Measurable f := measurable_from_prod_countable_left (f := f) fun n =>
    CKN.Leray.rieszPressureSpaceTime_measurable (3 / 2 : ℝ) (by norm_num)
      (blowupLimitAssemblyPressureWindowTensor U n) (hG n)
  have hidx : Measurable (fun z : Vec3 × ℝ => (z, ⌈-z.2⌉₊)) :=
    measurable_id.prodMk (Nat.measurable_ceil.comp measurable_snd.neg)
  have hcomp : blowupLimitAssemblyPressureLimit U hG =
      fun z : Vec3 × ℝ => f (z, ⌈-z.2⌉₊) := rfl
  rw [hcomp]
  exact hf.comp hidx

/-- On each past window the assembled limit pressure is the Riesz pressure
of one truncated tensor. -/
theorem blowupLimitAssemblyPressureLimit_ae_eq
    (U : Vec3 × ℝ → Vec3)
    (hG : ∀ n i j, MemLp (blowupLimitAssemblyPressureWindowTensor U n i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (T : ℝ) :
    blowupLimitAssemblyPressureLimit U hG =ᵐ[volume.restrict (Set.univ ×ˢ Ioo (-T) 0)]
      CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
        (blowupLimitAssemblyPressureWindowTensor U ⌈T⌉₊) (hG ⌈T⌉₊) := by
  set m : ℕ := ⌈T⌉₊
  have hall : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)), ∀ n : ℕ, n ≤ m →
      z ∈ Set.univ ×ˢ Ioo (-((n : ℝ) + 1)) 0 →
        CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
          (blowupLimitAssemblyPressureWindowTensor U m) (hG m) z =
        CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
          (blowupLimitAssemblyPressureWindowTensor U n) (hG n) z := by
    rw [ae_all_iff]
    intro n
    by_cases hnm : n ≤ m
    · filter_upwards [blowupLimitAssemblyPressure_window_agree U hG hnm] with z hz _
      exact hz
    · exact Eventually.of_forall fun z h => absurd h hnm
  have hW : MeasurableSet (Set.univ ×ˢ Ioo (-T) 0 : Set (Vec3 × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem hW] with z hz hzW
  have ht : z.2 ∈ Ioo (-T) 0 := hzW.2
  set n : ℕ := ⌈-z.2⌉₊ with hndef
  have hnm : n ≤ m := Nat.ceil_mono (by linarith only [ht.1])
  have hmem : z ∈ Set.univ ×ˢ Ioo (-((n : ℝ) + 1)) 0 := by
    refine ⟨mem_univ _, ?_, ht.2⟩
    have hle : -z.2 ≤ (n : ℝ) := Nat.le_ceil _
    linarith only [hle]
  exact (hz n hnm hmem).symm

/-- The Riesz pressure of an almost-everywhere vanishing tensor vanishes
almost everywhere. -/
theorem blowupLimitAssemblyPressure_rieszPressure_ae_zero
    {F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hzero : ∀ i j, F i j =ᵐ[volume] 0) :
    CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF =ᵐ[volume] 0 := by
  let Z : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun _ _ _ => 0
  have hZ : ∀ i j, MemLp (Z i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    fun _ _ => MemLp.zero'
  have hFZ := blowupLimitAssemblyPressure_rieszPressure_congr_ae hF hZ hzero
  have hadd : CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
      (fun i j z => Z i j z + Z i j z) (fun i j => (hZ i j).add (hZ i j)) =ᵐ[volume]
      fun z => CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) Z hZ z +
        CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) Z hZ z :=
    blowup_rieszPressureSpaceTime_add_ae Z Z hZ hZ
  have hsum : (fun i j z => Z i j z + Z i j z) = Z := by
    funext i j z
    simp [Z]
  have hcongr := blowup_rieszPressureSpaceTime_congr
    (fun i j => (hZ i j).add (hZ i j)) hZ hsum
  rw [hFZ]
  filter_upwards [hadd] with z hz
  have hz' := (congrFun hcongr z).symm.trans hz
  simp only [Pi.zero_apply]
  linarith only [hz']

end ESS

end
