/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145N6PositiveGraph
public import LeanPool.C145.C145UncalibratedSmallH2

/-!
# Recovery of the six-vertex calibration from response data.
-/

@[expose] public section
noncomputable section
namespace C145N6Frame
open scoped BigOperators
open C145.UncalibratedSmallH2

theorem source_modal_overlap : C145.Pulse.modalOverlap frame port = overlap := by
  funext i
  simpa only [C145.Pulse.modalOverlap, mul_comm] using (overlap_actual_projection i).symm

theorem source_overlap_positive : ∀ i, 0 < C145.Pulse.modalOverlap frame port i := by
  intro i
  rw [source_modal_overlap]
  unfold overlap
  apply div_pos
  · fin_cases i <;> norm_num [numerator]
  · exact mul_pos (by norm_num) (Real.sqrt_pos.2 (gramWeight_pos i))
theorem literalRates_injective : Function.Injective literalRates := by
  intro i j h; fin_cases i <;> fin_cases j <;> norm_num [literalRates] at *
theorem literalRates_above : ∀ i : Fin 5, 1 < literalRates i.succ := by
  intro i; fin_cases i <;> norm_num [literalRates]

theorem literal_N6_uncalibrated_identification {n : ℕ}
    (c1 : ℝ) (Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates1 b1 : Fin (n + 1) → ℝ)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hGround1 : ∀ v, Q1 v 0 = c1)
    (hRates1 : Function.Injective rates1)
    (hRateGround1 : rates1 0 = 1)
    (hAbove1 : ∀ j : Fin n, 1 < rates1 j.succ)
    (ha1 : ∀ j, 0 < C145.Pulse.modalOverlap Q1 b1 j)
    (hH1 : ∀ s : ℝ, 0 < s →
      C145.H1.firstTransfer literalRates (C145.Pulse.modalOverlap frame port) s =
        C145.H1.firstTransfer rates1 (C145.Pulse.modalOverlap Q1 b1) s)
    (hB : ∀ t : ℝ, 0 ≤ t →
      C145.Pulse.coincidentPulse frame literalRates port t =
        C145.Pulse.coincidentPulse Q1 rates1 b1 t)
    (hH2 : ∀ s t : ℝ, 0 < s → 0 < t →
      C145.H2.H literalRates
        (C145PhysicalFrame.T frame (C145.Pulse.modalOverlap frame port)) s t =
      C145.H2.H rates1
        (C145PhysicalFrame.T Q1 (C145.Pulse.modalOverlap Q1 b1)) s t) :
    ∃ e : Fin (5 + 1) ≃ Fin (n + 1),
      5 = n ∧ e 0 = 0 ∧
      (∀ i, rates1 (e i) = literalRates i) ∧
      (∀ i, C145.Pulse.modalOverlap Q1 b1 (e i) =
        C145.Pulse.modalOverlap frame port i) ∧
      (1 / Real.sqrt 6) = c1 ∧ (∑ v, port v) = (∑ w, b1 w) ∧
      ∃ π : Fin (5 + 1) ≃ Fin (n + 1),
        (∀ (w : Fin (n + 1)) (v : Fin (5 + 1)),
          (∑ i : Fin (5 + 1), Q1 w (e i) * frame v i) =
            if w = π v then 1 else 0) ∧
        (∀ (v i : Fin (5 + 1)), Q1 (π v) (e i) = frame v i) ∧
        (∀ (v u : Fin (5 + 1)),
          C145CoordinatePermutation.spectralGenerator rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.spectralGenerator literalRates frame v u) ∧
        (∀ v : Fin (5 + 1), b1 (π v) = port v) ∧
        (∀ (v u : Fin (5 + 1)),
          C145CoordinatePermutation.decayLaplacian 1 rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.decayLaplacian 1 literalRates frame v u) := by
  let μ : ℝ := 1
  let c0 : ℝ := 1 / Real.sqrt 6
  let Q0 := frame
  let rates0 := literalRates
  let b0 := port
  have hμ : 0 < μ := by norm_num [μ]
  have hQ0 := frame_orthonormal
  have hGround0 := frame_ground
  have hRates0 := literalRates_injective
  have hRateGround0 : rates0 0 = μ := rfl
  have hAbove0 := literalRates_above
  have ha0 := source_overlap_positive
  classical
  let a0 : Fin 6 → ℝ := C145.Pulse.modalOverlap Q0 b0
  let a1 : Fin (n + 1) → ℝ := C145.Pulse.modalOverlap Q1 b1
  obtain ⟨e, hSize, heGround, heRates, heOverlaps, hConstant, hMeans⟩ :=
    C145.Pulse.actual_signed_ground_calibration μ c0 c1 hμ Q0 Q1
      rates0 b0 a0 rates1 b1 a1 hQ0 hQ1 hGround0 hGround1
      hRates0 hRates1 hRateGround0 hRateGround1 hAbove0 hAbove1
      ha0 ha1 (fun _ => rfl) (fun _ => rfl) hH1 hB
  -- Size equality is a data-derived fact; the modal map is retained.
  subst n
  let Q1e : Fin 6 → Fin 6 → ℝ := columnReindex Q1 e
  let r0 : Fin 5 → ℝ := fun i => rates0 i.succ
  have hQ1e : C145PhysicalFrame.ColumnOrthonormal Q1e :=
    columnReindex_columnOrthonormal Q1 e hQ1
  have hG1e : ∀ v, Q1e v 0 = c0 := by
    intro v
    change Q1 v (e 0) = c0
    rw [heGround, hGround1, ← hConstant]
  have hResidualRates : Function.Injective r0 := by
    intro i j hij
    apply Fin.succ_inj.mp
    apply hRates0
    exact hij
  have hResidualPos : ∀ i : Fin 5, 0 < r0 i := by
    intro i
    exact lt_trans hμ (hAbove0 i)
  have hFull : C145.H2.fullRates μ r0 = rates0 :=
    fullRates_eq_own μ rates0 hRateGround0
  have hA : (fun i => a1 (e i)) = a0 := funext heOverlaps
  have hLam : (fun i => rates1 (e i)) = rates0 := funext heRates
  have hT : C145PhysicalFrame.T Q1e a0 =
      (fun i j k => C145PhysicalFrame.T Q1 a1 (e i) (e j) (e k)) := by
    funext i j k
    simpa only [Q1e, hA] using tensor_columnReindex Q1 a1 e i j k
  have hAlignedResponse : ∀ s t : ℝ,
      C145.H2.H rates0 (C145PhysicalFrame.T Q1e a0) s t =
        C145.H2.H rates1 (C145PhysicalFrame.T Q1 a1) s t := by
    intro s t
    have h := H_modal_reindex rates1 (C145PhysicalFrame.T Q1 a1) e s t
    rw [hLam, ← hT] at h
    exact h
  have hHAligned : C145.H2.SamePositive (C145.H2.fullRates μ r0)
      (C145PhysicalFrame.T Q0 a0) (C145PhysicalFrame.T Q1e a0) := by
    intro s t hs ht
    rw [hFull]
    exact (hH2 s t hs ht).trans (hAlignedResponse s t).symm
  have ha0eq : a0 = overlap := source_modal_overlap
  have hAlignedN6 : C145.H2.SamePositive (C145.H2.fullRates 1 C145N6.rates)
      (C145PhysicalFrame.T frame overlap) (C145PhysicalFrame.T Q1e overlap) := by
    simpa only [hFull, ha0eq, ← literalRates_full] using hHAligned
  obtain ⟨π, hDeltaRaw, hRowsRaw, _, _, _⟩ :=
    calibrated_response_spectral_transport 1 Q1e hQ1e hG1e hAlignedN6
  have hDelta : ∀ (w v : Fin 6),
      (∑ i : Fin 6, Q1 w (e i) * Q0 v i) =
        if w = π v then 1 else 0 := by
    intro w v
    exact hDeltaRaw w v
  have hRows : ∀ (v i : Fin 6), Q1 (π v) (e i) = Q0 v i := by
    intro v i
    exact hRowsRaw v i
  have hGenerator : ∀ (v u : Fin 6),
      C145CoordinatePermutation.spectralGenerator rates1 Q1 (π v) (π u) =
        C145CoordinatePermutation.spectralGenerator rates0 Q0 v u := by
    intro v u
    unfold C145CoordinatePermutation.spectralGenerator
    congr 1
    calc
      (∑ j, rates1 j * Q1 (π v) j * Q1 (π u) j) =
          ∑ i, rates1 (e i) * Q1 (π v) (e i) * Q1 (π u) (e i) :=
        (e.sum_comp (fun j => rates1 j * Q1 (π v) j * Q1 (π u) j)).symm
      _ = ∑ i, rates0 i * Q0 v i * Q0 u i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [heRates i, hRows v i, hRows u i]
  have hPort : ∀ v : Fin 6, b1 (π v) = b0 v := by
    intro v
    have hReconstruct1 := congrFun (spectralPort_modalOverlap Q1 b1 hQ1) (π v)
    have hReconstruct0 := congrFun (spectralPort_modalOverlap Q0 b0 hQ0) v
    change (∑ j, a1 j * Q1 (π v) j) = b1 (π v) at hReconstruct1
    change (∑ i, a0 i * Q0 v i) = b0 v at hReconstruct0
    calc
      b1 (π v) = ∑ j, a1 j * Q1 (π v) j := hReconstruct1.symm
      _ = ∑ i, a1 (e i) * Q1 (π v) (e i) :=
        (e.sum_comp (fun j => a1 j * Q1 (π v) j)).symm
      _ = ∑ i, a0 i * Q0 v i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [heOverlaps i, hRows v i]
      _ = b0 v := hReconstruct0
  have hL : ∀ (v u : Fin 6),
      C145CoordinatePermutation.decayLaplacian μ rates1 Q1 (π v) (π u) =
        C145CoordinatePermutation.decayLaplacian μ rates0 Q0 v u := by
    intro v u
    simp only [C145CoordinatePermutation.decayLaplacian, hGenerator,
      π.apply_eq_iff_eq]
  exact ⟨e, rfl, heGround, heRates, heOverlaps, hConstant, hMeans,
    π, hDelta, hRows, hGenerator, hPort, hL⟩

end C145N6Frame

end
