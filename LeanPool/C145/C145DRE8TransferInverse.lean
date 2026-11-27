/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145DRE8ActualCalibratedInverse
public import LeanPool.C145.C145DRE8SignedGroundResidue

/-! Source Theorem A from own H1/H2 alone. H1 derives the unknown size,
mode matching and positive overlaps; the fixed-positive-variable cleared
numerator argument derives the signed common ground from H2. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
open C145.UncalibratedSmallH2

theorem actual_H1_H2_theoremA_vertex_identification {m n : ℕ}
    (μ c0 c1 : ℝ) (hμ : 0 < μ)
    (Q0 : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates0 b0 : Fin (m + 1) → ℝ)
    (rates1 b1 : Fin (n + 1) → ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hGround0 : ∀ v, Q0 v 0 = c0)
    (hGround1 : ∀ v, Q1 v 0 = c1)
    (hRates0 : Function.Injective rates0)
    (hRates1 : Function.Injective rates1)
    (hRateGround0 : rates0 0 = μ)
    (hRateGround1 : rates1 0 = μ)
    (hAbove0 : ∀ i : Fin m, μ < rates0 i.succ)
    (hAbove1 : ∀ j : Fin n, μ < rates1 j.succ)
    (ha0 : ∀ i, 0 < C145.Pulse.modalOverlap Q0 b0 i)
    (ha1 : ∀ j, 0 < C145.Pulse.modalOverlap Q1 b1 j)
    (ell u : ℝ) (hw : ell < u) (hband : u < 2 * ell)
    (hlo : ∀ i : Fin m, ell ≤ rates0 i.succ) (hhi : ∀ i : Fin m, rates0 i.succ ≤ u)
    (delta : ℝ) (hd : 0 < delta)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤ (b0 j-b0 k) ^ 2)
    (hq : sourceQChebyshevSq b0 ell u delta < 1)
    (hH1 : ∀ s : ℝ, 0 < s →
      C145.H1.firstTransfer rates0 (C145.Pulse.modalOverlap Q0 b0) s =
        C145.H1.firstTransfer rates1 (C145.Pulse.modalOverlap Q1 b1) s)
    (hH2 : ∀ s t : ℝ, 0 < s → 0 < t →
      C145.H2.H rates0
        (C145PhysicalFrame.T Q0 (C145.Pulse.modalOverlap Q0 b0)) s t =
      C145.H2.H rates1
        (C145PhysicalFrame.T Q1 (C145.Pulse.modalOverlap Q1 b1)) s t) :
    ∃ e : Fin (m + 1) ≃ Fin (n + 1),
      m = n ∧ e 0 = 0 ∧
      (∀ i, rates1 (e i) = rates0 i) ∧
      (∀ i, C145.Pulse.modalOverlap Q1 b1 (e i) =
        C145.Pulse.modalOverlap Q0 b0 i) ∧
      c0 = c1 ∧ (∑ v, b0 v) = (∑ w, b1 w) ∧
      ∃ π : Fin (m + 1) ≃ Fin (n + 1),
        (∀ (w : Fin (n + 1)) (v : Fin (m + 1)),
          (∑ i : Fin (m + 1), Q1 w (e i) * Q0 v i) =
            if w = π v then 1 else 0) ∧
        (∀ (v i : Fin (m + 1)), Q1 (π v) (e i) = Q0 v i) ∧
        (∀ (v u : Fin (m + 1)),
          C145CoordinatePermutation.spectralGenerator rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.spectralGenerator rates0 Q0 v u) ∧
        (∀ v : Fin (m + 1), b1 (π v) = b0 v) ∧
        (∀ (v u : Fin (m + 1)),
          C145CoordinatePermutation.decayLaplacian μ rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.decayLaplacian μ rates0 Q0 v u) := by
  classical
  let a0 : Fin (m + 1) → ℝ := C145.Pulse.modalOverlap Q0 b0
  let a1 : Fin (n + 1) → ℝ := C145.Pulse.modalOverlap Q1 b1
  obtain ⟨e, hSize, heGround, heRates, heOverlaps⟩ :=
    C145.H1.known_ground_positive_modal_identification μ hμ rates0 a0 rates1 a1
      hRates0 hRates1 hRateGround0 hRateGround1 hAbove0 hAbove1 ha0 ha1 hH1
  -- Size equality is a data-derived fact; the modal map is retained.
  subst n
  let Q1e : Fin (m + 1) → Fin (m + 1) → ℝ := columnReindex Q1 e
  let r0 : Fin m → ℝ := fun i => rates0 i.succ
  have hQ1e : C145PhysicalFrame.ColumnOrthonormal Q1e :=
    columnReindex_columnOrthonormal Q1 e hQ1
  have hG1ePre : ∀ v, Q1e v 0 = c1 := by
    intro v
    change Q1 v (e 0) = c1
    rw [heGround,hGround1]
  have hResidualRates : Function.Injective r0 := by
    intro i j hij
    apply Fin.succ_inj.mp
    apply hRates0
    exact hij
  have hResidualPos : ∀ i : Fin m, 0 < r0 i := by
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
  have hPos0 : ∀ i, 0 < rates0 i := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j,hj⟩
    · rw [hi,hRateGround0]; exact hμ
    · rw [hj]; exact hμ.trans (hAbove0 j)
  have hHOwn : C145.H2.SamePositive rates0
      (C145PhysicalFrame.T Q0 a0) (C145PhysicalFrame.T Q1e a0) := by
    rw [← hFull]
    exact hHAligned
  have hConstant : c0 = c1 := signed_ground_from_actual_H2 μ hμ rates0 hRates0 hPos0
    hRateGround0 Q0 Q1e a0 c0 c1 hQ0 hQ1e hGround0 hG1ePre ha0 hHOwn
  have hG1e : ∀ v, Q1e v 0 = c0 := by
    intro v
    rw [hG1ePre,← hConstant]
  -- This derives the arbitrary-dimension vertex map from actual full H2.
  obtain ⟨π, hDeltaRaw, hRowsRaw⟩ :=
    actual_calibrated_H2_vertex_identification μ r0 hResidualRates Q0 Q1e b0 c0
      hQ0 hQ1e (fun i => ne_of_gt (ha0 i)) hGround0 hG1e hHAligned
      ell u hw hband hlo hhi delta hd hsep hq
  have hDelta : ∀ (w v : Fin (m + 1)),
      (∑ i : Fin (m + 1), Q1 w (e i) * Q0 v i) =
        if w = π v then 1 else 0 := by
    intro w v
    exact hDeltaRaw w v
  have hRows : ∀ (v i : Fin (m + 1)), Q1 (π v) (e i) = Q0 v i := by
    intro v i
    exact hRowsRaw v i
  have hGenerator : ∀ (v u : Fin (m + 1)),
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
  have hPort : ∀ v : Fin (m + 1), b1 (π v) = b0 v := by
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
  have hMeans : (∑ v,b0 v) = (∑ v,b1 v) := by
    calc
      _ = ∑ v,b1 (π v) := by
        apply Finset.sum_congr rfl; intro v hv; exact (hPort v).symm
      _ = _ := Equiv.sum_comp π b1
  have hL : ∀ (v u : Fin (m + 1)),
      C145CoordinatePermutation.decayLaplacian μ rates1 Q1 (π v) (π u) =
        C145CoordinatePermutation.decayLaplacian μ rates0 Q0 v u := by
    intro v u
    simp only [C145CoordinatePermutation.decayLaplacian, hGenerator,
      π.apply_eq_iff_eq]
  exact ⟨e, rfl, heGround, heRates, heOverlaps, hConstant, hMeans,
    π, hDelta, hRows, hGenerator, hPort, hL⟩

end C145DRE8

end
