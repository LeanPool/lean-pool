/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145CoordinatePermutation
public import LeanPool.C145.C145SignedGroundPulseCalibration
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
C145: own finite H1, actual coincident pulse and ordinary H2 data identify one
vertex bijection through total size N <= 5. Each model has its own full real
orthonormal frame, constant ground column, simple physical rates and signed
vertex port. Actual positively oriented visible overlaps are scalar products.

H1 and the actual pulse derive size, modal matching and the common signed
constant. Only the second frame's modal columns are then reindexed. The small
ordinary H2/counting-trace theorem derives a vertex map, retained for frame
rows, original generators, actual ports and decay Laplacians. Ground remains
in all full sums; the empty nonground family at N=1 is permitted. Physical
successor rates are not shifted by mu, and additive resonances are permitted.

Finite spectral data and the stated source-class assumptions are inputs.
Raw ODE/response extraction, temporal jets, graph positivity, normalization,
cyclicity-to-spectrum derivation and identification beyond N=5 are outside
this statement. The modal map and vertex map are distinct derived objects.
-/

@[expose] public section

noncomputable section
namespace C145.UncalibratedSmallH2
open scoped BigOperators

/-- Relabel the modal columns of a frame while preserving vertex indices. -/
def columnReindex {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (e : Equiv.Perm (Fin (n + 1))) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun v i => Q v (e i)

/-- Reindexing columns preserves the full Gram identities. -/
theorem columnReindex_columnOrthonormal {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (e : Equiv.Perm (Fin (n + 1)))
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q) :
    C145PhysicalFrame.ColumnOrthonormal (columnReindex Q e) := by
  classical
  intro i j
  change (∑ v, Q v (e i) * Q v (e j)) = if i = j then 1 else 0
  simpa only [e.apply_eq_iff_eq] using hQ (e i) (e j)

/-- All three tensor slots and their actual overlap factors move together. -/
theorem tensor_columnReindex {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (a : Fin (n + 1) → ℝ)
    (e : Equiv.Perm (Fin (n + 1)))
    (i j k : Fin (n + 1)) :
    C145PhysicalFrame.T (columnReindex Q e) (fun r => a (e r)) i j k =
      C145PhysicalFrame.T Q a (e i) (e j) (e k) := by
  rfl

/-- Literal equality of the complete triple sum, without pole evaluation. -/
theorem H_modal_reindex {N : ℕ}
    (rates : Fin N → ℝ) (E : C145.H2.Tensor N)
    (e : Equiv.Perm (Fin N)) (s t : ℝ) :
    C145.H2.H (fun i => rates (e i))
      (fun i j k => E (e i) (e j) (e k)) s t =
        C145.H2.H rates E s t := by
  classical
  let F : Fin N → Fin N → Fin N → ℝ := fun i j k =>
    E i j k / ((s + rates i) * (t + rates j) * (s + t + rates k))
  change (∑ i, ∑ j, ∑ k, F (e i) (e j) (e k)) = ∑ i, ∑ j, ∑ k, F i j k
  calc
    (∑ i, ∑ j, ∑ k, F (e i) (e j) (e k)) =
        ∑ i, ∑ j, ∑ k, F (e i) (e j) k := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact Equiv.sum_comp e (fun k => F (e i) (e j) k)
    _ = ∑ i, ∑ j, ∑ k, F (e i) j k := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Equiv.sum_comp e (fun j => ∑ k, F (e i) j k)
    _ = ∑ i, ∑ j, ∑ k, F i j k :=
      Equiv.sum_comp e (fun i => ∑ j, ∑ k, F i j k)

/-- The accepted successor family consists of physical rates themselves. -/
theorem fullRates_eq_own {n : ℕ}
    (μ : ℝ) (rates : Fin (n + 1) → ℝ)
    (hGround : rates 0 = μ) :
    C145.H2.fullRates μ (fun i : Fin n => rates i.succ) = rates := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, hj⟩
  · rw [hi]
    simpa only [C145.H2.fullRates, Fin.cases_zero] using hGround.symm
  · rw [hj]
    rfl

/-- Full-frame reconstruction recovers the actual signed vertex port. -/
theorem spectralPort_modalOverlap {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (b : Fin (n + 1) → ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q) :
    C145CoordinatePermutation.spectralPort (C145.Pulse.modalOverlap Q b) Q = b := by
  classical
  funext v
  simpa only [C145CoordinatePermutation.spectralPort, C145.Pulse.modalOverlap,
    mul_comm] using C145CoordinatePermutation.frame_reconstruction Q hQ b v

/-- Own actual data derive modal calibration and one common vertex bijection. -/
theorem actual_small_H2_vertex_identification {m n : ℕ}
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
    (hm : m ≤ 4)
    (hH1 : ∀ s : ℝ, 0 < s →
      C145.H1.firstTransfer rates0 (C145.Pulse.modalOverlap Q0 b0) s =
        C145.H1.firstTransfer rates1 (C145.Pulse.modalOverlap Q1 b1) s)
    (hB : ∀ t : ℝ, 0 ≤ t →
      C145.Pulse.coincidentPulse Q0 rates0 b0 t =
        C145.Pulse.coincidentPulse Q1 rates1 b1 t)
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
  obtain ⟨e, hSize, heGround, heRates, heOverlaps, hConstant, hMeans⟩ :=
    C145.Pulse.actual_signed_ground_calibration μ c0 c1 hμ Q0 Q1
      rates0 b0 a0 rates1 b1 a1 hQ0 hQ1 hGround0 hGround1
      hRates0 hRates1 hRateGround0 hRateGround1 hAbove0 hAbove1
      ha0 ha1 (fun _ => rfl) (fun _ => rfl) hH1 hB
  -- Size equality is a data-derived fact; the modal map is retained.
  subst n
  let Q1e : Fin (m + 1) → Fin (m + 1) → ℝ := columnReindex Q1 e
  let r0 : Fin m → ℝ := fun i => rates0 i.succ
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
  -- This is the sole call that derives the vertex map.
  obtain ⟨π, hDeltaRaw, hRowsRaw, _, _, _⟩ :=
    C145CoordinatePermutation.calibrated_small_H2_vertex_identification μ r0
      hResidualRates hResidualPos Q0 Q1e a0 c0 hQ0 hQ1e
      (fun i => ne_of_gt (ha0 i)) hGround0 hG1e hm hHAligned
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
  have hL : ∀ (v u : Fin (m + 1)),
      C145CoordinatePermutation.decayLaplacian μ rates1 Q1 (π v) (π u) =
        C145CoordinatePermutation.decayLaplacian μ rates0 Q0 v u := by
    intro v u
    simp only [C145CoordinatePermutation.decayLaplacian, hGenerator,
      π.apply_eq_iff_eq]
  exact ⟨e, rfl, heGround, heRates, heOverlaps, hConstant, hMeans,
    π, hDelta, hRows, hGenerator, hPort, hL⟩


end C145.UncalibratedSmallH2
end

end
