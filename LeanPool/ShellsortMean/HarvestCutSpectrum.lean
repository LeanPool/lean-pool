/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestProjectedFar
public import LeanPool.ShellsortMean.HarvestMenuSieve
public import LeanPool.ShellsortMean.RoughGapPeriodicCorrection

/-! Join the physical exponential Fourier energy to the signed, all-cuts
correction in the actual square displacement of one ordinary gap pass. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestCutSpectrum
open Finset ZMod RoughGapEndpoint RoughGapDenominatorAverage HarvestProjectedFar

private def gridEquiv (h : ℕ) [NeZero h] : Fin h ≃ ZMod h where
  toFun a := (a.val : ZMod h)
  invFun r := ⟨r.val, r.val_lt⟩
  left_inv a := Fin.ext (val_natCast_of_lt a.isLt)
  right_inv := natCast_zmod_val

theorem physical_nonzero_parseval {n h : ℕ} (p : RankPlacement n)
    (T : ℕ) (hT : T ≤ n) (hp : 0 < h) :
    (∑ a ∈ (range h).filter (0 < ·), energy 0 (fun i : Fin n => (slotError p T i : ℂ)) (a, h)) =
      (h : ℝ) * ∑ r : Fin h, (residueError p h T r.val : ℝ) ^ 2 := by
  let : NeZero h := ⟨hp.ne'⟩
  let loc (i : Fin n) := i.val
  let v (i : Fin n) := (slotError p T i : ℝ)
  let f (r : ZMod h) := ‖coeff loc (fun i => (v i : ℂ)) r‖ ^ 2
  have vz : ∑ i, v i = 0 := by dsimp [v]; exact_mod_cast sum_slotError p T
  have fz : f 0 = 0 := by simp [f, coeff, ←Complex.ofReal_sum, vz]
  have cut := RoughGapFiniteFourier.actual_nonzero_spectrum (fun i : Fin n => (i.val : ZMod h)) v
  change (∑ r ∈ univ.erase (0 : ZMod h), Complex.normSq (coeff loc (fun i => (v i : ℂ)) r)) = _
    at cut
  simp only [← Complex.sq_norm, vz, zero_div, sub_zero] at cut
  have allEq : (∑ r, f r) = ∑ r ∈ univ.erase (0 : ZMod h), f r := by
    simp [fz]
  have bin (r : Fin h) : RoughGapFiniteFourier.bins (fun i : Fin n => (i.val : ZMod h)) v
      (gridEquiv h r) = (residueError p h T r.val : ℝ) := by
    rw [residueError_eq_sum p T r.val hT, Int.cast_sum]
    apply sum_congr rfl
    intro i _
    have e : ((i.val : ZMod h) = gridEquiv h r) ↔ i.val % h = r.val := by
      change ((i.val : ZMod h) = (r.val : ZMod h)) ↔ _
      simp only [natCast_eq_natCast_iff', Nat.mod_eq_of_lt r.isLt]
    simp [e, v]
  have raw (a : ℕ) : energy 0 (fun i : Fin n => (slotError p T i : ℂ)) (a, h) = f (a : ZMod h) := by
    simpa [f, loc, v] using (coeff_energy (h := h) (fun i : Fin n => (slotError p T i : ℂ)) a).symm
  calc
    _ = ∑ a ∈ range h, f (a : ZMod h) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro a _
      by_cases ap : 0 < a
      · simp [ap, raw]
      · have : a = 0 := by omega
        simp [this, fz]
    _ = ∑ r, f r := by
      rw [← Fin.sum_univ_eq_sum_range]
      exact Fintype.sum_equiv (gridEquiv h) _ _ (fun _ => rfl)
    _ = _ := by
      rw [allEq, show (∑ r ∈ univ.erase (0 : ZMod h), f r) = _ from cut]
      congr 1
      exact (Fintype.sum_equiv (gridEquiv h) _ _ (fun r => by rw [bin])).symm

/-- Sum the true cut energies first. Only then is the total periodic
correction known to have the sign that yields the upper bound. -/
theorem square_le_physical_spectrum {n h : ℕ} (p : RankPlacement n) (hp : 0 < h) :
    (RoughGapScaleAssembly.squareDisplacement (gapSort p h) : ℝ) ≤
    ∑ t ∈ range n, ∑ a ∈ (range h).filter (0 < ·),
      energy 0 (fun i : Fin n => (slotError p (t + 1) i : ℂ)) (a, h) := by
  have each (t : ℕ) (ht : t ∈ range n) := physical_nonzero_parseval p (t + 1) (mem_range.mp ht) hp
  rw [sum_congr rfl each, ←mul_sum]
  exact_mod_cast gapSort_square_le_energy p hp


end Shellsort.HarvestCutSpectrum
