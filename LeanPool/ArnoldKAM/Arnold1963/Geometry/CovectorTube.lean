/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.TypeD
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.Erosion
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Abel

/-!
Exact images of maximum-norm closed balls under linear forms, and erosion of complex tubes.
-/

@[expose] public section
noncomputable section
open Set Metric
open scoped NNReal
namespace KamProject.Arnold1963

theorem covectorLength_nonneg {n} (ℓ : RealSpace n) : 0 ≤ covectorLength ℓ :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem realCovectorPairing_add {n} (ℓ : RealSpace n) (x y : ComplexSpace n) :
    realCovectorPairing ℓ (x + y) = realCovectorPairing ℓ x + realCovectorPairing ℓ y := by
  simp [realCovectorPairing, mul_add, Finset.sum_add_distrib]

theorem realCovectorPairing_sub {n} (ℓ : RealSpace n) (x y : ComplexSpace n) :
    realCovectorPairing ℓ (x - y) = realCovectorPairing ℓ x - realCovectorPairing ℓ y := by
  simp [realCovectorPairing, mul_sub, Finset.sum_sub_distrib]

theorem norm_realCovectorPairing_le {n} (ℓ : RealSpace n) (z : ComplexSpace n) :
    ‖realCovectorPairing ℓ z‖ ≤ covectorLength ℓ * ‖z‖ := by
  calc
    _ ≤ ∑ j, ‖(ℓ j : ℂ) * z j‖ := norm_sum_le _ _
    _ = ∑ j, |ℓ j| * ‖z j‖ := by simp
    _ ≤ ∑ j, |ℓ j| * ‖z‖ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm z j) (abs_nonneg _)
    _ = _ := by rw [covectorLength, Finset.sum_mul]

theorem covector_has_lift {n} (ℓ : RealSpace n) (hℓ : 0 < covectorLength ℓ) (w : ℂ) :
    ∃ v : ComplexSpace n, realCovectorPairing ℓ v = w ∧ ‖v‖ ≤ ‖w‖ / covectorLength ℓ := by
  classical
  let s : Fin n → ℝ := fun j => if 0 ≤ ℓ j then 1 else -1
  have hs : ∀ j, ℓ j * s j = |ℓ j| := by
    intro j
    dsimp [s]
    split_ifs with hj
    · simp [abs_of_nonneg hj]
    · simp [abs_of_neg (lt_of_not_ge hj)]
  let v : ComplexSpace n := fun j => (s j : ℂ) * (w / (covectorLength ℓ : ℂ))
  refine ⟨v, ?_, ?_⟩
  · have he : realCovectorPairing ℓ v =
        (covectorLength ℓ : ℂ) * (w / (covectorLength ℓ : ℂ)) := by
      simp only [realCovectorPairing, v, ← mul_assoc, ← Complex.ofReal_mul, hs,
        ← Finset.sum_mul, ← Complex.ofReal_sum, covectorLength]
    rw [he]
    field_simp [ne_of_gt hℓ]
  · apply (complex_norm_le_iff _ (by positivity)).mpr
    intro j
    have hsn : |s j| ≤ 1 := by dsimp [s]; split_ifs <;> norm_num
    calc
      ‖v j‖ = |s j| * (‖w‖ / covectorLength ℓ) := by
        simp only [v, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div,
          abs_of_pos hℓ]
      _ ≤ _ := by
        simpa using mul_le_mul_of_nonneg_right hsn
          (by positivity : 0 ≤ ‖w‖ / covectorLength ℓ)

theorem realCovectorPairing_image_closedBall {n} (ℓ : RealSpace n)
    (hℓ : 0 < covectorLength ℓ) (x : ComplexSpace n) (d : ℝ≥0) :
    realCovectorPairing ℓ '' closedBall x (d : ℝ) =
      closedBall (realCovectorPairing ℓ x) ((d : ℝ) * covectorLength ℓ) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    simp only [mem_closedBall, dist_eq_norm] at hz ⊢
    rw [← realCovectorPairing_sub]
    exact (norm_realCovectorPairing_le ℓ _).trans (by
      simpa only [dist_eq_norm, mul_comm] using mul_le_mul_of_nonneg_left hz hℓ.le)
  · intro hw
    obtain ⟨v, hv, hn⟩ := covector_has_lift ℓ hℓ (w - realCovectorPairing ℓ x)
    refine ⟨x + v, ?_, ?_⟩
    · simp only [mem_closedBall, dist_eq_norm] at hw ⊢
      rw [add_sub_cancel_left]
      exact hn.trans ((div_le_iff₀ hℓ).mpr hw)
    · rw [realCovectorPairing_add, hv]
      abel

theorem erosion_tube_complement {n} (ℓ : RealSpace n) (hℓ : 0 < covectorLength ℓ)
    (c a : ℝ) (ha : 0 < a) (d : ℝ≥0) :
    erosion {z | a ≤ ‖realCovectorPairing ℓ z - (c : ℂ)‖} d =
      {z | a + (d : ℝ) * covectorLength ℓ ≤ ‖realCovectorPairing ℓ z - (c : ℂ)‖} := by
  ext x
  have he : x ∈ erosion {z | a ≤ ‖realCovectorPairing ℓ z - (c : ℂ)‖} d ↔
      Disjoint (realCovectorPairing ℓ '' closedBall x (d : ℝ)) (ball (c : ℂ) a) := by
    rw [disjoint_left]
    constructor
    · rintro hx _ ⟨z, hz, rfl⟩ hw
      exact (not_lt_of_ge (hx hz)) (by simpa only [mem_ball, dist_eq_norm] using hw)
    · intro hx z hz
      exact le_of_not_gt (fun hw => hx ⟨z, hz, rfl⟩ (by
        simpa only [mem_ball, dist_eq_norm] using hw))
  rw [he, realCovectorPairing_image_closedBall ℓ hℓ,
    disjoint_closedBall_ball_iff (mul_nonneg d.coe_nonneg hℓ.le) ha]
  simp only [mem_ofPred_eq, dist_eq_norm, add_comm]

end KamProject.Arnold1963
