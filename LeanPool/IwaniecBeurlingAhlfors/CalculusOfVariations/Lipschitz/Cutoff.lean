/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.Gradient

/-!
# Lipschitz cut-offs

* `cubeCutoff δ = ∏ boundaryRamp δ (x_i)`: `0` off the unit cube, `1` on `[δ, 1 − δ]^m`,
  with values in `[0, 1]` and Lipschitz constant `m / δ` in the sup norm.
* `ballCutoff x r δ`: `1` on `closedBall x ((1 − δ) r)`, `0` outside `ball x r`,
  `1/(δ r)`-Lipschitz;
* `cv_lipschitz_smul`: a product `θ g` with `θ ∈ [0, 1]` vanishing outside `S` and `|g| ≤ B` on
  `S` is `(L_g + L_θ B)`-Lipschitz.
-/

@[expose] public section

open Metric Set MeasureTheory Filter Topology
open scoped Pointwise

namespace CalculusOfVariations

variable {d m : ℕ}

/-- The one-dimensional profile: `0` off `(0, 1)`, `1` on `[δ, 1 − δ]`, `(1/δ)`-Lipschitz. -/
noncomputable def boundaryRamp (δ t : ℝ) : ℝ := max 0 (min 1 (min (t / δ) ((1 - t) / δ)))

private lemma rd_h_mem (δ t : ℝ) : 0 ≤ boundaryRamp δ t ∧ boundaryRamp δ t ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private lemma rd_h_lip {δ : ℝ} (hδ : 0 < δ) (s t : ℝ) :
    |boundaryRamp δ s - boundaryRamp δ t| ≤ |s - t| / δ := by
  have h1 := abs_max_sub_max_le_max (0 : ℝ) (min 1 (min (s / δ) ((1 - s) / δ))) 0
    (min 1 (min (t / δ) ((1 - t) / δ)))
  have h2 := abs_min_sub_min_le_max (1 : ℝ) (min (s / δ) ((1 - s) / δ)) 1
      (min (t / δ) ((1 - t) / δ))
  have h3 := abs_min_sub_min_le_max (s / δ) ((1 - s) / δ) (t / δ) ((1 - t) / δ)
  have e1 : |s / δ - t / δ| = |s - t| / δ := by rw [← sub_div, abs_div, abs_of_pos hδ]
  have e2 : |(1 - s) / δ - (1 - t) / δ| = |s - t| / δ := by
    rw [← sub_div, abs_div, abs_of_pos hδ, show 1 - s - (1 - t) = -(s - t) by ring, abs_neg]
  change |max 0 _ - max 0 _| ≤ _
  calc _ ≤ _ := h1
    _ = |min 1 (min (s / δ) ((1 - s) / δ)) - min 1 (min (t / δ) ((1 - t) / δ))| := by simp
    _ ≤ _ := h2
    _ = |min (s / δ) ((1 - s) / δ) - min (t / δ) ((1 - t) / δ)| := by simp
    _ ≤ _ := h3
    _ = |s - t| / δ := by rw [e1, e2, max_self]

private lemma rd_h_zero {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ 0 ∨ 1 ≤ t) : boundaryRamp δ t = 0 := by
  apply max_eq_left
  refine (min_le_right _ _).trans ?_
  rcases ht with ht | ht
  · exact (min_le_left _ _).trans (div_nonpos_of_nonpos_of_nonneg ht hδ.le)
  · exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)

private lemma rd_h_one {δ t : ℝ} (hδ : 0 < δ) (h1 : δ ≤ t) (h2 : t ≤ 1 - δ) :
    boundaryRamp δ t = 1 := by
  have a : 1 ≤ t / δ := (one_le_div hδ).2 h1
  have b : 1 ≤ (1 - t) / δ := (one_le_div hδ).2 (by linarith)
  simp only [boundaryRamp, min_eq_left (le_min a b), max_eq_right zero_le_one]

/-- The cutoff `η_δ (x) = ∏ h_δ (x_i)`. -/
noncomputable def cubeCutoff (δ : ℝ) (x : Fin m → ℝ) : ℝ := ∏ i, boundaryRamp δ (x i)

private lemma rd_abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have hP : |∏ i ∈ s, a i| ≤ 1 := by
      rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => (ha i).1)]
      exact Finset.prod_le_one₀ (fun i _ => (ha i).1) fun i _ => (ha i).2
    have hbj : |b j| ≤ 1 := by rw [abs_of_nonneg (hb j).1]; exact (hb j).2
    calc |a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i|
        = |(a j - b j) * ∏ i ∈ s, a i + b j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)| := by ring_nf
      _ ≤ |a j - b j| * |∏ i ∈ s, a i| + |b j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |a j - b j| * 1 + 1 * ∑ i ∈ s, |a i - b i| := by
          gcongr
      _ = |a j - b j| + ∑ i ∈ s, |a i - b i| := by ring

lemma rd_eta_mem (δ : ℝ) (x : Fin m → ℝ) : 0 ≤ cubeCutoff δ x ∧ cubeCutoff δ x ≤ 1 :=
  ⟨Finset.prod_nonneg fun _ _ => (rd_h_mem δ _).1,
    Finset.prod_le_one₀ (fun _ _ => (rd_h_mem δ _).1) fun _ _ => (rd_h_mem δ _).2⟩

lemma rd_eta_lip {δ : ℝ} (hδ : 0 < δ) (x y : Fin m → ℝ) :
    |cubeCutoff δ x - cubeCutoff δ y| ≤ m * dist x y / δ := by
  refine (rd_abs_prod_sub_prod_le _ _ _ (fun i => rd_h_mem δ _) fun i => rd_h_mem δ _).trans ?_
  calc ∑ i, |boundaryRamp δ (x i) - boundaryRamp δ (y i)| ≤ ∑ _i : Fin m, dist x y / δ := by
        gcongr with i
        refine (rd_h_lip hδ _ _).trans ?_
        gcongr
        rw [← Real.dist_eq]; exact dist_le_pi_dist x y i
    _ = m * dist x y / δ := by simp [Finset.card_univ]; ring

lemma rd_eta_zero {δ : ℝ} (hδ : 0 < δ) {x : Fin m → ℝ} (hx : x ∉ unitCube m) :
    cubeCutoff δ x = 0 := by
  simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, not_forall,
    not_and_or, not_lt] at hx
  obtain ⟨i, hi⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (rd_h_zero hδ hi)

/-- The inner cube `(δ, 1 − δ)^m`. -/
def innerCube (δ : ℝ) : Set (Fin m → ℝ) := Set.pi univ fun _ => Ioo δ (1 - δ)

lemma rd_inner_isOpen (δ : ℝ) : IsOpen (innerCube (m := m) δ) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

lemma rd_eta_one {δ : ℝ} (hδ : 0 < δ) {x : Fin m → ℝ} (hx : x ∈ innerCube δ) :
    cubeCutoff δ x = 1 :=
  Finset.prod_eq_one fun i _ => rd_h_one hδ (hx i (Set.mem_univ _)).1.le
      (hx i (Set.mem_univ _)).2.le

/-- The cut-off equal to `1` on `closedBall x ((1 - δ) r)`, `0` outside `ball x r`, and
`1/(δ r)`-Lipschitz. -/
noncomputable def ballCutoff (x : Fin m → ℝ) (r δ : ℝ) (y : Fin m → ℝ) : ℝ :=
  max 0 (min 1 ((r - ‖y - x‖) / (δ * r)))

theorem ballCutoff_nonneg (x : Fin m → ℝ) (r δ : ℝ) (y : Fin m → ℝ) : 0 ≤ ballCutoff x r δ y :=
  le_max_left _ _

theorem ballCutoff_le_one (x : Fin m → ℝ) (r δ : ℝ) (y : Fin m → ℝ) : ballCutoff x r δ y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem ballCutoff_eq_one {x : Fin m → ℝ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) {y : Fin m → ℝ}
    (hy : ‖y - x‖ ≤ (1 - δ) * r) : ballCutoff x r δ y = 1 := by
  have h : 1 ≤ (r - ‖y - x‖) / (δ * r) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  simp [ballCutoff, min_eq_left h]

theorem ballCutoff_eq_zero {x : Fin m → ℝ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) {y : Fin m → ℝ}
    (hy : r ≤ ‖y - x‖) : ballCutoff x r δ y = 0 := by
  have h : (r - ‖y - x‖) / (δ * r) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  simp [ballCutoff, (min_le_right _ _).trans h]

theorem ballCutoff_lipschitz (x : Fin m → ℝ) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    LipschitzWith (1 / (δ * r)).toNNReal (ballCutoff x r δ) := by
  have hu : LipschitzWith (1 / (δ * r)).toNNReal fun y : Fin m → ℝ => (r - ‖y - x‖) / (δ * r) := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity), ← sub_div, abs_div,
      abs_of_pos (by positivity : 0 < δ * r), div_le_iff₀ (by positivity : 0 < δ * r)]
    have : |r - ‖y - x‖ - (r - ‖z - x‖)| ≤ dist y z := by
      rw [show r - ‖y - x‖ - (r - ‖z - x‖) = ‖z - x‖ - ‖y - x‖ by ring, dist_comm,
        dist_eq_norm]
      calc |‖z - x‖ - ‖y - x‖| ≤ ‖(z - x) - (y - x)‖ := abs_norm_sub_norm_le _ _
        _ = ‖z - y‖ := by rw [sub_sub_sub_cancel_right]
    calc |r - ‖y - x‖ - (r - ‖z - x‖)| ≤ dist y z := this
      _ = 1 / (δ * r) * dist y z * (δ * r) := by field_simp
  have := (hu.min_const 1).const_max 0
  convert this using 2 with y
  simp only [ballCutoff, min_comm]

/-- A product `θ g` with `θ ∈ [0, 1]` vanishing outside `S` and `|g| ≤ B` on `S` is
`(L_g + L_θ B)`-Lipschitz. -/
theorem cv_lipschitz_smul {E F : Type*} [PseudoMetricSpace E] [SeminormedAddCommGroup F]
    [NormedSpace ℝ F] {θ : E → ℝ} {g : E → F} {Lθ Lg : NNReal} {B : ℝ} {S : Set E}
    (hθ : LipschitzWith Lθ θ) (hθ0 : ∀ y, 0 ≤ θ y) (hθ1 : ∀ y, θ y ≤ 1)
    (hθS : ∀ y ∉ S, θ y = 0) (hg : LipschitzWith Lg g) (hgS : ∀ y ∈ S, ‖g y‖ ≤ B) (hB : 0 ≤ B) :
    LipschitzWith (Lg + Lθ * B.toNNReal) fun y => θ y • g y := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [dist_eq_norm]
  push_cast
  rw [Real.coe_toNNReal _ hB]
  have hθd : |θ y - θ z| ≤ Lθ * dist y z := by
    rw [← Real.dist_eq]; exact hθ.dist_le_mul y z
  have hgd : ‖g y - g z‖ ≤ Lg * dist y z := by
    rw [← dist_eq_norm]; exact hg.dist_le_mul y z
  by_cases hz : z ∈ S
  · -- θ y g y - θ z g z = θ y (g y - g z) + (θ y - θ z) g z
    have e : θ y • g y - θ z • g z = θ y • (g y - g z) + (θ y - θ z) • g z := by
      rw [smul_sub, sub_smul]; abel
    rw [e]
    calc ‖θ y • (g y - g z) + (θ y - θ z) • g z‖
        ≤ ‖θ y • (g y - g z)‖ + ‖(θ y - θ z) • g z‖ := norm_add_le _ _
      _ = |θ y| * ‖g y - g z‖ + |θ y - θ z| * ‖g z‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 * (Lg * dist y z) + (Lθ * dist y z) * B := by
          gcongr
          · rw [abs_of_nonneg (hθ0 y)]; exact hθ1 y
          · exact hgS z hz
      _ = (Lg + Lθ * B) * dist y z := by ring
  · by_cases hy : y ∈ S
    · have e : θ y • g y - θ z • g z = (θ y - θ z) • g y := by
        rw [hθS z hz, zero_smul, sub_zero, sub_zero]
      rw [e, norm_smul, Real.norm_eq_abs]
      calc |θ y - θ z| * ‖g y‖ ≤ (Lθ * dist y z) * B :=
            mul_le_mul hθd (hgS y hy) (norm_nonneg _) (by positivity)
        _ ≤ (Lg + Lθ * B) * dist y z := by
            have h1 : (0 : ℝ) ≤ Lg * dist y z := mul_nonneg Lg.2 dist_nonneg
            nlinarith
    · rw [hθS y hy, hθS z hz, zero_smul, zero_smul, sub_zero, norm_zero]
      exact mul_nonneg (by positivity) dist_nonneg

end CalculusOfVariations
