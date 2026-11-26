/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ModelLoop

/-!
# Points of the upper and lower side of a model surface

`Fv` maps the two discs of `modelW` to the sphere with holes: the disc in the slot `0` goes to the
upper half and the
disc in the slot `1` to the lower half. Here we compute `Fv` on the sides of the two polygons.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

open scoped OnePoint

theorem modelMirror_mirror (u : EuclideanPlane) : modelMirror (modelMirror u) = u := by
  ext i
  fin_cases i <;> simp [modelMirror]

theorem continuous_modelMirror : Continuous modelMirror := by
  have : modelMirror = fun u : EuclideanPlane => pt (u 0) (-(u 1)) := rfl
  rw [this]
  exact continuous_pt.comp ((by fun_prop : Continuous fun u : EuclideanPlane => u 0).prodMk
    (by fun_prop : Continuous fun u : EuclideanPlane => -(u 1)))

/-- The mirror map as a homeomorphism. -/
noncomputable def mirH : EuclideanPlane ≃ₜ EuclideanPlane where
  toFun := modelMirror
  invFun := modelMirror
  left_inv := modelMirror_mirror
  right_inv := modelMirror_mirror
  continuous_toFun := continuous_modelMirror
  continuous_invFun := continuous_modelMirror

/-- The mirror map on the sphere. -/
noncomputable def mirO : OnePoint EuclideanPlane ≃ₜ OnePoint EuclideanPlane := mirH.onePointCongr

@[simp] theorem mirO_coe (u : EuclideanPlane) : mirO (u : OnePoint EuclideanPlane) =
  (modelMirror u : EuclideanPlane) := rfl

@[simp] theorem mirO_infty : mirO ∞ = ∞ := rfl

theorem mirO_mirO (p : OnePoint EuclideanPlane) : mirO (mirO p) = p := by
  induction p using OnePoint.rec with
  | infty => rfl
  | coe u => simp [modelMirror_mirror]

/-- The sides on the axis are fixed by the mirror. -/
def IsAx (n : ℕ) (p : OnePoint EuclideanPlane) : Prop :=
  p = ∞ ∨ ∃ x, hgt n x = 0 ∧ p = ((pt x 0 : EuclideanPlane) : OnePoint EuclideanPlane)

theorem IsAx.mirO {n : ℕ} {p : OnePoint EuclideanPlane} (h : IsAx n p) : mirO p = p := by
  rcases h with rfl | ⟨x, -, rfl⟩
  · rfl
  · rw [mirO_coe, modelMirror_pt]
    simp

theorem upE_angT (n : ℕ) (s : ℝ) :
    upE n (cis' (angT s)) = ((pt s (hgt n s) : EuclideanPlane) : OnePoint EuclideanPlane) := by
  obtain ⟨h1, h2⟩ := cay_cis s
  rw [upE_ne h1, h2]
  simp

theorem isAx_of_angT {n : ℕ} {s : ℝ} (h : hgt n s = 0) : IsAx n (upE n (cis' (angT s))) := by
  rw [upE_angT, h]
  exact .inr ⟨s, h, rfl⟩

theorem exists_angT {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * Real.pi) : ∃ s, angT s = θ := by
  refine ⟨Real.tan ((θ - Real.pi) / 2), ?_⟩
  unfold angT
  rw [Real.arctan_tan (by linarith) (by linarith)]
  ring

/-- The part of the loop through the point at infinity is on the axis. -/
theorem isAx_top {n : ℕ} {y : ℝ} (h0 : 2 * (n : ℝ) ≤ y) (h1 : y ≤ ((2 * n + 2 : ℕ) : ℝ)) :
    IsAx n (upE n (cis' (angL n y))) := by
  have hm := strictMono_angL n
  have hlo : angT (axS (2 * n)) ≤ angL n y := by
    rw [← angL_le (le_refl (2 * (n : ℝ)))]
    exact hm.monotone h0
  have hhi : angL n y ≤ angT (axS 0) + 2 * Real.pi := by
    rw [← angL_top]
    exact hm.monotone h1
  have hlow := (angT_mem (axS (2 * n))).1
  rcases lt_trichotomy (angL n y) (2 * Real.pi) with h | h | h
  · obtain ⟨s, hs⟩ := exists_angT (hlo.trans_lt' hlow) h
    rw [← hs]
    refine isAx_of_angT (hgt_large ?_)
    have h2 : axS (2 * n) ≤ s := strictMono_angT.le_iff_le.mp (by rw [hs]; exact hlo)
    rw [axS_even] at h2
    exact h2
  · rw [h]
    have : cis' (2 * Real.pi) = 1 := by
      have := cis'_add_two_pi 0
      rw [zero_add, cis'_zero] at this
      exact this
    rw [this, upE_one]
    exact .inl rfl
  · have hup := (angT_mem (axS 0)).2
    obtain ⟨s, hs⟩ := exists_angT (θ := angL n y - 2 * Real.pi) (by linarith) (by linarith)
    have e : cis' (angL n y) = cis' (angT s) := by
      rw [hs, ← cis'_add_two_pi (angL n y - 2 * Real.pi), sub_add_cancel]
    rw [e]
    refine isAx_of_angT (hgt_small ?_)
    have h2 : s ≤ axS 0 := strictMono_angT.le_iff_le.mp (by rw [hs]; linarith)
    have h3 := axS_even 0
    simp only [Nat.cast_zero, mul_zero, zero_sub] at h3
    rw [h3] at h2
    exact h2

theorem isAx_seg {n k : ℕ} (hk : k < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IsAx n (upE n (cis' (angL n (2 * k + t)))) := by
  have h : (2 * (k : ℝ) + t) ≤ 2 * n := by
    have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    linarith [ht.2]
  rw [angL_le h]
  exact isAx_of_angT (hgt_seg (k := k) (by linarith [ht.1]) (by linarith [ht.2]))

/-- The height on the circle `k`. -/
noncomputable def axPsi (t : ℝ) : ℝ := √(1 - axPhi t ^ 2)

theorem axPhi_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : -1 ≤ axPhi t ∧ axPhi t ≤ 1 := by
  rw [← axPhi_zero, ← axPhi_one]
  exact ⟨strictMono_axPhi.monotone ht.1, strictMono_axPhi.monotone ht.2⟩

theorem axPsi_sq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : axPsi t ^ 2 = 1 - axPhi t ^ 2 := by
  obtain ⟨h1, h2⟩ := axPhi_mem ht
  exact Real.sq_sqrt (by nlinarith)

theorem axPsi_neg (t : ℝ) : axPsi (1 - t) = axPsi t := by
  simp [axPsi, axPhi_neg]

/-- The value of the loop on the circle `k`. -/
theorem upE_hole {n k : ℕ} (hk : k < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    upE n (cis' (angL n (2 * k + 1 + t))) =
      ((modelCentre k + pt (axPhi t) (axPsi t) : EuclideanPlane) : OnePoint EuclideanPlane) := by
  have h : (2 * (k : ℝ) + 1 + t) ≤ 2 * n := by
    have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    linarith [ht.2]
  rw [angL_le h, upE_angT, axS_hole]
  obtain ⟨h1, h2⟩ := axPhi_mem ht
  rw [hgt_eq hk (by rw [add_sub_cancel_left, abs_le]; exact ⟨h1, h2⟩), add_sub_cancel_left]
  congr 1
  ext i
  fin_cases i <;> simp [modelCentre_eq, axPsi]

theorem hgt_hole_pos {n k : ℕ} (hk : k < n) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    0 < hgt n (axS (2 * k + 1 + t)) := by
  have hm := strictMono_axPhi
  have h2 : -1 < axPhi t := by rw [← axPhi_zero]; exact hm h0
  have h3 : axPhi t < 1 := by rw [← axPhi_one]; exact hm h1
  rw [axS_hole, hgt_eq hk (by rw [add_sub_cancel_left, abs_le]; exact ⟨h2.le, h3.le⟩),
    add_sub_cancel_left]
  exact Real.sqrt_pos.mpr (by nlinarith)

/-- Each point of the unit circle lies on the loop. -/
theorem exists_loop_param (n : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ y ∈ Icc (0 : ℝ) (2 * n + 2 : ℕ), cis' (angL n y) = z := by
  obtain ⟨θ, hθ, rfl⟩ := exists_cis'_angle (angT (axS 0)) hz
  have hiv := intermediate_value_Icc (a := 0) (b := ((2 * n + 2 : ℕ) : ℝ)) (by positivity)
    (continuous_angL n).continuousOn
  rw [angL_zero, angL_top] at hiv
  obtain ⟨x, hx, rfl⟩ := hiv hθ
  exact ⟨x, hx, rfl⟩

/-- A point of the loop whose image is on the axis lies on a side on the axis. -/
theorem exists_side_of_ax {n : ℕ} {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (2 * n + 2 : ℕ))
    (h : hgt n (axS y) = 0 ∨ 2 * (n : ℝ) ≤ y) :
    (∃ k t, k < n ∧ t ∈ Icc (0 : ℝ) 1 ∧ y = 2 * k + t) ∨
      (2 * (n : ℝ) ≤ y) := by
  by_cases h2 : 2 * (n : ℝ) ≤ y
  · exact .inr h2
  have h' : hgt n (axS y) = 0 := h.resolve_right h2
  push Not at h2
  left
  set j := ⌊y⌋₊ with hj
  have h3 : (j : ℝ) ≤ y := Nat.floor_le hy.1
  have h4 : y < j + 1 := Nat.lt_floor_add_one y
  have hjn : j < 2 * n := by
    have : (j : ℝ) < 2 * n := by linarith
    exact_mod_cast this
  rcases Nat.even_or_odd' j with ⟨k, hk | hk⟩
  · refine ⟨k, y - j, by omega, ⟨by linarith, by linarith⟩, ?_⟩
    rw [hk]
    push_cast
    ring
  · have hk' : (j : ℝ) = 2 * k + 1 := by rw [hk]; push_cast; ring
    by_cases h5 : y = j
    · refine ⟨k, 1, by omega, ⟨by norm_num, le_rfl⟩, ?_⟩
      rw [h5, hk']
    · exfalso
      have h6 : 0 < y - j := sub_pos.mpr (lt_of_le_of_ne h3 (Ne.symm h5))
      have h7 := hgt_hole_pos (n := n) (k := k) (by omega) h6 (by linarith)
      rw [show 2 * (k : ℝ) + 1 + (y - j) = y by rw [hk']; ring, h'] at h7
      exact lt_irrefl _ h7

end GraphMinor.Surface
