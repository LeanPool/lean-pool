/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.DataSeparability

/-!
# DataApproximation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# A countable subclass approximating every normalized forcing field uniformly

The normalized forcing fields of Section 5.1 are `1/2`-Hölder on the *open* cube
and unconstrained outside it, so they are not points of a metric space of their
own.  Dilating the closed cube towards its centre by a factor `1 - δ` maps it
into the open cube, so composing a forcing field with that dilation produces a
field that *is* continuous on the closed cube, is again `1/2`-Hölder with the
same constant — the dilation is a contraction — and is uniformly close to the
original on the cube, by the Hölder bound and the diameter of the cube.

Second countability of `C(closedCubeAt y n, Vec d)` then supplies a countable
subclass of the dilated fields dense in the supremum distance, and hence a
single countable family that approximates every normalized forcing field
uniformly on the cube.  This is the family the suprema of the localized
quantities are realized on.

## Main definitions

* `shrinkTo y delta` — the dilation of `ℝ^d` towards `y` by the factor
  `1 - delta`.

## Main results

* `shrinkTo_mem_cubeSetAt`, `norm_sub_shrinkTo_le` — the dilation maps the
  closed cube into the open cube and moves points by at most `delta · 3^n / 2`.
* `exists_continuousMap_holder_close` — one continuous field on the closed cube
  with the same Hölder constant and prescribed uniform closeness.
* `exists_countable_holder_approx`, `exists_countable_normalizedForceAt_approx` —
  the countable family.

## References

* ABK26, the localized error and regularity quantities of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. The dilation towards the centre -/

/-- **The dilation of `ℝ^d` towards `y` by the factor `1 - delta`.** -/
def shrinkTo (y : Vec d) (delta : ℝ) (x : Vec d) : Vec d :=
  fun i => y i + (1 - delta) * (x i - y i)

theorem shrinkTo_apply (y : Vec d) (delta : ℝ) (x : Vec d) (i : Fin d) :
    shrinkTo y delta x i = y i + (1 - delta) * (x i - y i) := rfl

theorem continuous_shrinkTo (y : Vec d) (delta : ℝ) : Continuous (shrinkTo y delta) :=
  continuous_pi fun i =>
    continuous_const.add (continuous_const.mul ((continuous_apply i).sub continuous_const))

theorem shrinkTo_sub (y : Vec d) (delta : ℝ) (x z : Vec d) :
    shrinkTo y delta x - shrinkTo y delta z = (1 - delta) • (x - z) := by
  funext i
  show shrinkTo y delta x i - shrinkTo y delta z i = (1 - delta) * (x i - z i)
  simp only [shrinkTo]
  ring

/-- **The dilation maps the closed cube into the open cube.** -/
theorem shrinkTo_mem_cubeSetAt {y : Vec d} {n : ℤ} {delta : ℝ} (h0 : 0 < delta)
    (h1 : delta ≤ 1) {x : Vec d} (hx : x ∈ closedCubeAt y n) :
    shrinkTo y delta x ∈ cubeSetAt y n := by
  rw [mem_cubeSetAt_iff_forall_coord]
  intro i
  have hLpos : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by positivity
  have hfac : (0 : ℝ) ≤ 1 - delta := by linarith
  have hcoord : shrinkTo y delta x i - y i = (1 - delta) * (x i - y i) := by
    rw [shrinkTo_apply]
    ring
  have habs : |(1 - delta) * (x i - y i)| < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
    rw [abs_mul, abs_of_nonneg hfac]
    have hstep : (1 - delta) * |x i - y i| ≤ (1 - delta) * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left (hx i) hfac
    have hpos : (0 : ℝ) < delta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by positivity
    have heq : (1 - delta) * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) =
        (1 / 2 : ℝ) * (3 : ℝ) ^ n - delta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by ring
    rw [heq] at hstep
    linarith
  rw [hcoord]
  have hlt := abs_lt.1 habs
  constructor <;> linarith [hlt.1, hlt.2]

/-- **The dilation moves a point of the closed cube by at most `delta · 3^n / 2`.** -/
theorem norm_sub_shrinkTo_le {y : Vec d} {n : ℤ} {delta : ℝ} (h0 : 0 ≤ delta)
    {x : Vec d} (hx : x ∈ closedCubeAt y n) :
    ‖x - shrinkTo y delta x‖ ≤ delta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have hcoord : (x - shrinkTo y delta x) i = delta * (x i - y i) := by
    show x i - shrinkTo y delta x i = delta * (x i - y i)
    rw [shrinkTo_apply]
    ring
  rw [Real.norm_eq_abs, hcoord, abs_mul, abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left (hx i) h0

/-! ## 2. The dilated field is a continuous field on the closed cube -/

theorem exists_extendVec_shrinkTo (y : Vec d) (n : ℤ) {delta : ℝ} (h0 : 0 < delta)
    (h1 : delta ≤ 1) {g : Vec d → Vec d} (hg : ContinuousOn g (cubeSetAt y n)) :
    ∃ G : C(closedCubeAt y n, Vec d),
      ∀ x ∈ closedCubeAt y n, extendVec y n G x = g (shrinkTo y delta x) := by
  refine ⟨⟨fun p => g (shrinkTo y delta (p : Vec d)), ?_⟩, ?_⟩
  · exact hg.comp_continuous
      ((continuous_shrinkTo y delta).comp continuous_subtype_val)
      fun p => shrinkTo_mem_cubeSetAt h0 h1 p.2
  · intro x hx
    show g (shrinkTo y delta (clampTo y n x)) = g (shrinkTo y delta x)
    rw [clampTo_eq_self hx]

/-! ## 3. One uniformly close field with the same Hölder constant -/

/-- **Every `1/2`-Hölder forcing field is uniformly approximated on the cube by a
continuous field on the closed cube with the same Hölder constant.** -/
theorem exists_continuousMap_holder_close (y : Vec d) (n : ℤ) {K : ℝ} (hK : 0 ≤ K)
    {g : Vec d → Vec d} (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) K g)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ G : C(closedCubeAt y n, Vec d),
      HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) K (extendVec y n G) ∧
        ∀ x ∈ cubeSetAt y n, ‖g x - extendVec y n G x‖ ≤ eta := by
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  have hLpos : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by positivity
  set delta : ℝ :=
    min 1 ((eta / (K + 1)) ^ (2 : ℕ) / ((1 / 2 : ℝ) * (3 : ℝ) ^ n)) with hdeltadef
  have hd0 : 0 < delta := lt_min one_pos (by positivity)
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hdL : delta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) ≤ (eta / (K + 1)) ^ (2 : ℕ) := by
    have hmin := min_le_right (1 : ℝ)
      ((eta / (K + 1)) ^ (2 : ℕ) / ((1 / 2 : ℝ) * (3 : ℝ) ^ n))
    calc delta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n)
        ≤ ((eta / (K + 1)) ^ (2 : ℕ) / ((1 / 2 : ℝ) * (3 : ℝ) ^ n)) *
            ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := mul_le_mul_of_nonneg_right hmin hLpos.le
      _ = (eta / (K + 1)) ^ (2 : ℕ) := by field_simp
  have hgcont : ContinuousOn g (cubeSetAt y n) :=
    Section4.Provider.Schauder.continuousOn_of_holderSeminormBoundOn hK (by norm_num) hg
  obtain ⟨G, hG⟩ := exists_extendVec_shrinkTo y n hd0 hd1 hgcont
  refine ⟨G, ?_, ?_⟩
  · intro p hp q hq
    have hpK : p ∈ closedCubeAt y n := cubeSetAt_subset_closedCubeAt y n hp
    have hqK : q ∈ closedCubeAt y n := cubeSetAt_subset_closedCubeAt y n hq
    rw [hG p hpK, hG q hqK]
    have hbd := hg (shrinkTo y delta p) (shrinkTo_mem_cubeSetAt hd0 hd1 hpK)
      (shrinkTo y delta q) (shrinkTo_mem_cubeSetAt hd0 hd1 hqK)
    have hnorm : ‖shrinkTo y delta p - shrinkTo y delta q‖ ≤ ‖p - q‖ := by
      have hfac : (0 : ℝ) ≤ 1 - delta := by linarith
      rw [shrinkTo_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hfac]
      calc (1 - delta) * ‖p - q‖ ≤ 1 * ‖p - q‖ :=
            mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        _ = ‖p - q‖ := one_mul _
    have hmono : ‖shrinkTo y delta p - shrinkTo y delta q‖ ^ (1 / 2 : ℝ) ≤
        ‖p - q‖ ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (norm_nonneg _) hnorm (by norm_num)
    exact hbd.trans (mul_le_mul_of_nonneg_left hmono hK)
  · intro x hx
    have hxK : x ∈ closedCubeAt y n := cubeSetAt_subset_closedCubeAt y n hx
    rw [hG x hxK]
    have hdist := norm_sub_shrinkTo_le hd0.le hxK
    have hsqrt : ‖x - shrinkTo y delta x‖ ^ (1 / 2 : ℝ) ≤ eta / (K + 1) := by
      have h1 : ‖x - shrinkTo y delta x‖ ^ (1 / 2 : ℝ) ≤
          (delta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n)) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) hdist (by norm_num)
      have h2 : (delta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n)) ^ (1 / 2 : ℝ) ≤
          ((eta / (K + 1)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hdL (by norm_num)
      have h3 : ((eta / (K + 1)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = eta / (K + 1) := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
      linarith [h1, h2, h3]
    have hbd := hg x hx (shrinkTo y delta x) (shrinkTo_mem_cubeSetAt hd0 hd1 hxK)
    have hstep : K * ‖x - shrinkTo y delta x‖ ^ (1 / 2 : ℝ) ≤ K * (eta / (K + 1)) :=
      mul_le_mul_of_nonneg_left hsqrt hK
    have hfrac : K * (eta / (K + 1)) ≤ eta := by
      have hle1 : K / (K + 1) ≤ 1 := (div_le_one hK1).2 (by linarith)
      calc K * (eta / (K + 1)) = eta * (K / (K + 1)) := by ring
        _ ≤ eta * 1 := mul_le_mul_of_nonneg_left hle1 heta.le
        _ = eta := mul_one _
    linarith [hbd, hstep, hfrac]

/-! ## 4. The countable family -/

/-- **A single countable family of continuous fields on the closed cube
approximates every `1/2`-Hölder field with constant `K` uniformly on the cube,
and every member of it has the same Hölder constant.** -/
theorem exists_countable_holder_approx (y : Vec d) (n : ℤ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ t : Set C(closedCubeAt y n, Vec d), t.Countable ∧
      (∀ G ∈ t, HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) K (extendVec y n G)) ∧
        ∀ g : Vec d → Vec d, HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) K g →
          ∀ eta : ℝ, 0 < eta →
            ∃ G ∈ t, ∀ x ∈ cubeSetAt y n, ‖g x - extendVec y n G x‖ ≤ eta := by
  obtain ⟨t, hcount, hsub, hdense⟩ := exists_countable_subset_dense y n
    {G : C(closedCubeAt y n, Vec d) |
      HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) K (extendVec y n G)}
  refine ⟨t, hcount, fun G hG => hsub hG, fun g hg eta heta => ?_⟩
  obtain ⟨F, hF, hFclose⟩ := exists_continuousMap_holder_close y n hK hg (half_pos heta)
  obtain ⟨G, hGt, hGdist⟩ := hdense F hF (eta / 2) (half_pos heta)
  refine ⟨G, hGt, fun x hx => ?_⟩
  have hxK : x ∈ closedCubeAt y n := cubeSetAt_subset_closedCubeAt y n hx
  have hstep : ‖extendVec y n F x - extendVec y n G x‖ ≤ eta / 2 := by
    rw [extendVec_apply_of_mem F hxK, extendVec_apply_of_mem G hxK]
    have hcoe : F ⟨x, hxK⟩ - G ⟨x, hxK⟩ = (F - G) ⟨x, hxK⟩ := rfl
    rw [hcoe]
    refine le_trans ((F - G).norm_coe_le_norm _) ?_
    rw [← dist_eq_norm, dist_comm]
    exact hGdist.le
  have htri : ‖g x - extendVec y n G x‖ ≤
      ‖g x - extendVec y n F x‖ + ‖extendVec y n F x - extendVec y n G x‖ := by
    simpa [dist_eq_norm] using
      dist_triangle (g x) (extendVec y n F x) (extendVec y n G x)
  have hFx := hFclose x hx
  linarith [htri, hFx, hstep]

/-- **The countable family in the form the normalized forcing class uses.** -/
theorem exists_countable_normalizedForceAt_approx (y : Vec d) (n : ℤ) :
    ∃ t : Set C(closedCubeAt y n, Vec d), t.Countable ∧
      (∀ G ∈ t, NormalizedForceAt y n (extendVec y n G)) ∧
        ∀ g : Vec d → Vec d, NormalizedForceAt y n g →
          ∀ eta : ℝ, 0 < eta →
            ∃ G ∈ t, ∀ x ∈ cubeSetAt y n, ‖g x - extendVec y n G x‖ ≤ eta :=
  exists_countable_holder_approx y n
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-(n : ℝ) / 2))

end

end Algsuperdiff.Section5.Support
