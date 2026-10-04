/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Extension.Cutoff
public import LeanPool.EllipticPDE.Extension.Reflect
public import LeanPool.EllipticPDE.Embedding.GagliardoNirenberg


/-!
# Half space and its interface

The extension of a Sobolev class across a flat boundary is by reflection, and what has to be
proved is that the reflected class has a weak gradient across the interface. The identity of a
weak gradient on the open half space applies only to test functions supported strictly inside
it, so the test function is first multiplied by `slabCut j ε` and the slab is then let shrink.

Two terms survive the product rule. The one with the cutoff's own derivative vanishes
identically in the directions along the interface, since the cutoff depends on the `j`-th
coordinate alone. In the remaining direction it is the boundary term, and it vanishes in the
limit whenever the test function vanishes on the interface, which is exactly what the odd part
of a reflection does.

## Main declarations

* `EllipticPdes.Extension.halfSpace`: the open half space `{xⱼ > 0}`.
* `EllipticPdes.Extension.volume_interface`: the interface is null.
* `EllipticPdes.Extension.integral_partialD_of_ne`: no boundary term along the interface.
* `EllipticPdes.Extension.integral_partialD_of_eq`: none in the remaining direction either,
  for a test function vanishing on the interface.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4 Theorem 1.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)
open EllipticPdes.Embedding (HasWeakGradOn partialD_mul)

variable {d : ℕ}

/-- **Open half space above the interface `{xⱼ = 0}`.** -/
def halfSpace (j : Fin d) : Set (EuclideanSpace ℝ (Fin d)) := {x | 0 < x j}

theorem isOpen_halfSpace (j : Fin d) : IsOpen (halfSpace j) :=
  isOpen_lt continuous_const (EuclideanSpace.proj j).continuous

theorem measurableSet_halfSpace (j : Fin d) : MeasurableSet (halfSpace j) :=
  (isOpen_halfSpace j).measurableSet

/-- **Nullity of the interface**, being a proper linear subspace. -/
theorem volume_interface (j : Fin d) :
    volume {x : EuclideanSpace ℝ (Fin d) | x j = 0} = 0 := by
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
    LinearMap.ker ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) with hK
  have hset : {x : EuclideanSpace ℝ (Fin d) | x j = 0} = (K : Set (EuclideanSpace ℝ (Fin d))) := by
    ext x
    simp [hK, LinearMap.mem_ker]
  have hne : K ≠ ⊤ := by
    intro h
    have hmem : EuclideanSpace.single j (1 : ℝ) ∈ K := by rw [h]; exact Submodule.mem_top
    rw [hK, LinearMap.mem_ker] at hmem
    simp at hmem
  rw [hset]
  exact Measure.addHaar_submodule volume K hne

/-- The reflection sends the half space onto the other side. -/
theorem preimage_reflectLI_halfSpace (j : Fin d) :
    reflectLI j ⁻¹' halfSpace j = {x : EuclideanSpace ℝ (Fin d) | x j < 0} := by
  ext x
  have h : reflectLI j x j = -(x j) := by
    rw [reflectLI_apply, reflectSign, ite_eq_left rfl]; ring
  simp only [Set.mem_preimage, halfSpace, Set.mem_ofPred_eq, h, neg_pos]

/-! ### No boundary term -/

variable {j : Fin d} {u : EuclideanSpace ℝ (Fin d) → ℝ}
  {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- **`C¹` class vanishing on the interface is bounded by its gradient and the distance to
it.** This is what makes the boundary term vanish in the limit. -/
theorem abs_le_of_vanishes_on_interface (hψ : Differentiable ℝ ψ) {M : ℝ}
    (hM : ∀ z, ‖fderiv ℝ ψ z‖ ≤ M) (hzero : ∀ z : EuclideanSpace ℝ (Fin d), z j = 0 → ψ z = 0)
    (x : EuclideanSpace ℝ (Fin d)) (hx : 0 ≤ x j) : |ψ x| ≤ M * x j := by
  set x0 : EuclideanSpace ℝ (Fin d) := x - (x j) • EuclideanSpace.single j (1 : ℝ) with hx0
  have hx0j : x0 j = 0 := by
    rw [hx0]
    simp [PiLp.sub_apply, PiLp.smul_apply]
  have hdiff : x - x0 = (x j) • EuclideanSpace.single j (1 : ℝ) := by
    rw [hx0]; abel
  have hnorm : ‖x - x0‖ = x j := by
    rw [hdiff, norm_smul, PiLp.norm_single]
    simp [abs_of_nonneg hx]
  have hconv : Convex ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) := convex_univ
  have hmv := hconv.norm_image_sub_le_of_norm_fderiv_le
    (f := ψ) (fun z _ => hψ z) (fun z _ => hM z) (Set.mem_univ x0) (Set.mem_univ x)
  rw [hzero x0 hx0j, sub_zero, hnorm] at hmv
  simpa [Real.norm_eq_abs] using hmv

/-- The identity at each `ε`: multiplied by the cutoff, the test function is supported strictly
inside the half space, where the weak gradient applies. -/
private theorem cutoff_identity (hwg : HasWeakGradOn (halfSpace j) u g)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψcs : HasCompactSupport ψ) {ε : ℝ} (hε : 0 < ε) (k : Fin d) :
    ∫ x in halfSpace j, u x * (partialD k (slabCut j ε) x * ψ x
        + slabCut j ε x * partialD k ψ x)
      = - ∫ x in halfSpace j, g k x * (slabCut j ε x * ψ x) := by
  have h := hwg (fun x => slabCut j ε x * ψ x) ((contDiff_slabCut j ε).mul hψ)
    (hψcs.mul_left) (tsupport_mul_slabCut_subset hε ψ) k
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change u x * (partialD k (slabCut j ε) x * ψ x + slabCut j ε x * partialD k ψ x)
      = u x * partialD k (fun y => slabCut j ε y * ψ y) x
  rw [partialD_mul k ((contDiff_slabCut j ε).differentiable (by simp) x)
    (hψ.differentiable (by simp) x)]

/-- **Weak-gradient identity against a test function that need not vanish near the
interface**, given that the boundary term it leaves goes to zero. -/
private theorem integral_partialD_aux {k : Fin d} (hu : IntegrableOn u (halfSpace j) volume)
    (hg : IntegrableOn (g k) (halfSpace j) volume) (hwg : HasWeakGradOn (halfSpace j) u g)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψcs : HasCompactSupport ψ)
    (hbdry : Tendsto (fun n : ℕ => ∫ x in halfSpace j,
        u x * (partialD k (slabCut j (((n : ℝ) + 1)⁻¹)) x * ψ x)) atTop (𝓝 0)) :
    ∫ x in halfSpace j, u x * partialD k ψ x = - ∫ x in halfSpace j, g k x * ψ x := by
  classical
  set ε : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹ with hεdef
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  have hψc : Continuous ψ := hψ.continuous
  have hdψc : Continuous (partialD k ψ) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨M, hM⟩ := hψcs.exists_bound_of_continuous hψc
  obtain ⟨N, hN⟩ :=
    (hψcs.fderiv ℝ).comp_left (g := fun T : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ =>
      T (EuclideanSpace.single k (1 : ℝ))) (by simp) |>.exists_bound_of_continuous hdψc
  -- The cutoff is eventually `1` at each interior point.
  have hone : ∀ x ∈ halfSpace j, ∀ᶠ n : ℕ in atTop, slabCut j (ε n) x = 1 := by
    intro x hx
    have hxj : 0 < x j := hx
    obtain ⟨m, hm⟩ := exists_nat_gt (2 / x j)
    filter_upwards [eventually_ge_atTop m] with n hn
    refine slabCut_eq_one (hε n) ?_
    have hmn : (2 : ℝ) / x j < (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hxj] at hmn
    change 2 * ((n : ℝ) + 1)⁻¹ ≤ x j
    rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hn1]
    linarith
  -- The two dominated limits.
  have hlim1 : Tendsto (fun n : ℕ => ∫ x in halfSpace j,
      u x * (slabCut j (ε n) x * partialD k ψ x)) atTop
      (𝓝 (∫ x in halfSpace j, u x * partialD k ψ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => N * ‖u x‖) ?_ ?_ ?_ ?_
    · exact fun n =>
        hu.1.mul (((contDiff_slabCut j (ε n)).continuous.mul hdψc)).aestronglyMeasurable
    · exact hu.norm.const_mul N
    · intro n
      filter_upwards with x
      rw [norm_mul, norm_mul, mul_comm]
      refine mul_le_mul ?_ le_rfl (norm_nonneg _) (le_trans (norm_nonneg _) (hN 0))
      calc ‖slabCut j (ε n) x‖ * ‖partialD k ψ x‖
          ≤ 1 * N := by
            refine mul_le_mul ?_ (hN x) (norm_nonneg _) zero_le_one
            rw [Real.norm_eq_abs, abs_of_nonneg (slabCut_nonneg j (ε n) x)]
            exact slabCut_le_one j (ε n) x
        _ = N := one_mul N
    · rw [ae_restrict_iff' (measurableSet_halfSpace j)]
      filter_upwards with x hx
      have : Tendsto (fun n : ℕ => slabCut j (ε n) x) atTop (𝓝 1) :=
        Tendsto.congr' (by filter_upwards [hone x hx] with n hn using hn.symm) tendsto_const_nhds
      simpa using ((this.mul tendsto_const_nhds).const_mul (u x))
  have hlim2 : Tendsto (fun n : ℕ => ∫ x in halfSpace j,
      g k x * (slabCut j (ε n) x * ψ x)) atTop (𝓝 (∫ x in halfSpace j, g k x * ψ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => M * ‖g k x‖) ?_ ?_ ?_ ?_
    · exact fun n =>
        hg.1.mul (((contDiff_slabCut j (ε n)).continuous.mul hψc)).aestronglyMeasurable
    · exact hg.norm.const_mul M
    · intro n
      filter_upwards with x
      rw [norm_mul, norm_mul, mul_comm]
      refine mul_le_mul ?_ le_rfl (norm_nonneg _) (le_trans (norm_nonneg _) (hM 0))
      calc ‖slabCut j (ε n) x‖ * ‖ψ x‖
          ≤ 1 * M := by
            refine mul_le_mul ?_ (hM x) (norm_nonneg _) zero_le_one
            rw [Real.norm_eq_abs, abs_of_nonneg (slabCut_nonneg j (ε n) x)]
            exact slabCut_le_one j (ε n) x
        _ = M := one_mul M
    · rw [ae_restrict_iff' (measurableSet_halfSpace j)]
      filter_upwards with x hx
      have : Tendsto (fun n : ℕ => slabCut j (ε n) x) atTop (𝓝 1) :=
        Tendsto.congr' (by filter_upwards [hone x hx] with n hn using hn.symm) tendsto_const_nhds
      simpa using ((this.mul tendsto_const_nhds).const_mul (g k x))
  -- Each `ε` gives the identity, and the limit gives the statement.
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_stepProfile
  have hsplit : ∀ n : ℕ, (∫ x in halfSpace j, u x * (partialD k (slabCut j (ε n)) x * ψ x))
      + (∫ x in halfSpace j, u x * (slabCut j (ε n) x * partialD k ψ x))
      = - ∫ x in halfSpace j, g k x * (slabCut j (ε n) x * ψ x) := by
    intro n
    have hb1 : Integrable (fun x => u x * (partialD k (slabCut j (ε n)) x * ψ x))
        (volume.restrict (halfSpace j)) := by
      refine hu.mul_bdd (c := (C / ε n) * M) ?_ ?_
      · exact ((((contDiff_slabCut j (ε n)).continuous_fderiv
          (by simp)).clm_apply continuous_const).mul hψc).aestronglyMeasurable
      · filter_upwards with x
        rw [norm_mul]
        refine mul_le_mul ?_ (hM x) (norm_nonneg _) (by positivity)
        rw [Real.norm_eq_abs]
        exact norm_partialD_slabCut_le (hε n) hC k x
    have hb2 : Integrable (fun x => u x * (slabCut j (ε n) x * partialD k ψ x))
        (volume.restrict (halfSpace j)) := by
      refine hu.mul_bdd (c := 1 * N) ?_ ?_
      · exact ((contDiff_slabCut j (ε n)).continuous.mul hdψc).aestronglyMeasurable
      · filter_upwards with x
        rw [norm_mul]
        refine mul_le_mul ?_ (hN x) (norm_nonneg _) zero_le_one
        rw [Real.norm_eq_abs, abs_of_nonneg (slabCut_nonneg j (ε n) x)]
        exact slabCut_le_one j (ε n) x
    rw [← integral_add hb1 hb2, ← cutoff_identity hwg hψ hψcs (hε n) k]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hL : Tendsto (fun n : ℕ =>
      (∫ x in halfSpace j, u x * (partialD k (slabCut j (ε n)) x * ψ x))
        + (∫ x in halfSpace j, u x * (slabCut j (ε n) x * partialD k ψ x))) atTop
      (𝓝 (∫ x in halfSpace j, u x * partialD k ψ x)) := by
    simpa using hbdry.add hlim1
  exact tendsto_nhds_unique (hL.congr fun n => hsplit n) hlim2.neg

/-- **No boundary term along the interface.** The cutoff depends on the `j`-th coordinate
alone, so in every other direction its derivative vanishes and the identity passes to a test
function that need not vanish near the interface. -/
theorem integral_partialD_of_ne {k : Fin d} (hk : k ≠ j)
    (hu : IntegrableOn u (halfSpace j) volume) (hg : IntegrableOn (g k) (halfSpace j) volume)
    (hwg : HasWeakGradOn (halfSpace j) u g) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcs : HasCompactSupport ψ) :
    ∫ x in halfSpace j, u x * partialD k ψ x = - ∫ x in halfSpace j, g k x * ψ x := by
  refine integral_partialD_aux hu hg hwg hψ hψcs ?_
  have hzero : ∀ n : ℕ,
      (∫ x in halfSpace j, u x * (partialD k (slabCut j (((n : ℝ) + 1)⁻¹)) x * ψ x)) = 0 := by
    intro n
    have hpt : ∀ x : EuclideanSpace ℝ (Fin d),
        u x * (partialD k (slabCut j (((n : ℝ) + 1)⁻¹)) x * ψ x) = 0 := by
      intro x
      rw [partialD_slabCut_of_ne (by positivity) hk x, zero_mul, mul_zero]
    simp only [hpt, integral_zero]
  simp only [hzero]
  exact tendsto_const_nhds

/-- **No boundary term in the remaining direction either**, for a test function vanishing on the
interface. Where the cutoff's derivative is `C/ε` the test function is at most `2ε` times its
gradient, so the product is bounded uniformly and supported in a slab that shrinks to nothing. -/
theorem integral_partialD_of_eq (hu : IntegrableOn u (halfSpace j) volume)
    (hg : IntegrableOn (g j) (halfSpace j) volume) (hwg : HasWeakGradOn (halfSpace j) u g)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψcs : HasCompactSupport ψ)
    (hzero : ∀ z : EuclideanSpace ℝ (Fin d), z j = 0 → ψ z = 0) :
    ∫ x in halfSpace j, u x * partialD j ψ x = - ∫ x in halfSpace j, g j x * ψ x := by
  refine integral_partialD_aux hu hg hwg hψ hψcs ?_
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_stepProfile
  obtain ⟨M, hM⟩ := (hψcs.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv (by simp))
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hε : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := fun n => by positivity
  rw [show (0 : ℝ) = ∫ _x in halfSpace j, (0 : ℝ) by simp]
  refine tendsto_integral_of_dominated_convergence (fun x => 2 * C * M * ‖u x‖) ?_ ?_ ?_ ?_
  · intro n
    exact hu.1.mul (((((contDiff_slabCut j (((n : ℝ) + 1)⁻¹)).continuous_fderiv
      (by simp)).clm_apply continuous_const).mul hψ.continuous).aestronglyMeasurable)
  · exact hu.norm.const_mul (2 * C * M)
  · intro n
    rw [ae_restrict_iff' (measurableSet_halfSpace j)]
    filter_upwards with x hx
    have hxj : 0 < x j := hx
    rw [norm_mul, norm_mul, mul_comm (2 * C * M) ‖u x‖]
    refine mul_le_mul le_rfl ?_ (by positivity) (norm_nonneg _)
    by_cases hcase : 2 * ((n : ℝ) + 1)⁻¹ < x j
    · rw [partialD_slabCut_eq_zero_of_gt (hε n) j hcase]
      simp only [norm_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (by norm_num) hC0) hM0
    · have hcase' : x j ≤ 2 * ((n : ℝ) + 1)⁻¹ := not_lt.mp hcase
      have hψx : |ψ x| ≤ M * x j :=
        abs_le_of_vanishes_on_interface (hψ.differentiable (by simp)) hM hzero x hxj.le
      have h1 : ‖partialD j (slabCut j (((n : ℝ) + 1)⁻¹)) x‖ ≤ C / ((n : ℝ) + 1)⁻¹ := by
        rw [Real.norm_eq_abs]
        exact norm_partialD_slabCut_le (hε n) hC j x
      have h2 : ‖ψ x‖ ≤ M * (2 * ((n : ℝ) + 1)⁻¹) := by
        rw [Real.norm_eq_abs]
        exact le_trans hψx (by nlinarith [hM0, hcase'])
      calc ‖partialD j (slabCut j (((n : ℝ) + 1)⁻¹)) x‖ * ‖ψ x‖
          ≤ (C / ((n : ℝ) + 1)⁻¹) * (M * (2 * ((n : ℝ) + 1)⁻¹)) := by
            refine mul_le_mul h1 h2 (norm_nonneg _) ?_
            positivity
        _ = 2 * C * M := by field_simp
  · rw [ae_restrict_iff' (measurableSet_halfSpace j)]
    filter_upwards with x hx
    have hxj : 0 < x j := hx
    obtain ⟨m, hm⟩ := exists_nat_gt (2 / x j)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hmn : (2 : ℝ) / x j < (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ hxj] at hmn
    have hgt : 2 * ((n : ℝ) + 1)⁻¹ < x j := by
      rw [inv_eq_one_div, mul_one_div, div_lt_iff₀ hn1]
      linarith
    rw [partialD_slabCut_eq_zero_of_gt (hε n) j hgt, zero_mul, mul_zero]

end EllipticPdes.Extension
