/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
Finite-dimensional Hilbert mechanism for C145, Theorem E.
The domain norm is an inner-product norm; final tensor/grid instantiation must
use the source Frobenius/Euclidean norms, not default function sup norms.
-/

@[expose] public section

namespace C145DRE8HilbertStability

open scoped InnerProductSpace

variable {E Y Z : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The actual orthogonal decomposition, including projection norm contraction. -/
theorem orthogonal_decomposition (K : Submodule ℝ E) (x : E) :
    ∃ k r : E, k ∈ K ∧ r ∈ Kᗮ ∧ x = k + r ∧
      inner ℝ k r = 0 ∧ ‖k‖ ≤ ‖x‖ := by
  refine ⟨K.starProjection x, x - K.starProjection x,
    K.starProjection_apply_mem x, K.sub_starProjection_mem_orthogonal x,
    ?_, ?_, K.norm_starProjection_apply_le x⟩
  · abel
  · exact Submodule.inner_right_of_mem_orthogonal
      (K.starProjection_apply_mem x) (K.sub_starProjection_mem_orthogonal x)

omit [FiniteDimensional ℝ E] in
/-- Kernel equality proves injectivity on the orthogonal complement. -/
theorem complement_injective (M : E →ₗ[ℝ] Y) (K : Submodule ℝ E)
    (hker : LinearMap.ker M = K) :
    Function.Injective (M.domRestrict Kᗮ) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro u hu
  have hMu : M (u : E) = 0 := hu
  have hKu : (u : E) ∈ K := by
    simpa only [hker] using (show (u : E) ∈ LinearMap.ker M from hMu)
  have hu0 : (u : E) = 0 := by
    apply (Submodule.mem_bot ℝ).mp
    rw [← K.inf_orthogonal_eq_bot]
    exact ⟨hKu, u.property⟩
  exact (Submodule.mem_bot ℝ).mpr (Subtype.ext hu0)

/-- On a nonzero complement the genuine least unit-vector gain is attained
and strictly positive. The concluding bound is valid for every residual. -/
theorem exists_attained_positive_complement_gain
    (M : E →ₗ[ℝ] Y) (K : Submodule ℝ E)
    (hker : LinearMap.ker M = K) [Nontrivial Kᗮ] :
    ∃ (σ : ℝ) (u : Kᗮ), 0 < σ ∧ ‖u‖ = 1 ∧ ‖M (u : E)‖ = σ ∧
      (∀ v : Kᗮ, ‖v‖ = 1 → σ ≤ ‖M (v : E)‖) ∧
      (∀ r : E, r ∈ Kᗮ → σ * ‖r‖ ≤ ‖M r‖) := by
  have hne : (Metric.sphere (0 : Kᗮ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  have hcont : Continuous (fun u : Kᗮ => ‖M (u : E)‖) :=
    (M.continuous_of_finiteDimensional.comp continuous_subtype_val).norm
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : Kᗮ) 1).exists_isMinOn hne
    hcont.continuousOn
  have hun : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu
  have hMu : M (u : E) ≠ 0 := by
    intro heq
    have hu0 : u = 0 := (complement_injective M K hker) (by simpa using heq)
    simp [hu0] at hun
  refine ⟨‖M (u : E)‖, u, norm_pos_iff.mpr hMu, hun, rfl, ?_, ?_⟩
  · intro v hv
    exact hmin (by simpa only [Metric.mem_sphere, dist_zero_right] using hv)
  · intro r hr
    by_cases hr0 : r = 0
    · simp [hr0]
    have hn : 0 < ‖r‖ := norm_pos_iff.mpr hr0
    let v : Kᗮ := ⟨‖r‖⁻¹ • r, Kᗮ.smul_mem _ hr⟩
    have hv : ‖v‖ = 1 := by
      change ‖‖r‖⁻¹ • r‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
        inv_mul_cancel₀ hn.ne']
    have hm := hmin (show v ∈ Metric.sphere (0 : Kᗮ) 1 by
      simpa only [Metric.mem_sphere, dist_zero_right] using hv)
    change ‖M (u : E)‖ ≤ ‖M (‖r‖⁻¹ • r)‖ at hm
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)] at hm
    have hs := mul_le_mul_of_nonneg_left hm hn.le
    calc
      ‖M (u : E)‖ * ‖r‖ = ‖r‖ * ‖M (u : E)‖ := mul_comm _ _
      _ ≤ ‖r‖ * (‖r‖⁻¹ * ‖M r‖) := hs
      _ = ‖M r‖ := by rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]

omit [FiniteDimensional ℝ E] in
/-- If the complement is zero, σ=1 is a valid positive bound. This is a
vacuous lower-gain convention, not a minimum over an empty unit sphere. -/
theorem zero_complement_gain (M : E →ₗ[ℝ] Y) (K : Submodule ℝ E)
    [Subsingleton Kᗮ] :
    0 < (1 : ℝ) ∧ ∀ r : E, r ∈ Kᗮ → 1 * ‖r‖ ≤ ‖M r‖ := by
  refine ⟨zero_lt_one, ?_⟩
  intro r hr
  have hr0 : r = 0 := congrArg Subtype.val (Subsingleton.elim (⟨r, hr⟩ : Kᗮ) 0)
  simp [hr0]

/-- Every finite-dimensional operator has a positive lower gain off its kernel,
with the preceding σ=1 convention when that complement is zero. -/
theorem exists_positive_complement_gain
    (M : E →ₗ[ℝ] Y) (K : Submodule ℝ E)
    (hker : LinearMap.ker M = K) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ r : E, r ∈ Kᗮ → σ * ‖r‖ ≤ ‖M r‖ := by
  cases subsingleton_or_nontrivial Kᗮ with
  | inl h =>
      let := h
      exact ⟨1, zero_complement_gain M K⟩
  | inr h =>
      let := h
      obtain ⟨σ, u, hσ, -, -, -, hbound⟩ :=
        exists_attained_positive_complement_gain M K hker
      exact ⟨σ, hσ, hbound⟩

/-- Exact calibration stability. Physical rigidity is required only for x;
neither orthogonal component is assumed to be physical. σ may be the genuine
least gain above or any independently established positive lower gain. -/
theorem fixed_calibration_stability
    (M : E →ₗ[ℝ] Y) (K : Submodule ℝ E) (S : E →ₗ[ℝ] Z)
    (hker : LinearMap.ker M = K) (x : E)
    (a β B σ : ℝ) (ha : 0 ≤ a) (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hσ : 0 < σ) (hq : a * β < 1)
    (hgain : ∀ r : E, r ∈ Kᗮ → σ * ‖r‖ ≤ ‖M r‖)
    (hphysical : ‖x‖ ≤ a * ‖S x‖)
    (hkernel : ∀ k : E, k ∈ K → ‖S k‖ ≤ β * ‖k‖)
    (hslices : ∀ r : E, ‖S r‖ ≤ B * ‖r‖) :
    ‖x‖ ≤ (a * B / ((1 - a * β) * σ)) * ‖M x‖ := by
  obtain ⟨k, r, hk, hr, hxr, -, hkn⟩ := orthogonal_decomposition K x
  have hMk : M k = 0 := by
    have : k ∈ LinearMap.ker M := by rwa [hker]
    exact this
  have hMr : M r = M x := by rw [hxr, map_add, hMk, zero_add]
  have hS : ‖S x‖ ≤ β * ‖x‖ + B * ‖r‖ := by
    calc
      ‖S x‖ = ‖S k + S r‖ := by rw [hxr, map_add]
      _ ≤ ‖S k‖ + ‖S r‖ := norm_add_le _ _
      _ ≤ β * ‖k‖ + B * ‖r‖ := add_le_add (hkernel k hk) (hslices r)
      _ ≤ β * ‖x‖ + B * ‖r‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hkn hβ) le_rfl
  have habs : (1 - a * β) * ‖x‖ ≤ a * B * ‖r‖ := by
    have := hphysical.trans (mul_le_mul_of_nonneg_left hS ha)
    nlinarith only [this]
  have hgr : σ * ‖r‖ ≤ ‖M x‖ := by simpa only [hMr] using hgain r hr
  have hfinal : ((1 - a * β) * σ) * ‖x‖ ≤ (a * B) * ‖M x‖ := by
    calc
      ((1 - a * β) * σ) * ‖x‖ = σ * ((1 - a * β) * ‖x‖) := by ring
      _ ≤ σ * (a * B * ‖r‖) := mul_le_mul_of_nonneg_left habs hσ.le
      _ = (a * B) * (σ * ‖r‖) := by ring
      _ ≤ (a * B) * ‖M x‖ := mul_le_mul_of_nonneg_left hgr (mul_nonneg ha hB)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos (sub_pos.mpr hq) hσ)).mpr
  nlinarith only [hfinal]

/-- Literal source normalization a=√(N+2)/δ and q=√(N+2)β/δ. -/
theorem fixed_calibration_tensor_stability
    (M : E →ₗ[ℝ] Y) (K : Submodule ℝ E) (S : E →ₗ[ℝ] Z)
    (hker : LinearMap.ker M = K) (x : E)
    (N : ℕ) (δ β B σ : ℝ) (hδ : 0 < δ) (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hσ : 0 < σ) (hq : Real.sqrt (N + 2) * β / δ < 1)
    (hgain : ∀ r : E, r ∈ Kᗮ → σ * ‖r‖ ≤ ‖M r‖)
    (hphysical : ‖x‖ ≤ (Real.sqrt (N + 2) / δ) * ‖S x‖)
    (hkernel : ∀ k : E, k ∈ K → ‖S k‖ ≤ β * ‖k‖)
    (hslices : ∀ r : E, ‖S r‖ ≤ B * ‖r‖) :
    ‖x‖ ≤ (Real.sqrt (N + 2) * B /
      (δ * (1 - Real.sqrt (N + 2) * β / δ) * σ)) * ‖M x‖ := by
  have hq' : (Real.sqrt (N + 2) / δ) * β < 1 := by
    simpa only [div_mul_eq_mul_div] using hq
  have h := fixed_calibration_stability M K S hker x
    (Real.sqrt (N + 2) / δ) β B σ
    (div_nonneg (Real.sqrt_nonneg _) hδ.le) hβ hB hσ hq'
    hgain hphysical hkernel hslices
  convert h using 1; field_simp


end C145DRE8HilbertStability

end
