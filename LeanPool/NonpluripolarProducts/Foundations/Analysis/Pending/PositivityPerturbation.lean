/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HermitianGeometry

/-!
# Small perturbations of semipositive `(1,1)`-forms

`exists_isStrictlyPositive_add_smul`: let `a, b` be real two-forms on `ℂⁿ` with
`a(v, iv) ≥ 0` for all `v`, and `b(v, iv) > 0` whenever `v ≠ 0` and `a(v, iv) = 0`.  Then
`a + ε b` is strictly positive for all small `ε > 0`.

This is the pointwise heart of the Blanchard argument: `a = π^* ω` degenerates exactly along
the fibres of the blowup, where `b = ddᶜ log |s_E|²` is a Fubini-Study form.  The proof is
compactness of the unit sphere: on the compact set where `b(v, iv) ≤ 0`, `a(v, iv)` has a
positive minimum.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.PositivityPerturbation

open FirstPass

noncomputable section

variable {n : ℕ}

/-- The quadratic form `v ↦ a(v, iv)`. -/
def quad (a : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ) (v : ComplexModel n) : ℝ :=
  a ![v, Complex.I • v]

theorem continuous_quad (a : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ) : Continuous (quad a) := by
  unfold quad
  fun_prop

theorem quad_smul (a : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ) (t : ℝ) (v : ComplexModel n) :
    quad a (t • v) = t ^ 2 * quad a v := by
  unfold quad
  have h : (![t • v, Complex.I • (t • v)] : Fin 2 → ComplexModel n) =
      fun i => (fun _ : Fin 2 => t) i • (![v, Complex.I • v] : Fin 2 → ComplexModel n) i := by
    funext i
    fin_cases i
    · rfl
    · exact smul_comm Complex.I t v
  rw [h, a.map_smul_univ]
  simp [Finset.prod_const, smul_eq_mul]

theorem quad_add (a b : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ) (v : ComplexModel n) :
    quad (a + b) v = quad a v + quad b v := rfl

theorem quad_smul_form (c : ℝ) (a : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ) (v : ComplexModel n) :
    quad (c • a) v = c * quad a v := rfl

/-- **Small perturbations of a semipositive form that are positive on its null directions
are strictly positive.** -/
theorem exists_isStrictlyPositive_add_smul {a b : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : ∀ v, 0 ≤ quad a v) (hb : ∀ v, v ≠ 0 → quad a v = 0 → 0 < quad b v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → IsStrictlyPositive (a + ε • b) := by
  set S := sphere (0 : ComplexModel n) 1
  have hS : IsCompact S := isCompact_sphere 0 1
  set K := S ∩ {v | quad b v ≤ 0}
  have hK : IsCompact K := hS.inter_right (isClosed_le (continuous_quad b) continuous_const)
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn (continuous_quad b).continuousOn
  have hSne : ∀ u ∈ S, u ≠ 0 := fun u hu h => by
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hu; exact zero_ne_one hu
  obtain ⟨m, hm, hmK⟩ : ∃ m : ℝ, 0 < m ∧ ∀ u ∈ K, m ≤ quad a u := by
    by_cases hKe : K.Nonempty
    · obtain ⟨v₀, hv₀, hmin⟩ := hK.exists_isMinOn hKe (continuous_quad a).continuousOn
      refine ⟨quad a v₀, ?_, fun u hu => hmin hu⟩
      rcases (ha v₀).lt_or_eq with h | h
      · exact h
      · exact absurd hv₀.2 (not_le.mpr (hb v₀ (hSne v₀ hv₀.1) h.symm))
    · exact ⟨1, one_pos, fun u hu => absurd ⟨u, hu⟩ hKe⟩
  refine ⟨m / (|B| + 1), by positivity, fun ε hε hεle v hv => ?_⟩
  set u := ‖v‖⁻¹ • v
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have huS : u ∈ S := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn.ne']
  have hvu : v = ‖v‖ • u := by rw [smul_inv_smul₀ hvn.ne']
  have hu : 0 < quad (a + ε • b) u := by
    rw [quad_add, quad_smul_form]
    by_cases hbu : quad b u ≤ 0
    · have h1 := hmK u ⟨huS, hbu⟩
      have h2 : |quad b u| ≤ |B| := (Real.norm_eq_abs _ ▸ hB u huS).trans (le_abs_self B)
      have h3 : ε * |B| < m := by
        calc ε * |B| ≤ m / (|B| + 1) * |B| := by gcongr
          _ < m / (|B| + 1) * (|B| + 1) := by gcongr; linarith
          _ = m := div_mul_cancel₀ m (by positivity)
      have h4 : -(ε * |B|) ≤ ε * quad b u := by
        rw [← mul_neg]
        exact mul_le_mul_of_nonneg_left (neg_le_of_abs_le h2) hε.le
      linarith
    · push Not at hbu
      have := ha u
      nlinarith
  change 0 < quad (a + ε • b) v
  rw [hvu, quad_smul]
  positivity

end

end SGPT.Foundations.Analysis.Pending.PositivityPerturbation
