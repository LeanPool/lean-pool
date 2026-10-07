/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongCompactness
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitKernel

/-!
# The weak limit of the time derivatives

If the time derivatives of an `L²`-convergent sequence are bounded in `L²`, a subsequence of them
converges weakly, and the limit is the weak time derivative of the limit of the sequence against
every test pair for which the integration by parts identity holds along the sequence
(`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- A bounded sequence of triples of square integrable functions has a weakly convergent subsequence
whose limit represents the time derivative of the limit of the sequence against every test pair
for which the identity holds along the sequence. -/
theorem lps_weak_limit_time_derivative {μ : Measure ParabolicPoint} [SFinite μ]
    (Un Qn : ℕ → Fin 3 → ParabolicPoint → ℝ) (u : Fin 3 → ParabolicPoint → ℝ)
    (hUn : ∀ n i, MemLp (Un n i) 2 μ) (hQn : ∀ n i, MemLp (Qn n i) 2 μ)
    (hu : ∀ i, MemLp (u i) 2 μ)
    (hconv : ∀ i, Tendsto (fun n => ∫ z, (Un n i z - u i z) ^ 2 ∂μ) atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n i, ‖(hQn n i).toLp (Qn n i)‖ ≤ C)
    (P : (ParabolicPoint → ℝ) → (ParabolicPoint → ℝ) → Prop)
    (hP : ∀ θ Dθ, P θ Dθ → MemLp θ 2 μ ∧ MemLp Dθ 2 μ ∧
      ∀ n i, (∫ z, Un n i z * Dθ z ∂μ) = -∫ z, Qn n i z * θ z ∂μ) :
    ∃ Dt : Fin 3 → ParabolicPoint → ℝ, (∀ i, MemLp (Dt i) 2 μ) ∧
      (∀ i, ∀ θ Dθ, P θ Dθ → (∫ z, u i z * Dθ z ∂μ) = -∫ z, Dt i z * θ z ∂μ) := by
  classical
  let F : ℕ → Fin 3 → Lp ℝ 2 μ := fun n i => (hQn n i).toLp (Qn n i)
  have hFbound (n : ℕ) (i : Fin 3) : ‖F n i‖ ≤ C := hbound n i
  let : IsSeparable μ := inferInstance
  let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : TopologicalSpace.SeparableSpace (Lp ℝ 2 μ) := by
    exact TopologicalSpace.SecondCountableTopology.to_separableSpace
  obtain ⟨τ, hτ, H, hHweak⟩ :=
    CKN.Leray.exists_common_subsequence_weak_limit_of_bounded
      F (fun _ : Fin 3 => C) (fun _ => hC) hFbound
  refine ⟨fun i => H i, fun i => Lp.memLp (H i), ?_⟩
  intro i θ Dθ hθ
  obtain ⟨hθ2, hDθ2, hid⟩ := hP θ Dθ hθ
  -- the left side converges to the pairing with the limit
  have hleft : Tendsto (fun n => ∫ z, Un (τ n) i z * Dθ z ∂μ) atTop
      (𝓝 (∫ z, u i z * Dθ z ∂μ)) := by
    have hconst : Tendsto (fun _ : ℕ => ∫ z, (Dθ z - Dθ z) ^ 2 ∂μ) atTop (𝓝 0) := by
      simp
    exact lps_integral_mul_tendsto (F := fun n => Un (τ n) i) (G := fun _ => Dθ)
      (fun n => hUn (τ n) i) (fun _ => hDθ2) (hu i) hDθ2
      ((hconv i).comp hτ.tendsto_atTop) hconst
  have hright : Tendsto (fun n => -∫ z, Qn (τ n) i z * θ z ∂μ) atTop
      (𝓝 (-∫ z, H i z * θ z ∂μ)) := by
    refine Tendsto.neg ?_
    have hweak := hHweak i (hθ2.toLp θ)
    have hseq : (fun n => ∫ z, Qn (τ n) i z * θ z ∂μ) =
        fun n => inner ℝ (F (τ n) i) (hθ2.toLp θ) := by
      funext n
      symm
      exact lps_scalar_lp_inner_integral_generic (hQn (τ n) i) hθ2
    have hlim : inner ℝ (H i) (hθ2.toLp θ) = ∫ z, H i z * θ z ∂μ :=
      lps_scalar_lp_inner_left_eq_integral hθ2
    rw [hseq, ← hlim]
    exact hweak
  have heq : (fun n => ∫ z, Un (τ n) i z * Dθ z ∂μ) =
      fun n => -∫ z, Qn (τ n) i z * θ z ∂μ := funext fun n => hid (τ n) i
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end ESS.LPS

end
