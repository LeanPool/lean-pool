/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Convergence.Frequency

/-!
Actual Hamiltonian vector fields at each stage, their conjugacies, and vanishing error bounds.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace KamProject.Arnold1963.Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

/-- The Hamiltonian vector field at the specified iteration stage. -/
def vectorField (s : ℕ) : ComplexPhaseSpace n → ComplexPhaseSpace n :=
  hamiltonianVectorField (h.hamiltonian b s)

theorem hamiltonian_analytic (s : ℕ) : AnalyticOnNhd ℂ (h.hamiltonian b s) (h.phase b s) := by
  intro z hz
  exact (((h.state b s).input.analytic z.1 hz.1).comp analyticAt_fst).add
    ((h.state b s).perturbation.analytic z hz)

theorem vectorField_analytic (s : ℕ) : AnalyticOnNhd ℂ (h.vectorField b s) (h.phase b s) := by
  intro z hz
  exact (analyticAt_qGradient (h.hamiltonian_analytic b s z hz)).neg.prod
    (analyticAt_pGradient (h.hamiltonian_analytic b s z hz))

theorem vectorField_split (s : ℕ) {z : ComplexPhaseSpace n} (hz : z ∈ h.phase b s) :
    h.vectorField b s z = (0, h.frequency b s z.1) +
      hamiltonianVectorField (h.state b s).perturbation.toFun z := by
  have ha := (h.state b s).input.analytic z.1 hz.1
  have hf := (h.state b s).perturbation.analytic z hz
  change hamiltonianVectorField (((h.state b s).integrable ∘ Prod.fst) +
    (h.state b s).perturbation.toFun) z = _
  rw [hamiltonianVectorField_add (ha.comp analyticAt_fst).differentiableAt hf.differentiableAt,
    hamiltonianVectorField_actionOnly z ha.differentiableAt]
  rfl

theorem vectorField_conjugacy (s : ℕ) {z : ComplexPhaseSpace n} (hz : z ∈ h.phase b s) :
    fderiv ℂ (h.cumulative b s) z (h.vectorField b s z) =
      h.vectorField b 0 (h.cumulative b s z) := by
  have hh := (h.cumulative_canonical b s z hz).map_hamiltonianVectorField
    (h.hamiltonian_analytic b 0 _ (h.cumulative_maps b s hz)).differentiableAt
  have he : h.hamiltonian b 0 ∘ h.cumulative b s = h.hamiltonian b s :=
    funext (h.cumulative_identity b s)
  rw [he] at hh
  exact hh

theorem vectorField_limit_error (s : ℕ) {z : ComplexPhaseSpace n} (hz : z ∈ h.limitPhase b) :
    ‖h.vectorField b (s + 1) z - (0, h.limitFrequency b z.1)‖ < (beta δ₁ (s + 1) : ℝ) := by
  have hp : z.1 ∈ h.limitDomain b := mem_iInter.mpr fun j => (h.limitPhase_subset b j hz).1
  have hr := (norm_hamiltonianVectorField_le (h.state b (s + 1)).perturbation.toFun z).trans_lt
    (h.remainder_derivative b s (h.limitPhase_subset b (s + 1) hz))
  have hf := h.limitFrequency_tail b hp (s + 1)
  have hd : (delta δ₁ s : ℝ) < 1 / 4 := (b.delta_step_le s).trans_lt b.delta_quarter
  have hβ : (0 : ℝ) < beta δ₁ (s + 1) := pow_pos (b.delta_step_pos _) 3
  rw [h.vectorField_split b (s + 1) (h.limitPhase_subset b (s + 1) hz)]
  have he : (0, h.frequency b (s + 1) z.1) +
      hamiltonianVectorField (h.state b (s + 1)).perturbation.toFun z -
      (0, h.limitFrequency b z.1) =
    hamiltonianVectorField (h.state b (s + 1)).perturbation.toFun z +
      (0, h.frequency b (s + 1) z.1 - h.limitFrequency b z.1) := by
    ext j <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Pi.add_apply, Pi.sub_apply, Pi.zero_apply] <;> abel
  rw [he]
  have hnorm : ‖((0 : ComplexSpace n), h.frequency b (s + 1) z.1 - h.limitFrequency b z.1)‖ =
      ‖h.limitFrequency b z.1 - h.frequency b (s + 1) z.1‖ := by
    simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), norm_sub_rev]
  have ht := norm_add_le (hamiltonianVectorField (h.state b (s + 1)).perturbation.toFun z)
    (0, h.frequency b (s + 1) z.1 - h.limitFrequency b z.1)
  rw [hnorm] at ht
  nlinarith

theorem approximate_conjugacy (s : ℕ) {z : ComplexPhaseSpace n} (hz : z ∈ h.limitPhase b) :
    ‖fderiv ℂ (h.cumulative b (s + 1)) z (0, h.limitFrequency b z.1) -
      h.vectorField b 0 (h.cumulative b (s + 1) z)‖ ≤
      (2 : ℝ) ^ (s + 1) * beta δ₁ (s + 1) := by
  rw [← h.vectorField_conjugacy b (s + 1) (h.limitPhase_subset b (s + 1) hz),
    ← map_sub]
  exact ((fderiv ℂ (h.cumulative b (s + 1)) z).le_opNorm _).trans
    (mul_le_mul (h.cumulative_derivative b (s + 1) z (h.limitPhase_subset b (s + 1) hz))
      (by simpa only [norm_sub_rev] using (h.vectorField_limit_error b s hz).le)
      (norm_nonneg _) (by positivity))

end KamProject.Arnold1963.Iteration.InitialData
