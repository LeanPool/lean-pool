/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.FaithfulNormalBellMaximality
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
A norm-bounded family of actual algebra elements that approaches a common
state upper bound in one faithful normal state approaches that same bound
in every normal state. The proof uses actual positive dominated states and
full-dual norm density, without a representation or compactness premise.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open HC00 Filter
open scoped ComplexOrder Topology NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem state_evaluation_tendsto_upper_of_dominated
    (M : VonNeumannAlgebra H) (ω φ : StateSpace M)
    (T : ℕ → M.toStarSubalgebra) (C : ℝ)
    (hupper : ∀ ψ : StateSpace M, ∀ n, (ψ.1 (T n)).re ≤ C)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hdom : ∀ X : M.toStarSubalgebra, 0 ≤ X → t • φ.1 X ≤ ω.1 X)
    (hω : Tendsto (fun n => (ω.1 (T n)).re) atTop (𝓝 C)) :
    Tendsto (fun n => (φ.1 (T n)).re) atTop (𝓝 C) := by
  let ψ : StateSpace M :=
    ⟨dominatedStateResidual M ω φ t, dominatedStateResidual_isState M ω φ ht1 hdom⟩
  have hbound (n : ℕ) : C - (φ.1 (T n)).re ≤ (C - (ω.1 (T n)).re) / t := by
    apply (le_div_iff₀ ht).mpr
    have he := congrArg Complex.re (dominatedStateResidual_decomposition M ω φ ht1 (T n))
    change (t • φ.1 (T n) + (1 - t) • ψ.1 (T n)).re = (ω.1 (T n)).re at he
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at he
    have hp := mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr (hupper ψ n))
    nlinarith
  have hlim : Tendsto (fun n => (C - (ω.1 (T n)).re) / t) atTop (𝓝 0) := by
    simpa only [sub_self, zero_div] using ((tendsto_const_nhds (x := C)).sub hω).div_const t
  have hz := squeeze_zero (fun n => sub_nonneg.mpr (hupper φ n)) hbound hlim
  simpa only [sub_sub_cancel, sub_zero] using
    (tendsto_const_nhds (x := C)).sub hz

theorem normalState_evaluation_lipschitz (M : VonNeumannAlgebra H)
    (T : M.toStarSubalgebra) (K : ℝ≥0) (hT : ‖T‖ ≤ K) :
    LipschitzWith K (fun φ : NormalStateSpace M => (φ.1 T).re) := by
  apply LipschitzWith.of_dist_le_mul
  intro φ ψ
  simp only [Subtype.dist_eq, dist_eq_norm]
  change |(φ.1 T).re - (ψ.1 T).re| ≤ (K : ℝ) * ‖φ.1 - ψ.1‖
  calc
    _ = |((φ.1 - ψ.1) T).re| := by rw [sub_apply, Complex.sub_re]
    _ ≤ ‖(φ.1 - ψ.1) T‖ := Complex.abs_re_le_norm _
    _ ≤ ‖φ.1 - ψ.1‖ * ‖T‖ := (φ.1 - ψ.1).le_opNorm T
    _ ≤ ‖φ.1 - ψ.1‖ * (K : ℝ) := mul_le_mul_of_nonneg_left hT (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- The same sequence and the same limit serve every original normal state.
The upper bound is an actual inequality for every state, not a supremum
attainment or state-density hypothesis. -/
theorem normalState_evaluation_tendsto_upper_of_faithful
    (M : VonNeumannAlgebra H) (ω : NormalStateSpace M)
    (hf : ∀ a : M.toStarSubalgebra, ω.1 (star a * a) = 0 → a = 0)
    (T : ℕ → M.toStarSubalgebra) (C : ℝ) (K : ℝ≥0)
    (hbound : ∀ n, ‖T n‖ ≤ K)
    (hupper : ∀ ψ : StateSpace M, ∀ n, (ψ.1 (T n)).re ≤ C)
    (hω : Tendsto (fun n => (ω.1 (T n)).re) atTop (𝓝 C))
    (φ : NormalStateSpace M) :
    Tendsto (fun n => (φ.1 (T n)).re) atTop (𝓝 C) := by
  have heq : UniformEquicontinuous
      (fun n (ψ : NormalStateSpace M) => (ψ.1 (T n)).re) :=
    LipschitzWith.uniformEquicontinuous _ K
      (fun n => normalState_evaluation_lipschitz M (T n) K (hbound n))
  apply (heq.equicontinuous φ).tendsto_of_mem_closure
    (f := fun _ => C) tendsto_const_nhds ?_
    (normalState_mem_closure_dominated_of_faithful M ω hf φ)
  rintro ψ ⟨t, ht, ht1, hdom⟩
  exact state_evaluation_tendsto_upper_of_dominated M ⟨ω.1, ω.2.1⟩
    ⟨ψ.1, ψ.2.1⟩ T C hupper ht ht1 hdom hω

end VacuumBellSeparation.Bipartite
