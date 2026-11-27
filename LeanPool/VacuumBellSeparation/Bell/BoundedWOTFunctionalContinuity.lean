/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.VNAWeakOperatorCompactness
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Algebra.Monoid

/-!
# Full-dual norm approximation gives continuity on actual bounded WOT balls

The ball has the subspace topology from the actual weak operator topology,
not the operator norm topology. The approximation premise concerns finite
matrix coefficients in the ORIGINAL Hilbert space. No normal-functional
representation or normality-to-ultraweak equivalence is assumed or proved.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The original VNA's radius-R operator ball with its actual WOT topology. -/
def vnaWOTBall (M : VonNeumannAlgebra H) (R : ℝ) :=
  {T : H →WOT[ℂ] H // T.toCLM ∈ M ∧ ‖T.toCLM‖ ≤ R}

/-- The defining subtype carries the topology induced by the actual WOT. -/
instance vnaWOTBall.instTopologicalSpace (M : VonNeumannAlgebra H) (R : ℝ) :
    TopologicalSpace (vnaWOTBall M R) :=
  inferInstanceAs (TopologicalSpace
    {T : H →WOT[ℂ] H // T.toCLM ∈ M ∧ ‖T.toCLM‖ ≤ R})

/-- This map only forgets the WOT topology; continuity in operator norm is
neither used nor asserted. -/
def vnaWOTBallElement {M : VonNeumannAlgebra H} {R : ℝ}
    (T : vnaWOTBall M R) : M.toStarSubalgebra :=
  ⟨T.1.toCLM, T.2.1⟩

/-- Literal finite original-H coefficient representation; n=0 includes zero. -/
def IsFiniteVectorCoefficient (M : VonNeumannAlgebra H)
    (f : StrongDual ℂ M.toStarSubalgebra) : Prop :=
  ∃ (n : ℕ) (x y : Fin n → H) (c : Fin n → ℂ),
    ∀ T : M.toStarSubalgebra,
      f T = ∑ i, c i * inner ℂ (x i) ((T : H →L[ℂ] H) (y i))

theorem continuous_vnaWOTBall_eval_of_finite_coefficients
    (M : VonNeumannAlgebra H) (R : ℝ)
    (f : StrongDual ℂ M.toStarSubalgebra) (hf : IsFiniteVectorCoefficient M f) :
    Continuous (fun T : vnaWOTBall M R => f (vnaWOTBallElement T)) := by
  obtain ⟨n, x, y, c, he⟩ := hf
  have heq : (fun T : vnaWOTBall M R => f (vnaWOTBallElement T)) =
      fun T => ∑ i, c i * inner ℂ (x i) (T.1 (y i)) := by
    funext T
    exact he (vnaWOTBallElement T)
  rw [heq]
  apply continuous_finsetSum
  intro i _
  apply continuous_const.mul
  exact (ContinuousLinearMapWOT.continuous_iff.mp
    (continuous_subtype_val : Continuous (fun T : vnaWOTBall M R => T.1))) (y i) (x i)

/-- Uniform control comes from the FULL continuous-dual norm. There is no
operator-norm continuity assumption on the WOT ball itself. -/
theorem continuous_vnaWOTBall_eval_of_norm_approximation
    (M : VonNeumannAlgebra H) (R : ℝ)
    (f : StrongDual ℂ M.toStarSubalgebra)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : StrongDual ℂ M.toStarSubalgebra,
      Continuous (fun T : vnaWOTBall M R => g (vnaWOTBallElement T)) ∧ ‖f - g‖ < ε) :
    Continuous (fun T : vnaWOTBall M R => f (vnaWOTBallElement T)) := by
  apply Metric.continuous_iff'.mpr
  intro T₀ ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_mul_lt (half_pos hε) (2 * R)
  obtain ⟨g, hg, hfg⟩ := happrox δ hδ
  have hb (T : vnaWOTBall M R) :
      dist (f (vnaWOTBallElement T)) (g (vnaWOTBallElement T)) ≤ δ * R := by
    calc
      _ = ‖(f - g) (vnaWOTBallElement T)‖ := by
        rw [dist_eq_norm, sub_apply]
      _ ≤ ‖f - g‖ * ‖vnaWOTBallElement T‖ := (f - g).le_opNorm _
      _ ≤ δ * R := mul_le_mul hfg.le T.2.2 (norm_nonneg _) hδ.le
  have he := (Metric.continuous_iff'.mp hg) T₀ (ε / 2) (half_pos hε)
  filter_upwards [he] with T hT
  have h1 := hb T
  have h0 := hb T₀
  have ht1 := dist_triangle (f (vnaWOTBallElement T))
    (g (vnaWOTBallElement T)) (f (vnaWOTBallElement T₀))
  have ht2 := dist_triangle (g (vnaWOTBallElement T))
    (g (vnaWOTBallElement T₀)) (f (vnaWOTBallElement T₀))
  rw [dist_comm (g (vnaWOTBallElement T₀)) (f (vnaWOTBallElement T₀))] at ht2
  nlinarith

/-- Concrete norm-closure-to-WOT bridge for later normal representation work.
Membership in this norm closure is the displayed premise, not inferred from
order normality or from membership in the positive normal cone. -/
theorem continuous_vnaWOTBall_eval_of_mem_closure_coefficients
    (M : VonNeumannAlgebra H) (R : ℝ)
    (f : StrongDual ℂ M.toStarSubalgebra)
    (hf : f ∈ closure {g : StrongDual ℂ M.toStarSubalgebra |
      IsFiniteVectorCoefficient M g}) :
    Continuous (fun T : vnaWOTBall M R => f (vnaWOTBallElement T)) := by
  apply continuous_vnaWOTBall_eval_of_norm_approximation M R f
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := (Metric.mem_closure_iff
    (α := StrongDual ℂ M.toStarSubalgebra)).mp hf ε hε
  refine ⟨g, continuous_vnaWOTBall_eval_of_finite_coefficients M R g hg, ?_⟩
  have hdist : dist f g = ‖f - g‖ := _root_.dist_eq_norm f g
  exact hdist ▸ hfg

end VacuumBellSeparation.Bipartite
