/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsSelfAdjointEigenfunctions

/-!
# Constants and positive eigenspaces of the actual Gibbs operator

Constants lie in the actual closed energy domain and are annihilated by the
self-adjoint operator. Hence every nonzero-rate actual operator eigenvector
is orthogonal to constants, without a smooth representative assumption.
The converse statement about the zero eigenspace is not asserted here.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The `L²` class of a constant function under a Gibbs probability measure. -/
@[expose] noncomputable def gibbsConstantLp {V : E → ℝ}
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (c : ℝ) :
    E →₂[gibbsMeasure volume V] ℝ := by
  have := hprob
  exact (memLp_const c).toLp (fun _ : E => c)

/-- Constants belong to the actual closed form domain by the proved cutoff
approximation, with derivative exactly zero. -/
theorem gibbsConstantLp_graph_mem {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (c : ℝ) :
    (gibbsConstantLp hprob c, 0) ∈ (gibbsPositiveGenerator hV hprob).graph := by
  have := hprob
  have hf : MemLp (fun _ : E => c) 2 (gibbsMeasure volume V) := memLp_const c
  have hg : MemLp (gradient (fun _ : E => c)) 2 (gibbsMeasure volume V) := by
    rw [gradient_fun_const']
    exact memLp_const (0 : E)
  let u := c2GibbsSobolevLift hV hprob contDiff_const hf hg
  have hd : gibbsSobolevDerivative hV hprob u = 0 := by
    apply Lp.ext
    filter_upwards [hg.coeFn_toLp, Lp.coeFn_zero E 2 (gibbsMeasure volume V)] with x hx hz
    change hg.toLp (gradient (fun _ : E => c)) x = (0 : E →₂[gibbsMeasure volume V] E) x
    rw [hx, hz, gradient_fun_const]
    rfl
  have he : ∀ v : gibbsSobolevGraph hV hprob,
      gibbsDirichletEnergy hV hprob u v =
        inner ℝ (0 : E →₂[gibbsMeasure volume V] ℝ) (gibbsSobolevInclusion hV hprob v) := by
    intro v
    change inner ℝ (gibbsSobolevDerivative hV hprob u) (gibbsSobolevDerivative hV hprob v) = _
    rw [hd, inner_zero_left, inner_zero_left]
  exact gibbsPositiveGenerator_of_weak_equation hV hprob u 0 he

/-- Every actual nonzero-rate operator eigenvector is orthogonal to every
constant, from actual operator symmetry and the proved constant domain. -/
theorem gibbsOperatorEigen_inner_constant_eq_zero {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : ρ ≠ 0)
    (u : gibbsOperatorEigenspace hV hprob ρ) (c : ℝ) :
    inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (gibbsConstantLp hprob c) = 0 := by
  let A := gibbsPositiveGenerator hV hprob
  have hu : ((u : E →₂[gibbsMeasure volume V] ℝ), ρ • (u : E →₂[gibbsMeasure volume V] ℝ)) ∈
    A.graph :=
    u.property
  have hc : (gibbsConstantLp hprob c, (0 : E →₂[gibbsMeasure volume V] ℝ)) ∈ A.graph :=
    gibbsConstantLp_graph_mem hV hprob c
  obtain ⟨uv, huv, hau⟩ := A.mem_graph_iff.mp hu
  obtain ⟨cv, hcv, hac⟩ := A.mem_graph_iff.mp hc
  have hp := positiveResolventOperator_formalAdjoint (gibbsL2Resolvent hV hprob)
    (gibbsL2Resolvent_injective hV hprob) (gibbsL2Resolvent_symmetric hV hprob) uv cv
  change inner ℝ (A uv) (cv : E →₂[gibbsMeasure volume V] ℝ) =
    inner ℝ (uv : E →₂[gibbsMeasure volume V] ℝ) (A cv) at hp
  rw [hau, hac, huv, hcv, inner_zero_right, real_inner_smul_left] at hp
  exact (mul_eq_zero.mp hp).resolve_left hρ

end CutoffRigidity
