/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoActualDriftQuadratic.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoDriftVariation
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoDriftQuadratic

/-!
# Finite dimensional Ito actual drift quadratic

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `itoActualPath_drift_hessian_tendsto`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On actual continuous paths and actual Volterra drift increments, every
mixed and drift-square Hessian term vanishes in the uniform-partition limit. -/
theorem itoActualPath_drift_hessian_tendsto
    (f : E → ℝ) (U K : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hK : IsCompact K) (hKU : K ⊆ U) (T : ℝ≥0)
    (X W : ℝ≥0 → E) (b : ℝ → E)
    (hX : ∀ t ∈ Set.Icc 0 T, X t ∈ K)
    (hW : ContinuousOn W (Set.Icc 0 T)) (hb : ContinuousOn b (Set.Icc (0 : ℝ) T)) :
    Tendsto (fun n => ∑ i : Fin (n+1),
      (itoDirectionalHessian f (X (ginibreUniformBrownianTime T n i))
        ((W (ginibreUniformBrownianTime T n (i.val+1)) -
          W (ginibreUniformBrownianTime T n i)) + itoUniformDriftIncrement b T n i) -
      itoDirectionalHessian f (X (ginibreUniformBrownianTime T n i))
        (W (ginibreUniformBrownianTime T n (i.val+1)) -
          W (ginibreUniformBrownianTime T n i)))) atTop (𝓝 0) := by
  classical
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hb
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbm : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖b t‖ ≤ M :=
    fun t ht => (hB t ht).trans (le_max_left _ _)
  let q : ∀ n, ℕ → Fin (n+1) := fun n i => ⟨i%(n+1), Nat.mod_lt _ (Nat.succ_pos n)⟩
  let x := fun n i => X (ginibreUniformBrownianTime T n (q n i))
  let a := fun n i => W (ginibreUniformBrownianTime T n ((q n i).val+1)) -
    W (ginibreUniformBrownianTime T n (q n i))
  let c := fun n i => itoUniformDriftIncrement b T n (q n i)
  let m := fun n => itoUniformPathMesh W T n + M*((T : ℝ)/((n : ℝ)+1))
  have hm : Tendsto m atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (M*(T : ℝ))
    have hlim : Tendsto (fun n : ℕ => M*((T : ℝ)/((n : ℝ)+1))) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, mul_assoc] using hh
    simpa only [add_zero] using (itoUniformPathMesh_tendsto W T hW).add hlim
  have hv : ∀ n, ∑ i ∈ Finset.range (n+1), ‖c n i‖ ≤ M*(T : ℝ) := by
    intro n
    have hh := itoUniformDriftIncrement_variation_le b T n M hbm
    rw [←Fin.sum_univ_eq_sum_range (fun i => ‖c n i‖) (n+1)]
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    simp [c, q, Nat.mod_eq_of_lt i.is_lt]
  have ht := itoDirectionalHessian_local_compact_drift_sum_tendsto f U K hU hf hK hKU
    (fun n => Finset.range (n+1)) x a c
    (fun n i hi => hX _ ⟨bot_le, ginibreUniformBrownianTime_le_end T n _
      (Nat.le_of_lt (q n i).is_lt)⟩) (M*(T : ℝ)) (mul_nonneg hM T.coe_nonneg)
    m hm (fun n => add_nonneg (itoUniformPathMesh_nonneg W T n) (by positivity))
    (fun n i hi => (itoUniformPathMesh_increment_le W T n (q n i)).trans
      (le_add_of_nonneg_right (by positivity)))
    (fun n i hi => (itoUniformDriftIncrement_norm_le b T n M hbm (q n i)).trans
      (le_add_of_nonneg_left (itoUniformPathMesh_nonneg W T n))) hv
  convert ht using 1
  ext n
  rw [←Fin.sum_univ_eq_sum_range (fun i =>
    itoDirectionalHessian f (x n i) (a n i+c n i)-itoDirectionalHessian f (x n i) (a n i)) (n+1)]
  apply Finset.sum_congr rfl
  intro i hi
  simp [x, a, c, q, Nat.mod_eq_of_lt i.is_lt]

end
end GinibrePoincare
