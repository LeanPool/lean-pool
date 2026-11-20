/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreValueTruncationChainLimits.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreValueTruncationL2
public import LeanPool.GinibrePoincare.Analysis.L2BoundedCoefficientConvergence
public import LeanPool.GinibrePoincare.Analysis.GinibreSmoothDistributionalGradient
public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalClosure

/-! # Nonlinear chain rule through actual smooth graph limits -/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ContDiff NNReal
namespace GinibrePoincare
noncomputable section

/-- The concrete scalar value truncations have a common Lipschitz constant. -/
theorem sobolevValueTruncation_lipschitz : ∃ B : ℝ≥0, ∀ m,
    LipschitzWith B (sobolevValueTruncation m) := by
  obtain ⟨B, hB0, hB⟩ := sobolevValueTruncation_deriv_bound
  refine ⟨⟨B, hB0⟩, fun m => lipschitzWith_of_nnNorm_deriv_le
    ((sobolevValueTruncation_smooth m).differentiable (by simp)) ?_⟩
  intro x
  exact_mod_cast hB m x

/-- Actual value truncation is continuous on Ginibre L². -/
theorem ginibreValueTruncation_continuous (n m : ℕ) :
    Continuous (fun u : Lp ℝ 2 (ginibreMeasure n) =>
      (ginibreValueTruncation_memLp n m u (Lp.memLp u)).toLp
        (fun z => sobolevValueTruncation m (u z))) := by
  obtain ⟨B, hB⟩ := sobolevValueTruncation_lipschitz
  have he : (fun u : Lp ℝ 2 (ginibreMeasure n) =>
      (ginibreValueTruncation_memLp n m u (Lp.memLp u)).toLp
        (fun z => sobolevValueTruncation m (u z))) =
      (hB m).compLp (sobolevValueTruncation_zero m) := by
    funext u
    apply Lp.ext
    exact (ginibreValueTruncation_memLp n m u (Lp.memLp u)).coeFn_toLp.trans
      ((hB m).coeFn_compLp (sobolevValueTruncation_zero m) u).symm
  rw [he]
  exact (hB m).continuous_compLp (sobolevValueTruncation_zero m)

/-- The nonlinear weak chain rule holds for a limit of actual smooth
value-gradient pairs. This result will be applied to concrete local mollifications. -/
theorem ginibreValueTruncation_chain_of_smooth_limits (n : ℕ) (hn : 0 < n) (m : ℕ)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (v : ℕ → Lp ℝ 2 (ginibreMeasure n))
    (w : ℕ → Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (f : ℕ → Configuration n → ℝ) (hs : ∀ j, ContDiff ℝ ∞ (f j))
    (hv : ∀ j, (v j : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f j)
    (hw : ∀ j, (w j : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
      =ᵐ[ginibreMeasure n] ginibreEuclideanGradient (f j))
    (htv : Tendsto v atTop (𝓝 u)) (htw : Tendsto w atTop (𝓝 g)) :
    IsGinibreDistributionalGradient n
      ((ginibreValueTruncation_memLp n m u (Lp.memLp u)).toLp
        (fun z => sobolevValueTruncation m (u z)))
      ((ginibreValueTruncation_vector_memLp n m u (Lp.aestronglyMeasurable u) g (Lp.memLp g)).toLp
        (fun z => deriv (sobolevValueTruncation m) (u z) • g z)) := by
  obtain ⟨ns, hns, hnae⟩ := (tendstoInMeasure_of_tendsto_Lp htv).exists_seq_tendsto_ae
  obtain ⟨B, hB0, hB⟩ := sobolevValueTruncation_deriv_bound
  let a j z := deriv (sobolevValueTruncation m) (v (ns j) z)
  let c z := deriv (sobolevValueTruncation m) (u z)
  have ha (j : ℕ) : AEStronglyMeasurable (a j) (ginibreMeasure n) :=
    ((sobolevValueTruncation_smooth m).continuous_deriv (by simp)).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (v (ns j)))
  have hc : AEStronglyMeasurable c (ginibreMeasure n) :=
    ((sobolevValueTruncation_smooth m).continuous_deriv (by simp)).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable u)
  let q j := (L2_boundedCoefficient_memLp (ginibreMeasure n) (a j) (ha j) B hB0
    (fun z => hB m (v (ns j) z)) (w (ns j))).toLp (fun z => a j z • w (ns j) z)
  let r := (L2_boundedCoefficient_memLp (ginibreMeasure n) c hc B hB0
    (fun z => hB m (u z)) g).toLp (fun z => c z • g z)
  have hr : r = (ginibreValueTruncation_vector_memLp n m u (Lp.aestronglyMeasurable u) g (Lp.memLp
    g)).toLp
      (fun z => deriv (sobolevValueTruncation m) (u z) • g z) := by
    apply Lp.ext
    exact (L2_boundedCoefficient_memLp (ginibreMeasure n) c hc B hB0 (fun z => hB m (u z))
      g).coeFn_toLp.trans
      (ginibreValueTruncation_vector_memLp n m u (Lp.aestronglyMeasurable u) g (Lp.memLp
        g)).coeFn_toLp.symm
  have hq : Tendsto q atTop (𝓝 r) := by
    apply L2_boundedCoefficient_tendsto (ginibreMeasure n) a c ha hc B hB0
      (fun j z => hB m (v (ns j) z)) (fun z => hB m (u z))
    · filter_upwards [hnae] with z hz
      exact ((sobolevValueTruncation_smooth m).continuous_deriv (by
        simp)).continuousAt.tendsto.comp hz
    · exact htw.comp hns.tendsto_atTop
  rw [hr] at hq
  apply ginibre_distributional_gradient_tendsto n hn (l := atTop)
    (fun j => ((ginibreValueTruncation_memLp n m (v (ns j)) (Lp.memLp (v (ns j)))).toLp
      (fun z => sobolevValueTruncation m (v (ns j) z)), q j)) _ _
  · apply Eventually.of_forall
    intro j
    apply ginibre_smooth_distributional_gradient n hn _ _
      (fun z => sobolevValueTruncation m (f (ns j) z))
      ((sobolevValueTruncation_smooth m).comp (hs (ns j)))
    · apply (ginibreValueTruncation_memLp n m (v (ns j)) (Lp.memLp (v (ns j)))).coeFn_toLp.trans
      exact (hv (ns j)).fun_comp (sobolevValueTruncation m)
    · filter_upwards [(L2_boundedCoefficient_memLp (ginibreMeasure n) (a j) (ha j) B hB0
        (fun z => hB m (v (ns j) z)) (w (ns j))).coeFn_toLp,
        hv (ns j), hw (ns j)] with z h1 h2 h3
      change q j z = _ at h1
      rw [h1]
      dsimp only [a]
      rw [h2, h3, ginibreValueTruncation_smooth_gradient n m (f (ns j)) (hs (ns j))]
  · exact (ginibreValueTruncation_continuous n m).continuousAt.tendsto.comp
      (htv.comp hns.tendsto_atTop)
  · exact hq
end
end GinibrePoincare
