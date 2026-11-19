/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticBrownianFamilyPast.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyGaussian
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-! Every finite independent Brownian family has fresh increments independent of its entire joint
past. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Finset
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_family_increment_independent_past {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0) :
    IndepFun (fun ω i => B i (s+t) ω-B i s ω)
      (fun ω (p : ι × Set.Iic s) => B p.1 p.2 ω) P := by
  have := Fintype.ofFinite ι
  classical
  let X := fun i ω => B i (s+t) ω-B i s ω
  let Y := fun (p : ι × Set.Iic s) ω => B p.1 p.2 ω
  have hG := ginibreBrownian_family_isGaussianProcess B P hB hind
  have hXY : IsGaussianProcess (Sum.elim X Y) P := by
    apply hG.of_isGaussianProcess
    intro q
    cases q with
    | inl i =>
      refine ⟨{(i, s+t), (i, s)},
        { toFun := fun v => v ⟨(i, s+t), by simp⟩-v ⟨(i, s), by simp⟩
          map_add' := by intros; simp only [Pi.add_apply]; ring
          map_smul' := by intros; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring },
              ?_⟩
      intro ω
      rfl
    | inr p =>
      refine ⟨{(p.1, (p.2 : ℝ≥0))},
        { toFun := fun v => v ⟨(p.1, (p.2 : ℝ≥0)), by simp⟩
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }, ?_⟩
      intro ω
      rfl
  apply hXY.indepFun_of_covariance_eq_zero
    (fun i => (hB i).aemeasurable (s+t) |>.sub ((hB i).aemeasurable s))
    (fun p => (hB p.1).aemeasurable p.2)
  intro i p
  rcases p with ⟨j, v⟩
  have hXi : MemLp (X i) 2 P :=
    ((hB i).isGaussianProcess.hasGaussianLaw_eval (s+t)).memLp_two.sub
      ((hB i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hYj : MemLp (Y (j, v)) 2 P := ((hB j).isGaussianProcess.hasGaussianLaw_eval v).memLp_two
  by_cases hij : i = j
  · subst j
    have hi := (ginibreBrownian_increment_whole_past_independent (B i) P (hB i) s t).comp
      measurable_id (measurable_pi_apply v)
    exact hi.covariance_eq_zero hXi hYj
  · have hi := (hind.indepFun hij).comp
      (show Measurable (fun p : ℝ≥0 → ℝ => p (s+t)-p s) by fun_prop)
      (measurable_pi_apply (v : ℝ≥0))
    exact hi.covariance_eq_zero hXi hYj

theorem ginibreBrownian_family_increment_hasLaw {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0) :
    HasLaw (fun ω i => B i (s+t) ω-B i s ω)
      (Measure.pi (fun _ : ι => gaussianReal 0 t)) P := by
  have hL (i : ι) : HasLaw (fun ω => B i (s+t) ω-B i s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B i) P (hB i) s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hi := hind.comp (fun i p => p (s+t)-p s) (fun i => by fun_prop)
  exact hi.hasLaw_pi hL

end
end GinibrePoincare
