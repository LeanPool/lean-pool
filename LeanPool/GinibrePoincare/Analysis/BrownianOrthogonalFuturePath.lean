/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalFuturePath.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianAugmentedFreshIncrement

/-! Original Brownian whole-future independence, including the complete joint past. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Finset
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem brownianFamily_whole_future_independent_past {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s : ℝ≥0) :
    IndepFun (fun ω (q : ι × ℝ≥0) => B q.1 (s+q.2) ω-B q.1 s ω)
      (fun ω (p : ι × Set.Iic s) => B p.1 p.2 ω) P := by
  have := Fintype.ofFinite ι
  classical
  let X := fun (q : ι × ℝ≥0) ω => B q.1 (s+q.2) ω-B q.1 s ω
  let Y := fun (p : ι × Set.Iic s) ω => B p.1 p.2 ω
  have hG := ginibreBrownian_family_isGaussianProcess B P hB hind
  have hXY : IsGaussianProcess (Sum.elim X Y) P := by
    apply hG.of_isGaussianProcess
    intro q
    cases q with
    | inl q =>
      rcases q with ⟨i, t⟩
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
    (fun q => (hB q.1).aemeasurable (s+q.2) |>.sub ((hB q.1).aemeasurable s))
    (fun p => (hB p.1).aemeasurable p.2)
  intro q p
  rcases q with ⟨i, t⟩
  rcases p with ⟨j, v⟩
  have hXi : MemLp (X (i, t)) 2 P :=
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

/-- The family restarted at time `s`: coordinate `i` at time `t` is `B i (s + t) - B i s`. -/
def brownianFamilyShift {Ω ι : Type*} (B : ι → ℝ≥0 → Ω → ℝ) (s : ℝ≥0) :
    ι → ℝ≥0 → Ω → ℝ := fun i t ω => B i (s+t) ω-B i s ω

/-- Actual shifted coordinate paths are again an independent Brownian family. -/
theorem brownianFamilyShift_isBrownian_independent {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s : ℝ≥0) :
    (∀ i, IsBrownianReal (brownianFamilyShift B s i) P) ∧
      iIndepFun (fun i ω t => brownianFamilyShift B s i t ω) P := by
  have := Fintype.ofFinite ι
  refine ⟨fun i => (hB i).shift s,?_⟩
  exact hind.comp (fun i p t => p (s+t)-p s) (fun i => by
    apply Measurable.of_eval
    intro t
    exact (measurable_pi_apply (s+t)).sub (measurable_pi_apply s))

/-- The whole shifted Brownian family is independent of any actual completed-past
measurable random variable, not merely independent at a single increment time. -/
theorem brownianFamily_future_independent_augmented_variable {Ω ι A : Type*}
    [mAmbient : MeasurableSpace Ω] [Finite ι] [MeasurableSpace A]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s : ℝ≥0) (Y : Ω → A)
    (hY : @Measurable Ω A (ginibreBrownianAugmentedFiltration B P hB s) _ Y) :
    IndepFun (fun ω i t => brownianFamilyShift B s i t ω) Y P := by
  have := Fintype.ofFinite ι
  let X := fun ω (q : ι × ℝ≥0) => B q.1 (s+q.2) ω-B q.1 s ω
  have hx : Measurable X := by
    apply Measurable.of_eval
    intro q
    exact (aemeasurable_iff_measurable.mp ((hB q.1).aemeasurable (s+q.2))).sub
      (aemeasurable_iff_measurable.mp ((hB q.1).aemeasurable s))
  have hi : IndepFun X Y P := by
    apply indepFun_of_nullAugmented_measurable (mAmbient := mAmbient) P
      (ginibreBrownianFamilyPastSpace B s) (ginibreBrownianFamilyPastSpace_le B P hB s)
      X hx Y hY
    exact brownianFamily_whole_future_independent_past B P hB hind s
  have hm : Measurable (fun p : (ι × ℝ≥0) → ℝ => fun i t => p (i, t)) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro t
    exact measurable_pi_apply (i, t)
  exact hi.comp hm measurable_id

end
end GinibrePoincare
