/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.TwoFormPoincare
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SmoothCutoff

/-!
# The smooth Poincaré lemma for two-forms on a ball

A closed two-form that is smooth only on an open set has, near every point, a
globally smooth one-form primitive.  The form is cut off by a smooth bump
equal to one on a small ball; the radial homotopy primitive of the cut-off form
is smooth, and closedness is needed only along radial segments inside that ball.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology ContDiff Interval

namespace SGPT.Foundations.Analysis.Pending.LocalPotentials

noncomputable section

universe u

/-- A finite interval integral of a jointly smooth integrand is smooth in the
parameter.  Both spaces lie in one universe so that the induction may pass
to the space of derivatives. -/
theorem contDiff_intervalIntegral_of_contDiff
    {H F : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {G : H → ℝ → F} (hG : ContDiff ℝ ∞ G.uncurry) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x ↦ ∫ t in a..b, G x t) := by
  rw [contDiff_infty]
  intro m
  induction m generalizing F with
  | zero =>
    exact contDiff_zero.2
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hG.continuous a b)
  | succ m ih =>
    let G' : H → ℝ → H →L[ℝ] F := fun x t ↦ fderiv ℝ (fun y ↦ G y t) x
    have hG' : ContDiff ℝ ∞ G'.uncurry :=
      (hG.comp (by fun_prop : ContDiff ℝ ∞
        (fun q : (H × ℝ) × H ↦ (q.2, q.1.2)))).fderiv
          (g := fun p : H × ℝ ↦ p.1) contDiff_fst (by simp)
    have hder : ∀ x t, HasFDerivAt (fun y ↦ G y t) (G' x t) x := fun x t ↦
      ((hG.comp (by fun_prop : ContDiff ℝ ∞ (fun y : H ↦ (y, t)))).differentiable
        (by simp) x).hasFDerivAt
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    exact ⟨fun x ↦ ∫ t in a..b, G' x t, ih hG', fun x ↦
      hasFDerivAt_intervalIntegral_of_jointly_continuous hG.continuous
        hG'.continuous hder x a b⟩

/-- The radial homotopy primitive of a globally smooth two-form is smooth. -/
theorem contDiff_radialTwoFormPrimitive
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (a : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z : E) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (radialTwoFormPrimitive a z) :=
  contDiff_intervalIntegral_of_contDiff (contDiff_radialTwoFormIntegrand a z ha) 0 1

/-- **Smooth Poincaré lemma for two-forms.**  A two-form that is smooth and
closed on an open set has, on some ball about any of its points, a primitive
given by a globally smooth one-form. -/
theorem exists_smooth_local_twoForm_primitive
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (a : E → E [⋀^Fin 2]→L[ℝ] ℝ)
    (ha : ContDiffOn ℝ ∞ a U) (hclosed : ∀ y ∈ U, extDeriv a y = 0)
    {z : E} (hz : z ∈ U) :
    ∃ ε > 0, ball z ε ⊆ U ∧ ∃ S : E → E [⋀^Fin 1]→L[ℝ] ℝ,
      ContDiff ℝ ∞ S ∧ ∀ x ∈ ball z ε, extDeriv S x = a x := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU z hz
  let χ : ContDiffBump z := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  let b : E → E [⋀^Fin 2]→L[ℝ] ℝ := fun y ↦ χ y • a y
  have hsupp : tsupport χ ⊆ U := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_ball (by simp [χ]; linarith)).trans hδU
  have hb : ContDiff ℝ ∞ b := SmoothCutoff.contDiff_smul_of_tsupport_subset hU χ.contDiff hsupp ha
  have heq : EqOn b a (ball z (δ / 4)) := fun y hy ↦ by
    simp [b, χ.one_of_mem_closedBall (ball_subset_closedBall hy)]
  have hsmall : ball z (δ / 4) ⊆ U := (ball_subset_ball (by linarith)).trans hδU
  refine ⟨δ / 4, by positivity, hsmall, radialTwoFormPrimitive b z,
    contDiff_radialTwoFormPrimitive b z hb, fun x hx ↦ ?_⟩
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, z + t • (x - z) ∈ ball z (δ / 4) := fun t ht ↦
    (convex_ball z (δ / 4)).add_smul_sub_mem (mem_ball_self (by positivity)) hx ht
  rw [extDeriv_radialTwoFormPrimitive_of_closed_segment b z x hb fun t ht ↦ ?_]
  · exact heq hx
  · have hev : b =ᶠ[𝓝 (z + t • (x - z))] a :=
      eventually_of_mem (isOpen_ball.mem_nhds (hseg t ht)) heq
    rw [hev.extDeriv_eq]
    exact hclosed _ (hsmall (hseg t ht))

end

end SGPT.Foundations.Analysis.Pending.LocalPotentials
