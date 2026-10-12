/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.
import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
/-!
# The maximum principle and decaying classical harmonic functions

The scalar second derivative is nonpositive at a local maximum.

The Hessian quadratic form is nonpositive at a local maximum.
-/
public section
open Filter Set Metric
open scoped Topology
namespace LiebThirring
/-- The scalar second derivative is nonpositive at a local maximum. -/
lemma second_deriv_nonpos_at_local_max {f : ℝ → ℝ} {a : ℝ}
    (hf : ContDiffAt ℝ 2 f a) (hm : IsLocalMax f a) : iteratedDeriv 2 f a ≤ 0 := by
  obtain ⟨s, hs, _, hfs⟩ := (hf.contDiffWithinAt (s := univ)).contDiffOn (m := 2) le_rfl (by
    norm_num)
  have hs' : s ∈ 𝓝 a := by simpa using hs
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs'
  have ha : a ∈ ball a ε := mem_ball_self hε
  have hfb : ContDiffOn ℝ 2 f (ball a ε) := hfs.mono hεs
  have ht := Real.taylor_tendsto (convex_ball a ε) ha hfb
  have hp : ∀ t, taylorWithinEval f 2 (ball a ε) a t =
      f a + iteratedDeriv 2 f a / 2 * (t - a)^2 := by
    intro t
    rw [taylorWithinEval_succ f 1, taylorWithinEval_succ f 0, taylor_within_zero_eval]
    simp only [iteratedDerivWithin_of_isOpen isOpen_ball ha, smul_eq_mul]
    norm_num
    rw [hm.deriv_eq_zero]
    ring
  simp_rw [hp] at ht
  rw [nhdsWithin_eq_nhds.mpr (ball_mem_nhds a hε)] at ht
  have ht' := ht.mono_left (nhdsWithin_le_nhds (s := {a}ᶜ))
  have hm' : ∀ᶠ t in 𝓝[≠] a, f t ≤ f a := hm.filter_mono nhdsWithin_le_nhds
  have hle : (0 : ℝ) ≤ -(iteratedDeriv 2 f a / 2) := le_of_tendsto ht' (by
    filter_upwards [hm', eventually_mem_nhdsWithin] with t htm hta
    have hne : t - a ≠ 0 := sub_ne_zero.mpr hta
    have hsq : 0 < (t - a)^2 := sq_pos_of_ne_zero hne
    apply (div_le_iff₀ hsq).mpr
    nlinarith only [htm])
  linarith only [hle]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The Hessian quadratic form is nonpositive at a local maximum. -/
lemma hessian_nonpos_at_local_max {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) (v : E) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ 0 := by
  let l : ℝ → E := fun t => x + t • v
  have hl : ∀ t, HasDerivAt l v t := by
    intro t
    simpa only [one_smul, id_eq, l] using ((hasDerivAt_id t).smul_const v).const_add x
  have hl₀ : l 0 = x := by simp only [l, zero_smul, add_zero]
  have hfl : ContDiffAt ℝ 2 (f ∘ l) 0 := by
    have hf₀ : ContDiffAt ℝ 2 f (l 0) := hl₀.symm ▸ hf
    exact hf₀.comp 0 (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hm₀ : IsLocalMax (f ∘ l) 0 := by
    apply IsLocalMax.comp_continuous (g := l)
    · rwa [hl₀]
    · exact (hl 0).continuousAt
  have hd : deriv (f ∘ l) =ᶠ[𝓝 0] (fun t => fderiv ℝ f (l t) v) := by
    have htend : Tendsto l (𝓝 0) (𝓝 x) := by
      simpa only [ContinuousAt, hl₀] using (hl 0).continuousAt
    have hneigh := htend.eventually (hf.eventually (by norm_num))
    filter_upwards [hneigh] with t ht
    exact (ht.differentiableAt (by norm_num) |>.hasFDerivAt.comp_hasDerivAt t (hl t)).deriv
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  have hdd : HasDerivAt (fun t => fderiv ℝ f (l t) v)
      (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    have h₁ := (hdf.differentiableAt one_ne_zero).hasFDerivAt
    rw [← hl₀] at h₁
    simpa only [Function.comp_apply, add_zero, map_zero, hl₀] using
      (h₁.comp_hasDerivAt 0 (hl 0)).clm_apply (hasDerivAt_const 0 v)
  have hs := second_deriv_nonpos_at_local_max hfl hm₀
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    hd.deriv_eq, hdd.deriv] at hs
  exact hs

variable [FiniteDimensional ℝ E]
open InnerProductSpace Laplacian
/-- The Laplacian of a `C²` function is nonpositive at a local maximum. -/
lemma laplacian_nonpos_at_local_max {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) : Δ f x ≤ 0 := by
  classical
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_nonpos
  intro i _
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using
    hessian_nonpos_at_local_max hf hm ((stdOrthonormalBasis ℝ E) i)

/-- The Euclidean quadratic barrier has Laplacian twice the dimension. -/
lemma laplacian_norm_sq (x : E) : Δ (fun y : E => ‖y‖^2) x = 2 * Module.finrank ℝ E := by
  classical
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, fderiv_norm_sq]
  rw [fderiv_const_smul (innerSL ℝ (E := E)).differentiableAt]
  simp [ContinuousLinearMap.fderiv, innerSL, innerₛₗ, OrthonormalBasis.norm_eq_one]
  ring

/-- A function with positive Laplacian cannot have a local maximum. -/
lemma not_isLocalMax_of_laplacian_pos {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hΔ : 0 < Δ f x) : ¬ IsLocalMax f x :=
  fun hm => (not_lt_of_ge (laplacian_nonpos_at_local_max hf hm)) hΔ

variable [Nontrivial E]
/-- The maximum principle on a closed ball, proved with the quadratic barrier. -/
theorem le_of_laplacian_eq_zero_on_closedBall {h : E → ℝ} {c x : E} {R M : ℝ}
    (hR : 0 < R) (hh : ∀ y ∈ closedBall c R, ContDiffAt ℝ 2 h y)
    (hΔ : ∀ y ∈ ball c R, Δ h y = 0)
    (hbd : ∀ y ∈ sphere c R, h y ≤ M) (hx : x ∈ closedBall c R) : h x ≤ M := by
  have hbound : ∀ τ : ℝ, 0 < τ → h x ≤ M + τ * (‖c‖ + R)^2 := by
    intro τ hτ
    let q : E → ℝ := fun y => h y + τ * ‖y‖^2
    have hq : ∀ y ∈ closedBall c R, ContDiffAt ℝ 2 q y := by
      intro y hy
      exact (hh y hy).add ((contDiff_norm_sq ℝ).contDiffAt.const_smul τ)
    obtain ⟨y, hy, hmax⟩ := (isCompact_closedBall c R).exists_isMaxOn
      (nonempty_closedBall.mpr hR.le) (fun y hy => (hq y hy).continuousAt.continuousWithinAt)
    have hybd : y ∈ sphere c R := by
      apply mem_sphere.mpr
      apply le_antisymm (mem_closedBall.mp hy)
      by_contra hnot
      have hyin : y ∈ ball c R := mem_ball.mpr (lt_of_not_ge hnot)
      have hloc : IsLocalMax q y := hmax.isLocalMax
        (mem_of_superset (ball_mem_nhds y (sub_pos.mpr (mem_ball.mp hyin))) (by
          intro z hz
          apply mem_closedBall.mpr
          calc dist z c ≤ dist z y + dist y c := dist_triangle z y c
               _ ≤ R := by linarith only [mem_ball.mp hz]))
      have hlap : Δ q y = τ * (2 * Module.finrank ℝ E) := by
        calc
          Δ q y = Δ h y + Δ (τ • (fun z : E => ‖z‖^2)) y :=
            (hh y hy).laplacian_add ((contDiff_norm_sq ℝ).contDiffAt.const_smul τ)
          _ = τ * (2 * Module.finrank ℝ E) := by
            rw [hΔ y hyin, laplacian_smul τ (contDiff_norm_sq ℝ).contDiffAt, laplacian_norm_sq]
            simp only [zero_add, smul_eq_mul]
      have hpos : 0 < Δ q y := by
        rw [hlap]
        exact mul_pos hτ (mul_pos (by norm_num) (Nat.cast_pos.mpr Module.finrank_pos))
      exact not_isLocalMax_of_laplacian_pos (hq y hy) hpos hloc
    have hyn : ‖y‖ ≤ ‖c‖ + R := by
      calc ‖y‖ ≤ ‖y - c‖ + ‖c‖ := norm_le_norm_sub_add y c
           _ = ‖c‖ + R := by rw [← dist_eq_norm, mem_sphere.mp hybd]; ring
    have hsq : ‖y‖^2 ≤ (‖c‖ + R)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hyn 2
    have hcomp := hmax hx
    have hboundary := hbd y hybd
    have hbarrier : τ * ‖y‖^2 ≤ τ * (‖c‖ + R)^2 := mul_le_mul_of_nonneg_left hsq hτ.le
    have hxpos : 0 ≤ τ * ‖x‖^2 := mul_nonneg hτ.le (sq_nonneg _)
    change h x + τ * ‖x‖^2 ≤ h y + τ * ‖y‖^2 at hcomp
    linarith only [hcomp, hboundary, hbarrier, hxpos]
  have hτlim : Tendsto (fun τ : ℝ => τ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hclim : Tendsto (fun _ : ℝ => M) (𝓝[>] 0) (𝓝 M) := tendsto_const_nhds
  apply ge_of_tendsto (x := 𝓝[>] (0 : ℝ))
    (show Tendsto (fun τ : ℝ => M + τ * (‖c‖ + R)^2) (𝓝[>] 0) (𝓝 M) from by
      simpa only [zero_mul, add_zero] using hclim.add (hτlim.mul_const ((‖c‖ + R)^2)))
  filter_upwards [eventually_mem_nhdsWithin] with τ hτ
  exact hbound τ hτ

/-- A globally `C²` harmonic function decaying at infinity is nonpositive. -/
theorem nonpos_of_laplacian_eq_zero_of_tendsto {h : E → ℝ}
    (hh : ContDiff ℝ 2 h) (hΔ : ∀ x, Δ h x = 0)
    (hd : Tendsto h (cocompact E) (𝓝 0)) (x : E) : h x ≤ 0 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have he : ∀ᶠ y in cocompact E, h y < ε := hd.eventually (Iio_mem_nhds hε)
  obtain ⟨K, hK, hKe⟩ := mem_cocompact.mp he
  obtain ⟨A, hKA⟩ := hK.isBounded.subset_closedBall (0 : E)
  let R : ℝ := max A ‖x‖ + 1
  have hR : 0 < R := by
    have hm := le_max_right A ‖x‖
    have hx₀ := norm_nonneg x
    dsimp only [R]
    linarith only [hm, hx₀]
  have hxR : x ∈ closedBall (0 : E) R := by
    rw [mem_closedBall_zero_iff]
    exact (le_max_right A ‖x‖).trans (le_add_of_nonneg_right zero_le_one)
  have hbd : ∀ y ∈ sphere (0 : E) R, h y ≤ ε := by
    intro y hy
    refine le_of_lt (hKe ?_)
    intro hyK
    have hyA := mem_closedBall_zero_iff.mp (hKA hyK)
    have hyR : ‖y‖ = R := by simpa only [mem_sphere, dist_zero_right] using hy
    have hAR := le_max_left A ‖x‖
    dsimp only [R] at hyR
    linarith only [hyA, hyR, hAR]
  simpa only [zero_add] using le_of_laplacian_eq_zero_on_closedBall hR
    (fun y _ => hh.contDiffAt) (fun y _ => hΔ y) hbd hxR

/-- Uniqueness for classical harmonic functions decaying at infinity. -/
theorem eq_zero_of_laplacian_eq_zero_of_tendsto {h : E → ℝ}
    (hh : ContDiff ℝ 2 h) (hΔ : ∀ x, Δ h x = 0)
    (hd : Tendsto h (cocompact E) (𝓝 0)) : h = 0 := by
  funext x
  apply le_antisymm (nonpos_of_laplacian_eq_zero_of_tendsto hh hΔ hd x)
  have hnΔ : ∀ y, Δ (-h) y = 0 := by simp only [laplacian_neg, Pi.neg_apply, hΔ, neg_zero,
    implies_true]
  have hnd : Tendsto (-h) (cocompact E) (𝓝 0) := by simpa only [neg_zero, Pi.neg_def] using hd.neg
  have hn := nonpos_of_laplacian_eq_zero_of_tendsto hh.neg hnΔ hnd x
  simpa only [Pi.neg_apply, neg_nonpos] using hn
end LiebThirring
end
