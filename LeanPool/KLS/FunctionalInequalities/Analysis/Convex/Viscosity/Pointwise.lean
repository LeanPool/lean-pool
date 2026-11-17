/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Viscosity.Touching

/-!
# Pointwise Monge–Ampère identification from quadratic expansion

Supporting the convex Monge–Ampère infrastructure for Letwin
arXiv:2607.24164v1 Lemma 2.2. The declarations retain their original
source hypotheses, dimensional scope and mathematical conclusions.
-/

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein

section AlexandrovPointEquation

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein

/-! At a point of second-order expansion the Monge–Ampère equation holds pointwise with a positive
definite Hessian. -/

namespace FunctionalInequalities.Analysis

private lemma quadraticAt_shift_sub {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n))
    (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    quadraticAt (A - t • 1) x₀ b c x =
      quadraticAt A x₀ b c x - t / 2 * ‖x - x₀‖ ^ 2 := by
  simpa only [neg_smul, sub_eq_add_neg, neg_div, neg_mul] using
    quadraticAt_shift A x₀ b c x (-t)

private lemma posSemidef_sub_eventually {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) :
    ∀ᶠ t : ℝ in 𝓝 0, (B - t • 1).PosSemidef := by
  have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, t < hB.1.eigenvalues i :=
    eventually_all.mpr (fun i => eventually_lt_nhds (hB.eigenvalues_pos i))
  filter_upwards [he] with t ht
  let U := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) hB.1.eigenvectorUnitary
  have hd : (Matrix.diagonal (fun i => hB.1.eigenvalues i - t)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => le_of_lt (sub_pos.mpr (ht i)))
  have hc : Matrix.diagonal (fun _ : Fin n => t) = t • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  have heq : B - t • 1 = U (Matrix.diagonal (fun i => hB.1.eigenvalues i - t)) := by
    rw [← Matrix.diagonal_sub, map_sub, hc, map_smul, map_one]
    congr 1
    simpa [U, Function.comp_def] using hB.1.spectral_theorem
  rw [heq]
  exact hd.mul_mul_conjTranspose_same _

private lemma quadratic_upper_test_of_expansion {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ g : EuclideanSpace ℝ (Fin n)}
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (hexp : ∀ ε > 0, ∀ᶠ x in 𝓝 x₀,
      |u x - quadraticAt B x₀ g (u x₀) x| ≤ ε * ‖x - x₀‖ ^ 2)
    {t : ℝ} (ht : 0 < t) :
    (B + t • 1).IsHermitian ∧
      ContDiffAt ℝ 2 (quadraticAt (B + t • 1) x₀ g (u x₀)) x₀ ∧
      u x₀ = quadraticAt (B + t • 1) x₀ g (u x₀) x₀ ∧
      ∀ᶠ x in 𝓝 x₀, u x ≤ quadraticAt (B + t • 1) x₀ g (u x₀) x := by
  refine ⟨hB.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all t)),
    (contDiff_quadraticAt (B + t • 1) x₀ g (u x₀)).contDiffAt, by simp [quadraticAt], ?_⟩
  filter_upwards [hexp (t / 2) (by positivity)] with x hx
  rw [quadraticAt_shift]
  have hh := (abs_le.mp hx).2
  linarith

theorem posSemidef_of_quadratic_expansion {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u)
    {x₀ g : EuclideanSpace ℝ (Fin n)} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian)
    (hexp : ∀ ε > 0, ∀ᶠ x in 𝓝 x₀,
      |u x - quadraticAt B x₀ g (u x₀) x| ≤ ε * ‖x - x₀‖ ^ 2) :
    B.PosSemidef := by
  apply posSemidef_of_positive_shifts hB
  intro t ht
  obtain ⟨hs, hψ, hc, htouch⟩ := quadratic_upper_test_of_expansion hB hexp ht
  have hp := posSemidef_hessianMatrix_of_upper_touch hconv hψ hc htouch
  rwa [hessianMatrix_quadraticAt hs] at hp

/--
**The Monge–Ampère equation at points of second-order differentiability**: if the subgradient
images of the convex `u` on open subsets of `Ω` carry the density `f`,
`f` is continuous and positive at `x₀ ∈ Ω`, and `u` has a second-order expansion at `x₀` with a
symmetric
matrix `B` (`|u x − (u x₀ + ⟪g, x − x₀⟫ + ½ ⟪x − x₀, B (x − x₀)⟫)| ≤ ε ‖x − x₀‖²` near `x₀` for
every
`ε > 0`), then `B` is positive definite and `det B = f x₀`. -/
theorem posDef_and_det_eq_of_quadratic_expansion {n : ℕ} {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hMA :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen G →
          G ⊆ Ω →
            (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
              ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (hf : ContinuousAt f x₀) (hfpos : 0 < f x₀)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) {g : EuclideanSpace ℝ (Fin n)}
    (hexp : ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, |u x - quadraticAt B x₀ g (u x₀) x| ≤ ε * ‖x - x₀‖ ^ 2) :
    B.PosDef ∧ B.det = f x₀ := by
  have hu : ∀ t : ℝ, 0 < t → f x₀ ≤ (B + t • 1).det := by
    intro t ht
    obtain ⟨hs, hψ, hc, htouch⟩ := quadratic_upper_test_of_expansion hB hexp ht
    have hd := le_det_hessianMatrix_of_upper_touch hconv hΩ hMA hx₀ hf hψ hc htouch
    rwa [hessianMatrix_quadraticAt hs] at hd
  have hplus : Continuous (fun t : ℝ => B + t • 1) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hdet_lower : f x₀ ≤ B.det := by
    have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, f x₀ ≤ (B + t • 1).det := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hu t ht
    simpa using
      ge_of_tendsto
        (hplus.matrix_det.continuousAt.tendsto.mono_left
          (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0)))
        hh
  have hps : B.PosSemidef := posSemidef_of_quadratic_expansion hconv hB hexp
  have hpd : B.PosDef :=
    hps.posDef_iff_det_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hfpos hdet_lower))
  refine ⟨hpd, le_antisymm ?_ hdet_lower⟩
  have hlower : ∀ᶠ t : ℝ in 𝓝[>] 0, (B - t • 1).det ≤ f x₀ := by
    have he : ∀ᶠ t : ℝ in 𝓝[>] 0, (B - t • 1).PosSemidef :=
      (posSemidef_sub_eventually hpd).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, he] with t ht hpt
    have hc : u x₀ = quadraticAt (B - t • 1) x₀ g (u x₀) x₀ := by simp [quadraticAt]
    have htouch : ∀ᶠ x in 𝓝 x₀, quadraticAt (B - t • 1) x₀ g (u x₀) x ≤ u x := by
      filter_upwards [hexp (t / 2) (by exact div_pos ht (by norm_num))] with x hx
      rw [quadraticAt_shift_sub]
      have hh := (abs_le.mp hx).1
      linarith
    have hψ : ContDiffAt ℝ 2 (quadraticAt (B - t • 1) x₀ g (u x₀)) x₀ :=
      (contDiff_quadraticAt (B - t • 1) x₀ g (u x₀)).contDiffAt
    have hH : (hessianMatrix (quadraticAt (B - t • 1) x₀ g (u x₀)) x₀).PosSemidef := by
      rw [hessianMatrix_quadraticAt hpt.1]
      exact hpt
    have hd := det_hessianMatrix_le_of_lower_touch hconv hΩ hMA hx₀ hf hfpos.le hψ hH hc htouch
    rwa [hessianMatrix_quadraticAt hpt.1] at hd
  have hminus : Continuous (fun t : ℝ => B - t • 1) :=
    continuous_const.sub (continuous_id.smul continuous_const)
  simpa using
    le_of_tendsto
      (hminus.matrix_det.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0)))
      hlower

end FunctionalInequalities.Analysis

end AlexandrovPointEquation
