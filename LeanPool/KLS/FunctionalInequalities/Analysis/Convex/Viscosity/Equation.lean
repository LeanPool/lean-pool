/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Viscosity.Pointwise
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.SecondOrder.Expansion

/-!
# Almost-everywhere Monge–Ampère identification

Supporting the convex Monge–Ampère infrastructure for Letwin
arXiv:2607.24164v1 Lemma 2.2. The declarations retain their original
source hypotheses, dimensional scope and mathematical conclusions.
-/

@[expose] public section

noncomputable section

section AeMongeAmpere
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein


open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein

/-! **The Monge–Ampère equation almost everywhere**: an Alexandrov solution has, at almost every
point, a quadratic expansion with positive definite Hessian whose determinant equals the density. -/

namespace FunctionalInequalities.Analysis

/-- Coordinate conversion shared by the value and gradient-derivative producers. -/
private theorem quadraticAt_expansion_of_linear_expansion {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x p : EuclideanSpace ℝ (Fin n)}
    {B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hsym : ∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫)
    (hexp : ∀ ε > 0, ∀ᶠ y in 𝓝 x,
      |u y - u x - ⟪p, y - x⟫ - (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian ∧
      (Matrix.toEuclideanLin A).toContinuousLinearMap = B ∧
      ∀ ε > 0, ∀ᶠ y in 𝓝 x,
        |u y - quadraticAt A x p (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  let A : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.toEuclideanLin.symm
      (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  have hA : Matrix.toEuclideanLin A =
      (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :=
    Matrix.toEuclideanLin.apply_symm_apply _
  have hHermitian : A.IsHermitian := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    rw [hA]
    exact hsym
  have hquad (v : EuclideanSpace ℝ (Fin n)) :
      ⟪v, Matrix.toEuclideanLin A v⟫ = ⟪B v, v⟫ := by
    rw [hA]
    exact real_inner_comm (B v) v
  refine ⟨A, hHermitian, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L => L v) hA
  · intro ε hε
    filter_upwards [hexp ε hε] with y hy
    simpa only [quadraticAt, hquad, sub_add_eq_sub_sub] using hy

/-- **Alexandrov's theorem in coordinates**: a convex function on
`EuclideanSpace ℝ (Fin n)` has, at almost every point `x`, a second-order expansion
`|u y − quadraticAt B x g (u x) y| ≤ ε ‖y − x‖²` near `x` with a symmetric matrix `B`. -/
theorem ae_exists_quadraticAt_expansion {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ ∃ g : EuclideanSpace ℝ (Fin n),
        ∀ ε > 0, ∀ᶠ y in 𝓝 x, |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  filter_upwards [ae_exists_secondOrder_expansion hconv] with x hx
  rcases hx with ⟨p, B, hsym, _, hexp⟩
  obtain ⟨A, hA, _hAB, hquad⟩ := quadraticAt_expansion_of_linear_expansion hsym hexp
  exact ⟨A, hA, p, hquad⟩

/-- A globally convex function differentiable only on an open domain has a.e.
a genuine gradient derivative and expansion with the SAME coordinate matrix there.
No global differentiability/extension, C11 or W2p input. -/
theorem ae_exists_gradient_quadraticAt_expansion_on_open {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hdiff : DifferentiableOn ℝ u Ω) :
    ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω),
      ∃ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian ∧
        HasFDerivAt (gradient u) (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
        ∀ ε > 0, ∀ᶠ y in 𝓝 x,
          |u y - quadraticAt A x (gradient u x) (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  filter_upwards [ae_exists_gradient_secondOrder_expansion_on_open hconv hΩ hdiff] with x hx
  obtain ⟨B, hB, hd, hvalue⟩ := hx
  obtain ⟨A, hA, hAB, hquad⟩ := quadraticAt_expansion_of_linear_expansion hB hvalue
  exact ⟨A, hA, hAB.symm ▸ hd, hquad⟩

/-- The global gradient/quadratic theorem is the meaningful univ specialization
of the same local coordinate production, with its original public type. -/
theorem ae_exists_gradient_quadraticAt_expansion {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) (hdiff : Differentiable ℝ u) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian ∧
        HasFDerivAt (gradient u) (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
        ∀ ε > 0, ∀ᶠ y in 𝓝 x,
          |u y - quadraticAt A x (gradient u x) (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  simpa only [Measure.restrict_univ] using
    ae_exists_gradient_quadraticAt_expansion_on_open hconv isOpen_univ hdiff.differentiableOn

/-- Actual local MA equations identify the determinant of the SAME genuine
almost-everywhere gradient derivative matrix. Includes n=0; no Hessian/W2p input. -/
theorem ae_exists_gradient_posDef_det_eq_on_open {n : ℕ}
    {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hdiff : DifferentiableOn ℝ u Ω)
    (hf : ContinuousOn f Ω) (hfpos : ∀ x ∈ Ω, 0 < f x)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      volume (subgradientImage u G) = ∫⁻ y in G, ENNReal.ofReal (f y)) :
    ∀ᵐ x ∂(volume.restrict Ω),
      ∃ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian ∧ A.PosDef ∧ A.det = f x ∧
        HasFDerivAt (gradient u) (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
        ∀ ε > 0, ∀ᶠ y in 𝓝 x,
          |u y - quadraticAt A x (gradient u x) (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  filter_upwards [ae_exists_gradient_quadraticAt_expansion_on_open hconv hΩ hdiff,
    ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
  obtain ⟨A, hA, hd, hquad⟩ := hx
  obtain ⟨hp, hdet⟩ := posDef_and_det_eq_of_quadratic_expansion hconv hΩ hMA hxΩ
    (hf.continuousAt (hΩ.mem_nhds hxΩ)) (hfpos x hxΩ) hA hquad
  exact ⟨A, hA, hp, hdet, hd, hquad⟩

/-- Domain-relative Monge–Ampère localization for a strictly convex `C¹` function.
The matrix in the conclusion is simultaneously the positive definite determinant
matrix, the derivative of the genuine gradient, and the quadratic expansion matrix. -/
theorem ae_exists_gradient_posDef_det_eq_of_strictConvexOn {n : ℕ}
    {v f : EuclideanSpace ℝ (Fin n) → ℝ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hstrict : StrictConvexOn ℝ Ω v) (hv : ContDiffOn ℝ 1 v Ω) (hf : ContinuousOn f Ω)
    (hfpos : ∀ x ∈ Ω, 0 < f x)
    (hMA :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen G →
          G ⊆ Ω →
            volume {p | ∃ x ∈ G, ∀ y ∈ Ω, v x + ⟪p, y - x⟫ ≤ v y} =
              ∫⁻ y in G, ENNReal.ofReal (f y)) :
    ∀ᵐ x ∂(volume.restrict Ω),
      ∃ A : Matrix (Fin n) (Fin n) ℝ,
        A.IsHermitian ∧
          A.PosDef ∧
            A.det = f x ∧
              HasFDerivAt (gradient v) (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
                ∀ ε > 0,
                  ∀ᶠ y in 𝓝 x,
                    |v y - quadraticAt A x (gradient v x) (v x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  let E := EuclideanSpace ℝ (Fin n)
  let P : E → Prop := fun x =>
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      A.IsHermitian ∧
        A.PosDef ∧
          A.det = f x ∧
            HasFDerivAt (gradient v) (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
              ∀ ε > 0,
                ∀ᶠ y in 𝓝 x, |v y - quadraticAt A x (gradient v x) (v x) y| ≤ ε * ‖y - x‖ ^ 2
  obtain ⟨R, r, hRpos, hRsub, hrcountable, hcover⟩ := exists_countable_buffered_ball_cover hΩ
  have hlocal :
    ∀ c : E,
      ∀ r : ℝ, 0 < r → closedBall c r ⊆ Ω → ∀ᵐ x ∂(volume.restrict (ball c (r / 2))), P x := by
    intro c r hr hcr
    let K : Set E := closedBall c r
    let U : Set E := ball c (r / 2)
    have hKcompact : IsCompact K := isCompact_closedBall c r
    have hKnonempty : K.Nonempty := ⟨c, by simp [K, hr.le]⟩
    have hKΩ : K ⊆ Ω := by simpa [K] using hcr
    obtain ⟨V, hVconv, hVK, hVimage⟩ :=
      exists_compact_convex_extension hΩ hstrict hv hKcompact hKnonempty hKΩ
    have hUopen : IsOpen U := isOpen_ball
    have hUsub : U ⊆ interior K := by
      intro x hx
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
      refine ⟨r / 2, by linarith, ?_⟩
      intro y hy
      change dist y c ≤ r
      have hx' : dist x c < r / 2 := by simpa [U] using hx
      have hy' : dist y x < r / 2 := by exact hy
      linarith [dist_triangle y x c]
    have hVeq : ∀ x ∈ U, V =ᶠ[𝓝 x] v := by
      intro x hx
      filter_upwards [hUopen.mem_nhds hx] with y hy
      exact hVK y (interior_subset (hUsub hy))
    have hUΩ : U ⊆ Ω := hUsub.trans (interior_subset.trans hKΩ)
    have hVdiff : DifferentiableOn ℝ V U := by
      intro x hx
      have hdv :=
        ((hv.differentiableOn one_ne_zero) x (hUΩ hx)).differentiableAt (hΩ.mem_nhds (hUΩ hx))
      exact
        (hdv.hasFDerivAt.congr_of_eventuallyEq
            (hVeq x hx)).differentiableAt.differentiableWithinAt
    have hgradEq : ∀ x ∈ U, gradient V x = gradient v x := by
      intro x hx
      exact (hVeq x hx).gradient_eq
    have hVMA :
      ∀ G : Set E,
        IsOpen G → G ⊆ U → volume (subgradientImage V G) = ∫⁻ y in G, ENNReal.ofReal (f y) := by
      intro G hGopen hGU
      rw [hVimage G (hGU.trans hUsub)]
      exact hMA G hGopen (hGU.trans hUΩ)
    have hfU : ContinuousOn f U := hf.mono hUΩ
    have hfposU : ∀ x ∈ U, 0 < f x := by
      intro x hx
      exact hfpos x (hUΩ hx)
    have hglobal :=
      ae_exists_gradient_posDef_det_eq_on_open hVconv hUopen hVdiff hfU hfposU hVMA
    have hlocal' : ∀ᵐ x ∂(volume.restrict U), P x := by
      filter_upwards [hglobal, ae_restrict_mem hUopen.measurableSet] with x hx hxU
      obtain ⟨A, hA, hPD, hdet, hdV, hquadV⟩ := hx
      have hgradEv : gradient V =ᶠ[𝓝 x] gradient v := by
        filter_upwards [hUopen.mem_nhds hxU] with y hy
        exact hgradEq y hy
      have hdv : HasFDerivAt (gradient v) (Matrix.toEuclideanLin A).toContinuousLinearMap x :=
        hdV.congr_of_eventuallyEq hgradEv.symm
      have hquad :
        ∀ ε > 0,
          ∀ᶠ y in 𝓝 x, |v y - quadraticAt A x (gradient v x) (v x) y| ≤ ε * ‖y - x‖ ^ 2 := by
        intro ε hε
        filter_upwards [hquadV ε hε, hVeq x hxU] with y hy hyeq
        rw [hyeq, hgradEq x hxU, hVK x (interior_subset (hUsub hxU))] at hy
        exact hy
      exact ⟨A, hA, hPD, hdet, hdv, hquad⟩
    exact hlocal'
  let : Countable { x : Ω // x ∈ r } := hrcountable.to_subtype
  have hlocalall :
    ∀ᵐ x ∂(volume : Measure E),
      ∀ i : { x : Ω // x ∈ r }, x ∈ ball (i.val : E) (R i.val / 2) → P x := by
    rw [ae_all_iff]
    intro i
    have hi := hlocal (i.val : E) (R i.val) (hRpos i.val) (hRsub i.val)
    exact (ae_restrict_iff' isOpen_ball.measurableSet).1 hi
  have hΩP : ∀ᵐ x ∂(volume : Measure E), x ∈ Ω → P x := by
    filter_upwards [hlocalall] with x hxall hxΩ
    rcases mem_iUnion.mp (hcover hxΩ) with ⟨z, hz⟩
    rcases mem_iUnion.mp hz with ⟨hzr, hzx⟩
    exact hxall ⟨z, hzr⟩ hzx
  rw [ae_restrict_iff' hΩ.measurableSet]
  exact hΩP


/-- The old global-differentiability interface is the actual on-domain
specialization of the local same-matrix MA producer. -/
theorem ae_exists_gradient_posDef_det_eq {n : ℕ}
    {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) (hdiff : Differentiable ℝ u)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hf : ContinuousOn f Ω) (hfpos : ∀ x ∈ Ω, 0 < f x)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      volume (subgradientImage u G) = ∫⁻ y in G, ENNReal.ofReal (f y)) :
    ∀ᵐ x ∂(volume.restrict Ω),
      ∃ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian ∧ A.PosDef ∧ A.det = f x ∧
        HasFDerivAt (gradient u) (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
        ∀ ε > 0, ∀ᶠ y in 𝓝 x,
          |u y - quadraticAt A x (gradient u x) (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  exact ae_exists_gradient_posDef_det_eq_on_open hconv hΩ hdiff.differentiableOn hf hfpos hMA

/-- **The a.e. Monge–Ampère equation for an Alexandrov solution**:
if the subgradient images of the convex `u` on open sets carry a continuous positive density `f`,
then at
almost every point `u` has a second-order expansion with a positive definite symmetric `B`, `det B =
f x`. -/
theorem ae_exists_posDef_det_eq {n : ℕ} {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) (hf : Continuous f) (hfpos : ∀ x, 0 < f x)
    (hMA :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen G →
          (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
            ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ,
        B.IsHermitian ∧
          B.PosDef ∧
            B.det = f x ∧
              ∃ g : EuclideanSpace ℝ (Fin n),
                ∀ ε > 0, ∀ᶠ y in 𝓝 x, |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  filter_upwards [ae_exists_quadraticAt_expansion hconv] with x hx
  rcases hx with ⟨B, hB, g, hexp⟩
  have hresult : B.PosDef ∧ B.det = f x :=
    posDef_and_det_eq_of_quadratic_expansion hconv (Ω := univ) isOpen_univ
      (fun G hG _ => hMA G hG) (mem_univ x) hf.continuousAt (hfpos x) hB hexp
  exact ⟨B, hB, hresult.1, hresult.2, g, hexp⟩

end FunctionalInequalities.Analysis

end AeMongeAmpere
