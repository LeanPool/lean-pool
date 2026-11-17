/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Existence

/-!
# Affine transport and compactness of supporting images

Supporting convex infrastructure for Letwin arXiv:2607.24164v1
Theorem 1.2 and Lemma 2.2. Mathematical scopes and source attributions
are retained in the individual declarations.
-/

@[expose] public section

section
open Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

section DomainAffineTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma affineEquiv_linear_sub
    (e : E ≃ᵃ[ℝ] E) (a b : E) :
    (e.linear : E →ₗ[ℝ] E) (a - b) = e a - e b := by
  change (AffineEquiv.toAffineMap e).linear (a - b) =
    (AffineEquiv.toAffineMap e) a - (AffineEquiv.toAffineMap e) b
  exact (AffineEquiv.toAffineMap e).linear_apply_vsub a b

variable [FiniteDimensional ℝ E]

/-- Domain-relative affine covariance of the supporting-slope image. -/
theorem subgradientImageOn_comp_affineEquiv_symm
    (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (D G : Set E) :
    subgradientImageOn (u ∘ e.symm) (e '' D) (e '' G) =
      (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E)) ''
        subgradientImageOn u D G := by
  ext q
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, hq⟩
    let p : E :=
      LinearMap.adjoint (e.linear : E →ₗ[ℝ] E) q
    have hcomp :
        (e.linear : E →ₗ[ℝ] E) ∘ₗ
            (e.linear.symm : E →ₗ[ℝ] E) =
          LinearMap.id := by
      ext v
      simp
    have hadjcomp :
        LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) ∘ₗ
            LinearMap.adjoint (e.linear : E →ₗ[ℝ] E) =
          LinearMap.id := by
      calc
        LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) ∘ₗ
              LinearMap.adjoint (e.linear : E →ₗ[ℝ] E) =
            LinearMap.adjoint
              ((e.linear : E →ₗ[ℝ] E) ∘ₗ
                (e.linear.symm : E →ₗ[ℝ] E)) :=
          (LinearMap.adjoint_comp (e.linear : E →ₗ[ℝ] E)
            (e.linear.symm : E →ₗ[ℝ] E)).symm
        _ = LinearMap.adjoint LinearMap.id := by rw [hcomp]
        _ = LinearMap.id := LinearMap.adjoint_id
    have hadj :
        LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) p = q := by
      have h := congrArg
        (fun f : E →ₗ[ℝ] E => f q) hadjcomp
      simpa [p] using h
    have hp : p ∈ subgradientImageOn u D G := by
      refine ⟨x, hx, ?_⟩
      intro y hy
      have hi :
          inner ℝ q (e y - e x) =
            inner ℝ p (y - x) := by
        calc
          inner ℝ q (e y - e x) =
              inner ℝ ((e.linear : E →ₗ[ℝ] E) (y - x)) q := by
            rw [affineEquiv_linear_sub e y x]
            exact (real_inner_comm q (e y - e x)).symm
          _ = inner ℝ (y - x) p := by
            simpa [p] using
              (LinearMap.adjoint_inner_right
                (e.linear : E →ₗ[ℝ] E) (y - x) q).symm
          _ = inner ℝ p (y - x) :=
            real_inner_comm p (y - x)
      calc
        u x + inner ℝ p (y - x) =
            u x + inner ℝ q (e y - e x) := by rw [hi]
        _ ≤ u y := by
          simpa only [Function.comp_apply, e.symm_apply_apply] using
            hq (e y) ⟨y, hy, rfl⟩
    exact ⟨p, hp, hadj⟩
  · rintro ⟨p, ⟨x, hx, hpx⟩, rfl⟩
    refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    have hlin :
        (e.symm.linear : E →ₗ[ℝ] E) =
          (e.linear.symm : E →ₗ[ℝ] E) := by
      ext v
      simp
    have hv :
        (e.linear.symm : E →ₗ[ℝ] E) (e y - e x) = y - x := by
      calc
        (e.linear.symm : E →ₗ[ℝ] E) (e y - e x) =
            (e.symm.linear : E →ₗ[ℝ] E) (e y - e x) := by
              rw [hlin]
        _ = e.symm (e y) - e.symm (e x) :=
          affineEquiv_linear_sub e.symm (e y) (e x)
        _ = y - x := by simp
    have hi :
        inner ℝ
            (LinearMap.adjoint
              (e.linear.symm : E →ₗ[ℝ] E) p)
            (e y - e x) =
          inner ℝ p (y - x) := by
      calc
        inner ℝ
            (LinearMap.adjoint
              (e.linear.symm : E →ₗ[ℝ] E) p)
            (e y - e x) =
            inner ℝ (e y - e x)
              (LinearMap.adjoint
                (e.linear.symm : E →ₗ[ℝ] E) p) := by
          rw [real_inner_comm]
        _ = inner ℝ
              ((e.linear.symm : E →ₗ[ℝ] E) (e y - e x)) p :=
          LinearMap.adjoint_inner_right
            (e.linear.symm : E →ₗ[ℝ] E) (e y - e x) p
        _ = inner ℝ (y - x) p := by rw [hv]
        _ = inner ℝ p (y - x) := real_inner_comm p (y - x)
    simpa only [Function.comp_apply, e.symm_apply_apply, hi] using
      hpx y hy

end DomainAffineTransport

section CompactImages
open Set Metric
open scoped Topology


/-- Actual domain supporting slopes based on a compact subset of an open C0
convex domain form a compact set. The bound and closed graph are produced, not
assumed; empty compact sets and zero dimension are included. -/
theorem isCompact_subgradientImageOn_of_isCompact {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {v : E → ℝ} {Ω K : Set E} (hΩ : IsOpen Ω)
    (hv : ConvexOn ℝ Ω v) (hvc : ContinuousOn v Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsCompact (subgradientImageOn v Ω K) := by
  obtain ⟨R, _hR, _hex, hbound⟩ := exists_uniform_subgradient_bound_on_compact hΩ hv hvc hK hKΩ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A : Set (K × E) :=
    {q | q.2 ∈ closedBall (0 : E) R ∧ ∀ y ∈ Ω, v q.1.val + ⟪q.2, y - q.1.val⟫ ≤ v y}
  have hAc : IsClosed A :=
    (isClosed_closedBall.preimage continuous_snd).inter
      (isClosed_subgradient_graphOn (hvc.mono hKΩ))
  have hAk : IsCompact A :=
    (isCompact_univ.prod (isCompact_closedBall (0 : E) R)).of_isClosed_subset hAc
      (fun _ hq => ⟨mem_univ _, hq.1⟩)
  have heq : Prod.snd '' A = subgradientImageOn v Ω K := by
    ext p
    constructor
    · rintro ⟨⟨x, q⟩, hx, rfl⟩
      exact ⟨x.val, x.property, hx.2⟩
    · rintro ⟨x, hx, hp⟩
      refine ⟨(⟨x, hx⟩, p), ⟨?_, hp⟩, rfl⟩
      simpa only [mem_closedBall, dist_zero_right] using hbound x hx p hp
  rw [← heq]
  exact hAk.image continuous_snd

end CompactImages

end FunctionalInequalities.Analysis
