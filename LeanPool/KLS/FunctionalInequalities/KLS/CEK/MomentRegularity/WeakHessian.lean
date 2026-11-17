/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessian.Directional
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessian.Flux
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessian.Testing
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessian.Weighted
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Weak
public import LeanPool.KLS.FunctionalInequalities.Analysis.Graph.Area
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Products
public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic
public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.HessianKernel
public import LeanPool.KLS.FunctionalInequalities.KLS.CEK.MomentRegularity.WeakDerivative

/-!
# Regular-source weak inverse, Hessian mean, evolution and testing

The last producer, `exists_regular_moment_directional_hessian_subsolution`, adds at the same witness
the directional weak
subsolution inequality and compact-local bounds for the coefficient `e^{-u} (∇²u)⁻¹`.
-/

@[expose] public section

section RegularSource

/-! Shared regular-source hypotheses for the moment-map and quadratic-variance results.
Only the source-law theorems include these hypotheses; auxiliary lemmas retain their own scope. -/

open MeasureTheory Set
open scoped ContDiff

variable {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ)

section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein

section RegularMomentWeakInverse
open scoped Matrix.Norms.Elementwise
namespace FunctionalInequalities.Analysis

include hn hκ hK hKc hKint hW hstrong hμ hiso in
/-- Weak inverse formula (Letwin (2.5)) for the regular moment potential, retaining all of its
regularity and existence conclusions. -/
theorem exists_regular_moment_weak_inverse :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  obtain ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT, he, hfirst⟩ :=
    exists_regular_moment_weak_first_derivative hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT, he, hfirst, ?_⟩
  exact hasWeakDerivAlong_inverse_hessian_of_logdet hG hF
    (hd.mono fun _ hx => ⟨hx.1, hx.2.1⟩) hT

end FunctionalInequalities.Analysis
end RegularMomentWeakInverse

section RegularMomentWeakInverseMean
section
open MeasureTheory Set
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
namespace FunctionalInequalities.Analysis

/-! The same regular-law witnesses retain all weak inverse and first
Monge-Ampere fields and additionally have integrable Hessian entries with mean Id.
This does not establish Letwin's Theorem 2.5 or the compact bound with constant 8,
nor any C2 regularity upgrade. -/

include hn hκ hK hKc hKint hW hstrong hμ hiso in
theorem exists_regular_moment_weak_inverse_mean_hessian :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  obtain ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT, he, hfirst, hInv⟩ :=
    exists_regular_moment_weak_inverse hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT, he, hfirst, hInv, ?_⟩
  have hexp : Integrable (fun x => Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnrm]; norm_num)
  let ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
    ⟨(volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u),
      isProbabilityMeasure_tilted hexp⟩
  have hgm : Measurable (gradient u) := (BakryEmery.continuous_gradient hC1).measurable
  have hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient u) =
      (μ : Measure (EuclideanSpace ℝ (Fin n))) := hm
  have hmapProb : ν.map (gradient u) = μ := by
    apply Subtype.ext
    exact hmap
  have hIso : KLS.Isotropic (ν.map (gradient u)) := by
    rw [hmapProb]
    exact hiso
  have hgrad : MemLp (gradient u) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) :=
    memLp_two_gradient_of_map_eq hC1 ν μ hmap hiso.memLp_two
  let e : Fin n → EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ
  intro i j
  have hInt : Integrable (fun x => hessianMatrix u x i j)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
    change Integrable (fun x => hessianMatrix u x i j) (ν : Measure _)
    exact (integrable_const (16 / κ)).mono'
      (measurable_hessianMatrix_entry u i j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        have hb := norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j
        have hk : 0 ≤ 16 / κ := by positivity
        simpa only [Real.coe_toNNReal _ hk] using hb)
  refine ⟨hInt, ?_⟩
  have hmean :=
    BakryEmery.integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul
      u hC1 hG hc hexp hnrm hgrad (e j) (e i)
  have hsecond := KLS.integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map
    ν hgm hIso (e j) (e i)
  have heq : (fun x => hessianMatrix u x i j) =ᵐ[
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))]
      (fun x => ⟪fderiv ℝ (gradient u) x (e j), e i⟫) := by
    have had := (tilted_absolutelyContinuous
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (-u)).ae_le
        (hG.ae_differentiableAt (μ := volume))
    filter_upwards [had] with x hx
    have hmat := hessianMatrix_toEuclideanLin_of_differentiableAt_gradient hC1 hx
    calc
      hessianMatrix u x i j =
          ⟪e i, Matrix.toEuclideanLin (hessianMatrix u x) (e j)⟫ :=
        (inner_basisFun_toEuclideanLin (hessianMatrix u x) i j).symm
      _ = ⟪e i, fderiv ℝ (gradient u) x (e j)⟫ := by rw [hmat]; rfl
      _ = ⟪fderiv ℝ (gradient u) x (e j), e i⟫ := real_inner_comm _ _
  calc
    (∫ x, hessianMatrix u x i j
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
        ∫ x, ⟪fderiv ℝ (gradient u) x (e j), e i⟫
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) :=
      integral_congr_ae heq
    _ = ∫ x, fderiv ℝ u x (e j) * fderiv ℝ u x (e i)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := hmean
    _ = ⟪e j, e i⟫ := hsecond
    _ = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
      change ⟪EuclideanSpace.basisFun (Fin n) ℝ j,
        EuclideanSpace.basisFun (Fin n) ℝ i⟫ = _
      rw [EuclideanSpace.inner_basisFun_real]
      simp [EuclideanSpace.basisFun_apply, Matrix.one_apply]

end FunctionalInequalities.Analysis
end
end RegularMomentWeakInverseMean

section RegularMomentWeakHessianEvolution
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology
namespace FunctionalInequalities.Analysis

/-! Regular-class weak Hessian evolution and bounded Hessian testing at one actual witness. -/

/-- Actual compact Hessian multipliers have the bounded H1 data; no global T2 is used. -/
private theorem bounded_compact_hessian_test_data {n : ℕ}
    {u ψ : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (i j : Fin n) :
    ∃ C : ℝ, 0 ≤ C ∧
      HasCompactSupport (fun x => ψ x * hessianMatrix u x i j) ∧
      (∀ x, ‖ψ x * hessianMatrix u x i j‖ ≤ C) ∧
      MemLp (fun x => ψ x * hessianMatrix u x i j) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => ψ x * hessianMatrix u x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ k : Fin n,
        HasWeakDerivAlong (fun x => ψ x * hessianMatrix u x i j)
          (fun x => ψ x * T x k i j + fderiv ℝ ψ x
            (EuclideanSpace.basisFun (Fin n) ℝ k) * hessianMatrix u x i j)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (fun x => ψ x * T x k i j + fderiv ℝ ψ x
          (EuclideanSpace.basisFun (Fin n) ℝ k) * hessianMatrix u x i j) ∧
        MemLp (fun x => ψ x * T x k i j + fderiv ℝ ψ x
          (EuclideanSpace.basisFun (Fin n) ℝ k) * hessianMatrix u x i j) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨Cψ, hCψ⟩ := hψc.exists_bound_of_continuous hψ.continuous
  have hη2 : MemLp (fun x => ψ x * hessianMatrix u x i j) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_mul_of_hasCompactSupport hψ.continuous hψc
      (fun S hS => memLp_hessianMatrix_entry_of_isCompact hG i j hS)
  refine ⟨max Cψ 0 * (G : ℝ), mul_nonneg (le_max_right _ _) G.coe_nonneg,
    hψc.mul_right, ?_, hη2, hη2.locallyIntegrable one_le_two, ?_⟩
  · intro x
    rw [norm_mul]
    exact mul_le_mul ((hCψ x).trans (le_max_left _ _))
      (norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j)
      (norm_nonneg _) (le_max_right _ _)
  · intro k
    have hdata := HasWeakDerivAlong.compact_mul_data (hT k i j).1 (hT k i j).2
      (fun S hS => memLp_top_hessianMatrix_entry_of_isCompact hG i j S hS) hψ hψc
    exact ⟨hdata.1, hdata.2.2.1, hdata.2.2.2⟩

include hn hκ hK hKc hKint hW hstrong hμ hiso in
/-- The regular-class moment potential with its weak weighted Hessian evolution: the same `u, L, LF,
T`
as `exists_regular_moment_weak_inverse_mean_hessian`, with every earlier field, plus the weak
derivative of
the first Monge–Ampère trace, the unweighted flux identity and the weighted evolution identity with
curvature and Gram forcing (weak Letwin (2.6)). No analytic premise is added. -/
theorem exists_regular_moment_weak_hessian_evolution :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ i j : Fin n,
      HasWeakDerivAlong
        (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              hessianMatrix u x i a *
                ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
    (let Q := fun x i j => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
  (    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
    obtain
      ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT, he, hfirst, hInv,
        hmean⟩ :=
      exists_regular_moment_weak_inverse_mean_hessian hn hκ hK hKc hKint hW hstrong μ hμ
        hiso
    let Q := fun x i j =>
      -hessianMatrix u x j i +
        ∑ a : Fin n,
          (T x j i a * fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
    have hq :
      ∀ i j : Fin n,
        HasWeakDerivAlong
            (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
            (fun x => Q x i j) (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (fun x => Q x i j) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
      intro i j
      obtain ⟨hweak, hlocal⟩ :=
        hasWeakDerivAlong_mongeAmpere_first_rhs hC1 hl hG
          (hW.of_le (WithTop.coe_le_coe.mpr le_top)) T hT i j
      have htrace :
        (fun x =>
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
              ∑ a : Fin n,
                hessianMatrix u x i a *
                  fderiv ℝ W (gradient u x)
                    (EuclideanSpace.basisFun (Fin n) ℝ
                      a)) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace) := by
        filter_upwards [(hfirst i).2.2.2.2] with x hx
        exact hx.symm
      exact ⟨hweak.congr_ae htrace (Filter.Eventually.of_forall fun _ => rfl), hlocal⟩
    have hflux := integral_weak_hessian_flux_eq_trace_derivative hC1 hG T hT hInv Q hq
    refine
      ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT, he, hfirst, hInv, hmean,
        hq, hflux, ?_⟩
    have hdet :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)) := by
      filter_upwards [hd] with x hx
      rw [← hx.2.1, Real.exp_log hx.1.det_pos]
    exact
      integral_exp_neg_hessian_flux_eq_curvature_gram hC1 hl hG
        (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hF hdet T hT hInv
        (fun i => (hfirst i).2.2.2.2)

include hn hκ hK hKc hKint hW hstrong hμ hiso in
/-- The regular-class weighted Hessian evolution at the same witness, together with its bounded test
extension to `ψ * H_lk` for every compactly supported C1 `ψ`: both sides are integrable and the
weighted
identity holds. No global L2 bound of `T` and no new source premise is used. -/
theorem exists_regular_moment_bounded_weak_hessian_testing :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ i j : Fin n,
      HasWeakDerivAlong
        (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              hessianMatrix u x i a *
                ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
    (let Q := fun x i j => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
  (    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ l k i j : Fin n,
      (∀ b : Fin n, Integrable (fun x => Real.exp (-u x) * J x i j b * (ψ x * T x b l k + fderiv ℝ
        ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x
        (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    obtain
      ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT, he, hfirst, hInv, hmean,
        hq, hflux, hweighted⟩ :=
      exists_regular_moment_weak_hessian_evolution hn hκ hK hKc hKint hW hstrong μ hμ
        hiso
    have hdet :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)) := by
      filter_upwards [hd] with x hx
      rw [← hx.2.1, Real.exp_log hx.1.det_pos]
    refine
      ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT, he, hfirst, hInv, hmean,
        hq, hflux, hweighted, ?_⟩
    dsimp only
    intro ψ hψ hψc l k i j
    obtain ⟨C, _hC, hηc, hbound, _hη2, hη, hweak⟩ :=
      bounded_compact_hessian_test_data hG T hT hψ hψc l k
    exact
      integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test hC1 hl hG
        (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hF hdet T hT hInv
        (fun b => (hfirst b).2.2.2.2) hη hbound hηc (fun b => (hweak b).1)
        (fun b => (hweak b).2.1) (fun b => (hweak b).2.2) i j

include hn hκ hK hKc hKint hW hstrong hμ hiso in
/-- The regular-class weak Hessian evolution witness with its directional weak subsolution and local
coefficient bounds:
the same `u, L, LF, T` as `exists_regular_moment_weak_hessian_evolution` with every one of its
fields, plus, for every
direction `v` and every nonnegative compactly supported C1 `ψ`, the directional weak subsolution
inequality of
`h_v = vᵀ ∇²u v`, and, on every compact `S`, constants `c₀, c₁ > 0` with `c₀·Id ≤ e^{-u} (∇²u)⁻¹ ≤
c₁·Id` a.e. on `S`.
No `C²`, smoothness, Harnack or regularity premise is added. -/
theorem exists_regular_moment_directional_hessian_subsolution :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ i j : Fin n,
      HasWeakDerivAlong
        (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              hessianMatrix u x i a *
                ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
    (let Q := fun x i j => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
  (    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) ∧
      (∀ (v : Fin n → ℝ) (ψ : EuclideanSpace ℝ (Fin n) → ℝ),
        ContDiff ℝ 1 ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n,
          (∑ b : Fin n, (hessianMatrix u x)⁻¹ b a *
            (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        ∫ x, Real.exp (-u x) * (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
      ∧ ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
          ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
            (Real.exp (-u x) • (hessianMatrix u x)⁻¹ -
              c₀ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
            (c₁ • (1 : Matrix (Fin n) (Fin n) ℝ) -
              Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef := by
    obtain ⟨u, L, LF, T, h⟩ :=
      exists_regular_moment_weak_hessian_evolution hn hκ hK hKc hKint hW hstrong μ hμ
        hiso
    refine ⟨u, L, LF, T, h, ?_, ?_⟩
    · obtain ⟨-, hl, -, -, hC1, hG, hF, -, hd, hT, -, hfirst, hInv, -⟩ := h
      have hdet :
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)) := by
        filter_upwards [hd] with x hx
        rw [← hx.2.1, Real.exp_log hx.1.det_pos]
      have hVc : ConvexOn ℝ univ W :=
        UniformConvexOn.convexOn (strongConvexOn_iff_convex.mpr hstrong) fun r => by
          positivity
      intro v ψ hψ hψc hψn
      exact
        integral_directional_hessian_flux_le hC1 hl hG
          (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hF hdet T hT hInv
          (fun i => (hfirst i).2.2.2.2) hVc (hd.mono fun x hx => hx.1) v ψ hψ hψc hψn
    · obtain ⟨-, -, -, -, hC1, -, -, -, hd, -⟩ := h
      intro S hS
      exact
        exists_compact_inverse_hessian_coefficient_bounds hn hC1.continuous
          (hC1.continuous.neg.add
            (hW.continuous.comp (BakryEmery.continuous_gradient hC1)))
          (div_pos (by norm_num : (0 : ℝ) < 16) hκ) hd hS

end FunctionalInequalities.Analysis
end RegularMomentWeakHessianEvolution

end

end RegularSource
