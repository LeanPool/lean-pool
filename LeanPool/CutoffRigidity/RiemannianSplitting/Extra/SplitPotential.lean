/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.MeasureFinal
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.CDFactorMain
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitDistance
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitEigenFrame

/-! # Riemannian Gaussian splitting with the potential identity (Theorem 3.6, extra conjunct) -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Bundle
open scoped ENNReal NNReal ContDiff Manifold

namespace CutoffRigidity.Paper

section Riemannian

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

theorem riemannian_gaussian_splitting_potential {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : CutCur.IsWeightedVolume F μ V) {ρ : ℝ}
    (hρ : 0 < ρ)
    (hCD : CutCur.CD F ρ V) (hgap : CutCur.mSpectralGap F μ = ρ) :
    let k := CutCur.mFirstEigenDim F μ V
    ∃ (F' : Type) (_ : NormedAddCommGroup F') (_ : InnerProductSpace ℝ F')
      (_ : FiniteDimensional ℝ F') (N : Type) (_ : EMetricSpace N) (_ : ChartedSpace F' N)
      (_ : IsManifold 𝓘(ℝ, F') ∞ N) (_ : RiemannianBundle (fun y : N => TangentSpace 𝓘(ℝ, F') y))
      (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, F') ∞ F' (fun y : N => TangentSpace 𝓘(ℝ, F') y))
      (_ : IsRiemannianManifold 𝓘(ℝ, F') N) (_ : MeasurableSpace F') (_ : BorelSpace F')
      (_ : MeasurableSpace N) (_ : BorelSpace N)
      (V' : N → ℝ) (μ' : Measure N)
      (Φ : M ≃ₘ^∞⟮𝓘(ℝ, F), 𝓘(ℝ, CutCur.Rd k).prod 𝓘(ℝ, F')⟯ CutCur.Rd k × N),
      (ContMDiff 𝓘(ℝ, F') 𝓘(ℝ, ℝ) ∞ V' ∧ IsProbabilityMeasure μ' ∧
        CutCur.IsWeightedVolume F' μ' V' ∧ CutCur.CD F' ρ V' ∧ ConnectedSpace N ∧ CompleteSpace N) ∧
      (∀ x y, edist x y ^ 2 = edist (Φ x).1 (Φ y).1 ^ 2 + edist (Φ x).2 (Φ y).2 ^ 2) ∧
      (∀ x, V x = ρ * ‖(Φ x).1‖ ^ 2 / 2 + V' (Φ x).2 + k / 2 * Real.log (2 * Real.pi / ρ)) ∧
      μ.map Φ = (multivariateGaussian 0 (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))).prod μ' ∧
      (∀ f, CutCur.IsMEigenfunction F μ V ρ f → ∃ a : CutCur.Rd k,
        (∀ x, f x = inner ℝ a (Φ x).1) ∧ ‖a‖ ^ 2 = ρ * ∫ x, f x ^ 2 ∂μ) ∧
      ∀ f g (a b : CutCur.Rd k), CutCur.IsMEigenfunction F μ V ρ f →
        CutCur.IsMEigenfunction F μ V ρ g →
        (∀ x, f x = inner ℝ a (Φ x).1) → (∀ x, g x = inner ℝ b (Φ x).1) →
        ∫ x, f x * g x ∂μ = 0 → inner ℝ a b = 0 := by
  intro k
  obtain ⟨fr, hfs, horth, hexp⟩ := CutCur.exists_frame_of_eigen F hV hμ hρ hCD hgap
  obtain ⟨hV', hprob, hW, hfact⟩ := fr.weighted_factorization hV hμ hρ
    (fun i x => fr.mvfderiv_V_X i (hfs i) x)
  set γ := multivariateGaussian (0 : CutCur.Rd k) (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) with hγ
  have hfact' : μ.map fr.splitEquiv = γ.prod (μ.map fr.toLevel) := hfact
  have hCD' : CutCur.CD (CutoffRigidity.Riemann.LevelModel F (CutCur.Rd k)) ρ
      (fun y : fr.Level => V y.val + (k / 2 : ℝ) * Real.log (ρ / (2 * Real.pi))) :=
    fr.cd_level hV hμ hV' hW hfact' hCD
  have hg : ∀ i, MemLp (fun x => Real.sqrt ρ * fr.s i x) 2 μ := fun i => (hfs i).2.1.const_mul _
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hp : ∀ x i, (fr.sv x) i = Real.sqrt ρ * fr.s i x / Real.sqrt ρ := by
    intro x i
    field_simp
    rfl
  have hE : ∀ f, CutCur.IsMEigenfunction F μ V ρ f →
      ∃ c : Fin k → ℝ, ∀ x, f x = ∑ i, c i * (Real.sqrt ρ * fr.s i x) := by
    intro f hf
    obtain ⟨c, hc⟩ := hexp f hf
    refine ⟨fun i => c i / Real.sqrt ρ, fun x => ?_⟩
    rw [hc x]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  obtain ⟨hA, hB⟩ := CutoffRigidity.Riemann.affine_items hρ
    (fun i x => Real.sqrt ρ * fr.s i x) hg horth (fun x => fr.sv x) hp
    (CutCur.IsMEigenfunction F μ V ρ) hE
  have hconn : ConnectedSpace fr.Level :=
    Function.Surjective.connectedSpace (f := fun x : M => (⟨fr.retr x, fr.sv_retr x⟩ : fr.Level))
      (fun y => ⟨y.val, Subtype.ext (fr.retr_of_level y.property)⟩)
      (continuous_induced_rng.2 fr.contMDiff_retr.continuous)
  have hcompl : CompleteSpace fr.Level :=
    (isClosed_singleton.preimage fr.contMDiff_sv.continuous : IsClosed {x : M | fr.sv x =
        0}).completeSpace_coe
  refine ⟨CutoffRigidity.Riemann.LevelModel F (CutCur.Rd k), inferInstance, inferInstance,
    inferInstance, fr.Level, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (fun y : fr.Level => V y.val + (k / 2 : ℝ) * Real.log (ρ / (2 * Real.pi))),
    μ.map fr.toLevel, fr.splitEquiv, ⟨hV', hprob, hW, hCD', hconn, hcompl⟩, fun x y => fr.edist_sq
        x y, ?_, hfact', hA, hB⟩
  intro x
  have h := fr.V_action hV (fun i x => fr.mvfderiv_V_X i (hfs i) x) (fr.sv x) (fr.retr x)
    (fr.sv_retr x)
  rw [fr.comp_retr x] at h
  have hl : Real.log (2 * Real.pi / ρ) = -Real.log (ρ / (2 * Real.pi)) := by
    rw [← Real.log_inv, inv_div]
  change V x = ρ * ‖fr.sv x‖ ^ 2 / 2 + (V (fr.retr x) + (k / 2 : ℝ) * Real.log (ρ / (2 * Real.pi)))
    + k / 2 * Real.log (2 * Real.pi / ρ)
  rw [hl, h]; ring

/-- The Gaussian product splitting of a complete weighted Riemannian manifold
at curvature equality, including the potential identity and the first
eigenfunctions' representation, norms and orthogonality. -/
theorem riemannian_gaussian_splitting {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : CutCur.IsWeightedVolume F μ V) {ρ : ℝ}
    (hρ : 0 < ρ)
    (hCD : CutCur.CD F ρ V) (hgap : CutCur.mSpectralGap F μ = ρ) :
    let k := CutCur.mFirstEigenDim F μ V
    ∃ (F' : Type) (_ : NormedAddCommGroup F') (_ : InnerProductSpace ℝ F')
      (_ : FiniteDimensional ℝ F') (N : Type) (_ : EMetricSpace N) (_ : ChartedSpace F' N)
      (_ : IsManifold 𝓘(ℝ, F') ∞ N) (_ : RiemannianBundle (fun y : N => TangentSpace 𝓘(ℝ, F') y))
      (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, F') ∞ F' (fun y : N => TangentSpace 𝓘(ℝ, F') y))
      (_ : IsRiemannianManifold 𝓘(ℝ, F') N) (_ : MeasurableSpace F') (_ : BorelSpace F')
      (_ : MeasurableSpace N) (_ : BorelSpace N)
      (V' : N → ℝ) (μ' : Measure N)
      (Φ : M ≃ₘ^∞⟮𝓘(ℝ, F), 𝓘(ℝ, CutCur.Rd k).prod 𝓘(ℝ, F')⟯ CutCur.Rd k × N),
      (ContMDiff 𝓘(ℝ, F') 𝓘(ℝ, ℝ) ∞ V' ∧ IsProbabilityMeasure μ' ∧
        CutCur.IsWeightedVolume F' μ' V' ∧ CutCur.CD F' ρ V' ∧ ConnectedSpace N ∧ CompleteSpace N) ∧
      (∀ x y, edist x y ^ 2 = edist (Φ x).1 (Φ y).1 ^ 2 + edist (Φ x).2 (Φ y).2 ^ 2) ∧
      (∀ x, V x = ρ * ‖(Φ x).1‖ ^ 2 / 2 + V' (Φ x).2 + k / 2 * Real.log (2 * Real.pi / ρ)) ∧
      μ.map Φ = (multivariateGaussian 0 (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))).prod μ' ∧
      (∀ f, CutCur.IsMEigenfunction F μ V ρ f → ∃ a : CutCur.Rd k,
        (∀ x, f x = inner ℝ a (Φ x).1) ∧ ‖a‖ ^ 2 = ρ * ∫ x, f x ^ 2 ∂μ) ∧
      ∀ f g (a b : CutCur.Rd k), CutCur.IsMEigenfunction F μ V ρ f →
        CutCur.IsMEigenfunction F μ V ρ g →
        (∀ x, f x = inner ℝ a (Φ x).1) → (∀ x, g x = inner ℝ b (Φ x).1) →
        ∫ x, f x * g x ∂μ = 0 → inner ℝ a b = 0 :=
  riemannian_gaussian_splitting_potential F hV hμ hρ hCD hgap

end Riemannian

end CutoffRigidity.Paper
