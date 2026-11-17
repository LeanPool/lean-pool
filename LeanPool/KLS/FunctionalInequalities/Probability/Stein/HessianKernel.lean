/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.Kernel
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Weak
public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.Coordinates

/-!
# Hessian–Stein kernel, pushforward and inverse-map adapters
-/

@[expose] public section

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Probability.Stein
/--
The Hessian–Stein hessianKernel candidate `τ = ∇²φ ∘ Ψ` for a given potential `φ` and inverse map
`Ψ`
(Letwin Lemma 2.7: `Ψ = (∇φ)⁻¹`). -/
noncomputable def hessianKernel {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → Probability.Stein.KernelMatrix n := fun x =>
  hessianMatrix φ (Ψ x)

/--
The Hessian kernel `∇²φ ∘ Ψ` (the Hessian matrix of `φ` composed with `Ψ`) is symmetric everywhere.
-/
theorem hessianKernel_symmetricAE {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) :
    Probability.Stein.SymmetricAE μ (hessianKernel φ Ψ) := by
  exact Filter.Eventually.of_forall fun x i j => bilinearIteratedFDerivTwo_symm hφ (Ψ x) _ _

/-- If `(∇φ)_* ν = μ` and `μ` has finite second moment, then `∇φ ∈ L²(ν)`. -/
theorem memLp_two_gradient_of_map_eq {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hmap :
      (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient φ) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hμ2 :
      MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
        (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (gradient φ) 2 (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hg : Measurable (gradient φ) := (continuous_gradient hφ).measurable
  have hh :
    MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
      ((ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient φ)) := by
    rw [hmap]
    exact hμ2
  simpa only [Function.comp_def, id_eq] using
    (memLp_map_measure_iff continuous_id.aestronglyMeasurable hg.aemeasurable).mp hh

/-- With `Ψ ∘ ∇φ = id` a.e., the hessianKernel at `∇φ y` is the Hessian at `y`. -/
theorem hessianKernel_comp_gradient {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hInv : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient φ y) = y) :
    ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))),
      hessianKernel φ Ψ (gradient φ y) = hessianMatrix φ y := by
  filter_upwards [hInv] with y hy
  simp only [hessianKernel, hy]

theorem hessianKernel_entries_measurable {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) {Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hΨ : Measurable Ψ) (i j : Fin n) : Measurable (fun x => hessianKernel φ Ψ x i j) :=
  (hessian_entry_continuous hφ i j).measurable.comp hΨ

/-- `⟪v, (∇²φ)(y) w⟫ = D²φ(y)(v, w)`. -/
theorem inner_action_hessian {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (y v w : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Probability.Stein.action (hessianMatrix φ y) w⟫ = bilinearIteratedFDerivTwo ℝ φ y v w := by
  have hv : (∑ i, v i • EuclideanSpace.basisFun (Fin n) ℝ i) = v := by
    simpa only [EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  have hw : (∑ j, w j • EuclideanSpace.basisFun (Fin n) ℝ j) = w := by
    simpa only [EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w
  symm
  calc
    bilinearIteratedFDerivTwo ℝ φ y v w =
        bilinearIteratedFDerivTwo ℝ φ y (∑ i, v i • EuclideanSpace.basisFun (Fin n) ℝ i)
          (∑ j, w j • EuclideanSpace.basisFun (Fin n) ℝ j) := by
      rw [hv, hw]
    _ = ∑ i, ∑ j, v i * (hessianMatrix φ y i j * w j) := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        hessianMatrix, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ⟪v, Probability.Stein.action (hessianMatrix φ y) w⟫ := by
      simp only [Probability.Stein.action, PiLp.inner_apply, Real.inner_apply, Matrix.mulVec,
        dotProduct, Finset.mul_sum]


/-- The Hessian kernel of a convex `φ` is positive semidefinite. -/
theorem hessianKernel_quadratic_nonneg {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hcv : ConvexOn ℝ Set.univ φ)
    (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ⟪v, Probability.Stein.action (hessianKernel φ Ψ x) v⟫ := by
  rw [hessianKernel, inner_action_hessian]
  exact bilinearIteratedFDerivTwo_nonneg_of_convexOn hφ hcv _ _

/-- `∇φ ∘ Ψ = id` holds `μ`-a.e. when `Ψ ∘ ∇φ = id` holds `ν`-a.e. and `(∇φ)_* ν = μ`. -/
theorem gradient_comp_inverse_ae {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hmap :
      (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient φ) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hΨ : Measurable Ψ)
    (hInv : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient φ y) = y) :
    ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))), gradient φ (Ψ x) = x := by
  have hg := (continuous_gradient hφ).measurable
  rw [← hmap]
  apply
    (ae_map_iff (μ := (ν : Measure (EuclideanSpace ℝ (Fin n)))) (p := fun x =>
        gradient φ (Ψ x) = x) hg.aemeasurable
        (by
          simpa only [Function.comp_def, id_eq] using
            measurableSet_eq_fun (hg.comp hΨ) measurable_id)).mpr
  filter_upwards [hInv] with y hy
  rw [hy]

/-- An injective continuous gradient has a measurable left inverse. -/
theorem exists_measurable_leftInverse_gradient_of_injective {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hInj : Function.Injective (gradient φ)) :
    ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      Measurable Ψ ∧ Function.LeftInverse Ψ (gradient φ) := by
  have he : MeasurableEmbedding (gradient φ) :=
    (continuous_gradient hφ).measurableEmbedding hInj
  exact ⟨he.invFun, he.measurable_invFun, he.leftInverse_invFun⟩

end FunctionalInequalities.Probability.Stein

/-! ### The Hessian action in L²

If `∇u` is Lipschitz, then `y ↦ (∇²u y) v` is in `L²` of every finite measure. -/

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Probability.Stein

theorem memLp_hessian_action_of_lipschitz_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u))
    (mu : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure mu]
    (v : EuclideanSpace ℝ (Fin n)) :
    MemLp (fun y => action (hessianMatrix u y) v) 2 mu := by
  classical
  apply MemLp.of_eval_piLp
  intro i
  change MemLp (fun y => ∑ j, hessianMatrix u y i j * v j) 2 mu
  apply memLp_finsetSum Finset.univ
  intro j _
  have hij : MemLp (fun y => hessianMatrix u y i j) 2 mu :=
    MemLp.of_bound (measurable_hessianMatrix_entry u i j).aestronglyMeasurable
      (G : ℝ) (ae_of_all _ fun y => norm_hessianMatrix_entry_le_of_lipschitz_gradient hG y i j)
  exact hij.mul_const (v j)

end FunctionalInequalities.Probability.Stein

end

/-! ### Transport of source Hessian properties to the target kernel

For a measurable `Ψ` inverting `∇u` `ν`-a.e. with `(∇u)_# ν = μ`, the pushforward `Ψ_# μ = ν`
carries `ν`-a.e. positive
definiteness and the `L²(ν)` Hilbert–Schmidt bound of `∇²u` to `∇²u ∘ Ψ` under `μ`; `C¹` suffices.
-/

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Matrix.Norms.Frobenius
namespace FunctionalInequalities.Probability.Stein

/-- If `Ψ` inverts `∇u` `ν`-a.e. and `(∇u)_# ν = μ`, then `Ψ_# μ = ν`. -/
private theorem map_eq_of_ae_leftInverse_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient u) =
      (μ : Measure (EuclideanSpace ℝ (Fin n))))
    {Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hΨ : Measurable Ψ)
    (hInv : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient u y) = y) :
    (μ : Measure (EuclideanSpace ℝ (Fin n))).map Ψ = (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
  rw [← hmap, Measure.map_map hΨ (continuous_gradient hu).measurable]
  calc
    Measure.map (Ψ ∘ gradient u) (ν : Measure (EuclideanSpace ℝ (Fin n))) =
        Measure.map id (ν : Measure (EuclideanSpace ℝ (Fin n))) :=
      Measure.map_congr hInv
    _ = _ := Measure.map_id

/-- Source a.e. positive definiteness passes to the target Hessian kernel. -/
theorem hessianKernel_posDefAE_of_map {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient u) =
      (μ : Measure (EuclideanSpace ℝ (Fin n))))
    {Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hΨ : Measurable Ψ)
    (hInv : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient u y) = y)
    (hPD : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix u y).PosDef) :
    ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))), (hessianKernel u Ψ x).PosDef := by
  have hpush := map_eq_of_ae_leftInverse_gradient hu ν μ hmap hΨ hInv
  rw [← hpush] at hPD
  exact ae_of_ae_map hΨ.aemeasurable hPD

/-- The source Hilbert-Schmidt L2 estimate passes to the target kernel at C1 regularity. -/
theorem memLp_hsNorm_hessianKernel_of_map {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient u) =
      (μ : Measure (EuclideanSpace ℝ (Fin n))))
    {Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hΨ : Measurable Ψ)
    (hInv : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient u y) = y)
    (hHS : MemLp (fun y => hsNorm (hessianMatrix u y)) 2
      (ν : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (fun x => hsNorm (hessianKernel u Ψ x)) 2
      (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hpush := map_eq_of_ae_leftInverse_gradient hu ν μ hmap hΨ hInv
  simpa only [Function.comp_def, hessianKernel] using
    hHS.comp_measurePreserving (show MeasurePreserving Ψ
      (μ : Measure (EuclideanSpace ℝ (Fin n)))
      (ν : Measure (EuclideanSpace ℝ (Fin n))) from ⟨hΨ, hpush⟩)

end FunctionalInequalities.Probability.Stein

end
