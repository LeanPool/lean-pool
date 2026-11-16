/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Composition
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Testing
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.MongeAmpere
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Integral

/-!
# Unweighted weak Hessian flux and trace forcing

Weak supporting identities for Letwin arXiv:2607.24164v1 Lemma 2.4 (2.6).
Given weak Hessian and inverse-derivative inputs, local integrability and
test-class qualifications are retained explicitly. No source regularity
or mathematical completion is inferred.
-/

@[expose] public section

section

section MongeAmpereFirstRhsDerivative
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace Topology
namespace FunctionalInequalities.Analysis

/-- Closed weak-coordinate calculation already used inside the canonical
weak third-derivative symmetry proof; kept private for its consuming module. -/
private theorem hasWeakDerivAlong_fderiv_of_lipschitz_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hGradLip : LipschitzWith G (gradient u)) (i j : Fin n) :
    HasWeakDerivAlong
      (fun x => fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i))
      (fun x => hessianMatrix u x j i) (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => hessianMatrix u x j i) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hCoordLip : LipschitzWith (‖(innerSL ℝ) (e i)‖₊ * G)
      (fun x => fderiv ℝ u x (e i)) := by
    simpa [Function.comp_def, inner_gradient_left] using
      (((innerSL ℝ) (e i)).lipschitzWith.comp hGradLip)
  have hAE : (fun x => fderiv ℝ (fun y => fderiv ℝ u y (e i)) x (e j)) =ᵐ[
      (volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => hessianMatrix u x j i) := by
    filter_upwards [hGradLip.ae_differentiableAt (μ := volume)] with x hx
    exact hessian_coord_of_gradient_diff (i := j) (j := i) hx
  refine ⟨(hasWeakDerivAlong_of_lipschitz hCoordLip (e j)).congr_ae
    (Filter.Eventually.of_forall fun _ => rfl) hAE, ?_⟩
  intro S hS
  exact memLp_hessianMatrix_entry_of_isCompact hGradLip j i hS


/-- Closed finite linearity for one negative term and a finite sum, encoded by
Option with coefficient -1 at none and 1 at every some. Kept local. -/
private theorem hasWeakDerivAlong_neg_add_sum {n m : ℕ}
    {f₀ df₀ : EuclideanSpace ℝ (Fin n) → ℝ}
    {f df : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (h₀ : HasWeakDerivAlong f₀ df₀ v)
    (h₀₂ : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df₀ 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hf : ∀ i : Fin m, HasWeakDerivAlong (f i) (df i) v)
    (hdf₂ : ∀ i : Fin m, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (df i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => -f₀ x + ∑ i : Fin m, f i x)
      (fun x => -df₀ x + ∑ i : Fin m, df i x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => -df₀ x + ∑ i : Fin m, df i x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let F : Option (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ := fun i =>
    match i with
    | none => f₀
    | some i => f i
  let D : Option (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ := fun i =>
    match i with
    | none => df₀
    | some i => df i
  let c : Option (Fin m) → ℝ := fun i =>
    match i with
    | none => -1
    | some _ => 1
  have hF (i : Option (Fin m)) : HasWeakDerivAlong (F i) (D i) v := by
    cases i with
    | none => exact h₀
    | some i => exact hf i
  have hD (i : Option (Fin m)) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (D i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    cases i with
    | none => exact h₀₂ S hS
    | some i => exact hdf₂ i S hS
  have h := hasWeakDerivAlong_finsetSum_mul (Finset.univ : Finset (Option (Fin m))) c
    (f := F) (df := D) (fun i _ => hF i) (fun i _ => hD i)
  simpa only [Fintype.sum_option, F, D, c, one_mul, neg_one_mul] using h


/--
Weak derivative of the right-hand side `-∂ᵢu + Σₐ Hᵢₐ ∂ₐW(∇u)` of the first weak Monge–Ampère
identity
along every coordinate, with compact-local L2 density, for a C1 potential with Lipschitz gradient, a
C2
`W` and a given compact-local L2 weak Hessian tensor `T`. -/
theorem hasWeakDerivAlong_mongeAmpere_first_rhs {n : ℕ} {u W : EuclideanSpace ℝ (Fin n) → ℝ}
    {L G : NNReal} (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (fun x => T x k i j) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    ∀ i j : Fin n,
      HasWeakDerivAlong
          (fun x =>
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
              ∑ a : Fin n,
                hessianMatrix u x i a *
                  fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
          (fun x =>
            -hessianMatrix u x j i +
              ∑ a : Fin n,
                (T x j i a * fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a) +
                  hessianMatrix u x i a *
                    ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp
              (fun x =>
                -hessianMatrix u x j i +
                  ∑ a : Fin n,
                    (T x j i a *
                        fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a) +
                      hessianMatrix u x i a *
                        ∑ b : Fin n,
                          hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
              2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  intro i j
  have hPartial := hasWeakDerivAlong_fderiv_of_lipschitz_gradient hG i j
  have hProducts :
    ∀ a : Fin n,
      HasWeakDerivAlong
          (fun x =>
            hessianMatrix u x i a *
              fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
          (fun x =>
            T x j i a * fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a) +
              hessianMatrix u x i a *
                ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp
              (fun x =>
                T x j i a * fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a) +
                  hessianMatrix u x i a *
                    ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
              2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro a
    obtain ⟨_, hCompLip, hComp⟩ := exists_lipschitzWith_weak_fderiv_comp_gradient hu hL hG hW a
    exact
      (hT j i a).1.mul_of_locally_bounded (hComp j).1
        (fun S hS => memLp_top_hessianMatrix_entry_of_isCompact hG i a S hS)
        (fun S hS => memLp_top_restrict_of_continuous hCompLip.continuous S hS) (hT j i a).2
        (hComp j).2
  exact
    hasWeakDerivAlong_neg_add_sum hPartial.1 hPartial.2 (fun a => (hProducts a).1)
      (fun a => (hProducts a).2)

end FunctionalInequalities.Analysis
end MongeAmpereFirstRhsDerivative

section HessianFluxTraceForcing
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
namespace FunctionalInequalities.Analysis

/--
Compact-local L2 Hessian flux `Jᵢⱼₐ = Σ_b (H⁻¹)_{ba} T_{bij}` and local integrability of the trace
forcing `Cᵢⱼ` from compact-local L2 tensor and inverse-derivative data and compact-local inverse
bounds. -/
theorem localLp_hessian_flux_trace_forcing {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT2 :
      ∀ k i j : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (fun x => T x k i j) 2
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv2 :
      ∀ k i j : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp
              (fun x =>
                -(((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x k a b) *
                      (hessianMatrix u x)⁻¹)
                    i j))
              2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hRtop :
      ∀ i j : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (Q : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (hQ :
      ∀ i j : Fin n,
        LocallyIntegrable (fun x => Q x i j) (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j =>
      Q x i j - (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
        ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n,
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (fun x => J x i j a) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        LocallyIntegrable (fun x => C x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  dsimp only
  intro i j
  constructor
  · intro a S hS
    apply MeasureTheory.memLp_finsetSum (Finset.univ : Finset (Fin n))
    intro b _hb
    exact (hRtop b a S hS).fun_mul (hT2 b i j S hS)
  · have hTD :
      LocallyIntegrable
        (fun x =>
          ∑ a : Fin n,
            ∑ b : Fin n,
              T x i a b *
                -(((hessianMatrix u x)⁻¹ * (Matrix.of fun c d => T x j c d) *
                      (hessianMatrix u x)⁻¹)
                    b a))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply MeasureTheory.locallyIntegrable_finsetSum (Finset.univ : Finset (Fin n))
      intro a _ha
      apply MeasureTheory.locallyIntegrable_finsetSum (Finset.univ : Finset (Fin n))
      intro b _hb
      exact locallyIntegrable_mul_of_compact_L2 (hT2 i a b) (hInv2 j b a)
    have hdouble :
      LocallyIntegrable
        (fun x =>
          ∑ b : Fin n,
            ∑ a : Fin n,
              T x b i j *
                -(((hessianMatrix u x)⁻¹ * (Matrix.of fun c d => T x a c d) *
                      (hessianMatrix u x)⁻¹)
                    b a))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply MeasureTheory.locallyIntegrable_finsetSum (Finset.univ : Finset (Fin n))
      intro b _hb
      apply MeasureTheory.locallyIntegrable_finsetSum (Finset.univ : Finset (Fin n))
      intro a _ha
      exact locallyIntegrable_mul_of_compact_L2 (hT2 b i j) (hInv2 a b a)
    have hRow :
      LocallyIntegrable
        (fun x =>
          ∑ b : Fin n,
            T x b i j *
              (∑ a : Fin n,
                -(((hessianMatrix u x)⁻¹ * (Matrix.of fun c d => T x a c d) *
                      (hessianMatrix u x)⁻¹)
                    b a)))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [Finset.mul_sum] using hdouble
    exact ((hQ i j).sub hTD).add hRow

end FunctionalInequalities.Analysis
end HessianFluxTraceForcing

section ArrayPairBalance
open MeasureTheory
namespace FunctionalInequalities.Analysis

/-- Finite integral balance of paired integrable arrays; one-use support of the flux identity. -/
private theorem integral_finsetSum_finsetSum {Ω : Type*} [MeasurableSpace Ω]
    {ι κ : Type*} [Fintype ι] [Fintype κ] {μ : Measure Ω} (f : ι → κ → Ω → ℝ)
    (hf : ∀ a b, Integrable (f a b) μ) :
    (∫ x, ∑ a, ∑ b, f a b x ∂μ) = ∑ a, ∑ b, ∫ x, f a b x ∂μ := by
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => hf a b)]
  exact Finset.sum_congr rfl fun a _ => integral_finsetSum _ fun b _ => hf a b

private theorem integral_array_pair_balance {n : ℕ}
    (A B C D : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hA : ∀ a b, Integrable (A a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hB : ∀ a b, Integrable (B a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hC : ∀ a b, Integrable (C a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hD : ∀ a b, Integrable (D a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hF : Integrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hPair : ∀ a b,
      (∫ x, A a b x + B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, C a b x + D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hTrace : (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    -(∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
      ∑ a : Fin n, ∑ b : Fin n, A a b x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  have hA_total := integrable_finsetSum Finset.univ
    (fun a _ => integrable_finsetSum Finset.univ (fun b _ => hA a b))
  have hC_total := integrable_finsetSum Finset.univ
    (fun a _ => integrable_finsetSum Finset.univ (fun b _ => hC a b))
  have hIA := integral_finsetSum_finsetSum A hA
  have hIB := integral_finsetSum_finsetSum B hB
  have hIC := integral_finsetSum_finsetSum C hC
  have hID := integral_finsetSum_finsetSum D hD
  -- Combine the pair balance and identify its trace contribution.
  have hPairSum :
      (∑ a : Fin n, ∑ b : Fin n,
        ((∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) =
      (∑ a : Fin n, ∑ b : Fin n,
        ((∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    have h := hPair a b
    rw [integral_add (hA a b) (hB a b),
      integral_add (hC a b) (hD a b)] at h
    exact h
  have hSums :
      (∑ a : Fin n, ∑ b : Fin n,
        (∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) +
        (∑ a : Fin n, ∑ b : Fin n,
          (∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) =
      (∑ a : Fin n, ∑ b : Fin n,
        (∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) +
        (∑ a : Fin n, ∑ b : Fin n,
          (∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
    simpa only [Finset.sum_add_distrib] using hPairSum
  have hBalance :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
        (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
        (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [hIA, hIB]
      _ =
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := hSums
      _ =
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [← hIC, ← hID]
  have hDTrace :
      (∑ a : Fin n, ∑ b : Fin n,
          ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    calc
      (∑ a : Fin n, ∑ b : Fin n,
          ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hID.symm
      _ = -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := hTrace
  have hExpand :
      (∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
          ∑ a : Fin n, ∑ b : Fin n, A a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        (∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) -
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    calc
      (∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
          ∑ a : Fin n, ∑ b : Fin n, A a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          (∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
            (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        exact integral_add (hF.sub hC_total) hA_total
      _ =
          (∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) -
            (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
            (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [integral_sub hF hC_total]
  rw [hExpand]
  linarith [hBalance, hDTrace]

end FunctionalInequalities.Analysis
end ArrayPairBalance

section WeakHessianFlux
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
namespace FunctionalInequalities.Analysis

private theorem memLp_two_of_compact_local_memLp_top {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  intro S hS
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact (hf S hS).mono_exponent le_top

/-- Closed actual inverse/Hessian pairwise compact curl test, before any trace assembly. -/
private theorem integral_compact_hessian_inverse_curl {n : ℕ}
    {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv : ∀ k i j : Fin n,
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
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (i j a b : Fin n) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k r s => -((R x * (Matrix.of fun c d => T x k c d) * R x) r s)
    (∫ x, T x j i b * (ψ x * D x a b a +
      fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a) * R x b a)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    ∫ x, T x a i b * (ψ x * D x j b a +
      fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j) * R x b a)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hηj := HasWeakDerivAlong.compact_mul_data
    (hInv j b a).1 (hInv j b a).2.1 (hInv j b a).2.2 hψ hψc
  have hηa := HasWeakDerivAlong.compact_mul_data
    (hInv a b a).1 (hInv a b a).2.1 (hInv a b a).2.2 hψ hψc
  exact integral_weakDeriv_mul_eq_swap
    (hT j i b).1 (hT a i b).1 (hT j i b).2 (hT a i b).2
    hηj.1 hηa.1 hηj.2.1 hηj.2.2.1 hηa.2.2.1 hηj.2.2.2 hηa.2.2.2



private theorem integrable_compact_continuous_mul_of_local_memLp_two {n : ℕ}
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Integrable (fun x => χ x * f x) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  simpa only [smul_eq_mul] using
    (locallyIntegrable_of_compact_local_memLp_two hf).integrable_smul_left_of_hasCompactSupport
      hχ hχc


/-- Unweighted weak Hessian flux identity: for every compactly supported C1 `ψ`,
`∫ Σₐ Jᵢⱼₐ ∂ₐψ = -∫ Cᵢⱼ ψ`, with `J` compact-local L2 and `C` locally integrable, from a C1
potential
with Lipschitz gradient, its weak Hessian tensor, weak inverse derivatives and a weak trace
derivative. -/
theorem integral_weak_hessian_flux_eq_trace_derivative {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal} (hu : ContDiff ℝ 1 u)
    (hG : LipschitzWith G (gradient u))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (fun x => T x k i j) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
            (fun x =>
              -(((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x k a b) *
                    (hessianMatrix u x)⁻¹)
                  i j))
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          (∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp
                  (fun x =>
                    -(((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x k a b) *
                          (hessianMatrix u x)⁻¹)
                        i j))
                  2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            ∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
                  ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (Q : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (hQ :
      ∀ i j : Fin n,
        HasWeakDerivAlong
            (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
            (fun x => Q x i j) (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (fun x => Q x i j) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j =>
      Q x i j - (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
        ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n,
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (fun x => J x i j a) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        LocallyIntegrable (fun x => C x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
            ContDiff ℝ 1 ψ →
              HasCompactSupport ψ →
                (∫ x,
                    ∑ a : Fin n,
                      J x i j a *
                        fderiv ℝ ψ x
                          (EuclideanSpace.basisFun (Fin n) ℝ
                            a) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
                  -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  classical
  let R := fun x => (hessianMatrix u x)⁻¹
  let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
  let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
  let C₀ := fun x i j =>
    Q x i j - (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
  change ∀ i j : Fin n, _
  intro i j
  have hdata :=
    localLp_hessian_flux_trace_forcing T (fun k i j => (hT k i j).2)
      (fun k i j => (hInv k i j).2.1) (fun i j => (hInv i i j).2.2) Q
      (fun i j => (hQ i j).1.2.1)
  refine ⟨(hdata i j).1, (hdata i j).2, ?_⟩
  intro ψ hψ hψc
  let e : Fin n → EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ
  let dψ := fun x a => fderiv ℝ ψ x (e a)
  let A := fun a b x => ψ x * (T x b i j * D x a b a)
  let B := fun a b x => dψ x a * (T x b i j * R x b a)
  let C := fun a b x => ψ x * (T x i a b * D x j b a)
  let E := fun a b x => dψ x j * (T x i a b * R x b a)
  let F := fun x => Q x i j * ψ x
  have hR2 (b a : Fin n) :
    ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact S →
        MemLp (fun x => R x b a) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    memLp_two_of_compact_local_memLp_top (hInv i b a).2.2
  have hdψ (a : Fin n) : Continuous (fun x => dψ x a) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdψc (a : Fin n) : HasCompactSupport (fun x => dψ x a) := hψc.fderiv_apply ℝ (e a)
  have hTD (k l m v b a : Fin n) :
    LocallyIntegrable (fun x => T x k l m * D x v b a)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    locallyIntegrable_mul_of_compact_L2 (hT k l m).2 (hInv v b a).2.1
  have hTR (k l m b a : Fin n) :
    LocallyIntegrable (fun x => T x k l m * R x b a)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    locallyIntegrable_mul_of_compact_L2 (hT k l m).2 (hR2 b a)
  have hA (a b : Fin n) : Integrable (A a b) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul] using
      (hTD b i j a b a).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
  have hB (a b : Fin n) : Integrable (B a b) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul] using
      (hTR b i j b a).integrable_smul_left_of_hasCompactSupport (hdψ a) (hdψc a)
  have hC (a b : Fin n) : Integrable (C a b) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul] using
      (hTD i a b j b a).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
  have hE (a b : Fin n) : Integrable (E a b) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul] using
      (hTR i a b b a).integrable_smul_left_of_hasCompactSupport (hdψ j) (hdψc j)
  have hF : Integrable F (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hf := integrable_compact_continuous_mul_of_local_memLp_two (hQ i j).2 hψ.continuous hψc
    simpa only [mul_comm] using hf
  have hsymm := ae_weak_third_derivative_symm hu hG (fun k i j => (hT k i j).1)
  have hPair (a b : Fin n) :
    (∫ x, A a b x + B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, C a b x + E a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hc := integral_compact_hessian_inverse_curl T hT hInv hψ hψc i j a b
    change
      (∫ x,
          T x j i b *
            (ψ x * D x a b a +
              dψ x a * R x b a) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x,
          T x a i b *
            (ψ x * D x j b a +
              dψ x j * R x b a) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) at hc
    calc
      _ =
          ∫ x,
            T x j i b *
              (ψ x * D x a b a +
                dψ x a * R x b a) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply integral_congr_ae
        filter_upwards [hsymm] with x hx
        have ht : T x j i b = T x b i j := (hx j i b).1.trans ((hx i j b).2.trans (hx i b j).1)
        dsimp only [A, B]
        rw [ht]
        ring
      _ = _ := hc
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hsymm] with x hx
        dsimp only [C, E]
        rw [(hx a i b).1]
        ring
  have hTracePoint (x : EuclideanSpace ℝ (Fin n)) :
    (∑ a : Fin n, ∑ b : Fin n, E a b x) =
      (R x * (Matrix.of fun a b => T x i a b)).trace * dψ x j := by
    dsimp only [E]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hTrace :
    (∫ x, ∑ a : Fin n, ∑ b : Fin n, E a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    calc
      _ =
          ∫ x,
            (R x * (Matrix.of fun a b => T x i a b)).trace *
              dψ x j ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
        integral_congr_ae (Filter.Eventually.of_forall hTracePoint)
      _ = _ := (hQ i j).1.2.2 ψ hψ hψc
  have hBalance := integral_array_pair_balance A B C E F hA hB hC hE hF hPair hTrace
  have hFluxPoint (x : EuclideanSpace ℝ (Fin n)) :
    (∑ a : Fin n, J x i j a * dψ x a) = ∑ a : Fin n, ∑ b : Fin n, B a b x := by
    dsimp only [J, B]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hForcePoint (x : EuclideanSpace ℝ (Fin n)) :
    C₀ x i j * ψ x =
      F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) + ∑ a : Fin n, ∑ b : Fin n, A a b x := by
    dsimp only [C₀, F, C, A]
    simp only [sub_mul, add_mul, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
  change
    (∫ x, ∑ a : Fin n, J x i j a * dψ x a ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, C₀ x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
  rw [integral_congr_ae (Filter.Eventually.of_forall hFluxPoint)]
  rw [integral_congr_ae (Filter.Eventually.of_forall hForcePoint)]
  exact hBalance

end FunctionalInequalities.Analysis
end WeakHessianFlux
