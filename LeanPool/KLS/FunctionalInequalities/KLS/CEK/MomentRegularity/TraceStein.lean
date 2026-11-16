/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.MongeAmpere
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Weak
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.Conservativity
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Integral
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Positivity
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Trace.Gram
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.WeakDerivative
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.WeakTrace
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HessianStein
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HessianTrace
public import LeanPool.KLS.FunctionalInequalities.KLS.CEK.MomentRegularity.Cutoff

/-!
# Trace and weak Stein estimates at one regular moment witness
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

noncomputable section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein

section RegularMomentTraceQuadraticTesting

open MeasureTheory Set Filter Matrix
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

/-! Fixed-witness trace properties. Source-law hypotheses enter only at the witness factory. -/

private def MomentTraceData {n : ℕ} (W : EuclideanSpace ℝ (Fin n) → ℝ) (κ : ℝ)
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (L : NNReal) (LF : NNReal) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ) :
    Prop :=
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
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))

private def CutoffTraceTesting {n : ℕ} (W : EuclideanSpace ℝ (Fin n) → ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
        fderiv ℝ W (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, ∃ C_B : ℝ, 0 ≤ C_B ∧
        (∀ x, ‖(B * hessianMatrix u x * B * hessianMatrix u x).trace‖ ≤ C_B) ∧
        LocallyIntegrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ k : Fin n,
          HasWeakDerivAlong (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
            (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i
              j)).trace)
              2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ r : ℝ, 1 ≤ r →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x *
          Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))

private def TraceContraction {n : ℕ}
    (W : EuclideanSpace ℝ (Fin n) → ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∀ B : Matrix (Fin n) (Fin n) ℝ,
      let H := fun x => hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let a := fun x i => 2 * (B * H x * B * Tm x i).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        Integrable (fun x => Real.exp (-u x) * g x * ψ x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ j : Fin n, Integrable (fun x => Real.exp (-u x) *
          (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (∫ x, Real.exp (-u x) * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))

private def TraceConservativity {n : ℕ}
    (W : EuclideanSpace ℝ (Fin n) → ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      let H := fun x => hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      Integrable g ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, g x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) = 0

private def TraceEnergyBound {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∀ B : Matrix (Fin n) (Fin n) ℝ,
    B.PosSemidef →
      let D := fun x =>
        ∑ i : Fin n,
          ∑ j : Fin n,
            (hessianMatrix u x)⁻¹ i j *
              (B * (Matrix.of fun a b => T x i a b) * B *
                  (Matrix.of fun a b => T x j a b)).trace
      Integrable D ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, D x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤
          (1 / 2 : ℝ) *
            ∫ x,
              (B * hessianMatrix u x * B *
                  hessianMatrix u
                    x).trace ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))

private def PositiveTraceBound {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ 2 * (B * B).trace

private def SymmetricTraceBound {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ 2 * (B * B).trace

private def WeightedWeakPairing {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ (eta : EuclideanSpace ℝ (Fin n) → ℝ) (Leta : NNReal) (C : ℝ),
    LipschitzWith Leta eta →
      (∀ x, ‖eta x‖ ≤ C) →
        ∀ v : EuclideanSpace ℝ (Fin n),
          Integrable (fun x => fderiv ℝ eta x v)
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
            Integrable (fun x => eta x * fderiv ℝ u x v)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
              (∫ x,
                  fderiv ℝ eta x
                    v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
                ∫ x,
                  eta x *
                    fderiv ℝ u x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))

include hn hκ hK hKc hKint hW hstrong hμ hiso in
private theorem exists_trace_cutoff_witness :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal) (T :
      EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      MomentTraceData W κ μ u L LF T ∧ CutoffTraceTesting W u T := by
  obtain
    ⟨u, L, LF, T, hrest, c, C, hC, hlower, hreg, hmono, hpoint, hint, hbound, hdecay, hrough⟩ :=
    exists_regular_moment_bounded_weak_cutoff_testing hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hcopy := hrest
  rcases hcopy with
    ⟨_hc, _hl, _hnrm, _hm, _hC1, hG, _hF, _hw, _hd, hT, _he, _hfirst, _hInv, _hmean, _hq,
      _hflux, _hweighted, _hbounded⟩
  refine ⟨u, L, LF, T, hrest, c, C, hC, hlower, hreg, hmono, hpoint, hint, hbound, hdecay, ?_⟩
  dsimp only
  intro B
  obtain ⟨C_B, hCB, hfbound, hfloc, hweakB⟩ :=
    bounded_trace_quadratic_weak_derivative_data B (fun x => hessianMatrix u x)
      (fun k x => Matrix.of fun i j => T x k i j)
      (fun i j => measurable_hessianMatrix_entry u i j)
      (fun x i j => norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j)
      (fun k i j => (hT k i j).1) (fun k i j => (hT k i j).2)
  refine ⟨C_B, hCB, hfbound, hfloc, hweakB, ?_⟩
  intro r hr
  exact hrough r hr _ _ C_B hfloc hfbound (fun k => (hweakB k).1) (fun k => (hweakB k).2)

end FunctionalInequalities.Analysis

end RegularMomentTraceQuadraticTesting

section RegularMomentWeakTraceContraction

open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

private theorem trace_contraction {u : EuclideanSpace ℝ (Fin n) → ℝ} {L LF : NNReal}
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hbase : MomentTraceData W κ μ u L LF T) :
    TraceContraction W u T := by
  rcases hbase with ⟨_hc, _hl, _hnrm, _hm, hC1, hG, _hF, _hw, _hd, hT, _he,
    _hfirst, _hInv, _hmean, _hq, _hflux, hweighted, hbounded⟩
  intro B
  apply integral_trace_quadratic_flux_eq_neg_density B
    (fun x => hessianMatrix u x) (fun x => (hessianMatrix u x)⁻¹)
    (fun x => Matrix.of fun i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b) * (hessianMatrix u x)⁻¹ *
        (Matrix.of fun a b => T x j a b)).trace)
    (fun x i => Matrix.of fun a b => T x i a b) (fun x => Real.exp (-u x))
    (Real.continuous_exp.comp hC1.continuous.neg)
  · intro i j
    exact memLp_top_of_bound (measurable_hessianMatrix_entry u i j).aestronglyMeasurable
      (Real.toNNReal (16 / κ) : ℝ) (Filter.Eventually.of_forall fun x =>
        norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j)
  · exact fun a i j => (hT a i j).2
  · exact fun i j a => (hweighted i j).1 a
  · exact fun i j => (hweighted i j).2.1
  · exact fun ψ hψ hψc l k i j => (hbounded ψ hψ hψc l k i j).2.2

end FunctionalInequalities.Analysis

end RegularMomentWeakTraceContraction

section RegularMomentWeakTraceDensity

open MeasureTheory Set Matrix
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

private theorem ae_weak_trace_density_add_twice_energy_nonneg {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k)) :
    let E := fun x => Matrix.of fun i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b) *
        (hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x j a b)).trace
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      0 ≤ (2 * (B * hessianMatrix u x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (B * (Matrix.of fun a b => T x i a b) * B *
            (Matrix.of fun a b => T x j a b)).trace) +
        2 * (B * hessianMatrix u x * B * hessianMatrix u x).trace := by
  have hW2 : ContDiff ℝ 2 W := hW.of_le (WithTop.coe_le_coe.mpr le_top)
  have hVc : ConvexOn ℝ univ W :=
    UniformConvexOn.convexOn (strongConvexOn_iff_convex.mpr hstrong) fun r => by positivity
  have hWP (x : EuclideanSpace ℝ (Fin n)) : (hessianMatrix W x).PosSemidef :=
    hessianMatrixIn_posSemidef (EuclideanSpace.basisFun (Fin n) ℝ) hW2.contDiffAt
      (bilinearIteratedFDerivTwo_nonneg_of_convexOn hW2 hVc x)
  have hsym := ae_weak_third_derivative_symm hu hG hT
  dsimp only
  filter_upwards [hPD, hsym] with x hPx hSx
  intro B hB
  have hTx : ∀ i : Fin n, (Matrix.of fun a b => T x i a b).IsSymm := by
    intro i
    ext a b
    exact (hSx i b a).2
  exact trace_forcing_add_twice_energy_nonneg B (hessianMatrix u x)
    (hessianMatrix u x)⁻¹ (hessianMatrix W (gradient u x)) hB hPx.posSemidef
    hPx.inv.posSemidef (hWP _) (fun i => Matrix.of fun a b => T x i a b) hTx

end FunctionalInequalities.Analysis

end RegularMomentWeakTraceDensity

section RegularMomentTiltedCutoffConservativity

open MeasureTheory Filter
open scoped Topology

namespace FunctionalInequalities.Analysis

private theorem integrable_zero_tilted_of_weighted_cutoff_defect {n : ℕ}
    (u f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hnorm : (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hf : LocallyIntegrable f (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg : LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C)
    (c : ℝ) (hc : 0 < c)
    (hLower : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ g x + c * f x)
    (chi defect : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hChi : ∀ m, Continuous (chi m))
    (hChiBounds : ∀ m x, 0 ≤ chi m x ∧ chi m x ≤ 1)
    (hChiLim : ∀ x, Tendsto (fun m => chi m x) atTop (𝓝 1))
    (hDefect : ∀ m, Integrable (defect m)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)))
    (hDefectLim : Tendsto (fun m => ∫ x, |defect m x|
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0))
    (hCutoff : ∀ m, Integrable (fun x => chi m x * g x * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hPair : ∀ m,
      (∫ x, chi m x * g x * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, f x * defect m x * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Integrable g ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
      (∫ x, g x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) = 0 := by
  have hexp := BakryEmery.integrable_exp_neg_of_integral_eq_one
    (volume : Measure (EuclideanSpace ℝ (Fin n))) u hnorm
  let nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
    ⟨(volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u), isProbabilityMeasure_tilted hexp⟩
  have hac := tilted_absolutelyContinuous
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (-u)
  apply integrable_and_integral_eq_zero_of_cutoff_defect nu f g
    (hf.aestronglyMeasurable.mono_ac hac) (hg.aestronglyMeasurable.mono_ac hac)
    C hC (Filter.Eventually.of_forall hbound) c hc (hac.ae_le hLower) chi defect
    (fun m => (hChi m).aestronglyMeasurable)
    (fun m => Filter.Eventually.of_forall (hChiBounds m))
    (Filter.Eventually.of_forall hChiLim) hDefect hDefectLim
  · intro m
    apply (integrable_tilted_iff hexp _).mpr
    simpa only [Pi.neg_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hCutoff m
  · intro m
    change (∫ x, chi m x * g x
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
      ∫ x, f x * defect m x
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))
    rw [integral_tilted, integral_tilted]
    simp only [Pi.neg_apply, hnorm, div_one, smul_eq_mul]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hPair m

end FunctionalInequalities.Analysis

end RegularMomentTiltedCutoffConservativity

section RegularMomentWeakTraceConservativity

open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

private theorem trace_conservativity {u : EuclideanSpace ℝ (Fin n) → ℝ} {L LF : NNReal}
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hκ : 0 < κ) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (hbase : MomentTraceData W κ μ u L LF T)
    (hcutoffs : CutoffTraceTesting W u T)
    (hTrace : TraceContraction W u T) :
    TraceConservativity W u T := by
  rcases hbase with ⟨_hc, _hl, hnrm, _hm, hC1, hG, _hF, _hw, hdata, hT, _he,
    _hfirst, _hInv, _hmean, _hq, _hflux, _hweighted, _hbounded⟩
  obtain ⟨c, C, _hC, _hlower, hreg, _hmono, hpoint, hint, _hbound, hdecay, hrough⟩ := hcutoffs
  intro B hB
  dsimp only
  let H := fun x => hessianMatrix u x
  let R := fun x => (H x)⁻¹
  let Tm := fun x i => Matrix.of fun a b => T x i a b
  let E := fun x => Matrix.of fun i j => -H x i j +
    (H x * hessianMatrix W (gradient u x) * H x) i j +
    (R x * Tm x i * R x * Tm x j).trace
  let a := fun x i => 2 * (B * H x * B * Tm x i).trace
  let g := fun x => 2 * (B * H x * B * E x).trace +
    2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
  let f := fun x => (B * H x * B * H x).trace
  let chi := fun (r : ℝ) x => Real.smoothTransition (2 - (u x - c) / r)
  let defect := fun (r : ℝ) x => ((H x)⁻¹ * hessianMatrix (chi r) x).trace -
    fderiv ℝ W (gradient u x) (gradient (chi r) x)
  have h1 (m : ℕ) : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hcofinal : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  obtain ⟨C_B, hCB, hfbound, hfloc, _hweakB, hpair⟩ := hrough B
  have hTr := hTrace B
  have hLower : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      0 ≤ g x + 2 * f x := by
    have hn := ae_weak_trace_density_add_twice_energy_nonneg hκ hW hstrong hC1 hG
      (hdata.mono fun _ hx => hx.1) T (fun k i j => (hT k i j).1)
    filter_upwards [hn] with x hx
    exact hx B hB
  apply integrable_zero_tilted_of_weighted_cutoff_defect u f g hnrm hfloc hTr.1
    C_B hCB (fun x => by simpa only [Real.norm_eq_abs] using hfbound x)
    2 (by norm_num) hLower
    (fun m => chi ((m : ℝ) + 1)) (fun m => defect ((m : ℝ) + 1))
    (fun m => (hreg _ (h1 m)).1.continuous)
    (fun m => (hreg _ (h1 m)).2.2.2)
    (fun x => (hpoint x).comp hcofinal)
    (fun m => hint _ (h1 m)) (hdecay.comp hcofinal)
  · intro m
    have ht := (hTr.2 (chi ((m : ℝ) + 1)) (hreg _ (h1 m)).1
      (hreg _ (h1 m)).2.1).1
    change Integrable (fun x => Real.exp (-u x) * g x * chi ((m : ℝ) + 1) x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) at ht
    apply ht.congr
    filter_upwards [] with x
    ring
  · intro m
    have ht := (hTr.2 (chi ((m : ℝ) + 1)) (hreg _ (h1 m)).1
      (hreg _ (h1 m)).2.1).2.2
    have hp := (hpair ((m : ℝ) + 1) (h1 m)).2.2
    have hswap :
        (∫ x, (∑ i : Fin n, ∑ j : Fin n, R x i j * a x i *
          fderiv ℝ (chi ((m : ℝ) + 1)) x (EuclideanSpace.basisFun (Fin n) ℝ j)) *
          Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, Real.exp (-u x) * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ (chi ((m : ℝ) + 1)) x (EuclideanSpace.basisFun (Fin n) ℝ j))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [mul_comm, Finset.sum_comm]
      simp only [Finset.sum_mul]
    change (∫ x, f x * defect ((m : ℝ) + 1) x * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = _ at hp
    rw [hswap, ht] at hp
    have heq : (∫ x, Real.exp (-u x) * g x * chi ((m : ℝ) + 1) x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, chi ((m : ℝ) + 1) x * g x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    rw [heq, neg_neg] at hp
    exact hp.symm

end FunctionalInequalities.Analysis

end RegularMomentWeakTraceConservativity

section RegularMomentHalfDomination

open Matrix MeasureTheory

namespace FunctionalInequalities.Analysis

private theorem integrable_and_integral_le_half_of_four_mul_le {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (f g D : α → ℝ)
    (hf : Integrable f mu) (hg : Integrable g mu) (hD : AEStronglyMeasurable D mu)
    (hD0 : ∀ᵐ x ∂mu, 0 ≤ D x)
    (hUpper : ∀ᵐ x ∂mu, 4 * D x ≤ g x + 2 * f x)
    (hZero : (∫ x, g x ∂mu) = 0) :
    Integrable D mu ∧ (∫ x, D x ∂mu) ≤ (1 / 2 : ℝ) * ∫ x, f x ∂mu := by
  have hi : Integrable (fun x => g x + 2 * f x) mu := hg.add (hf.const_mul 2)
  have hInt : Integrable D mu := by
    apply (hi.norm.div_const 4).mono' hD
    filter_upwards [hD0, hUpper] with x hx0 hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx0, Real.norm_eq_abs]
    have ha := le_abs_self (g x + 2 * f x)
    linarith
  refine ⟨hInt, ?_⟩
  have hm := integral_mono_ae (hInt.const_mul 4) hi hUpper
  rw [integral_const_mul, integral_add hg (hf.const_mul 2), integral_const_mul, hZero] at hm
  linarith

end FunctionalInequalities.Analysis

end RegularMomentHalfDomination

section RegularMomentWeakTraceEnergy

open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/--
Weak half-trace tensor energy at one regular moment witness (Letwin arXiv:2607.24164v1 (2.14), weak
form): with the
whole payload of the bounded weak cutoff testing, trace-quadratic testing, weak trace contraction
and conservativity
retained at the same `u`, `L`, `LF`, `T`, for every positive semidefinite `B` the trace tensor
energy
`D = ∑ (∇²u)⁻¹ᵢⱼ tr(B Tᵢ B Tⱼ)` is integrable for `e^{-u} dx` and `∫ D ≤ (1/2) ∫ tr(B ∇²u B ∇²u)`.
-/
private theorem trace_energy_bound {u : EuclideanSpace ℝ (Fin n) → ℝ} {L LF : NNReal}
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ} (hκ : 0 < κ)
    (hW : ContDiff ℝ ∞ W) (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (hbase : MomentTraceData W κ μ u L LF T) (hcutoffs : CutoffTraceTesting W u T)
    (hConserve : TraceConservativity W u T) : TraceEnergyBound u T := by
  rcases hbase with
    ⟨_hc, _hl, hnrm, _hm, hC1, hG, _hF, _hw, hdata, hT, _he, _hfirst, hInv, _hmean, _hq, _hflux,
      _hweighted, _hbounded⟩
  obtain ⟨_c, _C, _hC, _hlower, _hreg, _hmono, _hpoint, _hint, _hbound, _hdecay, hrough⟩ :=
    hcutoffs
  have hW2 : ContDiff ℝ 2 W := hW.of_le (WithTop.coe_le_coe.mpr le_top)
  have hVc : ConvexOn ℝ univ W :=
    UniformConvexOn.convexOn (strongConvexOn_iff_convex.mpr hstrong) fun r => by positivity
  have hWP (x : EuclideanSpace ℝ (Fin n)) : (hessianMatrix W x).PosSemidef :=
    hessianMatrixIn_posSemidef (EuclideanSpace.basisFun (Fin n) ℝ) hW2.contDiffAt
      (bilinearIteratedFDerivTwo_nonneg_of_convexOn hW2 hVc x)
  have hsym := ae_weak_third_derivative_symm hC1 hG (fun k i j => (hT k i j).1)
  have hRm (i j : Fin n) :
    AEMeasurable (fun x => (hessianMatrix u x)⁻¹ i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hLoc :
      LocallyIntegrable (fun x => (hessianMatrix u x)⁻¹ i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply locallyIntegrable_iff.mpr
      intro S hS
      let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
        isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
      exact ((hInv i i j).2.2 S hS).integrable (by simp)
    exact hLoc.aestronglyMeasurable.aemeasurable
  have hTm (k i j : Fin n) :
    AEMeasurable (fun x => T x k i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hLoc :
      LocallyIntegrable (fun x => T x k i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply locallyIntegrable_iff.mpr
      intro S hS
      let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
        isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
      exact ((hT k i j).2 S hS).integrable (by norm_num)
    exact hLoc.aestronglyMeasurable.aemeasurable
  have hexp :=
    integrable_exp_neg_of_integral_eq_one (volume : Measure (EuclideanSpace ℝ (Fin n))) u hnrm
  let nu : Measure (EuclideanSpace ℝ (Fin n)) :=
    (volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)
  let : IsProbabilityMeasure nu := isProbabilityMeasure_tilted hexp
  have hac := tilted_absolutelyContinuous (volume : Measure (EuclideanSpace ℝ (Fin n))) (-u)
  intro B hB
  dsimp only
  let H := fun x => hessianMatrix u x
  let R := fun x => (H x)⁻¹
  let Tmat := fun x i => Matrix.of fun a b => T x i a b
  let E := fun x =>
    Matrix.of fun i j =>
      -H x i j + (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tmat x i * R x * Tmat x j).trace
  let f := fun x => (B * H x * B * H x).trace
  let g := fun x =>
    2 * (B * H x * B * E x).trace +
      2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tmat x i * B * Tmat x j).trace
  let D := fun x => ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tmat x i * B * Tmat x j).trace
  obtain ⟨C_B, _hCB, hfbound, hfloc, _hweakB, _hpair⟩ := hrough B
  have hf : Integrable f nu :=
    (integrable_const C_B).mono' (hfloc.aestronglyMeasurable.mono_ac hac)
      (Filter.Eventually.of_forall hfbound)
  have hCons : Integrable g nu ∧ (∫ x, g x ∂nu) = 0 := hConserve B hB
  have hDvol : AEMeasurable D (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply Finset.aemeasurable_fun_sum
    intro i _
    apply Finset.aemeasurable_fun_sum
    intro j _
    apply (hRm i j).mul
    simp only [Tmat, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
    apply Finset.aemeasurable_fun_sum
    intro a _
    apply Finset.aemeasurable_fun_sum
    intro d _
    apply AEMeasurable.mul _ (hTm j d a)
    apply Finset.aemeasurable_fun_sum
    intro c _
    apply AEMeasurable.mul _ aemeasurable_const
    apply Finset.aemeasurable_fun_sum
    intro b _
    exact aemeasurable_const.mul (hTm i b c)
  have hBoth :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ D x ∧ 4 * D x ≤ g x + 2 * f x := by
    filter_upwards [hdata, hsym] with x hx hs
    exact
      four_tensor_trace_le_density_add_twice_energy B (H x) (hessianMatrix W (gradient u x)) hB
        hx.1 (hWP _) (T x) (fun a b c => (hs a b c).1) (fun a b c => (hs a b c).2)
  exact
    integrable_and_integral_le_half_of_four_mul_le nu f g D hf hCons.1
      (hDvol.aestronglyMeasurable.mono_ac hac) (hac.ae_le (hBoth.mono fun _ hx => hx.1))
      (hac.ae_le (hBoth.mono fun _ hx => hx.2)) hCons.2

end FunctionalInequalities.Analysis

end RegularMomentWeakTraceEnergy

section RegularMomentWeakTheorem25

open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

private theorem positive_trace_bound {u : EuclideanSpace ℝ (Fin n) → ℝ} {L LF : NNReal}
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hbase : MomentTraceData W κ μ u L LF T)
    (hEnergy : TraceEnergyBound u T) :
    PositiveTraceBound u := by
  rcases hbase with ⟨hc, hl, hnrm, _hm, hC1, hG, _hF, _hw, hdata, hT, _he,
    _hfirst, hInv, hmean, _hq, _hflux, _hweighted, _hbounded⟩
  intro B hB
  have hexp : Integrable (fun x => Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnrm]; norm_num)
  let nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
    ⟨(volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u), isProbabilityMeasure_tilted hexp⟩
  obtain ⟨hD, hhalf⟩ := hEnergy B hB
  exact KLS.LogConcave.integral_trace_quadratic_le_two_mul_trace_sq
    (nu := nu) rfl hc hC1 hG hl hnrm (hdata.mono fun _ hx => hx.1) T hT
    (fun i j K hK => (hInv i i j).2.2 K hK) hmean B hB hD hhalf

end FunctionalInequalities.Analysis

end RegularMomentWeakTheorem25

section RegularMomentWeakSymmetricTraceBound

open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

private theorem symmetric_trace_bound {u : EuclideanSpace ℝ (Fin n) → ℝ} {L LF : NNReal}
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hbase : MomentTraceData W κ μ u L LF T)
    (hPSD : PositiveTraceBound u) :
    SymmetricTraceBound u := by
  rcases hbase with ⟨_hc, _hl, _hnrm, _hm, _hC1, _hG, _hF, _hw, hdata, _hT, _he,
    _hfirst, _hInv, _hmean, _hq, _hflux, _hweighted, _hbounded⟩
  have hAE : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)),
      (hessianMatrix u x).PosSemidef :=
    (tilted_absolutelyContinuous (volume : Measure (EuclideanSpace ℝ (Fin n))) (-u)).ae_le
      (hdata.mono fun _ hx => hx.1.posSemidef)
  intro B hB
  exact symmetric_trace_integral_extension_of_ae_posSemidef
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))
    (fun x => hessianMatrix u x) (fun i j => measurable_hessianMatrix_entry u i j)
    hAE hPSD hB

end FunctionalInequalities.Analysis

end RegularMomentWeakSymmetricTraceBound

section RegularMomentWeightedWeakPairing

open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

private theorem weighted_weak_pairing {u : EuclideanSpace ℝ (Fin n) → ℝ} {L LF : NNReal}
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hbase : MomentTraceData W κ μ u L LF T) :
    WeightedWeakPairing u := by
  rcases hbase with ⟨_hc, hl, hnrm, _hm, _hC1, _hG, _hF, _hw, _hdata, _hT, _he,
    _hfirst, _hInv, _hmean, _hq, _hflux, _hweighted, _hbounded⟩
  intro eta Leta C heta hbound v
  exact integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz
    hl heta C hbound hnrm v

end FunctionalInequalities.Analysis

end RegularMomentWeightedWeakPairing

section RegularMomentWeakSteinCoupling

open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

include hn hκ hK hKc hKint hW hstrong hμ hiso in
/-- Weak source Stein coupling at one regular moment witness: at the same `u`, `L`, `LF`, `T` the
whole payload (cutoff testing,
trace contraction, conservativity, half energy, all-symmetric Theorem 2.5 trace bound and
bounded-Lipschitz weighted
pairing) is retained, and every C1 globally Lipschitz globally bounded test satisfies the coordinate
source Stein identity. -/
theorem exists_regular_moment_weak_stein_coupling :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
((      ((      (      ((ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
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
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
        fderiv ℝ W (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, ∃ C_B : ℝ, 0 ≤ C_B ∧
        (∀ x, ‖(B * hessianMatrix u x * B * hessianMatrix u x).trace‖ ≤ C_B) ∧
        LocallyIntegrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ k : Fin n,
          HasWeakDerivAlong (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
            (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i
              j)).trace)
              2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ r : ℝ, 1 ≤ r →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x *
          Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ,
      let H := fun x => hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let a := fun x i => 2 * (B * H x * B * Tm x i).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        Integrable (fun x => Real.exp (-u x) * g x * ψ x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ j : Fin n, Integrable (fun x => Real.exp (-u x) *
          (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (∫ x, Real.exp (-u x) * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      let H := fun x => hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      Integrable g ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, g x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) = 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      let D := fun x => ∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        (B * (Matrix.of fun a b => T x i a b) * B * (Matrix.of fun a b => T x j a b)).trace
      Integrable D ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, D x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤
        (1 / 2 : ℝ) * ∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ 2 * (B * B).trace) ∧
      ∀ (eta : EuclideanSpace ℝ (Fin n) → ℝ) (Leta : NNReal) (C : ℝ),
        LipschitzWith Leta eta → (∀ x, ‖eta x‖ ≤ C) →
        ∀ v : EuclideanSpace ℝ (Fin n),
        Integrable (fun x => fderiv ℝ eta x v) ((volume : Measure (EuclideanSpace ℝ (Fin
          n))).tilted (-u)) ∧
        Integrable (fun x => eta x * fderiv ℝ u x v) ((volume : Measure (EuclideanSpace ℝ (Fin
          n))).tilted (-u)) ∧
        (∫ x, fderiv ℝ eta x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          ∫ x, eta x * fderiv ℝ u x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted
            (-u))) ∧
      ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ) (Lf : NNReal) (C : ℝ),
        ContDiff ℝ 1 f → LipschitzWith Lf f → (∀ x, ‖f x‖ ≤ C) → ∀ i : Fin n,
        Integrable (fun y => gradient u y i * f (gradient u y))
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        Integrable (fun y => ∑ j, hessianMatrix u y i j * gradient f (gradient u y) j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ y, gradient u y i * f (gradient u y)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          ∫ y, (∑ j, hessianMatrix u y i j * gradient f (gradient u y) j)
            ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
  obtain ⟨u, L, LF, T, hbase, hcutoffs⟩ := exists_trace_cutoff_witness
    hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hTrace := trace_contraction (μ := μ) hbase
  have hConserve := trace_conservativity (μ := μ) hκ hW hstrong hbase hcutoffs hTrace
  have hEnergy := trace_energy_bound (μ := μ) hκ hW hstrong hbase hcutoffs hConserve
  have hPSD := positive_trace_bound (μ := μ) hbase hEnergy
  have hSymm := symmetric_trace_bound (μ := μ) hbase hPSD
  have hPair := weighted_weak_pairing (μ := μ) hbase
  refine ⟨u, L, LF, T, ⟨⟨⟨⟨⟨⟨hbase, hcutoffs⟩, hTrace⟩, hConserve⟩, hEnergy⟩, hSymm⟩, hPair⟩, ?_⟩
  rcases hbase with ⟨_hc, hl, _hnrm, _hm, hC1, hG, _hF, _hw, _hdata, _hT, _he,
    _hfirst, _hInv, _hmean, _hq, _hflux, _hweighted, _hbounded⟩
  intro f Lf C hf hfLip hbound i
  exact KLS.LogConcave.source_stein_identity_of_bounded_lipschitz_test hC1 hl hG _hnrm
    hf hfLip C hbound i

end FunctionalInequalities.Analysis

end RegularMomentWeakSteinCoupling

section RegularMomentHessianTraceBound

open MeasureTheory Set Matrix
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff

namespace FunctionalInequalities.Analysis

include hn hκ hK hKc hKint hW hstrong hμ hiso in
/--
The properties of one actual regular moment witness used by the Letwin regular-class assembly, as a
flat conjunction at
the same cutoff-source witness underlying `exists_regular_moment_weak_stein_coupling`: convexity,
Lipschitz bound, normalization,
pushforward to `μ`, `C¹` with `16/κ`-Lipschitz gradient, the a.e. positive definite Hessian with
log-det identity and
`16/κ` cap, integrable Hessian entries with mean `Id`, and the weak Theorem 2.5 bound `E tr(B Hess u
B Hess u) ≤ 2 tr(B²)`
for every real symmetric `B`. The hypotheses are exactly those of the witness producer. -/
theorem exists_regular_moment_hessian_trace_bound :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal),
      ConvexOn ℝ univ u ∧
        LipschitzWith L u ∧
          (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
                (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
              ContDiff ℝ 1 u ∧
                LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
                  (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
                      (hessianMatrix u x).PosDef ∧
                        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
                          ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
                              hessianMatrix u x).PosSemidef) ∧
                    (∀ i j : Fin n,
                        Integrable (fun x => hessianMatrix u x i j)
                            ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
                          (∫ x,
                              hessianMatrix u x i
                                j ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted
                                (-u))) =
                            (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
                      (∀ B : Matrix (Fin n) (Fin n) ℝ,
                        B.IsSymm →
                          Integrable
                              (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
                              ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
                            (∫ x,
                                (B * hessianMatrix u x * B *
                                    hessianMatrix u
                                      x).trace ∂((volume :
                                      Measure (EuclideanSpace ℝ (Fin n))).tilted
                                  (-u))) ≤
                              2 * (B * B).trace) := by
  obtain ⟨u, L, LF, T, hbase, hcutoffs⟩ :=
    exists_trace_cutoff_witness hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hTrace := trace_contraction (μ := μ) hbase
  have hConserve := trace_conservativity (μ := μ) hκ hW hstrong hbase hcutoffs hTrace
  have hEnergy := trace_energy_bound (μ := μ) hκ hW hstrong hbase hcutoffs hConserve
  have hT25 :=
    symmetric_trace_bound (μ := μ) hbase (positive_trace_bound (μ := μ) hbase hEnergy)
  rcases hbase with
    ⟨hc, hl, hnrm, hm, hC1, hG, _hF, _hw, hdata, _hT, _he, _hfirst, _hInv, hmean, _hq, _hflux,
      _hweighted, _hbounded⟩
  exact ⟨u, L, hc, hl, hnrm, hm, hC1, hG, hdata, hmean, hT25⟩

end FunctionalInequalities.Analysis

end RegularMomentHessianTraceBound

section RegularMomentTargetSteinKernel

open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Matrix.Norms.Frobenius

namespace FunctionalInequalities.Analysis

include hn hκ hK hKc hKint hW hstrong hμ hiso in
/--
**Target Stein kernel of the strong regular class** (weak Hessian route to Letwin
arXiv:2607.24164v1, Lemma 2.7 with the
`Theorem 2.5` bound): at the same `u` and `L` as `exists_regular_moment_hessian_trace_bound`, with
all of its fields, and a
measurable everywhere left inverse `Ψ` of that `∇u`, the kernel `∇²u ∘ Ψ` is a Stein kernel of `μ`
that is `μ`-a.e. positive
definite and symmetric, has mean `Id`, Hilbert–Schmidt norm in `L²(μ)` and `∫ |∇²u ∘ Ψ|_HS² dμ ≤
2n`. Not the smooth
diffeomorphism of Lemma 2.2 nor everywhere positive definiteness. -/
theorem exists_regular_moment_target_stein_kernel :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal) (Ψ :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      (ConvexOn ℝ univ u ∧
          LipschitzWith L u ∧
            (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
                  (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
                ContDiff ℝ 1 u ∧
                  LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
                    (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
                        (hessianMatrix u x).PosDef ∧
                          Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
                            ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
                                hessianMatrix u x).PosSemidef) ∧
                      (∀ i j : Fin n,
                          Integrable (fun x => hessianMatrix u x i j)
                              ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
                            (∫ x,
                                hessianMatrix u x i
                                  j ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted
                                  (-u))) =
                              (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
                        (∀ B : Matrix (Fin n) (Fin n) ℝ,
                          B.IsSymm →
                            Integrable
                                (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
                                ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
                              (∫ x,
                                  (B * hessianMatrix u x * B *
                                      hessianMatrix u
                                        x).trace ∂((volume :
                                        Measure (EuclideanSpace ℝ (Fin n))).tilted
                                    (-u))) ≤
                                2 * (B * B).trace)) ∧
        Measurable Ψ ∧
          Function.LeftInverse Ψ (gradient u) ∧
            IsSteinKernel μ (hessianKernel u Ψ) ∧
              (∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))), (hessianKernel u Ψ x).PosDef) ∧
                SymmetricAE μ (hessianKernel u Ψ) ∧
                  MemLp (fun x => hsNorm (hessianKernel u Ψ x)) 2
                      (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
                    (∫ x,
                          hsNorm (hessianKernel u Ψ x) ^
                            2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ≤
                        2 * n ∧
                      (∀ i j : Fin n,
                        (∫ x,
                            hessianKernel u Ψ x i j ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
                          (1 : Matrix (Fin n) (Fin n) ℝ) i j) := by
  classical
  obtain ⟨u, L, hc, hl, hnorm, hm, hC1, hG, hdata, hmean, hT25⟩ :=
    exists_regular_moment_hessian_trace_bound hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨_, Ψ, hΨ, hInv⟩ :=
    measurable_inverse_gradient_of_map_gradient hn hl hc hnorm hC1 hK hKc
      (hKint.mono interior_subset) hW.continuous (hm.trans hμ)
  let ρ : Measure (EuclideanSpace ℝ (Fin n)) := volume.tilted (-u)
  have hexp :
    Integrable (fun y => Real.exp (-u y)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  let ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := ⟨ρ, isProbabilityMeasure_tilted hexp⟩
  have hiAE : ∀ᵐ y ∂ρ, Ψ (gradient u y) = y := ae_of_all _ hInv
  have hPDρ : ∀ᵐ y ∂ρ, (hessianMatrix u y).PosDef := by
    filter_upwards [(tilted_absolutelyContinuous (volume : Measure (EuclideanSpace ℝ (Fin n)))
            (-u)).ae_le
        hdata] with
      y hy
    exact hy.1
  have hEq :
    (fun y => hsNorm (hessianMatrix u y) ^ 2) =ᵐ[ρ] fun y =>
      (hessianMatrix u y * hessianMatrix u y).trace := by
    filter_upwards [hPDρ] with y hy
    exact hsNorm_sq_eq_trace_mul_self _ (Matrix.isHermitian_iff_isSymm.mp hy.isHermitian)
  have hTI := hT25 1 Matrix.isSymm_one
  have hInt : Integrable (fun y => hsNorm (hessianMatrix u y) ^ 2) ρ := by
    apply
      (show Integrable (fun y => (hessianMatrix u y * hessianMatrix u y).trace) ρ by
            simpa only [one_mul, mul_one] using hTI.1).congr
        hEq.symm
  have hHSρ : MemLp (fun y => hsNorm (hessianMatrix u y)) 2 ρ :=
    (memLp_hsNorm_iff_integrable_sq (fun i j => measurable_hessianMatrix_entry u i j)).2 hInt
  have hPD := hessianKernel_posDefAE_of_map hC1 ν μ hm hΨ hiAE hPDρ
  have hSym : SymmetricAE μ (hessianKernel u Ψ) := by
    filter_upwards [hPD] with x hx i j
    exact congrArg (fun A => A j i) hx.isHermitian
  have hHS := memLp_hsNorm_hessianKernel_of_map hC1 ν μ hm hΨ hiAE hHSρ
  have hmeas (i j : Fin n) : Measurable (fun x => hessianKernel u Ψ x i j) :=
    (measurable_hessianMatrix_entry u i j).comp hΨ
  have hHSint :
    (∫ x, hsNorm (hessianKernel u Ψ x) ^ 2 ∂(μ : Measure _)) =
      ∫ y, hsNorm (hessianMatrix u y) ^ 2 ∂ρ := by
    rw [← hm,
      integral_map (BakryEmery.continuous_gradient hC1).measurable.aemeasurable
        ((hsNorm_measurable hmeas).pow_const 2).aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hiAE] with y hy
    simp only [hessianKernel, hy]
  refine
    ⟨u, L, Ψ, ⟨hc, hl, hnorm, hm, hC1, hG, hdata, hmean, hT25⟩, hΨ, hInv,
      KLS.LogConcave.weak_hessianKernel_isSteinKernel hC1 hl hG hnorm μ hm hiso hΨ hiAE, hPD,
      hSym, hHS, ?_, ?_⟩
  · rw [hHSint, integral_congr_ae hEq]
    simpa only [one_mul, mul_one, Matrix.trace_one, Fintype.card_fin, Nat.cast_id] using hTI.2
  · intro i j
    rw [← hm,
      integral_map (BakryEmery.continuous_gradient hC1).measurable.aemeasurable
        (hmeas i j).aestronglyMeasurable]
    calc
      _ = ∫ y, hessianMatrix u y i j ∂ρ := by
        apply integral_congr_ae
        filter_upwards [hiAE] with y hy
        simp only [hessianKernel, hy]
      _ = _ := (hmean i j).2

end FunctionalInequalities.Analysis

end RegularMomentTargetSteinKernel

end

end RegularSource
