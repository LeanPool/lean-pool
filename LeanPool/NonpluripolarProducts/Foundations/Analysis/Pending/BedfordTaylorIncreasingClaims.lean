/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorCollarSymmetry
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorQuasiContinuity

/-!
# Claims for the Bedford–Taylor convergence theorem along increasing sequences

Cegrell's proof of the convergence of mixed Monge–Ampère measures along increasing
sequences of locally bounded plurisubharmonic functions (Błocki, *The complex
Monge–Ampère operator in pluripotential theory*, lecture notes, Thm 2.2.5) is an
induction on the number `q` of slots carrying a genuinely varying sequence. Slots of
index at least `q` are fixed smooth functions with positive semidefinite complex
Hessian; for `q = 0` the measure is a smooth density, absolutely continuous with
respect to Lebesgue measure, so Lebesgue-almost-everywhere convergence of the weights
suffices.

The increasing sequences converge only almost everywhere. No negligible-set theorem
is used later: the symmetric integration by parts
`integral_sub_eq_integral_sub_of_eqOn_compl` takes its place.

This file fixes the notions used by the induction.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- An increasing approximation of `w` on `Ω`: locally bounded plurisubharmonic
functions, pointwise increasing and below `w` on `Ω`, converging to `w` Lebesgue-almost
everywhere on `Ω`. -/
def IsIncApprox (Ω : Opens (ComplexModel n)) (w : ComplexModel n → ℝ)
    (G : ℕ → ComplexModel n → ℝ) : Prop :=
  (∀ k, IsLocallyBoundedPshOn Ω (G k)) ∧ (∀ z ∈ Ω, Monotone fun k => G k z) ∧
    (∀ k, ∀ z ∈ Ω, G k z ≤ w z) ∧
    ∀ᵐ z, z ∈ Ω → Tendsto (fun k => G k z) atTop (𝓝 (w z))

/-- Admissible increasing families at level `q`: every slot is an increasing
approximation of a locally bounded plurisubharmonic limit, and the slots of index at
least `q` are constant, equal to a smooth function with positive semidefinite complex
Hessian. -/
def IsIncAdmissible (q : ℕ) (Ω : Opens (ComplexModel n)) (u : Fin n → ComplexModel n → ℝ)
    (F : Fin n → ℕ → ComplexModel n → ℝ) : Prop :=
  (∀ i, IsLocallyBoundedPshOn Ω (u i)) ∧ (∀ i, IsIncApprox Ω (u i) (F i)) ∧
    ∀ i : Fin n, q ≤ i.val → IsSmoothPsdOn Ω (u i) ∧ ∀ k, EqOn (F i k) (u i) Ω

/-- Unweighted convergence claim at level `q`. -/
def IncPClaim (n q : ℕ) : Prop :=
  ∀ (Ω : Opens (ComplexModel n)) (u : Fin n → ComplexModel n → ℝ)
    (F : Fin n → ℕ → ComplexModel n → ℝ) (μs : ℕ → Measure (ComplexModel n))
    (μ : Measure (ComplexModel n)),
    IsIncAdmissible q Ω u F → (∀ k, IsBTLimit Ω (fun i => F i k) (μs k)) →
      IsBTLimit Ω u μ →
      ∀ χ : ComplexModel n → ℝ, Continuous χ → HasCompactSupport χ →
        tsupport χ ⊆ (Ω : Set (ComplexModel n)) →
        Tendsto (fun k => ∫ z, χ z ∂(μs k)) atTop (𝓝 (∫ z, χ z ∂μ))

/-- Weighted convergence claim at level `q`, with an increasing sequence of weights. -/
def IncWClaim (n q : ℕ) : Prop :=
  ∀ (Ω : Opens (ComplexModel n)) (u : Fin n → ComplexModel n → ℝ)
    (F : Fin n → ℕ → ComplexModel n → ℝ) (μs : ℕ → Measure (ComplexModel n))
    (μ : Measure (ComplexModel n)),
    IsIncAdmissible q Ω u F → (∀ k, IsBTLimit Ω (fun i => F i k) (μs k)) →
      IsBTLimit Ω u μ →
      ∀ (w : ComplexModel n → ℝ) (G : ℕ → ComplexModel n → ℝ),
        IsLocallyBoundedPshOn Ω w → IsIncApprox Ω w G →
        ∀ χ : ComplexModel n → ℝ, Continuous χ → HasCompactSupport χ →
          tsupport χ ⊆ (Ω : Set (ComplexModel n)) →
          Tendsto (fun k => ∫ z, χ z * G k z ∂(μs k)) atTop (𝓝 (∫ z, χ z * w z ∂μ))

/-- The weighted claim at level `q` restricted to *collared data*: `Ω` is an open ball,
and there are a smooth function `g` with positive semidefinite complex Hessian and a
compact `K ⊆ Ω` such that every varying slot (index `< q`), its limit, the weights and
their limit all equal `g` on `Ω \ K`. -/
def IncWCollarClaim (n q : ℕ) : Prop :=
  ∀ (z₀ : ComplexModel n) (R : ℝ) (u : Fin n → ComplexModel n → ℝ)
    (F : Fin n → ℕ → ComplexModel n → ℝ) (μs : ℕ → Measure (ComplexModel n))
    (μ : Measure (ComplexModel n)) (g : ComplexModel n → ℝ) (K : Set (ComplexModel n)),
    let Ω : Opens (ComplexModel n) := ⟨Metric.ball z₀ R, Metric.isOpen_ball⟩
    IsSmoothPsdOn Ω g → IsCompact K → K ⊆ (Ω : Set (ComplexModel n)) →
    IsIncAdmissible q Ω u F →
    (∀ i : Fin n, i.val < q → (∀ z ∈ (Ω : Set (ComplexModel n)) \ K, u i z = g z) ∧
      ∀ k, ∀ z ∈ (Ω : Set (ComplexModel n)) \ K, F i k z = g z) →
    (∀ k, IsBTLimit Ω (fun i => F i k) (μs k)) → IsBTLimit Ω u μ →
    ∀ (w : ComplexModel n → ℝ) (G : ℕ → ComplexModel n → ℝ),
      IsLocallyBoundedPshOn Ω w → IsIncApprox Ω w G →
      (∀ z ∈ (Ω : Set (ComplexModel n)) \ K, w z = g z) →
      (∀ k, ∀ z ∈ (Ω : Set (ComplexModel n)) \ K, G k z = g z) →
      ∀ χ : ComplexModel n → ℝ, Continuous χ → HasCompactSupport χ →
        tsupport χ ⊆ (Ω : Set (ComplexModel n)) →
        Tendsto (fun k => ∫ z, χ z * G k z ∂(μs k)) atTop (𝓝 (∫ z, χ z * w z ∂μ))

/-- A constant sequence is an increasing approximation of its value. -/
theorem isIncApprox_const {Ω : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    (hw : IsLocallyBoundedPshOn Ω w) : IsIncApprox Ω w fun _ => w :=
  ⟨fun _ => hw, fun _ _ => monotone_const, fun _ _ _ => le_rfl,
    Eventually.of_forall fun _ _ => tendsto_const_nhds⟩

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
