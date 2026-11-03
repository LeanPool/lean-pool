/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import LeanPool.TrilinearHilbertTransform.Auto.Sec111aPredictors.Setup

/-!
# Trilinear Hilbert transform: band_scale_sum_core
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate

open scoped Classical in
private def BandScaleSumCoreHT2Statement : Prop :=
  ∀ (G : RealDyadicGrid)
    (κ : LocalKernelClass)
    (J : ℤ × ℤ)
    (S : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2)
    (Fa : ℝ → ℂ)
    (Fb : ℝ → ℂ)
    (za : ℤ × ℤ → ℝ → ℂ)
    (zb : ℤ × ℤ → ℝ → ℂ)
    (Ka : ℝ)
    (Kb : ℝ)
    (_ : (0 : ℝ) ≤ Ka)
    (_ : (0 : ℝ) ≤ Kb)
    (_ : HasDepthEnergy G J Fa za Ka)
    (_ : HasDepthEnergy G J Fb zb Kb)
    (lam : ℤ → ℝ)
    (X : Finset ℤ)
    (tiny : ℤ → ℝ)
    (_ : ∀ (s : ℤ), (0 : ℝ) ≤ tiny s)
    (Θ : ℝ)
    (_ : ∑ s ∈ Finset.image Prod.fst S with s ∉ X, (|lam s| * dyadicGridLength G s ^ (2 : ℕ)
      + tiny s) ≤ Θ)
    (Atot : ℝ),
  let Na : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ (2 : ℕ))
  let Nb : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ (2 : ℕ))
  ∀ (_ : (0 : ℝ) ≤ localKernelSupBound κ)
    (_ : (0 : ℝ) ≤ Atot)
    (Xe : ℤ × ℤ → ℝ)
    (_ : Xe = fun (I : ℤ × ℤ) => ∫ (y : ℝ) in dyadicGridCell G I.1 I.2, ‖za I y‖ ^ (2 : ℕ))
    (Ye : ℤ × ℤ → ℝ)
    (_ : Ye = fun (I : ℤ × ℤ) => ∫ (y : ℝ) in dyadicGridCell G I.1 I.2, ‖zb I y‖ ^ (2 : ℕ)),
  let SN : Finset (ℤ × ℤ) :=
    {I ∈ S | I.1 ∉ X}
  ∑ I ∈ SN, localKernelSupBound κ * Atot * ((2 : ℝ) * Real.pi) * (|lam I.1| *
    dyadicGridLength G I.1 ^ (2 : ℕ) + tiny I.1) * (√(Xe I) * √(Ye I)) ≤
    localKernelSupBound κ * Atot * ((2 : ℝ) * Real.pi) * Θ * Ka * Kb * Na * Nb


open scoped Classical in
private def BandScaleSumCoreHT3Statement : Prop :=
  ∀ (G : RealDyadicGrid)
    (κ : LocalKernelClass)
    (J : ℤ × ℤ)
    (S : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G
      I.1) (w I))
    (a : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ b)
    (ψa : ℝ → ℂ)
    (ψb : ℝ → ℂ)
    (_ : Measurable ψa)
    (_ : Measurable ψb)
    (_ : ∀ (y : ℝ), ‖ψa y‖ ≤ (1 : ℝ))
    (_ : ∀ (y : ℝ), ‖ψb y‖ ≤ (1 : ℝ))
    (Fa : ℝ → ℂ)
    (Fb : ℝ → ℂ)
    (za : ℤ × ℤ → ℝ → ℂ)
    (zb : ℤ × ℤ → ℝ → ℂ)
    (Ka : ℝ)
    (Kb : ℝ)
    (_ : (0 : ℝ) ≤ Ka)
    (_ : (0 : ℝ) ≤ Kb)
    (_ : IsAdmissibleOpponent G J Fa za Ka)
    (_ : IsAdmissibleOpponent G J Fb zb Kb)
    (_ : HasDepthEnergy G J Fa za Ka)
    (_ : HasDepthEnergy G J Fb zb Kb)
    (_ : ∀ (I : ℤ × ℤ), Measurable (za I))
    (_ : ∀ (I : ℤ × ℤ), Measurable (zb I))
    (_ : ∀ (I : ℤ × ℤ), MemLp (za I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (_ : ∀ (I : ℤ × ℤ), MemLp (zb I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (τ : Type)
    [DecidableEq τ]
    (lam : ℤ → ℝ)
    (freq : ℤ → τ → ℝ)
    (P : Finset τ)
    (X : Finset ℤ)
    (env : τ → ℝ)
    (Mt : τ → ℝ)
    (_ : ∀ p ∉ P, ∀ (ξ : ℝ), ∑ x ∈ Finset.image (fun (I : ℤ × ℤ) => (I.1, freq I.1 p / ((↑(↑b
      : ℕ) : ℝ) - (↑(↑a : ℕ) : ℝ)))) S, bumpMultiplier (dyadicGridLength G x.1 * (ξ -
      x.2)) ≤ Mt p)
    (Λ : ℝ)
    (_ : ∑ s ∈ Finset.image Prod.fst S, (2 : ℝ) * Real.pi * |lam s| * dyadicGridLength G s ^
      (2 : ℕ) ≤ Λ)
    (Tt : ℝ)
    (_ : Summable fun (p : τ) => if p ∈ P then (0 : ℝ) else env p * (linearScaleConst κ * Mt
      p + localKernelSupBound κ * Λ))
    (_ : (∑' (p : τ), if p ∈ P then (0 : ℝ) else env p * (linearScaleConst κ * Mt p +
      localKernelSupBound κ * Λ)) ≤ Tt),
  let Na : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ (2 : ℕ))
  let Nb : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ (2 : ℕ))
  ∀ (Hf : ℤ × ℤ → (ℝ → ℂ) → ℂ)
    (_ : ∀ (I : ℤ × ℤ) (φ : ℝ → ℂ), (separatedLocalForm (dyadicGridLength G I.1) (w I) φ a b
      (fun (y : ℝ) => ψa y * za I y) fun (y : ℝ) => ψb y * zb I y) = Hf I φ),
  let SN : Finset (ℤ × ℤ) :=
    {I ∈ S | I.1 ∉ X}
  ∀ (_ : ∀ (p : τ), (0 : ℝ) ≤ env p)
    (_ : ∀ I ∈ SN, Summable fun (p : τ) => if p ∈ P then (0 : ℝ) else env p *
      (dyadicGridLength G I.1 * ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖)),
  (∑ I ∈ SN, ∑' (p : τ), if p ∈ P then (0 : ℝ) else env p * (dyadicGridLength G I.1 *
    ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖)) ≤ Tt * Ka * Kb * Na * Nb


open scoped Classical in
private def BandScaleSumCoreHexcStatement : Prop :=
  ∀ (G : RealDyadicGrid)
    (κ : LocalKernelClass)
    (J : ℤ × ℤ)
    (S : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G
      I.1) (w I))
    (a : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ b)
    (Q : ℝ → ℂ)
    (_ : Measurable Q)
    (_ : ∀ (t : ℝ), ‖Q t‖ ≤ (1 : ℝ))
    (ψa : ℝ → ℂ)
    (ψb : ℝ → ℂ)
    (Fa : ℝ → ℂ)
    (Fb : ℝ → ℂ)
    (za : ℤ × ℤ → ℝ → ℂ)
    (zb : ℤ × ℤ → ℝ → ℂ)
    (Ka : ℝ)
    (Kb : ℝ)
    (_ : (0 : ℝ) ≤ Ka)
    (_ : (0 : ℝ) ≤ Kb)
    (_ : HasDepthEnergy G J Fa za Ka)
    (_ : HasDepthEnergy G J Fb zb Kb)
    (A₀ : ℝ)
    (_ : ∀ I ∈ S, ∀ (ξ : ℝ), bandAmplitude Q (dyadicGridLength G I.1) ξ ≤ A₀)
    (X : Finset ℤ),
  let Na : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ (2 : ℕ))
  let Nb : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ (2 : ℕ))
  ∀ (_ : (0 : ℝ) ≤ kernelFourierConst κ)
    (_ : (0 : ℝ) ≤ A₀)
    (Hf : ℤ × ℤ → (ℝ → ℂ) → ℂ)
    (_ : ∀ (I : ℤ × ℤ) (φ : ℝ → ℂ), (separatedLocalForm (dyadicGridLength G I.1) (w I) φ a b
      (fun (y : ℝ) => ψa y * za I y) fun (y : ℝ) => ψb y * zb I y) = Hf I φ)
    (Xe : ℤ × ℤ → ℝ)
    (_ : Xe = fun (I : ℤ × ℤ) => ∫ (y : ℝ) in dyadicGridCell G I.1 I.2, ‖za I y‖ ^ (2 : ℕ))
    (Ye : ℤ × ℤ → ℝ)
    (_ : Ye = fun (I : ℤ × ℤ) => ∫ (y : ℝ) in dyadicGridCell G I.1 I.2, ‖zb I y‖ ^ (2 : ℕ))
    (_ : ∀ (I : ℤ × ℤ), MemLp (fun (y : ℝ) => ψa y * za I y) (2 : ENNReal) (volume.restrict
      (Set.Ico (dyadicGridLeft G I.1 I.2) (dyadicGridLeft G I.1 I.2 + dyadicGridLength G
      I.1))))
    (_ : ∀ (I : ℤ × ℤ), MemLp (fun (y : ℝ) => ψb y * zb I y) (2 : ENNReal) (volume.restrict
      (Set.Ico (dyadicGridLeft G I.1 I.2) (dyadicGridLeft G I.1 I.2 + dyadicGridLength G
      I.1))))
    (_ : ∀ (I : ℤ × ℤ), Measurable fun (y : ℝ) => ψa y * za I y)
    (_ : ∀ (I : ℤ × ℤ), Measurable fun (y : ℝ) => ψb y * zb I y)
    (_ : ∀ (I : ℤ × ℤ), dyadicGridLength G I.1 * (√((dyadicGridLength G I.1)⁻¹ * ∫ (y : ℝ) in
      Set.Ico (dyadicGridLeft G I.1 I.2) (dyadicGridLeft G I.1 I.2 + dyadicGridLength G
      I.1), ‖ψa y * za I y‖ ^ (2 : ℕ)) * √((dyadicGridLength G I.1)⁻¹ * ∫ (y : ℝ) in
      Set.Ico (dyadicGridLeft G I.1 I.2) (dyadicGridLeft G I.1 I.2 + dyadicGridLength G
      I.1), ‖ψb y * zb I y‖ ^ (2 : ℕ))) ≤ √(Xe I) * √(Ye I)),
  let SX : Finset (ℤ × ℤ) :=
    {I ∈ S | I.1 ∈ X}
  ∑ I ∈ SX, dyadicGridLength G I.1 * ‖Hf I Q‖ ≤ kernelFourierConst κ * A₀ * (↑X.card :
    ℝ) * Ka * Kb * Na * Nb


open scoped Classical in
private def BandScaleSumCoreHT1Statement : Prop :=
  ∀ (G : RealDyadicGrid)
    (κ : LocalKernelClass)
    (J : ℤ × ℤ)
    (S : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G
      I.1) (w I))
    (a : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ b)
    (ψa : ℝ → ℂ)
    (ψb : ℝ → ℂ)
    (_ : Measurable ψa)
    (_ : Measurable ψb)
    (_ : ∀ (y : ℝ), ‖ψa y‖ ≤ (1 : ℝ))
    (_ : ∀ (y : ℝ), ‖ψb y‖ ≤ (1 : ℝ))
    (Fa : ℝ → ℂ)
    (Fb : ℝ → ℂ)
    (za : ℤ × ℤ → ℝ → ℂ)
    (zb : ℤ × ℤ → ℝ → ℂ)
    (Ka : ℝ)
    (Kb : ℝ)
    (_ : (0 : ℝ) ≤ Ka)
    (_ : (0 : ℝ) ≤ Kb)
    (_ : IsAdmissibleOpponent G J Fa za Ka)
    (_ : IsAdmissibleOpponent G J Fb zb Kb)
    (_ : ∀ (I : ℤ × ℤ), Measurable (za I))
    (_ : ∀ (I : ℤ × ℤ), Measurable (zb I))
    (_ : ∀ (I : ℤ × ℤ), MemLp (za I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (_ : ∀ (I : ℤ × ℤ), MemLp (zb I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (τ : Type)
    (freq : ℤ → τ → ℝ)
    (P : Finset τ)
    (X : Finset ℤ)
    (ε₂ : ℝ)
    (L₂ : ℝ)
    (_ : (3 : ℝ) ≤ L₂)
    (dχ : ℕ)
    (χ : Fin dχ → ℝ)
    (Bc : ℝ)
    (_ : (2 : ℝ) ≤ Bc)
    (_ : ∀ s ∈ Finset.image Prod.fst S, ∀ p ∈ P, ∃ (q : Fin dχ → ℚ), (∀ (j : Fin dχ),
      (↑(rationalHeight (q j)) : ℝ) ≤ Bc) ∧ freq s p / ((↑(↑b : ℕ) : ℝ) - (↑(↑a : ℕ) :
      ℝ)) = ∑ j : Fin dχ, (↑(q j) : ℝ) * χ j),
  let Na : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ (2 : ℕ))
  let Nb : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ (2 : ℕ))
  ∀ (Hf : ℤ × ℤ → (ℝ → ℂ) → ℂ)
    (_ : ∀ (I : ℤ × ℤ) (φ : ℝ → ℂ), (separatedLocalForm (dyadicGridLength G I.1) (w I) φ a b
      (fun (y : ℝ) => ψa y * za I y) fun (y : ℝ) => ψb y * zb I y) = Hf I φ),
  let SN : Finset (ℤ × ℤ) :=
    {I ∈ S | I.1 ∉ X}
  ∀ (rep : ℤ → τ → τ)
    (_ : ∀ s ∈ Finset.image Prod.fst S, s ∉ X → (∀ p ∈ P, rep s p ∈ P ∧ dyadicGridLength G s
      * |freq s p - freq s (rep s p)| ≤ ε₂) ∧ ∀ p ∈ P, ∀ q ∈ P, rep s p ≠ rep s q → L₂ ≤
      dyadicGridLength G s * |freq s (rep s p) - freq s (rep s q)|)
    (R : ℤ → Finset ℝ)
    (_ : R = fun (s : ℤ) => Finset.image (fun (p : τ) => freq s (rep s p)) P)
    (_ : (↑(↑b : ℕ) : ℝ) - (↑(↑a : ℕ) : ℝ) ≠ (0 : ℝ))
    (_ : |(↑(↑b : ℕ) : ℝ) - (↑(↑a : ℕ) : ℝ)| ≤ (3 : ℝ)),
  ∑ I ∈ SN, ∑ x ∈ R I.1, dyadicGridLength G I.1 * ‖Hf I fun (t : ℝ) => (↑((𝐞 : ℝ →
    Circle) (x * t)) : ℂ)‖ ≤ linearScaleConst κ * clumpMultiplicity dχ Bc * Ka * Kb *
    Na * Nb


open scoped Classical in
private def BandScaleSumCoreHcellNStatement : Prop :=
  ∀ (G : RealDyadicGrid)
    (κ : LocalKernelClass)
    (S : Finset (ℤ × ℤ))
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G
      I.1) (w I))
    (a : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ b)
    (Q : ℝ → ℂ)
    (ψa : ℝ → ℂ)
    (ψb : ℝ → ℂ)
    (za : ℤ × ℤ → ℝ → ℂ)
    (zb : ℤ × ℤ → ℝ → ℂ)
    (A₀ : ℝ)
    (τ : Type)
    [Countable τ]
    [DecidableEq τ]
    (coef : ℤ → τ → ℂ)
    (lam : ℤ → ℝ)
    (freq : ℤ → τ → ℝ)
    (_ : ∀ s ∈ Finset.image Prod.fst S, ∀ (t : ℝ), |t| ≤ (2 : ℝ) * dyadicGridLength G s →
      HasSum (fun (p : τ) => coef s p * quadPhase (lam s) (freq s p) t) (Q t))
    (_ : ∀ (s : ℤ), Summable fun (p : τ) => ‖coef s p‖)
    (P : Finset τ)
    (X : Finset ℤ)
    (ε₂ : ℝ)
    (L₂ : ℝ)
    (tiny : ℤ → ℝ)
    (_ : ∀ (s : ℤ), (0 : ℝ) ≤ tiny s)
    (_ : ∀ s ∈ Finset.image Prod.fst S, s ∉ X → ∀ p ∈ P, ∀ q ∈ P, dyadicGridLength G s *
      |freq s p - freq s q| ≤ ε₂ → dyadicGridLength G s * |freq s p - freq s q| ≤ tiny s)
    (Atot : ℝ)
    (_ : ∀ (s : ℤ), ∑ p ∈ P, ‖coef s p‖ ≤ Atot)
    (env : τ → ℝ)
    (_ : ∀ (s : ℤ) (p : τ), ‖coef s p‖ ≤ env p)
    (_ : (0 : ℝ) ≤ localKernelSupBound κ)
    (_ : (0 : ℝ) ≤ Atot)
    (Hf : ℤ × ℤ → (ℝ → ℂ) → ℂ)
    (_ : ∀ (I : ℤ × ℤ) (φ : ℝ → ℂ), (separatedLocalForm (dyadicGridLength G I.1) (w I) φ a b
      (fun (y : ℝ) => ψa y * za I y) fun (y : ℝ) => ψb y * zb I y) = Hf I φ)
    (Xe : ℤ × ℤ → ℝ)
    (Ye : ℤ × ℤ → ℝ)
    (_ : ∀ (I : ℤ × ℤ), MemLp (fun (y : ℝ) => ψa y * za I y) (2 : ENNReal) (volume.restrict
      (Set.Ico (dyadicGridLeft G I.1 I.2) (dyadicGridLeft G I.1 I.2 + dyadicGridLength G
      I.1))))
    (_ : ∀ (I : ℤ × ℤ), MemLp (fun (y : ℝ) => ψb y * zb I y) (2 : ENNReal) (volume.restrict
      (Set.Ico (dyadicGridLeft G I.1 I.2) (dyadicGridLeft G I.1 I.2 + dyadicGridLength G
      I.1))))
    (_ : ∀ (I : ℤ × ℤ), Measurable fun (y : ℝ) => ψa y * za I y)
    (_ : ∀ (I : ℤ × ℤ), Measurable fun (y : ℝ) => ψb y * zb I y)
    (_ : ∀ (I : ℤ × ℤ), dyadicGridLength G I.1 * (√((dyadicGridLength G I.1)⁻¹ * ∫ (y : ℝ) in
      Set.Ico (dyadicGridLeft G I.1 I.2) (dyadicGridLeft G I.1 I.2 + dyadicGridLength G
      I.1), ‖ψa y * za I y‖ ^ (2 : ℕ)) * √((dyadicGridLength G I.1)⁻¹ * ∫ (y : ℝ) in
      Set.Ico (dyadicGridLeft G I.1 I.2) (dyadicGridLeft G I.1 I.2 + dyadicGridLength G
      I.1), ‖ψb y * zb I y‖ ^ (2 : ℕ))) ≤ √(Xe I) * √(Ye I)),
  let SN : Finset (ℤ × ℤ) :=
    {I ∈ S | I.1 ∉ X}
  ∀ (rep : ℤ → τ → τ)
    (_ : ∀ s ∈ Finset.image Prod.fst S, s ∉ X → (∀ p ∈ P, rep s p ∈ P ∧ dyadicGridLength G s
      * |freq s p - freq s (rep s p)| ≤ ε₂) ∧ ∀ p ∈ P, ∀ q ∈ P, rep s p ≠ rep s q → L₂ ≤
      dyadicGridLength G s * |freq s (rep s p) - freq s (rep s q)|)
    (R : ℤ → Finset ℝ)
    (_ : R = fun (s : ℤ) => Finset.image (fun (p : τ) => freq s (rep s p)) P)
    (bc : ℤ → ℝ → ℂ)
    (_ : bc = fun (s : ℤ) (x : ℝ) => ∑ p ∈ P with freq s (rep s p) = x, coef s p)
    (_ : ∀ s ∈ Finset.image Prod.fst S, s ∉ X → ∀ x ∈ R s, ‖bc s x‖ ≤ A₀)
    (_ : ∀ I ∈ SN, Summable fun (p : τ) => if p ∈ P then (0 : ℝ) else env p *
      (dyadicGridLength G I.1 * ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖)),
  ∀ I ∈ SN, dyadicGridLength G I.1 * ‖Hf I Q‖ ≤ A₀ * ∑ x ∈ R I.1, dyadicGridLength G
    I.1 * ‖Hf I fun (t : ℝ) => (↑((𝐞 : ℝ → Circle) (x * t)) : ℂ)‖ +
    localKernelSupBound κ * Atot * ((2 : ℝ) * Real.pi) * (|lam I.1| * dyadicGridLength
    G I.1 ^ (2 : ℕ) + tiny I.1) * (√(Xe I) * √(Ye I)) + ∑' (p : τ), if p ∈ P then (0 :
    ℝ) else env p * (dyadicGridLength G I.1 * ‖Hf I (quadPhase (lam I.1) (freq I.1
    p))‖)


open scoped Classical in
private def BandScaleSumCoreStage2Statement : Prop :=
  ∀ (G : RealDyadicGrid)
    (κ : LocalKernelClass)
    (J : ℤ × ℤ)
    (S : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G
      I.1) (w I))
    (a : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ b)
    (Q : ℝ → ℂ)
    (ψa : ℝ → ℂ)
    (ψb : ℝ → ℂ)
    (_ : Measurable ψa)
    (_ : Measurable ψb)
    (_ : ∀ (y : ℝ), ‖ψa y‖ ≤ (1 : ℝ))
    (_ : ∀ (y : ℝ), ‖ψb y‖ ≤ (1 : ℝ))
    (Fa : ℝ → ℂ)
    (Fb : ℝ → ℂ)
    (za : ℤ × ℤ → ℝ → ℂ)
    (zb : ℤ × ℤ → ℝ → ℂ)
    (Ka : ℝ)
    (Kb : ℝ)
    (_ : (0 : ℝ) ≤ Ka)
    (_ : (0 : ℝ) ≤ Kb)
    (_ : IsAdmissibleOpponent G J Fa za Ka)
    (_ : IsAdmissibleOpponent G J Fb zb Kb)
    (_ : HasDepthEnergy G J Fa za Ka)
    (_ : HasDepthEnergy G J Fb zb Kb)
    (_ : ∀ (I : ℤ × ℤ), Measurable (za I))
    (_ : ∀ (I : ℤ × ℤ), Measurable (zb I))
    (_ : ∀ (I : ℤ × ℤ), MemLp (za I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (_ : ∀ (I : ℤ × ℤ), MemLp (zb I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (A₀ : ℝ)
    (τ : Type)
    [DecidableEq τ]
    (lam : ℤ → ℝ)
    (freq : ℤ → τ → ℝ)
    (P : Finset τ)
    (X : Finset ℤ)
    (ε₂ : ℝ)
    (L₂ : ℝ)
    (_ : (3 : ℝ) ≤ L₂)
    (tiny : ℤ → ℝ)
    (_ : ∀ (s : ℤ), (0 : ℝ) ≤ tiny s)
    (Θ : ℝ)
    (_ : ∑ s ∈ Finset.image Prod.fst S with s ∉ X, (|lam s| * dyadicGridLength G s ^ (2 : ℕ)
      + tiny s) ≤ Θ)
    (Atot : ℝ)
    (dχ : ℕ)
    (χ : Fin dχ → ℝ)
    (Bc : ℝ)
    (_ : (2 : ℝ) ≤ Bc)
    (_ : ∀ s ∈ Finset.image Prod.fst S, ∀ p ∈ P, ∃ (q : Fin dχ → ℚ), (∀ (j : Fin dχ),
      (↑(rationalHeight (q j)) : ℝ) ≤ Bc) ∧ freq s p / ((↑(↑b : ℕ) : ℝ) - (↑(↑a : ℕ) :
      ℝ)) = ∑ j : Fin dχ, (↑(q j) : ℝ) * χ j)
    (env : τ → ℝ)
    (Mt : τ → ℝ)
    (_ : ∀ p ∉ P, ∀ (ξ : ℝ), ∑ x ∈ Finset.image (fun (I : ℤ × ℤ) => (I.1, freq I.1 p / ((↑(↑b
      : ℕ) : ℝ) - (↑(↑a : ℕ) : ℝ)))) S, bumpMultiplier (dyadicGridLength G x.1 * (ξ -
      x.2)) ≤ Mt p)
    (Λ : ℝ)
    (_ : ∑ s ∈ Finset.image Prod.fst S, (2 : ℝ) * Real.pi * |lam s| * dyadicGridLength G s ^
      (2 : ℕ) ≤ Λ)
    (Tt : ℝ)
    (_ : Summable fun (p : τ) => if p ∈ P then (0 : ℝ) else env p * (linearScaleConst κ * Mt
      p + localKernelSupBound κ * Λ))
    (_ : (∑' (p : τ), if p ∈ P then (0 : ℝ) else env p * (linearScaleConst κ * Mt p +
      localKernelSupBound κ * Λ)) ≤ Tt),
  let Na : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ (2 : ℕ))
  let Nb : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ (2 : ℕ))
  ∀ (_ : (0 : ℝ) ≤ localKernelSupBound κ)
    (_ : (0 : ℝ) ≤ Atot)
    (_ : (0 : ℝ) ≤ A₀)
    (Hf : ℤ × ℤ → (ℝ → ℂ) → ℂ)
    (_ : ∀ (I : ℤ × ℤ) (φ : ℝ → ℂ), (separatedLocalForm (dyadicGridLength G I.1) (w I) φ a b
      (fun (y : ℝ) => ψa y * za I y) fun (y : ℝ) => ψb y * zb I y) = Hf I φ)
    (Xe : ℤ × ℤ → ℝ)
    (_ : Xe = fun (I : ℤ × ℤ) => ∫ (y : ℝ) in dyadicGridCell G I.1 I.2, ‖za I y‖ ^ (2 : ℕ))
    (Ye : ℤ × ℤ → ℝ)
    (_ : Ye = fun (I : ℤ × ℤ) => ∫ (y : ℝ) in dyadicGridCell G I.1 I.2, ‖zb I y‖ ^ (2 : ℕ)),
  let SX : Finset (ℤ × ℤ) :=
    {I ∈ S | I.1 ∈ X}
  let SN : Finset (ℤ × ℤ) :=
    {I ∈ S | I.1 ∉ X}
  ∀ (_ : ∑ I ∈ SX, dyadicGridLength G I.1 * ‖Hf I Q‖ ≤ kernelFourierConst κ * A₀ * (↑X.card :
      ℝ) * Ka * Kb * Na * Nb)
    (rep : ℤ → τ → τ)
    (_ : ∀ s ∈ Finset.image Prod.fst S, s ∉ X → (∀ p ∈ P, rep s p ∈ P ∧ dyadicGridLength G s
      * |freq s p - freq s (rep s p)| ≤ ε₂) ∧ ∀ p ∈ P, ∀ q ∈ P, rep s p ≠ rep s q → L₂ ≤
      dyadicGridLength G s * |freq s (rep s p) - freq s (rep s q)|)
    (R : ℤ → Finset ℝ)
    (_ : R = fun (s : ℤ) => Finset.image (fun (p : τ) => freq s (rep s p)) P)
    (_ : ∀ (p : τ), (0 : ℝ) ≤ env p)
    (_ : ∀ I ∈ SN, Summable fun (p : τ) => if p ∈ P then (0 : ℝ) else env p *
      (dyadicGridLength G I.1 * ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖))
    (_ : ∀ I ∈ SN, dyadicGridLength G I.1 * ‖Hf I Q‖ ≤ A₀ * ∑ x ∈ R I.1, dyadicGridLength G
      I.1 * ‖Hf I fun (t : ℝ) => (↑((𝐞 : ℝ → Circle) (x * t)) : ℂ)‖ +
      localKernelSupBound κ * Atot * ((2 : ℝ) * Real.pi) * (|lam I.1| * dyadicGridLength
      G I.1 ^ (2 : ℕ) + tiny I.1) * (√(Xe I) * √(Ye I)) + ∑' (p : τ), if p ∈ P then (0 :
      ℝ) else env p * (dyadicGridLength G I.1 * ‖Hf I (quadPhase (lam I.1) (freq I.1
      p))‖)),
  ∑ x ∈ S with x.1 ∈ X, dyadicGridLength G x.1 * ‖Hf x Q‖ + ∑ x ∈ S with x.1 ∉ X,
    dyadicGridLength G x.1 * ‖Hf x Q‖ ≤ (kernelFourierConst κ * A₀ * (↑X.card : ℝ) +
    A₀ * linearScaleConst κ * clumpMultiplicity dχ Bc + localKernelSupBound κ * Atot *
    ((2 : ℝ) * Real.pi) * Θ + Tt) * Ka * Kb * Na * Nb


open scoped Classical in
private def BandScaleSumCoreStage1Statement : Prop :=
  ∀ (G : RealDyadicGrid)
    (κ : LocalKernelClass)
    (J : ℤ × ℤ)
    (S : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G
      I.1) (w I))
    (a : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ b)
    (Q : ℝ → ℂ)
    (_ : Measurable Q)
    (_ : ∀ (t : ℝ), ‖Q t‖ ≤ (1 : ℝ))
    (ψa : ℝ → ℂ)
    (ψb : ℝ → ℂ)
    (_ : Measurable ψa)
    (_ : Measurable ψb)
    (_ : ∀ (y : ℝ), ‖ψa y‖ ≤ (1 : ℝ))
    (_ : ∀ (y : ℝ), ‖ψb y‖ ≤ (1 : ℝ))
    (Fa : ℝ → ℂ)
    (Fb : ℝ → ℂ)
    (za : ℤ × ℤ → ℝ → ℂ)
    (zb : ℤ × ℤ → ℝ → ℂ)
    (Ka : ℝ)
    (Kb : ℝ)
    (_ : (0 : ℝ) ≤ Ka)
    (_ : (0 : ℝ) ≤ Kb)
    (_ : IsAdmissibleOpponent G J Fa za Ka)
    (_ : IsAdmissibleOpponent G J Fb zb Kb)
    (_ : HasDepthEnergy G J Fa za Ka)
    (_ : HasDepthEnergy G J Fb zb Kb)
    (_ : ∀ (I : ℤ × ℤ), Measurable (za I))
    (_ : ∀ (I : ℤ × ℤ), Measurable (zb I))
    (_ : ∀ (I : ℤ × ℤ), MemLp (za I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (_ : ∀ (I : ℤ × ℤ), MemLp (zb I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (A₀ : ℝ)
    (_ : ∀ I ∈ S, ∀ (ξ : ℝ), bandAmplitude Q (dyadicGridLength G I.1) ξ ≤ A₀)
    (τ : Type)
    [Countable τ]
    [DecidableEq τ]
    (coef : ℤ → τ → ℂ)
    (lam : ℤ → ℝ)
    (freq : ℤ → τ → ℝ)
    (_ : ∀ s ∈ Finset.image Prod.fst S, ∀ (t : ℝ), |t| ≤ (2 : ℝ) * dyadicGridLength G s →
      HasSum (fun (p : τ) => coef s p * quadPhase (lam s) (freq s p) t) (Q t))
    (_ : ∀ (s : ℤ), Summable fun (p : τ) => ‖coef s p‖)
    (P : Finset τ)
    (X : Finset ℤ)
    (ε₁ : ℝ)
    (ε₂ : ℝ)
    (L₂ : ℝ)
    (_ : (0 : ℝ) ≤ ε₁)
    (_ : (0 : ℝ) ≤ ε₂)
    (_ : (3 : ℝ) ≤ L₂)
    (_ : ∀ s ∈ Finset.image Prod.fst S, s ∉ X → |lam s| * dyadicGridLength G s ^ (2 : ℕ) ≤ ε₁)
    (tiny : ℤ → ℝ)
    (_ : ∀ (s : ℤ), (0 : ℝ) ≤ tiny s)
    (_ : ∀ s ∈ Finset.image Prod.fst S, s ∉ X → ∀ p ∈ P, ∀ q ∈ P, dyadicGridLength G s *
      |freq s p - freq s q| ≤ ε₂ → dyadicGridLength G s * |freq s p - freq s q| ≤ tiny s)
    (Θ : ℝ)
    (_ : ∑ s ∈ Finset.image Prod.fst S with s ∉ X, (|lam s| * dyadicGridLength G s ^ (2 : ℕ)
      + tiny s) ≤ Θ)
    (Atot : ℝ)
    (τt : ℝ)
    (Cζ : ℝ)
    (_ : ∀ (η : ℝ), η ≠ (0 : ℝ) → ‖∫ (u : ℝ), (↑(bandCutoff u) : ℂ) * (↑((𝐞 : ℝ → Circle)
      (-(η * u))) : ℂ)‖ ≤ Cζ / η ^ (2 : ℕ))
    (_ : (0 : ℝ) ≤ Cζ)
    (_ : ∀ (s : ℤ), ∑ p ∈ P, ‖coef s p‖ ≤ Atot)
    (_ : ∀ (s : ℤ), (∑' (p : τ), if p ∈ P then (0 : ℝ) else ‖coef s p‖) ≤ τt)
    (_ : τt + Atot * ((8 : ℝ) * Real.pi * ε₁ + (4 : ℝ) * Real.pi * ε₂) + Cζ * Atot / L₂ ^ (2
      : ℕ) ≤ A₀ / (2 : ℝ))
    (dχ : ℕ)
    (χ : Fin dχ → ℝ)
    (Bc : ℝ)
    (_ : (2 : ℝ) ≤ Bc)
    (_ : ∀ s ∈ Finset.image Prod.fst S, ∀ p ∈ P, ∃ (q : Fin dχ → ℚ), (∀ (j : Fin dχ),
      (↑(rationalHeight (q j)) : ℝ) ≤ Bc) ∧ freq s p / ((↑(↑b : ℕ) : ℝ) - (↑(↑a : ℕ) :
      ℝ)) = ∑ j : Fin dχ, (↑(q j) : ℝ) * χ j)
    (env : τ → ℝ)
    (_ : ∀ (s : ℤ) (p : τ), ‖coef s p‖ ≤ env p)
    (_ : Summable env)
    (Mt : τ → ℝ)
    (_ : ∀ p ∉ P, ∀ (ξ : ℝ), ∑ x ∈ Finset.image (fun (I : ℤ × ℤ) => (I.1, freq I.1 p / ((↑(↑b
      : ℕ) : ℝ) - (↑(↑a : ℕ) : ℝ)))) S, bumpMultiplier (dyadicGridLength G x.1 * (ξ -
      x.2)) ≤ Mt p)
    (Λ : ℝ)
    (_ : ∑ s ∈ Finset.image Prod.fst S, (2 : ℝ) * Real.pi * |lam s| * dyadicGridLength G s ^
      (2 : ℕ) ≤ Λ)
    (Tt : ℝ)
    (_ : Summable fun (p : τ) => if p ∈ P then (0 : ℝ) else env p * (linearScaleConst κ * Mt
      p + localKernelSupBound κ * Λ))
    (_ : (∑' (p : τ), if p ∈ P then (0 : ℝ) else env p * (linearScaleConst κ * Mt p +
      localKernelSupBound κ * Λ)) ≤ Tt),
  let Na : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ (2 : ℕ))
  let Nb : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ (2 : ℕ))
  ∀ (_ : (0 : ℝ) ≤ localKernelSupBound κ)
    (_ : (0 : ℝ) ≤ Atot)
    (_ : (0 : ℝ) ≤ A₀)
    (Hf : ℤ × ℤ → (ℝ → ℂ) → ℂ)
    (_ : ∀ (I : ℤ × ℤ) (φ : ℝ → ℂ), (separatedLocalForm (dyadicGridLength G I.1) (w I) φ a b
      (fun (y : ℝ) => ψa y * za I y) fun (y : ℝ) => ψb y * zb I y) = Hf I φ)
    (Xe : ℤ × ℤ → ℝ)
    (_ : Xe = fun (I : ℤ × ℤ) => ∫ (y : ℝ) in dyadicGridCell G I.1 I.2, ‖za I y‖ ^ (2 : ℕ))
    (Ye : ℤ × ℤ → ℝ)
    (_ : Ye = fun (I : ℤ × ℤ) => ∫ (y : ℝ) in dyadicGridCell G I.1 I.2, ‖zb I y‖ ^ (2 : ℕ))
    (_ : ∀ (I : ℤ × ℤ), MemLp (fun (y : ℝ) => ψa y * za I y) (2 : ENNReal) (volume.restrict
      (Set.Ico (dyadicGridLeft G I.1 I.2) (dyadicGridLeft G I.1 I.2 + dyadicGridLength G
      I.1))))
    (_ : ∀ (I : ℤ × ℤ), MemLp (fun (y : ℝ) => ψb y * zb I y) (2 : ENNReal) (volume.restrict
      (Set.Ico (dyadicGridLeft G I.1 I.2) (dyadicGridLeft G I.1 I.2 + dyadicGridLength G
      I.1))))
    (_ : ∀ (I : ℤ × ℤ), Measurable fun (y : ℝ) => ψa y * za I y)
    (_ : ∀ (I : ℤ × ℤ), Measurable fun (y : ℝ) => ψb y * zb I y)
    (_ : ∀ (I : ℤ × ℤ), dyadicGridLength G I.1 * (√((dyadicGridLength G I.1)⁻¹ * ∫ (y : ℝ) in
      Set.Ico (dyadicGridLeft G I.1 I.2) (dyadicGridLeft G I.1 I.2 + dyadicGridLength G
      I.1), ‖ψa y * za I y‖ ^ (2 : ℕ)) * √((dyadicGridLength G I.1)⁻¹ * ∫ (y : ℝ) in
      Set.Ico (dyadicGridLeft G I.1 I.2) (dyadicGridLeft G I.1 I.2 + dyadicGridLength G
      I.1), ‖ψb y * zb I y‖ ^ (2 : ℕ))) ≤ √(Xe I) * √(Ye I)),
  let SX : Finset (ℤ × ℤ) :=
    {I ∈ S | I.1 ∈ X}
  ∀ (_ : ∑ I ∈ SX, dyadicGridLength G I.1 * ‖Hf I Q‖ ≤ kernelFourierConst κ * A₀ * (↑X.card :
      ℝ) * Ka * Kb * Na * Nb)
    (rep : ℤ → τ → τ)
    (_ : ∀ s ∈ Finset.image Prod.fst S, s ∉ X → (∀ p ∈ P, rep s p ∈ P ∧ dyadicGridLength G s
      * |freq s p - freq s (rep s p)| ≤ ε₂) ∧ ∀ p ∈ P, ∀ q ∈ P, rep s p ≠ rep s q → L₂ ≤
      dyadicGridLength G s * |freq s (rep s p) - freq s (rep s q)|)
    (R : ℤ → Finset ℝ)
    (_ : R = fun (s : ℤ) => Finset.image (fun (p : τ) => freq s (rep s p)) P),
  ∑ x ∈ S with x.1 ∈ X, dyadicGridLength G x.1 * ‖Hf x Q‖ + ∑ x ∈ S with x.1 ∉ X,
    dyadicGridLength G x.1 * ‖Hf x Q‖ ≤ (kernelFourierConst κ * A₀ * (↑X.card : ℝ) +
    A₀ * linearScaleConst κ * clumpMultiplicity dχ Bc + localKernelSupBound κ * Atot *
    ((2 : ℝ) * Real.pi) * Θ + Tt) * Ka * Kb * Na * Nb




private theorem band_scale_sum_core_hT2 : BandScaleSumCoreHT2Statement := by
  classical
  intro G κ J S hSJ Fa Fb za zb Ka Kb hKa hKb hEa hEb lam X tiny htiny0 Θ hΘ Atot Na Nb hC hAtot0
    Xe hXe Ye hYe SN
  have hw' := depth_weighted_energy_sum G J SN
    (fun I hI => hSJ I (Finset.mem_filter.mp hI).1)
    (fun s => localKernelSupBound κ * Atot * (2 * Real.pi) *
      (|lam s| * dyadicGridLength G s ^ 2 + tiny s))
    (fun s => by have := htiny0 s; positivity) hKa hKb hEa hEb
  simp only [hXe, hYe]
  refine hw'.trans ?_
  have hsub : SN.image Prod.fst ⊆ (S.image Prod.fst).filter (fun s => s ∉ X) := by
    intro s hs
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.mp hI).1,
      (Finset.mem_filter.mp hI).2⟩
  have hle : ∑ s ∈ SN.image Prod.fst, localKernelSupBound κ * Atot * (2 * Real.pi) *
      (|lam s| * dyadicGridLength G s ^ 2 + tiny s) ≤
      localKernelSupBound κ * Atot * (2 * Real.pi) * Θ := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun s _ _ => by have := htiny0 s; positivity)).trans hΘ) (by positivity)
  have hK : 0 ≤ Ka * Kb * Na * Nb := by positivity
  calc (∑ s ∈ SN.image Prod.fst, localKernelSupBound κ * Atot * (2 * Real.pi) *
        (|lam s| * dyadicGridLength G s ^ 2 + tiny s)) * Ka * Kb * Na * Nb
      = (∑ s ∈ SN.image Prod.fst, localKernelSupBound κ * Atot * (2 * Real.pi) *
        (|lam s| * dyadicGridLength G s ^ 2 + tiny s)) * (Ka * Kb * Na * Nb) := by ring
    _ ≤ (localKernelSupBound κ * Atot * (2 * Real.pi) * Θ) * (Ka * Kb * Na * Nb) :=
        mul_le_mul_of_nonneg_right hle hK
    _ = _ := by ring
-- (T3) the tails



private theorem band_scale_sum_core_hT3 : BandScaleSumCoreHT3Statement := by
  classical
  intro G κ J S hSJ w hw a b hab ψa ψb hψam hψbm hψa hψb Fa Fb za zb Ka Kb hKa hKb hza hzb hEa hEb
    hzam hzbm hza2 hzb2 τ inst_1 lam freq P X env Mt hMt Λ hΛ Tt hTs hTt Na Nb Hf eHf SN henv0 hgs
  rw [← Summable.tsum_finsetSum hgs]
  have hK : 0 ≤ Ka * Kb * Na * Nb := by positivity
  have hpt : ∀ p, ∑ I ∈ SN, (if p ∈ P then 0 else
      env p * (dyadicGridLength G I.1 * ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖)) ≤
      (if p ∈ P then 0 else
        env p * (linearScaleConst κ * Mt p + localKernelSupBound κ * Λ)) *
        (Ka * Kb * Na * Nb) := by
    intro p
    by_cases hp : p ∈ P
    · simp [hp]
    simp only [hp, ite_false]
    rw [← Finset.mul_sum]
    have hsp := single_phase_scale_sum G κ J SN
      (fun I hI => hSJ I (Finset.mem_filter.mp hI).1) w
      (fun I hI => hw I (Finset.mem_filter.mp hI).1) hab lam (fun s => freq s p)
      hψam hψbm hψa hψb hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2
      (M := Mt p) (fun ξ => (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_image (Finset.filter_subset _ _))
        (fun _ _ _ => bumpMultiplier_nonneg _)).trans (hMt p hp ξ))
      (Λ := Λ) ((Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_image (Finset.filter_subset _ _))
        (fun s _ _ => by positivity)).trans hΛ)
    simp only [eHf] at hsp
    calc env p * ∑ I ∈ SN, dyadicGridLength G I.1 *
          ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖
        ≤ env p * ((linearScaleConst κ * Mt p + localKernelSupBound κ * Λ) * Ka * Kb *
          Na * Nb) := mul_le_mul_of_nonneg_left hsp (henv0 p)
      _ = _ := by ring
  have hsr : Summable (fun p => (if p ∈ P then 0 else
      env p * (linearScaleConst κ * Mt p + localKernelSupBound κ * Λ)) *
        (Ka * Kb * Na * Nb)) := hTs.mul_right _
  refine (Summable.tsum_le_tsum hpt (summable_sum fun I hI => hgs I hI) hsr).trans ?_
  rw [tsum_mul_right]
  calc (∑' p, (if p ∈ P then 0 else
        env p * (linearScaleConst κ * Mt p + localKernelSupBound κ * Λ))) *
        (Ka * Kb * Na * Nb) ≤ Tt * (Ka * Kb * Na * Nb) :=
        mul_le_mul_of_nonneg_right hTt hK
    _ = _ := by ring
-- assemble



private theorem band_scale_sum_core_hexc : BandScaleSumCoreHexcStatement := by
  classical
  intro G κ J S hSJ w hw a b hab Q hQm hQ1 ψa ψb Fa Fb za zb Ka Kb hKa hKb hEa hEb A₀ hband X Na
    Nb hKF hA00 Hf eHf Xe hXe Ye hYe hma hmb hFam hFbm hnorm SX
  have hcell : ∀ I ∈ SX, dyadicGridLength G I.1 * ‖Hf I Q‖ ≤
      kernelFourierConst κ * A₀ * (Real.sqrt (Xe I) * Real.sqrt (Ye I)) := by
    intro I hI
    have hIS := (Finset.mem_filter.mp hI).1
    have hr := dyadicGridLength_pos G I.1
    have h := separated_form_le_band hr (hw I hIS) hab hQm hQ1 (hband I hIS)
      (hFam I) (hFbm I) (hma I) (hmb I)
    rw [eHf] at h
    calc dyadicGridLength G I.1 * ‖Hf I Q‖
        ≤ dyadicGridLength G I.1 * (kernelFourierConst κ * A₀ *
          Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
            (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψa y * za I y‖ ^ 2) *
          Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
            (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψb y * zb I y‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h hr.le
      _ = kernelFourierConst κ * A₀ * (dyadicGridLength G I.1 *
          (Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
            (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψa y * za I y‖ ^ 2) *
          Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
            (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψb y * zb I y‖ ^ 2))) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hnorm I) (by positivity)
  have hw' := depth_weighted_energy_sum G J SX (fun I hI => hSJ I (Finset.mem_filter.mp hI).1)
    (fun _ => kernelFourierConst κ * A₀) (fun _ => by positivity) hKa hKb hEa hEb
  refine (Finset.sum_le_sum hcell).trans ?_
  simp only [hXe, hYe]
  refine hw'.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((SX.image Prod.fst).card : ℝ) ≤ X.card := by
    refine Nat.cast_le.mpr (Finset.card_le_card fun s hs => ?_)
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hs
    exact (Finset.mem_filter.mp hI).2
  have hK : 0 ≤ Ka * Kb * Na * Nb := by positivity
  calc ((SX.image Prod.fst).card : ℝ) * (kernelFourierConst κ * A₀) * Ka * Kb * Na * Nb
      = ((SX.image Prod.fst).card : ℝ) * (kernelFourierConst κ * A₀ * (Ka * Kb * Na * Nb)) := by
        ring
    _ ≤ (X.card : ℝ) * (kernelFourierConst κ * A₀ * (Ka * Kb * Na * Nb)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring
-- representatives on the non-exceptional depths



private theorem band_scale_sum_core_hT1 : BandScaleSumCoreHT1Statement := by
  classical
  intro G κ J S hSJ w hw a b hab ψa ψb hψam hψbm hψa hψb Fa Fb za zb Ka Kb hKa hKb hza hzb hzam
    hzbm hza2 hzb2 τ freq P X ε₂ L₂ hL₂ dχ χ Bc hBc hrat Na Nb Hf eHf SN rep hrep R hR
  let S' : Finset ((_ : ℤ × ℤ) × ℝ) :=
    SN.sigma fun (I : ℤ × ℤ) => R I.1
  intro hd hdabs
  rw [← Finset.sum_sigma SN (fun I => R I.1)
    (fun i => dyadicGridLength G (i.1).1 *
      ‖Hf i.1 (fun t => (Real.fourierChar (i.2 * t) : ℂ))‖)]
  have hmult : ∀ ξ, ∑ p ∈ S'.image (fun i => ((i.1).1, i.2 / ((b : ℝ) - (a : ℝ)))),
      bumpMultiplier (dyadicGridLength G p.1 * (ξ - p.2)) ≤ clumpMultiplicity dχ Bc := by
    intro ξ
    refine rational_center_multiplicity G χ hBc _ (fun p hp => ?_) (fun p hp q hq hpq hne => ?_) ξ
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hI, hx⟩ := Finset.mem_sigma.mp hi
      have hIS := (Finset.mem_filter.mp hI).1
      rw [hR] at hx
      obtain ⟨p', hp', hx'⟩ := Finset.mem_image.mp hx
      have hs : (i.1).1 ∈ S.image Prod.fst := Finset.mem_image_of_mem _ hIS
      have hsX := (Finset.mem_filter.mp hI).2
      obtain ⟨q, hq, hqe⟩ := hrat (i.1).1 hs (rep (i.1).1 p') ((hrep _ hs hsX).1 p' hp').1
      refine ⟨q, hq, ?_⟩
      simp only
      rw [← hx', hqe]
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hI, hx⟩ := Finset.mem_sigma.mp hi
      obtain ⟨hJ, hy⟩ := Finset.mem_sigma.mp hj
      simp only at hpq hne ⊢
      have hIS := (Finset.mem_filter.mp hI).1
      have hs : (i.1).1 ∈ S.image Prod.fst := Finset.mem_image_of_mem _ hIS
      have hsX := (Finset.mem_filter.mp hI).2
      rw [hpq] at hx
      have hxy : i.2 ≠ j.2 := fun h => hne (by rw [hpq, h])
      rw [hR] at hx hy
      obtain ⟨p', hp', hx'⟩ := Finset.mem_image.mp hx
      obtain ⟨q', hq', hy'⟩ := Finset.mem_image.mp hy
      have hrepne : rep (j.1).1 p' ≠ rep (j.1).1 q' := fun h => hxy (by rw [← hx', ← hy', h])
      have hJS := (Finset.mem_filter.mp hJ).1
      have hsJ : (j.1).1 ∈ S.image Prod.fst := Finset.mem_image_of_mem _ hJS
      have hsXJ := (Finset.mem_filter.mp hJ).2
      have hL := (hrep (j.1).1 hsJ hsXJ).2 p' hp' q' hq' hrepne
      rw [hx', hy'] at hL
      rw [hpq, ← sub_div, abs_div, mul_div_assoc']
      rw [le_div_iff₀ (abs_pos.mpr hd)]
      calc 1 * |(b : ℝ) - (a : ℝ)| ≤ 3 := by linarith
        _ ≤ L₂ := hL₂
        _ ≤ _ := hL
  have h := linear_phase_scale_sum G κ J (fun i : (Σ _ : ℤ × ℤ, ℝ) => i.1) S'
    (fun i hi => hSJ i.1 (Finset.mem_filter.mp (Finset.mem_sigma.mp hi).1).1)
    (fun i => w i.1)
    (fun i hi => hw i.1 (Finset.mem_filter.mp (Finset.mem_sigma.mp hi).1).1) hab
    (fun i => i.2)
    (fun i _ j _ hij => by
      simp only [Prod.mk.injEq] at hij
      obtain ⟨h1, h2⟩ := hij
      have h2' : i.2 = j.2 := by
        have hd' : (b : ℝ) - (a : ℝ) ≠ 0 := hd
        field_simp at h2
        exact h2
      exact Sigma.ext h1 (heq_of_eq h2'))
    hψam hψbm hψa hψb hKa hKb hza hzb hzam hzbm
    (fun i _ => integrableOn_cell_of_memLp G i.1 (hza2 i.1))
    (fun i _ => integrableOn_cell_of_memLp G i.1 (hzb2 i.1)) hmult
  simp only [eHf] at h
  exact h
-- (T2) the replacement errors



private theorem band_scale_sum_core_hcellN : BandScaleSumCoreHcellNStatement := by
  classical
  intro G κ S w hw a b hab Q ψa ψb za zb A₀ τ inst inst_1 coef lam freq hexp hcs P X ε₂ L₂ tiny
    htiny0 htiny Atot hAtot env henv hC hAtot0 Hf eHf Xe Ye hma hmb hFam hFbm hnorm SN rep hrep R
    hR bc hbc hbcle hgs I hI
  have hIS := (Finset.mem_filter.mp hI).1
  have hsX := (Finset.mem_filter.mp hI).2
  have hs : I.1 ∈ S.image Prod.fst := Finset.mem_image_of_mem _ hIS
  have hr := dyadicGridLength_pos G I.1
  have hβ : ∀ p ∈ P, dyadicGridLength G I.1 * |freq I.1 p - freq I.1 (rep I.1 p)| ≤
      tiny I.1 := fun p hp =>
    htiny I.1 hs hsX p hp (rep I.1 p) ((hrep I.1 hs hsX).1 p hp).1
      ((hrep I.1 hs hsX).1 p hp).2
  have h := clump_cell_bound hr (hw I hIS) hab (coef I.1) (hcs I.1) (lam I.1) (freq I.1)
    (fun t ht => hexp I.1 hs t (by linarith [abs_nonneg t])) P (rep I.1) hβ
    (hFam I) (hFbm I) (hma I) (hmb I)
  simp only [eHf] at h
  have hsumP := hAtot I.1
  -- term 1
  have t1 : dyadicGridLength G I.1 * ∑ x ∈ P.image (fun p => freq I.1 (rep I.1 p)),
      ‖∑ p ∈ P.filter (fun p => freq I.1 (rep I.1 p) = x), coef I.1 p‖ *
        ‖Hf I (fun t => (Real.fourierChar (x * t) : ℂ))‖ ≤
      A₀ * ∑ x ∈ R I.1, dyadicGridLength G I.1 *
        ‖Hf I (fun t => (Real.fourierChar (x * t) : ℂ))‖ := by
    rw [Finset.mul_sum, Finset.mul_sum, hR]
    refine Finset.sum_le_sum fun x hx => ?_
    have hb := hbcle I.1 hs hsX x (by rw [hR]; exact hx)
    rw [hbc] at hb
    calc dyadicGridLength G I.1 *
          (‖∑ p ∈ P.filter (fun p => freq I.1 (rep I.1 p) = x), coef I.1 p‖ *
            ‖Hf I (fun t => (Real.fourierChar (x * t) : ℂ))‖)
        = ‖∑ p ∈ P.filter (fun p => freq I.1 (rep I.1 p) = x), coef I.1 p‖ *
            (dyadicGridLength G I.1 * ‖Hf I (fun t => (Real.fourierChar (x * t) : ℂ))‖) := by
          ring
      _ ≤ A₀ * (dyadicGridLength G I.1 * ‖Hf I (fun t => (Real.fourierChar (x * t) : ℂ))‖) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
  -- term 2
  have t2 : dyadicGridLength G I.1 * ((∑ p ∈ P, ‖coef I.1 p‖) * (localKernelSupBound κ *
        (2 * Real.pi * (|lam I.1| * dyadicGridLength G I.1 ^ 2 + tiny I.1)) *
        Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
          (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψa y * za I y‖ ^ 2) *
        Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
          (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψb y * zb I y‖ ^ 2))) ≤
      localKernelSupBound κ * Atot * (2 * Real.pi) *
        (|lam I.1| * dyadicGridLength G I.1 ^ 2 + tiny I.1) *
        (Real.sqrt (Xe I) * Real.sqrt (Ye I)) := by
    have hq0 : 0 ≤ |lam I.1| * dyadicGridLength G I.1 ^ 2 + tiny I.1 := by
      have := htiny0 I.1; positivity
    calc _ = (∑ p ∈ P, ‖coef I.1 p‖) * (localKernelSupBound κ * (2 * Real.pi) *
          (|lam I.1| * dyadicGridLength G I.1 ^ 2 + tiny I.1)) *
          (dyadicGridLength G I.1 *
          (Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
            (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψa y * za I y‖ ^ 2) *
          Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
            (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψb y * zb I y‖ ^ 2))) := by
          ring
      _ ≤ Atot * (localKernelSupBound κ * (2 * Real.pi) *
          (|lam I.1| * dyadicGridLength G I.1 ^ 2 + tiny I.1)) *
          (Real.sqrt (Xe I) * Real.sqrt (Ye I)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hsumP (by positivity)) (hnorm I)
            (by positivity) (by positivity)
      _ = _ := by ring
  -- term 3
  have t3 : dyadicGridLength G I.1 * ∑' p, (if p ∈ P then 0 else
        ‖coef I.1 p‖ * ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖) ≤
      ∑' p, (if p ∈ P then 0 else
        env p * (dyadicGridLength G I.1 * ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖)) := by
    rw [← tsum_mul_left]
    have hs1 : Summable (fun p => dyadicGridLength G I.1 * (if p ∈ P then 0 else
        ‖coef I.1 p‖ * ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖)) := by
      refine Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity) (fun p => ?_)
        (hgs I hI)
      split_ifs
      · simp
      · calc dyadicGridLength G I.1 * (‖coef I.1 p‖ *
              ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖)
            = ‖coef I.1 p‖ * (dyadicGridLength G I.1 *
              ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (henv I.1 p) (by positivity)
    refine Summable.tsum_le_tsum (fun p => ?_) hs1 (hgs I hI)
    split_ifs
    · simp
    · calc dyadicGridLength G I.1 * (‖coef I.1 p‖ *
            ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖)
          = ‖coef I.1 p‖ * (dyadicGridLength G I.1 *
            ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (henv I.1 p) (by positivity)
  calc dyadicGridLength G I.1 * ‖Hf I Q‖ ≤ dyadicGridLength G I.1 * (_ + _ + _) :=
        mul_le_mul_of_nonneg_left h hr.le
    _ = _ := by rw [mul_add, mul_add]
    _ ≤ _ := add_le_add (add_le_add t1 t2) t3
-- (T1) the clump terms, via the linear-phase scale sum over (cell, center) pairs



private theorem band_scale_sum_core_stage_2 : BandScaleSumCoreStage2Statement := by
  classical
  intro G κ J S hSJ w hw a b hab Q ψa ψb hψam hψbm hψa hψb Fa Fb za zb Ka Kb hKa hKb hza hzb hEa
    hEb hzam hzbm hza2 hzb2 A₀ τ inst_1 lam freq P X ε₂ L₂ hL₂ tiny htiny0 Θ hΘ Atot dχ χ Bc hBc
    hrat env Mt hMt Λ hΛ Tt hTs hTt Na Nb hC hAtot0 hA00 Hf eHf Xe hXe Ye hYe SX SN hexc rep hrep
    R hR henv0 hgs hcellN
  set! S' : Finset (Σ _ : ℤ × ℤ, ℝ) := SN.sigma (fun I => R I.1) with hS'
  have hd := fin_cast_sub_ne hab
  have hdabs : |(b : ℝ) - (a : ℝ)| ≤ 3 := by
    have ha := abs_fin_four_le a
    have hb := abs_fin_four_le b
    rw [abs_le] at ha hb ⊢; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2,
      show (0 : ℝ) ≤ (a : ℝ) by positivity, show (0 : ℝ) ≤ (b : ℝ) by positivity]
  have hT1 : ∑ I ∈ SN, ∑ x ∈ R I.1, dyadicGridLength G I.1 *
      ‖Hf I (fun t => (Real.fourierChar (x * t) : ℂ))‖ ≤
      linearScaleConst κ * clumpMultiplicity dχ Bc * Ka * Kb * Na * Nb := by
    expose_names
    exact @band_scale_sum_core_hT1 G κ J S hSJ w hw a b hab ψa ψb hψam hψbm hψa hψb Fa Fb za zb Ka
      Kb hKa hKb hza hzb hzam hzbm hza2 hzb2 τ freq P X ε₂ L₂ hL₂ dχ χ Bc hBc hrat Hf eHf rep hrep
      R hR hd hdabs
  have hT2 : ∑ I ∈ SN, localKernelSupBound κ * Atot * (2 * Real.pi) *
      (|lam I.1| * dyadicGridLength G I.1 ^ 2 + tiny I.1) *
      (Real.sqrt (Xe I) * Real.sqrt (Ye I)) ≤
      localKernelSupBound κ * Atot * (2 * Real.pi) * Θ * Ka * Kb * Na * Nb := by
    expose_names
    exact @band_scale_sum_core_hT2 G κ J S hSJ Fa Fb za zb Ka Kb hKa hKb hEa hEb lam X tiny htiny0
      Θ hΘ Atot hC hAtot0 Xe hXe Ye hYe
  have hT3 : ∑ I ∈ SN, ∑' p, (if p ∈ P then 0 else
      env p * (dyadicGridLength G I.1 * ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖)) ≤
      Tt * Ka * Kb * Na * Nb := by
    expose_names
    exact @band_scale_sum_core_hT3 G κ J S hSJ w hw a b hab ψa ψb hψam hψbm hψa hψb Fa Fb za zb Ka
      Kb hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 τ inst_1 lam freq P X env Mt hMt Λ hΛ Tt hTs
      hTt Hf eHf henv0 hgs
  have hN : ∑ I ∈ SN, dyadicGridLength G I.1 * ‖Hf I Q‖ ≤
      A₀ * (linearScaleConst κ * clumpMultiplicity dχ Bc * Ka * Kb * Na * Nb) +
        localKernelSupBound κ * Atot * (2 * Real.pi) * Θ * Ka * Kb * Na * Nb +
        Tt * Ka * Kb * Na * Nb := by
    refine (Finset.sum_le_sum hcellN).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hT1 hA00) hT2) hT3
  calc ∑ I ∈ SX, dyadicGridLength G I.1 * ‖Hf I Q‖ +
        ∑ I ∈ SN, dyadicGridLength G I.1 * ‖Hf I Q‖
      ≤ kernelFourierConst κ * A₀ * X.card * Ka * Kb * Na * Nb +
        (A₀ * (linearScaleConst κ * clumpMultiplicity dχ Bc * Ka * Kb * Na * Nb) +
          localKernelSupBound κ * Atot * (2 * Real.pi) * Θ * Ka * Kb * Na * Nb +
          Tt * Ka * Kb * Na * Nb) := add_le_add hexc hN
    _ = _ := by ring



private theorem band_scale_sum_core_stage_1 : BandScaleSumCoreStage1Statement := by
  classical
  intro G κ J S hSJ w hw a b hab Q hQm hQ1 ψa ψb hψam hψbm hψa hψb Fa Fb za zb Ka Kb hKa hKb hza
    hzb hEa hEb hzam hzbm hza2 hzb2 A₀ hband τ inst inst_1 coef lam freq hexp hcs P X ε₁ ε₂ L₂ hε₁
    hε₂ hL₂ hquad tiny htiny0 htiny Θ hΘ Atot τt Cζ hCζ hCζ0 hAtot htail hsmall dχ χ Bc hBc hrat
    env henv hens Mt hMt Λ hΛ Tt hTs hTt Na Nb hC hAtot0 hA00 Hf eHf Xe hXe Ye hYe hma hmb hFam
    hFbm hnorm SX
  let SN : Finset (ℤ × ℤ) :=
    {I ∈ S | I.1 ∉ X}
  intro hexc rep hrep R hR
  obtain ⟨bc, hbc⟩ : ∃ bc : ℤ → ℝ → ℂ, bc = fun s x =>
      ∑ p ∈ P.filter (fun p => freq s (rep s p) = x), coef s p := ⟨_, rfl⟩
  have hL₂0 : 0 < L₂ := by linarith
  -- clump coefficients are small
  have hbcle : ∀ s ∈ S.image Prod.fst, s ∉ X → ∀ x ∈ R s, ‖bc s x‖ ≤ A₀ := by
    intro s hs hsX x hx
    obtain ⟨I, hIS, hIs⟩ := Finset.mem_image.mp hs
    have hr := dyadicGridLength_pos G s
    have hsep : ∀ c ∈ R s, ∀ c' ∈ R s, c ≠ c' → L₂ ≤ dyadicGridLength G s * |c - c'| := by
      intro c hc c' hc' hne
      rw [hR] at hc hc'
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc'
      exact (hrep s hs hsX).2 p hp q hq (fun h => hne (by rw [h]))
    have herr : ∀ t, |t| ≤ 2 * dyadicGridLength G s →
        ‖Q t - ∑ c ∈ R s, bc s c * (Real.fourierChar (c * t) : ℂ)‖ ≤
          τt + Atot * (8 * Real.pi * ε₁ + 4 * Real.pi * ε₂) := by
      intro t ht
      rw [hR, hbc]
      exact clump_sup_error (coef s) (hcs s) (lam s) (freq s) ht (hexp s hs t ht) P (rep s)
        hε₁ hε₂ (fun p hp => ((hrep s hs hsX).1 p hp).2) (hquad s hs hsX) (htail s) (hAtot s)
    have hA : ∀ ξ, bandAmplitude Q (dyadicGridLength G s) ξ ≤ A₀ := by
      rw [← hIs]; exact hband I hIS
    have h := clump_coefficient_le hQm hQ1 hr (R s) (bc s) hL₂0 hCζ hCζ0 hsep herr hA hx
    have hsum : ∑ c' ∈ R s, ‖bc s c'‖ ≤ Atot := by
      rw [hR, hbc]; exact (clump_coeff_sum_le P (coef s) _).trans (hAtot s)
    have : Cζ * (∑ c' ∈ R s, ‖bc s c'‖) / L₂ ^ 2 ≤ Cζ * Atot / L₂ ^ 2 := by gcongr
    linarith
  -- uniform bound of single forms
  have hphase : ∀ I ∈ S, ∀ φ : ℝ → ℂ, (∀ t, ‖φ t‖ ≤ 1) →
      dyadicGridLength G I.1 * ‖Hf I φ‖ ≤ localKernelSupBound κ *
        (Real.sqrt (Xe I) * Real.sqrt (Ye I)) := by
    intro I hIS φ hφ
    have hr := dyadicGridLength_pos G I.1
    have h := separatedLocalForm_sup_le hr (hw I hIS) hab zero_le_one (fun t _ => hφ t)
      (hFam I) (hFbm I) (hma I) (hmb I)
    rw [eHf] at h
    calc dyadicGridLength G I.1 * ‖Hf I φ‖
        ≤ dyadicGridLength G I.1 * (localKernelSupBound κ * 1 *
            Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
              (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψa y * za I y‖ ^ 2) *
            Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
              (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψb y * zb I y‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h hr.le
      _ = localKernelSupBound κ * (dyadicGridLength G I.1 *
            (Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
              (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψa y * za I y‖ ^ 2) *
            Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
              (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψb y * zb I y‖ ^ 2))) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hnorm I) hC
  have hXY0 : ∀ I, 0 ≤ Real.sqrt (Xe I) * Real.sqrt (Ye I) := fun I => by positivity
  have henv0 : ∀ p, 0 ≤ env p := fun p => (norm_nonneg _).trans (henv 0 p)
  -- the tail summability at one cell
  have hgs : ∀ I ∈ SN, Summable (fun p => if p ∈ P then 0 else
      env p * (dyadicGridLength G I.1 * ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖)) := by
    intro I hI
    have hIS := (Finset.mem_filter.mp hI).1
    have hr := dyadicGridLength_pos G I.1
    refine Summable.of_nonneg_of_le (fun p => by
        have := henv0 p; split_ifs <;> positivity) (fun p => ?_)
      (hens.mul_right (localKernelSupBound κ * (Real.sqrt (Xe I) * Real.sqrt (Ye I))))
    split_ifs
    · have := henv0 p; have := hXY0 I; positivity
    · exact mul_le_mul_of_nonneg_left (hphase I hIS _ fun t => (norm_quadPhase _ _ t).le)
        (henv0 p)
  -- the per-cell bound on non-exceptional cells
  have hcellN : ∀ I ∈ SN, dyadicGridLength G I.1 * ‖Hf I Q‖ ≤
      A₀ * ∑ x ∈ R I.1, dyadicGridLength G I.1 *
          ‖Hf I (fun t => (Real.fourierChar (x * t) : ℂ))‖ +
        localKernelSupBound κ * Atot * (2 * Real.pi) *
          (|lam I.1| * dyadicGridLength G I.1 ^ 2 + tiny I.1) *
          (Real.sqrt (Xe I) * Real.sqrt (Ye I)) +
        ∑' p, (if p ∈ P then 0 else
          env p * (dyadicGridLength G I.1 * ‖Hf I (quadPhase (lam I.1) (freq I.1 p))‖)) := by
    expose_names
    exact @band_scale_sum_core_hcellN G κ S w hw a b hab Q ψa ψb za zb A₀ τ inst inst_1 coef lam
      freq hexp hcs P X ε₂ L₂ tiny htiny0 htiny Atot hAtot env henv hC hAtot0 Hf eHf Xe Ye hma hmb
      hFam hFbm hnorm rep hrep R hR bc hbc hbcle hgs
  expose_names
  exact @band_scale_sum_core_stage_2 G κ J S hSJ w hw a b hab Q ψa ψb hψam hψbm hψa hψb Fa Fb za
    zb Ka Kb hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 A₀ τ inst_1 lam freq P X ε₂ L₂ hL₂ tiny
    htiny0 Θ hΘ Atot dχ χ Bc hBc hrat env Mt hMt Λ hΛ Tt hTs hTt hC hAtot0 hA00 Hf eHf Xe hXe Ye
    hYe hexc rep hrep R hR henv0 hgs hcellN


/-- Blueprint lem:predictors, proof lines 1517–1542 (core of `eq:band-scale-sum`): given at
every depth an expansion `Q = Σ_p c_p e(λ t² + γ_p t)` on `|t| ≤ 2r`, a finite catalog `P`,
a set `X` of exceptional depths, and outside `X` the tiny/large dichotomy for the catalog
frequencies and tiny quadratics, the absolute scale sum is bounded by the exceptional
contribution, the clump contribution (with clump coefficients `≤ A₀`), the replacement
errors and the tail outside the catalog. -/
theorem band_scale_sum_core (G : RealDyadicGrid) (κ : LocalKernelClass) (J : ℤ × ℤ)
    (S : Finset (ℤ × ℤ))
    (hSJ : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    {a b : Fin 4} (hab : a ≠ b) {Q : ℝ → ℂ} (hQm : Measurable Q) (hQ1 : ∀ t, ‖Q t‖ ≤ 1)
    {ψa ψb : ℝ → ℂ} (hψam : Measurable ψa) (hψbm : Measurable ψb)
    (hψa : ∀ y, ‖ψa y‖ ≤ 1) (hψb : ∀ y, ‖ψb y‖ ≤ 1)
    {Fa Fb : ℝ → ℂ} {za zb : ℤ × ℤ → ℝ → ℂ} {Ka Kb : ℝ} (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb)
    (hza : IsAdmissibleOpponent G J Fa za Ka) (hzb : IsAdmissibleOpponent G J Fb zb Kb)
    (hEa : HasDepthEnergy G J Fa za Ka) (hEb : HasDepthEnergy G J Fb zb Kb)
    (hzam : ∀ I, Measurable (za I)) (hzbm : ∀ I, Measurable (zb I))
    (hza2 : ∀ I, MemLp (za I) 2 (volume.restrict (dyadicGridCell G I.1 I.2)))
    (hzb2 : ∀ I, MemLp (zb I) 2 (volume.restrict (dyadicGridCell G I.1 I.2)))
    {A₀ : ℝ} (hband : ∀ I ∈ S, ∀ ξ, bandAmplitude Q (dyadicGridLength G I.1) ξ ≤ A₀)
    {τ : Type} [Countable τ] [DecidableEq τ] (coef : ℤ → τ → ℂ) (lam : ℤ → ℝ)
    (freq : ℤ → τ → ℝ)
    (hexp : ∀ s ∈ S.image Prod.fst, ∀ t, |t| ≤ 2 * dyadicGridLength G s →
      HasSum (fun p => coef s p * quadPhase (lam s) (freq s p) t) (Q t))
    (hcs : ∀ s, Summable (fun p => ‖coef s p‖))
    (P : Finset τ) (X : Finset ℤ) {ε₁ ε₂ L₂ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (h3 : 3 * ε₂ < L₂)
    (hL₂ : 3 ≤ L₂)
    (hdich : ∀ s ∈ S.image Prod.fst, s ∉ X → ∀ p ∈ P, ∀ q ∈ P,
      dyadicGridLength G s * |freq s p - freq s q| ≤ ε₂ ∨
        L₂ ≤ dyadicGridLength G s * |freq s p - freq s q|)
    (hquad : ∀ s ∈ S.image Prod.fst, s ∉ X → |lam s| * dyadicGridLength G s ^ 2 ≤ ε₁)
    (tiny : ℤ → ℝ) (htiny0 : ∀ s, 0 ≤ tiny s)
    (htiny : ∀ s ∈ S.image Prod.fst, s ∉ X → ∀ p ∈ P, ∀ q ∈ P,
      dyadicGridLength G s * |freq s p - freq s q| ≤ ε₂ →
        dyadicGridLength G s * |freq s p - freq s q| ≤ tiny s)
    {Θ : ℝ} (hΘ : ∑ s ∈ (S.image Prod.fst).filter (fun s => s ∉ X),
      (|lam s| * dyadicGridLength G s ^ 2 + tiny s) ≤ Θ)
    {Atot τt Cζ : ℝ}
    (hCζ : ∀ η : ℝ, η ≠ 0 →
      ‖∫ u, (bandCutoff u : ℂ) * (Real.fourierChar (-(η * u)) : ℂ)‖ ≤ Cζ / η ^ 2)
    (hCζ0 : 0 ≤ Cζ)
    (hAtot : ∀ s, ∑ p ∈ P, ‖coef s p‖ ≤ Atot)
    (htail : ∀ s, ∑' p, (if p ∈ P then 0 else ‖coef s p‖) ≤ τt)
    (hsmall : τt + Atot * (8 * Real.pi * ε₁ + 4 * Real.pi * ε₂) + Cζ * Atot / L₂ ^ 2 ≤
      A₀ / 2)
    {dχ : ℕ} (χ : Fin dχ → ℝ) {Bc : ℝ} (hBc : 2 ≤ Bc)
    (hrat : ∀ s ∈ S.image Prod.fst, ∀ p ∈ P, ∃ q : Fin dχ → ℚ,
      (∀ j, (rationalHeight (q j) : ℝ) ≤ Bc) ∧
        freq s p / ((b : ℝ) - (a : ℝ)) = ∑ j, (q j : ℝ) * χ j)
    (env : τ → ℝ) (henv : ∀ s p, ‖coef s p‖ ≤ env p) (hens : Summable env)
    (Mt : τ → ℝ)
    (hMt : ∀ p, p ∉ P → ∀ ξ, ∑ x ∈ S.image (fun I => (I.1, freq I.1 p / ((b : ℝ) - (a : ℝ)))),
      bumpMultiplier (dyadicGridLength G x.1 * (ξ - x.2)) ≤ Mt p)
    {Λ : ℝ} (hΛ : ∑ s ∈ S.image Prod.fst, 2 * Real.pi * |lam s| * dyadicGridLength G s ^ 2 ≤ Λ)
    {Tt : ℝ}
    (hTs : Summable (fun p => if p ∈ P then 0 else
      env p * (linearScaleConst κ * Mt p + localKernelSupBound κ * Λ)))
    (hTt : ∑' p, (if p ∈ P then 0 else
      env p * (linearScaleConst κ * Mt p + localKernelSupBound κ * Λ)) ≤ Tt) :
    ∑ I ∈ S, dyadicGridLength G I.1 *
      ‖separatedLocalForm (dyadicGridLength G I.1) (w I) Q a b
        (fun y => ψa y * za I y) (fun y => ψb y * zb I y)‖ ≤
      (kernelFourierConst κ * A₀ * X.card + A₀ * linearScaleConst κ * clumpMultiplicity dχ Bc +
        localKernelSupBound κ * Atot * (2 * Real.pi) * Θ + Tt) * Ka * Kb *
        Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2) *
        Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) := by
  classical
  set Na := Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2)
  set Nb := Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2)
  have hNa0 : 0 ≤ Na := Real.sqrt_nonneg _
  have hNb0 : 0 ≤ Nb := Real.sqrt_nonneg _
  have hC := localKernelSupBound_nonneg κ
  have hKF := kernelFourierConst_nonneg κ
  have hlin0 := linearScaleConst_nonneg κ
  have hτt0 : 0 ≤ τt := (tsum_nonneg fun p => by split_ifs <;> positivity).trans (htail 0)
  have hAtot0 : 0 ≤ Atot := (Finset.sum_nonneg fun p _ => norm_nonneg _).trans (hAtot 0)
  have hA00 : 0 ≤ A₀ := by
    have : 0 ≤ Atot * (8 * Real.pi * ε₁ + 4 * Real.pi * ε₂) := by positivity
    have : 0 ≤ Cζ * Atot / L₂ ^ 2 := by positivity
    linarith
  -- abbreviations for the cell data
  obtain ⟨Hf, hHf⟩ : ∃ Hf : ℤ × ℤ → (ℝ → ℂ) → ℂ, Hf = fun I φ =>
      separatedLocalForm (dyadicGridLength G I.1) (w I) φ a b
        (fun y => ψa y * za I y) (fun y => ψb y * zb I y) := ⟨_, rfl⟩
  have eHf : ∀ I φ, separatedLocalForm (dyadicGridLength G I.1) (w I) φ a b
      (fun y => ψa y * za I y) (fun y => ψb y * zb I y) = Hf I φ := fun I φ => by rw [hHf]
  obtain ⟨Xe, hXe⟩ : ∃ Xe : ℤ × ℤ → ℝ, Xe = fun I =>
      ∫ y in dyadicGridCell G I.1 I.2, ‖za I y‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Ye, hYe⟩ : ∃ Ye : ℤ × ℤ → ℝ, Ye = fun I =>
      ∫ y in dyadicGridCell G I.1 I.2, ‖zb I y‖ ^ 2 := ⟨_, rfl⟩
  have hma : ∀ I, MemLp (fun y => ψa y * za I y) 2
      (volume.restrict (Set.Ico (dyadicGridLeft G I.1 I.2)
        (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1))) := fun I =>
    memLp_mul_bounded_restrict hψam hψa (hza2 I)
  have hmb : ∀ I, MemLp (fun y => ψb y * zb I y) 2
      (volume.restrict (Set.Ico (dyadicGridLeft G I.1 I.2)
        (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1))) := fun I =>
    memLp_mul_bounded_restrict hψbm hψb (hzb2 I)
  have hFam : ∀ I, Measurable (fun y => ψa y * za I y) := fun I => hψam.mul (hzam I)
  have hFbm : ∀ I, Measurable (fun y => ψb y * zb I y) := fun I => hψbm.mul (hzbm I)
  -- the normalized-product conversion
  have hnorm : ∀ I : ℤ × ℤ, dyadicGridLength G I.1 *
      (Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
        (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψa y * za I y‖ ^ 2) *
      Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
        (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψb y * zb I y‖ ^ 2)) ≤
      Real.sqrt (Xe I) * Real.sqrt (Ye I) := by
    intro I
    rw [cell_normalized_product (dyadicGridLength_pos G I.1), hXe, hYe]
    exact mul_le_mul (Real.sqrt_le_sqrt (setIntegral_mul_bounded_le hψa (hza2 I)))
      (Real.sqrt_le_sqrt (setIntegral_mul_bounded_le hψb (hzb2 I))) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  set! SX := S.filter (fun I => I.1 ∈ X) with hSX
  set! SN := S.filter (fun I => I.1 ∉ X) with hSN
  have hsplitS := Finset.sum_filter_add_sum_filter_not S (fun I => I.1 ∈ X)
    (fun I => dyadicGridLength G I.1 * ‖Hf I Q‖)
  simp only [eHf]
  rw [← hsplitS]
  -- exceptional depths
  have hexc : ∑ I ∈ SX, dyadicGridLength G I.1 * ‖Hf I Q‖ ≤
      kernelFourierConst κ * A₀ * X.card * Ka * Kb * Na * Nb := by
    expose_names
    exact @band_scale_sum_core_hexc G κ J S hSJ w hw a b hab Q hQm hQ1 ψa ψb Fa Fb za zb Ka Kb hKa
      hKb hEa hEb A₀ hband X hKF hA00 Hf eHf Xe hXe Ye hYe hma hmb hFam hFbm hnorm
  have hrepex : ∀ s : ℤ, ∃ rep : τ → τ, s ∈ S.image Prod.fst → s ∉ X →
      (∀ p ∈ P, rep p ∈ P ∧ dyadicGridLength G s * |freq s p - freq s (rep p)| ≤ ε₂) ∧
      ∀ p ∈ P, ∀ q ∈ P, rep p ≠ rep q →
        L₂ ≤ dyadicGridLength G s * |freq s (rep p) - freq s (rep q)| := by
    intro s
    by_cases hs : s ∈ S.image Prod.fst ∧ s ∉ X
    · obtain ⟨rep, h1, h2⟩ := exists_clump_representatives P (freq s) hε₂ h3
        (hdich s hs.1 hs.2) (dyadicGridLength_pos G s).le
      exact ⟨rep, fun _ _ => ⟨h1, h2⟩⟩
    · exact ⟨id, fun h1 h2 => absurd ⟨h1, h2⟩ hs⟩
  choose rep hrep using hrepex
  obtain ⟨R, hR⟩ : ∃ R : ℤ → Finset ℝ, R = fun s => P.image (fun p => freq s (rep s p)) :=
    ⟨_, rfl⟩
  expose_names
  exact @band_scale_sum_core_stage_1 G κ J S hSJ w hw a b hab Q hQm hQ1 ψa ψb hψam hψbm hψa hψb Fa
    Fb za zb Ka Kb hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 A₀ hband τ inst inst_1 coef lam
    freq hexp hcs P X ε₁ ε₂ L₂ hε₁ hε₂ hL₂ hquad tiny htiny0 htiny Θ hΘ Atot τt Cζ hCζ hCζ0 hAtot
    htail hsmall dχ χ Bc hBc hrat env henv hens Mt hMt Λ hΛ Tt hTs hTt hC hAtot0 hA00 Hf eHf Xe
    hXe Ye hYe hma hmb hFam hFbm hnorm hexc rep hrep R hR

theorem one_le_rationalHeight (q : ℚ) : (1 : ℝ) ≤ rationalHeight q := by
  have : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  have h2 : (q.den : ℝ) ≤ rationalHeight q := by exact_mod_cast le_max_right _ _
  linarith

/-- Heights of sums of rationals. -/
theorem rationalHeight_add_le (q r : ℚ) :
    (rationalHeight (q + r) : ℝ) ≤ 3 * ((rationalHeight q : ℝ) * rationalHeight r) ^ 2 := by
  have hD : 0 < q.den * r.den := Nat.mul_pos q.den_pos r.den_pos
  have h := rationalHeight_le_of_mul_int (q + r) hD ⟨q.num * r.den + r.num * q.den, by
    push_cast
    rw [show (q.den : ℚ) * r.den * (q + r) = (q.den * q) * r.den + (r.den * r) * q.den by ring,
      Rat.den_mul_eq_num, Rat.den_mul_eq_num]⟩
  have hq := abs_rat_le_rationalHeight q
  have hr := abs_rat_le_rationalHeight r
  have hqd : (q.den : ℝ) ≤ rationalHeight q := by exact_mod_cast le_max_right _ _
  have hrd : (r.den : ℝ) ≤ rationalHeight r := by exact_mod_cast le_max_right _ _
  have hq1 := one_le_rationalHeight q
  have hr1 := one_le_rationalHeight r
  set P := (rationalHeight q : ℝ) * rationalHeight r
  have hP1 : 1 ≤ P := one_le_mul_of_one_le_of_one_le hq1 hr1
  have hDP : ((q.den * r.den : ℕ) : ℝ) ≤ P := by
    push_cast; exact mul_le_mul hqd hrd (by positivity) (by linarith)
  have hqr : |((q + r : ℚ) : ℝ)| + 1 ≤ 3 * P := by
    push_cast
    have := abs_add_le (q : ℝ) (r : ℝ)
    have h1 : (rationalHeight q : ℝ) ≤ P := by
      calc (rationalHeight q : ℝ) = rationalHeight q * 1 := by ring
        _ ≤ P := mul_le_mul_of_nonneg_left hr1 (by linarith)
    have h2 : (rationalHeight r : ℝ) ≤ P := by
      calc (rationalHeight r : ℝ) = 1 * rationalHeight r := by ring
        _ ≤ P := mul_le_mul_of_nonneg_right hq1 (by linarith)
    linarith
  calc (rationalHeight (q + r) : ℝ) ≤ ((q.den * r.den : ℕ) : ℝ) * (|((q + r : ℚ) : ℝ)| + 1) := h
    _ ≤ P * (3 * P) := mul_le_mul hDP hqr (by positivity) (by linarith)
    _ = 3 * P ^ 2 := by ring

theorem rationalHeight_sub_le (q r : ℚ) :
    (rationalHeight (q - r) : ℝ) ≤ 3 * ((rationalHeight q : ℝ) * rationalHeight r) ^ 2 := by
  rw [sub_eq_add_neg]
  have := rationalHeight_add_le q (-r)
  rwa [rationalHeight_neg] at this

/-- Heights of quotients by a nonzero integer. -/
theorem rationalHeight_div_intCast_le (q : ℚ) {k : ℤ} (hk : k ≠ 0) :
    (rationalHeight (q / k) : ℝ) ≤ 2 * |(k : ℝ)| * (rationalHeight q : ℝ) ^ 2 := by
  have hD : 0 < q.den * k.natAbs := Nat.mul_pos q.den_pos (Int.natAbs_pos.mpr hk)
  have h := rationalHeight_le_of_mul_int (q / k) hD ⟨q.num * k.sign, by
    have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
    push_cast
    rw [show (q.den : ℚ) * (k.natAbs : ℚ) * (q / k) = (q.den * q) * ((k.natAbs : ℚ) / k) by
      field_simp]
    rw [Rat.den_mul_eq_num]
    congr 1
    rcases lt_or_gt_of_ne hk with h | h
    · rw [Int.sign_eq_neg_one_of_neg h, Nat.cast_natAbs, abs_of_neg (by exact_mod_cast h)]
      field_simp; push_cast; ring
    · rw [Int.sign_eq_one_of_pos h, Nat.cast_natAbs, abs_of_pos (by exact_mod_cast h)]
      field_simp; push_cast; ring⟩
  have hq := abs_rat_le_rationalHeight q
  have hqd : (q.den : ℝ) ≤ rationalHeight q := by exact_mod_cast le_max_right _ _
  have hq1 := one_le_rationalHeight q
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  have hdiv : |(q : ℝ) / (k : ℝ)| ≤ rationalHeight q := by
    rw [abs_div]
    exact (div_le_self (abs_nonneg _) hk1).trans hq
  calc (rationalHeight (q / k) : ℝ) ≤ ((q.den * k.natAbs : ℕ) : ℝ) * (|((q / k : ℚ) : ℝ)| + 1) :=
        h
    _ ≤ ((rationalHeight q : ℝ) * |(k : ℝ)|) * (2 * rationalHeight q) := by
        push_cast
        rw [Nat.cast_natAbs, Int.cast_abs]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hqd (abs_nonneg _))
          (by linarith [hdiv, hq1]) (by positivity) (by positivity)
    _ = 2 * |(k : ℝ)| * (rationalHeight q : ℝ) ^ 2 := by ring

/-- Blueprint lem:predictors, proof line 1517: at a scale of the band `A_r > δ`, lemmas
`lem:weyl` and `lem:chartfourier` (through `separatedPhase`) expand the time factor into
phases `e(λ_* t² + γ t)` on `|t| ≤ 2r`, with `λ_*` and `γ - β` bounded-height rational
evaluations of the fixed chart parameters, indexed by `ℕ × ℤ^{2d}`. -/
theorem chart_depth_expansion (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ DJ : ℕ → ℕ, ∀ {d : ℕ} (H δ r : ℝ) (A : QuadraticChartData d),
      QuadraticChartComplexity c₀ H A → 0 < r → 0 < δ →
      (∀ u, ‖(bandCutoff u : ℂ)‖ ≤ H) →
      (∀ u v, ‖(bandCutoff v : ℂ) - (bandCutoff u : ℂ)‖ ≤ H * |v - u|) →
      (∃ ξ, δ < bandAmplitude (quadraticChartAtom A) r ξ) →
      ∃ (lam : ℝ) (M : Matrix (Fin d) (Fin d) ℚ) (σ : ℕ × (Fin (d + d) → ℤ) → Fin d → ℚ)
        (coef : ℕ × (Fin (d + d) → ℤ) → ℂ),
        (∀ i j, (rationalHeight (M i j) : ℝ) ≤
          Real.exp (D * (1 + Real.log H + Real.log (max 1 δ⁻¹)) ^ D)) ∧
        lam = A.quadratic + ∑ i, ∑ j, A.horizontal i * (M i j : ℝ) * A.horizontal j ∧
        |lam| * r ^ 2 ≤ Real.exp (D * (1 + Real.log H + Real.log (max 1 δ⁻¹)) ^ D) ∧
        (∀ p i, (rationalHeight (σ p i) : ℝ) ≤
          Real.exp (D * (1 + Real.log H + Real.log (max 1 δ⁻¹)) ^ D) *
            (1 + frequencyLength p.2)) ∧
        (∀ t, |t| ≤ 2 * r → HasSum (fun p => coef p *
          quadPhase lam (A.linear + ∑ i, (σ p i : ℝ) * A.horizontal i) t)
            (quadraticChartAtom A t)) ∧
        Summable (fun p => ‖coef p‖) ∧
        (∑' p, ‖coef p‖) ≤ Real.exp (D * (1 + Real.log H + Real.log (max 1 δ⁻¹)) ^ D) ∧
        (∀ p, ⌊Real.exp (D * (1 + Real.log H + Real.log (max 1 δ⁻¹)) ^ D)⌋₊ ≤ p.1 →
          coef p = 0) ∧
        ∀ p, ‖coef p‖ * (1 + frequencyLength p.2) ^ ((d + 1) ^ 2) ≤
          Real.exp (DJ 1 * (1 + Real.log H + Real.log (max 1 δ⁻¹)) ^ DJ 1) := by
  obtain ⟨D, hD, DJ, hsp⟩ := separatedPhase c₀ hc 2 (by norm_num)
  refine ⟨D, hD, DJ, ?_⟩
  intro d H δ r A hA hr hδ hζb hζL hband
  set X := 1 + Real.log H + Real.log (max 1 δ⁻¹) with hX
  have hζm : Measurable (fun u => (bandCutoff u : ℂ)) :=
    Complex.measurable_ofReal.comp bandCutoff_spec.1.continuous.measurable
  have hsupp : ∀ u, (bandCutoff u : ℂ) ≠ 0 → |u| ≤ 2 := fun u hu =>
    (bandCutoff_eq_zero_of_ne (fun h => hu (by rw [h]; simp))).le
  have hlow : ∀ s < δ, ∃ ξ : ℝ, s < ‖∫ u, (Real.fourierChar (-(u * ξ)) : ℂ) *
      ((bandCutoff u : ℂ) * quadraticChartAtom A (r * u))‖ := by
    intro s hs
    obtain ⟨ξ, hξ⟩ := hband
    refine ⟨ξ, hs.trans (lt_of_lt_of_le hξ (le_of_eq ?_))⟩
    unfold bandAmplitude
    congr 2; funext u
    rw [mul_comm u ξ]; ring
  obtain ⟨M, hM, hlam, ι, hfin, σ, hcard, hσ, a, hexp, hsum, htsum, hJ⟩ :=
    hsp H δ r A hA hr (fun u => (bandCutoff u : ℂ)) hζm hζb hζL hsupp hδ hlow
  classical
  set E := Real.exp (D * X ^ D) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by
    have hH1 : 1 ≤ H := by linarith [hA.lower, Real.add_one_le_exp (2 : ℝ)]
    have : 0 ≤ X := by
      have := Real.log_nonneg hH1
      have := Real.log_nonneg (le_max_left 1 δ⁻¹)
      simp only [hX]; linarith
    positivity)
  obtain ⟨N, hN⟩ : ∃ N, N = Fintype.card ι := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ι ≃ Fin N, e = hN ▸ Fintype.equivFin ι := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ι × (Fin (d + d) → ℤ) → ℕ × (Fin (d + d) → ℤ),
      g = fun p => ((e p.1 : ℕ), p.2) := ⟨_, rfl⟩
  have hginj : Function.Injective g := by
    intro p q h
    simp only [hg, Prod.mk.injEq] at h
    exact Prod.ext (e.injective (Fin.ext h.1)) h.2
  obtain ⟨coef, hcoef⟩ : ∃ coef : ℕ × (Fin (d + d) → ℤ) → ℂ,
      coef = fun q => if h : q.1 < N then a (e.symm ⟨q.1, h⟩, q.2) else 0 := ⟨_, rfl⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ' : ℕ × (Fin (d + d) → ℤ) → Fin d → ℚ,
      σ' = fun q => if h : q.1 < N then σ (e.symm ⟨q.1, h⟩, q.2) else 0 := ⟨_, rfl⟩
  have hcoefg : ∀ p, coef (g p) = a p := by
    intro p
    rw [hcoef, hg]
    simp only
    simp only [(e p.1).isLt, ↓reduceDIte]
    simp
  have hσg : ∀ p, σ' (g p) = σ p := by
    intro p
    rw [hσ', hg]
    simp only
    simp only [(e p.1).isLt, ↓reduceDIte]
    simp
  have hrange : ∀ q, q ∉ Set.range g → coef q = 0 := by
    intro q hq
    rw [hcoef]
    simp only
    split_ifs with h
    · exfalso
      exact hq ⟨(e.symm ⟨q.1, h⟩, q.2), by simp [hg]⟩
    · rfl
  set lam := A.quadratic + ∑ i, ∑ j, A.horizontal i * (M i j : ℝ) * A.horizontal j with hlamd
  refine ⟨lam, M, σ', coef, hM, rfl, hlam, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q i
    rw [hσ']
    simp only
    split_ifs with h
    · exact hσ _ i
    · have h0 : (rationalHeight (0 : ℚ) : ℝ) = 1 := by
        rw [show rationalHeight (0 : ℚ) = 1 by decide]; norm_num
      simp only [Pi.zero_apply]
      rw [h0]
      have := frequencyLength_nonneg q.2
      nlinarith only [hE1, this]
  · intro t ht
    have h := (hexp t (by linarith)).mul_right
      (Real.fourierChar (lam * t ^ 2 + A.linear * t) : ℂ)
    have hcancel : (Real.fourierChar (-(lam * t ^ 2 + A.linear * t)) : ℂ) *
        quadraticChartAtom A t * (Real.fourierChar (lam * t ^ 2 + A.linear * t) : ℂ) =
        quadraticChartAtom A t := by
      rw [mul_comm, ← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      simp
    rw [hcancel] at h
    rw [← hginj.hasSum_iff (fun q hq => by simp [hrange q hq])]
    convert h using 1
    funext p
    simp only [Function.comp, hcoefg, hσg]
    unfold quadPhase
    rw [mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3
    ring
  · rw [← hginj.summable_iff (fun q hq => by simp [hrange q hq])]
    convert hsum using 1
    funext p; simp [Function.comp, hcoefg]
  · rw [← hginj.tsum_eq (f := fun q => ‖coef q‖) (fun q hq => by
      by_contra h
      exact hq (by simp [hrange q h]))]
    convert htsum using 1
    congr 1; funext p; simp [hcoefg]
  · intro q hq
    rw [hcoef]
    simp only
    have hNE : (N : ℝ) ≤ E := by rw [hN]; exact hcard
    have hNf : N ≤ ⌊E⌋₊ := Nat.le_floor hNE
    simp only [show ¬ q.1 < N by omega, ↓reduceDIte]
  · intro q
    rw [hcoef]
    simp only
    split_ifs with h
    · have := (hJ 1).1 (e.symm ⟨q.1, h⟩, q.2)
      simpa using this
    · simp only [norm_zero, zero_mul]; positivity

/-- Lattice tail of the weight `(1 + |v|)^{-k}` beyond a dyadic radius, `k > D`. -/
theorem lattice_weight_tail {D k : ℕ} (hD : 1 ≤ D) (hk : D < k) (K₀ : ℕ) :
    Summable (fun v : Fin D → ℤ => if v ≠ 0 ∧ (2 : ℝ) ^ K₀ ≤ 1 + frequencyLength v then
      ((1 + frequencyLength v) ^ k)⁻¹ else 0) ∧
    (∑' v : Fin D → ℤ, if v ≠ 0 ∧ (2 : ℝ) ^ K₀ ≤ 1 + frequencyLength v then
      ((1 + frequencyLength v) ^ k)⁻¹ else 0) ≤
      2 * 7 ^ D * (2 * Real.pi) ^ k / 2 ^ K₀ := by
  classical
  set c : (Fin D → ℤ) → ℂ := fun n => ((((1 + frequencyLength n) ^ k)⁻¹ : ℝ) : ℂ) with hcdef
  have hsD : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  set A : ℝ := (2 * Real.pi / Real.sqrt (D : ℝ)) ^ k with hA
  have hA0 : 0 ≤ A := by positivity
  have hcn : ∀ n, ‖c n‖ = ((1 + frequencyLength n) ^ k)⁻¹ := fun n => by
    simp only [hcdef, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by have := frequencyLength_nonneg n; positivity)
  have hc : ∀ n, n ≠ 0 → ‖c n‖ ≤
      A * (Real.sqrt (D : ℝ) / (2 * Real.pi * frequencyLength n)) ^ k := by
    intro n hn
    have hL := one_le_frequencyLength hn
    rw [hcn, hA, ← mul_pow]
    have e : 2 * Real.pi / Real.sqrt (D : ℝ) *
        (Real.sqrt (D : ℝ) / (2 * Real.pi * frequencyLength n)) = (frequencyLength n)⁻¹ := by
      field_simp
    rw [e, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) k)
  have htail := frequency_tail_bound hA0 hk c hc K₀
  have hsum := summable_norm_of_frequency_decay hA0 hk c hc
  refine ⟨hsum.of_nonneg_of_le (fun v => by
    split_ifs
    · have := frequencyLength_nonneg v; positivity
    · exact le_rfl) (fun v => ?_), ?_⟩
  · split_ifs
    · rw [hcn]
    · exact norm_nonneg _
  · have heq : (∑' v : Fin D → ℤ, if v ≠ 0 ∧ (2 : ℝ) ^ K₀ ≤ 1 + frequencyLength v then
        ((1 + frequencyLength v) ^ k)⁻¹ else 0) =
        ∑' n, if n ≠ 0 ∧ (2 : ℝ) ^ K₀ ≤ 1 + frequencyLength n then ‖c n‖ else 0 := by
      congr 1; funext v; split_ifs <;> simp [hcn]
    rw [heq]
    refine htail.trans ?_
    have hAs : A * Real.sqrt (D : ℝ) ^ k = (2 * Real.pi) ^ k := by
      rw [hA, ← mul_pow]; congr 1; field_simp
    have hneg : ((D : ℝ) - k) ≤ -1 := by
      have : (D : ℝ) + 1 ≤ k := by exact_mod_cast hk
      linarith
    have hr1 : (2 : ℝ) ^ ((D : ℝ) - k) ≤ 1 / 2 := by
      calc (2 : ℝ) ^ ((D : ℝ) - k) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hneg
        _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
    have hK : ((2 : ℝ) ^ K₀) ^ ((D : ℝ) - k) ≤ (2 ^ K₀)⁻¹ := by
      have h1 : (1 : ℝ) ≤ 2 ^ K₀ := one_le_pow₀ (by norm_num)
      calc ((2 : ℝ) ^ K₀) ^ ((D : ℝ) - k) ≤ ((2 : ℝ) ^ K₀) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1 hneg
        _ = (2 ^ K₀)⁻¹ := Real.rpow_neg_one _
    have hden : 1 / 2 ≤ 1 - (2 : ℝ) ^ ((D : ℝ) - k) := by linarith
    have hden0 : 0 < 1 - (2 : ℝ) ^ ((D : ℝ) - k) := by linarith
    have hnum0 : 0 ≤ (7 : ℝ) ^ D * A * Real.sqrt (D : ℝ) ^ k := by positivity
    rw [div_le_iff₀ hden0]
    calc (7 : ℝ) ^ D * A * Real.sqrt (D : ℝ) ^ k * ((2 : ℝ) ^ K₀) ^ ((D : ℝ) - k)
        ≤ (7 : ℝ) ^ D * A * Real.sqrt (D : ℝ) ^ k * (2 ^ K₀)⁻¹ :=
          mul_le_mul_of_nonneg_left hK hnum0
      _ = 2 * 7 ^ D * (2 * Real.pi) ^ k / 2 ^ K₀ * (1 / 2) := by
          rw [show (7 : ℝ) ^ D * A * Real.sqrt (D : ℝ) ^ k = 7 ^ D * (A * Real.sqrt (D : ℝ) ^ k)
            by ring, hAs]
          field_simp
      _ ≤ 2 * 7 ^ D * (2 * Real.pi) ^ k / 2 ^ K₀ * (1 - (2 : ℝ) ^ ((D : ℝ) - k)) :=
          mul_le_mul_of_nonneg_left hden (by positivity)

/-- Sums over `ℕ × V` of functions supported on finitely many first coordinates. -/
theorem tsum_prod_range_le {V : Type*} (f : ℕ × V → ℝ) (hf0 : ∀ q, 0 ≤ f q) (N : ℕ)
    (w : V → ℝ) (hw : Summable w) (hfw : ∀ q, f q ≤ if q.1 < N then w q.2 else 0) :
    Summable f ∧ (∑' q, f q) ≤ N * ∑' v, w v := by
  classical
  set h : ℕ × V → ℝ := fun q => if q.1 < N then w q.2 else 0 with hh
  set hn : ℕ → ℕ × V → ℝ := fun n q => if q.1 = n then w q.2 else 0 with hhn
  have hsn : ∀ n, Summable (hn n) ∧ ∑' q, hn n q = ∑' v, w v := by
    intro n
    have hinj : Function.Injective (fun v : V => (n, v)) := fun a b hab => by
      simpa using hab
    have hvan : ∀ q, q ∉ Set.range (fun v : V => (n, v)) → hn n q = 0 := by
      intro q hq
      simp only [hhn]
      split_ifs with h1
      · exfalso; exact hq ⟨q.2, by rw [← h1]⟩
      · rfl
    have hcomp : hn n ∘ (fun v : V => (n, v)) = w := by
      funext v; simp [hhn]
    refine ⟨(hinj.summable_iff hvan).mp (hcomp ▸ hw), ?_⟩
    rw [← hinj.tsum_eq (fun q hq => by
      by_contra hr; exact hq (hvan q hr)), ← hcomp]
    rfl
  have hhsum : h = fun q => ∑ n ∈ Finset.range N, hn n q := by
    funext q
    simp only [hh, hhn]
    rw [Finset.sum_ite_eq (Finset.range N) q.1 (fun _ => w q.2)]
    simp [Finset.mem_range]
  have hhs : Summable h := by
    rw [hhsum]; exact summable_sum fun n _ => (hsn n).1
  have hht : ∑' q, h q = N * ∑' v, w v := by
    rw [hhsum, Summable.tsum_finsetSum fun n _ => (hsn n).1]
    simp only [fun n => (hsn n).2]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfs : Summable f := hhs.of_nonneg_of_le hf0 hfw
  exact ⟨hfs, (hfs.tsum_le_tsum hfw hhs).trans hht.le⟩

theorem rationalHeight_le_floor {q : ℚ} {B : ℝ} (h : (rationalHeight q : ℝ) ≤ B) :
    rationalHeight q ≤ ⌊B⌋₊ :=
  Nat.le_floor h

/-- A tiny scaled bounded-height rational evaluation is dominated by the tiny maximum. -/
theorem le_tinyMaximum_of_rational {d : ℕ} (χ : Fin d → ℝ) {B : ℝ} (a : Fin d → ℚ)
    (ha : ∀ j, (rationalHeight (a j) : ℝ) ≤ B) {w ε : ℝ} (hw : 0 ≤ w)
    (hsmall : w * |∑ j, (a j : ℝ) * χ j| ≤ ε) :
    w * |∑ j, (a j : ℝ) * χ j| ≤
      finiteTinyMaximum (boundedRationalMagnitudes ⌊B⌋₊ (rationalEvaluation χ)) w ε := by
  by_cases h0 : w * |∑ j, (a j : ℝ) * χ j| = 0
  · rw [h0]; exact finiteTinyMaximum_nonneg _ _ _
  have hx : 0 < |∑ j, (a j : ℝ) * χ j| := by
    rcases (abs_nonneg (∑ j, (a j : ℝ) * χ j)).lt_or_eq with h | h
    · exact h
    · exfalso; apply h0; rw [← h]; ring
  have hwpos : 0 < w * |∑ j, (a j : ℝ) * χ j| :=
    lt_of_le_of_ne (mul_nonneg hw (abs_nonneg _)) (Ne.symm h0)
  refine le_finiteTinyMaximum ?_ hwpos hsmall
  exact mem_boundedRationalMagnitudes.mpr ⟨hx, a, fun j => rationalHeight_le_floor (ha j), rfl⟩

/-- `lem:height`, eq:tiny-sum on a finite set of depths of a dyadic grid. -/
theorem grid_tiny_sum_le {d u : ℕ} (G : RealDyadicGrid) (χ : Fin d → ℝ) {B ε : ℝ}
    (hB : 2 ≤ B) (hu : 1 ≤ u) (hε : 0 ≤ ε) (T : Finset ℤ) :
    ∑ s ∈ T, finiteTinyMaximum (boundedRationalMagnitudes ⌊B⌋₊ (rationalEvaluation χ))
      (dyadicGridLength G s ^ u) ε ≤ 128 * (d + 1 : ℝ) ^ 4 * Real.log (2 * B) * ε := by
  obtain ⟨hs, hb⟩ := rational_frequency_tiny_sum hB hu hε χ G.baseLength
  refine le_trans ?_ hb
  exact hs.sum_le_tsum T (fun n _ => finiteTinyMaximum_nonneg _ _ _)

/-- The vector `(λ, θ_i θ_j)` whose bounded-height rational evaluations are the effective
quadratic coefficients `λ_* = λ + θᵀ M θ`. -/
noncomputable def quadraticParamVector {d : ℕ} (lam : ℝ) (θ : Fin d → ℝ) :
    Fin (d * d + 1) → ℝ :=
  Fin.cons lam (fun x => θ (finProdFinEquiv.symm x).1 * θ (finProdFinEquiv.symm x).2)

theorem quadraticParam_eval {d : ℕ} (lam : ℝ) (θ : Fin d → ℝ)
    (M : Matrix (Fin d) (Fin d) ℚ) :
    ∑ j, ((Fin.cons (1 : ℚ) (fun x => M (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2) :
      Fin (d * d + 1) → ℚ) j : ℝ) * quadraticParamVector lam θ j =
      lam + ∑ i, ∑ j, θ i * (M i j : ℝ) * θ j := by
  rw [Fin.sum_univ_succ, Fin.cons_zero]
  have h0 : quadraticParamVector lam θ 0 = lam := by
    unfold quadraticParamVector; rw [Fin.cons_zero]
  have hs : ∀ x : Fin (d * d), ((Fin.cons (1 : ℚ) (fun x => M (finProdFinEquiv.symm x).1
      (finProdFinEquiv.symm x).2) : Fin (d * d + 1) → ℚ) x.succ : ℝ) *
        quadraticParamVector lam θ x.succ =
      θ (finProdFinEquiv.symm x).1 * (M (finProdFinEquiv.symm x).1
        (finProdFinEquiv.symm x).2 : ℝ) * θ (finProdFinEquiv.symm x).2 := by
    intro x
    unfold quadraticParamVector
    rw [Fin.cons_succ, Fin.cons_succ]; ring
  rw [h0, Rat.cast_one, one_mul, Finset.sum_congr rfl (fun x _ => hs x)]
  congr 1
  rw [← Fintype.sum_prod_type']
  exact (finProdFinEquiv.symm.sum_comp
    (fun p : Fin d × Fin d => θ p.1 * (M p.1 p.2 : ℝ) * θ p.2))

theorem quadraticParam_height {d : ℕ} (M : Matrix (Fin d) (Fin d) ℚ) {B : ℝ} (hB : 1 ≤ B)
    (hM : ∀ i j, (rationalHeight (M i j) : ℝ) ≤ B) (j : Fin (d * d + 1)) :
    (rationalHeight ((Fin.cons (1 : ℚ) (fun x => M (finProdFinEquiv.symm x).1
      (finProdFinEquiv.symm x).2) : Fin (d * d + 1) → ℚ) j) : ℝ) ≤ B := by
  refine Fin.cases ?_ (fun x => ?_) j
  · rw [Fin.cons_zero, show rationalHeight (1 : ℚ) = 1 by decide]; push_cast; exact hB
  · rw [Fin.cons_succ]; exact hM _ _

/-- Centers `(β + σ·θ)/(b-a)` as rational evaluations of `(β, θ)`. -/
theorem center_rational {d : ℕ} (β : ℝ) (θ : Fin d → ℝ) (σ : Fin d → ℚ) {k : ℤ}
    (hk : k ≠ 0) (hk3 : |(k : ℝ)| ≤ 3) {B : ℝ} (hσ : ∀ i, (rationalHeight (σ i) : ℝ) ≤ B) :
    (∀ j, (rationalHeight ((Fin.cons ((1 : ℚ) / k) (fun i => σ i / k) : Fin (d + 1) → ℚ) j) :
        ℝ) ≤ 6 * B ^ 2 + 6) ∧
      (β + ∑ i, (σ i : ℝ) * θ i) / (k : ℝ) =
        ∑ j, ((Fin.cons ((1 : ℚ) / k) (fun i => σ i / k) : Fin (d + 1) → ℚ) j : ℝ) *
          (Fin.cons β θ : Fin (d + 1) → ℝ) j := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  constructor
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [Fin.cons_zero]
      have h := rationalHeight_div_intCast_le (1 : ℚ) hk
      rw [show rationalHeight (1 : ℚ) = 1 by decide] at h
      push_cast at h
      have : 0 ≤ 6 * B ^ 2 := by positivity
      linarith
    · rw [Fin.cons_succ]
      have h := rationalHeight_div_intCast_le (σ i) hk
      have hB0 : 0 ≤ (rationalHeight (σ i) : ℝ) := by positivity
      have h2 : (rationalHeight (σ i) : ℝ) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hB0 (hσ i) 2
      nlinarith only [hk3, h, h2]
  · rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_zero]
    simp_rw [Fin.cons_succ]
    push_cast
    rw [add_div, Finset.sum_div]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun i _ => ?_; ring

/-- The Lipschitz constant of the band plateau. -/
noncomputable def bandLip : ℝ := Classical.choose bandCutoff_lipschitz

theorem bandLip_spec : 0 ≤ bandLip ∧ ∀ u v, |bandCutoff v - bandCutoff u| ≤ bandLip * |v - u| :=
  Classical.choose_spec bandCutoff_lipschitz

/-- The Fourier decay constant of the band plateau. -/
noncomputable def bandDecay : ℝ := Classical.choose bandCutoff_fourier_decay

theorem bandDecay_spec : 0 ≤ bandDecay ∧ ∀ η : ℝ, η ≠ 0 →
    ‖∫ u, (bandCutoff u : ℂ) * (Real.fourierChar (-(η * u)) : ℂ)‖ ≤ bandDecay / η ^ 2 :=
  Classical.choose_spec bandCutoff_fourier_decay

/-! Explicit parameters of the band scale sum (blueprint lem:predictors, proof lines
1517–1527), as functions of the chart-expansion exponents `D, J₁`, the dimension `d`, the
band index `m` and `Lh = log H`. -/

/-- Combined logarithmic-size and accuracy parameter for the band-scale estimates. -/
noncomputable def bsX (m : ℕ) (Lh : ℝ) : ℝ := 2 + Lh + m

/-- Exponential complexity budget in the band-scale estimates. -/
noncomputable def bsE (D m : ℕ) (Lh : ℝ) : ℝ := Real.exp (D * bsX m Lh ^ D)

/-- Exponential coefficient-tail budget in the band-scale estimates. -/
noncomputable def bsE1 (J1 m : ℕ) (Lh : ℝ) : ℝ := Real.exp (J1 * bsX m Lh ^ J1)

/-- Approximation tolerance balancing the band-scale complexity and accuracy. -/
noncomputable def bsEps (D m : ℕ) (Lh : ℝ) : ℝ :=
  Real.exp (-(m : ℝ)) / (64 * Real.pi * bsE D m Lh)

/-- Cutoff scale controlling the band-scale L² tail. -/
noncomputable def bsL2 (D m : ℕ) (Lh : ℝ) : ℝ :=
  3 + 8 * bandDecay * bsE D m Lh * Real.exp (m : ℝ)

/-- Frequency cutoff in the band-scale expansion. -/
noncomputable def bsLam (d D m : ℕ) (Lh : ℝ) : ℝ :=
  2 * Real.pi * (128 * ((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 * Real.log (2 * (bsE D m Lh + 2)) *
    bsE D m Lh)

/-- Phase-growth budget in the band-scale expansion. -/
noncomputable def bsAlpha (d D m : ℕ) (Lh : ℝ) : ℝ :=
  24 * (2 * Real.pi) ^ 2 * (4 * (32 * (((d + 1 : ℕ) + 1 : ℝ) + 1) ^ 4 *
    (Real.log 24 + 2 * (D * bsX m Lh ^ D) + 2 + Real.log 4)))

/-- Kernel-weighted combination of phase and frequency budgets for band-scale summation. -/
noncomputable def bsCT (κ : LocalKernelClass) (d D m : ℕ) (Lh : ℝ) : ℝ :=
  linearScaleConst κ * bsAlpha d D m Lh + localKernelSupBound κ * bsLam d D m Lh

/-- Dyadic truncation depth sufficient for the band-scale approximation error. -/
noncomputable def bsK0 (κ : LocalKernelClass) (d D J1 m : ℕ) (Lh : ℝ) : ℕ :=
  ⌈Real.logb 2 (16 * (bsE D m Lh + 1) * bsE1 J1 m Lh * (bsCT κ d D m Lh + 1) *
    7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2) * Real.exp (m : ℝ))⌉₊

/-- Frequency-size budget after dyadic truncation of the band-scale expansion. -/
noncomputable def bsBσ (κ : LocalKernelClass) (d D J1 m : ℕ) (Lh : ℝ) : ℝ :=
  bsE D m Lh * 2 ^ bsK0 κ d D J1 m Lh

/-- Quadratic-size budget derived from the truncated frequency-size bound. -/
noncomputable def bsB2 (κ : LocalKernelClass) (d D J1 m : ℕ) (Lh : ℝ) : ℝ :=
  3 * bsBσ κ d D J1 m Lh ^ 4 + 2

/-- Basic chart-complexity budget in the band-scale expansion. -/
noncomputable def bsB1 (D m : ℕ) (Lh : ℝ) : ℝ := bsE D m Lh + 2

/-- Coefficient-sum budget derived from the truncated frequency-size bound. -/
noncomputable def bsBc (κ : LocalKernelClass) (d D J1 m : ℕ) (Lh : ℝ) : ℝ :=
  6 * bsBσ κ d D J1 m Lh ^ 2 + 6

/-- The polynomial factor in `eq:band-scale-sum` before its final simplification. -/
noncomputable def bandBracket (κ : LocalKernelClass) (d D J1 m : ℕ) (Lh : ℝ) : ℝ :=
  kernelFourierConst κ * (32 * ((d : ℝ) + 1) ^ 4 *
      (Real.log (2 * bsB2 κ d D J1 m Lh) + Real.log (2 * bsL2 D m Lh / bsEps D m Lh)) +
    32 * ((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 *
      (Real.log (2 * bsB1 D m Lh) + Real.log (2 * bsE D m Lh / bsEps D m Lh))) +
  linearScaleConst κ * clumpMultiplicity (d + 1) (bsBc κ d D J1 m Lh) +
  4 * localKernelSupBound κ * (((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 * Real.log (2 * bsB1 D m Lh) +
    ((d : ℝ) + 1) ^ 4 * Real.log (2 * bsB2 κ d D J1 m Lh)) + 1

theorem frequencyTruncationSet_le {D K : ℕ} {v : Fin D → ℤ}
    (hv : v ∈ frequencyTruncationSet D K) : 1 + frequencyLength v ≤ 2 ^ K := by
  rcases mem_frequencyTruncationSet.mp hv with h | h
  · subst h
    have : frequencyLength (0 : Fin D → ℤ) = 0 := by simp [frequencyLength]
    rw [this, add_zero]; exact one_le_pow₀ (by norm_num)
  · exact h.le

theorem not_mem_frequencyTruncationSet {D K : ℕ} {v : Fin D → ℤ}
    (hv : v ∉ frequencyTruncationSet D K) :
    v ≠ 0 ∧ (2 : ℝ) ^ K ≤ 1 + frequencyLength v := by
  rw [mem_frequencyTruncationSet] at hv
  push Not at hv
  exact hv

theorem two_pow_ceil_logb_ge {Z : ℝ} (hZ : 0 < Z) : Z ≤ (2 : ℝ) ^ ⌈Real.logb 2 Z⌉₊ := by
  have h := Nat.le_ceil (Real.logb 2 Z)
  calc Z = (2 : ℝ) ^ (Real.logb 2 Z) := (Real.rpow_logb (by norm_num) (by norm_num) hZ).symm
    _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 Z⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h
    _ = (2 : ℝ) ^ ⌈Real.logb 2 Z⌉₊ := Real.rpow_natCast _ _

theorem bsE_one_le (D m : ℕ) {Lh : ℝ} (hLh : 0 ≤ Lh) : 1 ≤ bsE D m Lh := by
  unfold bsE bsX
  exact Real.one_le_exp (by positivity)

theorem summable_lattice_weight {D k : ℕ} (hD : 1 ≤ D) (hk : D < k) :
    Summable (fun v : Fin D → ℤ => ((1 + frequencyLength v) ^ k)⁻¹) := by
  classical
  have h := (lattice_weight_tail hD hk 0).1
  have h0 : Summable (fun v : Fin D → ℤ => if v = 0 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) (fun v hv => by simp at hv; simp [hv])
  refine (h.add h0).of_nonneg_of_le (fun v => by
    have := frequencyLength_nonneg v; positivity) (fun v => ?_)
  have hL := frequencyLength_nonneg v
  by_cases hv : v = 0
  · subst hv
    have : frequencyLength (0 : Fin D → ℤ) = 0 := by simp [frequencyLength]
    simp [this]
  · have hcond : v ≠ 0 ∧ (2 : ℝ) ^ (0 : ℕ) ≤ 1 + frequencyLength v := ⟨hv, by simp; linarith⟩
    split_ifs; simp_all

theorem bsEps_pos (D m : ℕ) {Lh : ℝ} (hLh : 0 ≤ Lh) : 0 < bsEps D m Lh := by
  have := bsE_one_le D m hLh
  unfold bsEps; positivity

theorem bsEps_le_one (D m : ℕ) {Lh : ℝ} (hLh : 0 ≤ Lh) : bsEps D m Lh ≤ 1 := by
  have hE := bsE_one_le D m hLh
  have hem1 : Real.exp (-(m : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := Nat.cast_nonneg (α := ℝ) m; linarith)
  unfold bsEps
  rw [div_le_one (by positivity)]
  have : 1 ≤ 64 * Real.pi * bsE D m Lh := by nlinarith [Real.pi_gt_three]
  linarith

theorem three_le_bsL2 (D m : ℕ) {Lh : ℝ} (hLh : 0 ≤ Lh) : 3 ≤ bsL2 D m Lh := by
  have hE := bsE_one_le D m hLh
  have := bandDecay_spec.1
  unfold bsL2
  have : 0 ≤ 8 * bandDecay * bsE D m Lh * Real.exp (m : ℝ) := by positivity
  linarith

theorem one_le_bsBσ (κ : LocalKernelClass) (d D J1 m : ℕ) {Lh : ℝ} (hLh : 0 ≤ Lh) :
    1 ≤ bsBσ κ d D J1 m Lh := by
  have hE := bsE_one_le D m hLh
  have hK : 1 ≤ (2 : ℝ) ^ bsK0 κ d D J1 m Lh := one_le_pow₀ (by norm_num)
  unfold bsBσ
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ _ := mul_le_mul hE hK zero_le_one (by linarith)

theorem two_le_bsB2 (κ : LocalKernelClass) (d D J1 m : ℕ) {Lh : ℝ} (hLh : 0 ≤ Lh) :
    2 ≤ bsB2 κ d D J1 m Lh := by
  have h := one_le_bsBσ κ d D J1 m hLh
  unfold bsB2
  have : 0 ≤ 3 * bsBσ κ d D J1 m Lh ^ 4 := by positivity
  linarith

theorem two_le_bsB1 (D m : ℕ) {Lh : ℝ} (hLh : 0 ≤ Lh) : 2 ≤ bsB1 D m Lh := by
  have h := bsE_one_le D m hLh
  unfold bsB1; linarith

theorem two_le_bsBc (κ : LocalKernelClass) (d D J1 m : ℕ) (Lh : ℝ) :
    2 ≤ bsBc κ d D J1 m Lh := by
  unfold bsBc
  have : 0 ≤ 6 * bsBσ κ d D J1 m Lh ^ 2 := by positivity
  linarith

theorem bs_quadratic_budget (D m : ℕ) {Lh : ℝ} (hLh : 0 ≤ Lh) :
    bsE D m Lh * (8 * Real.pi * bsEps D m Lh + 4 * Real.pi * bsEps D m Lh) =
      3 / 16 * Real.exp (-(m : ℝ)) := by
  have hE := bsE_one_le D m hLh
  unfold bsEps
  field_simp
  ring

theorem bs_decay_budget (D m : ℕ) {Lh : ℝ} (hLh : 0 ≤ Lh) :
    bandDecay * bsE D m Lh / bsL2 D m Lh ^ 2 ≤ Real.exp (-(m : ℝ)) / 8 := by
  have hE := bsE_one_le D m hLh
  have hL := three_le_bsL2 D m hLh
  have hdec := bandDecay_spec.1
  have hem : Real.exp (-(m : ℝ)) * Real.exp (m : ℝ) = 1 := by
    rw [← Real.exp_add]; simp
  have hL2 : bsL2 D m Lh ≤ bsL2 D m Lh ^ 2 := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have key : bandDecay * bsE D m Lh * 8 ≤ Real.exp (-(m : ℝ)) * bsL2 D m Lh := by
    unfold bsL2
    have : Real.exp (-(m : ℝ)) * (8 * bandDecay * bsE D m Lh * Real.exp (m : ℝ)) =
        8 * bandDecay * bsE D m Lh := by
      calc _ = 8 * bandDecay * bsE D m Lh * (Real.exp (-(m : ℝ)) * Real.exp (m : ℝ)) := by
            ring
        _ = _ := by rw [hem, mul_one]
    nlinarith [Real.exp_pos (-(m : ℝ))]
  calc bandDecay * bsE D m Lh * 8 ≤ Real.exp (-(m : ℝ)) * bsL2 D m Lh := key
    _ ≤ Real.exp (-(m : ℝ)) * bsL2 D m Lh ^ 2 :=
        mul_le_mul_of_nonneg_left hL2 (Real.exp_pos _).le

theorem bsCT_nonneg (κ : LocalKernelClass) (d D m : ℕ) {Lh : ℝ} (hLh : 0 ≤ Lh) :
    0 ≤ bsCT κ d D m Lh := by
  have hE := bsE_one_le D m hLh
  have hlin := linearScaleConst_nonneg κ
  have hC := localKernelSupBound_nonneg κ
  have h24 : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hX : 0 ≤ bsX m Lh := by unfold bsX; positivity
  have hl : 0 ≤ Real.log (2 * (bsE D m Lh + 2)) := Real.log_nonneg (by linarith)
  unfold bsCT bsAlpha bsLam
  positivity

/-- The catalog truncation level makes the pooled tails small. -/
theorem bs_tail_budget (κ : LocalKernelClass) (d D J1 m : ℕ) {Lh : ℝ} (hLh : 0 ≤ Lh)
    {k : ℕ} (hk : k ≤ (d + 1) ^ 2) {C : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ bsCT κ d D m Lh + 1) :
    (⌊bsE D m Lh⌋₊ : ℝ) * bsE1 J1 m Lh * C *
      (2 * 7 ^ (d + d) * (2 * Real.pi) ^ k / 2 ^ bsK0 κ d D J1 m Lh) ≤
      Real.exp (-(m : ℝ)) / 8 := by
  have hE := bsE_one_le D m hLh
  have hE1 : 0 < bsE1 J1 m Lh := Real.exp_pos _
  have hfl : (⌊bsE D m Lh⌋₊ : ℝ) ≤ bsE D m Lh + 1 := by
    have := Nat.floor_le (show 0 ≤ bsE D m Lh by linarith); linarith
  have hCT := bsCT_nonneg κ d D m hLh
  set Z := 16 * (bsE D m Lh + 1) * bsE1 J1 m Lh * (bsCT κ d D m Lh + 1) *
    7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2) * Real.exp (m : ℝ) with hZ
  have hZ0 : 0 < Z := by rw [hZ]; positivity
  have hK : Z ≤ (2 : ℝ) ^ bsK0 κ d D J1 m Lh := two_pow_ceil_logb_ge hZ0
  have hpi : (2 * Real.pi) ^ k ≤ (2 * Real.pi) ^ ((d + 1) ^ 2) :=
    pow_le_pow_right₀ (by nlinarith only [Real.pi_gt_three]) hk
  have hnum : (⌊bsE D m Lh⌋₊ : ℝ) * bsE1 J1 m Lh * C * (2 * 7 ^ (d + d) * (2 * Real.pi) ^ k) ≤
      (bsE D m Lh + 1) * bsE1 J1 m Lh * (bsCT κ d D m Lh + 1) *
        (2 * 7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2)) := by
    gcongr
  have hem : Real.exp (-(m : ℝ)) * Real.exp (m : ℝ) = 1 := by rw [← Real.exp_add]; simp
  calc (⌊bsE D m Lh⌋₊ : ℝ) * bsE1 J1 m Lh * C *
        (2 * 7 ^ (d + d) * (2 * Real.pi) ^ k / 2 ^ bsK0 κ d D J1 m Lh)
      = (⌊bsE D m Lh⌋₊ : ℝ) * bsE1 J1 m Lh * C * (2 * 7 ^ (d + d) * (2 * Real.pi) ^ k) /
          2 ^ bsK0 κ d D J1 m Lh := by ring
    _ ≤ (bsE D m Lh + 1) * bsE1 J1 m Lh * (bsCT κ d D m Lh + 1) *
          (2 * 7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2)) / Z :=
        div_le_div₀ (by positivity) hnum hZ0 hK
    _ = Real.exp (-(m : ℝ)) / 8 := by
        rw [hZ, div_eq_iff (by positivity)]
        have hem' : Real.exp (m : ℝ) * Real.exp (-(m : ℝ)) = 1 := by rw [mul_comm]; exact hem
        field_simp
        nlinarith only [hem', Real.exp_pos (m : ℝ)]

/-- The pooled catalog tail of one depth expansion. -/
theorem catalog_tail_le {d : ℕ} (hd : 1 ≤ d) (coef : ℕ × (Fin (d + d) → ℤ) → ℂ)
    {N₀ K₀ : ℕ} {E1 : ℝ} (hE1 : 0 ≤ E1) (hvan : ∀ p, N₀ ≤ p.1 → coef p = 0)
    (henv : ∀ p, ‖coef p‖ * (1 + frequencyLength p.2) ^ ((d + 1) ^ 2) ≤ E1) :
    (∑' p, (if p ∈ (Finset.range N₀) ×ˢ (frequencyTruncationSet (d + d) K₀) then 0
      else ‖coef p‖)) ≤
      N₀ * (E1 * (2 * 7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2) / 2 ^ K₀)) := by
  classical
  have hk : d + d < (d + 1) ^ 2 := by nlinarith
  have hD : 1 ≤ d + d := by omega
  obtain ⟨hws, hwt⟩ := lattice_weight_tail hD hk K₀
  set w : (Fin (d + d) → ℤ) → ℝ := fun v => E1 * (if v ≠ 0 ∧
    (2 : ℝ) ^ K₀ ≤ 1 + frequencyLength v then ((1 + frequencyLength v) ^ ((d + 1) ^ 2))⁻¹
      else 0) with hw
  have h := tsum_prod_range_le (fun p => if p ∈ (Finset.range N₀) ×ˢ
      (frequencyTruncationSet (d + d) K₀) then 0 else ‖coef p‖)
    (fun p => by split_ifs <;> positivity) N₀ w (hws.mul_left E1) (fun p => ?_)
  · refine h.2.trans ?_
    rw [hw, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwt hE1) (Nat.cast_nonneg _)
  · simp only [Finset.mem_product, Finset.mem_range]
    by_cases hp1 : p.1 < N₀
    · rw [ite_eq_left hp1]
      by_cases hp2 : p.2 ∈ frequencyTruncationSet (d + d) K₀
      · rw [ite_eq_left ⟨hp1, hp2⟩]
        simp only [hw]
        have : 0 ≤ (if p.2 ≠ 0 ∧ (2 : ℝ) ^ K₀ ≤ 1 + frequencyLength p.2 then
          ((1 + frequencyLength p.2) ^ ((d + 1) ^ 2))⁻¹ else 0) := by
          split_ifs
          · have := frequencyLength_nonneg p.2; positivity
          · exact le_rfl
        positivity
      · rw [ite_eq_right (fun h => hp2 h.2)]
        have hc := not_mem_frequencyTruncationSet hp2
        simp only [hw, ite_eq_left hc]
        have hL := frequencyLength_nonneg p.2
        have hpos : 0 < (1 + frequencyLength p.2) ^ ((d + 1) ^ 2) := by positivity
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]
        exact henv p
    · rw [ite_eq_right hp1, hvan p (not_lt.mp hp1)]
      simp

/-- The weighted pooled tail against the coefficient envelope. -/
theorem catalog_weighted_tail {d : ℕ} (hd : 1 ≤ d) {N₀ K₀ : ℕ} {E1 CT : ℝ} (hE1 : 0 ≤ E1)
    (hCT : 0 ≤ CT) (g : ℕ × (Fin (d + d) → ℤ) → ℝ) (hg0 : ∀ p, 0 ≤ g p)
    (hg : ∀ p, g p ≤ CT * (1 + frequencyLength p.2)) :
    Summable (fun p : ℕ × (Fin (d + d) → ℤ) => if p.1 < N₀ then
      E1 * ((1 + frequencyLength p.2) ^ ((d + 1) ^ 2))⁻¹ else 0) ∧
    Summable (fun p => if p ∈ (Finset.range N₀) ×ˢ (frequencyTruncationSet (d + d) K₀) then 0
      else (if p.1 < N₀ then E1 * ((1 + frequencyLength p.2) ^ ((d + 1) ^ 2))⁻¹ else 0) *
        g p) ∧
    (∑' p, if p ∈ (Finset.range N₀) ×ˢ (frequencyTruncationSet (d + d) K₀) then 0
      else (if p.1 < N₀ then E1 * ((1 + frequencyLength p.2) ^ ((d + 1) ^ 2))⁻¹ else 0) *
        g p) ≤
      N₀ * (E1 * CT * (2 * 7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2 - 1) / 2 ^ K₀)) := by
  classical
  have hD : 1 ≤ d + d := by omega
  have hk1 : d + d < (d + 1) ^ 2 := by nlinarith
  have hk2 : d + d < (d + 1) ^ 2 - 1 := by
    have : (d + 1) ^ 2 = d * d + 2 * d + 1 := by ring
    have : 1 ≤ d * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hsum1 := summable_lattice_weight hD hk1
  obtain ⟨hws, hwt⟩ := lattice_weight_tail hD hk2 K₀
  have hpos : ∀ v : Fin (d + d) → ℤ, 0 < 1 + frequencyLength v := fun v => by
    have := frequencyLength_nonneg v; linarith
  refine ⟨(tsum_prod_range_le _ (fun p => by
      split_ifs
      · have := hpos p.2; positivity
      · exact le_rfl) N₀ _ (hsum1.mul_left E1) (fun p => le_of_eq (by
        split_ifs <;> rfl))).1, ?_⟩
  set w : (Fin (d + d) → ℤ) → ℝ := fun v => E1 * CT * (if v ≠ 0 ∧
    (2 : ℝ) ^ K₀ ≤ 1 + frequencyLength v then ((1 + frequencyLength v) ^ ((d + 1) ^ 2 - 1))⁻¹
      else 0) with hw
  have h := tsum_prod_range_le (fun p => if p ∈ (Finset.range N₀) ×ˢ
      (frequencyTruncationSet (d + d) K₀) then 0 else
      (if p.1 < N₀ then E1 * ((1 + frequencyLength p.2) ^ ((d + 1) ^ 2))⁻¹ else 0) * g p)
    (fun p => by
      split_ifs
      · exact le_rfl
      · have := hpos p.2; have := hg0 p; positivity
      · simp) N₀ w (hws.mul_left (E1 * CT)) (fun p => ?_)
  · refine ⟨h.1, h.2.trans ?_⟩
    rw [hw, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwt (by positivity))
      (Nat.cast_nonneg _)
  · simp only [Finset.mem_product, Finset.mem_range]
    by_cases hp1 : p.1 < N₀
    · rw [ite_eq_left hp1]
      by_cases hp2 : p.2 ∈ frequencyTruncationSet (d + d) K₀
      · rw [ite_eq_left ⟨hp1, hp2⟩]
        simp only [hw]
        have : 0 ≤ (if p.2 ≠ 0 ∧ (2 : ℝ) ^ K₀ ≤ 1 + frequencyLength p.2 then
          ((1 + frequencyLength p.2) ^ ((d + 1) ^ 2 - 1))⁻¹ else 0) := by
          split_ifs
          · have := hpos p.2; positivity
          · exact le_rfl
        positivity
      · rw [ite_eq_right (fun h => hp2 h.2), ite_eq_left hp1]
        have hc := not_mem_frequencyTruncationSet hp2
        simp only [hw, ite_eq_left hc]
        have hu := hpos p.2
        have hexp : (d + 1) ^ 2 = ((d + 1) ^ 2 - 1) + 1 := by
          have : 1 ≤ (d + 1) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
          omega
        calc E1 * ((1 + frequencyLength p.2) ^ ((d + 1) ^ 2))⁻¹ * g p
            ≤ E1 * ((1 + frequencyLength p.2) ^ ((d + 1) ^ 2))⁻¹ *
                (CT * (1 + frequencyLength p.2)) :=
              mul_le_mul_of_nonneg_left (hg p) (by positivity)
          _ = E1 * CT * ((1 + frequencyLength p.2) ^ ((d + 1) ^ 2 - 1))⁻¹ := by
              have hpw : (1 + frequencyLength p.2) ^ ((d + 1) ^ 2) =
                  (1 + frequencyLength p.2) ^ ((d + 1) ^ 2 - 1) * (1 + frequencyLength p.2) := by
                rw [← pow_succ]; congr 1
              rw [hpw]
              field_simp
    · rw [ite_eq_right hp1]
      split_ifs <;> simp

/-- The tail multiplicity constant grows at most linearly in `1 + |v|`. -/
theorem clumpMultiplicity_tail_le (d D m : ℕ) {Lh : ℝ} (hLh : 0 ≤ Lh) {u : ℝ} (hu : 1 ≤ u) :
    clumpMultiplicity (d + 1) (6 * (bsE D m Lh * u) ^ 2 + 6) ≤ bsAlpha d D m Lh * u := by
  have hE := bsE_one_le D m hLh
  have hlE : Real.log (bsE D m Lh) = D * bsX m Lh ^ D := by unfold bsE; exact Real.log_exp _
  have hX0 : 0 ≤ D * bsX m Lh ^ D := by unfold bsX; positivity
  have hEu : 1 ≤ bsE D m Lh * u := by nlinarith
  have harg : 2 * (6 * (bsE D m Lh * u) ^ 2 + 6) ≤ 24 * (bsE D m Lh * u) ^ 2 := by nlinarith
  have hlog : Real.log (2 * (6 * (bsE D m Lh * u) ^ 2 + 6)) ≤
      (Real.log 24 + 2 * (D * bsX m Lh ^ D) + 2) * u := by
    have h1 : Real.log (2 * (6 * (bsE D m Lh * u) ^ 2 + 6)) ≤
        Real.log (24 * (bsE D m Lh * u) ^ 2) := Real.log_le_log (by positivity) harg
    have h2 : Real.log (24 * (bsE D m Lh * u) ^ 2) =
        Real.log 24 + 2 * Real.log (bsE D m Lh) + 2 * Real.log u := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_mul
        (by positivity) (by positivity)]
      push_cast; ring
    have h3 : Real.log u ≤ u := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have h24 : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
    rw [h2, hlE] at h1
    nlinarith only [hu, hX0, h1, h3, h24]
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold clumpMultiplicity heightBandConst bsAlpha
  have hcast : (((d + 1 + 1 : ℕ) : ℝ) + 1) = (((d + 1 : ℕ) : ℝ) + 1) + 1 := by push_cast; ring
  rw [hcast]
  have hc0 : 0 ≤ 24 * (2 * Real.pi) ^ 2 * (4 * (32 * ((((d + 1 : ℕ) : ℝ) + 1) + 1) ^ 4)) := by
    positivity
  have key : Real.log (2 * (6 * (bsE D m Lh * u) ^ 2 + 6)) + Real.log 4 ≤
      (Real.log 24 + 2 * (D * bsX m Lh ^ D) + 2 + Real.log 4) * u := by nlinarith only [hu, hlog,
          h4]
  calc 24 * (2 * Real.pi) ^ 2 * (4 * (32 * ((((d + 1 : ℕ) : ℝ) + 1) + 1) ^ 4 *
        (Real.log (2 * (6 * (bsE D m Lh * u) ^ 2 + 6)) + Real.log 4)))
      = 24 * (2 * Real.pi) ^ 2 * (4 * (32 * ((((d + 1 : ℕ) : ℝ) + 1) + 1) ^ 4)) *
        (Real.log (2 * (6 * (bsE D m Lh * u) ^ 2 + 6)) + Real.log 4) := by ring
    _ ≤ 24 * (2 * Real.pi) ^ 2 * (4 * (32 * ((((d + 1 : ℕ) : ℝ) + 1) + 1) ^ 4)) *
        ((Real.log 24 + 2 * (D * bsX m Lh ^ D) + 2 + Real.log 4) * u) :=
        mul_le_mul_of_nonneg_left key hc0
    _ = _ := by ring

/-- Blueprint lem:predictors, proof line 1525: exceptional depths. Outside a set of
`lem:height`-many depths, all scaled catalog differences are tiny or large, and the
effective quadratic coefficient is tiny. -/
theorem band_exceptional_depths (G : RealDyadicGrid) {d : ℕ} (θ : Fin d → ℝ) (q₀ : ℝ)
    (T : Finset ℤ) (lam : ℤ → ℝ) (M : ℤ → Matrix (Fin d) (Fin d) ℚ) {τ : Type*}
    (P : Finset τ) (σ : ℤ → τ → Fin d → ℚ) {ε L₂ E B₁ B₂ : ℝ} (hε : 0 < ε) (hεL : ε ≤ L₂)
    (hεE : ε ≤ E) (hB₁ : 2 ≤ B₁) (hB₂ : 2 ≤ B₂)
    (hlam : ∀ s ∈ T, lam s = q₀ + ∑ i, ∑ j, θ i * (M s i j : ℝ) * θ j)
    (hM : ∀ s ∈ T, ∀ i j, (rationalHeight (M s i j) : ℝ) ≤ B₁)
    (hlamE : ∀ s ∈ T, |lam s| * dyadicGridLength G s ^ 2 ≤ E)
    (hσ : ∀ s ∈ T, ∀ p ∈ P, ∀ q ∈ P, ∀ i, (rationalHeight (σ s p i - σ s q i) : ℝ) ≤ B₂) :
    ∃ X : Finset ℤ, (X.card : ℝ) ≤
        32 * ((d : ℝ) + 1) ^ 4 * (Real.log (2 * B₂) + Real.log (2 * L₂ / ε)) +
        32 * ((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 * (Real.log (2 * B₁) + Real.log (2 * E / ε)) ∧
      (∀ s ∈ T, s ∉ X → ∀ p ∈ P, ∀ q ∈ P,
        dyadicGridLength G s * |∑ i, ((σ s p i - σ s q i : ℚ) : ℝ) * θ i| ≤ ε ∨
          L₂ ≤ dyadicGridLength G s * |∑ i, ((σ s p i - σ s q i : ℚ) : ℝ) * θ i|) ∧
      ∀ s ∈ T, s ∉ X → |lam s| * dyadicGridLength G s ^ 2 ≤ ε := by
  classical
  have hlen : ∀ s, dyadicGridLength G s = G.baseLength * (2 : ℝ) ^ (-s) := fun s => rfl
  obtain ⟨N1, hN1, hN1c⟩ := rational_frequency_scale_count (d := d) (u := 1) hB₂ le_rfl hε
    hεL θ G.baseLength
  obtain ⟨N2, hN2, hN2c⟩ := rational_frequency_scale_count (d := d * d + 1) (u := 2) hB₁
    (by norm_num) hε hεE (quadraticParamVector q₀ θ) G.baseLength
  refine ⟨N1 ∪ N2, ?_, ?_, ?_⟩
  · have hc := Finset.card_union_le N1 N2
    have hc' : ((N1 ∪ N2).card : ℝ) ≤ N1.card + N2.card := by exact_mod_cast hc
    exact hc'.trans (add_le_add hN1c hN2c)
  · intro s hs hsX p hp q hq
    have hs1 : s ∉ N1 := fun h => hsX (Finset.mem_union_left _ h)
    by_contra hcon
    push Not at hcon
    apply hs1
    refine (hN1 s).mpr ⟨fun i => σ s p i - σ s q i, hσ s hs p hp q hq, ?_, ?_⟩
    · rw [pow_one, ← hlen]; exact hcon.1.le
    · rw [pow_one, ← hlen]; exact hcon.2.le
  · intro s hs hsX
    have hs2 : s ∉ N2 := fun h => hsX (Finset.mem_union_right _ h)
    have hq := quadraticParam_eval q₀ θ (M s)
    rw [← hlam s hs] at hq
    have hh := quadraticParam_height (M s) (by linarith) (hM s hs)
    by_contra hcon
    push Not at hcon
    apply hs2
    refine (hN2 s).mpr ⟨_, hh, ?_, ?_⟩
    · rw [← hlen, hq, mul_comm]; exact hcon.le
    · rw [← hlen, hq, mul_comm]; exact hlamE s hs

/-- Blueprint lem:predictors, proof line 1525 with eq:tiny-sum: the replacement errors on
the non-exceptional depths sum to `O(ε log)` over all depths. -/
theorem band_tiny_sum (G : RealDyadicGrid) {d : ℕ} (θ : Fin d → ℝ) (q₀ : ℝ) (T : Finset ℤ)
    (lam : ℤ → ℝ) (M : ℤ → Matrix (Fin d) (Fin d) ℚ) {ε B₁ B₂ : ℝ} (hε : 0 ≤ ε)
    (hB₁ : 2 ≤ B₁) (hB₂ : 2 ≤ B₂)
    (hlam : ∀ s ∈ T, lam s = q₀ + ∑ i, ∑ j, θ i * (M s i j : ℝ) * θ j)
    (hM : ∀ s ∈ T, ∀ i j, (rationalHeight (M s i j) : ℝ) ≤ B₁)
    (hquad : ∀ s ∈ T, |lam s| * dyadicGridLength G s ^ 2 ≤ ε) :
    ∑ s ∈ T, (|lam s| * dyadicGridLength G s ^ 2 + finiteTinyMaximum
      (boundedRationalMagnitudes ⌊B₂⌋₊ (rationalEvaluation θ))
      (dyadicGridLength G s ^ 1) ε) ≤
      128 * ((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 * Real.log (2 * B₁) * ε +
        128 * ((d : ℝ) + 1) ^ 4 * Real.log (2 * B₂) * ε := by
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · have h := grid_tiny_sum_le (d := d * d + 1) (u := 2) G (quadraticParamVector q₀ θ) hB₁
      (by norm_num) hε T
    refine le_trans (Finset.sum_le_sum fun s hs => ?_) h
    have hq := quadraticParam_eval q₀ θ (M s)
    rw [← hlam s hs] at hq
    have hh := quadraticParam_height (M s) (by linarith) (hM s hs)
    have := le_tinyMaximum_of_rational (quadraticParamVector q₀ θ) _ hh
      (w := dyadicGridLength G s ^ 2) (ε := ε) (by positivity)
      (by rw [hq, mul_comm]; exact hquad s hs)
    rw [hq, mul_comm] at this
    exact this
  · exact grid_tiny_sum_le G θ hB₂ le_rfl hε T

/-- The total quadratic size over all depths, by eq:tiny-sum at the threshold `E`. -/
theorem band_quadratic_total (G : RealDyadicGrid) {d : ℕ} (θ : Fin d → ℝ) (q₀ : ℝ)
    (T : Finset ℤ) (lam : ℤ → ℝ) (M : ℤ → Matrix (Fin d) (Fin d) ℚ) {E B₁ : ℝ} (hE : 0 ≤ E)
    (hB₁ : 2 ≤ B₁)
    (hlam : ∀ s ∈ T, lam s = q₀ + ∑ i, ∑ j, θ i * (M s i j : ℝ) * θ j)
    (hM : ∀ s ∈ T, ∀ i j, (rationalHeight (M s i j) : ℝ) ≤ B₁)
    (hlamE : ∀ s ∈ T, |lam s| * dyadicGridLength G s ^ 2 ≤ E) :
    ∑ s ∈ T, 2 * Real.pi * |lam s| * dyadicGridLength G s ^ 2 ≤
      2 * Real.pi * (128 * ((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 * Real.log (2 * B₁) * E) := by
  have h := grid_tiny_sum_le (d := d * d + 1) (u := 2) G (quadraticParamVector q₀ θ) hB₁
    (by norm_num) hE T
  have e : ∑ s ∈ T, 2 * Real.pi * |lam s| * dyadicGridLength G s ^ 2 =
      2 * Real.pi * ∑ s ∈ T, |lam s| * dyadicGridLength G s ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [e]
  refine mul_le_mul_of_nonneg_left (le_trans (Finset.sum_le_sum fun s hs => ?_) h)
    (by positivity)
  have hq := quadraticParam_eval q₀ θ (M s)
  rw [← hlam s hs] at hq
  have hh := quadraticParam_height (M s) (by linarith) (hM s hs)
  have := le_tinyMaximum_of_rational (quadraticParamVector q₀ θ) _ hh
    (w := dyadicGridLength G s ^ 2) (ε := E) (by positivity)
    (by rw [hq, mul_comm]; exact hlamE s hs)
  rw [hq, mul_comm] at this
  exact this



end TrilinearHT.Auto
end
