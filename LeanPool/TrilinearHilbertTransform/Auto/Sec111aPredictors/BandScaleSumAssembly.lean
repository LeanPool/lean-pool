/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec111aPredictors.BandScaleSumCore

/-!
# Trilinear Hilbert transform: band_scale_sum_assembly
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate

open scoped Classical in
private def BandScaleSumAssemblyStage2Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (d : ℕ)
    (_ : (1 : ℕ) ≤ d)
    (A : QuadraticChartData d)
    (_ : IsBoundedQuadraticChart A)
    (D : ℕ)
    (J1 : ℕ)
    (m : ℕ)
    (Lh : ℝ)
    (_ : (0 : ℝ) ≤ Lh)
    (G : RealDyadicGrid)
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
    (_ : ∀ I ∈ S, ∀ (ξ : ℝ), bandAmplitude (quadraticChartAtom A) (dyadicGridLength G I.1) ξ
      ≤ Real.exp (-(↑m : ℝ)))
    (lamf : ℤ → ℝ)
    (Mf : ℤ → Matrix (Fin d) (Fin d) ℚ)
    (σf : ℤ → ℕ × (Fin (d + d) → ℤ) → Fin d → ℚ)
    (coeff : ℤ → ℕ × (Fin (d + d) → ℤ) → ℂ),
  let T : Finset ℤ :=
    Finset.image Prod.fst S
  ∀ (_ : ∀ s ∉ T, coeff s = (0 : ℕ × (Fin (d + d) → ℤ) → ℂ))
    (_ : (1 : ℝ) ≤ bsE D m Lh)
    (_ : (0 : ℝ) < bsEps D m Lh)
    (_ : (3 : ℝ) ≤ bsL2 D m Lh)
    (_ : (2 : ℝ) ≤ bsBc κ d D J1 m Lh)
    (_ : (0 : ℝ) ≤ bsE1 J1 m Lh),
  let N₀ : ℕ :=
    ⌊bsE D m Lh⌋₊
  ∀ (_ : ∀ s ∈ T, (∀ (i j : Fin d), (↑(rationalHeight (Mf s i j)) : ℝ) ≤ bsE D m Lh) ∧ lamf s
      = A.quadratic + ∑ i : Fin d, ∑ j : Fin d, A.horizontal i * (↑(Mf s i j) : ℝ) *
      A.horizontal j ∧ |lamf s| * dyadicGridLength G s ^ (2 : ℕ) ≤ bsE D m Lh ∧ (∀ (p :
      ℕ × (Fin (d + d) → ℤ)) (i : Fin d), (↑(rationalHeight (σf s p i)) : ℝ) ≤ bsE D m
      Lh * ((1 : ℝ) + frequencyLength p.2)) ∧ (∀ (t : ℝ), |t| ≤ (2 : ℝ) *
      dyadicGridLength G s → HasSum (fun (p : ℕ × (Fin (d + d) → ℤ)) => coeff s p *
      quadPhase (lamf s) (A.linear + ∑ i : Fin d, (↑(σf s p i) : ℝ) * A.horizontal i) t)
      (quadraticChartAtom A t)) ∧ (Summable fun (p : ℕ × (Fin (d + d) → ℤ)) => ‖coeff s
      p‖) ∧ ∑' (p : ℕ × (Fin (d + d) → ℤ)), ‖coeff s p‖ ≤ bsE D m Lh ∧ (∀ (p : ℕ × (Fin
      (d + d) → ℤ)), N₀ ≤ p.1 → coeff s p = (0 : ℂ)) ∧ ∀ (p : ℕ × (Fin (d + d) → ℤ)),
      ‖coeff s p‖ * ((1 : ℝ) + frequencyLength p.2) ^ (d + (1 : ℕ)) ^ (2 : ℕ) ≤ bsE1 J1
      m Lh),
  let K₀ : ℕ :=
    bsK0 κ d D J1 m Lh
  let P : Finset (ℕ × (Fin (d + d) → ℤ)) :=
    Finset.range N₀ ×ˢ frequencyTruncationSet (d + d) K₀
  ∀ (X : Finset ℤ)
    (_ : (↑X.card : ℝ) ≤ (32 : ℝ) * ((↑d : ℝ) + (1 : ℝ)) ^ (4 : ℕ) * (Real.log ((2 : ℝ) *
      bsB2 κ d D J1 m Lh) + Real.log ((2 : ℝ) * bsL2 D m Lh / bsEps D m Lh)) + (32 : ℝ)
      * ((↑(d * d + (1 : ℕ)) : ℝ) + (1 : ℝ)) ^ (4 : ℕ) * (Real.log ((2 : ℝ) * bsB1 D m
      Lh) + Real.log ((2 : ℝ) * bsE D m Lh / bsEps D m Lh)))
    (_ : ∀ s ∈ T, s ∉ X → |lamf s| * dyadicGridLength G s ^ (2 : ℕ) ≤ bsEps D m Lh),
  let freq : ℤ → ℕ × (Fin (d + d) → ℤ) → ℝ :=
    fun (s : ℤ) (p : ℕ × (Fin (d + d) → ℤ)) => A.linear + ∑ i : Fin d, (↑(σf s p i) : ℝ)
      * A.horizontal i
  ∀ (_ : ∀ s ∈ T, s ∉ X → ∀ p ∈ P, ∀ q ∈ P, dyadicGridLength G s * |freq s p - freq s q| ≤
      bsEps D m Lh ∨ bsL2 D m Lh ≤ dyadicGridLength G s * |freq s p - freq s q|),
  let tiny : ℤ → ℝ :=
    fun (s : ℤ) => finiteTinyMaximum (boundedRationalMagnitudes ⌊bsB2 κ d D J1 m Lh⌋₊
      (rationalEvaluation A.horizontal)) (dyadicGridLength G s ^ (1 : ℕ)) (bsEps D m Lh)
  ∀ (_ : ∀ (s : ℤ), (0 : ℝ) ≤ tiny s)
    (_ : ∀ s ∈ T, s ∉ X → ∀ p ∈ P, ∀ q ∈ P, dyadicGridLength G s * |freq s p - freq s q| ≤
      bsEps D m Lh → dyadicGridLength G s * |freq s p - freq s q| ≤ tiny s)
    (_ : ∑ s ∈ T with s ∉ X, (|lamf s| * dyadicGridLength G s ^ (2 : ℕ) + tiny s) ≤ (128 : ℝ)
      * ((↑(d * d + (1 : ℕ)) : ℝ) + (1 : ℝ)) ^ (4 : ℕ) * Real.log ((2 : ℝ) * bsB1 D m
      Lh) * bsEps D m Lh + (128 : ℝ) * ((↑d : ℝ) + (1 : ℝ)) ^ (4 : ℕ) * Real.log ((2 :
      ℝ) * bsB2 κ d D J1 m Lh) * bsEps D m Lh)
    (_ : ∀ (s : ℤ), ∑ p ∈ P, ‖coeff s p‖ ≤ bsE D m Lh),
  let τt : ℝ :=
    (↑N₀ : ℝ) * (bsE1 J1 m Lh * ((2 : ℝ) * (7 : ℝ) ^ (d + d) * ((2 : ℝ) * Real.pi) ^ (d
      + (1 : ℕ)) ^ (2 : ℕ) / (2 : ℝ) ^ K₀))
  ∀ (_ : ∀ (s : ℤ), (∑' (p : ℕ × (Fin (d + d) → ℤ)), if p ∈ P then (0 : ℝ) else ‖coeff s p‖)
      ≤ τt)
    (_ : τt + bsE D m Lh * ((8 : ℝ) * Real.pi * bsEps D m Lh + (4 : ℝ) * Real.pi * bsEps D m
      Lh) + bandDecay * bsE D m Lh / bsL2 D m Lh ^ (2 : ℕ) ≤ Real.exp (-(↑m : ℝ)) / (2 :
      ℝ)),
  let χc : Fin (d + (1 : ℕ)) → ℝ :=
    Fin.cons A.linear A.horizontal
  ∀ (_ : ∀ s ∈ T, ∀ p ∈ P, ∃ (q : Fin (d + (1 : ℕ)) → ℚ), (∀ (j : Fin (d + (1 : ℕ))),
      (↑(rationalHeight (q j)) : ℝ) ≤ bsBc κ d D J1 m Lh) ∧ freq s p / ((↑(↑b : ℕ) : ℝ)
      - (↑(↑a : ℕ) : ℝ)) = ∑ j : Fin (d + (1 : ℕ)), (↑(q j) : ℝ) * χc j),
  let env : ℕ × (Fin (d + d) → ℤ) → ℝ :=
    fun (p : ℕ × (Fin (d + d) → ℤ)) => if p.1 < N₀ then bsE1 J1 m Lh * (((1 : ℝ) +
      frequencyLength p.2) ^ (d + (1 : ℕ)) ^ (2 : ℕ))⁻¹ else (0 : ℝ)
  ∀ (_ : ∀ (s : ℤ) (p : ℕ × (Fin (d + d) → ℤ)), ‖coeff s p‖ ≤ env p),
  let Λ : ℝ :=
    bsLam d D m Lh
  ∀ (_ : ∑ s ∈ T, (2 : ℝ) * Real.pi * |lamf s| * dyadicGridLength G s ^ (2 : ℕ) ≤ Λ),
  let Mt : ℕ × (Fin (d + d) → ℤ) → ℝ :=
    fun (p : ℕ × (Fin (d + d) → ℤ)) => clumpMultiplicity (d + (1 : ℕ)) ((6 : ℝ) * (bsE D
      m Lh * ((1 : ℝ) + frequencyLength p.2)) ^ (2 : ℕ) + (6 : ℝ))
  ∀ (_ : ∀ p ∉ P, ∀ (ξ : ℝ), ∑ x ∈ Finset.image (fun (I : ℤ × ℤ) => (I.1, freq I.1 p / ((↑(↑b
      : ℕ) : ℝ) - (↑(↑a : ℕ) : ℝ)))) S, bumpMultiplier (dyadicGridLength G x.1 * (ξ -
      x.2)) ≤ Mt p)
    (_ : (0 : ℝ) ≤ bsCT κ d D m Lh)
    (_ : ∀ (p : ℕ × (Fin (d + d) → ℤ)), linearScaleConst κ * Mt p + localKernelSupBound κ * Λ
      ≤ bsCT κ d D m Lh * ((1 : ℝ) + frequencyLength p.2))
    (_ : ∀ (p : ℕ × (Fin (d + d) → ℤ)), (0 : ℝ) ≤ linearScaleConst κ * Mt p +
      localKernelSupBound κ * Λ),
  ∑ I ∈ S, dyadicGridLength G I.1 * ‖separatedLocalForm (dyadicGridLength G I.1) (w I)
    (quadraticChartAtom A) a b (fun (y : ℝ) => ψa y * za I y) fun (y : ℝ) => ψb y * zb
    I y‖ ≤ Real.exp (-(↑m : ℝ)) * bandBracket κ d D J1 m Lh * Ka * Kb * √(∫ (y : ℝ) in
    dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ (2 : ℕ)) * √(∫ (y : ℝ) in dyadicGridCell G J.1
    J.2, ‖Fb y‖ ^ (2 : ℕ))


open scoped Classical in
private def BandScaleSumAssemblyStage1Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (d : ℕ)
    (_ : (1 : ℕ) ≤ d)
    (A : QuadraticChartData d)
    (_ : IsBoundedQuadraticChart A)
    (D : ℕ)
    (J1 : ℕ)
    (m : ℕ)
    (Lh : ℝ)
    (_ : (0 : ℝ) ≤ Lh)
    (G : RealDyadicGrid)
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
    (_ : ∀ I ∈ S, ∀ (ξ : ℝ), bandAmplitude (quadraticChartAtom A) (dyadicGridLength G I.1) ξ
      ≤ Real.exp (-(↑m : ℝ)))
    (lamf : ℤ → ℝ)
    (Mf : ℤ → Matrix (Fin d) (Fin d) ℚ)
    (σf : ℤ → ℕ × (Fin (d + d) → ℤ) → Fin d → ℚ)
    (coeff : ℤ → ℕ × (Fin (d + d) → ℤ) → ℂ),
  let T : Finset ℤ :=
    Finset.image Prod.fst S
  ∀ (_ : ∀ s ∉ T, coeff s = (0 : ℕ × (Fin (d + d) → ℤ) → ℂ))
    (_ : (1 : ℝ) ≤ bsE D m Lh)
    (_ : (0 : ℝ) < bsEps D m Lh)
    (_ : (3 : ℝ) ≤ bsL2 D m Lh)
    (_ : (2 : ℝ) ≤ bsB1 D m Lh)
    (_ : (2 : ℝ) ≤ bsBc κ d D J1 m Lh)
    (_ : (0 : ℝ) ≤ bsE1 J1 m Lh),
  let N₀ : ℕ :=
    ⌊bsE D m Lh⌋₊
  ∀ (_ : ∀ s ∈ T, (∀ (i j : Fin d), (↑(rationalHeight (Mf s i j)) : ℝ) ≤ bsE D m Lh) ∧ lamf s
      = A.quadratic + ∑ i : Fin d, ∑ j : Fin d, A.horizontal i * (↑(Mf s i j) : ℝ) *
      A.horizontal j ∧ |lamf s| * dyadicGridLength G s ^ (2 : ℕ) ≤ bsE D m Lh ∧ (∀ (p :
      ℕ × (Fin (d + d) → ℤ)) (i : Fin d), (↑(rationalHeight (σf s p i)) : ℝ) ≤ bsE D m
      Lh * ((1 : ℝ) + frequencyLength p.2)) ∧ (∀ (t : ℝ), |t| ≤ (2 : ℝ) *
      dyadicGridLength G s → HasSum (fun (p : ℕ × (Fin (d + d) → ℤ)) => coeff s p *
      quadPhase (lamf s) (A.linear + ∑ i : Fin d, (↑(σf s p i) : ℝ) * A.horizontal i) t)
      (quadraticChartAtom A t)) ∧ (Summable fun (p : ℕ × (Fin (d + d) → ℤ)) => ‖coeff s
      p‖) ∧ ∑' (p : ℕ × (Fin (d + d) → ℤ)), ‖coeff s p‖ ≤ bsE D m Lh ∧ (∀ (p : ℕ × (Fin
      (d + d) → ℤ)), N₀ ≤ p.1 → coeff s p = (0 : ℂ)) ∧ ∀ (p : ℕ × (Fin (d + d) → ℤ)),
      ‖coeff s p‖ * ((1 : ℝ) + frequencyLength p.2) ^ (d + (1 : ℕ)) ^ (2 : ℕ) ≤ bsE1 J1
      m Lh),
  let K₀ : ℕ :=
    bsK0 κ d D J1 m Lh
  let P : Finset (ℕ × (Fin (d + d) → ℤ)) :=
    Finset.range N₀ ×ˢ frequencyTruncationSet (d + d) K₀
  ∀ (_ : ∀ s ∈ T, ∀ p ∈ P, ∀ (i : Fin d), (↑(rationalHeight (σf s p i)) : ℝ) ≤ bsBσ κ d D J1
      m Lh)
    (X : Finset ℤ)
    (_ : (↑X.card : ℝ) ≤ (32 : ℝ) * ((↑d : ℝ) + (1 : ℝ)) ^ (4 : ℕ) * (Real.log ((2 : ℝ) *
      bsB2 κ d D J1 m Lh) + Real.log ((2 : ℝ) * bsL2 D m Lh / bsEps D m Lh)) + (32 : ℝ)
      * ((↑(d * d + (1 : ℕ)) : ℝ) + (1 : ℝ)) ^ (4 : ℕ) * (Real.log ((2 : ℝ) * bsB1 D m
      Lh) + Real.log ((2 : ℝ) * bsE D m Lh / bsEps D m Lh)))
    (_ : ∀ s ∈ T, s ∉ X → |lamf s| * dyadicGridLength G s ^ (2 : ℕ) ≤ bsEps D m Lh),
  let freq : ℤ → ℕ × (Fin (d + d) → ℤ) → ℝ :=
    fun (s : ℤ) (p : ℕ × (Fin (d + d) → ℤ)) => A.linear + ∑ i : Fin d, (↑(σf s p i) : ℝ)
      * A.horizontal i
  ∀ (_ : ∀ s ∈ T, s ∉ X → ∀ p ∈ P, ∀ q ∈ P, dyadicGridLength G s * |freq s p - freq s q| ≤
      bsEps D m Lh ∨ bsL2 D m Lh ≤ dyadicGridLength G s * |freq s p - freq s q|),
  let tiny : ℤ → ℝ :=
    fun (s : ℤ) => finiteTinyMaximum (boundedRationalMagnitudes ⌊bsB2 κ d D J1 m Lh⌋₊
      (rationalEvaluation A.horizontal)) (dyadicGridLength G s ^ (1 : ℕ)) (bsEps D m Lh)
  ∀ (_ : ∀ (s : ℤ), (0 : ℝ) ≤ tiny s)
    (_ : ∀ s ∈ T, s ∉ X → ∀ p ∈ P, ∀ q ∈ P, dyadicGridLength G s * |freq s p - freq s q| ≤
      bsEps D m Lh → dyadicGridLength G s * |freq s p - freq s q| ≤ tiny s)
    (_ : ∑ s ∈ T with s ∉ X, (|lamf s| * dyadicGridLength G s ^ (2 : ℕ) + tiny s) ≤ (128 : ℝ)
      * ((↑(d * d + (1 : ℕ)) : ℝ) + (1 : ℝ)) ^ (4 : ℕ) * Real.log ((2 : ℝ) * bsB1 D m
      Lh) * bsEps D m Lh + (128 : ℝ) * ((↑d : ℝ) + (1 : ℝ)) ^ (4 : ℕ) * Real.log ((2 :
      ℝ) * bsB2 κ d D J1 m Lh) * bsEps D m Lh)
    (_ : ∀ (s : ℤ), ∑ p ∈ P, ‖coeff s p‖ ≤ bsE D m Lh),
  let τt : ℝ :=
    (↑N₀ : ℝ) * (bsE1 J1 m Lh * ((2 : ℝ) * (7 : ℝ) ^ (d + d) * ((2 : ℝ) * Real.pi) ^ (d
      + (1 : ℕ)) ^ (2 : ℕ) / (2 : ℝ) ^ K₀))
  ∀ (_ : ∀ (s : ℤ), (∑' (p : ℕ × (Fin (d + d) → ℤ)), if p ∈ P then (0 : ℝ) else ‖coeff s p‖)
      ≤ τt)
    (_ : τt ≤ Real.exp (-(↑m : ℝ)) / (8 : ℝ)),
  ∑ I ∈ S, dyadicGridLength G I.1 * ‖separatedLocalForm (dyadicGridLength G I.1) (w I)
    (quadraticChartAtom A) a b (fun (y : ℝ) => ψa y * za I y) fun (y : ℝ) => ψb y * zb
    I y‖ ≤ Real.exp (-(↑m : ℝ)) * bandBracket κ d D J1 m Lh * Ka * Kb * √(∫ (y : ℝ) in
    dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ (2 : ℕ)) * √(∫ (y : ℝ) in dyadicGridCell G J.1
    J.2, ‖Fb y‖ ^ (2 : ℕ))




private theorem band_scale_sum_assembly_stage_2 : BandScaleSumAssemblyStage2Statement := by
  classical
  intro κ d hd A hAb D J1 m Lh hLh G J S hSJ w hw a b hab ψa ψb hψam hψbm hψa hψb Fa Fb za zb Ka
    Kb hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 hband lamf Mf σf coeff T hzero hE1 hε0 hL₂3
    hBc2 hE10 N₀ hprops K₀ P X hXc hXquad freq hdich tiny htiny0 htiny hΘ hAtot τt htail hsmall
  let k : ℤ :=
    (↑(↑b : ℕ) : ℤ) - (↑(↑a : ℕ) : ℤ)
  intro χc hrat env henv Λ hΛ Mt hMt hCT0 hg hg0
  obtain ⟨hens, hTs, hTt⟩ := catalog_weighted_tail hd (N₀ := N₀) (K₀ := K₀) hE10 hCT0
    (fun p => linearScaleConst κ * Mt p + localKernelSupBound κ * Λ) hg0 hg
  have hTt' : ∑' p, (if p ∈ P then 0 else
      env p * (linearScaleConst κ * Mt p + localKernelSupBound κ * Λ)) ≤
      Real.exp (-(m : ℝ)) := by
    refine hTt.trans ?_
    have h := bs_tail_budget κ d D J1 m hLh (k := (d + 1) ^ 2 - 1) (Nat.sub_le _ _) hCT0
      (by linarith)
    have h8 : Real.exp (-(m : ℝ)) / 8 ≤ Real.exp (-(m : ℝ)) := by
      have := Real.exp_pos (-(m : ℝ)); linarith
    refine le_trans (le_of_eq ?_) (h.trans h8)
    ring
  -- the remaining inputs of the core estimate
  have hexp : ∀ s ∈ T, ∀ t, |t| ≤ 2 * dyadicGridLength G s →
      HasSum (fun p => coeff s p * quadPhase (lamf s) (freq s p) t) (quadraticChartAtom A t) :=
    fun s hs t ht => (hprops s hs).2.2.2.2.1 t ht
  have hcs : ∀ s, Summable (fun p => ‖coeff s p‖) := by
    intro s
    by_cases hs : s ∈ T
    · exact (hprops s hs).2.2.2.2.2.1
    · rw [hzero s hs]; simp only [Pi.zero_apply, norm_zero]; exact summable_zero
  have hεlt : bsEps D m Lh < 1 := by
    have hem1 : Real.exp (-(m : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := Nat.cast_nonneg (α := ℝ) m; linarith)
    unfold bsEps
    rw [div_lt_one (by positivity)]
    nlinarith only [Real.pi_gt_three, hE1, hem1]
  have h3 : 3 * bsEps D m Lh < bsL2 D m Lh := by linarith
  have hcore := band_scale_sum_core G κ J S hSJ w hw hab (quadraticChartAtom_measurable A) hAb
    hψam hψbm hψa hψb hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 hband coeff lamf freq hexp
    hcs P X hε0.le hε0.le h3 hL₂3 hdich hXquad tiny htiny0 htiny hΘ bandDecay_spec.2
    bandDecay_spec.1 hAtot htail hsmall χc hBc2 hrat env henv hens Mt hMt hΛ hTs hTt'
  refine hcore.trans ?_
  -- compare with the explicit bracket
  set Na := Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2)
  set Nb := Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2)
  have hK : 0 ≤ Ka * Kb * Na * Nb := by positivity
  have hem := Real.exp_pos (-(m : ℝ))
  have hKF := kernelFourierConst_nonneg κ
  have hcardX : kernelFourierConst κ * Real.exp (-(m : ℝ)) * X.card ≤
      Real.exp (-(m : ℝ)) * (kernelFourierConst κ * (32 * ((d : ℝ) + 1) ^ 4 *
        (Real.log (2 * bsB2 κ d D J1 m Lh) + Real.log (2 * bsL2 D m Lh / bsEps D m Lh)) +
        32 * ((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 *
        (Real.log (2 * bsB1 D m Lh) + Real.log (2 * bsE D m Lh / bsEps D m Lh)))) := by
    rw [show kernelFourierConst κ * Real.exp (-(m : ℝ)) * X.card =
      Real.exp (-(m : ℝ)) * (kernelFourierConst κ * X.card) by ring]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXc hKF) hem.le
  have hΘeq : localKernelSupBound κ * bsE D m Lh * (2 * Real.pi) *
      (128 * ((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 * Real.log (2 * bsB1 D m Lh) * bsEps D m Lh +
        128 * ((d : ℝ) + 1) ^ 4 * Real.log (2 * bsB2 κ d D J1 m Lh) * bsEps D m Lh) =
      Real.exp (-(m : ℝ)) * (4 * localKernelSupBound κ *
        (((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 * Real.log (2 * bsB1 D m Lh) +
          ((d : ℝ) + 1) ^ 4 * Real.log (2 * bsB2 κ d D J1 m Lh))) := by
    unfold bsEps
    field_simp
    ring
  have hbr : kernelFourierConst κ * Real.exp (-(m : ℝ)) * X.card +
      Real.exp (-(m : ℝ)) * linearScaleConst κ * clumpMultiplicity (d + 1) (bsBc κ d D J1 m Lh) +
      localKernelSupBound κ * bsE D m Lh * (2 * Real.pi) *
        (128 * ((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 * Real.log (2 * bsB1 D m Lh) * bsEps D m Lh +
          128 * ((d : ℝ) + 1) ^ 4 * Real.log (2 * bsB2 κ d D J1 m Lh) * bsEps D m Lh) +
      Real.exp (-(m : ℝ)) ≤ Real.exp (-(m : ℝ)) * bandBracket κ d D J1 m Lh := by
    rw [hΘeq]
    calc _ ≤ Real.exp (-(m : ℝ)) * (kernelFourierConst κ * (32 * ((d : ℝ) + 1) ^ 4 *
          (Real.log (2 * bsB2 κ d D J1 m Lh) + Real.log (2 * bsL2 D m Lh / bsEps D m Lh)) +
          32 * ((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 *
          (Real.log (2 * bsB1 D m Lh) + Real.log (2 * bsE D m Lh / bsEps D m Lh)))) +
        Real.exp (-(m : ℝ)) * linearScaleConst κ *
          clumpMultiplicity (d + 1) (bsBc κ d D J1 m Lh) +
        Real.exp (-(m : ℝ)) * (4 * localKernelSupBound κ *
          (((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 * Real.log (2 * bsB1 D m Lh) +
            ((d : ℝ) + 1) ^ 4 * Real.log (2 * bsB2 κ d D J1 m Lh))) +
        Real.exp (-(m : ℝ)) := by linarith only [hcardX]
      _ = _ := by unfold bandBracket; ring
  calc (kernelFourierConst κ * Real.exp (-(m : ℝ)) * X.card +
        Real.exp (-(m : ℝ)) * linearScaleConst κ * clumpMultiplicity (d + 1) (bsBc κ d D J1 m Lh) +
        localKernelSupBound κ * bsE D m Lh * (2 * Real.pi) *
          (128 * ((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 * Real.log (2 * bsB1 D m Lh) * bsEps D m Lh +
            128 * ((d : ℝ) + 1) ^ 4 * Real.log (2 * bsB2 κ d D J1 m Lh) * bsEps D m Lh) +
        Real.exp (-(m : ℝ))) * Ka * Kb * Na * Nb
      = (kernelFourierConst κ * Real.exp (-(m : ℝ)) * X.card +
        Real.exp (-(m : ℝ)) * linearScaleConst κ * clumpMultiplicity (d + 1) (bsBc κ d D J1 m Lh) +
        localKernelSupBound κ * bsE D m Lh * (2 * Real.pi) *
          (128 * ((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 * Real.log (2 * bsB1 D m Lh) * bsEps D m Lh +
            128 * ((d : ℝ) + 1) ^ 4 * Real.log (2 * bsB2 κ d D J1 m Lh) * bsEps D m Lh) +
        Real.exp (-(m : ℝ))) * (Ka * Kb * Na * Nb) := by ring
    _ ≤ (Real.exp (-(m : ℝ)) * bandBracket κ d D J1 m Lh) * (Ka * Kb * Na * Nb) :=
        mul_le_mul_of_nonneg_right hbr hK
    _ = _ := by ring



private theorem band_scale_sum_assembly_stage_1 : BandScaleSumAssemblyStage1Statement := by
  classical
  intro κ d hd A hAb D J1 m Lh hLh G J S hSJ w hw a b hab ψa ψb hψam hψbm hψa hψb Fa Fb za zb Ka
    Kb hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 hband lamf Mf σf coeff T hzero hE1 hε0 hL₂3
    hB₁2 hBc2 hE10 N₀ hprops K₀ P hσP X hXc hXquad freq hdich tiny htiny0 htiny hΘ hAtot τt htail
    hτtb
  have hsmall : τt + bsE D m Lh * (8 * Real.pi * bsEps D m Lh + 4 * Real.pi * bsEps D m Lh) +
      bandDecay * bsE D m Lh / bsL2 D m Lh ^ 2 ≤ Real.exp (-(m : ℝ)) / 2 := by
    have h1 := bs_quadratic_budget D m hLh
    have h2 := bs_decay_budget D m hLh
    have h3 := Real.exp_pos (-(m : ℝ))
    rw [h1]
    linarith
  -- rational centers
  set! k : ℤ := ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) with hkd
  have hkR : (k : ℝ) = (b : ℝ) - (a : ℝ) := by rw [hkd]; push_cast; rfl
  have hk0 : k ≠ 0 := by
    rw [hkd]; intro h; apply hab; apply Fin.ext; omega
  have hk3 : |(k : ℝ)| ≤ 3 := by
    rw [hkR]
    have ha := abs_fin_four_le a
    have hb := abs_fin_four_le b
    rw [abs_le] at ha hb ⊢
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2,
      show (0 : ℝ) ≤ (a : ℝ) by positivity, show (0 : ℝ) ≤ (b : ℝ) by positivity]
  set! χc : Fin (d + 1) → ℝ := Fin.cons A.linear A.horizontal with hχc
  have hrat : ∀ s ∈ T, ∀ p ∈ P, ∃ q : Fin (d + 1) → ℚ,
      (∀ j, (rationalHeight (q j) : ℝ) ≤ bsBc κ d D J1 m Lh) ∧
        freq s p / ((b : ℝ) - (a : ℝ)) = ∑ j, (q j : ℝ) * χc j := by
    intro s hs p hp
    obtain ⟨h1, h2⟩ := center_rational A.linear A.horizontal (σf s p) hk0 hk3 (hσP s hs p hp)
    refine ⟨_, fun j => (h1 j).trans (le_of_eq (by unfold bsBc; rfl)), ?_⟩
    rw [← hkR]; exact h2
  -- envelope of the coefficients
  set! env : ℕ × (Fin (d + d) → ℤ) → ℝ := fun p => if p.1 < N₀ then
    bsE1 J1 m Lh * ((1 + frequencyLength p.2) ^ ((d + 1) ^ 2))⁻¹ else 0 with henvd
  have henv : ∀ s p, ‖coeff s p‖ ≤ env p := by
    intro s p
    have hpos : 0 < (1 + frequencyLength p.2) ^ ((d + 1) ^ 2) := by
      have := frequencyLength_nonneg p.2; positivity
    by_cases hs : s ∈ T
    · simp only [henvd]
      split_ifs with hp
      · rw [← div_eq_mul_inv, le_div_iff₀ hpos]
        exact (hprops s hs).2.2.2.2.2.2.2.2 p
      · rw [(hprops s hs).2.2.2.2.2.2.2.1 p (not_lt.mp hp), norm_zero]
    · rw [hzero s hs]
      simp only [Pi.zero_apply, norm_zero, henvd]
      split_ifs
      · positivity
      · exact le_rfl
  -- tail multiplicities and the quadratic total
  set! Λ := bsLam d D m Lh with hΛd
  have hΛ : ∑ s ∈ T, 2 * Real.pi * |lamf s| * dyadicGridLength G s ^ 2 ≤ Λ := by
    have h := band_quadratic_total G A.horizontal A.quadratic T lamf Mf (by linarith) hB₁2
      (fun s hs => (hprops s hs).2.1)
      (fun s hs i j => ((hprops s hs).1 i j).trans (by unfold bsB1; linarith))
      (fun s hs => (hprops s hs).2.2.1)
    refine h.trans (le_of_eq ?_)
    rw [hΛd, bsLam, bsB1]
  set! Mt : ℕ × (Fin (d + d) → ℤ) → ℝ := fun p =>
    clumpMultiplicity (d + 1) (6 * (bsE D m Lh * (1 + frequencyLength p.2)) ^ 2 + 6) with hMtd
  have hMt : ∀ p, p ∉ P → ∀ ξ, ∑ x ∈ S.image (fun I => (I.1, freq I.1 p / ((b : ℝ) - (a : ℝ)))),
      bumpMultiplier (dyadicGridLength G x.1 * (ξ - x.2)) ≤ Mt p := by
    intro p _ ξ
    have hu : 1 ≤ 1 + frequencyLength p.2 := by have := frequencyLength_nonneg p.2; linarith
    have hB : 2 ≤ 6 * (bsE D m Lh * (1 + frequencyLength p.2)) ^ 2 + 6 := by
      have : 0 ≤ 6 * (bsE D m Lh * (1 + frequencyLength p.2)) ^ 2 := by positivity
      linarith
    refine rational_center_multiplicity G χc hB _ (fun x hx => ?_) (fun x hx y hy hxy hne => ?_) ξ
    · obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hx
      have hs : I.1 ∈ T := Finset.mem_image_of_mem _ hI
      obtain ⟨h1, h2⟩ := center_rational A.linear A.horizontal (σf I.1 p) hk0 hk3
        ((hprops I.1 hs).2.2.2.1 p)
      refine ⟨_, h1, ?_⟩
      simp only
      rw [← hkR]; exact h2
    · exfalso
      obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨I', _, rfl⟩ := Finset.mem_image.mp hy
      simp only at hxy
      apply hne
      simp only [hxy]
  have hCT0 := bsCT_nonneg κ d D m hLh
  have hg : ∀ p : ℕ × (Fin (d + d) → ℤ), linearScaleConst κ * Mt p + localKernelSupBound κ * Λ ≤
      bsCT κ d D m Lh * (1 + frequencyLength p.2) := by
    intro p
    have hu : 1 ≤ 1 + frequencyLength p.2 := by have := frequencyLength_nonneg p.2; linarith
    have h1 := clumpMultiplicity_tail_le d D m hLh hu
    have hlin := linearScaleConst_nonneg κ
    have hC := localKernelSupBound_nonneg κ
    have hΛ0 : 0 ≤ Λ := by
      rw [hΛd, bsLam]
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (bsE D m Lh + 2) by linarith)
      positivity
    have e1 : linearScaleConst κ * Mt p ≤
        linearScaleConst κ * bsAlpha d D m Lh * (1 + frequencyLength p.2) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 hlin
    have e2 : localKernelSupBound κ * Λ ≤
        localKernelSupBound κ * Λ * (1 + frequencyLength p.2) :=
      le_mul_of_one_le_right (mul_nonneg hC hΛ0) hu
    calc linearScaleConst κ * Mt p + localKernelSupBound κ * Λ
        ≤ linearScaleConst κ * bsAlpha d D m Lh * (1 + frequencyLength p.2) +
          localKernelSupBound κ * Λ * (1 + frequencyLength p.2) := add_le_add e1 e2
      _ = bsCT κ d D m Lh * (1 + frequencyLength p.2) := by
          rw [bsCT, hΛd]; ring
  have hg0 : ∀ p, 0 ≤ linearScaleConst κ * Mt p + localKernelSupBound κ * Λ := by
    intro p
    have hu : 1 ≤ 1 + frequencyLength p.2 := by have := frequencyLength_nonneg p.2; linarith
    have hlin := linearScaleConst_nonneg κ
    have hC := localKernelSupBound_nonneg κ
    have hΛ0 : 0 ≤ Λ := by
      rw [hΛd, bsLam]
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (bsE D m Lh + 2) by linarith)
      positivity
    have hM0 : 0 ≤ Mt p := by
      simp only [hMtd, clumpMultiplicity]
      have : 2 ≤ 6 * (bsE D m Lh * (1 + frequencyLength p.2)) ^ 2 + 6 := by
        have : 0 ≤ 6 * (bsE D m Lh * (1 + frequencyLength p.2)) ^ 2 := by positivity
        linarith
      have := heightBandConst_nonneg (d + 1) this
      positivity
    positivity
  expose_names
  exact @band_scale_sum_assembly_stage_2 κ d hd A hAb D J1 m Lh hLh G J S hSJ w hw a b hab ψa ψb
    hψam hψbm hψa hψb Fa Fb za zb Ka Kb hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 hband lamf Mf
    σf coeff hzero hE1 hε0 hL₂3 hBc2 hE10 hprops X hXc hXquad hdich htiny0 htiny hΘ hAtot htail
    hsmall hrat henv hΛ hMt hCT0 hg hg0


/-- Assembly of `eq:band-scale-sum` from per-depth chart expansions with the explicit
parameters (blueprint lem:predictors, proof lines 1517–1542). -/
theorem band_scale_sum_assembly (κ : LocalKernelClass) {d : ℕ} (hd : 1 ≤ d)
    (A : QuadraticChartData d) (hAb : IsBoundedQuadraticChart A) (D J1 m : ℕ) {Lh : ℝ}
    (hLh : 0 ≤ Lh) (G : RealDyadicGrid) (J : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (hSJ : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    {a b : Fin 4} (hab : a ≠ b) {ψa ψb : ℝ → ℂ} (hψam : Measurable ψa) (hψbm : Measurable ψb)
    (hψa : ∀ y, ‖ψa y‖ ≤ 1) (hψb : ∀ y, ‖ψb y‖ ≤ 1)
    {Fa Fb : ℝ → ℂ} {za zb : ℤ × ℤ → ℝ → ℂ} {Ka Kb : ℝ} (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb)
    (hza : IsAdmissibleOpponent G J Fa za Ka) (hzb : IsAdmissibleOpponent G J Fb zb Kb)
    (hEa : HasDepthEnergy G J Fa za Ka) (hEb : HasDepthEnergy G J Fb zb Kb)
    (hzam : ∀ I, Measurable (za I)) (hzbm : ∀ I, Measurable (zb I))
    (hza2 : ∀ I, MemLp (za I) 2 (volume.restrict (dyadicGridCell G I.1 I.2)))
    (hzb2 : ∀ I, MemLp (zb I) 2 (volume.restrict (dyadicGridCell G I.1 I.2)))
    (hband : ∀ I ∈ S, ∀ ξ, bandAmplitude (quadraticChartAtom A) (dyadicGridLength G I.1) ξ ≤
      Real.exp (-(m : ℝ)))
    (lamf : ℤ → ℝ) (Mf : ℤ → Matrix (Fin d) (Fin d) ℚ)
    (σf : ℤ → ℕ × (Fin (d + d) → ℤ) → Fin d → ℚ) (coeff : ℤ → ℕ × (Fin (d + d) → ℤ) → ℂ)
    (hprops : ∀ s ∈ S.image Prod.fst,
      (∀ i j, (rationalHeight (Mf s i j) : ℝ) ≤ bsE D m Lh) ∧
      lamf s = A.quadratic + ∑ i, ∑ j, A.horizontal i * (Mf s i j : ℝ) * A.horizontal j ∧
      |lamf s| * dyadicGridLength G s ^ 2 ≤ bsE D m Lh ∧
      (∀ p i, (rationalHeight (σf s p i) : ℝ) ≤ bsE D m Lh * (1 + frequencyLength p.2)) ∧
      (∀ t, |t| ≤ 2 * dyadicGridLength G s → HasSum (fun p => coeff s p *
        quadPhase (lamf s) (A.linear + ∑ i, (σf s p i : ℝ) * A.horizontal i) t)
          (quadraticChartAtom A t)) ∧
      Summable (fun p => ‖coeff s p‖) ∧ (∑' p, ‖coeff s p‖) ≤ bsE D m Lh ∧
      (∀ p, ⌊bsE D m Lh⌋₊ ≤ p.1 → coeff s p = 0) ∧
      ∀ p, ‖coeff s p‖ * (1 + frequencyLength p.2) ^ ((d + 1) ^ 2) ≤ bsE1 J1 m Lh)
    (hzero : ∀ s, s ∉ S.image Prod.fst → coeff s = 0) :
    ∑ I ∈ S, dyadicGridLength G I.1 *
      ‖separatedLocalForm (dyadicGridLength G I.1) (w I) (quadraticChartAtom A) a b
        (fun y => ψa y * za I y) (fun y => ψb y * zb I y)‖ ≤
      Real.exp (-(m : ℝ)) * bandBracket κ d D J1 m Lh * Ka * Kb *
        Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2) *
        Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) := by
  classical
  set T := S.image Prod.fst with hT
  -- basic facts about the parameters
  have hE1 := bsE_one_le D m hLh
  have hε0 := bsEps_pos D m hLh
  have hε1 := bsEps_le_one D m hLh
  have hL₂3 := three_le_bsL2 D m hLh
  have hBσ1 := one_le_bsBσ κ d D J1 m hLh
  have hB₂2 := two_le_bsB2 κ d D J1 m hLh
  have hB₁2 := two_le_bsB1 D m hLh
  have hBc2 := two_le_bsBc κ d D J1 m Lh
  have hE10 : 0 ≤ bsE1 J1 m Lh := (Real.exp_pos _).le
  have hεL : bsEps D m Lh ≤ bsL2 D m Lh := by linarith
  have hεE : bsEps D m Lh ≤ bsE D m Lh := by linarith
  -- the catalog
  set N₀ := ⌊bsE D m Lh⌋₊ with hN₀
  set! K₀ := bsK0 κ d D J1 m Lh with hK₀
  set! P : Finset (ℕ × (Fin (d + d) → ℤ)) :=
    (Finset.range N₀) ×ˢ (frequencyTruncationSet (d + d) K₀) with hP
  have hmemP : ∀ p, p ∈ P ↔ p.1 < N₀ ∧ p.2 ∈ frequencyTruncationSet (d + d) K₀ := by
    intro p; simp [hP, Finset.mem_product]
  have hσP : ∀ s ∈ T, ∀ p ∈ P, ∀ i,
      (rationalHeight (σf s p i) : ℝ) ≤ bsBσ κ d D J1 m Lh := by
    intro s hs p hp i
    refine ((hprops s hs).2.2.2.1 p i).trans ?_
    unfold bsBσ
    exact mul_le_mul_of_nonneg_left (frequencyTruncationSet_le ((hmemP p).mp hp).2)
      (by linarith)
  have hdiffh : ∀ s ∈ T, ∀ p ∈ P, ∀ q ∈ P, ∀ i,
      (rationalHeight (σf s p i - σf s q i) : ℝ) ≤ bsB2 κ d D J1 m Lh := by
    intro s hs p hp q hq i
    refine (rationalHeight_sub_le _ _).trans ?_
    have h1 := hσP s hs p hp i
    have h2 := hσP s hs q hq i
    have h0 : 0 ≤ (rationalHeight (σf s p i) : ℝ) * rationalHeight (σf s q i) := by positivity
    have h3 : (rationalHeight (σf s p i) : ℝ) * rationalHeight (σf s q i) ≤
        bsBσ κ d D J1 m Lh * bsBσ κ d D J1 m Lh :=
      mul_le_mul h1 h2 (by positivity) (by linarith)
    have h4 := pow_le_pow_left₀ h0 h3 2
    unfold bsB2
    nlinarith only [h0, h3]
  -- exceptional depths
  obtain ⟨X, hXc, hXdich, hXquad⟩ := band_exceptional_depths G A.horizontal A.quadratic T lamf
    Mf P σf hε0 hεL hεE hB₁2 hB₂2 (fun s hs => (hprops s hs).2.1)
    (fun s hs i j => ((hprops s hs).1 i j).trans (by unfold bsB1; linarith))
    (fun s hs => (hprops s hs).2.2.1) hdiffh
  -- frequencies
  set! freq : ℤ → ℕ × (Fin (d + d) → ℤ) → ℝ :=
    fun s p => A.linear + ∑ i, (σf s p i : ℝ) * A.horizontal i with hfreq
  have hdiff : ∀ s p q, freq s p - freq s q =
      ∑ i, ((σf s p i - σf s q i : ℚ) : ℝ) * A.horizontal i := by
    intro s p q
    simp only [hfreq]
    rw [show A.linear + ∑ i, (σf s p i : ℝ) * A.horizontal i -
      (A.linear + ∑ i, (σf s q i : ℝ) * A.horizontal i) =
      ∑ i, (σf s p i : ℝ) * A.horizontal i - ∑ i, (σf s q i : ℝ) * A.horizontal i by ring,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  have hdich : ∀ s ∈ T, s ∉ X → ∀ p ∈ P, ∀ q ∈ P,
      dyadicGridLength G s * |freq s p - freq s q| ≤ bsEps D m Lh ∨
        bsL2 D m Lh ≤ dyadicGridLength G s * |freq s p - freq s q| := by
    intro s hs hsX p hp q hq
    rw [hdiff]; exact hXdich s hs hsX p hp q hq
  -- tiny maxima
  set! tiny : ℤ → ℝ := fun s => finiteTinyMaximum
    (boundedRationalMagnitudes ⌊bsB2 κ d D J1 m Lh⌋₊ (rationalEvaluation A.horizontal))
    (dyadicGridLength G s ^ 1) (bsEps D m Lh) with htinyd
  have htiny0 : ∀ s, 0 ≤ tiny s := fun s => finiteTinyMaximum_nonneg _ _ _
  have htiny : ∀ s ∈ T, s ∉ X → ∀ p ∈ P, ∀ q ∈ P,
      dyadicGridLength G s * |freq s p - freq s q| ≤ bsEps D m Lh →
        dyadicGridLength G s * |freq s p - freq s q| ≤ tiny s := by
    intro s hs _ p hp q hq hsmall
    rw [hdiff] at hsmall ⊢
    have h := le_tinyMaximum_of_rational A.horizontal (fun i => σf s p i - σf s q i)
      (hdiffh s hs p hp q hq) (w := dyadicGridLength G s ^ 1) (ε := bsEps D m Lh)
      (pow_nonneg (dyadicGridLength_pos G s).le 1) (by rw [pow_one]; exact hsmall)
    calc dyadicGridLength G s * |∑ i, ((σf s p i - σf s q i : ℚ) : ℝ) * A.horizontal i|
        = dyadicGridLength G s ^ 1 * |∑ i, ((σf s p i - σf s q i : ℚ) : ℝ) * A.horizontal i| := by
          rw [pow_one]
      _ ≤ tiny s := h
  have hΘ : ∑ s ∈ T.filter (fun s => s ∉ X),
      (|lamf s| * dyadicGridLength G s ^ 2 + tiny s) ≤
      128 * ((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 * Real.log (2 * bsB1 D m Lh) * bsEps D m Lh +
        128 * ((d : ℝ) + 1) ^ 4 * Real.log (2 * bsB2 κ d D J1 m Lh) * bsEps D m Lh :=
    band_tiny_sum G A.horizontal A.quadratic _ lamf Mf hε0.le hB₁2 hB₂2
      (fun s hs => (hprops s (Finset.mem_filter.mp hs).1).2.1)
      (fun s hs i j => ((hprops s (Finset.mem_filter.mp hs).1).1 i j).trans
        (by unfold bsB1; linarith))
      (fun s hs => hXquad s (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp hs).2)
  -- catalog mass and tails
  have hAtot : ∀ s, ∑ p ∈ P, ‖coeff s p‖ ≤ bsE D m Lh := by
    intro s
    by_cases hs : s ∈ T
    · exact ((hprops s hs).2.2.2.2.2.1.sum_le_tsum P
        (fun _ _ => norm_nonneg _)).trans (hprops s hs).2.2.2.2.2.2.1
    · rw [hzero s hs]; simp; linarith
  set! τt : ℝ := (N₀ : ℝ) * (bsE1 J1 m Lh * (2 * 7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2) /
    2 ^ K₀)) with hτt
  have htail : ∀ s, ∑' p, (if p ∈ P then 0 else ‖coeff s p‖) ≤ τt := by
    intro s
    by_cases hs : s ∈ T
    · exact catalog_tail_le hd (coeff s) hE10 (hprops s hs).2.2.2.2.2.2.2.1
        (hprops s hs).2.2.2.2.2.2.2.2
    · rw [hzero s hs]; simp only [Pi.zero_apply, norm_zero, ite_self, tsum_zero, hτt]
      positivity
  have hτtb : τt ≤ Real.exp (-(m : ℝ)) / 8 := by
    have h := bs_tail_budget κ d D J1 m hLh (k := (d + 1) ^ 2) le_rfl zero_le_one
      (by linarith [bsCT_nonneg κ d D m hLh])
    rw [hτt]
    calc (N₀ : ℝ) * (bsE1 J1 m Lh * (2 * 7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2) / 2 ^ K₀))
        = (N₀ : ℝ) * bsE1 J1 m Lh * 1 *
          (2 * 7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2) / 2 ^ K₀) := by ring
      _ ≤ _ := h
  expose_names
  exact @band_scale_sum_assembly_stage_1 κ d hd A hAb D J1 m Lh hLh G J S hSJ w hw a b hab ψa ψb
    hψam hψbm hψa hψb Fa Fb za zb Ka Kb hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 hband lamf Mf
    σf coeff hzero hE1 hε0 hL₂3 hB₁2 hBc2 hE10 hprops hσP X hXc hXquad hdich htiny0 htiny hΘ hAtot
    htail hτtb

/-- Blueprint lem:predictors, `eq:band-scale-sum` with explicit parameters: for one
separated time factor `Q` (a bounded chart of complexity `H`) and admissible opponents,
the absolute length-weighted sum over the cells of the `m`-th Fourier-supremum band is at
most `e^{-m}` times the explicit bracket `bandBracket` (a polynomial in `1 + m, log H`;
see `band_scale_sum`). -/
theorem band_scale_sum_param (c₀ : ℕ) (hc : 1 ≤ c₀) (κ : LocalKernelClass) :
    ∃ D J1 : ℕ, 1 ≤ D ∧ ∀ {d : ℕ} (H : ℝ) (A : QuadraticChartData d), 1 ≤ d →
      QuadraticChartComplexity c₀ H A → IsBoundedQuadraticChart A → ∀ (m : ℕ)
      (G : RealDyadicGrid) (J : ℤ × ℤ) (S : Finset (ℤ × ℤ)),
      (∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2) →
      ∀ (w : ℤ × ℤ → ℝ × ℝ → ℂ), (∀ I ∈ S, IsAdmissibleLocalKernel κ
        (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I)) →
      ∀ {a b : Fin 4}, a ≠ b → ∀ {ψa ψb : ℝ → ℂ}, Measurable ψa → Measurable ψb →
      (∀ y, ‖ψa y‖ ≤ 1) → (∀ y, ‖ψb y‖ ≤ 1) →
      ∀ {Fa Fb : ℝ → ℂ} {za zb : ℤ × ℤ → ℝ → ℂ} {Ka Kb : ℝ}, 0 ≤ Ka → 0 ≤ Kb →
      IsAdmissibleOpponent G J Fa za Ka → IsAdmissibleOpponent G J Fb zb Kb →
      HasDepthEnergy G J Fa za Ka → HasDepthEnergy G J Fb zb Kb →
      (∀ I, Measurable (za I)) → (∀ I, Measurable (zb I)) →
      (∀ I, MemLp (za I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) →
      (∀ I, MemLp (zb I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) →
      (∀ I ∈ S, InScaleBand (quadraticChartAtom A) m (dyadicGridLength G I.1)) →
      ∑ I ∈ S, dyadicGridLength G I.1 *
        ‖separatedLocalForm (dyadicGridLength G I.1) (w I) (quadraticChartAtom A) a b
          (fun y => ψa y * za I y) (fun y => ψb y * zb I y)‖ ≤
        Real.exp (-(m : ℝ)) * bandBracket κ d D J1 m (Real.log (max H (bandLip + 1))) *
          Ka * Kb * Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2) *
          Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) := by
  obtain ⟨D, hD, DJ, hexpand⟩ := chart_depth_expansion c₀ hc
  refine ⟨D, DJ 1, hD, ?_⟩
  intro d H A hd hA hAb m G J S hSJ w hw a b hab ψa ψb hψam hψbm hψa hψb Fa Fb za zb Ka Kb
    hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 hband
  classical
  -- the enlarged complexity and the band precision
  obtain ⟨H', hH'⟩ : ∃ H', H' = max H (bandLip + 1) := ⟨_, rfl⟩
  rw [← hH']
  obtain ⟨Lh, hLh⟩ : ∃ Lh, Lh = Real.log H' := ⟨_, rfl⟩
  rw [← hLh]
  have hH2 : Real.exp 2 ≤ H := hA.lower
  have hH1 : 1 ≤ H := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hHH' : H ≤ H' := by rw [hH']; exact le_max_left _ _
  have hH'1 : 1 ≤ H' := hH1.trans hHH'
  have hLh0 : 0 ≤ Lh := by rw [hLh]; exact Real.log_nonneg hH'1
  have hA' := quadraticChartComplexity_mono hA hHH'
  have hζb : ∀ u, ‖(bandCutoff u : ℂ)‖ ≤ H' := fun u => by
    rw [Complex.norm_real, Real.norm_of_nonneg (bandCutoff_spec.2.1 u)]
    exact (bandCutoff_spec.2.2.1 u).trans hH'1
  have hζL : ∀ u v, ‖(bandCutoff v : ℂ) - (bandCutoff u : ℂ)‖ ≤ H' * |v - u| := by
    intro u v
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    refine (bandLip_spec.2 u v).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    rw [hH']; exact (le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = Real.exp (-((m : ℝ) + 1)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact Real.exp_pos _
  have hlogδ : Real.log (max 1 δ⁻¹) = (m : ℝ) + 1 := by
    rw [hδ, ← Real.exp_neg, neg_neg, max_eq_right (Real.one_le_exp (by positivity)),
      Real.log_exp]
  have hXe : 1 + Real.log H' + Real.log (max 1 δ⁻¹) = bsX m Lh := by
    rw [hlogδ, bsX, hLh]; ring
  -- per-depth chart expansions
  have hdepth : ∀ s : ℤ, ∃ (lam : ℝ) (M : Matrix (Fin d) (Fin d) ℚ)
      (σ : ℕ × (Fin (d + d) → ℤ) → Fin d → ℚ) (coef : ℕ × (Fin (d + d) → ℤ) → ℂ),
      (s ∈ S.image Prod.fst →
        (∀ i j, (rationalHeight (M i j) : ℝ) ≤ bsE D m Lh) ∧
        lam = A.quadratic + ∑ i, ∑ j, A.horizontal i * (M i j : ℝ) * A.horizontal j ∧
        |lam| * dyadicGridLength G s ^ 2 ≤ bsE D m Lh ∧
        (∀ p i, (rationalHeight (σ p i) : ℝ) ≤ bsE D m Lh * (1 + frequencyLength p.2)) ∧
        (∀ t, |t| ≤ 2 * dyadicGridLength G s → HasSum (fun p => coef p *
          quadPhase lam (A.linear + ∑ i, (σ p i : ℝ) * A.horizontal i) t)
            (quadraticChartAtom A t)) ∧
        Summable (fun p => ‖coef p‖) ∧ (∑' p, ‖coef p‖) ≤ bsE D m Lh ∧
        (∀ p, ⌊bsE D m Lh⌋₊ ≤ p.1 → coef p = 0) ∧
        ∀ p, ‖coef p‖ * (1 + frequencyLength p.2) ^ ((d + 1) ^ 2) ≤ bsE1 (DJ 1) m Lh) ∧
      (s ∉ S.image Prod.fst → coef = 0) := by
    intro s
    by_cases hs : s ∈ S.image Prod.fst
    · obtain ⟨I, hIS, hIs⟩ := Finset.mem_image.mp hs
      have hlow : ∃ ξ, δ < bandAmplitude (quadraticChartAtom A) (dyadicGridLength G s) ξ := by
        obtain ⟨ξ, hξ⟩ := (hband I hIS).2
        exact ⟨ξ, by rw [hδ, ← hIs]; exact hξ⟩
      obtain ⟨lam, M, σ, coef, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
        hexpand H' δ (dyadicGridLength G s) A hA' (dyadicGridLength_pos G s) hδ0 hζb hζL hlow
      rw [hXe, ← bsE] at h1 h3 h4 h7 h8
      rw [hXe] at h9
      refine ⟨lam, M, σ, coef, fun _ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩, fun h => absurd hs h⟩
      rw [bsE1]; exact h9
    · exact ⟨0, 0, 0, 0, fun h => absurd h hs, fun _ => rfl⟩
  choose lamf Mf σf coeff hprops hzero using hdepth
  exact band_scale_sum_assembly κ hd A hAb D (DJ 1) m hLh0 G J S hSJ w hw hab hψam hψbm hψa
    hψb hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 (fun I hI ξ => (hband I hI).1 ξ)
    lamf Mf σf coeff hprops hzero

/-- The master size `Ω = (D + J₁ + 1) W^{D+J₁+1}`, `W = 2 + m + Lh`, dominating all the
logarithmic budgets of the band scale sum. -/
noncomputable def bsOmega (D J1 m : ℕ) (Lh : ℝ) : ℝ :=
  ((D + J1 + 1 : ℕ) : ℝ) * (2 + m + Lh) ^ (D + J1 + 1)

section BandBudget
variable {D J1 m : ℕ} {Lh : ℝ}

theorem bsOmega_ge_W (hLh : 0 ≤ Lh) : 2 + (m : ℝ) + Lh ≤ bsOmega D J1 m Lh := by
  unfold bsOmega
  have hW : 1 ≤ 2 + (m : ℝ) + Lh := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have h1 : (1 : ℝ) ≤ ((D + J1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  calc 2 + (m : ℝ) + Lh = 1 * (2 + m + Lh) ^ 1 := by ring
    _ ≤ ((D + J1 + 1 : ℕ) : ℝ) * (2 + m + Lh) ^ (D + J1 + 1) :=
        mul_le_mul h1 (pow_le_pow_right₀ hW (by omega)) (by positivity) (by positivity)

theorem one_le_bsOmega (hLh : 0 ≤ Lh) : 1 ≤ bsOmega D J1 m Lh :=
  le_trans (by linarith [Nat.cast_nonneg (α := ℝ) m]) (bsOmega_ge_W (D := D) (J1 := J1) hLh)

theorem bsOmega_ge_lE (hLh : 0 ≤ Lh) : (D : ℝ) * bsX m Lh ^ D ≤ bsOmega D J1 m Lh := by
  unfold bsOmega bsX
  have hW : 1 ≤ 2 + Lh + (m : ℝ) := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have h1 : (D : ℝ) ≤ ((D + J1 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : D ≤ D + J1 + 1)
  rw [show (2 : ℝ) + m + Lh = 2 + Lh + m by ring]
  exact mul_le_mul h1 (pow_le_pow_right₀ hW (by omega)) (by positivity) (by positivity)

theorem bsOmega_ge_lE1 (hLh : 0 ≤ Lh) : (J1 : ℝ) * bsX m Lh ^ J1 ≤ bsOmega D J1 m Lh := by
  unfold bsOmega bsX
  have hW : 1 ≤ 2 + Lh + (m : ℝ) := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have h1 : (J1 : ℝ) ≤ ((D + J1 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : J1 ≤ D + J1 + 1)
  rw [show (2 : ℝ) + m + Lh = 2 + Lh + m by ring]
  exact mul_le_mul h1 (pow_le_pow_right₀ hW (by omega)) (by positivity) (by positivity)

theorem log_bsE (D m : ℕ) (Lh : ℝ) : Real.log (bsE D m Lh) = D * bsX m Lh ^ D := by
  unfold bsE; exact Real.log_exp _

theorem log_two_bsB1_le (hLh : 0 ≤ Lh) : Real.log (2 * bsB1 D m Lh) ≤ 3 * bsOmega D J1 m Lh := by
  have hE := bsE_one_le D m hLh
  have hΩ := one_le_bsOmega (D := D) (J1 := J1) (m := m) hLh
  have hlE := bsOmega_ge_lE (D := D) (J1 := J1) (m := m) hLh
  unfold bsB1
  have h1 : Real.log (2 * (bsE D m Lh + 2)) ≤ Real.log 6 + Real.log (bsE D m Lh) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by positivity) (by linarith)
  have h6 : Real.log 6 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    rw [h2]
    calc (6 : ℝ) ≤ 2.7 ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h4 2
  rw [log_bsE] at h1
  linarith

theorem log_two_bsE_div_bsEps_le (hLh : 0 ≤ Lh) :
    Real.log (2 * bsE D m Lh / bsEps D m Lh) ≤ 11 * bsOmega D J1 m Lh := by
  have hE := bsE_one_le D m hLh
  have hΩ := one_le_bsOmega (D := D) (J1 := J1) (m := m) hLh
  have hlE := bsOmega_ge_lE (D := D) (J1 := J1) (m := m) hLh
  have hW := bsOmega_ge_W (D := D) (J1 := J1) (m := m) hLh
  have e : 2 * bsE D m Lh / bsEps D m Lh =
      (128 * Real.pi) * bsE D m Lh * bsE D m Lh * Real.exp (m : ℝ) := by
    unfold bsEps
    rw [Real.exp_neg]
    field_simp
    ring
  rw [e, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_exp, log_bsE]
  have hπ : Real.log (128 * Real.pi) ≤ 7 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h1 : (128 : ℝ) * Real.pi ≤ 410 := by nlinarith [Real.pi_lt_d2]
    have h2 : (410 : ℝ) ≤ Real.exp 7 := by
      have := Real.add_one_le_exp (7 : ℝ)
      have h3 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
      have h4 : (2.7 : ℝ) ≤ Real.exp 1 := by
        have := Real.exp_one_gt_d9; linarith
      rw [h3]
      calc (410 : ℝ) ≤ 2.7 ^ 7 := by norm_num
        _ ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) h4 7
    linarith
  have hm : (m : ℝ) ≤ bsOmega D J1 m Lh := by linarith
  linarith

theorem log_le_self_of_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ x :=
  (Real.log_le_sub_one_of_pos hx).trans (by linarith)

/-- A uniform numeric constant bounding `log(128π (3 + 8 C_ζ))`. -/
noncomputable def bsLConst : ℝ := Real.log (128 * Real.pi * (3 + 8 * bandDecay))

theorem bsLConst_nonneg : 0 ≤ bsLConst := by
  unfold bsLConst
  have := bandDecay_spec.1
  exact Real.log_nonneg (by nlinarith [Real.pi_gt_three])

theorem log_two_bsL2_div_bsEps_le (hLh : 0 ≤ Lh) :
    Real.log (2 * bsL2 D m Lh / bsEps D m Lh) ≤ (bsLConst + 4) * bsOmega D J1 m Lh := by
  have hE := bsE_one_le D m hLh
  have hΩ := one_le_bsOmega (D := D) (J1 := J1) (m := m) hLh
  have hlE := bsOmega_ge_lE (D := D) (J1 := J1) (m := m) hLh
  have hW := bsOmega_ge_W (D := D) (J1 := J1) (m := m) hLh
  have hdec := bandDecay_spec.1
  have hem : 1 ≤ Real.exp (m : ℝ) := Real.one_le_exp (Nat.cast_nonneg m)
  have hL : bsL2 D m Lh ≤ (3 + 8 * bandDecay) * bsE D m Lh * Real.exp (m : ℝ) := by
    unfold bsL2
    have : 1 ≤ bsE D m Lh * Real.exp (m : ℝ) := one_le_mul_of_one_le_of_one_le hE hem
    nlinarith
  have e : 2 * ((3 + 8 * bandDecay) * bsE D m Lh * Real.exp (m : ℝ)) / bsEps D m Lh =
      (128 * Real.pi * (3 + 8 * bandDecay)) * bsE D m Lh * Real.exp (m : ℝ) * bsE D m Lh *
        Real.exp (m : ℝ) := by
    unfold bsEps
    rw [Real.exp_neg]
    field_simp
    ring
  have hL3 := three_le_bsL2 D m hLh
  have hε := bsEps_pos D m hLh
  have hmono : Real.log (2 * bsL2 D m Lh / bsEps D m Lh) ≤
      Real.log (2 * ((3 + 8 * bandDecay) * bsE D m Lh * Real.exp (m : ℝ)) / bsEps D m Lh) :=
    Real.log_le_log (by positivity) (by gcongr)
  refine hmono.trans ?_
  rw [e, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul
    (by positivity) (by positivity), Real.log_exp, log_bsE]
  have hc := bsLConst_nonneg
  unfold bsLConst at hc ⊢
  have hm : (m : ℝ) ≤ bsOmega D J1 m Lh := by linarith
  nlinarith only [hLh, hlE, hW, hc]

theorem bsOmega_ge_d {d : ℕ} (hLh : 0 ≤ Lh) (hdL : (d : ℝ) ≤ Lh) :
    (d : ℝ) ≤ bsOmega D J1 m Lh := by
  have hW := bsOmega_ge_W (D := D) (J1 := J1) (m := m) hLh
  have := Nat.cast_nonneg (α := ℝ) m
  linarith

theorem log_le_two_of_le_six {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 6) : Real.log x ≤ 2 := by
  rw [Real.log_le_iff_le_exp hx0]
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have h4 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  rw [h2]
  calc x ≤ 2.7 ^ 2 := by linarith
    _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h4 2

/-- The explicit constant controlling `log(1 + C_T)`. -/
noncomputable def bsCCT (κ : LocalKernelClass) : ℝ :=
  linearScaleConst κ * (24 * (2 * Real.pi) ^ 2 * (4 * 32) * 2560) +
    localKernelSupBound κ * (2 * Real.pi * 128 * 81 * 3) + 1

theorem bsCCT_nonneg (κ : LocalKernelClass) : 0 ≤ bsCCT κ := by
  unfold bsCCT
  have := linearScaleConst_nonneg κ
  have := localKernelSupBound_nonneg κ
  positivity

theorem bsCT_add_one_le (κ : LocalKernelClass) {d : ℕ} (hLh : 0 ≤ Lh) (hdL : (d : ℝ) ≤ Lh) :
    bsCT κ d D m Lh + 1 ≤ bsCCT κ * bsOmega D J1 m Lh ^ 9 * bsE D m Lh := by
  have hE := bsE_one_le D m hLh
  have hΩ := one_le_bsOmega (D := D) (J1 := J1) (m := m) hLh
  have hlE := bsOmega_ge_lE (D := D) (J1 := J1) (m := m) hLh
  have hd := bsOmega_ge_d (D := D) (J1 := J1) (m := m) hLh hdL
  have hlin := linearScaleConst_nonneg κ
  have hC := localKernelSupBound_nonneg κ
  set Ω := bsOmega D J1 m Lh
  have h24 : Real.log 24 ≤ 4 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    rw [h4]
    calc (24 : ℝ) ≤ 2.7 ^ 4 := by norm_num
      _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) h27 4
  have hl4 : Real.log 4 ≤ 2 := log_le_two_of_le_six (by norm_num) (by norm_num)
  have hl4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hl24' : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
  -- the multiplicity part
  have hα : bsAlpha d D m Lh ≤ 24 * (2 * Real.pi) ^ 2 * (4 * 32) * 2560 * Ω ^ 5 := by
    unfold bsAlpha
    have hd3 : (((d + 1 : ℕ) : ℝ) + 1) + 1 ≤ 4 * Ω := by push_cast; linarith
    have hd30 : 0 ≤ (((d + 1 : ℕ) : ℝ) + 1) + 1 := by positivity
    have hlog : Real.log 24 + 2 * (D * bsX m Lh ^ D) + 2 + Real.log 4 ≤ 10 * Ω := by linarith
    have hlog0 : 0 ≤ Real.log 24 + 2 * (D * bsX m Lh ^ D) + 2 + Real.log 4 := by
      have : 0 ≤ (D : ℝ) * bsX m Lh ^ D := by unfold bsX; positivity
      linarith
    have hp : ((((d + 1 : ℕ) : ℝ) + 1) + 1) ^ 4 ≤ (4 * Ω) ^ 4 := pow_le_pow_left₀ hd30 hd3 4
    calc 24 * (2 * Real.pi) ^ 2 * (4 * (32 * ((((d + 1 : ℕ) : ℝ) + 1) + 1) ^ 4 *
          (Real.log 24 + 2 * (D * bsX m Lh ^ D) + 2 + Real.log 4)))
        = 24 * (2 * Real.pi) ^ 2 * (4 * 32) * (((((d + 1 : ℕ) : ℝ) + 1) + 1) ^ 4 *
          (Real.log 24 + 2 * (D * bsX m Lh ^ D) + 2 + Real.log 4)) := by ring
      _ ≤ 24 * (2 * Real.pi) ^ 2 * (4 * 32) * ((4 * Ω) ^ 4 * (10 * Ω)) := by gcongr
      _ = 24 * (2 * Real.pi) ^ 2 * (4 * 32) * 2560 * Ω ^ 5 := by ring
  -- the quadratic part
  have hΛ : bsLam d D m Lh ≤ 2 * Real.pi * 128 * 81 * 3 * Ω ^ 9 * bsE D m Lh := by
    unfold bsLam
    have hdd : (((d * d + 1 : ℕ) : ℝ) + 1) ≤ 3 * Ω ^ 2 := by
      push_cast
      have : (d : ℝ) * d ≤ Ω ^ 2 := by
        rw [sq]; exact mul_le_mul hd hd (Nat.cast_nonneg _) (by linarith)
      nlinarith only [hΩ, hd]
    have hdd0 : 0 ≤ (((d * d + 1 : ℕ) : ℝ) + 1) := by positivity
    have hlg : Real.log (2 * (bsE D m Lh + 2)) ≤ 3 * Ω := by
      have h1 : Real.log (2 * (bsE D m Lh + 2)) ≤ Real.log 6 + Real.log (bsE D m Lh) := by
        rw [← Real.log_mul (by norm_num) (by linarith)]
        exact Real.log_le_log (by positivity) (by linarith)
      have h6 : Real.log 6 ≤ 2 := log_le_two_of_le_six (by norm_num) le_rfl
      rw [log_bsE] at h1
      linarith
    have hlg0 : 0 ≤ Real.log (2 * (bsE D m Lh + 2)) := Real.log_nonneg (by linarith)
    have hp : (((d * d + 1 : ℕ) : ℝ) + 1) ^ 4 ≤ (3 * Ω ^ 2) ^ 4 := pow_le_pow_left₀ hdd0 hdd 4
    calc 2 * Real.pi * (128 * (((d * d + 1 : ℕ) : ℝ) + 1) ^ 4 *
          Real.log (2 * (bsE D m Lh + 2)) * bsE D m Lh)
        = 2 * Real.pi * 128 * ((((d * d + 1 : ℕ) : ℝ) + 1) ^ 4 *
          Real.log (2 * (bsE D m Lh + 2))) * bsE D m Lh := by ring
      _ ≤ 2 * Real.pi * 128 * ((3 * Ω ^ 2) ^ 4 * (3 * Ω)) * bsE D m Lh := by gcongr
      _ = 2 * Real.pi * 128 * 81 * 3 * Ω ^ 9 * bsE D m Lh := by ring
  unfold bsCT bsCCT
  have hΩ5 : Ω ^ 5 ≤ Ω ^ 9 := pow_le_pow_right₀ hΩ (by norm_num)
  have hΩ9 : 1 ≤ Ω ^ 9 := one_le_pow₀ hΩ
  have h1 : linearScaleConst κ * bsAlpha d D m Lh ≤
      linearScaleConst κ * (24 * (2 * Real.pi) ^ 2 * (4 * 32) * 2560) * Ω ^ 9 * bsE D m Lh := by
    have : 24 * (2 * Real.pi) ^ 2 * (4 * 32) * 2560 * Ω ^ 5 ≤
        24 * (2 * Real.pi) ^ 2 * (4 * 32) * 2560 * Ω ^ 9 * bsE D m Lh := by
      have hc : 0 ≤ 24 * (2 * Real.pi) ^ 2 * (4 * 32) * 2560 := by positivity
      calc 24 * (2 * Real.pi) ^ 2 * (4 * 32) * 2560 * Ω ^ 5
          ≤ 24 * (2 * Real.pi) ^ 2 * (4 * 32) * 2560 * Ω ^ 9 :=
            mul_le_mul_of_nonneg_left hΩ5 hc
        _ ≤ 24 * (2 * Real.pi) ^ 2 * (4 * 32) * 2560 * Ω ^ 9 * bsE D m Lh :=
            le_mul_of_one_le_right (by positivity) hE
    calc linearScaleConst κ * bsAlpha d D m Lh
        ≤ linearScaleConst κ * (24 * (2 * Real.pi) ^ 2 * (4 * 32) * 2560 * Ω ^ 5) :=
          mul_le_mul_of_nonneg_left hα hlin
      _ ≤ linearScaleConst κ * (24 * (2 * Real.pi) ^ 2 * (4 * 32) * 2560 * Ω ^ 9 * bsE D m Lh) :=
          mul_le_mul_of_nonneg_left this hlin
      _ = _ := by ring
  have h2 : localKernelSupBound κ * bsLam d D m Lh ≤
      localKernelSupBound κ * (2 * Real.pi * 128 * 81 * 3) * Ω ^ 9 * bsE D m Lh := by
    calc localKernelSupBound κ * bsLam d D m Lh
        ≤ localKernelSupBound κ * (2 * Real.pi * 128 * 81 * 3 * Ω ^ 9 * bsE D m Lh) :=
          mul_le_mul_of_nonneg_left hΛ hC
      _ = _ := by ring
  have h3 : (1 : ℝ) ≤ Ω ^ 9 * bsE D m Lh := one_le_mul_of_one_le_of_one_le hΩ9 hE
  calc linearScaleConst κ * bsAlpha d D m Lh + localKernelSupBound κ * bsLam d D m Lh + 1
      ≤ linearScaleConst κ * (24 * (2 * Real.pi) ^ 2 * (4 * 32) * 2560) * Ω ^ 9 * bsE D m Lh +
        localKernelSupBound κ * (2 * Real.pi * 128 * 81 * 3) * Ω ^ 9 * bsE D m Lh +
        Ω ^ 9 * bsE D m Lh := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

theorem log_le_of_le_exp_one_pow {x : ℝ} {n : ℕ} (hx0 : 0 < x) (hx : x ≤ 2.7 ^ n) :
    Real.log x ≤ n := by
  rw [Real.log_le_iff_le_exp hx0]
  have h1 : Real.exp (n : ℝ) = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul]; norm_num
  have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  rw [h1]
  exact hx.trans (pow_le_pow_left₀ (by norm_num) h27 n)

theorem one_le_bsCCT (κ : LocalKernelClass) : 1 ≤ bsCCT κ := by
  unfold bsCCT
  have := linearScaleConst_nonneg κ
  have := localKernelSupBound_nonneg κ
  have h1 : 0 ≤ linearScaleConst κ * (24 * (2 * Real.pi) ^ 2 * (4 * 32) * 2560) := by positivity
  have h2 : 0 ≤ localKernelSupBound κ * (2 * Real.pi * 128 * 81 * 3) := by positivity
  linarith

theorem bsK0_le (κ : LocalKernelClass) {d : ℕ} (hLh : 0 ≤ Lh) (hdL : (d : ℝ) ≤ Lh) :
    (bsK0 κ d D J1 m Lh : ℝ) ≤ (2 * bsCCT κ + 41) * bsOmega D J1 m Lh ^ 9 := by
  have hE := bsE_one_le D m hLh
  have hΩ := one_le_bsOmega (D := D) (J1 := J1) (m := m) hLh
  have hlE := bsOmega_ge_lE (D := D) (J1 := J1) (m := m) hLh
  have hlE1 := bsOmega_ge_lE1 (D := D) (J1 := J1) (m := m) hLh
  have hW := bsOmega_ge_W (D := D) (J1 := J1) (m := m) hLh
  have hd := bsOmega_ge_d (D := D) (J1 := J1) (m := m) hLh hdL
  have hCT := bsCT_add_one_le (D := D) (J1 := J1) (m := m) κ hLh hdL
  have hCCT := one_le_bsCCT κ
  have hCT0 := bsCT_nonneg κ d D m hLh
  set Ω := bsOmega D J1 m Lh
  have hΩ9 : 1 ≤ Ω ^ 9 := one_le_pow₀ hΩ
  have hΩ19 : Ω ≤ Ω ^ 9 := by
    calc Ω = Ω ^ 1 := (pow_one _).symm
      _ ≤ Ω ^ 9 := pow_le_pow_right₀ hΩ (by norm_num)
  have hΩ29 : Ω ^ 2 ≤ Ω ^ 9 := pow_le_pow_right₀ hΩ (by norm_num)
  have hpi1 : 1 ≤ 2 * Real.pi := by nlinarith only [Real.pi_gt_three]
  have hE1 : 1 ≤ bsE1 J1 m Lh := Real.one_le_exp (by unfold bsX; positivity)
  have h7 : (1 : ℝ) ≤ 7 ^ (d + d) := one_le_pow₀ (by norm_num)
  have h2π : 1 ≤ (2 * Real.pi) ^ ((d + 1) ^ 2) := one_le_pow₀ hpi1
  have hem : 1 ≤ Real.exp (m : ℝ) := Real.one_le_exp (Nat.cast_nonneg m)
  set Z := 16 * (bsE D m Lh + 1) * bsE1 J1 m Lh * (bsCT κ d D m Lh + 1) *
    7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2) * Real.exp (m : ℝ) with hZ
  have hZ1 : 1 ≤ Z := by
    rw [hZ]
    have h5 : (1 : ℝ) ≤ 16 * (bsE D m Lh + 1) := by linarith
    have h6 : (1 : ℝ) ≤ bsCT κ d D m Lh + 1 := by linarith
    calc (1 : ℝ) = 1 * 1 * 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have hlogZ : Real.log Z ≤ (bsCCT κ + 20) * Ω ^ 9 := by
    rw [hZ]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul
      (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow,
      Real.log_pow]
    have l16 : Real.log 16 ≤ 3 := log_le_of_le_exp_one_pow (by norm_num) (by norm_num)
    have lEp1 : Real.log (bsE D m Lh + 1) ≤ 1 + Ω := by
      have h := Real.log_le_log (by positivity) (show bsE D m Lh + 1 ≤ 2 * bsE D m Lh by linarith)
      rw [Real.log_mul (by norm_num) (by positivity), log_bsE] at h
      have l2 : Real.log 2 ≤ 1 := by
        have := log_le_of_le_exp_one_pow (x := 2) (n := 1) (by norm_num) (by norm_num)
        simpa using this
      linarith
    have lE1' : Real.log (bsE1 J1 m Lh) ≤ Ω := by unfold bsE1; rw [Real.log_exp]; exact hlE1
    have lCT : Real.log (bsCT κ d D m Lh + 1) ≤ bsCCT κ * Ω ^ 9 + Ω := by
      have h0 : 0 < bsCCT κ * Ω ^ 9 := by positivity
      have h := Real.log_le_log (by linarith) hCT
      rw [Real.log_mul h0.ne' (by positivity), log_bsE] at h
      have := log_le_self_of_pos h0
      linarith
    have l7 : Real.log 7 ≤ 2 := log_le_of_le_exp_one_pow (by norm_num) (by norm_num)
    have l70 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
    have l2pi : Real.log (2 * Real.pi) ≤ 2 :=
      log_le_of_le_exp_one_pow (by positivity) (by nlinarith only [Real.pi_lt_d2])
    have l2pi0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg hpi1
    have hdd : ((d + d : ℕ) : ℝ) * Real.log 7 ≤ 4 * Ω := by
      push_cast
      calc ((d : ℝ) + d) * Real.log 7 ≤ ((d : ℝ) + d) * 2 :=
            mul_le_mul_of_nonneg_left l7 (by positivity)
        _ ≤ 4 * Ω := by linarith
    have hd1 : (((d + 1) ^ 2 : ℕ) : ℝ) * Real.log (2 * Real.pi) ≤ 8 * Ω ^ 2 := by
      push_cast
      have h1 : ((d : ℝ) + 1) ^ 2 ≤ (2 * Ω) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      calc ((d : ℝ) + 1) ^ 2 * Real.log (2 * Real.pi) ≤ (2 * Ω) ^ 2 * 2 :=
            mul_le_mul h1 l2pi l2pi0 (by positivity)
        _ = 8 * Ω ^ 2 := by ring
    have hm : (m : ℝ) ≤ Ω := by linarith [Nat.cast_nonneg (α := ℝ) m]
    have hsum : Real.log 16 + Real.log (bsE D m Lh + 1) + Real.log (bsE1 J1 m Lh) +
        Real.log (bsCT κ d D m Lh + 1) + ((d + d : ℕ) : ℝ) * Real.log 7 +
        (((d + 1) ^ 2 : ℕ) : ℝ) * Real.log (2 * Real.pi) + (m : ℝ) ≤
        3 + (1 + Ω) + Ω + (bsCCT κ * Ω ^ 9 + Ω) + 4 * Ω + 8 * Ω ^ 2 + Ω := by
      linarith
    have hfin : 3 + (1 + Ω) + Ω + (bsCCT κ * Ω ^ 9 + Ω) + 4 * Ω + 8 * Ω ^ 2 + Ω ≤
        (bsCCT κ + 20) * Ω ^ 9 := by nlinarith only [hΩ, hΩ29]
    exact hsum.trans hfin
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlogZ0 : 0 ≤ Real.log Z := Real.log_nonneg hZ1
  have hK : (bsK0 κ d D J1 m Lh : ℝ) ≤ Real.logb 2 Z + 1 := by
    unfold bsK0
    rw [← hZ]
    exact (Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hZ1)).le
  have hlogb : Real.logb 2 Z ≤ 2 * Real.log Z := by
    unfold Real.logb
    rw [div_le_iff₀ (by linarith)]
    nlinarith only [hl2, hlogZ0]
  calc (bsK0 κ d D J1 m Lh : ℝ) ≤ 2 * Real.log Z + 1 := by linarith
    _ ≤ 2 * ((bsCCT κ + 20) * Ω ^ 9) + Ω ^ 9 := by linarith
    _ = (2 * bsCCT κ + 41) * Ω ^ 9 := by ring

theorem log_bsBσ_le (κ : LocalKernelClass) {d : ℕ} (hLh : 0 ≤ Lh) (hdL : (d : ℝ) ≤ Lh) :
    Real.log (bsBσ κ d D J1 m Lh) ≤ (2 * bsCCT κ + 42) * bsOmega D J1 m Lh ^ 9 := by
  have hE := bsE_one_le D m hLh
  have hΩ := one_le_bsOmega (D := D) (J1 := J1) (m := m) hLh
  have hlE := bsOmega_ge_lE (D := D) (J1 := J1) (m := m) hLh
  have hK := bsK0_le (D := D) (J1 := J1) (m := m) κ hLh hdL
  have hΩ9 : bsOmega D J1 m Lh ≤ bsOmega D J1 m Lh ^ 9 := by
    calc bsOmega D J1 m Lh = bsOmega D J1 m Lh ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hΩ (by norm_num)
  unfold bsBσ
  rw [Real.log_mul (by positivity) (by positivity), log_bsE, Real.log_pow]
  have l2 : Real.log 2 ≤ 1 := by
    have := log_le_of_le_exp_one_pow (x := 2) (n := 1) (by norm_num) (by norm_num)
    simpa using this
  have l20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK0 := Nat.cast_nonneg (α := ℝ) (bsK0 κ d D J1 m Lh)
  have : ((bsK0 κ d D J1 m Lh : ℕ) : ℝ) * Real.log 2 ≤ (bsK0 κ d D J1 m Lh : ℝ) := by
    calc ((bsK0 κ d D J1 m Lh : ℕ) : ℝ) * Real.log 2 ≤ ((bsK0 κ d D J1 m Lh : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left l2 hK0
      _ = _ := mul_one _
  linarith

theorem log_two_bsB2_le (κ : LocalKernelClass) {d : ℕ} (hLh : 0 ≤ Lh) (hdL : (d : ℝ) ≤ Lh) :
    Real.log (2 * bsB2 κ d D J1 m Lh) ≤ (8 * bsCCT κ + 171) * bsOmega D J1 m Lh ^ 9 := by
  have hB := one_le_bsBσ κ d D J1 m hLh
  have hlB := log_bsBσ_le (D := D) (J1 := J1) (m := m) κ hLh hdL
  have hΩ := one_le_bsOmega (D := D) (J1 := J1) (m := m) hLh
  have hΩ9 : 1 ≤ bsOmega D J1 m Lh ^ 9 := one_le_pow₀ hΩ
  have hB4 : 1 ≤ bsBσ κ d D J1 m Lh ^ 4 := one_le_pow₀ hB
  unfold bsB2
  have h1 : Real.log (2 * (3 * bsBσ κ d D J1 m Lh ^ 4 + 2)) ≤
      Real.log (10 * bsBσ κ d D J1 m Lh ^ 4) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (x := (10 : ℝ)) (y := bsBσ κ d D J1 m Lh ^ 4) (by norm_num)
    (by positivity), Real.log_pow] at h1
  have l10 : Real.log 10 ≤ 3 := log_le_of_le_exp_one_pow (by norm_num) (by norm_num)
  push_cast at h1
  linarith

theorem log_two_bsBc_le (κ : LocalKernelClass) {d : ℕ} (hLh : 0 ≤ Lh) (hdL : (d : ℝ) ≤ Lh) :
    Real.log (2 * bsBc κ d D J1 m Lh) ≤ (4 * bsCCT κ + 88) * bsOmega D J1 m Lh ^ 9 := by
  have hB := one_le_bsBσ κ d D J1 m hLh
  have hlB := log_bsBσ_le (D := D) (J1 := J1) (m := m) κ hLh hdL
  have hΩ := one_le_bsOmega (D := D) (J1 := J1) (m := m) hLh
  have hΩ9 : 1 ≤ bsOmega D J1 m Lh ^ 9 := one_le_pow₀ hΩ
  have hB2 : 1 ≤ bsBσ κ d D J1 m Lh ^ 2 := one_le_pow₀ hB
  unfold bsBc
  have h1 : Real.log (2 * (6 * bsBσ κ d D J1 m Lh ^ 2 + 6)) ≤
      Real.log (24 * bsBσ κ d D J1 m Lh ^ 2) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (x := (24 : ℝ)) (y := bsBσ κ d D J1 m Lh ^ 2) (by norm_num)
    (by positivity), Real.log_pow] at h1
  have l24 : Real.log 24 ≤ 4 := log_le_of_le_exp_one_pow (by norm_num) (by norm_num)
  push_cast at h1
  linarith

theorem bsOmega_pow_mono (hLh : 0 ≤ Lh) {a b : ℕ} (hab : a ≤ b) :
    bsOmega D J1 m Lh ^ a ≤ bsOmega D J1 m Lh ^ b :=
  pow_le_pow_right₀ (one_le_bsOmega hLh) hab

theorem bracket_d1_le {d : ℕ} (hLh : 0 ≤ Lh) (hdL : (d : ℝ) ≤ Lh) :
    ((d : ℝ) + 1) ^ 4 ≤ 16 * bsOmega D J1 m Lh ^ 4 := by
  have hΩ := one_le_bsOmega (D := D) (J1 := J1) (m := m) hLh
  have hd := bsOmega_ge_d (D := D) (J1 := J1) (m := m) hLh hdL
  have : (d : ℝ) + 1 ≤ 2 * bsOmega D J1 m Lh := by linarith
  calc ((d : ℝ) + 1) ^ 4 ≤ (2 * bsOmega D J1 m Lh) ^ 4 := pow_le_pow_left₀ (by positivity) this 4
    _ = 16 * bsOmega D J1 m Lh ^ 4 := by ring

theorem bracket_dd_le {d : ℕ} (hLh : 0 ≤ Lh) (hdL : (d : ℝ) ≤ Lh) :
    (((d * d + 1 : ℕ) : ℝ) + 1) ^ 4 ≤ 81 * bsOmega D J1 m Lh ^ 8 := by
  have hΩ := one_le_bsOmega (D := D) (J1 := J1) (m := m) hLh
  have hd := bsOmega_ge_d (D := D) (J1 := J1) (m := m) hLh hdL
  have h : ((d * d + 1 : ℕ) : ℝ) + 1 ≤ 3 * bsOmega D J1 m Lh ^ 2 := by
    push_cast
    have h1 : (d : ℝ) * d ≤ bsOmega D J1 m Lh ^ 2 := by
      rw [sq]; exact mul_le_mul hd hd (Nat.cast_nonneg _) (by linarith)
    have h2 : 1 ≤ bsOmega D J1 m Lh ^ 2 := one_le_pow₀ hΩ
    linarith
  calc (((d * d + 1 : ℕ) : ℝ) + 1) ^ 4 ≤ (3 * bsOmega D J1 m Lh ^ 2) ^ 4 :=
        pow_le_pow_left₀ (by positivity) h 4
    _ = 81 * bsOmega D J1 m Lh ^ 8 := by ring

theorem bracket_t1_le (κ : LocalKernelClass) {d : ℕ} (hLh : 0 ≤ Lh) (hdL : (d : ℝ) ≤ Lh) :
    32 * ((d : ℝ) + 1) ^ 4 *
      (Real.log (2 * bsB2 κ d D J1 m Lh) + Real.log (2 * bsL2 D m Lh / bsEps D m Lh)) ≤
      512 * (8 * bsCCT κ + 175 + bsLConst) * bsOmega D J1 m Lh ^ 13 := by
  have hΩ := one_le_bsOmega (D := D) (J1 := J1) (m := m) hLh
  have hB2 := log_two_bsB2_le (D := D) (J1 := J1) (m := m) κ hLh hdL
  have hLε := log_two_bsL2_div_bsEps_le (D := D) (J1 := J1) (m := m) hLh
  have hd1 := bracket_d1_le (D := D) (J1 := J1) (m := m) hLh hdL
  have hbL := bsLConst_nonneg
  have hc := one_le_bsCCT κ
  have h19 := bsOmega_pow_mono (D := D) (J1 := J1) (m := m) hLh (show 1 ≤ 9 by norm_num)
  rw [pow_one] at h19
  have hp : (bsLConst + 4) * bsOmega D J1 m Lh ≤ (bsLConst + 4) * bsOmega D J1 m Lh ^ 9 :=
    mul_le_mul_of_nonneg_left h19 (by linarith)
  have hs : Real.log (2 * bsB2 κ d D J1 m Lh) + Real.log (2 * bsL2 D m Lh / bsEps D m Lh) ≤
      (8 * bsCCT κ + 175 + bsLConst) * bsOmega D J1 m Lh ^ 9 := by linarith
  have hs0 : 0 ≤ Real.log (2 * bsB2 κ d D J1 m Lh) +
      Real.log (2 * bsL2 D m Lh / bsEps D m Lh) := by
    have h1 := Real.log_nonneg (show (1 : ℝ) ≤ 2 * bsB2 κ d D J1 m Lh by
      have := two_le_bsB2 κ d D J1 m hLh; linarith)
    have h2 : (1 : ℝ) ≤ 2 * bsL2 D m Lh / bsEps D m Lh := by
      rw [le_div_iff₀ (bsEps_pos D m hLh)]
      have := three_le_bsL2 D m hLh; have := bsEps_le_one D m hLh; linarith
    have := Real.log_nonneg h2
    linarith
  calc 32 * ((d : ℝ) + 1) ^ 4 *
        (Real.log (2 * bsB2 κ d D J1 m Lh) + Real.log (2 * bsL2 D m Lh / bsEps D m Lh))
      ≤ 32 * (16 * bsOmega D J1 m Lh ^ 4) *
        ((8 * bsCCT κ + 175 + bsLConst) * bsOmega D J1 m Lh ^ 9) := by gcongr
    _ = 512 * (8 * bsCCT κ + 175 + bsLConst) * bsOmega D J1 m Lh ^ 13 := by ring

theorem bracket_t2_le {d : ℕ} (hLh : 0 ≤ Lh) (hdL : (d : ℝ) ≤ Lh) :
    32 * (((d * d + 1 : ℕ) : ℝ) + 1) ^ 4 *
      (Real.log (2 * bsB1 D m Lh) + Real.log (2 * bsE D m Lh / bsEps D m Lh)) ≤
      36288 * bsOmega D J1 m Lh ^ 13 := by
  have hB1 := log_two_bsB1_le (D := D) (J1 := J1) (m := m) hLh
  have hEε := log_two_bsE_div_bsEps_le (D := D) (J1 := J1) (m := m) hLh
  have hdd := bracket_dd_le (D := D) (J1 := J1) (m := m) hLh hdL
  have h913 := bsOmega_pow_mono (D := D) (J1 := J1) (m := m) hLh (show 9 ≤ 13 by norm_num)
  have hs0 : 0 ≤ Real.log (2 * bsB1 D m Lh) + Real.log (2 * bsE D m Lh / bsEps D m Lh) := by
    have h1 := Real.log_nonneg (show (1 : ℝ) ≤ 2 * bsB1 D m Lh by
      have := two_le_bsB1 D m hLh; linarith)
    have h2 : (1 : ℝ) ≤ 2 * bsE D m Lh / bsEps D m Lh := by
      rw [le_div_iff₀ (bsEps_pos D m hLh)]
      have := bsE_one_le D m hLh; have := bsEps_le_one D m hLh; linarith
    have := Real.log_nonneg h2
    linarith
  have hs : Real.log (2 * bsB1 D m Lh) + Real.log (2 * bsE D m Lh / bsEps D m Lh) ≤
      14 * bsOmega D J1 m Lh := by linarith
  calc 32 * (((d * d + 1 : ℕ) : ℝ) + 1) ^ 4 *
        (Real.log (2 * bsB1 D m Lh) + Real.log (2 * bsE D m Lh / bsEps D m Lh))
      ≤ 32 * (81 * bsOmega D J1 m Lh ^ 8) * (14 * bsOmega D J1 m Lh) := by gcongr
    _ = 36288 * bsOmega D J1 m Lh ^ 9 := by ring
    _ ≤ 36288 * bsOmega D J1 m Lh ^ 13 := by linarith

theorem bracket_t3_le (κ : LocalKernelClass) {d : ℕ} (hLh : 0 ≤ Lh) (hdL : (d : ℝ) ≤ Lh) :
    clumpMultiplicity (d + 1) (bsBc κ d D J1 m Lh) ≤
      24 * (2 * Real.pi) ^ 2 * 32768 * (4 * bsCCT κ + 90) * bsOmega D J1 m Lh ^ 13 := by
  have hΩ := one_le_bsOmega (D := D) (J1 := J1) (m := m) hLh
  have hd := bsOmega_ge_d (D := D) (J1 := J1) (m := m) hLh hdL
  have hBc := log_two_bsBc_le (D := D) (J1 := J1) (m := m) κ hLh hdL
  have h09 : 1 ≤ bsOmega D J1 m Lh ^ 9 := one_le_pow₀ hΩ
  have hd3 : (((d + 1 + 1 : ℕ) : ℝ) + 1) ^ 4 ≤ 256 * bsOmega D J1 m Lh ^ 4 := by
    have : ((d + 1 + 1 : ℕ) : ℝ) + 1 ≤ 4 * bsOmega D J1 m Lh := by push_cast; linarith
    calc (((d + 1 + 1 : ℕ) : ℝ) + 1) ^ 4 ≤ (4 * bsOmega D J1 m Lh) ^ 4 :=
          pow_le_pow_left₀ (by positivity) this 4
      _ = 256 * bsOmega D J1 m Lh ^ 4 := by ring
  unfold clumpMultiplicity heightBandConst
  have hl4 : Real.log 4 ≤ 2 := log_le_two_of_le_six (by norm_num) (by norm_num)
  have hs0 : 0 ≤ Real.log (2 * bsBc κ d D J1 m Lh) + Real.log 4 := by
    have h1 := Real.log_nonneg (show (1 : ℝ) ≤ 2 * bsBc κ d D J1 m Lh by
      have := two_le_bsBc κ d D J1 m Lh; linarith)
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith
  have hs : Real.log (2 * bsBc κ d D J1 m Lh) + Real.log 4 ≤
      (4 * bsCCT κ + 90) * bsOmega D J1 m Lh ^ 9 := by linarith
  calc 24 * (2 * Real.pi) ^ 2 * (4 * (32 * (((d + 1 + 1 : ℕ) : ℝ) + 1) ^ 4 *
        (Real.log (2 * bsBc κ d D J1 m Lh) + Real.log 4)))
      = 24 * (2 * Real.pi) ^ 2 * 128 * ((((d + 1 + 1 : ℕ) : ℝ) + 1) ^ 4 *
        (Real.log (2 * bsBc κ d D J1 m Lh) + Real.log 4)) := by ring
    _ ≤ 24 * (2 * Real.pi) ^ 2 * 128 * ((256 * bsOmega D J1 m Lh ^ 4) *
        ((4 * bsCCT κ + 90) * bsOmega D J1 m Lh ^ 9)) := by gcongr
    _ = 24 * (2 * Real.pi) ^ 2 * 32768 * (4 * bsCCT κ + 90) * bsOmega D J1 m Lh ^ 13 := by
        ring

theorem bracket_t4_le (κ : LocalKernelClass) {d : ℕ} (hLh : 0 ≤ Lh) (hdL : (d : ℝ) ≤ Lh) :
    (((d * d + 1 : ℕ) : ℝ) + 1) ^ 4 * Real.log (2 * bsB1 D m Lh) +
      ((d : ℝ) + 1) ^ 4 * Real.log (2 * bsB2 κ d D J1 m Lh) ≤
      (243 + 16 * (8 * bsCCT κ + 171)) * bsOmega D J1 m Lh ^ 13 := by
  have hB1 := log_two_bsB1_le (D := D) (J1 := J1) (m := m) hLh
  have hB2 := log_two_bsB2_le (D := D) (J1 := J1) (m := m) κ hLh hdL
  have hd1 := bracket_d1_le (D := D) (J1 := J1) (m := m) hLh hdL
  have hdd := bracket_dd_le (D := D) (J1 := J1) (m := m) hLh hdL
  have h913 := bsOmega_pow_mono (D := D) (J1 := J1) (m := m) hLh (show 9 ≤ 13 by norm_num)
  have hc := one_le_bsCCT κ
  have hl1 : 0 ≤ Real.log (2 * bsB1 D m Lh) := Real.log_nonneg (by
    have := two_le_bsB1 D m hLh; linarith)
  have hl2 : 0 ≤ Real.log (2 * bsB2 κ d D J1 m Lh) := Real.log_nonneg (by
    have := two_le_bsB2 κ d D J1 m hLh; linarith)
  have a1 : (((d * d + 1 : ℕ) : ℝ) + 1) ^ 4 * Real.log (2 * bsB1 D m Lh) ≤
      243 * bsOmega D J1 m Lh ^ 13 := by
    calc (((d * d + 1 : ℕ) : ℝ) + 1) ^ 4 * Real.log (2 * bsB1 D m Lh)
        ≤ (81 * bsOmega D J1 m Lh ^ 8) * (3 * bsOmega D J1 m Lh) :=
          mul_le_mul hdd hB1 hl1 (by positivity)
      _ = 243 * bsOmega D J1 m Lh ^ 9 := by ring
      _ ≤ 243 * bsOmega D J1 m Lh ^ 13 := by linarith
  have a2 : ((d : ℝ) + 1) ^ 4 * Real.log (2 * bsB2 κ d D J1 m Lh) ≤
      16 * (8 * bsCCT κ + 171) * bsOmega D J1 m Lh ^ 13 := by
    calc ((d : ℝ) + 1) ^ 4 * Real.log (2 * bsB2 κ d D J1 m Lh)
        ≤ (16 * bsOmega D J1 m Lh ^ 4) * ((8 * bsCCT κ + 171) * bsOmega D J1 m Lh ^ 9) :=
          mul_le_mul hd1 hB2 hl2 (by positivity)
      _ = 16 * (8 * bsCCT κ + 171) * bsOmega D J1 m Lh ^ 13 := by ring
  calc _ ≤ 243 * bsOmega D J1 m Lh ^ 13 + 16 * (8 * bsCCT κ + 171) * bsOmega D J1 m Lh ^ 13 :=
        add_le_add a1 a2
    _ = _ := by ring

/-- The explicit constant of the final polynomial bound of the band bracket. -/
noncomputable def bsKfin (κ : LocalKernelClass) : ℝ :=
  kernelFourierConst κ * (512 * (8 * bsCCT κ + 175 + bsLConst) + 36288) +
    linearScaleConst κ * (24 * (2 * Real.pi) ^ 2 * 32768 * (4 * bsCCT κ + 90)) +
    4 * localKernelSupBound κ * (243 + 16 * (8 * bsCCT κ + 171)) + 1

theorem bandBracket_le (κ : LocalKernelClass) {d : ℕ} (hLh : 0 ≤ Lh) (hdL : (d : ℝ) ≤ Lh) :
    bandBracket κ d D J1 m Lh ≤ bsKfin κ * bsOmega D J1 m Lh ^ 13 := by
  have hΩ := one_le_bsOmega (D := D) (J1 := J1) (m := m) hLh
  have hKF := kernelFourierConst_nonneg κ
  have hlin := linearScaleConst_nonneg κ
  have hC := localKernelSupBound_nonneg κ
  have t1 := bracket_t1_le (D := D) (J1 := J1) (m := m) κ hLh hdL
  have t2 := bracket_t2_le (D := D) (J1 := J1) (m := m) hLh hdL
  have t3 := bracket_t3_le (D := D) (J1 := J1) (m := m) κ hLh hdL
  have t4 := bracket_t4_le (D := D) (J1 := J1) (m := m) κ hLh hdL
  have h013 : 1 ≤ bsOmega D J1 m Lh ^ 13 := one_le_pow₀ hΩ
  unfold bandBracket bsKfin
  calc _ ≤ kernelFourierConst κ * (512 * (8 * bsCCT κ + 175 + bsLConst) *
          bsOmega D J1 m Lh ^ 13 + 36288 * bsOmega D J1 m Lh ^ 13) +
        linearScaleConst κ * (24 * (2 * Real.pi) ^ 2 * 32768 * (4 * bsCCT κ + 90) *
          bsOmega D J1 m Lh ^ 13) +
        4 * localKernelSupBound κ * ((243 + 16 * (8 * bsCCT κ + 171)) *
          bsOmega D J1 m Lh ^ 13) + bsOmega D J1 m Lh ^ 13 := by
        gcongr
    _ = _ := by ring

/-- The `eq:band-scale-sum` bracket is polynomial in `W = 2 + m + log H`. -/
theorem bandBracket_poly (κ : LocalKernelClass) (D J1 : ℕ) : ∃ C : ℕ, ∀ (d m : ℕ) (Lh : ℝ),
    0 ≤ Lh → (d : ℝ) ≤ Lh → bandBracket κ d D J1 m Lh ≤ C * (2 + m + Lh) ^ C := by
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = ⌈bsKfin κ * ((D + J1 + 1 : ℕ) : ℝ) ^ 13⌉₊ + 13 * (D + J1 + 1) :=
    ⟨_, rfl⟩
  refine ⟨C, fun d m Lh hLh hdL => ?_⟩
  have h := bandBracket_le (D := D) (J1 := J1) (m := m) κ hLh hdL
  have hW : 1 ≤ 2 + (m : ℝ) + Lh := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  refine h.trans ?_
  have h1 : bsKfin κ * ((D + J1 + 1 : ℕ) : ℝ) ^ 13 ≤ (C : ℝ) := by
    have h2 := Nat.le_ceil (bsKfin κ * ((D + J1 + 1 : ℕ) : ℝ) ^ 13)
    have h3 : (C : ℝ) = (⌈bsKfin κ * ((D + J1 + 1 : ℕ) : ℝ) ^ 13⌉₊ : ℝ) +
        ((13 * (D + J1 + 1) : ℕ) : ℝ) := by rw [hC]; push_cast; ring
    have h4 : (0 : ℝ) ≤ ((13 * (D + J1 + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have h2 : (2 + (m : ℝ) + Lh) ^ ((D + J1 + 1) * 13) ≤ (2 + (m : ℝ) + Lh) ^ C :=
    pow_le_pow_right₀ hW (by rw [hC]; omega)
  have hK0 : 0 ≤ bsKfin κ := by
    unfold bsKfin
    have := kernelFourierConst_nonneg κ; have := linearScaleConst_nonneg κ
    have := localKernelSupBound_nonneg κ; have := bsCCT_nonneg κ; have := bsLConst_nonneg
    positivity
  unfold bsOmega
  calc bsKfin κ * (((D + J1 + 1 : ℕ) : ℝ) * (2 + (m : ℝ) + Lh) ^ (D + J1 + 1)) ^ 13
      = (bsKfin κ * ((D + J1 + 1 : ℕ) : ℝ) ^ 13) * (2 + (m : ℝ) + Lh) ^ ((D + J1 + 1) * 13) := by
        rw [mul_pow, ← pow_mul]; ring
    _ ≤ (C : ℝ) * (2 + (m : ℝ) + Lh) ^ C := mul_le_mul h1 h2 (by positivity) (by positivity)

end BandBudget

/-- Blueprint lem:predictors, `eq:band-scale-sum`: for one separated time factor
`Q = quadraticChartAtom A`, a bounded chart of complexity `H` (fixed Gevrey order `c₀`), and
admissible opponents with transfer constants `K_a, K_b`, the absolute length-weighted sum
over the cells of the `m`-th Fourier-supremum band `e^{-m-1} < A_{|I|} ≤ e^{-m}` is at most
`e^{-m} C (2 + m + log H)^C K_a K_b ‖1_J F_a‖₂ ‖1_J F_b‖₂`, with `C` depending only on the
Gevrey order and the kernel class. -/
theorem band_scale_sum (c₀ : ℕ) (hc : 1 ≤ c₀) (κ : LocalKernelClass) :
    ∃ C : ℕ, ∀ {d : ℕ} (H : ℝ) (A : QuadraticChartData d), 1 ≤ d →
      QuadraticChartComplexity c₀ H A → IsBoundedQuadraticChart A → ∀ (m : ℕ)
      (G : RealDyadicGrid) (J : ℤ × ℤ) (S : Finset (ℤ × ℤ)),
      (∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2) →
      ∀ (w : ℤ × ℤ → ℝ × ℝ → ℂ), (∀ I ∈ S, IsAdmissibleLocalKernel κ
        (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I)) →
      ∀ {a b : Fin 4}, a ≠ b → ∀ {ψa ψb : ℝ → ℂ}, Measurable ψa → Measurable ψb →
      (∀ y, ‖ψa y‖ ≤ 1) → (∀ y, ‖ψb y‖ ≤ 1) →
      ∀ {Fa Fb : ℝ → ℂ} {za zb : ℤ × ℤ → ℝ → ℂ} {Ka Kb : ℝ}, 0 ≤ Ka → 0 ≤ Kb →
      IsAdmissibleOpponent G J Fa za Ka → IsAdmissibleOpponent G J Fb zb Kb →
      HasDepthEnergy G J Fa za Ka → HasDepthEnergy G J Fb zb Kb →
      (∀ I, Measurable (za I)) → (∀ I, Measurable (zb I)) →
      (∀ I, MemLp (za I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) →
      (∀ I, MemLp (zb I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) →
      (∀ I ∈ S, InScaleBand (quadraticChartAtom A) m (dyadicGridLength G I.1)) →
      ∑ I ∈ S, dyadicGridLength G I.1 *
        ‖separatedLocalForm (dyadicGridLength G I.1) (w I) (quadraticChartAtom A) a b
          (fun y => ψa y * za I y) (fun y => ψb y * zb I y)‖ ≤
        Real.exp (-(m : ℝ)) * (C * (2 + m + Real.log H) ^ C) *
          Ka * Kb * Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2) *
          Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) := by
  obtain ⟨D, J1, hD, hpar⟩ := band_scale_sum_param c₀ hc κ
  obtain ⟨C₀, hC₀⟩ := bandBracket_poly κ D J1
  set c₁ : ℝ := 1 + Real.log (bandLip + 2) with hc₁
  have hL0 := bandLip_spec.1
  have hc₁1 : 1 ≤ c₁ := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ bandLip + 2 by linarith); linarith
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = ⌈(C₀ : ℝ) * c₁ ^ C₀⌉₊ + C₀ := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  intro d H A hd hA hAb m G J S hSJ w hw a b hab ψa ψb hψam hψbm hψa hψb Fa Fb za zb Ka Kb
    hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 hband
  have h := hpar H A hd hA hAb m G J S hSJ w hw hab hψam hψbm hψa hψb hKa hKb hza hzb hEa hEb
    hzam hzbm hza2 hzb2 hband
  refine h.trans ?_
  have hH1 : 1 ≤ H := by linarith [hA.lower, Real.add_one_le_exp (2 : ℝ)]
  have hlogH0 : 0 ≤ Real.log H := Real.log_nonneg hH1
  set Lh := Real.log (max H (bandLip + 1)) with hLhd
  have hLh0 : 0 ≤ Lh := Real.log_nonneg (hH1.trans (le_max_left _ _))
  have hdL : (d : ℝ) ≤ Lh :=
    hA.dimension.trans (Real.log_le_log (by linarith) (le_max_left _ _))
  have hLh : Lh ≤ Real.log H + Real.log (bandLip + 2) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    refine Real.log_le_log (by positivity) (max_le ?_ ?_)
    · nlinarith only [hL0, hH1]
    · nlinarith only [hL0, hH1]
  have hbr := hC₀ d m Lh hLh0 hdL
  set W := 2 + (m : ℝ) + Real.log H with hWd
  have hW1 : 1 ≤ W := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hWL : 2 + (m : ℝ) + Lh ≤ c₁ * W := by
    rw [hc₁, hWd]
    have hl := Real.log_nonneg (show (1 : ℝ) ≤ bandLip + 2 by linarith)
    nlinarith only [hc₁1, hlogH0, hLh]
  have hpow : (2 + (m : ℝ) + Lh) ^ C₀ ≤ c₁ ^ C₀ * W ^ C₀ := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hWL C₀
  have hfin : (C₀ : ℝ) * (2 + (m : ℝ) + Lh) ^ C₀ ≤ (C : ℝ) * W ^ C := by
    have h1 : (C₀ : ℝ) * c₁ ^ C₀ ≤ (C : ℝ) := by
      have h2 := Nat.le_ceil ((C₀ : ℝ) * c₁ ^ C₀)
      have h3 : (C : ℝ) = (⌈(C₀ : ℝ) * c₁ ^ C₀⌉₊ : ℝ) + (C₀ : ℝ) := by rw [hC]; push_cast; ring
      have h4 := Nat.cast_nonneg (α := ℝ) C₀
      linarith
    have h5 : W ^ C₀ ≤ W ^ C := pow_le_pow_right₀ hW1 (by rw [hC]; omega)
    calc (C₀ : ℝ) * (2 + (m : ℝ) + Lh) ^ C₀ ≤ (C₀ : ℝ) * (c₁ ^ C₀ * W ^ C₀) :=
          mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
      _ = ((C₀ : ℝ) * c₁ ^ C₀) * W ^ C₀ := by ring
      _ ≤ (C : ℝ) * W ^ C := mul_le_mul h1 h5 (by positivity) (by positivity)
  have hK : 0 ≤ Ka * Kb * Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2) *
      Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) := by positivity
  have hem := (Real.exp_pos (-(m : ℝ))).le
  calc Real.exp (-(m : ℝ)) * bandBracket κ d D J1 m Lh * Ka * Kb *
        Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2) *
        Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2)
      = Real.exp (-(m : ℝ)) * bandBracket κ d D J1 m Lh * (Ka * Kb *
        Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2) *
        Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2)) := by ring
    _ ≤ Real.exp (-(m : ℝ)) * ((C : ℝ) * W ^ C) * (Ka * Kb *
        Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2) *
        Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbr.trans hfin) hem) hK
    _ = _ := by ring

/-- Blueprint lem:predictors, proof line 1543 ("distribute each `e(γt)` between the two
remaining slots"): on the progression `t = (y_b - y_a)/(b - a)`. -/
theorem separatedLocalForm_phase_distribute (r : ℝ) (w : ℝ × ℝ → ℂ) (lam γ : ℝ) {a b : Fin 4}
    (hab : a ≠ b) (Fa Fb : ℝ → ℂ) :
    separatedLocalForm r w (quadPhase lam γ) a b Fa Fb =
      separatedLocalForm r w (fun t => (Real.fourierChar (lam * t ^ 2) : ℂ)) a b
        (fun y => (Real.fourierChar (-(γ / ((b : ℝ) - (a : ℝ)) * y)) : ℂ) * Fa y)
        (fun y => (Real.fourierChar (γ / ((b : ℝ) - (a : ℝ)) * y) : ℂ) * Fb y) := by
  have hd := fin_cast_sub_ne hab
  unfold separatedLocalForm
  congr 2; funext z
  have hph : quadPhase lam γ z.2 = (Real.fourierChar (lam * z.2 ^ 2) : ℂ) *
      ((Real.fourierChar (-(γ / ((b : ℝ) - (a : ℝ)) * realProgressionCoordinate a z)) : ℂ) *
        (Real.fourierChar (γ / ((b : ℝ) - (a : ℝ)) * realProgressionCoordinate b z) : ℂ)) := by
    unfold quadPhase
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← Circle.coe_mul,
      ← AddChar.map_add_eq_mul]
    congr 2
    simp only [realProgressionCoordinate]
    field_simp
    ring
  rw [hph]; ring

/-- The Fourier-supremum `A_r = sup_ξ |∫ Q(ru) ζ(u) e(-ξu) du|` of a time factor. -/
noncomputable def bandSup (Q : ℝ → ℂ) (r : ℝ) : ℝ := ⨆ ξ, bandAmplitude Q r ξ

theorem bandAmplitude_le_of_bound {Q : ℝ → ℂ} {c : ℝ}
    (hQ : ∀ t, ‖Q t‖ ≤ c) (r ξ : ℝ) : bandAmplitude Q r ξ ≤ 4 * c := by
  have hc : 0 ≤ c := (norm_nonneg _).trans (hQ 0)
  unfold bandAmplitude
  refine (norm_integral_le_integral_norm _).trans ?_
  have h4 := integral_bandCutoff_le_four
  have hb : ∀ u, ‖Q (r * u) * (bandCutoff u : ℂ) * (Real.fourierChar (-(ξ * u)) : ℂ)‖ ≤
      c * bandCutoff u := fun u => by
    rw [norm_mul, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (bandCutoff_spec.2.1 u)]
    exact mul_le_mul_of_nonneg_right (hQ _) (bandCutoff_spec.2.1 u)
  calc ∫ u, ‖Q (r * u) * (bandCutoff u : ℂ) * (Real.fourierChar (-(ξ * u)) : ℂ)‖
      ≤ ∫ u, c * bandCutoff u :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (bandCutoff_integrable.const_mul c) (Filter.Eventually.of_forall hb)
    _ = c * ∫ u, bandCutoff u := integral_const_mul _ _
    _ ≤ c * 4 := mul_le_mul_of_nonneg_left h4 hc
    _ = 4 * c := by ring

theorem bandAmplitude_bddAbove {Q : ℝ → ℂ} {c : ℝ} (hQ : ∀ t, ‖Q t‖ ≤ c)
    (r : ℝ) : BddAbove (Set.range (bandAmplitude Q r)) :=
  ⟨4 * c, by rintro _ ⟨ξ, rfl⟩; exact bandAmplitude_le_of_bound hQ r ξ⟩

theorem bandAmplitude_le_bandSup {Q : ℝ → ℂ} {c : ℝ}
    (hQ : ∀ t, ‖Q t‖ ≤ c) (r ξ : ℝ) : bandAmplitude Q r ξ ≤ bandSup Q r :=
  le_ciSup (bandAmplitude_bddAbove hQ r) ξ

theorem bandSup_nonneg (Q : ℝ → ℂ) (r : ℝ) : 0 ≤ bandSup Q r := by
  unfold bandSup
  exact Real.iSup_nonneg fun ξ => norm_nonneg _

theorem bandSup_le {Q : ℝ → ℂ} {c : ℝ} (hQ : ∀ t, ‖Q t‖ ≤ c) (r : ℝ) :
    bandSup Q r ≤ 4 * c := by
  have hc : 0 ≤ c := (norm_nonneg _).trans (hQ 0)
  unfold bandSup
  exact Real.iSup_le (fun ξ => bandAmplitude_le_of_bound hQ r ξ) (by positivity)

/-- A positive band supremum at most one lies in exactly one band `e^{-m-1} < A_r ≤ e^{-m}`. -/
theorem inScaleBand_of_bandSup {Q : ℝ → ℂ} {c : ℝ}
    (hQ : ∀ t, ‖Q t‖ ≤ c) {r : ℝ} (hpos : 0 < bandSup Q r) (hle : bandSup Q r ≤ 1) :
    InScaleBand Q ⌊-Real.log (bandSup Q r)⌋₊ r := by
  have hlog : 0 ≤ -Real.log (bandSup Q r) := by
    have := Real.log_nonpos hpos.le hle; linarith
  have h1 : ((⌊-Real.log (bandSup Q r)⌋₊ : ℕ) : ℝ) ≤ -Real.log (bandSup Q r) :=
    Nat.floor_le hlog
  have h2 : -Real.log (bandSup Q r) < ((⌊-Real.log (bandSup Q r)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  refine ⟨fun ξ => (bandAmplitude_le_bandSup hQ r ξ).trans ?_, ?_⟩
  · calc bandSup Q r = Real.exp (Real.log (bandSup Q r)) := (Real.exp_log hpos).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · have hlt : Real.exp (-(((⌊-Real.log (bandSup Q r)⌋₊ : ℕ) : ℝ) + 1)) < bandSup Q r := by
      calc Real.exp (-(((⌊-Real.log (bandSup Q r)⌋₊ : ℕ) : ℝ) + 1))
          < Real.exp (Real.log (bandSup Q r)) := Real.exp_lt_exp.mpr (by linarith)
        _ = bandSup Q r := Real.exp_log hpos
    obtain ⟨ξ, hξ⟩ := exists_lt_of_lt_ciSup hlt
    exact ⟨ξ, hξ⟩

/-- The separated form vanishes at scales whose band supremum vanishes
(blueprint lem:predictors, line 1495: "the term vanishes when `A_{|I|} = 0`"). -/
theorem separatedLocalForm_eq_zero_of_bandSup {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) {a b : Fin 4} (hab : a ≠ b)
    {Q : ℝ → ℂ} (hQm : Measurable Q) (hQ1 : ∀ t, ‖Q t‖ ≤ 1) (h0 : bandSup Q r = 0)
    {Fa Fb : ℝ → ℂ} (hFam : Measurable Fa) (hFbm : Measurable Fb)
    (hFa : MemLp Fa 2 (volume.restrict (Set.Ico a₀ (a₀ + r))))
    (hFb : MemLp Fb 2 (volume.restrict (Set.Ico a₀ (a₀ + r)))) :
    separatedLocalForm r w Q a b Fa Fb = 0 := by
  have h := separated_form_le_band hr hw hab hQm hQ1 (M := 0)
    (fun ξ => (bandAmplitude_le_bandSup hQ1 r ξ).trans h0.le) hFam hFbm hFa hFb
  simp only [mul_zero, zero_mul] at h
  exact norm_le_zero_iff.mp h

theorem summable_band_series (C : ℕ) :
    Summable (fun m : ℕ => (1 + (m : ℝ)) ^ C * Real.exp (-(m : ℝ) / 2)) := by
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul C (r := 1 / 2) (by norm_num)
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 (r := 1 / 2) (by norm_num)
  refine ((h1.add h0).mul_left (2 ^ C)).of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
  have he : Real.exp (-(m : ℝ) / 2) = Real.exp (-(1 / 2) * m) := by ring_nf
  rw [he]
  have hm : (1 + (m : ℝ)) ^ C ≤ 2 ^ C * ((m : ℝ) ^ C + 1) := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp only [Nat.cast_zero, add_zero, one_pow, zero_pow_eq]
      have : (1 : ℝ) ≤ 2 ^ C := one_le_pow₀ (by norm_num)
      split_ifs <;> nlinarith
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h
      calc (1 + (m : ℝ)) ^ C ≤ (2 * m) ^ C := pow_le_pow_left₀ (by positivity) (by linarith) C
        _ = 2 ^ C * (m : ℝ) ^ C := mul_pow _ _ _
        _ ≤ 2 ^ C * ((m : ℝ) ^ C + 1) := by nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) C]
  have hp : 0 ≤ Real.exp (-(1 / 2) * m) := (Real.exp_pos _).le
  calc (1 + (m : ℝ)) ^ C * Real.exp (-(1 / 2) * m)
      ≤ 2 ^ C * ((m : ℝ) ^ C + 1) * Real.exp (-(1 / 2) * m) := mul_le_mul_of_nonneg_right hm hp
    _ = 2 ^ C * ((m : ℝ) ^ C * Real.exp (-(1 / 2) * m) +
        (m : ℝ) ^ 0 * Real.exp (-(1 / 2) * m)) := by ring

/-- The constant `Σ_m (1 + m)^C e^{-m/2}` for summing band estimates. -/
noncomputable def bandSeriesConst (C : ℕ) : ℝ :=
  ∑' m : ℕ, (1 + (m : ℝ)) ^ C * Real.exp (-(m : ℝ) / 2)

theorem bandSeriesConst_nonneg (C : ℕ) : 0 ≤ bandSeriesConst C :=
  tsum_nonneg fun m => by positivity

theorem band_series_term_le (C m M₀ : ℕ) (hm : M₀ ≤ m) {L : ℝ} (hL : 0 ≤ L) :
    Real.exp (-(m : ℝ)) * (2 + m + L) ^ C ≤
      Real.exp (-(M₀ : ℝ) / 2) * (2 + L) ^ C * ((1 + (m : ℝ)) ^ C * Real.exp (-(m : ℝ) / 2)) := by
  have h1 : (2 + (m : ℝ) + L) ≤ (2 + L) * (1 + m) := by
    have := Nat.cast_nonneg (α := ℝ) m; nlinarith
  have h2 : (2 + (m : ℝ) + L) ^ C ≤ (2 + L) ^ C * (1 + m) ^ C := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 C
  have h3 : Real.exp (-(m : ℝ)) ≤ Real.exp (-(M₀ : ℝ) / 2) * Real.exp (-(m : ℝ) / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : (M₀ : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  calc Real.exp (-(m : ℝ)) * (2 + m + L) ^ C
      ≤ (Real.exp (-(M₀ : ℝ) / 2) * Real.exp (-(m : ℝ) / 2)) * ((2 + L) ^ C * (1 + m) ^ C) :=
        mul_le_mul h3 h2 (by positivity) (by positivity)
    _ = _ := by ring

/-- Finite sums of band estimates above a threshold. -/
theorem band_sum_le (C M₀ : ℕ) (Ms : Finset ℕ) (hMs : ∀ m ∈ Ms, M₀ ≤ m) {L : ℝ} (hL : 0 ≤ L) :
    ∑ m ∈ Ms, Real.exp (-(m : ℝ)) * (2 + m + L) ^ C ≤
      Real.exp (-(M₀ : ℝ) / 2) * (2 + L) ^ C * bandSeriesConst C := by
  calc ∑ m ∈ Ms, Real.exp (-(m : ℝ)) * (2 + m + L) ^ C
      ≤ ∑ m ∈ Ms, Real.exp (-(M₀ : ℝ) / 2) * (2 + L) ^ C *
          ((1 + (m : ℝ)) ^ C * Real.exp (-(m : ℝ) / 2)) :=
        Finset.sum_le_sum fun m hm => band_series_term_le C m M₀ (hMs m hm) hL
    _ = Real.exp (-(M₀ : ℝ) / 2) * (2 + L) ^ C *
          ∑ m ∈ Ms, (1 + (m : ℝ)) ^ C * Real.exp (-(m : ℝ) / 2) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(M₀ : ℝ) / 2) * (2 + L) ^ C * bandSeriesConst C :=
        mul_le_mul_of_nonneg_left ((summable_band_series C).sum_le_tsum Ms
          (fun m _ => by positivity)) (by positivity)

theorem quarterChart_bounded {d : ℕ} {A : QuadraticChartData d} (hAb : IsBoundedQuadraticChart A) :
    IsBoundedQuadraticChart (scaleQuadraticChartAmplitude (1 / 4 : ℂ) A) := by
  intro y
  rw [scaleQuadraticChartAmplitude_atom, norm_mul]
  have : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [this]
  have := hAb y
  nlinarith

theorem quarterChart_norm_le {d : ℕ} {A : QuadraticChartData d}
    (hAb : IsBoundedQuadraticChart A) (y : ℝ) :
    ‖quadraticChartAtom (scaleQuadraticChartAmplitude (1 / 4 : ℂ) A) y‖ ≤ 1 / 4 := by
  rw [scaleQuadraticChartAmplitude_atom, norm_mul]
  have : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [this]
  have := hAb y
  nlinarith

/-- Blueprint lem:predictors, proof lines 1544-1546: the band scale sums of one separated
time factor summed over all bands `m ≥ M₀` of the normalized factor `Q/4`. -/
theorem chart_band_range_scale_sum (c₀ : ℕ) (hc : 1 ≤ c₀) (κ : LocalKernelClass) :
    ∃ C : ℕ, ∀ {d : ℕ} (H : ℝ) (A : QuadraticChartData d), 1 ≤ d →
      QuadraticChartComplexity c₀ H A → IsBoundedQuadraticChart A → ∀ (M₀ : ℕ)
      (G : RealDyadicGrid) (J : ℤ × ℤ) (S : Finset (ℤ × ℤ)),
      (∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2) →
      ∀ (w : ℤ × ℤ → ℝ × ℝ → ℂ), (∀ I ∈ S, IsAdmissibleLocalKernel κ
        (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I)) →
      ∀ {a b : Fin 4}, a ≠ b → ∀ {ψa ψb : ℝ → ℂ}, Measurable ψa → Measurable ψb →
      (∀ y, ‖ψa y‖ ≤ 1) → (∀ y, ‖ψb y‖ ≤ 1) →
      ∀ {Fa Fb : ℝ → ℂ} {za zb : ℤ × ℤ → ℝ → ℂ} {Ka Kb : ℝ}, 0 ≤ Ka → 0 ≤ Kb →
      IsAdmissibleOpponent G J Fa za Ka → IsAdmissibleOpponent G J Fb zb Kb →
      HasDepthEnergy G J Fa za Ka → HasDepthEnergy G J Fb zb Kb →
      (∀ I, Measurable (za I)) → (∀ I, Measurable (zb I)) →
      (∀ I, MemLp (za I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) →
      (∀ I, MemLp (zb I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) →
      (∀ I ∈ S, bandSup (quadraticChartAtom (scaleQuadraticChartAmplitude (1 / 4 : ℂ) A))
        (dyadicGridLength G I.1) ≤ Real.exp (-(M₀ : ℝ))) →
      ∑ I ∈ S, dyadicGridLength G I.1 *
        ‖separatedLocalForm (dyadicGridLength G I.1) (w I) (quadraticChartAtom A) a b
          (fun y => ψa y * za I y) (fun y => ψb y * zb I y)‖ ≤
        Real.exp (-(M₀ : ℝ) / 2) * (C * (2 + Real.log H) ^ C) *
          Ka * Kb * Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2) *
          Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) := by
  obtain ⟨Cb, hCb⟩ := band_scale_sum c₀ hc κ
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = ⌈4 * (Cb : ℝ) * bandSeriesConst Cb⌉₊ + Cb := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  intro d H A hd hA hAb M₀ G J S hSJ w hw a b hab ψa ψb hψam hψbm hψa hψb Fa Fb za zb Ka Kb
    hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 hband
  classical
  set A' := scaleQuadraticChartAmplitude (1 / 4 : ℂ) A with hA'
  have hA'c : QuadraticChartComplexity c₀ H A' :=
    scaleQuadraticChartAmplitude_complexity hA (by norm_num)
  have hA'b := quarterChart_bounded hAb
  have hQm := quadraticChartAtom_measurable A'
  have hQ4 := quarterChart_norm_le hAb
  set Q' := quadraticChartAtom A' with hQ'
  set Na := Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2)
  set Nb := Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2)
  have hK : 0 ≤ Ka * Kb * Na * Nb := by positivity
  have hH1 : 1 ≤ H := by linarith [hA.lower, Real.add_one_le_exp (2 : ℝ)]
  have hL0 : 0 ≤ Real.log H := Real.log_nonneg hH1
  -- band index
  set! band : ℤ × ℤ → ℕ := fun I => ⌊-Real.log (bandSup Q' (dyadicGridLength G I.1))⌋₊
    with hbandd
  set! Sp := S.filter (fun I => 0 < bandSup Q' (dyadicGridLength G I.1)) with hSp
  have hzero : ∀ I ∈ S, ¬ 0 < bandSup Q' (dyadicGridLength G I.1) →
      separatedLocalForm (dyadicGridLength G I.1) (w I) Q' a b
        (fun y => ψa y * za I y) (fun y => ψb y * zb I y) = 0 := by
    intro I hI hIp
    have h0 : bandSup Q' (dyadicGridLength G I.1) = 0 := by
      have := bandSup_nonneg Q' (dyadicGridLength G I.1)
      by_contra hne
      exact hIp (lt_of_le_of_ne this (Ne.symm hne))
    exact separatedLocalForm_eq_zero_of_bandSup (dyadicGridLength_pos G I.1) (hw I hI) hab hQm
      (fun t => (hQ4 t).trans (by norm_num)) h0 (hψam.mul (hzam I)) (hψbm.mul (hzbm I))
      (memLp_mul_bounded_restrict hψam hψa (hza2 I))
      (memLp_mul_bounded_restrict hψbm hψb (hzb2 I))
  have hmain : ∑ I ∈ S, dyadicGridLength G I.1 * ‖separatedLocalForm (dyadicGridLength G I.1)
      (w I) Q' a b (fun y => ψa y * za I y) (fun y => ψb y * zb I y)‖ ≤
      Real.exp (-(M₀ : ℝ) / 2) * (2 + Real.log H) ^ Cb * bandSeriesConst Cb *
        ((Cb : ℝ) * (Ka * Kb * Na * Nb)) := by
    rw [← Finset.sum_filter_add_sum_filter_not S
      (fun I => 0 < bandSup Q' (dyadicGridLength G I.1))]
    rw [Finset.sum_eq_zero (s := S.filter (fun I => ¬ 0 < bandSup Q' (dyadicGridLength G I.1)))
      (fun I hI => by
        rw [hzero I (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hI).2, norm_zero,
          mul_zero]), add_zero]
    rw [← hSp, ← Finset.sum_fiberwise_of_maps_to (g := band) (t := Sp.image band)
      (fun I hI => Finset.mem_image_of_mem _ hI)]
    have hfib : ∀ m ∈ Sp.image band, ∑ I ∈ Sp.filter (fun I => band I = m),
        dyadicGridLength G I.1 * ‖separatedLocalForm (dyadicGridLength G I.1) (w I) Q' a b
          (fun y => ψa y * za I y) (fun y => ψb y * zb I y)‖ ≤
        Real.exp (-(m : ℝ)) * (2 + m + Real.log H) ^ Cb * ((Cb : ℝ) * (Ka * Kb * Na * Nb)) := by
      intro m _
      have hS' : ∀ I ∈ Sp.filter (fun I => band I = m), I ∈ S ∧
          0 < bandSup Q' (dyadicGridLength G I.1) ∧ band I = m := fun I hI =>
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).1,
          (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2, (Finset.mem_filter.mp hI).2⟩
      have h := hCb H A' hd hA'c hA'b m G J (Sp.filter (fun I => band I = m))
        (fun I hI => hSJ I (hS' I hI).1) w (fun I hI => hw I (hS' I hI).1) hab hψam hψbm hψa
        hψb hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 (fun I hI => by
          have hb := inScaleBand_of_bandSup (fun t => hQ4 t) (hS' I hI).2.1
            (bandSup_le (fun t => hQ4 t) _ |>.trans (by norm_num))
          have : band I = m := (hS' I hI).2.2
          rw [hbandd] at this
          simp only at this
          rw [this] at hb
          exact hb)
      refine h.trans (le_of_eq ?_)
      ring
    refine (Finset.sum_le_sum hfib).trans ?_
    rw [← Finset.sum_mul]
    have hge : ∀ m ∈ Sp.image band, M₀ ≤ m := by
      intro m hm
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hm
      have hIS := (Finset.mem_filter.mp hI).1
      have hpos := (Finset.mem_filter.mp hI).2
      have hb := hband I hIS
      have hlog : (M₀ : ℝ) ≤ -Real.log (bandSup Q' (dyadicGridLength G I.1)) := by
        have := Real.log_le_log hpos hb
        rw [Real.log_exp] at this
        linarith
      exact Nat.le_floor hlog
    have hbs := band_sum_le Cb M₀ (Sp.image band) hge hL0
    have hCK : 0 ≤ (Cb : ℝ) * (Ka * Kb * Na * Nb) := by positivity
    calc (∑ m ∈ Sp.image band, Real.exp (-(m : ℝ)) * (2 + m + Real.log H) ^ Cb) *
          ((Cb : ℝ) * (Ka * Kb * Na * Nb))
        ≤ (Real.exp (-(M₀ : ℝ) / 2) * (2 + Real.log H) ^ Cb * bandSeriesConst Cb) *
          ((Cb : ℝ) * (Ka * Kb * Na * Nb)) := mul_le_mul_of_nonneg_right hbs hCK
      _ = _ := by ring
  -- the factor `4`
  have hQ : ∀ I, separatedLocalForm (dyadicGridLength G I.1) (w I) (quadraticChartAtom A) a b
      (fun y => ψa y * za I y) (fun y => ψb y * zb I y) =
      4 * separatedLocalForm (dyadicGridLength G I.1) (w I) Q' a b
        (fun y => ψa y * za I y) (fun y => ψb y * zb I y) := by
    intro I
    rw [← separatedLocalForm_const_mul]
    congr 1; funext t
    rw [hQ', hA', scaleQuadraticChartAmplitude_atom]; ring
  have hsum4 : ∑ I ∈ S, dyadicGridLength G I.1 * ‖separatedLocalForm (dyadicGridLength G I.1)
      (w I) (quadraticChartAtom A) a b (fun y => ψa y * za I y) (fun y => ψb y * zb I y)‖ =
      4 * ∑ I ∈ S, dyadicGridLength G I.1 * ‖separatedLocalForm (dyadicGridLength G I.1)
      (w I) Q' a b (fun y => ψa y * za I y) (fun y => ψb y * zb I y)‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hQ I, norm_mul]
    have : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [this]; ring
  rw [hsum4]
  have hBS := bandSeriesConst_nonneg Cb
  have hC1 : 4 * (Cb : ℝ) * bandSeriesConst Cb ≤ (C : ℝ) := by
    have h2 := Nat.le_ceil (4 * (Cb : ℝ) * bandSeriesConst Cb)
    have h3 : (C : ℝ) = (⌈4 * (Cb : ℝ) * bandSeriesConst Cb⌉₊ : ℝ) + (Cb : ℝ) := by
      rw [hC]; push_cast; ring
    have h4 := Nat.cast_nonneg (α := ℝ) Cb
    linarith only [h2, h3]
  have hW : 1 ≤ 2 + Real.log H := by linarith
  have hpow : (2 + Real.log H) ^ Cb ≤ (2 + Real.log H) ^ C :=
    pow_le_pow_right₀ hW (by rw [hC]; omega)
  have hem := (Real.exp_pos (-(M₀ : ℝ) / 2)).le
  calc 4 * ∑ I ∈ S, dyadicGridLength G I.1 * ‖separatedLocalForm (dyadicGridLength G I.1)
        (w I) Q' a b (fun y => ψa y * za I y) (fun y => ψb y * zb I y)‖
      ≤ 4 * (Real.exp (-(M₀ : ℝ) / 2) * (2 + Real.log H) ^ Cb * bandSeriesConst Cb *
        ((Cb : ℝ) * (Ka * Kb * Na * Nb))) := mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = Real.exp (-(M₀ : ℝ) / 2) * ((4 * (Cb : ℝ) * bandSeriesConst Cb) * (2 + Real.log H) ^ Cb) *
        (Ka * Kb * Na * Nb) := by ring
    _ ≤ Real.exp (-(M₀ : ℝ) / 2) * ((C : ℝ) * (2 + Real.log H) ^ C) * (Ka * Kb * Na * Nb) := by
        gcongr
    _ = _ := by ring

/-- The tail multiplicity growth constant at coefficient budget `E`. -/
noncomputable def tailAlpha (d : ℕ) (E : ℝ) : ℝ :=
  24 * (2 * Real.pi) ^ 2 * (4 * (32 * (((d + 1 : ℕ) + 1 : ℝ) + 1) ^ 4 *
    (Real.log 24 + 2 * Real.log E + 2 + Real.log 4)))

/-- The quadratic total at coefficient budget `E`. -/
noncomputable def tailLam (d : ℕ) (E : ℝ) : ℝ :=
  2 * Real.pi * (128 * ((d * d + 1 : ℕ) + 1 : ℝ) ^ 4 * Real.log (2 * (E + 2)) * E)

/-- The catalog tail constant at coefficient budget `E`. -/
noncomputable def tailCT (κ : LocalKernelClass) (d : ℕ) (E : ℝ) : ℝ :=
  linearScaleConst κ * tailAlpha d E + localKernelSupBound κ * tailLam d E

theorem tailCT_nonneg (κ : LocalKernelClass) (d : ℕ) {E : ℝ} (hE : 1 ≤ E) :
    0 ≤ tailCT κ d E := by
  have hlin := linearScaleConst_nonneg κ
  have hC := localKernelSupBound_nonneg κ
  have h24 : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlE : 0 ≤ Real.log E := Real.log_nonneg hE
  have hl : 0 ≤ Real.log (2 * (E + 2)) := Real.log_nonneg (by linarith)
  unfold tailCT tailAlpha tailLam
  positivity

theorem clumpMultiplicity_tail_le' (d : ℕ) {E u : ℝ} (hE : 1 ≤ E) (hu : 1 ≤ u) :
    clumpMultiplicity (d + 1) (6 * (E * u) ^ 2 + 6) ≤ tailAlpha d E * u := by
  have hlE0 : 0 ≤ Real.log E := Real.log_nonneg hE
  have hEu : 1 ≤ E * u := by nlinarith
  have harg : 2 * (6 * (E * u) ^ 2 + 6) ≤ 24 * (E * u) ^ 2 := by nlinarith
  have hlog : Real.log (2 * (6 * (E * u) ^ 2 + 6)) ≤ (Real.log 24 + 2 * Real.log E + 2) * u := by
    have h1 : Real.log (2 * (6 * (E * u) ^ 2 + 6)) ≤ Real.log (24 * (E * u) ^ 2) :=
      Real.log_le_log (by positivity) harg
    have h2 : Real.log (24 * (E * u) ^ 2) = Real.log 24 + 2 * Real.log E + 2 * Real.log u := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_mul
        (by positivity) (by positivity)]
      push_cast; ring
    have h3 : Real.log u ≤ u := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have h24 : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
    rw [h2] at h1
    nlinarith
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold clumpMultiplicity heightBandConst tailAlpha
  have hcast : (((d + 1 + 1 : ℕ) : ℝ) + 1) = (((d + 1 : ℕ) : ℝ) + 1) + 1 := by push_cast; ring
  rw [hcast]
  have hc0 : 0 ≤ 24 * (2 * Real.pi) ^ 2 * (4 * (32 * ((((d + 1 : ℕ) : ℝ) + 1) + 1) ^ 4)) := by
    positivity
  have key : Real.log (2 * (6 * (E * u) ^ 2 + 6)) + Real.log 4 ≤
      (Real.log 24 + 2 * Real.log E + 2 + Real.log 4) * u := by nlinarith only [hu, hlog, h4]
  calc 24 * (2 * Real.pi) ^ 2 * (4 * (32 * ((((d + 1 : ℕ) : ℝ) + 1) + 1) ^ 4 *
        (Real.log (2 * (6 * (E * u) ^ 2 + 6)) + Real.log 4)))
      = 24 * (2 * Real.pi) ^ 2 * (4 * (32 * ((((d + 1 : ℕ) : ℝ) + 1) + 1) ^ 4)) *
        (Real.log (2 * (6 * (E * u) ^ 2 + 6)) + Real.log 4) := by ring
    _ ≤ 24 * (2 * Real.pi) ^ 2 * (4 * (32 * ((((d + 1 : ℕ) : ℝ) + 1) + 1) ^ 4)) *
        ((Real.log 24 + 2 * Real.log E + 2 + Real.log 4) * u) :=
        mul_le_mul_of_nonneg_left key hc0
    _ = _ := by ring



end TrilinearHT.Auto
end
