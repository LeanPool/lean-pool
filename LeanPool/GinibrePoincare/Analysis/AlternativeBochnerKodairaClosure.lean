/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBochnerKodairaClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.AlternativeBochnerKodairaCompact

/-! # Closure of the integrated Gaussian Bochner–Kodaira identity

The closure here is explicitly the closure of actual compact smooth jets.
No equality with the entire Gaussian number-operator domain is asserted in
this module. The derivative fields of every closed jet are genuine weak
Wirtinger derivatives.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff ComplexConjugate BigOperators Topology
namespace GinibrePoincare
noncomputable section

/-- Complex `L²` of the Gaussian reference measure. -/
abbrev BKGaussianL2 (n : ℕ) := Lp ℂ 2 (complexGaussianMeasure n)
/-- Jets in Gaussian `L²`: a value, its number-operator image, its first `dbar` derivatives and
its second `dbar` derivatives. -/
abbrev BKGaussianJet (n : ℕ) :=
  BKGaussianL2 n × BKGaussianL2 n × (Fin n → BKGaussianL2 n) ×
    (Fin n → Fin n → BKGaussianL2 n)

/-- The jet of a compact smooth test `f`: the `L²` classes of `f`, of its Gaussian number
operator image, of `dbar_j f`, and of `dbar_k (dbar_j f)`. -/
def bkCompactJet {n : ℕ} (f : BKCompactTest n) : BKGaussianJet n :=
  (f.l2, bkCompactNumberL2 f, (fun j => (f.dbar j).l2),
    fun j k => ((f.dbar j).dbar k).l2)

/-- The closure in Gaussian `L²` jets of the jets of compact smooth tests. -/
def bkGaussianClosedJets (n : ℕ) : Set (BKGaussianJet n) :=
  closure (Set.range (bkCompactJet (n := n)))

theorem bkCompact_number_pairing {n : ℕ} (hn : 0 < n) (f : BKCompactTest n) :
    inner ℂ f.l2 (bkCompactNumberL2 f) =
      (∑ j : Fin n, ‖(f.dbar j).l2‖ ^ 2 : ℝ) := by
  unfold bkCompactNumberL2
  rw [inner_sum]
  simp_rw [bkCompact_adjoint_pairing_right hn f, inner_self_eq_norm_sq_to_K]
  simp

theorem bkClosedJet_weak_derivatives {n : ℕ} (hn : 0 < n)
    (p : BKGaussianJet n) (hp : p ∈ bkGaussianClosedJets n) :
    (∀ j, IsGaussianWeakDbar n p.1 (p.2.2.1 j) j) ∧
      (∀ j k, IsGaussianWeakDbar n (p.2.2.1 j) (p.2.2.2 j k) k) := by
  have hc : IsClosed {p : BKGaussianJet n |
      (∀ j, IsGaussianWeakDbar n p.1 (p.2.2.1 j) j) ∧
        (∀ j k, IsGaussianWeakDbar n (p.2.2.1 j) (p.2.2.2 j k) k)} := by
    simp only [Set.ofPred_and, Set.ofPred_forall]
    apply IsClosed.inter
    · apply isClosed_iInter
      intro j
      exact (isClosed_gaussianWeakDbar_graph n j).preimage
        (continuous_fst.prodMk (by fun_prop))
    · apply isClosed_iInter
      intro j
      apply isClosed_iInter
      intro k
      exact (isClosed_gaussianWeakDbar_graph n k).preimage
        (show Continuous (fun p : BKGaussianJet n => (p.2.2.1 j, p.2.2.2 j k)) by fun_prop)
  apply closure_minimal (s := Set.range bkCompactJet) ?_ hc hp
  rintro _ ⟨f, rfl⟩
  constructor
  · intro j
    exact gaussian_smooth_weak_dbar hn j f.l2 (f.dbar j).l2 f
      (f.smooth.of_le (by simp)) f.l2_coe (f.dbar j).l2_coe
  · intro j k
    exact gaussian_smooth_weak_dbar hn k (f.dbar j).l2 ((f.dbar j).dbar k).l2
      (f.dbar j) ((f.dbar j).smooth.of_le (by simp))
      (f.dbar j).l2_coe ((f.dbar j).dbar k).l2_coe

/-- Integration by parts survives closure of the genuine compact smooth jets. -/
theorem bkClosedJet_number_pairing {n : ℕ} (hn : 0 < n)
    (p : BKGaussianJet n) (hp : p ∈ bkGaussianClosedJets n) :
    inner ℂ p.1 p.2.1 = (∑ j : Fin n, ‖p.2.2.1 j‖ ^ 2 : ℝ) := by
  have hc : IsClosed {p : BKGaussianJet n |
      inner ℂ p.1 p.2.1 = (∑ j : Fin n, ‖p.2.2.1 j‖ ^ 2 : ℝ)} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  apply closure_minimal (s := Set.range bkCompactJet) ?_ hc hp
  rintro _ ⟨f, rfl⟩
  exact bkCompact_number_pairing hn f

/-- The integrated identity (6.8) on the actual closed compact-jet domain. -/
theorem bkClosedJet_integrated_identity {n : ℕ} (hn : 0 < n)
    (p : BKGaussianJet n) (hp : p ∈ bkGaussianClosedJets n) :
    ‖p.2.1‖ ^ 2 = (∑ j : Fin n, ∑ k : Fin n, ‖p.2.2.2 j k‖ ^ 2) +
      (n : ℝ) * ∑ j : Fin n, ‖p.2.2.1 j‖ ^ 2 := by
  have hc : IsClosed {p : BKGaussianJet n |
      ‖p.2.1‖ ^ 2 = (∑ j : Fin n, ∑ k : Fin n, ‖p.2.2.2 j k‖ ^ 2) +
        (n : ℝ) * ∑ j : Fin n, ‖p.2.2.1 j‖ ^ 2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  apply closure_minimal (s := Set.range bkCompactJet) ?_ hc hp
  rintro _ ⟨f, rfl⟩
  exact bkCompact_integrated_identity hn f

/-- Equation (6.9) with genuine weak derivatives on the closed compact-jet domain. -/
theorem bkClosedJet_bochner_kodaira {n : ℕ} (hn : 0 < n)
    (p : BKGaussianJet n) (hp : p ∈ bkGaussianClosedJets n) :
    ‖p.2.1‖ ^ 2 - (n : ℝ) * (inner ℂ p.1 p.2.1).re =
      ∑ j : Fin n, ∑ k : Fin n, ‖p.2.2.2 j k‖ ^ 2 := by
  rw [bkClosedJet_number_pairing hn p hp]
  simp only [Complex.ofReal_re]
  linarith [bkClosedJet_integrated_identity hn p hp]

end
end GinibrePoincare

