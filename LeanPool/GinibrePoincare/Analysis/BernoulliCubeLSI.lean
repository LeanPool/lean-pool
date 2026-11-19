/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BernoulliCubeLSI.lean.
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

public import LeanPool.GinibrePoincare.Analysis.TwoPointLSI

/-!
# Bernoulli cube LSI

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `bernoulliCube_lsi`.
-/

@[expose] public section

open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- A recursively presented finite Bernoulli cube. -/
def BernoulliCube : ℕ → Type
  | 0 => Unit
  | n + 1 => BernoulliCube n × Bool

instance bernoulliCubeFintype : (n : ℕ) → Fintype (BernoulliCube n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd (BernoulliCube n) Bool (bernoulliCubeFintype n) inferInstance

instance bernoulliCubeNonempty : (n : ℕ) → Nonempty (BernoulliCube n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n + 1 => @instNonemptyProd (BernoulliCube n) Bool (bernoulliCubeNonempty n) inferInstance

/-- The sum of the conditional two-point energies, with probability normalization. -/
def bernoulliCubeEnergy : (n : ℕ) → (BernoulliCube n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, f =>
      (∑ y : Bool, bernoulliCubeEnergy n (fun x => f (x, y))) / 2 +
      (∑ x : BernoulliCube n, (f (x, true) - f (x, false)) ^ 2 / 2) /
        Fintype.card (BernoulliCube n)

/-- Sharp logarithmic Sobolev inequality on every finite fair Bernoulli cube. -/
theorem bernoulliCube_lsi (n : ℕ) (f : BernoulliCube n → ℝ) :
    uniformFiniteEntropy (fun x => (f x) ^ 2) ≤ bernoulliCubeEnergy n f := by
  induction n with
  | zero =>
      change uniformFiniteEntropy (fun x : Unit => (f x) ^ 2) ≤ 0
      simp [uniformFiniteEntropy, Fintype.card_unique]
  | succ n ih =>
      have h := uniformFiniteLSI_tensorization (bernoulliCubeEnergy n)
        (fun f : Bool → ℝ => (f true - f false) ^ 2 / 2) ih uniformFiniteLSI_bool f
      change uniformFiniteEntropy (fun p : BernoulliCube n × Bool => (f p) ^ 2) ≤ _
      simpa [bernoulliCubeEnergy] using h

end
end GinibrePoincare
