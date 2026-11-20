/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/LogSobolevInequality.lean.
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

public import LeanPool.GinibrePoincare.Analysis.PolynomialEigenfunctions
public import LeanPool.GinibrePoincare.Analysis.GinibreEntropy
public import LeanPool.GinibrePoincare.Analysis.FullRadialLSIReduction

/-!
# Unconditional sharp radial logarithmic Sobolev inequality

The entire smooth compact symmetric radial class and its value-gradient
Sobolev completion are covered. The sharp Gaussian input is proved by the
Bernoulli tensorization, binomial CLT and Taylor route, then transported to
the concrete complex block law. No Gaussian inequality remains a hypothesis.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ContDiff

namespace GinibrePoincare

noncomputable section

-- Define entropy
/-- The entropy of f^2 with respect to μ_n. -/
def entropy (n : ℕ) (f : Configuration n → ℝ) : ℝ :=
  ginibreSquareEntropy n f

/-- The paper's Dirichlet form includes the essential `1/n` factor. -/
def dirichletFormLSI (n : ℕ) (f : Configuration n → ℝ) : ℝ :=
  smoothGinibreEnergy n f

/-- A function of a configuration is symmetric if it is invariant under permutations of the
particles. -/
def IsSymmetricFunctionLSI {n : ℕ} (f : Configuration n → ℝ) : Prop :=
  IsSymmetric f

/-- A function of a configuration is radial if it depends only on the squared moduli
`|z_1|², …, |z_n|²`. -/
def IsRadialFunctionLSI {n : ℕ} (f : Configuration n → ℝ) : Prop :=
  ∃ F : (Fin n → ℝ) → ℝ,
    ∀ z, f z = F (fun i => Complex.normSq (z i))

/-- A function of a configuration is smooth (`C^∞`) with compact support. -/
def IsSmoothCompactSupportLSI {n : ℕ} (f : Configuration n → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f

/-- The radial log-Sobolev inequality (Theorem 1.12 of arXiv:2608.19358v2): the entropy of
every smooth compactly supported symmetric radial function is bounded by its Dirichlet form. -/
structure LogSobolevInequality (n : ℕ) : Prop where
  -- For all symmetric radial smooth compactly supported functions f,
  -- the entropy is bounded by the Dirichlet form
  inequality :
    ∀ (f : Configuration n → ℝ),
      IsSmoothCompactSupportLSI f →
      IsSymmetricFunctionLSI f →
      IsRadialFunctionLSI f →
      entropy n f ≤ dirichletFormLSI n f
  
  -- The unconditional Sobolev completion theorem is `radial_sobolev_lsi`.

/-- The unconditional sharp LSI for the full smooth symmetric radial core. -/
theorem logSobolevInequality_instance (n : ℕ) (hn : n ≥ 1) : LogSobolevInequality n := by
  constructor
  intro f hfc hs hr
  exact radial_core_lsi n hn f ⟨⟨hfc.1, hfc.2, hs⟩, hr⟩

end

end GinibrePoincare
