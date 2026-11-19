/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Endgame/FullNonQuadraticPotential.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialSharpPoincare
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryPotentialRadialLipschitzLSI

/-! # Both concrete functional inequalities for nonquadratic potentials -/

@[expose] public section
namespace GinibrePoincare
noncomputable section

theorem fullNonQuadraticPotentialTheorem (n : ℕ) (hn : 0 < n) :
    NonQuadraticPotentialTheorem n := by
  constructor
  · intro V ρ hV hrot hfin hρ hsub f hf
    exact rhoSubharmonic_potential_smooth_poincare hn hV hrot hfin ρ hρ hsub f hf
  · intro V ρ hV hrot hfin hρ hconv f hf hr
    simpa only [mul_comm (n : ℝ) ρ] using
      bakryEmery_potential_smooth_radial_lsi n hn ρ hρ hV hrot hconv f hf hr

end
end GinibrePoincare
