/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

module

public import LeanPool.LatticeDiracDerivation.V35CompleteCovariantObservables

/-!
# Free Dirac covariance and observables from a reciprocal C19 lattice action

Source: url:https://github.com/gpartin/LeanDiracDerivation/tree/43859849eb6ed37e16c802fbae3fd50dd731665c
Authors: G. D. Partin
Status: verified
Main declarations: `LeanDirac.V2.v35_complete_covariant_observables`,
  `LeanDirac.V2.v35_antiparticle_spin_sum_is_negative_pole`,
  `LeanDirac.V2.v35_lorentz_word_covariant`, `LeanDirac.V2.v35_lorentz_word_preserves_solutions`,
  `LeanDirac.V2.v35_fierz_completeness`, `LeanDirac.V2.v35_on_shell_pauli_lubanski_spin_half`,
  `LeanDirac.V2.v35_helicity_is_normalized_pauli_lubanski_time`,
  `LeanDirac.V2.v32_no_global_exact_local_oriented_root`,
  `LeanDirac.V2.v32_absolute_energy_scale_not_selected`
Tags: mathematical-physics, dirac-operator, clifford-algebra, lattice, fourier-analysis
MSC: 81Q05, 15A66, 65M06, 81R20
-/

/-
MIT License

Copyright (c) 2026 G. D. Partin

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
