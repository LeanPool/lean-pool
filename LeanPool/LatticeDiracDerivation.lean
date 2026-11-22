/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

module

public import LeanPool.LatticeDiracDerivation.V2

/-!
# Free Dirac dynamics from a reciprocal C19 lattice action

Source: url:https://github.com/gpartin/LeanDiracDerivation/tree/9522a8d32f51e79f57fcf16e85f214a7d88b1ff2
Authors: G. D. Partin
Status: verified
Main declarations: `LeanDirac.V2.complete_first_principles_free_dirac`,
  `LeanDirac.V2.cubical_flavor_classification`,
  `LeanDirac.V2.periodic_quantized_add_char_bijective`,
  `LeanDirac.V2.periodic_integrated_positive_packet_current_bridge`,
  `LeanDirac.V2.positive_packet_pointwise_bridge_is_false`
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
