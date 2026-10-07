/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across072500077500
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Across0725000775000
import Mathlib.Tactic.FinCases

/-!
# Across 072500 077500

Kernel-checked forced assignments and closed-interval exclusions.
-/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

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

@[expose] public section

-- Generated checkpoints are proposals; all acceptance proofs are checked by the kernel.

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Across072500077500

private theorem initial : initModel Data.Across072500077500.case Data.Across072500077500.lo
    Data.Across072500077500.hi Data.Across072500077500.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded5_1 : ExcludedOn (model5.B 1) 9000000000000 (model5.caps 1) (model5.ord 1) 0 1 200
    := by
  apply ExclusionHint.sound (.witnessedFan (.next ([652500000000, 9000000000000], [652500000000,
      9000000000000]) none none (.next ([157500000000, -9000000000000], [217500000000,
      9000000000000]) none none (.next ([277500000000, 9000000000000], [810000000000]) none none
      (.next ([810000000000], [2730000000000]) none none (.next ([652500000000, 9000000000000],
      [2512500000000, -9000000000000]) none none (.next ([0], [3817500000000, 9000000000000]) none
      none (.next ([-652500000000, -9000000000000], [1305000000000, 18000000000000]) none none
      (.next ([-217500000000, -9000000000000], [375000000000, 0]) none none (.next ([-810000000000],
      [1087500000000, 9000000000000]) none none (.next ([-2730000000000], [3540000000000]) none none
      (.next ([-2512500000000, 9000000000000], [3165000000000, 0]) none none (.terminal none none
      none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
  decide +kernel

private theorem tail5 : ModelImpossible model5 9000000000000 0 1 200 :=
  final_checkpoint model5 9000000000000 0 1 200 1 excluded5_1
private theorem tail4 : ModelImpossible model4 9000000000000 0 1 200 :=
  replay_checkpoint model4 model5 9000000000000 0 1 200 step4 next4 checked4 tail5
private theorem tail3 : ModelImpossible model3 9000000000000 0 1 200 :=
  replay_checkpoint model3 model4 9000000000000 0 1 200 step3 next3 checked3 tail4
private theorem tail2 : ModelImpossible model2 9000000000000 0 1 200 :=
  replay_checkpoint model2 model3 9000000000000 0 1 200 step2 next2 checked2 tail3
private theorem tail1 : ModelImpossible model1 9000000000000 0 1 200 :=
  replay_checkpoint model1 model2 9000000000000 0 1 200 step1 next1 checked1 tail2
private theorem tail0 : ModelImpossible model0 9000000000000 0 1 200 :=
  replay_checkpoint model0 model1 9000000000000 0 1 200 step0 next0 checked0 tail1
end Across072500077500

theorem Across_072500_077500_checked : Data.Across072500077500.Valid := by
  apply certificate_checkpoint Data.Across072500077500 Across072500077500.model0 9000000000000 1
      200
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across072500077500.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across072500077500.tail0

end ConwaySoifer.Simplified.Certificates
