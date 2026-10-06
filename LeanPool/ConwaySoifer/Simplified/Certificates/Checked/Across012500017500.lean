/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across012500017500
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Across0125000175000
import Mathlib.Tactic.FinCases

/-!
# Across 012500 017500

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
namespace Across012500017500

private theorem initial : initModel Data.Across012500017500.case Data.Across012500017500.lo
    Data.Across012500017500.hi Data.Across012500017500.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded6_6 : ExcludedOn (model6.B 6) 9000000000000 (model6.caps 6) (model6.ord 6) 0 1 200
    := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000], [187500000000]) (some (4, 1, 2))
      (some (4, 1, 3)) (.next ([112500000000, 9000000000000], [112500000000, 9000000000000]) (some
      (0, 1, 3)) (some (0, 1, 3)) (.next ([3075000000000, 9000000000000], [5887500000000,
      -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2962500000000], [6000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2850000000000, -9000000000000], [6000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([262500000000, 9000000000000], [8512500000000,
      -9000000000000]) (some (0, 1, 3)) (some (0, 1, 4)) (.next ([150000000000], [8625000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([37500000000, -9000000000000], [8625000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-187500000000], [2812500000000]) (some (0, 1, 4))
      (some (0, 2, 4)) (.next ([-112500000000, -9000000000000], [225000000000, 18000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-5887500000000, 9000000000000], [8962500000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6000000000000], [8962500000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-6000000000000], [8850000000000, -9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-8512500000000, 9000000000000], [8775000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-8625000000000], [8775000000000]) (some (0, 2, 4)) (some (1, 2, 4))
      (.terminal (some (1, 2, 4)) (some (1, 2, 4)) (some (1, 2, 4))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

private theorem tail6 : ModelImpossible model6 9000000000000 0 1 200 :=
  final_checkpoint model6 9000000000000 0 1 200 6 excluded6_6
private theorem tail5 : ModelImpossible model5 9000000000000 0 1 200 :=
  replay_checkpoint model5 model6 9000000000000 0 1 200 step5 next5 checked5 tail6
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
end Across012500017500

theorem Across_012500_017500_checked : Data.Across012500017500.Valid := by
  apply certificate_checkpoint Data.Across012500017500 Across012500017500.model0 9000000000000 1
      200
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across012500017500.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across012500017500.tail0

end ConwaySoifer.Simplified.Certificates
