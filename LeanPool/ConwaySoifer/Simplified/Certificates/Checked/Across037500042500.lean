/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across037500042500
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Across0375000425000
import Mathlib.Tactic.FinCases

/-!
# Across 037500 042500

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
namespace Across037500042500

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan6Owner0Part0 : FanWitness := (.next ([8615437500000, 5745000000000], [267281250000,
    -2872500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([8507718750000, 2872500000000],
    [482718750000, 2872500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([8292281250000,
    -2872500000000], [590437500000, 5745000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
    ([7706250000000], [787500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([7921687500000,
    5745000000000], [1017281250000, -2872500000000]) (some (4, 1, 3)) (some (5, 1, 3)) (.next
    ([7813968750000, 2872500000000], [1232718750000, 2872500000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([7598531250000, -2872500000000], [1340437500000, 5745000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([445218750000, 2872500000000], [107718750000, 2872500000000]) (some (5,
    1, 3)) (some (5, 1, 3)) (.next ([215437500000, 5745000000000], [229781250000, -2872500000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([107718750000, 2872500000000], [445218750000,
    2872500000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([56250000000], [693750000000]) (some
    (0, 2, 3)) (some (0, 2, 3)) (.next ([0, 0], [323156250000, 8617500000000]) (some (0, 2, 3))
    (some (0, 2, 4)) (.next ([-37500000000], [8437500000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-267281250000, 2872500000000], [8882718750000, 2872500000000]) (some (0, 2, 4)) (some
    (0, 2, 4)) (.next ([-482718750000, -2872500000000], [8990437500000, 5745000000000]) (some (0, 2,
    4)) (some (0, 2, 4)) (.next ([-590437500000, -5745000000000], [8882718750000, 2872500000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-787500000000], [8493750000000]) (some (0, 2, 4))
    (some (0, 3, 4)) (.next ([-1017281250000, 2872500000000], [8938968750000, 2872500000000]) (some
    (0, 3, 4)) (some (0, 3, 4)) (.next ([-1232718750000, -2872500000000], [9046687500000,
    5745000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-1340437500000, -5745000000000],
    [8938968750000, 2872500000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-107718750000,
    -2872500000000], [552937500000, 5745000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
    ([-229781250000, 2872500000000], [445218750000, 2872500000000]) (some (0, 3, 4)) (some (0, 3,
    4)) (.next ([-445218750000, -2872500000000], [552937500000, 5745000000000]) (some (0, 3, 4))
    (some (1, 3, 4)) (.next ([-693750000000], [750000000000]) (some (1, 3, 4)) (some (1, 3, 4))
    (.terminal (some (1, 3, 4)) (some (1, 3, 4)) (some (1, 3, 4)))))))))))))))))))))))))))

private theorem initial : initModel Data.Across037500042500.case Data.Across037500042500.lo
    Data.Across037500042500.hi Data.Across037500042500.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded6_0 : ExcludedOn (model6.B 0) 9000000000000 (model6.caps 0) (model6.ord 0) 0 1 200
    := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8400000000000], [37500000000]) (some (4, 1, 3))
      (some (4, 1, 3)) fan6Owner0Part0)) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200
      (by decide +kernel)
  decide +kernel

private theorem tail6 : ModelImpossible model6 9000000000000 0 1 200 :=
  final_checkpoint model6 9000000000000 0 1 200 0 excluded6_0
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
end Across037500042500

theorem Across_037500_042500_checked : Data.Across037500042500.Valid := by
  apply certificate_checkpoint Data.Across037500042500 Across037500042500.model0 9000000000000 1
      200
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across037500042500.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across037500042500.tail0

end ConwaySoifer.Simplified.Certificates
