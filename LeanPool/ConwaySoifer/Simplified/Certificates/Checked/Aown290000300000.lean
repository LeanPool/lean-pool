/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown290000300000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2900003000000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2900003000001
import Mathlib.Tactic.FinCases

/-!
# Aown 290000 300000

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
namespace Aown290000300000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part0 : FanWitness := (.next ([2820000000000], [1410000000000]) (some (5, 2, 4))
    (some (5, 2, 4)) (.next ([2625000000000], [1410000000000]) (some (5, 2, 4)) (some (5, 2, 4))
    (.next ([4020000000000], [3270000000000]) (some (5, 2, 4)) (some (5, 3, 4)) (.next
    ([555000000000], [555000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([555000000000],
    [750000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([1515000000000], [3360000000000])
    (some (5, 3, 4)) (some (5, 3, 4)) (.next ([960000000000], [4470000000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([765000000000], [4665000000000]) (some (0, 3, 4)) (some (0, 3, 4))
    (.next ([480000000000], [4500000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([0],
    [195000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-570000000000], [5835000000000])
    (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-855000000000], [4785000000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([-960000000000], [3750000000000]) (some (0, 3, 4)) (some (0, 3, 4))
    (.next ([-1680000000000], [6390000000000]) (some (0, 3, 4)) (some (0, 3, 5)) (.next
    ([-1875000000000], [6390000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1410000000000],
    [4230000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1410000000000], [4035000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-3270000000000], [7290000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-555000000000], [1110000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([-750000000000], [1305000000000]) (some (0, 3, 5)) (some (1, 3, 5)) (.next
    ([-3360000000000], [4875000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-4470000000000],
    [5430000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-4665000000000], [5430000000000])
    (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-4500000000000], [4980000000000]) (some (1, 3, 5))
    (some (1, 3, 5)) (.terminal (some (1, 3, 5)) (some (1, 4, 5)) (some (1, 4,
    5)))))))))))))))))))))))))))

private theorem initial : initModel Data.Aown290000300000.case Data.Aown290000300000.lo
    Data.Aown290000300000.hi Data.Aown290000300000.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded15_0 : ExcludedOn (model15.B 0) 9000000000000 (model15.caps 0) (model15.ord 0) 0 1
    100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5265000000000], [570000000000]) (some (5, 1, 4))
      (some (5, 2, 4)) (.next ([3930000000000], [855000000000]) (some (5, 2, 4)) (some (5, 2, 4))
      (.next ([2790000000000], [960000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([4710000000000], [1680000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([4515000000000],
      [1875000000000]) (some (5, 2, 4)) (some (5, 2, 4)) fan15Owner0Part0)))))) (den :=
      9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

private theorem tail15 : ModelImpossible model15 9000000000000 0 1 100 :=
  final_checkpoint model15 9000000000000 0 1 100 0 excluded15_0
private theorem tail14 : ModelImpossible model14 9000000000000 0 1 100 :=
  replay_checkpoint model14 model15 9000000000000 0 1 100 step14 next14 checked14 tail15
private theorem tail13 : ModelImpossible model13 9000000000000 0 1 100 :=
  replay_checkpoint model13 model14 9000000000000 0 1 100 step13 next13 checked13 tail14
private theorem tail12 : ModelImpossible model12 9000000000000 0 1 100 :=
  replay_checkpoint model12 model13 9000000000000 0 1 100 step12 next12 checked12 tail13
private theorem tail11 : ModelImpossible model11 9000000000000 0 1 100 :=
  replay_checkpoint model11 model12 9000000000000 0 1 100 step11 next11 checked11 tail12
private theorem tail10 : ModelImpossible model10 9000000000000 0 1 100 :=
  replay_checkpoint model10 model11 9000000000000 0 1 100 step10 next10 checked10 tail11
private theorem tail9 : ModelImpossible model9 9000000000000 0 1 100 :=
  replay_checkpoint model9 model10 9000000000000 0 1 100 step9 next9 checked9 tail10
private theorem tail8 : ModelImpossible model8 9000000000000 0 1 100 :=
  replay_checkpoint model8 model9 9000000000000 0 1 100 step8 next8 checked8 tail9
private theorem tail7 : ModelImpossible model7 9000000000000 0 1 100 :=
  replay_checkpoint model7 model8 9000000000000 0 1 100 step7 next7 checked7 tail8
private theorem tail6 : ModelImpossible model6 9000000000000 0 1 100 :=
  replay_checkpoint model6 model7 9000000000000 0 1 100 step6 next6 checked6 tail7
private theorem tail5 : ModelImpossible model5 9000000000000 0 1 100 :=
  replay_checkpoint model5 model6 9000000000000 0 1 100 step5 next5 checked5 tail6
private theorem tail4 : ModelImpossible model4 9000000000000 0 1 100 :=
  replay_checkpoint model4 model5 9000000000000 0 1 100 step4 next4 checked4 tail5
private theorem tail3 : ModelImpossible model3 9000000000000 0 1 100 :=
  replay_checkpoint model3 model4 9000000000000 0 1 100 step3 next3 checked3 tail4
private theorem tail2 : ModelImpossible model2 9000000000000 0 1 100 :=
  replay_checkpoint model2 model3 9000000000000 0 1 100 step2 next2 checked2 tail3
private theorem tail1 : ModelImpossible model1 9000000000000 0 1 100 :=
  replay_checkpoint model1 model2 9000000000000 0 1 100 step1 next1 checked1 tail2
private theorem tail0 : ModelImpossible model0 9000000000000 0 1 100 :=
  replay_checkpoint model0 model1 9000000000000 0 1 100 step0 next0 checked0 tail1
end Aown290000300000

theorem Aown_290000_300000_checked : Data.Aown290000300000.Valid := by
  apply certificate_checkpoint Data.Aown290000300000 Aown290000300000.model0 9000000000000 1 100
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown290000300000.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown290000300000.tail0

end ConwaySoifer.Simplified.Certificates
