/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown310000320000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown3100003200000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown3100003200001
import Mathlib.Tactic.FinCases

/-!
# Aown 310000 320000

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
namespace Aown310000320000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part0 : FanWitness := (.next ([-420000000000], [3420000000000]) (some (0, 4, 5))
    (some (0, 4, 6)) (.next ([-897000000000], [6270000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    (.next ([-525000000000], [3420000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-1002000000000], [6375000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1647000000000],
    [6705000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1872000000000], [7272000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-855000000000], [3105000000000]) (some (0, 4, 6))
    (some (0, 4, 6)) (.next ([-2292000000000], [7020000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    (.next ([-2727000000000], [6705000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-315000000000], [750000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1170000000000],
    [2775000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-855000000000], [2025000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-645000000000], [1395000000000]) (some (0, 4, 6))
    (some (0, 4, 6)) (.next ([-315000000000], [645000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    (.next ([-645000000000], [1290000000000]) (some (0, 4, 6)) (some (1, 4, 6)) (.next
    ([-330000000000], [645000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-3897000000000],
    [5850000000000]) (some (1, 4, 6)) (some (2, 4, 6)) (.next ([-4272000000000], [5820000000000])
    (some (2, 4, 6)) (some (2, 5, 6)) (.next ([-4377000000000], [5925000000000]) (some (2, 5, 6))
    (some (2, 5, 6)) (.next ([-1395000000000], [1830000000000]) (some (2, 5, 6)) (some (2, 5, 6))
    (.next ([-5022000000000], [6255000000000]) (some (2, 5, 6)) (some (2, 5, 6)) (.next
    ([-1395000000000], [1725000000000]) (some (2, 5, 6)) (some (2, 5, 6)) (.next ([-5667000000000],
    [6570000000000]) (some (2, 5, 6)) (some (2, 5, 6)) (.next ([-6102000000000], [6255000000000])
    (some (2, 5, 6)) (some (2, 5, 6)) (.terminal (some (2, 5, 6)) (some (2, 5, 6)) (some (2, 5,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part1 : FanWitness := (.next ([2895000000000], [525000000000]) (some (6, 2, 5)) (some
    (6, 2, 5)) (.next ([5373000000000], [1002000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next
    ([5058000000000], [1647000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([5400000000000],
    [1872000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([2250000000000], [855000000000])
    (some (6, 2, 5)) (some (6, 2, 5)) (.next ([4728000000000], [2292000000000]) (some (6, 2, 5))
    (some (6, 2, 5)) (.next ([3978000000000], [2727000000000]) (some (6, 2, 5)) (some (6, 2, 5))
    (.next ([435000000000], [315000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next
    ([1605000000000], [1170000000000]) (some (6, 2, 5)) (some (6, 3, 5)) (.next ([1170000000000],
    [855000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([750000000000], [645000000000]) (some
    (6, 3, 5)) (some (6, 4, 5)) (.next ([330000000000], [315000000000]) (some (6, 4, 5)) (some (6,
    4, 5)) (.next ([645000000000], [645000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([315000000000], [330000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([1953000000000],
    [3897000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([1548000000000], [4272000000000])
    (some (6, 4, 5)) (some (6, 4, 5)) (.next ([1548000000000], [4377000000000]) (some (6, 4, 5))
    (some (7, 4, 5)) (.next ([435000000000], [1395000000000]) (some (7, 4, 5)) (some (7, 4, 5))
    (.next ([1233000000000], [5022000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next
    ([330000000000], [1395000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([903000000000],
    [5667000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([153000000000], [6102000000000])
    (some (7, 4, 5)) (some (7, 4, 5)) (.next ([0], [105000000000]) (some (7, 4, 5)) (some (7, 4, 5))
    (.next ([-450000000000], [3825000000000]) (some (0, 4, 5)) (some (0, 4, 5))
    fan15Owner0Part0))))))))))))))))))))))))

private theorem initial : initModel Data.Aown310000320000.case Data.Aown310000320000.lo
    Data.Aown310000320000.hi Data.Aown310000320000.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded15_0 : ExcludedOn (model15.B 0) 9000000000000 (model15.caps 0) (model15.ord 0) 0 1
    100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [450000000000]) (some (6, 2, 5))
      (some (6, 2, 5)) (.next ([3000000000000], [420000000000]) (some (6, 2, 5)) (some (6, 2, 5))
      (.next ([5373000000000], [897000000000]) (some (6, 2, 5)) (some (6, 2, 5))
      fan15Owner0Part1))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
end Aown310000320000

theorem Aown_310000_320000_checked : Data.Aown310000320000.Valid := by
  apply certificate_checkpoint Data.Aown310000320000 Aown310000320000.model0 9000000000000 1 100
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown310000320000.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown310000320000.tail0

end ConwaySoifer.Simplified.Certificates
