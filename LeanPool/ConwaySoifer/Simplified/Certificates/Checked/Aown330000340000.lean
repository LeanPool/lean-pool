/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown330000340000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown3300003400000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown3300003400001
import Mathlib.Tactic.FinCases

/-!
# Aown 330000 340000

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
namespace Aown330000340000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part0 : FanWitness := (.next ([4404000000000], [2706000000000]) (some (5, 2, 4))
    (some (5, 2, 4)) (.next ([2055000000000], [1485000000000]) (some (5, 2, 4)) (some (5, 2, 4))
    (.next ([375000000000], [360000000000]) (some (5, 2, 4)) (some (5, 3, 4)) (.next
    ([735000000000], [735000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([360000000000],
    [375000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([1656000000000], [4440000000000])
    (some (5, 3, 4)) (some (5, 3, 4)) (.next ([1296000000000], [5175000000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([864000000000], [4761000000000]) (some (0, 3, 4)) (some (0, 3, 4))
    (.next ([921000000000], [5910000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
    ([-279000000000], [3483000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-750000000000],
    [4275000000000]) (some (0, 3, 4)) (some (0, 3, 5)) (.next ([-1236000000000], [6375000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1125000000000], [3915000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-1971000000000], [6750000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([-2619000000000], [7965000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-2706000000000], [7110000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1485000000000],
    [3540000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-360000000000], [735000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-735000000000], [1470000000000]) (some (0, 3, 5))
    (some (1, 3, 5)) (.next ([-375000000000], [735000000000]) (some (1, 3, 5)) (some (1, 3, 5))
    (.next ([-4440000000000], [6096000000000]) (some (1, 3, 5)) (some (2, 3, 5)) (.next
    ([-5175000000000], [6471000000000]) (some (2, 3, 5)) (some (2, 3, 5)) (.next ([-4761000000000],
    [5625000000000]) (some (2, 3, 5)) (some (2, 3, 5)) (.next ([-5910000000000], [6831000000000])
    (some (2, 3, 5)) (some (2, 4, 5)) (.terminal (some (2, 4, 5)) (some (2, 4, 5)) (some (2, 4,
    5)))))))))))))))))))))))))))

private theorem initial : initModel Data.Aown330000340000.case Data.Aown330000340000.lo
    Data.Aown330000340000.hi Data.Aown330000340000.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded14_0 : ExcludedOn (model14.B 0) 9000000000000 (model14.caps 0) (model14.ord 0) 0 1
    100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3204000000000], [279000000000]) (some (5, 2, 4))
      (some (5, 2, 4)) (.next ([3525000000000], [750000000000]) (some (5, 2, 4)) (some (5, 2, 4))
      (.next ([5139000000000], [1236000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([2790000000000], [1125000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([4779000000000],
      [1971000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([5346000000000], [2619000000000])
      (some (5, 2, 4)) (some (5, 2, 4)) fan14Owner0Part0))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

private theorem tail14 : ModelImpossible model14 9000000000000 0 1 100 :=
  final_checkpoint model14 9000000000000 0 1 100 0 excluded14_0
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
end Aown330000340000

theorem Aown_330000_340000_checked : Data.Aown330000340000.Valid := by
  apply certificate_checkpoint Data.Aown330000340000 Aown330000340000.model0 9000000000000 1 100
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown330000340000.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown330000340000.tail0

end ConwaySoifer.Simplified.Certificates
