/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown270000280000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2700002800000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2700002800001
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2700002800002
import Mathlib.Tactic.FinCases

/-!
# Aown 270000 280000

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
namespace Aown270000280000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner0Part0 : FanWitness := (.next ([-1965000000000], [6930000000000]) (some (0, 5, 7))
    (some (0, 5, 7)) (.next ([-750000000000], [2625000000000]) (some (0, 5, 7)) (some (0, 5, 7))
    (.next ([-2430000000000], [7185000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next
    ([-465000000000], [1215000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next ([-2895000000000],
    [7395000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next ([-960000000000], [2370000000000])
    (some (0, 5, 7)) (some (0, 5, 7)) (.next ([-3180000000000], [7395000000000]) (some (0, 5, 7))
    (some (0, 5, 7)) (.next ([-210000000000], [465000000000]) (some (0, 5, 7)) (some (0, 5, 7))
    (.next ([-960000000000], [2085000000000]) (some (0, 5, 7)) (some (1, 5, 7)) (.next
    ([-750000000000], [1620000000000]) (some (1, 5, 7)) (some (1, 5, 7)) (.next ([-3435000000000],
    [7185000000000]) (some (1, 5, 7)) (some (1, 5, 7)) (.next ([-465000000000], [930000000000])
    (some (1, 5, 7)) (some (1, 5, 7)) (.next ([-255000000000], [465000000000]) (some (1, 5, 7))
    (some (1, 5, 7)) (.next ([-750000000000], [1215000000000]) (some (1, 5, 7)) (some (2, 5, 7))
    (.next ([-4305000000000], [6435000000000]) (some (2, 5, 7)) (some (2, 5, 7)) (.next
    ([-1215000000000], [1755000000000]) (some (2, 5, 7)) (some (2, 6, 7)) (.next ([-540000000000],
    [750000000000]) (some (2, 6, 7)) (some (2, 6, 7)) (.next ([-4605000000000], [6090000000000])
    (some (2, 6, 7)) (some (2, 6, 7)) (.next ([-4890000000000], [6375000000000]) (some (2, 6, 7))
    (some (2, 6, 7)) (.next ([-5355000000000], [6630000000000]) (some (2, 6, 7)) (some (2, 6, 7))
    (.next ([-1215000000000], [1470000000000]) (some (2, 6, 7)) (some (2, 6, 7)) (.next
    ([-5820000000000], [6840000000000]) (some (2, 6, 7)) (some (2, 6, 7)) (.next ([-6105000000000],
    [6840000000000]) (some (2, 6, 7)) (some (2, 6, 7)) (.next ([-6360000000000], [6630000000000])
    (some (2, 6, 7)) (some (2, 6, 7)) (.terminal (some (2, 6, 7)) (some (2, 6, 7)) (some (2, 6,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner0Part1 : FanWitness := (.next ([255000000000], [210000000000]) (some (7, 3, 6)) (some
    (7, 3, 6)) (.next ([1125000000000], [960000000000]) (some (7, 3, 6)) (some (7, 4, 6)) (.next
    ([870000000000], [750000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([3750000000000],
    [3435000000000]) (some (7, 4, 6)) (some (7, 5, 6)) (.next ([465000000000], [465000000000]) (some
    (7, 5, 6)) (some (7, 5, 6)) (.next ([210000000000], [255000000000]) (some (7, 5, 6)) (some (7,
    5, 6)) (.next ([465000000000], [750000000000]) (some (7, 5, 6)) (some (7, 5, 6)) (.next
    ([2130000000000], [4305000000000]) (some (7, 5, 6)) (some (7, 5, 6)) (.next ([540000000000],
    [1215000000000]) (some (7, 5, 6)) (some (7, 5, 6)) (.next ([210000000000], [540000000000]) (some
    (7, 5, 6)) (some (7, 5, 6)) (.next ([1485000000000], [4605000000000]) (some (7, 5, 6)) (some (7,
    5, 6)) (.next ([1485000000000], [4890000000000]) (some (7, 5, 6)) (some (8, 5, 6)) (.next
    ([1275000000000], [5355000000000]) (some (8, 5, 6)) (some (8, 5, 6)) (.next ([255000000000],
    [1215000000000]) (some (8, 5, 6)) (some (8, 5, 6)) (.next ([1020000000000], [5820000000000])
    (some (8, 5, 6)) (some (8, 5, 6)) (.next ([735000000000], [6105000000000]) (some (8, 5, 6))
    (some (8, 5, 6)) (.next ([270000000000], [6360000000000]) (some (8, 5, 6)) (some (8, 5, 6))
    (.next ([0], [285000000000]) (some (8, 5, 6)) (some (8, 5, 6)) (.next ([-210000000000],
    [2835000000000]) (some (0, 5, 6)) (some (0, 5, 6)) (.next ([-555000000000], [3480000000000])
    (some (0, 5, 6)) (some (0, 5, 6)) (.next ([-495000000000], [2835000000000]) (some (0, 5, 6))
    (some (0, 5, 7)) (.next ([-1350000000000], [7230000000000]) (some (0, 5, 7)) (some (0, 5, 7))
    (.next ([-1680000000000], [6645000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next
    ([-210000000000], [750000000000]) (some (0, 5, 7)) (some (0, 5, 7))
    fan21Owner0Part0))))))))))))))))))))))))

private theorem initial : initModel Data.Aown270000280000.case Data.Aown270000280000.lo
    Data.Aown270000280000.hi Data.Aown270000280000.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0) 9000000000000 (model21.caps 0) (model21.ord 0) 0 1
    100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000], [210000000000]) (some (7, 2, 6))
      (some (7, 3, 6)) (.next ([2925000000000], [555000000000]) (some (7, 3, 6)) (some (7, 3, 6))
      (.next ([2340000000000], [495000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next
      ([5880000000000], [1350000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([4965000000000],
      [1680000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([540000000000], [210000000000])
      (some (7, 3, 6)) (some (7, 3, 6)) (.next ([4965000000000], [1965000000000]) (some (7, 3, 6))
      (some (7, 3, 6)) (.next ([1875000000000], [750000000000]) (some (7, 3, 6)) (some (7, 3, 6))
      (.next ([4755000000000], [2430000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next
      ([750000000000], [465000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([4500000000000],
      [2895000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([1410000000000], [960000000000])
      (some (7, 3, 6)) (some (7, 3, 6)) (.next ([4215000000000], [3180000000000]) (some (7, 3, 6))
      (some (7, 3, 6)) fan21Owner0Part1)))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

private theorem tail21 : ModelImpossible model21 9000000000000 0 1 100 :=
  final_checkpoint model21 9000000000000 0 1 100 0 excluded21_0
private theorem tail20 : ModelImpossible model20 9000000000000 0 1 100 :=
  replay_checkpoint model20 model21 9000000000000 0 1 100 step20 next20 checked20 tail21
private theorem tail19 : ModelImpossible model19 9000000000000 0 1 100 :=
  replay_checkpoint model19 model20 9000000000000 0 1 100 step19 next19 checked19 tail20
private theorem tail18 : ModelImpossible model18 9000000000000 0 1 100 :=
  replay_checkpoint model18 model19 9000000000000 0 1 100 step18 next18 checked18 tail19
private theorem tail17 : ModelImpossible model17 9000000000000 0 1 100 :=
  replay_checkpoint model17 model18 9000000000000 0 1 100 step17 next17 checked17 tail18
private theorem tail16 : ModelImpossible model16 9000000000000 0 1 100 :=
  replay_checkpoint model16 model17 9000000000000 0 1 100 step16 next16 checked16 tail17
private theorem tail15 : ModelImpossible model15 9000000000000 0 1 100 :=
  replay_checkpoint model15 model16 9000000000000 0 1 100 step15 next15 checked15 tail16
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
end Aown270000280000

theorem Aown_270000_280000_checked : Data.Aown270000280000.Valid := by
  apply certificate_checkpoint Data.Aown270000280000 Aown270000280000.model0 9000000000000 1 100
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown270000280000.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown270000280000.tail0

end ConwaySoifer.Simplified.Certificates
