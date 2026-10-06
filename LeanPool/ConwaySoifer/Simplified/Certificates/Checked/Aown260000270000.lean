/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown260000270000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2600002700000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2600002700001
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2600002700002
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2600002700003
import Mathlib.Tactic.FinCases

/-!
# Aown 260000 270000

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
namespace Aown260000270000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner0Part0 : FanWitness := (.next ([-1788000000000], [7170000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-1725000000000], [6420000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-375000000000], [1170000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-2538000000000], [7545000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-735000000000],
    [1920000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-2958000000000], [7545000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-525000000000], [1335000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-2490000000000], [5685000000000]) (some (0, 3, 6)) (some (0, 3, 7))
    (.next ([-735000000000], [1500000000000]) (some (0, 3, 7)) (some (0, 4, 7)) (.next
    ([-375000000000], [750000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next ([-3723000000000],
    [6810000000000]) (some (0, 4, 7)) (some (1, 4, 7)) (.next ([-4020000000000], [6750000000000])
    (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-4440000000000], [7170000000000]) (some (1, 4, 7))
    (some (1, 4, 7)) (.next ([-795000000000], [1170000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-5190000000000], [7545000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-2760000000000], [3885000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-5610000000000],
    [7545000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-4830000000000], [6225000000000])
    (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-5250000000000], [6645000000000]) (some (1, 4, 7))
    (some (1, 4, 7)) (.next ([-6000000000000], [7020000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-4095000000000], [4695000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-6420000000000], [7020000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-6375000000000],
    [6810000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-2295000000000], [2355000000000])
    (some (1, 4, 7)) (some (1, 4, 7)) (.terminal (some (1, 4, 7)) (some (1, 4, 7)) (some (1, 4,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner0Part1 : FanWitness := (.next ([375000000000], [375000000000]) (some (7, 2, 5)) (some
    (7, 3, 5)) (.next ([3087000000000], [3723000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([2730000000000], [4020000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([2730000000000],
    [4440000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([375000000000], [795000000000]) (some
    (7, 3, 5)) (some (7, 3, 5)) (.next ([2355000000000], [5190000000000]) (some (7, 3, 5)) (some (7,
    3, 5)) (.next ([1125000000000], [2760000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([1935000000000], [5610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([1395000000000],
    [4830000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([1395000000000], [5250000000000])
    (some (7, 3, 5)) (some (8, 3, 5)) (.next ([1020000000000], [6000000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([600000000000], [4095000000000]) (some (8, 3, 5)) (some (8, 3, 5))
    (.next ([600000000000], [6420000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next
    ([435000000000], [6375000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([60000000000],
    [2295000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([0], [420000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-135000000000], [5625000000000]) (some (0, 3, 5)) (some (0, 3, 6))
    (.next ([-108000000000], [1233000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-555000000000], [6045000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-900000000000],
    [7185000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-525000000000], [3987000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-360000000000], [2295000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-1368000000000], [6750000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-1305000000000], [6420000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    fan25Owner0Part0))))))))))))))))))))))))

private theorem initial : initModel Data.Aown260000270000.case Data.Aown260000270000.lo
    Data.Aown260000270000.hi Data.Aown260000270000.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded25_0 : ExcludedOn (model25.B 0) 9000000000000 (model25.caps 0) (model25.ord 0) 0 1
    100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5490000000000], [135000000000]) (some (7, 1, 4))
      (some (7, 2, 4)) (.next ([1125000000000], [108000000000]) (some (7, 2, 4)) (some (7, 2, 4))
      (.next ([5490000000000], [555000000000]) (some (7, 2, 4)) (some (7, 2, 5)) (.next
      ([6285000000000], [900000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([3462000000000],
      [525000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([1935000000000], [360000000000])
      (some (7, 2, 5)) (some (7, 2, 5)) (.next ([5382000000000], [1368000000000]) (some (7, 2, 5))
      (some (7, 2, 5)) (.next ([5115000000000], [1305000000000]) (some (7, 2, 5)) (some (7, 2, 5))
      (.next ([5382000000000], [1788000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
      ([4695000000000], [1725000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([795000000000],
      [375000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([5007000000000], [2538000000000])
      (some (7, 2, 5)) (some (7, 2, 5)) (.next ([1185000000000], [735000000000]) (some (7, 2, 5))
      (some (7, 2, 5)) (.next ([4587000000000], [2958000000000]) (some (7, 2, 5)) (some (7, 2, 5))
      (.next ([810000000000], [525000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
      ([3195000000000], [2490000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([765000000000],
      [735000000000]) (some (7, 2, 5)) (some (7, 2, 5)) fan25Owner0Part1)))))))))))))))))) (den :=
      9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

private theorem tail25 : ModelImpossible model25 9000000000000 0 1 100 :=
  final_checkpoint model25 9000000000000 0 1 100 0 excluded25_0
private theorem tail24 : ModelImpossible model24 9000000000000 0 1 100 :=
  replay_checkpoint model24 model25 9000000000000 0 1 100 step24 next24 checked24 tail25
private theorem tail23 : ModelImpossible model23 9000000000000 0 1 100 :=
  replay_checkpoint model23 model24 9000000000000 0 1 100 step23 next23 checked23 tail24
private theorem tail22 : ModelImpossible model22 9000000000000 0 1 100 :=
  replay_checkpoint model22 model23 9000000000000 0 1 100 step22 next22 checked22 tail23
private theorem tail21 : ModelImpossible model21 9000000000000 0 1 100 :=
  replay_checkpoint model21 model22 9000000000000 0 1 100 step21 next21 checked21 tail22
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
end Aown260000270000

theorem Aown_260000_270000_checked : Data.Aown260000270000.Valid := by
  apply certificate_checkpoint Data.Aown260000270000 Aown260000270000.model0 9000000000000 1 100
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown260000270000.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown260000270000.tail0

end ConwaySoifer.Simplified.Certificates
