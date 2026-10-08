/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown240000250000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2400002500000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2400002500001
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2400002500002
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2400002500003
import Mathlib.Tactic.FinCases

/-!
# Aown 240000 250000

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
namespace Aown240000250000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner0Part0 : FanWitness := (.next ([-405000000000], [1125000000000]) (some (0, 6, 8))
    (some (0, 6, 8)) (.next ([-195000000000], [405000000000]) (some (0, 6, 8)) (some (0, 6, 8))
    (.next ([-405000000000], [810000000000]) (some (0, 6, 8)) (some (1, 6, 8)) (.next
    ([-210000000000], [405000000000]) (some (1, 6, 8)) (some (1, 6, 8)) (.next ([-3405000000000],
    [6237000000000]) (some (1, 6, 8)) (some (2, 6, 8)) (.next ([-3720000000000], [6237000000000])
    (some (2, 6, 8)) (some (2, 6, 8)) (.next ([-4752000000000], [7752000000000]) (some (2, 6, 8))
    (some (2, 6, 8)) (.next ([-720000000000], [1125000000000]) (some (2, 6, 8)) (some (2, 6, 8))
    (.next ([-3930000000000], [6042000000000]) (some (2, 6, 8)) (some (2, 6, 8)) (.next
    ([-1125000000000], [1650000000000]) (some (2, 6, 8)) (some (2, 6, 8)) (.next ([-4125000000000],
    [5832000000000]) (some (2, 6, 8)) (some (2, 6, 8)) (.next ([-525000000000], [720000000000])
    (some (2, 6, 8)) (some (2, 6, 8)) (.next ([-4125000000000], [5517000000000]) (some (2, 6, 8))
    (some (2, 6, 8)) (.next ([-4920000000000], [6405000000000]) (some (2, 6, 8)) (some (2, 6, 8))
    (.next ([-3930000000000], [5112000000000]) (some (2, 6, 8)) (some (2, 6, 8)) (.next
    ([-5235000000000], [6720000000000]) (some (2, 6, 8)) (some (2, 6, 8)) (.next ([-3720000000000],
    [4707000000000]) (some (2, 6, 8)) (some (2, 6, 8)) (.next ([-5640000000000], [6930000000000])
    (some (2, 6, 8)) (some (2, 6, 8)) (.next ([-1530000000000], [1845000000000]) (some (2, 6, 8))
    (some (2, 6, 8)) (.next ([-1125000000000], [1335000000000]) (some (2, 6, 8)) (some (2, 6, 8))
    (.next ([-6045000000000], [7125000000000]) (some (2, 6, 8)) (some (2, 6, 8)) (.next
    ([-6360000000000], [7125000000000]) (some (2, 6, 8)) (some (2, 6, 8)) (.next ([-3087000000000],
    [3375000000000]) (some (2, 6, 8)) (some (2, 6, 8)) (.next ([-6570000000000], [6930000000000])
    (some (2, 6, 8)) (some (2, 7, 8)) (.terminal (some (2, 7, 8)) (some (2, 7, 8)) (some (2, 7,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner0Part1 : FanWitness := (.next ([1392000000000], [4125000000000]) (some (8, 5, 7))
    (some (8, 5, 7)) (.next ([1485000000000], [4920000000000]) (some (8, 5, 7)) (some (8, 5, 7))
    (.next ([1182000000000], [3930000000000]) (some (8, 5, 7)) (some (9, 5, 7)) (.next
    ([1485000000000], [5235000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([987000000000],
    [3720000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([1290000000000], [5640000000000])
    (some (9, 5, 7)) (some (9, 6, 7)) (.next ([315000000000], [1530000000000]) (some (9, 6, 7))
    (some (9, 6, 7)) (.next ([210000000000], [1125000000000]) (some (9, 6, 7)) (some (9, 6, 7))
    (.next ([1080000000000], [6045000000000]) (some (9, 6, 7)) (some (9, 6, 7)) (.next
    ([765000000000], [6360000000000]) (some (9, 6, 7)) (some (9, 6, 7)) (.next ([288000000000],
    [3087000000000]) (some (9, 6, 7)) (some (9, 6, 7)) (.next ([360000000000], [6570000000000])
    (some (9, 6, 7)) (some (9, 6, 7)) (.next ([0], [1530000000000]) (some (9, 6, 7)) (some (9, 6,
    7)) (.next ([-45000000000], [6765000000000]) (some (0, 6, 7)) (some (0, 6, 7)) (.next
    ([-255000000000], [6780000000000]) (some (0, 6, 7)) (some (0, 6, 7)) (.next ([-375000000000],
    [5040000000000]) (some (0, 6, 7)) (some (0, 6, 7)) (.next ([-570000000000], [7095000000000])
    (some (0, 6, 7)) (some (0, 6, 8)) (.next ([-975000000000], [7305000000000]) (some (0, 6, 8))
    (some (0, 6, 8)) (.next ([-210000000000], [1335000000000]) (some (0, 6, 8)) (some (0, 6, 8))
    (.next ([-1380000000000], [7500000000000]) (some (0, 6, 8)) (some (0, 6, 8)) (.next
    ([-1695000000000], [7500000000000]) (some (0, 6, 8)) (some (0, 6, 8)) (.next ([-1905000000000],
    [7305000000000]) (some (0, 6, 8)) (some (0, 6, 8)) (.next ([-195000000000], [720000000000])
    (some (0, 6, 8)) (some (0, 6, 8)) (.next ([-2100000000000], [7095000000000]) (some (0, 6, 8))
    (some (0, 6, 8)) fan26Owner0Part0))))))))))))))))))))))))

private theorem initial : initModel Data.Aown240000250000.case Data.Aown240000250000.lo
    Data.Aown240000250000.hi Data.Aown240000250000.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded26_0 : ExcludedOn (model26.B 0) 9000000000000 (model26.caps 0) (model26.ord 0) 0 1
    100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6720000000000], [45000000000]) (some (8, 2, 7))
      (some (8, 3, 7)) (.next ([6525000000000], [255000000000]) (some (8, 3, 7)) (some (8, 3, 7))
      (.next ([4665000000000], [375000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
      ([6525000000000], [570000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([6330000000000],
      [975000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([1125000000000], [210000000000])
      (some (8, 3, 7)) (some (8, 3, 7)) (.next ([6120000000000], [1380000000000]) (some (8, 3, 7))
      (some (8, 3, 7)) (.next ([5805000000000], [1695000000000]) (some (8, 3, 7)) (some (8, 3, 7))
      (.next ([5400000000000], [1905000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
      ([525000000000], [195000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([4995000000000],
      [2100000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([720000000000], [405000000000])
      (some (8, 3, 7)) (some (8, 3, 7)) (.next ([210000000000], [195000000000]) (some (8, 3, 7))
      (some (8, 3, 7)) (.next ([405000000000], [405000000000]) (some (8, 3, 7)) (some (8, 4, 7))
      (.next ([195000000000], [210000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
      ([2832000000000], [3405000000000]) (some (8, 4, 7)) (some (8, 5, 7)) (.next ([2517000000000],
      [3720000000000]) (some (8, 5, 7)) (some (8, 5, 7)) (.next ([3000000000000], [4752000000000])
      (some (8, 5, 7)) (some (8, 5, 7)) (.next ([405000000000], [720000000000]) (some (8, 5, 7))
      (some (8, 5, 7)) (.next ([2112000000000], [3930000000000]) (some (8, 5, 7)) (some (8, 5, 7))
      (.next ([525000000000], [1125000000000]) (some (8, 5, 7)) (some (8, 5, 7)) (.next
      ([1707000000000], [4125000000000]) (some (8, 5, 7)) (some (8, 5, 7)) (.next ([195000000000],
      [525000000000]) (some (8, 5, 7)) (some (8, 5, 7)) fan26Owner0Part1))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

private theorem tail26 : ModelImpossible model26 9000000000000 0 1 100 :=
  final_checkpoint model26 9000000000000 0 1 100 0 excluded26_0
private theorem tail25 : ModelImpossible model25 9000000000000 0 1 100 :=
  replay_checkpoint model25 model26 9000000000000 0 1 100 step25 next25 checked25 tail26
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
end Aown240000250000

theorem Aown_240000_250000_checked : Data.Aown240000250000.Valid := by
  apply certificate_checkpoint Data.Aown240000250000 Aown240000250000.model0 9000000000000 1 100
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown240000250000.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown240000250000.tail0

end ConwaySoifer.Simplified.Certificates
