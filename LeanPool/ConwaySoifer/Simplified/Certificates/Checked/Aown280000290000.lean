/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown280000290000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2800002900000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2800002900001
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown2800002900002
import Mathlib.Tactic.FinCases

/-!
# Aown 280000 290000

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
namespace Aown280000290000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part0 : FanWitness := (.next ([-2100000000000], [6975000000000]) (some (0, 4, 6))
    (some (0, 4, 6)) (.next ([-45000000000], [135000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    (.next ([-420000000000], [1125000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-1215000000000], [3000000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1260000000000],
    [2670000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-420000000000], [885000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1215000000000], [2535000000000]) (some (0, 4, 6))
    (some (1, 4, 6)) (.next ([-750000000000], [1500000000000]) (some (1, 4, 6)) (some (1, 4, 6))
    (.next ([-3375000000000], [6150000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next
    ([-885000000000], [1590000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-3615000000000],
    [6390000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-3420000000000], [5760000000000])
    (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-750000000000], [1260000000000]) (some (1, 4, 6))
    (some (1, 5, 6)) (.next ([-765000000000], [1176000000000]) (some (1, 5, 6)) (some (1, 5, 6))
    (.next ([-885000000000], [1350000000000]) (some (1, 5, 6)) (some (1, 5, 7)) (.next
    ([-4500000000000], [6855000000000]) (some (1, 5, 7)) (some (1, 5, 7)) (.next ([-3786000000000],
    [5385000000000]) (some (1, 5, 7)) (some (1, 5, 7)) (.next ([-4875000000000], [6900000000000])
    (some (1, 5, 7)) (some (1, 5, 7)) (.next ([-4026000000000], [5625000000000]) (some (1, 5, 7))
    (some (1, 5, 7)) (.next ([-4965000000000], [6855000000000]) (some (1, 5, 7)) (some (1, 5, 7))
    (.next ([-4911000000000], [6090000000000]) (some (1, 5, 7)) (some (1, 5, 7)) (.next
    ([-5286000000000], [6135000000000]) (some (1, 5, 7)) (some (1, 5, 7)) (.next ([-330000000000],
    [375000000000]) (some (1, 5, 7)) (some (1, 5, 7)) (.next ([-5376000000000], [6090000000000])
    (some (1, 5, 7)) (some (2, 5, 7)) (.terminal (some (2, 5, 7)) (some (2, 5, 7)) (some (2, 5,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part1 : FanWitness := (.next ([2340000000000], [3420000000000]) (some (7, 4, 5))
    (some (7, 4, 5)) (.next ([510000000000], [750000000000]) (some (7, 4, 5)) (some (7, 4, 5))
    (.next ([411000000000], [765000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next
    ([465000000000], [885000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([2355000000000],
    [4500000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([1599000000000], [3786000000000])
    (some (7, 4, 5)) (some (7, 4, 5)) (.next ([2025000000000], [4875000000000]) (some (7, 4, 5))
    (some (8, 4, 5)) (.next ([1599000000000], [4026000000000]) (some (8, 4, 5)) (some (8, 4, 5))
    (.next ([1890000000000], [4965000000000]) (some (8, 4, 5)) (some (8, 4, 5)) (.next
    ([1179000000000], [4911000000000]) (some (8, 4, 5)) (some (8, 4, 5)) (.next ([849000000000],
    [5286000000000]) (some (8, 4, 5)) (some (8, 4, 5)) (.next ([45000000000], [330000000000]) (some
    (8, 4, 5)) (some (8, 4, 5)) (.next ([714000000000], [5376000000000]) (some (8, 4, 5)) (some (8,
    4, 5)) (.next ([0], [240000000000]) (some (8, 4, 5)) (some (8, 4, 5)) (.next ([-120000000000],
    [2985000000000]) (some (0, 4, 5)) (some (0, 4, 5)) (.next ([-510000000000], [6270000000000])
    (some (0, 4, 5)) (some (0, 4, 6)) (.next ([-645000000000], [6285000000000]) (some (0, 4, 6))
    (some (0, 4, 6)) (.next ([-750000000000], [6510000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    (.next ([-510000000000], [3420000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-885000000000], [4161000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-750000000000],
    [3420000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1635000000000], [6975000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1821000000000], [6696000000000]) (some (0, 4, 6))
    (some (0, 4, 6)) (.next ([-2010000000000], [7020000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    fan19Owner0Part0))))))))))))))))))))))))

private theorem initial : initModel Data.Aown280000290000.case Data.Aown280000290000.lo
    Data.Aown280000290000.hi Data.Aown280000290000.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded19_0 : ExcludedOn (model19.B 0) 9000000000000 (model19.caps 0) (model19.ord 0) 0 1
    100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2865000000000], [120000000000]) (some (7, 2, 5))
      (some (7, 2, 5)) (.next ([5760000000000], [510000000000]) (some (7, 2, 5)) (some (7, 2, 5))
      (.next ([5640000000000], [645000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
      ([5760000000000], [750000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([2910000000000],
      [510000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([3276000000000], [885000000000])
      (some (7, 2, 5)) (some (7, 2, 5)) (.next ([2670000000000], [750000000000]) (some (7, 2, 5))
      (some (7, 2, 5)) (.next ([5340000000000], [1635000000000]) (some (7, 2, 5)) (some (7, 2, 5))
      (.next ([4875000000000], [1821000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
      ([5010000000000], [2010000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([4875000000000],
      [2100000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([90000000000], [45000000000]) (some
      (7, 2, 5)) (some (7, 2, 5)) (.next ([705000000000], [420000000000]) (some (7, 2, 5)) (some (7,
      3, 5)) (.next ([1785000000000], [1215000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
      ([1410000000000], [1260000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([465000000000],
      [420000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([1320000000000], [1215000000000])
      (some (7, 3, 5)) (some (7, 3, 5)) (.next ([750000000000], [750000000000]) (some (7, 3, 5))
      (some (7, 4, 5)) (.next ([2775000000000], [3375000000000]) (some (7, 4, 5)) (some (7, 4, 5))
      (.next ([705000000000], [885000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next
      ([2775000000000], [3615000000000]) (some (7, 4, 5)) (some (7, 4, 5))
      fan19Owner0Part1)))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

private theorem tail19 : ModelImpossible model19 9000000000000 0 1 100 :=
  final_checkpoint model19 9000000000000 0 1 100 0 excluded19_0
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
end Aown280000290000

theorem Aown_280000_290000_checked : Data.Aown280000290000.Valid := by
  apply certificate_checkpoint Data.Aown280000290000 Aown280000290000.model0 9000000000000 1 100
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown280000290000.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown280000290000.tail0

end ConwaySoifer.Simplified.Certificates
