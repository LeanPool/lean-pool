/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext240000250000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext2400002500000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext2400002500001
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext2400002500002
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext2400002500003
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext2400002500004
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext2400002500005
import Mathlib.Tactic.FinCases

/-!
# Sext 240000 250000

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
namespace Sext240000250000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan44Owner0Part0 : FanWitness := (.next ([-2175000000000], [7815000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-2565000000000], [7965000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-135000000000], [375000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-2250000000000], [6210000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2655000000000],
    [7020000000000]) (some (0, 2, 4)) (some (0, 2, 5)) (.next ([-2970000000000], [7335000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1125000000000], [2535000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-3780000000000], [7740000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-405000000000], [810000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1125000000000], [2220000000000]) (some (0, 2, 5)) (some (0, 2, 6)) (.next ([-720000000000],
    [1410000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-240000000000], [390000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-5190000000000], [8430000000000]) (some (0, 2, 6))
    (some (0, 3, 6)) (.next ([-720000000000], [1125000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-2160000000000], [3150000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-2400000000000], [3015000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-2160000000000],
    [2625000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-5220000000000], [6120000000000])
    (some (0, 3, 6)) (some (0, 4, 6)) (.next ([-5595000000000], [6360000000000]) (some (0, 4, 6))
    (some (0, 4, 6)) (.next ([-6030000000000], [6525000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    (.next ([-5745000000000], [6120000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-6405000000000], [6765000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-6345000000000],
    [6525000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-6720000000000], [6765000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.terminal (some (0, 4, 6)) (some (0, 4, 6)) (some (0, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan44Owner0Part1 : FanWitness := (.next ([405000000000], [405000000000]) (some (7, 2, 4)) (some
    (7, 2, 4)) (.next ([1095000000000], [1125000000000]) (some (7, 2, 4)) (some (8, 2, 4)) (.next
    ([690000000000], [720000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([150000000000],
    [240000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([3240000000000], [5190000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([405000000000], [720000000000]) (some (0, 2, 4)) (some
    (0, 2, 4)) (.next ([990000000000], [2160000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([615000000000], [2400000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([465000000000],
    [2160000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([900000000000], [5220000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([765000000000], [5595000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([495000000000], [6030000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([375000000000], [5745000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([360000000000], [6405000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([180000000000],
    [6345000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([45000000000], [6720000000000]) (some
    (0, 2, 4)) (some (0, 2, 4)) (.next ([0], [525000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-30000000000], [6555000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-345000000000], [6870000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-630000000000],
    [6750000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-765000000000], [7125000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1155000000000], [7275000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-720000000000], [2940000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-2040000000000], [7440000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    fan44Owner0Part0))))))))))))))))))))))))

private theorem initial : initModel Data.Sext240000250000.case Data.Sext240000250000.lo
    Data.Sext240000250000.hi Data.Sext240000250000.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded44_0 : ExcludedOn (model44.B 0) 9000000000000 (model44.caps 0) (model44.ord 0) 0 1
    100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6525000000000], [30000000000]) (some (6, 0, 4))
      (some (7, 0, 4)) (.next ([6525000000000], [345000000000]) (some (7, 0, 4)) (some (7, 0, 4))
      (.next ([6120000000000], [630000000000]) (some (7, 0, 4)) (some (7, 0, 4)) (.next
      ([6360000000000], [765000000000]) (some (7, 0, 4)) (some (7, 0, 4)) (.next ([6120000000000],
      [1155000000000]) (some (7, 0, 4)) (some (7, 0, 4)) (.next ([2220000000000], [720000000000])
      (some (7, 0, 4)) (some (7, 0, 4)) (.next ([5400000000000], [2040000000000]) (some (7, 0, 4))
      (some (7, 0, 4)) (.next ([5640000000000], [2175000000000]) (some (7, 0, 4)) (some (7, 1, 4))
      (.next ([5400000000000], [2565000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([240000000000], [135000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([3960000000000],
      [2250000000000]) (some (7, 1, 4)) (some (7, 2, 4)) (.next ([4365000000000], [2655000000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([4365000000000], [2970000000000]) (some (7, 2, 4))
      (some (7, 2, 4)) (.next ([1410000000000], [1125000000000]) (some (7, 2, 4)) (some (7, 2, 4))
      (.next ([3960000000000], [3780000000000]) (some (7, 2, 4)) (some (7, 2, 4))
      fan44Owner0Part1)))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

private theorem tail44 : ModelImpossible model44 9000000000000 0 1 100 :=
  final_checkpoint model44 9000000000000 0 1 100 0 excluded44_0
private theorem tail43 : ModelImpossible model43 9000000000000 0 1 100 :=
  replay_checkpoint model43 model44 9000000000000 0 1 100 step43 next43 checked43 tail44
private theorem tail42 : ModelImpossible model42 9000000000000 0 1 100 :=
  replay_checkpoint model42 model43 9000000000000 0 1 100 step42 next42 checked42 tail43
private theorem tail41 : ModelImpossible model41 9000000000000 0 1 100 :=
  replay_checkpoint model41 model42 9000000000000 0 1 100 step41 next41 checked41 tail42
private theorem tail40 : ModelImpossible model40 9000000000000 0 1 100 :=
  replay_checkpoint model40 model41 9000000000000 0 1 100 step40 next40 checked40 tail41
private theorem tail39 : ModelImpossible model39 9000000000000 0 1 100 :=
  replay_checkpoint model39 model40 9000000000000 0 1 100 step39 next39 checked39 tail40
private theorem tail38 : ModelImpossible model38 9000000000000 0 1 100 :=
  replay_checkpoint model38 model39 9000000000000 0 1 100 step38 next38 checked38 tail39
private theorem tail37 : ModelImpossible model37 9000000000000 0 1 100 :=
  replay_checkpoint model37 model38 9000000000000 0 1 100 step37 next37 checked37 tail38
private theorem tail36 : ModelImpossible model36 9000000000000 0 1 100 :=
  replay_checkpoint model36 model37 9000000000000 0 1 100 step36 next36 checked36 tail37
private theorem tail35 : ModelImpossible model35 9000000000000 0 1 100 :=
  replay_checkpoint model35 model36 9000000000000 0 1 100 step35 next35 checked35 tail36
private theorem tail34 : ModelImpossible model34 9000000000000 0 1 100 :=
  replay_checkpoint model34 model35 9000000000000 0 1 100 step34 next34 checked34 tail35
private theorem tail33 : ModelImpossible model33 9000000000000 0 1 100 :=
  replay_checkpoint model33 model34 9000000000000 0 1 100 step33 next33 checked33 tail34
private theorem tail32 : ModelImpossible model32 9000000000000 0 1 100 :=
  replay_checkpoint model32 model33 9000000000000 0 1 100 step32 next32 checked32 tail33
private theorem tail31 : ModelImpossible model31 9000000000000 0 1 100 :=
  replay_checkpoint model31 model32 9000000000000 0 1 100 step31 next31 checked31 tail32
private theorem tail30 : ModelImpossible model30 9000000000000 0 1 100 :=
  replay_checkpoint model30 model31 9000000000000 0 1 100 step30 next30 checked30 tail31
private theorem tail29 : ModelImpossible model29 9000000000000 0 1 100 :=
  replay_checkpoint model29 model30 9000000000000 0 1 100 step29 next29 checked29 tail30
private theorem tail28 : ModelImpossible model28 9000000000000 0 1 100 :=
  replay_checkpoint model28 model29 9000000000000 0 1 100 step28 next28 checked28 tail29
private theorem tail27 : ModelImpossible model27 9000000000000 0 1 100 :=
  replay_checkpoint model27 model28 9000000000000 0 1 100 step27 next27 checked27 tail28
private theorem tail26 : ModelImpossible model26 9000000000000 0 1 100 :=
  replay_checkpoint model26 model27 9000000000000 0 1 100 step26 next26 checked26 tail27
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
end Sext240000250000

theorem Sext_240000_250000_checked : Data.Sext240000250000.Valid := by
  apply certificate_checkpoint Data.Sext240000250000 Sext240000250000.model0 9000000000000 1 100
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Sext240000250000.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Sext240000250000.tail0

end ConwaySoifer.Simplified.Certificates
