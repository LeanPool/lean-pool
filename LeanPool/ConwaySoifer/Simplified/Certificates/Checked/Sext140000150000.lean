/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext140000150000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext1400001500000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext1400001500001
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext1400001500002
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext1400001500003
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext1400001500004
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext1400001500005
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext1400001500006
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext1400001500007
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext1400001500008
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Sext1400001500009
import Mathlib.Tactic.FinCases

/-!
# Sext 140000 150000

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
namespace Sext140000150000

private theorem initial : initModel Data.Sext140000150000.case Data.Sext140000150000.lo
    Data.Sext140000150000.hi Data.Sext140000150000.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded76_1 : ExcludedOn (model76.B 1) 9000000000000 (model76.caps 1) (model76.ord 1) 0 1
    100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5580000000000], [630000000000]) (some (5, 1, 2))
      (some (5, 1, 3)) (.next ([4320000000000, -9000000000000], [630000000000, 0]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([3510000000000, 9000000000000], [2700000000000, -9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4830000000000], [4710000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([1260000000000, 9000000000000], [1260000000000, 9000000000000]) (some
      (5, 1, 3)) (some (5, 1, 3)) (.next ([2250000000000], [3960000000000]) (some (5, 1, 3)) (some
      (5, 1, 3)) (.next ([1500000000000], [3960000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([1500000000000], [4710000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([990000000000,
      -9000000000000], [3960000000000, 0]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([630000000000,
      9000000000000], [6210000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([240000000000,
      -9000000000000], [5220000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([0], [3330000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-630000000000],
      [6210000000000]) (some (0, 1, 3)) (some (0, 1, 4)) (.next ([-630000000000, 0], [4950000000000,
      -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2700000000000, 9000000000000],
      [6210000000000]) (some (0, 1, 4)) (some (0, 1, 5)) (.next ([-4710000000000], [9540000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1260000000000, -9000000000000], [2520000000000,
      18000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3960000000000], [6210000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3960000000000], [5460000000000]) (some (0, 1, 5))
      (some (0, 2, 5)) (.next ([-4710000000000], [6210000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-3960000000000, 0], [4950000000000, -9000000000000]) (some (0, 2, 5)) (some (1, 2,
      5)) (.next ([-6210000000000], [6840000000000, 9000000000000]) (some (1, 2, 5)) (some (1, 2,
      5)) (.next ([-5220000000000, -9000000000000], [5460000000000, 0]) (some (1, 2, 5)) (some (1,
      2, 5)) (.terminal (some (1, 2, 5)) (some (1, 2, 5)) (some (1, 2, 5)))))))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

private theorem tail76 : ModelImpossible model76 9000000000000 0 1 100 :=
  final_checkpoint model76 9000000000000 0 1 100 1 excluded76_1
private theorem tail75 : ModelImpossible model75 9000000000000 0 1 100 :=
  replay_checkpoint model75 model76 9000000000000 0 1 100 step75 next75 checked75 tail76
private theorem tail74 : ModelImpossible model74 9000000000000 0 1 100 :=
  replay_checkpoint model74 model75 9000000000000 0 1 100 step74 next74 checked74 tail75
private theorem tail73 : ModelImpossible model73 9000000000000 0 1 100 :=
  replay_checkpoint model73 model74 9000000000000 0 1 100 step73 next73 checked73 tail74
private theorem tail72 : ModelImpossible model72 9000000000000 0 1 100 :=
  replay_checkpoint model72 model73 9000000000000 0 1 100 step72 next72 checked72 tail73
private theorem tail71 : ModelImpossible model71 9000000000000 0 1 100 :=
  replay_checkpoint model71 model72 9000000000000 0 1 100 step71 next71 checked71 tail72
private theorem tail70 : ModelImpossible model70 9000000000000 0 1 100 :=
  replay_checkpoint model70 model71 9000000000000 0 1 100 step70 next70 checked70 tail71
private theorem tail69 : ModelImpossible model69 9000000000000 0 1 100 :=
  replay_checkpoint model69 model70 9000000000000 0 1 100 step69 next69 checked69 tail70
private theorem tail68 : ModelImpossible model68 9000000000000 0 1 100 :=
  replay_checkpoint model68 model69 9000000000000 0 1 100 step68 next68 checked68 tail69
private theorem tail67 : ModelImpossible model67 9000000000000 0 1 100 :=
  replay_checkpoint model67 model68 9000000000000 0 1 100 step67 next67 checked67 tail68
private theorem tail66 : ModelImpossible model66 9000000000000 0 1 100 :=
  replay_checkpoint model66 model67 9000000000000 0 1 100 step66 next66 checked66 tail67
private theorem tail65 : ModelImpossible model65 9000000000000 0 1 100 :=
  replay_checkpoint model65 model66 9000000000000 0 1 100 step65 next65 checked65 tail66
private theorem tail64 : ModelImpossible model64 9000000000000 0 1 100 :=
  replay_checkpoint model64 model65 9000000000000 0 1 100 step64 next64 checked64 tail65
private theorem tail63 : ModelImpossible model63 9000000000000 0 1 100 :=
  replay_checkpoint model63 model64 9000000000000 0 1 100 step63 next63 checked63 tail64
private theorem tail62 : ModelImpossible model62 9000000000000 0 1 100 :=
  replay_checkpoint model62 model63 9000000000000 0 1 100 step62 next62 checked62 tail63
private theorem tail61 : ModelImpossible model61 9000000000000 0 1 100 :=
  replay_checkpoint model61 model62 9000000000000 0 1 100 step61 next61 checked61 tail62
private theorem tail60 : ModelImpossible model60 9000000000000 0 1 100 :=
  replay_checkpoint model60 model61 9000000000000 0 1 100 step60 next60 checked60 tail61
private theorem tail59 : ModelImpossible model59 9000000000000 0 1 100 :=
  replay_checkpoint model59 model60 9000000000000 0 1 100 step59 next59 checked59 tail60
private theorem tail58 : ModelImpossible model58 9000000000000 0 1 100 :=
  replay_checkpoint model58 model59 9000000000000 0 1 100 step58 next58 checked58 tail59
private theorem tail57 : ModelImpossible model57 9000000000000 0 1 100 :=
  replay_checkpoint model57 model58 9000000000000 0 1 100 step57 next57 checked57 tail58
private theorem tail56 : ModelImpossible model56 9000000000000 0 1 100 :=
  replay_checkpoint model56 model57 9000000000000 0 1 100 step56 next56 checked56 tail57
private theorem tail55 : ModelImpossible model55 9000000000000 0 1 100 :=
  replay_checkpoint model55 model56 9000000000000 0 1 100 step55 next55 checked55 tail56
private theorem tail54 : ModelImpossible model54 9000000000000 0 1 100 :=
  replay_checkpoint model54 model55 9000000000000 0 1 100 step54 next54 checked54 tail55
private theorem tail53 : ModelImpossible model53 9000000000000 0 1 100 :=
  replay_checkpoint model53 model54 9000000000000 0 1 100 step53 next53 checked53 tail54
private theorem tail52 : ModelImpossible model52 9000000000000 0 1 100 :=
  replay_checkpoint model52 model53 9000000000000 0 1 100 step52 next52 checked52 tail53
private theorem tail51 : ModelImpossible model51 9000000000000 0 1 100 :=
  replay_checkpoint model51 model52 9000000000000 0 1 100 step51 next51 checked51 tail52
private theorem tail50 : ModelImpossible model50 9000000000000 0 1 100 :=
  replay_checkpoint model50 model51 9000000000000 0 1 100 step50 next50 checked50 tail51
private theorem tail49 : ModelImpossible model49 9000000000000 0 1 100 :=
  replay_checkpoint model49 model50 9000000000000 0 1 100 step49 next49 checked49 tail50
private theorem tail48 : ModelImpossible model48 9000000000000 0 1 100 :=
  replay_checkpoint model48 model49 9000000000000 0 1 100 step48 next48 checked48 tail49
private theorem tail47 : ModelImpossible model47 9000000000000 0 1 100 :=
  replay_checkpoint model47 model48 9000000000000 0 1 100 step47 next47 checked47 tail48
private theorem tail46 : ModelImpossible model46 9000000000000 0 1 100 :=
  replay_checkpoint model46 model47 9000000000000 0 1 100 step46 next46 checked46 tail47
private theorem tail45 : ModelImpossible model45 9000000000000 0 1 100 :=
  replay_checkpoint model45 model46 9000000000000 0 1 100 step45 next45 checked45 tail46
private theorem tail44 : ModelImpossible model44 9000000000000 0 1 100 :=
  replay_checkpoint model44 model45 9000000000000 0 1 100 step44 next44 checked44 tail45
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
end Sext140000150000

theorem Sext_140000_150000_checked : Data.Sext140000150000.Valid := by
  apply certificate_checkpoint Data.Sext140000150000 Sext140000150000.model0 9000000000000 1 100
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Sext140000150000.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Sext140000150000.tail0

end ConwaySoifer.Simplified.Certificates
