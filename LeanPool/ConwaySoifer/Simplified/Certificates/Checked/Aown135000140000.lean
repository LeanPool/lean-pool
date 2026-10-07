/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown135000140000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown1350001400000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Aown1350001400001
import Mathlib.Tactic.FinCases

/-!
# Aown 135000 140000

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
namespace Aown135000140000

private theorem initial : initModel Data.Aown135000140000.case Data.Aown135000140000.lo
    Data.Aown135000140000.hi Data.Aown135000140000.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded11_6 : ExcludedOn (model11.B 6) 9000000000000 (model11.caps 6) (model11.ord 6) 0 1
    200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8190000000000], [60000000000]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([6975000000000, -9000000000000], [1275000000000, 9000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1215000000000, 9000000000000], [1215000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([3402000000000, 9000000000000],
      [4698000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2187000000000],
      [5913000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1155000000000, 9000000000000],
      [7035000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([90000000000],
      [2247000000000]) (some (0, 1, 3)) (some (0, 1, 4)) (.next ([0, 0], [1215000000000,
      9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-60000000000], [8250000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1275000000000, -9000000000000], [8250000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1215000000000, -9000000000000], [2430000000000,
      18000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4698000000000, 9000000000000],
      [8100000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-5913000000000], [8100000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-7035000000000, 9000000000000], [8190000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2247000000000], [2337000000000]) (some (0, 2, 4))
      (some (1, 2, 4)) (.terminal (some (1, 2, 0)) (some (1, 2, 0)) (some (1, 2,
      0))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
  decide +kernel

private theorem tail11 : ModelImpossible model11 9000000000000 0 1 200 :=
  final_checkpoint model11 9000000000000 0 1 200 6 excluded11_6
private theorem tail10 : ModelImpossible model10 9000000000000 0 1 200 :=
  replay_checkpoint model10 model11 9000000000000 0 1 200 step10 next10 checked10 tail11
private theorem tail9 : ModelImpossible model9 9000000000000 0 1 200 :=
  replay_checkpoint model9 model10 9000000000000 0 1 200 step9 next9 checked9 tail10
private theorem tail8 : ModelImpossible model8 9000000000000 0 1 200 :=
  replay_checkpoint model8 model9 9000000000000 0 1 200 step8 next8 checked8 tail9
private theorem tail7 : ModelImpossible model7 9000000000000 0 1 200 :=
  replay_checkpoint model7 model8 9000000000000 0 1 200 step7 next7 checked7 tail8
private theorem tail6 : ModelImpossible model6 9000000000000 0 1 200 :=
  replay_checkpoint model6 model7 9000000000000 0 1 200 step6 next6 checked6 tail7
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
end Aown135000140000

theorem Aown_135000_140000_checked : Data.Aown135000140000.Valid := by
  apply certificate_checkpoint Data.Aown135000140000 Aown135000140000.model0 9000000000000 1 200
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown135000140000.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Aown135000140000.tail0

end ConwaySoifer.Simplified.Certificates
