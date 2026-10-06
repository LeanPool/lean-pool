/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across022500027500
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Across0225000275000
import Mathlib.Tactic.FinCases

/-!
# Across 022500 027500

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
namespace Across022500027500

private theorem initial : initModel Data.Across022500027500.case Data.Across022500027500.lo
    Data.Across022500027500.hi Data.Across022500027500.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded7_0 : ExcludedOn (model7.B 0) 9000000000000 (model7.caps 0) (model7.ord 0) 0 1 200
    := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8756287500000, 5835000000000], [35606250000,
      -2917500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([8690643750000, 2917500000000],
      [166893750000, 2917500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([8559356250000,
      -2917500000000], [232537500000, 5835000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([7998750000000], [697500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([8130037500000,
      5835000000000], [834356250000, -2917500000000]) (some (4, 1, 3)) (some (5, 1, 3)) (.next
      ([8064393750000, 2917500000000], [965643750000, 2917500000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([7933106250000, -2917500000000], [1031287500000, 5835000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([268143750000, 2917500000000], [65643750000, 2917500000000]) (some
      (5, 1, 3)) (some (5, 1, 3)) (.next ([131287500000, 5835000000000], [136856250000,
      -2917500000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([172500000000], [626250000000])
      (some (0, 1, 3)) (some (0, 2, 3)) (.next ([101250000000], [8523750000000]) (some (0, 2, 3))
      (some (0, 2, 4)) (.next ([0, 0], [196931250000, 8752500000000]) (some (0, 2, 4)) (some (0, 2,
      4)) (.next ([-35606250000, 2917500000000], [8791893750000, 2917500000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-166893750000, -2917500000000], [8857537500000, 5835000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-232537500000, -5835000000000], [8791893750000,
      2917500000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-697500000000], [8696250000000])
      (some (0, 2, 4)) (some (0, 3, 4)) (.next ([-834356250000, 2917500000000], [8964393750000,
      2917500000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-965643750000, -2917500000000],
      [9030037500000, 5835000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-1031287500000,
      -5835000000000], [8964393750000, 2917500000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
      ([-65643750000, -2917500000000], [333787500000, 5835000000000]) (some (0, 3, 4)) (some (0, 3,
      4)) (.next ([-136856250000, 2917500000000], [268143750000, 2917500000000]) (some (0, 3, 4))
      (some (0, 3, 4)) (.next ([-626250000000], [798750000000]) (some (0, 3, 4)) (some (1, 3, 4))
      (.next ([-8523750000000], [8625000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.terminal (some
      (1, 3, 4)) (some (1, 3, 4)) (some (1, 3, 4))))))))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

private theorem tail7 : ModelImpossible model7 9000000000000 0 1 200 :=
  final_checkpoint model7 9000000000000 0 1 200 0 excluded7_0
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
end Across022500027500

theorem Across_022500_027500_checked : Data.Across022500027500.Valid := by
  apply certificate_checkpoint Data.Across022500027500 Across022500027500.model0 9000000000000 1
      200
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across022500027500.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across022500027500.tail0

end ConwaySoifer.Simplified.Certificates
