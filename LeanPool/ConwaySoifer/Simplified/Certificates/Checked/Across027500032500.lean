/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across027500032500
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Across0275000325000
import Mathlib.Tactic.FinCases

/-!
# Across 027500 032500

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
namespace Across027500032500

private theorem initial : initModel Data.Across027500032500.case Data.Across027500032500.lo
    Data.Across027500032500.hi Data.Across027500032500.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded4_0 : ExcludedOn (model4.B 0) 9000000000000 (model4.caps 0) (model4.ord 0) 0 1 200
    := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8704818750000, 2902500000000], [162318750000,
      2902500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([8545181250000, -2902500000000],
      [242137500000, 5805000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([7954818750000,
      2902500000000], [841612500000, -5805000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([8034637500000, 5805000000000], [921431250000, -2902500000000]) (some (4, 1, 3)) (some (5, 1,
      3)) (.next ([7954818750000, 2902500000000], [1081068750000, 2902500000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([7795181250000, -2902500000000], [1160887500000, 5805000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([79818750000, 2902500000000], [79818750000,
      2902500000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([168750000000], [750000000000])
      (some (0, 1, 3)) (some (0, 2, 3)) (.next ([77137500000, 5805000000000], [8627681250000,
      -2902500000000]) (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-2681250000, 2902500000000],
      [8787318750000, 2902500000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-162318750000,
      -2902500000000], [8867137500000, 5805000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-242137500000, -5805000000000], [8787318750000, 2902500000000]) (some (0, 2, 4)) (some (0,
      2, 4)) (.next ([-841612500000, 5805000000000], [8796431250000, -2902500000000]) (some (0, 2,
      4)) (some (0, 3, 4)) (.next ([-921431250000, 2902500000000], [8956068750000, 2902500000000])
      (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-1081068750000, -2902500000000], [9035887500000,
      5805000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-1160887500000, -5805000000000],
      [8956068750000, 2902500000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-79818750000,
      -2902500000000], [159637500000, 5805000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
      ([-750000000000], [918750000000]) (some (0, 3, 4)) (some (1, 3, 4)) (.next ([-8627681250000,
      2902500000000], [8704818750000, 2902500000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.terminal
      (some (1, 3, 4)) (some (1, 3, 4)) (some (1, 3, 4))))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

private theorem tail4 : ModelImpossible model4 9000000000000 0 1 200 :=
  final_checkpoint model4 9000000000000 0 1 200 0 excluded4_0
private theorem tail3 : ModelImpossible model3 9000000000000 0 1 200 :=
  replay_checkpoint model3 model4 9000000000000 0 1 200 step3 next3 checked3 tail4
private theorem tail2 : ModelImpossible model2 9000000000000 0 1 200 :=
  replay_checkpoint model2 model3 9000000000000 0 1 200 step2 next2 checked2 tail3
private theorem tail1 : ModelImpossible model1 9000000000000 0 1 200 :=
  replay_checkpoint model1 model2 9000000000000 0 1 200 step1 next1 checked1 tail2
private theorem tail0 : ModelImpossible model0 9000000000000 0 1 200 :=
  replay_checkpoint model0 model1 9000000000000 0 1 200 step0 next0 checked0 tail1
end Across027500032500

theorem Across_027500_032500_checked : Data.Across027500032500.Valid := by
  apply certificate_checkpoint Data.Across027500032500 Across027500032500.model0 9000000000000 1
      200
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across027500032500.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across027500032500.tail0

end ConwaySoifer.Simplified.Certificates
