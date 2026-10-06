/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across017500022500
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Across0175000225000
import Mathlib.Tactic.FinCases

/-!
# Across 017500 022500

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
namespace Across017500022500

private theorem initial : initModel Data.Across017500022500.case Data.Across017500022500.lo
    Data.Across017500022500.hi Data.Across017500022500.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded4_0 : ExcludedOn (model4.B 0) 9000000000000 (model4.caps 0) (model4.ord 0) 0 1 200
    := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8727637500000, 5865000000000], [53681250000,
      -2932500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([8676318750000, 2932500000000],
      [156318750000, 2932500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([8573681250000,
      -2932500000000], [207637500000, 5865000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([8151318750000, 2932500000000], [692362500000, -5865000000000]) (some (4, 1, 3)) (some (4, 1,
      3)) (.next ([8202637500000, 5865000000000], [743681250000, -2932500000000]) (some (4, 1, 3))
      (some (5, 1, 3)) (.next ([8151318750000, 2932500000000], [846318750000, 2932500000000]) (some
      (5, 1, 3)) (some (5, 1, 3)) (.next ([8048681250000, -2932500000000], [897637500000,
      5865000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([51318750000, 2932500000000],
      [51318750000, 2932500000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([165000000000],
      [525000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-2362500000, 5865000000000],
      [8678681250000, -2932500000000]) (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-53681250000,
      2932500000000], [8781318750000, 2932500000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-156318750000, -2932500000000], [8832637500000, 5865000000000]) (some (0, 2, 4)) (some (0,
      2, 4)) (.next ([-207637500000, -5865000000000], [8781318750000, 2932500000000]) (some (0, 2,
      4)) (some (0, 2, 4)) (.next ([-692362500000, 5865000000000], [8843681250000, -2932500000000])
      (some (0, 2, 4)) (some (0, 3, 4)) (.next ([-743681250000, 2932500000000], [8946318750000,
      2932500000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-846318750000, -2932500000000],
      [8997637500000, 5865000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-897637500000,
      -5865000000000], [8946318750000, 2932500000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
      ([-51318750000, -2932500000000], [102637500000, 5865000000000]) (some (0, 3, 4)) (some (0, 3,
      4)) (.next ([-525000000000], [690000000000]) (some (0, 3, 4)) (some (1, 3, 4)) (.terminal
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
end Across017500022500

theorem Across_017500_022500_checked : Data.Across017500022500.Valid := by
  apply certificate_checkpoint Data.Across017500022500 Across017500022500.model0 9000000000000 1
      200
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across017500022500.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across017500022500.tail0

end ConwaySoifer.Simplified.Certificates
