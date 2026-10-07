/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across042500047500
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Across0425000475000
import Mathlib.Tactic.FinCases

/-!
# Across 042500 047500

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
namespace Across042500047500

private theorem initial : initModel Data.Across042500047500.case Data.Across042500047500.lo
    Data.Across042500047500.hi Data.Across042500047500.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded5_0 : ExcludedOn (model5.B 0) 9000000000000 (model5.caps 0) (model5.ord 0) 0 1 200
    := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8555193750000, 2857500000000], [132112500000,
      -5715000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([8676637500000, 5715000000000],
      [253556250000, -2857500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([8555193750000,
      2857500000000], [496443750000, 2857500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([8312306250000, -2857500000000], [617887500000, 5715000000000]) (some (4, 1, 3)) (some (4, 1,
      3)) (.next ([7805193750000, 2857500000000], [882112500000, -5715000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([7926637500000, 5715000000000], [1003556250000, -2857500000000])
      (some (4, 1, 3)) (some (5, 1, 3)) (.next ([7805193750000, 2857500000000], [1246443750000,
      2857500000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([7562306250000, -2857500000000],
      [1367887500000, 5715000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([121443750000,
      2857500000000], [121443750000, 2857500000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0,
      0], [364331250000, 8572500000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-132112500000,
      5715000000000], [8687306250000, -2857500000000]) (some (0, 2, 3)) (some (0, 2, 4)) (.next
      ([-253556250000, 2857500000000], [8930193750000, 2857500000000]) (some (0, 2, 4)) (some (0, 2,
      4)) (.next ([-496443750000, -2857500000000], [9051637500000, 5715000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-617887500000, -5715000000000], [8930193750000, 2857500000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-882112500000, 5715000000000], [8687306250000,
      -2857500000000]) (some (0, 2, 4)) (some (0, 3, 4)) (.next ([-1003556250000, 2857500000000],
      [8930193750000, 2857500000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-1246443750000,
      -2857500000000], [9051637500000, 5715000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
      ([-1367887500000, -5715000000000], [8930193750000, 2857500000000]) (some (0, 3, 4)) (some (0,
      3, 4)) (.next ([-121443750000, -2857500000000], [242887500000, 5715000000000]) (some (0, 3,
      4)) (some (0, 3, 4)) (.terminal (some (0, 3, 4)) (some (1, 3, 4)) (some (1, 3,
      4))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
  decide +kernel

private theorem tail5 : ModelImpossible model5 9000000000000 0 1 200 :=
  final_checkpoint model5 9000000000000 0 1 200 0 excluded5_0
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
end Across042500047500

theorem Across_042500_047500_checked : Data.Across042500047500.Valid := by
  apply certificate_checkpoint Data.Across042500047500 Across042500047500.model0 9000000000000 1
      200
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across042500047500.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across042500047500.tail0

end ConwaySoifer.Simplified.Certificates
