/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across117500122500
public import LeanPool.ConwaySoifer.Simplified.Certificates.Steps.Across1175001225000
import Mathlib.Tactic.FinCases

/-!
# Across 117500 122500

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
namespace Across117500122500

private theorem initial : initModel Data.Across117500122500.case Data.Across117500122500.lo
    Data.Across117500122500.hi Data.Across117500122500.den = some model0 := by
  apply initial_checkpoint
  · decide +kernel
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded1_0 : ExcludedOn (model1.B 0) 9000000000000 (model1.caps 0) (model1.ord 0) 0 1 200
    := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8559318750000, 2632500000000], [1818750000,
      2632500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([7940681250000, -2632500000000],
      [311137500000, 5265000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([309318750000,
      2632500000000], [309318750000, 2632500000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.next
      ([926137500000, 5265000000000], [7633181250000, -2632500000000]) (some (4, 1, 4)) (some (4, 2,
      4)) (.next ([616818750000, 2632500000000], [8251818750000, 2632500000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([0, 0], [927956250000, 7897500000000]) (some (0, 2, 4)) (some (0, 2,
      4)) (.next ([-1818750000, -2632500000000], [8561137500000, 5265000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-311137500000, -5265000000000], [8251818750000, 2632500000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-309318750000, -2632500000000], [618637500000,
      5265000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-7633181250000, 2632500000000],
      [8559318750000, 2632500000000]) (some (0, 2, 4)) (some (1, 3, 4)) (.next ([-8251818750000,
      -2632500000000], [8868637500000, 5265000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.terminal
      (some (1, 3, 4)) (some (1, 3, 4)) (some (1, 3, 4))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

private theorem tail1 : ModelImpossible model1 9000000000000 0 1 200 :=
  final_checkpoint model1 9000000000000 0 1 200 0 excluded1_0
private theorem tail0 : ModelImpossible model0 9000000000000 0 1 200 :=
  replay_checkpoint model0 model1 9000000000000 0 1 200 step0 next0 checked0 tail1
end Across117500122500

theorem Across_117500_122500_checked : Data.Across117500122500.Valid := by
  apply certificate_checkpoint Data.Across117500122500 Across117500122500.model0 9000000000000 1
      200
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across117500122500.initial
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Across117500122500.tail0

end ConwaySoifer.Simplified.Certificates
