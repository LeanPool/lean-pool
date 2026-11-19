/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2300002400003
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2300002400003Part4. -/

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

public section

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint230000240000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint230000240000

theorem checkedWitnessForExcluded27_6 :
    ExclusionHint.check
      (model27.B 6 ++ [step27.q])
      9000000000000
      (model27.caps 6)
      (model27.ord 6)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded27_7 :
    ExclusionHint.check
      (model27.B 7 ++ [step27.q])
      9000000000000
      (model27.caps 7)
      (model27.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded27_8 :
    ExclusionHint.check
      (model27.B 8 ++ [step27.q])
      9000000000000
      (model27.caps 8)
      (model27.ord 8)
      12
      (.witnessedFan (.next ([5250000000000], [1845000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([2625000000000], [1470000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([2625000000000], [7095000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1155000000000], [4470000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [4470000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1845000000000], [7095000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1470000000000], [4095000000000]) (some (0, 1, 3))
      (some (0, 3, 3)) (.next ([-7095000000000], [9720000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-4470000000000], [5625000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded27_9 :
    ExclusionHint.check
      (model27.B 9 ++ [step27.q])
      9000000000000
      (model27.caps 9)
      (model27.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded28_0 :
    ExclusionHint.check
      (model28.B 0 ++ [step28.q])
      9000000000000
      (model28.caps 0)
      (model28.ord 0)
      12
      (.pair 9 12)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded28_1 :
    ExclusionHint.check
      (model28.B 1 ++ [step28.q])
      9000000000000
      (model28.caps 1)
      (model28.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded28_2 :
    ExclusionHint.check
      (model28.B 2 ++ [step28.q])
      9000000000000
      (model28.caps 2)
      (model28.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded28_3 :
    ExclusionHint.check
      (model28.B 3 ++ [step28.q])
      9000000000000
      (model28.caps 3)
      (model28.ord 3)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

end Sint230000240000
end ConwaySoifer.Simplified.Certificates
