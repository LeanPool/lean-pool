/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2800002900002
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2800002900002Part8. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint280000290000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint280000290000

theorem checkedWitnessForExcluded23_1 :
    ExclusionHint.check
      (model23.B 1 ++ [step23.q])
      9000000000000
      (model23.caps 1)
      (model23.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded23_2 :
    ExclusionHint.check
      (model23.B 2 ++ [step23.q])
      9000000000000
      (model23.caps 2)
      (model23.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded23_3 :
    ExclusionHint.check
      (model23.B 3 ++ [step23.q])
      9000000000000
      (model23.caps 3)
      (model23.ord 3)
      12
      (.pair 2 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded23_5 :
    ExclusionHint.check
      (model23.B 5 ++ [step23.q])
      9000000000000
      (model23.caps 5)
      (model23.ord 5)
      12
      (.witnessedFan (.next ([5040000000000], [2640000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([3900000000000, -9000000000000], [2520000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2880000000000, 0], [2520000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 3)) (.next ([1260000000000], [1380000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([2880000000000], [3540000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([2520000000000, -9000000000000], [5160000000000, 9000000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([240000000000], [4800000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([0], [2880000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2640000000000],
      [7680000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-2520000000000, -9000000000000],
      [6420000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2520000000000, -9000000000000],
      [5400000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1380000000000],
      [2640000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3540000000000], [6420000000000])
      (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-5160000000000, -9000000000000], [7680000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4800000000000], [5040000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2,
      4)))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded23_6 :
    ExclusionHint.check
      (model23.B 6 ++ [step23.q])
      9000000000000
      (model23.caps 6)
      (model23.ord 6)
      12
      (.pair 1 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded23_7 :
    ExclusionHint.check
      (model23.B 7 ++ [step23.q])
      9000000000000
      (model23.caps 7)
      (model23.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded23_8 :
    ExclusionHint.check
      (model23.B 8 ++ [step23.q])
      9000000000000
      (model23.caps 8)
      (model23.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded23_9 :
    ExclusionHint.check
      (model23.B 9 ++ [step23.q])
      9000000000000
      (model23.caps 9)
      (model23.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint280000290000
end ConwaySoifer.Simplified.Certificates
