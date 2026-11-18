/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2000002100006
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2000002100006Part2. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint200000210000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint200000210000

theorem checkedWitnessForExcluded49_8 :
    ExclusionHint.check
      (model49.B 8 ++ [step49.q])
      9000000000000
      (model49.caps 8)
      (model49.ord 8)
      12
      (.witnessedFan (.next ([6600000000000], [600000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([3450000000000], [5550000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([1800000000000], [3750000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1050000000000], [2400000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [7200000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-600000000000], [7200000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5550000000000], [9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-3750000000000], [5550000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-2400000000000], [3450000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded49_9 :
    ExclusionHint.check
      (model49.B 9 ++ [step49.q])
      9000000000000
      (model49.caps 9)
      (model49.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded50_0 :
    ExclusionHint.check
      (model50.B 0 ++ [step50.q])
      9000000000000
      (model50.caps 0)
      (model50.ord 0)
      12
      (.pair 0 9)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded50_1 :
    ExclusionHint.check
      (model50.B 1 ++ [step50.q])
      9000000000000
      (model50.caps 1)
      (model50.ord 1)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded50_2 :
    ExclusionHint.check
      (model50.B 2 ++ [step50.q])
      9000000000000
      (model50.caps 2)
      (model50.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded50_3 :
    ExclusionHint.check
      (model50.B 3 ++ [step50.q])
      9000000000000
      (model50.caps 3)
      (model50.ord 3)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded50_4 :
    ExclusionHint.check
      (model50.B 4 ++ [step50.q])
      9000000000000
      (model50.caps 4)
      (model50.ord 4)
      12
      (.witnessedFan (.next ([5550000000000], [75000000000]) (some (4, 0, 3))
      (some (4, 5, 3)) (.next ([5550000000000, 0], [1800000000000, 9000000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([3825000000000, -9000000000000], [1800000000000, 9000000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5550000000000], [3750000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([1800000000000], [2700000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([2850000000000], [4500000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([1125000000000], [1800000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1875000000000],
      [3750000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([750000000000], [1950000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0, 0], [1800000000000, 9000000000000]) (some (4, 5,
      3)) (some (4, 5, 3)) (.next ([-75000000000], [5625000000000]) (some (0, 5, 3)) (some (0, 5,
      3)) (.next ([-1800000000000, -9000000000000], [7350000000000, 9000000000000]) (some (0, 5, 3))
      (some (0, 5, 4)) (.next ([-1800000000000, -9000000000000], [5625000000000, 0]) (some (0, 5,
      4)) (some (0, 5, 4)) (.next ([-3750000000000], [9300000000000]) (some (0, 5, 4)) (some (0, 5,
      4)) (.next ([-2700000000000], [4500000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-4500000000000], [7350000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-1800000000000], [2925000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3750000000000], [5625000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-1950000000000], [2700000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.terminal (some (0, 3,
      4)) (some (0, 3, 4)) (some (0, 3, 4)))))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded50_6 :
    ExclusionHint.check
      (model50.B 6 ++ [step50.q])
      9000000000000
      (model50.caps 6)
      (model50.ord 6)
      12
      (.pair 1 5)
      0
      1
      100 = true := by
  decide +kernel

end Sint200000210000
end ConwaySoifer.Simplified.Certificates
