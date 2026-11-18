/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2300002400003
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2300002400003Part0. -/

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

theorem checkedWitnessForExcluded24_0 :
    ExclusionHint.check
      (model24.B 0 ++ [step24.q])
      9000000000000
      (model24.caps 0)
      (model24.ord 0)
      12
      (.pair 9 12)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded24_1 :
    ExclusionHint.check
      (model24.B 1 ++ [step24.q])
      9000000000000
      (model24.caps 1)
      (model24.ord 1)
      12
      (.witnessedFan (.next ([3825000000000], [3480000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2070000000000, 9000000000000], [2070000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3825000000000], [5550000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([1755000000000, -9000000000000], [7620000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [2070000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-3480000000000, 9000000000000],
      [7305000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-2070000000000,
      -9000000000000], [4140000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-5550000000000], [9375000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-7620000000000,
      -9000000000000], [9375000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded24_2 :
    ExclusionHint.check
      (model24.B 2 ++ [step24.q])
      9000000000000
      (model24.caps 2)
      (model24.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded24_3 :
    ExclusionHint.check
      (model24.B 3 ++ [step24.q])
      9000000000000
      (model24.caps 3)
      (model24.ord 3)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded24_4 :
    ExclusionHint.check
      (model24.B 4 ++ [step24.q])
      9000000000000
      (model24.caps 4)
      (model24.ord 4)
      12
      (.pair 0 6)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded24_5 :
    ExclusionHint.check
      (model24.B 5 ++ [step24.q])
      9000000000000
      (model24.caps 5)
      (model24.ord 5)
      12
      (.witnessedFan (.next ([8490000000000], [135000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([3825000000000], [375000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([2940000000000], [885000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([3315000000000, 0], [2070000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([5175000000000], [3450000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([3105000000000,
      -9000000000000], [3450000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1755000000000,
      -9000000000000], [2445000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([750000000000], [4800000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [3315000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-135000000000], [8625000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-375000000000], [4200000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-885000000000], [3825000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-2070000000000, -9000000000000], [5385000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-3450000000000], [8625000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-3450000000000, 0], [6555000000000, -9000000000000]) (some (0, 2, 4)) (some (0, 2,
      4)) (.next ([-2445000000000, -9000000000000], [4200000000000]) (some (0, 2, 4)) (some (0, 4,
      4)) (.next ([-4800000000000], [5550000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.terminal
      (some (0, 4, 3)) (some (0, 4, 3)) (some (0, 4, 3)))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded24_7 :
    ExclusionHint.check
      (model24.B 7 ++ [step24.q])
      9000000000000
      (model24.caps 7)
      (model24.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded24_8 :
    ExclusionHint.check
      (model24.B 8 ++ [step24.q])
      9000000000000
      (model24.caps 8)
      (model24.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint230000240000
end ConwaySoifer.Simplified.Certificates
