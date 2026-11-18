/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2300002400003
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2300002400003Part3. -/

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

theorem checkedWitnessForExcluded26_6 :
    ExclusionHint.check
      (model26.B 6 ++ [step26.q])
      9000000000000
      (model26.caps 6)
      (model26.ord 6)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded26_7 :
    ExclusionHint.check
      (model26.B 7 ++ [step26.q])
      9000000000000
      (model26.caps 7)
      (model26.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded26_9 :
    ExclusionHint.check
      (model26.B 9 ++ [step26.q])
      9000000000000
      (model26.caps 9)
      (model26.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded27_0 :
    ExclusionHint.check
      (model27.B 0 ++ [step27.q])
      9000000000000
      (model27.caps 0)
      (model27.ord 0)
      12
      (.witnessedFan (.next ([6585000000000], [105000000000]) (some (12, 12,
      8)) (some (12, 12, 8)) (.next ([5955000000000], [285000000000]) (some (12, 12, 8)) (some (12,
      12, 8)) (.next ([1725000000000], [90000000000]) (some (12, 12, 8)) (some (12, 12, 8)) (.next
      ([1649400000000, 2280000000000], [89400000000, 2280000000000]) (some (12, 12, 8)) (some (12,
      12, 8)) (.next ([5550000000000], [375000000000]) (some (12, 12, 8)) (some (12, 12, 8)) (.next
      ([6180000000000], [480000000000]) (some (12, 12, 8)) (some (12, 12, 9)) (.next
      ([375000000000], [30000000000]) (some (12, 12, 9)) (some (12, 12, 9)) (.next ([6899400000000,
      2280000000000], [856200000000, -4560000000000]) (some (12, 12, 9)) (some (12, 12, 9)) (.next
      ([5610000000000], [765000000000]) (some (12, 2, 9)) (some (12, 2, 9))
      fan27Owner0Part4))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded27_1 :
    ExclusionHint.check
      (model27.B 1 ++ [step27.q])
      9000000000000
      (model27.caps 1)
      (model27.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded27_2 :
    ExclusionHint.check
      (model27.B 2 ++ [step27.q])
      9000000000000
      (model27.caps 2)
      (model27.ord 2)
      12
      (.pair 1 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded27_4 :
    ExclusionHint.check
      (model27.B 4 ++ [step27.q])
      9000000000000
      (model27.caps 4)
      (model27.ord 4)
      12
      (.witnessedFan (.next ([285000000000], [15000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([4500000000000], [360000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([4014000000000], [486000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([3624000000000], [516000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([3339000000000],
      [501000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([4140000000000], [750000000000])
      (some (6, 1, 2)) (some (6, 1, 2)) (.next ([7095000000000, 0], [1350000000000, 9000000000000])
      (some (6, 1, 2)) (some (6, 1, 2)) (.next ([3840000000000], [1035000000000]) (some (6, 1, 2))
      (some (6, 1, 2)) (.next ([4374000000000, 0], [2070000000000, 9000000000000]) (some (6, 1, 2))
      (some (6, 1, 2)) (.next ([2430000000000, -9000000000000], [2430000000000, 9000000000000])
      (some (6, 1, 2)) (some (6, 1, 2)) (.next ([2220000000000], [3120000000000]) (some (6, 1, 2))
      (some (6, 1, 2)) (.next ([2205000000000], [3420000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([2235000000000], [3780000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      fan27Owner4Part0))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded27_5 :
    ExclusionHint.check
      (model27.B 5 ++ [step27.q])
      9000000000000
      (model27.caps 5)
      (model27.ord 5)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

end Sint230000240000
end ConwaySoifer.Simplified.Certificates
