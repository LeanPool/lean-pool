/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2300002400003
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2300002400003Part6. -/

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

theorem checkedWitnessForExcluded29_3 :
    ExclusionHint.check
      (model29.B 3 ++ [step29.q])
      9000000000000
      (model29.caps 3)
      (model29.ord 3)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded29_4 :
    ExclusionHint.check
      (model29.B 4 ++ [step29.q])
      9000000000000
      (model29.caps 4)
      (model29.ord 4)
      12
      (.witnessedFan (.next ([285000000000], [15000000000]) (some (5, 0, 6))
      (some (5, 1, 6)) (.next ([4170000000000], [315000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([4500000000000], [360000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([4014000000000], [486000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3624000000000],
      [516000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3339000000000], [501000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4200000000000], [675000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([4125000000000], [690000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([4140000000000], [750000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([4185000000000], [975000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3840000000000],
      [1035000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2055000000000, -9000000000000],
      [690000000000, 0]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4374000000000, 0],
      [2070000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 6, 2)) (.next ([2430000000000,
      -9000000000000], [2430000000000, 9000000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([3684000000000], [4815000000000]) (some (5, 6, 2)) (some (5, 6, 2))
      fan29Owner4Part0))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded29_6 :
    ExclusionHint.check
      (model29.B 6 ++ [step29.q])
      9000000000000
      (model29.caps 6)
      (model29.ord 6)
      12
      (.pair 2 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded29_7 :
    ExclusionHint.check
      (model29.B 7 ++ [step29.q])
      9000000000000
      (model29.caps 7)
      (model29.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded29_8 :
    ExclusionHint.check
      (model29.B 8 ++ [step29.q])
      9000000000000
      (model29.caps 8)
      (model29.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded29_9 :
    ExclusionHint.check
      (model29.B 9 ++ [step29.q])
      9000000000000
      (model29.caps 9)
      (model29.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded30_0 :
    ExclusionHint.check
      (model30.B 0 ++ [step30.q])
      9000000000000
      (model30.caps 0)
      (model30.ord 0)
      12
      (.witnessedFan (.next ([6585000000000], [105000000000]) (some (10, 12,
      8)) (some (10, 12, 8)) (.next ([5955000000000], [285000000000]) (some (10, 12, 8)) (some (10,
      12, 8)) (.next ([1725000000000], [90000000000]) (some (10, 12, 8)) (some (10, 12, 8))
      fan30Owner0Part4))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded30_1 :
    ExclusionHint.check
      (model30.B 1 ++ [step30.q])
      9000000000000
      (model30.caps 1)
      (model30.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint230000240000
end ConwaySoifer.Simplified.Certificates
