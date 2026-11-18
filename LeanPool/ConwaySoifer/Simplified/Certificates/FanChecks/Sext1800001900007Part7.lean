/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1800001900007
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sext1800001900007Part7. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sext180000190000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sext180000190000

theorem checkedWitnessForExcluded62_3 :
    ExclusionHint.check
      (model62.B 3 ++ [step62.q])
      9000000000000
      (model62.caps 3)
      (model62.ord 3)
      12
      (.witnessedFan (.next ([4950000000000], [675000000000]) (some (4, 0, 6))
      (some (5, 0, 6)) (.next ([1995000000000], [330000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([5130000000000, 9000000000000], [1620000000000, -9000000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([3000000000000], [1620000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([4620000000000], [3000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([1710000000000], [1425000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3510000000000],
      [3240000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([2160000000000], [3090000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1995000000000, 9000000000000], [3330000000000,
      -9000000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next ([1500000000000], [2970000000000])
      (some (5, 0, 3)) (some (5, 0, 3)) (.next ([2250000000000], [5460000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([1380000000000], [3750000000000]) (some (5, 0, 3)) (some (5, 6, 3))
      (.next ([750000000000], [2490000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      fan62Owner3Part0))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded62_4 :
    ExclusionHint.check
      (model62.B 4 ++ [step62.q])
      9000000000000
      (model62.caps 4)
      (model62.ord 4)
      12
      (.witnessedFan (.next ([7710000000000], [750000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) fan62Owner4Part0))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded62_5 :
    ExclusionHint.check
      (model62.B 5 ++ [step62.q])
      9000000000000
      (model62.caps 5)
      (model62.ord 5)
      12
      (.pair 1 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded62_6 :
    ExclusionHint.check
      (model62.B 6 ++ [step62.q])
      9000000000000
      (model62.caps 6)
      (model62.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded62_7 :
    ExclusionHint.check
      (model62.B 7 ++ [step62.q])
      9000000000000
      (model62.caps 7)
      (model62.ord 7)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded62_8 :
    ExclusionHint.check
      (model62.B 8 ++ [step62.q])
      9000000000000
      (model62.caps 8)
      (model62.ord 8)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded62_9 :
    ExclusionHint.check
      (model62.B 9 ++ [step62.q])
      9000000000000
      (model62.caps 9)
      (model62.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded63_0 :
    ExclusionHint.check
      (model63.B 0 ++ [step63.q])
      9000000000000
      (model63.caps 0)
      (model63.ord 0)
      12
      (.witnessedFan (.next ([6915000000000], [30000000000]) (some (10, 2, 5))
      (some (10, 3, 5)) (.next ([6915000000000], [195000000000]) (some (10, 3, 5)) (some (10, 3, 5))
      (.next ([3615000000000], [315000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
      ([6855000000000], [915000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([6750000000000],
      [1110000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([915000000000], [165000000000])
      (some (10, 3, 5)) (some (10, 3, 5)) (.next ([750000000000], [165000000000]) (some (10, 3, 5))
      (some (10, 3, 5)) (.next ([5730000000000], [1560000000000]) (some (10, 3, 5)) (some (10, 3,
      5)) (.next ([2055000000000], [585000000000]) (some (10, 3, 5)) (some (10, 3, 5))
      fan63Owner0Part3))))))))))
      0
      1
      100 = true := by
  certify_fan

end Sext180000190000
end ConwaySoifer.Simplified.Certificates
