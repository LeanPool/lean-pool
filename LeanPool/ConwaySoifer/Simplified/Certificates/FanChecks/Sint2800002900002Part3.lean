/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2800002900002
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2800002900002Part3. -/

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

theorem checkedWitnessForExcluded18_6 :
    ExclusionHint.check
      (model18.B 6 ++ [step18.q])
      9000000000000
      (model18.caps 6)
      (model18.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded18_7 :
    ExclusionHint.check
      (model18.B 7 ++ [step18.q])
      9000000000000
      (model18.caps 7)
      (model18.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded18_9 :
    ExclusionHint.check
      (model18.B 9 ++ [step18.q])
      9000000000000
      (model18.caps 9)
      (model18.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded19_0 :
    ExclusionHint.check
      (model19.B 0 ++ [step19.q])
      9000000000000
      (model19.caps 0)
      (model19.ord 0)
      12
      (.witnessedFan (.next ([6090000000000], [165000000000]) (some (12, 12,
      6)) (some (12, 12, 7)) (.next ([5625000000000], [255000000000]) (some (12, 12, 7)) (some (12,
      12, 7)) (.next ([1856400000000, 2130000000000], [86400000000, 2130000000000]) (some (12, 12,
      7)) (some (12, 12, 7)) fan19Owner0Part4))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded19_1 :
    ExclusionHint.check
      (model19.B 1 ++ [step19.q])
      9000000000000
      (model19.caps 1)
      (model19.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded19_2 :
    ExclusionHint.check
      (model19.B 2 ++ [step19.q])
      9000000000000
      (model19.caps 2)
      (model19.ord 2)
      12
      (.pair 1 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded19_4 :
    ExclusionHint.check
      (model19.B 4 ++ [step19.q])
      9000000000000
      (model19.caps 4)
      (model19.ord 4)
      12
      (.witnessedFan (.next ([4125000000000], [339000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([3780000000000], [720000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([7125000000000, 0], [1515000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([2691000000000], [684000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([2310000000000], [720000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([3780000000000,
      0], [1770000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([750000000000],
      [510000000000, -9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([2181000000000,
      9000000000000], [1944000000000, -9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([2520000000000, 9000000000000], [2520000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1,
      2)) (.next ([1800000000000, 9000000000000], [1980000000000, -9000000000000]) (some (6, 1, 2))
      (some (6, 1, 2)) (.next ([2661000000000], [3120000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([1605000000000, -9000000000000], [2859000000000, 9000000000000]) (some (6, 1, 2))
      (some (6, 1, 6)) (.next ([1260000000000, -9000000000000], [3240000000000, 9000000000000])
      (some (6, 1, 6)) (some (6, 1, 6)) fan19Owner4Part0))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded19_5 :
    ExclusionHint.check
      (model19.B 5 ++ [step19.q])
      9000000000000
      (model19.caps 5)
      (model19.ord 5)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

end Sint280000290000
end ConwaySoifer.Simplified.Certificates
