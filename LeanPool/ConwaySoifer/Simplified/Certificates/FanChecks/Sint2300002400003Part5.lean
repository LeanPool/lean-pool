/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2300002400003
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2300002400003Part5. -/

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

theorem checkedWitnessForExcluded28_4 :
    ExclusionHint.check
      (model28.B 4 ++ [step28.q])
      9000000000000
      (model28.caps 4)
      (model28.ord 4)
      12
      (.witnessedFan (.next ([4860000000000], [126000000000]) (some (5, 0, 6))
      (some (5, 6, 6)) (.next ([285000000000], [15000000000]) (some (5, 6, 2)) (some (5, 6, 2))
      (.next ([4500000000000], [360000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([4890000000000], [486000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([4014000000000],
      [486000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([3624000000000], [516000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([3339000000000], [501000000000]) (some (5, 6, 2))
      (some (5, 6, 2)) (.next ([4875000000000], [786000000000]) (some (5, 6, 2)) (some (5, 6, 2))
      (.next ([4140000000000], [750000000000]) (some (5, 6, 2)) (some (5, 6, 2))
      fan28Owner4Part0))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded28_6 :
    ExclusionHint.check
      (model28.B 6 ++ [step28.q])
      9000000000000
      (model28.caps 6)
      (model28.ord 6)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded28_7 :
    ExclusionHint.check
      (model28.B 7 ++ [step28.q])
      9000000000000
      (model28.caps 7)
      (model28.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded28_8 :
    ExclusionHint.check
      (model28.B 8 ++ [step28.q])
      9000000000000
      (model28.caps 8)
      (model28.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded28_9 :
    ExclusionHint.check
      (model28.B 9 ++ [step28.q])
      9000000000000
      (model28.caps 9)
      (model28.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded29_0 :
    ExclusionHint.check
      (model29.B 0 ++ [step29.q])
      9000000000000
      (model29.caps 0)
      (model29.ord 0)
      12
      (.pair 9 12)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded29_1 :
    ExclusionHint.check
      (model29.B 1 ++ [step29.q])
      9000000000000
      (model29.caps 1)
      (model29.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded29_2 :
    ExclusionHint.check
      (model29.B 2 ++ [step29.q])
      9000000000000
      (model29.caps 2)
      (model29.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint230000240000
end ConwaySoifer.Simplified.Certificates
