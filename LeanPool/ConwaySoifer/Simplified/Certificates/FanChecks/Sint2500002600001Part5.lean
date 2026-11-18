/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2500002600001
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2500002600001Part5. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint250000260000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint250000260000

theorem checkedWitnessForExcluded12_5 :
    ExclusionHint.check
      (model12.B 5 ++ [step12.q])
      9000000000000
      (model12.caps 5)
      (model12.ord 5)
      12
      (.witnessedFan (.next ([4575000000000, 0], [2925000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([2250000000000, 9000000000000],
      [2250000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4575000000000],
      [5175000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2325000000000, -9000000000000],
      [7425000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [2250000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-2925000000000,
      9000000000000], [7500000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 2, 3)) (.next
      ([-2250000000000, -9000000000000], [4500000000000, 18000000000000]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-5175000000000], [9750000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-7425000000000, -9000000000000], [9750000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.terminal (some (0, 2, 3)) (some (0, 2, 3)) (some (0, 2, 3)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded12_6 :
    ExclusionHint.check
      (model12.B 6 ++ [step12.q])
      9000000000000
      (model12.caps 6)
      (model12.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded12_7 :
    ExclusionHint.check
      (model12.B 7 ++ [step12.q])
      9000000000000
      (model12.caps 7)
      (model12.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded12_8 :
    ExclusionHint.check
      (model12.B 8 ++ [step12.q])
      9000000000000
      (model12.caps 8)
      (model12.ord 8)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded12_9 :
    ExclusionHint.check
      (model12.B 9 ++ [step12.q])
      9000000000000
      (model12.caps 9)
      (model12.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded13_0 :
    ExclusionHint.check
      (model13.B 0 ++ [step13.q])
      9000000000000
      (model13.caps 0)
      (model13.ord 0)
      12
      (.pair 6 9)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded13_1 :
    ExclusionHint.check
      (model13.B 1 ++ [step13.q])
      9000000000000
      (model13.caps 1)
      (model13.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded13_2 :
    ExclusionHint.check
      (model13.B 2 ++ [step13.q])
      9000000000000
      (model13.caps 2)
      (model13.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint250000260000
end ConwaySoifer.Simplified.Certificates
