/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1500001600000
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sext1500001600000Part6. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sext150000160000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sext150000160000

theorem checkedWitnessForExcluded5_3 :
    ExclusionHint.check
      (model5.B 3 ++ [step5.q])
      9000000000000
      (model5.caps 3)
      (model5.ord
    3)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded5_5 :
    ExclusionHint.check
      (model5.B 5 ++ [step5.q])
      9000000000000
      (model5.caps 5)
      (model5.ord
    5)
      12
      (.pair 2 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded5_6 :
    ExclusionHint.check
      (model5.B 6 ++ [step5.q])
      9000000000000
      (model5.caps 6)
      (model5.ord
    6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded5_7 :
    ExclusionHint.check
      (model5.B 7 ++ [step5.q])
      9000000000000
      (model5.caps 7)
      (model5.ord
    7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded5_8 :
    ExclusionHint.check
      (model5.B 8 ++ [step5.q])
      9000000000000
      (model5.caps 8)
      (model5.ord
    8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded5_9 :
    ExclusionHint.check
      (model5.B 9 ++ [step5.q])
      9000000000000
      (model5.caps 9)
      (model5.ord
    9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded6_1 :
    ExclusionHint.check
      (model6.B 1 ++ [step6.q])
      9000000000000
      (model6.caps 1)
      (model6.ord
    1)
      12
      (.witnessedFan (.next ([5400000000000], [3150000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([5400000000000], [4500000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([1350000000000, 9000000000000], [1350000000000, 9000000000000]) (some
      (0, 3, 2)) (some (0, 3, 2)) (.next ([4050000000000, -9000000000000], [5850000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1350000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-3150000000000, 9000000000000],
      [8550000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-4500000000000],
      [9900000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-5850000000000,
      -9000000000000], [9900000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded6_2 :
    ExclusionHint.check
      (model6.B 2 ++ [step6.q])
      9000000000000
      (model6.caps 2)
      (model6.ord
    2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sext150000160000
end ConwaySoifer.Simplified.Certificates
