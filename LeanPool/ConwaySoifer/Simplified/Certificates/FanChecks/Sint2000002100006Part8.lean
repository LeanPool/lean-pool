/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2000002100006
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2000002100006Part8. -/

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

theorem checkedWitnessForExcluded55_2 :
    ExclusionHint.check
      (model55.B 2 ++ [step55.q])
      9000000000000
      (model55.caps 2)
      (model55.ord 2)
      12
      (.witnessedFan (.next ([450000000000, -9000000000000], [0,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1800000000000], [450000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([7200000000000, -9000000000000], [1800000000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([6750000000000, -9000000000000],
      [2250000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3150000000000, -9000000000000],
      [1800000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4950000000000],
      [4050000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3150000000000, -9000000000000],
      [5850000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([2700000000000],
      [5850000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0], [1800000000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, -9000000000000], [450000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-450000000000], [2250000000000]) (some (0, 4, 3))
      (some (1, 4, 3)) (.next ([-1800000000000, -9000000000000], [9000000000000, 0]) (some (1, 4,
      3)) (some (1, 4, 3)) (.next ([-2250000000000, 0], [9000000000000, -9000000000000]) (some (1,
      4, 3)) (some (1, 4, 3)) (.next ([-1800000000000, -9000000000000], [4950000000000, 0]) (some
      (1, 4, 3)) (some (1, 4, 3)) (.next ([-4050000000000], [9000000000000]) (some (1, 2, 3)) (some
      (1, 2, 3)) (.next ([-5850000000000, -9000000000000], [9000000000000]) (some (1, 2, 3)) (some
      (1, 2, 3)) (.next ([-5850000000000], [8550000000000]) (some (1, 2, 3)) (some (1, 2, 3))
      (.terminal (some (1, 2, 3)) (some (4, 2, 0)) (some (4, 2, 3)))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded55_3 :
    ExclusionHint.check
      (model55.B 3 ++ [step55.q])
      9000000000000
      (model55.caps 3)
      (model55.ord 3)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded55_4 :
    ExclusionHint.check
      (model55.B 4 ++ [step55.q])
      9000000000000
      (model55.caps 4)
      (model55.ord 4)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded55_5 :
    ExclusionHint.check
      (model55.B 5 ++ [step55.q])
      9000000000000
      (model55.caps 5)
      (model55.ord 5)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded55_6 :
    ExclusionHint.check
      (model55.B 6 ++ [step55.q])
      9000000000000
      (model55.caps 6)
      (model55.ord 6)
      12
      (.witnessedFan (.next ([8175000000000], [225000000000]) (some (5, 1, 3))
      (some (5, 1, 4)) fan55Owner6Part0))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded55_7 :
    ExclusionHint.check
      (model55.B 7 ++ [step55.q])
      9000000000000
      (model55.caps 7)
      (model55.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded55_8 :
    ExclusionHint.check
      (model55.B 8 ++ [step55.q])
      9000000000000
      (model55.caps 8)
      (model55.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded55_9 :
    ExclusionHint.check
      (model55.B 9 ++ [step55.q])
      9000000000000
      (model55.caps 9)
      (model55.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint200000210000
end ConwaySoifer.Simplified.Certificates
