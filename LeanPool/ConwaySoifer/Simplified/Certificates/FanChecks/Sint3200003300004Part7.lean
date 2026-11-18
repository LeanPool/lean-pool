/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint3200003300004
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint3200003300004Part7. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint320000330000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint320000330000

theorem checkedWitnessForExcluded38_2 :
    ExclusionHint.check
      (model38.B 2 ++ [step38.q])
      9000000000000
      (model38.caps 2)
      (model38.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded38_3 :
    ExclusionHint.check
      (model38.B 3 ++ [step38.q])
      9000000000000
      (model38.caps 3)
      (model38.ord 3)
      12
      (.pair 2 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded38_5 :
    ExclusionHint.check
      (model38.B 5 ++ [step38.q])
      9000000000000
      (model38.caps 5)
      (model38.ord 5)
      12
      (.witnessedFan (.next ([5760000000000, 0], [255000000000,
      9000000000000]) (some (5, 0, 3)) (some (5, 1, 3)) (.next ([3390000000000], [360000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3135000000000], [405000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([3375000000000], [441000000000]) (some (5, 1, 3)) (some (6, 1, 3))
      (.next ([5400000000000], [1125000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([5319000000000], [1191000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([66000000000],
      [15000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4380000000000], [1785000000000])
      (some (6, 1, 3)) (some (6, 1, 4)) (.next ([4380000000000, 0], [2880000000000, 9000000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([510000000000, -9000000000000], [360000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3285000000000, -9000000000000], [2880000000000,
      9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) fan38Owner5Part0))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded38_6 :
    ExclusionHint.check
      (model38.B 6 ++ [step38.q])
      9000000000000
      (model38.caps 6)
      (model38.ord 6)
      12
      (.pair 3 7)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded38_7 :
    ExclusionHint.check
      (model38.B 7 ++ [step38.q])
      9000000000000
      (model38.caps 7)
      (model38.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded38_8 :
    ExclusionHint.check
      (model38.B 8 ++ [step38.q])
      9000000000000
      (model38.caps 8)
      (model38.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded38_9 :
    ExclusionHint.check
      (model38.B 9 ++ [step38.q])
      9000000000000
      (model38.caps 9)
      (model38.ord 9)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded39_1 :
    ExclusionHint.check
      (model39.B 1 ++ [step39.q])
      9000000000000
      (model39.caps 1)
      (model39.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint320000330000
end ConwaySoifer.Simplified.Certificates
