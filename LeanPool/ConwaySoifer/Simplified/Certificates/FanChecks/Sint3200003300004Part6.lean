/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint3200003300004
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint3200003300004Part6. -/

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

theorem checkedWitnessForExcluded37_3 :
    ExclusionHint.check
      (model37.B 3 ++ [step37.q])
      9000000000000
      (model37.caps 3)
      (model37.ord 3)
      12
      (.witnessedFan (.next ([8865000000000], [135000000000]) (some (3, 5, 5))
      (some (4, 5, 5)) (.next ([8025000000000], [225000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([861000000000], [264000000000]) (some (4, 5, 3)) (some (4, 5, 3)) fan37Owner3Part0))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded37_5 :
    ExclusionHint.check
      (model37.B 5 ++ [step37.q])
      9000000000000
      (model37.caps 5)
      (model37.ord 5)
      12
      (.witnessedFan (.next ([3390000000000], [360000000000]) (some (6, 0, 3))
      (some (6, 1, 3)) (.next ([3375000000000], [441000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([66000000000], [15000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([4380000000000], [1785000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([2835000000000],
      [1350000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4380000000000, 0], [2880000000000,
      9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([510000000000, -9000000000000],
      [360000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4815000000000], [4185000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3285000000000, -9000000000000], [2880000000000,
      9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4020000000000], [3750000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3939000000000], [3816000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) fan37Owner5Part0))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded37_6 :
    ExclusionHint.check
      (model37.B 6 ++ [step37.q])
      9000000000000
      (model37.caps 6)
      (model37.ord 6)
      12
      (.pair 2 7)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded37_7 :
    ExclusionHint.check
      (model37.B 7 ++ [step37.q])
      9000000000000
      (model37.caps 7)
      (model37.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded37_8 :
    ExclusionHint.check
      (model37.B 8 ++ [step37.q])
      9000000000000
      (model37.caps 8)
      (model37.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded37_9 :
    ExclusionHint.check
      (model37.B 9 ++ [step37.q])
      9000000000000
      (model37.caps 9)
      (model37.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded38_0 :
    ExclusionHint.check
      (model38.B 0 ++ [step38.q])
      9000000000000
      (model38.caps 0)
      (model38.ord 0)
      12
      (.pair 4 6)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded38_1 :
    ExclusionHint.check
      (model38.B 1 ++ [step38.q])
      9000000000000
      (model38.caps 1)
      (model38.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint320000330000
end ConwaySoifer.Simplified.Certificates
