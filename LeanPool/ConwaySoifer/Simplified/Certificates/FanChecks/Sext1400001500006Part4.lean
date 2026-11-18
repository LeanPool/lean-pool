/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1400001500006
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sext1400001500006Part4. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sext140000150000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sext140000150000

theorem checkedWitnessForExcluded51_6 :
    ExclusionHint.check
      (model51.B 6 ++ [step51.q])
      9000000000000
      (model51.caps 6)
      (model51.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded51_7 :
    ExclusionHint.check
      (model51.B 7 ++ [step51.q])
      9000000000000
      (model51.caps 7)
      (model51.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded51_8 :
    ExclusionHint.check
      (model51.B 8 ++ [step51.q])
      9000000000000
      (model51.caps 8)
      (model51.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded51_9 :
    ExclusionHint.check
      (model51.B 9 ++ [step51.q])
      9000000000000
      (model51.caps 9)
      (model51.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded52_0 :
    ExclusionHint.check
      (model52.B 0 ++ [step52.q])
      9000000000000
      (model52.caps 0)
      (model52.ord 0)
      12
      (.witnessedFan (.next ([1125000000000], [45000000000]) (some (8, 2, 4))
      (some (8, 3, 4)) (.next ([1080000000000], [90000000000]) (some (8, 3, 4)) (some (8, 3, 4))
      (.next ([6810000000000], [690000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next
      ([6045000000000], [930000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next ([5955000000000],
      [930000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([7035000000000], [1125000000000])
      (some (7, 3, 4)) (some (7, 3, 4)) (.next ([6060000000000], [1065000000000]) (some (7, 3, 4))
      (some (7, 3, 8)) (.next ([6375000000000], [1350000000000]) (some (7, 3, 8)) (some (7, 3, 8))
      (.next ([5295000000000], [1260000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
      ([6000000000000], [2100000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([375000000000],
      [375000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([1305000000000], [1530000000000])
      (some (7, 3, 8)) (some (7, 3, 8)) (.next ([705000000000], [840000000000]) (some (7, 3, 8))
      (some (7, 3, 8)) (.next ([330000000000], [420000000000]) (some (7, 3, 8)) (some (7, 3, 8))
      (.next ([2010000000000], [3585000000000]) (some (0, 3, 8)) (some (0, 3, 8))
      fan52Owner0Part1))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded52_2 :
    ExclusionHint.check
      (model52.B 2 ++ [step52.q])
      9000000000000
      (model52.caps 2)
      (model52.ord 2)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded52_3 :
    ExclusionHint.check
      (model52.B 3 ++ [step52.q])
      9000000000000
      (model52.caps 3)
      (model52.ord 3)
      12
      (.pair 0 10)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded52_4 :
    ExclusionHint.check
      (model52.B 4 ++ [step52.q])
      9000000000000
      (model52.caps 4)
      (model52.ord 4)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

end Sext140000150000
end ConwaySoifer.Simplified.Certificates
