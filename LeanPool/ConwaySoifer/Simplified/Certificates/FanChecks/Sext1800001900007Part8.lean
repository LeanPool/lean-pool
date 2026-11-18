/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1800001900007
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sext1800001900007Part8. -/

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

theorem checkedWitnessForExcluded63_1 :
    ExclusionHint.check
      (model63.B 1 ++ [step63.q])
      9000000000000
      (model63.caps 1)
      (model63.ord 1)
      12
      (.witnessedFan (.next ([3015000000000, -9000000000000], [810000000000,
      9000000000000]) (some (4, 4, 1)) (some (4, 4, 2)) (.next ([2430000000000, 9000000000000],
      [2205000000000, -9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([5175000000000,
      9000000000000], [4950000000000, -9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([2745000000000], [2745000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3555000000000],
      [6570000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1935000000000, -9000000000000],
      [6570000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([810000000000], [3825000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0], [1620000000000, 9000000000000]) (some (4, 1,
      2)) (some (4, 1, 2)) (.next ([-810000000000, -9000000000000], [3825000000000, 0]) (some (4, 1,
      2)) (some (4, 1, 3)) (.next ([-2205000000000, 9000000000000], [4635000000000]) (some (4, 1,
      3)) (some (4, 1, 3)) (.next ([-4950000000000, 9000000000000], [10125000000000]) (some (4, 1,
      3)) (some (4, 1, 3)) (.next ([-2745000000000], [5490000000000]) (some (4, 1, 3)) (some (4, 1,
      3)) (.next ([-6570000000000], [10125000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-6570000000000, 0], [8505000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-3825000000000], [4635000000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.terminal (some
      (4, 1, 4)) (some (4, 1, 4)) (some (4, 1, 4)))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded63_3 :
    ExclusionHint.check
      (model63.B 3 ++ [step63.q])
      9000000000000
      (model63.caps 3)
      (model63.ord 3)
      12
      (.split (0) (3) (4) (400) (.witnessedFan (.next ([7875000000000],
      [555000000000]) (some (4, 0, 6)) (some (5, 0, 6)) (.next ([4950000000000], [675000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([5445000000000, 0], [810000000000, -9000000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1995000000000], [330000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([4635000000000], [1305000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([5130000000000, 9000000000000], [1620000000000, -9000000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([2445000000000], [810000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([5445000000000], [2430000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([3000000000000], [1620000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([4620000000000],
      [3000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1710000000000], [1425000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3510000000000], [3240000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([1995000000000, 9000000000000], [3330000000000, -9000000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1380000000000], [3750000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([750000000000], [2490000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      fan63Owner3Part0)))))))))))))))) (.witnessedFan (.next ([7875000000000], [555000000000]) (some
      (4, 0, 6)) (some (5, 0, 6)) (.next ([5445000000000, 0], [810000000000, -9000000000000]) (some
      (5, 0, 6)) (some (5, 0, 6)) (.next ([4950000000000], [675000000000]) (some (5, 0, 6)) (some
      (5, 0, 6)) (.next ([1995000000000], [330000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([4635000000000], [1305000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([5130000000000,
      9000000000000], [1620000000000, -9000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([2445000000000], [810000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([5445000000000],
      [2430000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3000000000000], [1620000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([4620000000000], [3000000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([1710000000000], [1425000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([3510000000000], [3240000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([1995000000000, 9000000000000], [3330000000000, -9000000000000]) (some (5, 0, 6)) (some (5,
      0, 6)) (.next ([1380000000000], [3750000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([750000000000], [2490000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      fan63Owner3Part1)))))))))))))))))
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded63_4 :
    ExclusionHint.check
      (model63.B 4 ++ [step63.q])
      9000000000000
      (model63.caps 4)
      (model63.ord 4)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded63_5 :
    ExclusionHint.check
      (model63.B 5 ++ [step63.q])
      9000000000000
      (model63.caps 5)
      (model63.ord 5)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded63_6 :
    ExclusionHint.check
      (model63.B 6 ++ [step63.q])
      9000000000000
      (model63.caps 6)
      (model63.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded63_7 :
    ExclusionHint.check
      (model63.B 7 ++ [step63.q])
      9000000000000
      (model63.caps 7)
      (model63.ord 7)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded63_8 :
    ExclusionHint.check
      (model63.B 8 ++ [step63.q])
      9000000000000
      (model63.caps 8)
      (model63.ord 8)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded63_9 :
    ExclusionHint.check
      (model63.B 9 ++ [step63.q])
      9000000000000
      (model63.caps 9)
      (model63.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

end Sext180000190000
end ConwaySoifer.Simplified.Certificates
