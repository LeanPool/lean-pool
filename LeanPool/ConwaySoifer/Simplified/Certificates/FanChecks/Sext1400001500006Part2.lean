/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1400001500006
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sext1400001500006Part2. -/

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

theorem checkedWitnessForExcluded49_8 :
    ExclusionHint.check
      (model49.B 8 ++ [step49.q])
      9000000000000
      (model49.caps 8)
      (model49.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded49_9 :
    ExclusionHint.check
      (model49.B 9 ++ [step49.q])
      9000000000000
      (model49.caps 9)
      (model49.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded50_0 :
    ExclusionHint.check
      (model50.B 0 ++ [step50.q])
      9000000000000
      (model50.caps 0)
      (model50.ord 0)
      12
      (.pair 4 8)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded50_1 :
    ExclusionHint.check
      (model50.B 1 ++ [step50.q])
      9000000000000
      (model50.caps 1)
      (model50.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded50_2 :
    ExclusionHint.check
      (model50.B 2 ++ [step50.q])
      9000000000000
      (model50.caps 2)
      (model50.ord 2)
      12
      (.witnessedFan (.next ([4980000000000], [1020000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([3120000000000], [900000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([1890000000000, 9000000000000], [1860000000000, -9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([3630000000000], [6000000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([1260000000000, 9000000000000], [4650000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([630000000000], [3120000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0],
      [4650000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1020000000000], [6000000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-900000000000], [4020000000000]) (some (0, 4, 3))
      (some (4, 4, 3)) (.next ([-1860000000000, 9000000000000], [3750000000000, 0]) (some (4, 4, 3))
      (some (4, 4, 3)) (.next ([-6000000000000], [9630000000000]) (some (4, 4, 3)) (some (4, 2, 3))
      (.next ([-4650000000000, 0], [5910000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-3120000000000], [3750000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some
      (4, 2, 3)) (some (4, 2, 0)) (some (4, 2, 3)))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded50_4 :
    ExclusionHint.check
      (model50.B 4 ++ [step50.q])
      9000000000000
      (model50.caps 4)
      (model50.ord 4)
      12
      (.witnessedFan (.next ([8370000000000], [135000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([5370000000000], [1740000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([2520000000000], [855000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([5370000000000], [3000000000000]) (some (3, 1, 2)) (some (3, 1, 4)) (.next
      ([1635000000000, 9000000000000], [4590000000000, -9000000000000]) (some (3, 1, 4)) (some (3,
      1, 4)) (.next ([1260000000000, 9000000000000], [5505000000000]) (some (3, 1, 4)) (some (3, 1,
      4)) (.next ([720000000000], [5130000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([375000000000], [5850000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [5505000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-135000000000], [8505000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1740000000000, 9000000000000], [7110000000000,
      -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-855000000000], [3375000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3000000000000], [8370000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-4590000000000, 9000000000000], [6225000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5505000000000], [6765000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5130000000000], [5850000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-5850000000000], [6225000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4)))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded50_5 :
    ExclusionHint.check
      (model50.B 5 ++ [step50.q])
      9000000000000
      (model50.caps 5)
      (model50.ord 5)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded50_6 :
    ExclusionHint.check
      (model50.B 6 ++ [step50.q])
      9000000000000
      (model50.caps 6)
      (model50.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sext140000150000
end ConwaySoifer.Simplified.Certificates
