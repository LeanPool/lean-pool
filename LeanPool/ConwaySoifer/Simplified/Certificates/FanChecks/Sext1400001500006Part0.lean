/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1400001500006
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sext1400001500006Part0. -/

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

theorem checkedWitnessForExcluded48_0 :
    ExclusionHint.check
      (model48.B 0 ++ [step48.q])
      9000000000000
      (model48.caps 0)
      (model48.ord 0)
      12
      (.pair 4 8)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded48_1 :
    ExclusionHint.check
      (model48.B 1 ++ [step48.q])
      9000000000000
      (model48.caps 1)
      (model48.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded48_2 :
    ExclusionHint.check
      (model48.B 2 ++ [step48.q])
      9000000000000
      (model48.caps 2)
      (model48.ord 2)
      12
      (.witnessedFan (.next ([5475000000000], [690000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([3120000000000], [900000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([3330000000000], [3045000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([3960000000000], [6165000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1260000000000,
      9000000000000], [4650000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([630000000000],
      [3120000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0], [4650000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([-690000000000], [6165000000000]) (some (0, 4, 2)) (some (0, 4,
      3)) (.next ([-900000000000], [4020000000000]) (some (0, 4, 3)) (some (4, 4, 3)) (.next
      ([-3045000000000], [6375000000000]) (some (4, 4, 3)) (some (4, 4, 3)) (.next
      ([-6165000000000], [10125000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next
      ([-4650000000000, 0], [5910000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3120000000000], [3750000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3)))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded48_4 :
    ExclusionHint.check
      (model48.B 4 ++ [step48.q])
      9000000000000
      (model48.caps 4)
      (model48.ord 4)
      12
      (.witnessedFan (.next ([7875000000000], [465000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([5040000000000], [1575000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([5040000000000], [2835000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([2025000000000], [1185000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([1635000000000, 9000000000000], [4590000000000, -9000000000000]) (some (3, 1, 2)) (some (3,
      1, 4)) (.next ([1260000000000, 9000000000000], [5505000000000]) (some (3, 1, 4)) (some (3, 1,
      4)) (.next ([720000000000], [5130000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([375000000000], [5850000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [5505000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-465000000000], [8340000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1575000000000, 9000000000000], [6615000000000,
      -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2835000000000], [7875000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1185000000000], [3210000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-4590000000000, 9000000000000], [6225000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5505000000000], [6765000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5130000000000], [5850000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-5850000000000], [6225000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4)))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded48_5 :
    ExclusionHint.check
      (model48.B 5 ++ [step48.q])
      9000000000000
      (model48.caps 5)
      (model48.ord 5)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded48_6 :
    ExclusionHint.check
      (model48.B 6 ++ [step48.q])
      9000000000000
      (model48.caps 6)
      (model48.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded48_7 :
    ExclusionHint.check
      (model48.B 7 ++ [step48.q])
      9000000000000
      (model48.caps 7)
      (model48.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded48_8 :
    ExclusionHint.check
      (model48.B 8 ++ [step48.q])
      9000000000000
      (model48.caps 8)
      (model48.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sext140000150000
end ConwaySoifer.Simplified.Certificates
