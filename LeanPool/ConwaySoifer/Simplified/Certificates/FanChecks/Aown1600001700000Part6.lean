/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1600001700000
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown1600001700000Part6. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Aown160000170000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Aown160000170000

theorem checkedWitnessForExcluded5_4 :
    ExclusionHint.check
      (model5.B 4 ++ [step5.q])
      9000000000000
      (model5.caps 4)
      (model5.ord
    4)
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
      (.pair 0 3)
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
      (.witnessedFan (.next ([7560000000000, -9000000000000], [0,
      9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([1440000000000, 9000000000000],
      [1440000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2880000000000,
      9000000000000], [6120000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([1440000000000], [7560000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [1440000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, -9000000000000],
      [7560000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-1440000000000, -9000000000000],
      [2880000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-6120000000000,
      9000000000000], [9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-7560000000000],
      [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1,
      3)) (some (0, 1, 3)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded5_7 :
    ExclusionHint.check
      (model5.B 7 ++ [step5.q])
      9000000000000
      (model5.caps 7)
      (model5.ord
    7)
      12
      (.pair 1 4)
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

theorem checkedWitnessForExcluded6_0 :
    ExclusionHint.check
      (model6.B 0 ++ [step6.q])
      9000000000000
      (model6.caps 0)
      (model6.ord
    0)
      12
      (.witnessedFan (.next ([1838400000000, 2490000000000], [398400000000,
      2490000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([796800000000, 4980000000000],
      [261600000000, -2490000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([1058400000000,
      2490000000000], [398400000000, 2490000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([1440000000000], [660000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([261600000000,
      -2490000000000], [136800000000, 4980000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([1041600000000, -2490000000000], [796800000000, 4980000000000]) (some (10, 2, 10)) (some (10,
      3, 10)) (.next ([780000000000], [660000000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next
      ([398400000000, 2490000000000], [398400000000, 2490000000000]) (some (10, 3, 10)) (some (10,
      3, 10)) (.next ([660000000000], [780000000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next
      ([796800000000, 4980000000000], [1041600000000, -2490000000000]) (some (10, 3, 10)) (some (10,
      3, 10)) (.next ([3660000000000], [5340000000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next
      ([3398400000000, 2490000000000], [5203200000000, -4980000000000]) (some (9, 3, 10)) (some (9,
      3, 10)) (.next ([3660000000000], [6000000000000]) (some (9, 3, 10)) (some (0, 4, 10)) (.next
      ([3000000000000], [5340000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([3398400000000,
      2490000000000], [6398400000000, 2490000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
      ([660000000000], [1440000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([3000000000000],
      [6660000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([398400000000, 2490000000000],
      [1058400000000, 2490000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([2340000000000],
      [6660000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([261600000000, -2490000000000],
      [796800000000, 4980000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([1560000000000],
      [6000000000000]) (some (0, 4, 10)) (some (0, 4, 10)) fan6Owner0Part0))))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded6_1 :
    ExclusionHint.check
      (model6.B 1 ++ [step6.q])
      9000000000000
      (model6.caps 1)
      (model6.ord
    1)
      12
      (.witnessedFan (.next ([1440000000000, 9000000000000], [1440000000000,
      9000000000000]) none none (.next ([1440000000000, 9000000000000], [3060000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1500000000000], [4500000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1440000000000, 9000000000000], [6000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [4560000000000, -9000000000000]) (some (3,
      1, 2)) (some (3, 1, 2)) (.next ([-1440000000000, -9000000000000], [2880000000000,
      18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3060000000000, 9000000000000],
      [4500000000000, 0]) (some (3, 1, 2)) none (.next ([-4500000000000], [6000000000000]) none none
      (.next ([-6000000000000], [7440000000000, 9000000000000]) none none (.terminal none none
      none)))))))))))
      0
      1
      100 = true := by
  certify_fan

end Aown160000170000
end ConwaySoifer.Simplified.Certificates
