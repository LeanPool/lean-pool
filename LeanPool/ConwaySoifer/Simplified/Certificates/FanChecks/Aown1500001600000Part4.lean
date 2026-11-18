/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1500001600000
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown1500001600000Part4. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Aown150000160000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Aown150000160000

theorem checkedWitnessForExcluded3_6 :
    ExclusionHint.check
      (model3.B 6 ++ [step3.q])
      9000000000000
      (model3.caps 6)
      (model3.ord
    6)
      12
      (.witnessedFan (.next ([7650000000000, -9000000000000], [0,
      9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([1350000000000, 9000000000000],
      [1350000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2700000000000,
      9000000000000], [6300000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([1350000000000], [7650000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, -9000000000000],
      [7650000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-6300000000000,
      9000000000000], [9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-7650000000000],
      [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1,
      3)) (some (0, 1, 3)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded3_7 :
    ExclusionHint.check
      (model3.B 7 ++ [step3.q])
      9000000000000
      (model3.caps 7)
      (model3.ord
    7)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded3_8 :
    ExclusionHint.check
      (model3.B 8 ++ [step3.q])
      9000000000000
      (model3.caps 8)
      (model3.ord
    8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded3_9 :
    ExclusionHint.check
      (model3.B 9 ++ [step3.q])
      9000000000000
      (model3.caps 9)
      (model3.ord
    9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded4_0 :
    ExclusionHint.check
      (model4.B 0 ++ [step4.q])
      9000000000000
      (model4.caps 0)
      (model4.ord
    0)
      12
      (.split (0) (5) (8) (800) (.witnessedFan (.next ([1056000000000,
      5040000000000], [72000000000, -2520000000000]) (some (8, 2, 8)) (some (8, 2, 8)) (.next
      ([1128000000000, 2520000000000], [78000000000, 2520000000000]) (some (8, 2, 8)) (some (8, 2,
      8)) (.next ([7503000000000, 2520000000000], [669000000000, -5040000000000]) (some (8, 2, 8))
      (some (8, 2, 8)) (.next ([7881000000000, 5040000000000], [1047000000000, -2520000000000])
      (some (7, 2, 8)) (some (7, 2, 8)) (.next ([7875000000000], [1125000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([1728000000000, 2520000000000], [378000000000, 2520000000000]) (some
      (7, 2, 8)) (some (7, 2, 8)) (.next ([7503000000000, 2520000000000], [1803000000000,
      2520000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([5775000000000], [1425000000000])
      (some (7, 2, 8)) (some (7, 2, 8)) (.next ([7425000000000], [1875000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([1650000000000], [450000000000]) (some (7, 2, 8)) (some (7, 2, 8))
      (.next ([6825000000000], [2175000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
      ([6747000000000, -2520000000000], [2181000000000, 5040000000000]) (some (7, 2, 8)) (some (7,
      2, 8)) (.next ([1050000000000], [750000000000]) (some (7, 2, 8)) (some (7, 3, 8)) (.next
      ([972000000000, -2520000000000], [756000000000, 5040000000000]) (some (7, 3, 8)) (some (7, 3,
      8)) (.next ([372000000000, -2520000000000], [306000000000, 5040000000000]) (some (7, 3, 8))
      (some (7, 3, 8)) (.next ([378000000000, 2520000000000], [378000000000, 2520000000000]) (some
      (7, 3, 8)) (some (7, 3, 8)) (.next ([306000000000, 5040000000000], [372000000000,
      -2520000000000]) (some (0, 3, 8)) (some (0, 4, 8)) (.next ([756000000000, 5040000000000],
      [972000000000, -2520000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([300000000000],
      [450000000000]) (some (0, 4, 8)) (some (0, 4, 8)) fan4Owner0Part0))))))))))))))))))))
      (.witnessedFan (.next ([1056000000000, 5040000000000], [72000000000, -2520000000000]) (some
      (8, 2, 8)) (some (8, 2, 8)) (.next ([7503000000000, 2520000000000], [669000000000,
      -5040000000000]) (some (8, 2, 8)) (some (8, 2, 8)) (.next ([7881000000000, 5040000000000],
      [1047000000000, -2520000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([7875000000000],
      [1125000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([1728000000000, 2520000000000],
      [378000000000, 2520000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([7503000000000,
      2520000000000], [1803000000000, 2520000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
      ([5775000000000], [1425000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([7425000000000],
      [1875000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([1650000000000], [450000000000])
      (some (7, 2, 8)) (some (7, 2, 8)) (.next ([6825000000000], [2175000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([6747000000000, -2520000000000], [2181000000000, 5040000000000])
      (some (7, 2, 8)) (some (7, 2, 8)) (.next ([1050000000000], [750000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([828000000000, 2520000000000], [678000000000, 2520000000000]) (some
      (7, 2, 8)) (some (7, 2, 8)) (.next ([972000000000, -2520000000000], [756000000000,
      5040000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([372000000000, -2520000000000],
      [306000000000, 5040000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([756000000000,
      5040000000000], [972000000000, -2520000000000]) (some (7, 3, 8)) (some (0, 5, 8)) (.next
      ([372000000000, -2520000000000], [456000000000, 5040000000000]) (some (0, 5, 8)) (some (0, 5,
      8)) (.next ([300000000000], [450000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next
      ([378000000000, 2520000000000], [1728000000000, 2520000000000]) (some (0, 5, 8)) (some (0, 5,
      8)) fan4Owner0Part1)))))))))))))))))))))
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded4_1 :
    ExclusionHint.check
      (model4.B 1 ++ [step4.q])
      9000000000000
      (model4.caps 1)
      (model4.ord
    1)
      12
      (.witnessedFan (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) none none (.next ([1875000000000], [3075000000000]) none none (.next
      ([900000000000, 9000000000000], [1875000000000]) none none (.next ([1350000000000,
      9000000000000], [3150000000000, -9000000000000]) none none (.next ([75000000000,
      -9000000000000], [450000000000, 0]) none none (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) none none (.next ([-3075000000000], [4950000000000]) none
      none (.next ([-1875000000000], [2775000000000, 9000000000000]) none none (.next
      ([-3150000000000, 9000000000000], [4500000000000, 0]) none none (.terminal none none
      none)))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded4_3 :
    ExclusionHint.check
      (model4.B 3 ++ [step4.q])
      9000000000000
      (model4.caps 3)
      (model4.ord
    3)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded4_4 :
    ExclusionHint.check
      (model4.B 4 ++ [step4.q])
      9000000000000
      (model4.caps 4)
      (model4.ord
    4)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Aown150000160000
end ConwaySoifer.Simplified.Certificates
