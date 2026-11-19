/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1500001600000
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown1500001600000Part1. -/

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

theorem checkedWitnessForExcluded0_9 :
    ExclusionHint.check
      (model0.B 9 ++ [step0.q])
      9000000000000
      (model0.caps 9)
      (model0.ord
    9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded1_1 :
    ExclusionHint.check
      (model1.B 1 ++ [step1.q])
      9000000000000
      (model1.caps 1)
      (model1.ord
    1)
      12
      (.pair 2 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded1_2 :
    ExclusionHint.check
      (model1.B 2 ++ [step1.q])
      9000000000000
      (model1.caps 2)
      (model1.ord
    2)
      12
      (.pair 1 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded1_3 :
    ExclusionHint.check
      (model1.B 3 ++ [step1.q])
      9000000000000
      (model1.caps 3)
      (model1.ord
    3)
      12
      (.pair 2 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded1_4 :
    ExclusionHint.check
      (model1.B 4 ++ [step1.q])
      9000000000000
      (model1.caps 4)
      (model1.ord
    4)
      12
      (.witnessedFan (.next ([7350000000000, -9000000000000], [900000000000,
      9000000000000]) (some (2, 0, 3)) (some (2, 1, 3)) (.next ([1350000000000, 9000000000000],
      [1350000000000, 9000000000000]) (some (2, 1, 3)) (some (2, 1, 3)) (.next ([1800000000000,
      9000000000000], [6900000000000, -9000000000000]) (some (2, 1, 3)) (some (2, 1, 3)) (.next
      ([450000000000], [8250000000000]) (some (2, 1, 3)) (some (2, 1, 3)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (2, 1, 3)) (some (2, 1, 3)) (.next ([-900000000000,
      -9000000000000], [8250000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1350000000000, -9000000000000], [2700000000000, 18000000000000]) (some (0, 1, 3)) (some (0,
      3, 3)) (.next ([-6900000000000, 9000000000000], [8700000000000]) (some (0, 3, 3)) (some (0, 3,
      3)) (.next ([-8250000000000], [8700000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal
      (some (0, 3, 2)) (some (0, 3, 2)) (some (0, 3, 2)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded1_5 :
    ExclusionHint.check
      (model1.B 5 ++ [step1.q])
      9000000000000
      (model1.caps 5)
      (model1.ord
    5)
      12
      (.witnessedFan (.next ([8250000000000], [300000000000]) (some (3, 0, 2))
      (some (3, 1, 2)) (.next ([6900000000000, -9000000000000], [1650000000000, 9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([1050000000000, 9000000000000],
      [7200000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-300000000000],
      [8550000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-1650000000000, -9000000000000],
      [8550000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-7200000000000,
      9000000000000], [8250000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded1_6 :
    ExclusionHint.check
      (model1.B 6 ++ [step1.q])
      9000000000000
      (model1.caps 6)
      (model1.ord
    6)
      12
      (.witnessedFan (.next ([8550000000000], [750000000000]) (some (3, 0, 1))
      (some (3, 0, 2)) (.next ([7200000000000, -9000000000000], [2100000000000, 9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([600000000000, 9000000000000],
      [7950000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-750000000000],
      [9300000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2100000000000, -9000000000000],
      [9300000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-7950000000000,
      9000000000000], [8550000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.terminal (some (0, 1, 3))
      (some (0, 1, 3)) (some (0, 1, 3)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded1_7 :
    ExclusionHint.check
      (model1.B 7 ++ [step1.q])
      9000000000000
      (model1.caps 7)
      (model1.ord
    7)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

end Aown150000160000
end ConwaySoifer.Simplified.Certificates
