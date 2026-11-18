/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint1500001600001
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint1500001600001Part1. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint150000160000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint150000160000

theorem checkedWitnessForExcluded8_9 :
    ExclusionHint.check
      (model8.B 9 ++ [step8.q])
      9000000000000
      (model8.caps 9)
      (model8.ord
    9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded9_0 :
    ExclusionHint.check
      (model9.B 0 ++ [step9.q])
      9000000000000
      (model9.caps 0)
      (model9.ord
    0)
      12
      (.witnessedFan (.next ([4881000000000, 5040000000000], [72000000000,
      -2520000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([4428000000000, 2520000000000],
      [144000000000, -5040000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([3978000000000,
      2520000000000], [144000000000, -5040000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([4806000000000, 5040000000000], [522000000000, -2520000000000]) (some (7, 8, 4)) (some (7, 8,
      4)) (.next ([4356000000000, 5040000000000], [522000000000, -2520000000000]) (some (7, 8, 4))
      (some (7, 8, 4)) (.next ([450000000000], [75000000000]) (some (7, 8, 4)) (some (7, 8, 4))
      (.next ([4428000000000, 2520000000000], [753000000000, 2520000000000]) (some (7, 8, 4)) (some
      (7, 8, 4)) (.next ([4503000000000, 2520000000000], [828000000000, 2520000000000]) (some (7, 8,
      4)) (some (7, 8, 4)) (.next ([375000000000], [75000000000]) (some (7, 8, 4)) (some (7, 8, 4))
      (.next ([4428000000000, 2520000000000], [1278000000000, 2520000000000]) (some (7, 8, 4)) (some
      (7, 8, 4)) (.next ([3978000000000, 2520000000000], [1278000000000, 2520000000000]) (some (7,
      8, 4)) (some (7, 8, 4)) fan9Owner0Part1))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded9_1 :
    ExclusionHint.check
      (model9.B 1 ++ [step9.q])
      9000000000000
      (model9.caps 1)
      (model9.ord
    1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded9_2 :
    ExclusionHint.check
      (model9.B 2 ++ [step9.q])
      9000000000000
      (model9.caps 2)
      (model9.ord
    2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded9_3 :
    ExclusionHint.check
      (model9.B 3 ++ [step9.q])
      9000000000000
      (model9.caps 3)
      (model9.ord
    3)
      12
      (.pair 1 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded9_5 :
    ExclusionHint.check
      (model9.B 5 ++ [step9.q])
      9000000000000
      (model9.caps 5)
      (model9.ord
    5)
      12
      (.witnessedFan (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([3000000000000, 0], [5220000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3000000000000], [6570000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1650000000000, -9000000000000], [7920000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1350000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (3, 1, 3)) (some (3, 2, 3)) (.next ([-5220000000000,
      9000000000000], [8220000000000, -9000000000000]) (some (3, 2, 3)) (some (3, 2, 3)) (.next
      ([-6570000000000], [9570000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-7920000000000,
      -9000000000000], [9570000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded9_6 :
    ExclusionHint.check
      (model9.B 6 ++ [step9.q])
      9000000000000
      (model9.caps 6)
      (model9.ord
    6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded9_7 :
    ExclusionHint.check
      (model9.B 7 ++ [step9.q])
      9000000000000
      (model9.caps 7)
      (model9.ord
    7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint150000160000
end ConwaySoifer.Simplified.Certificates
