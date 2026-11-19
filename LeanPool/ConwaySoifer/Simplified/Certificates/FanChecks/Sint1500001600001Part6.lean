/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint1500001600001
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint1500001600001Part6. -/

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

theorem checkedWitnessForExcluded13_3 :
    ExclusionHint.check
      (model13.B 3 ++ [step13.q])
      9000000000000
      (model13.caps 3)
      (model13.ord 3)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded13_4 :
    ExclusionHint.check
      (model13.B 4 ++ [step13.q])
      9000000000000
      (model13.caps 4)
      (model13.ord 4)
      12
      (.witnessedFan (.next ([3375000000000, 0], [0, 9000000000000]) (some (4,
      0, 6)) (some (4, 1, 6)) (.next ([7725000000000, 9000000000000], [825000000000,
      -9000000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([3375000000000, 0], [450000000000,
      9000000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([2430000000000], [570000000000])
      (some (4, 1, 6)) (some (4, 1, 6)) (.next ([6375000000000], [2175000000000]) (some (4, 1, 6))
      (some (4, 1, 6)) (.next ([5025000000000, -9000000000000], [2175000000000, 0]) (some (4, 1, 6))
      (some (4, 1, 6)) (.next ([1350000000000, 9000000000000], [1350000000000, 9000000000000]) (some
      (4, 1, 6)) (some (4, 6, 6)) (.next ([900000000000], [1125000000000, -9000000000000]) (some (4,
      6, 6)) (some (4, 6, 6)) (.next ([1350000000000], [2025000000000]) (some (4, 6, 6)) (some (5,
      6, 6)) fan13Owner4Part0))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded13_6 :
    ExclusionHint.check
      (model13.B 6 ++ [step13.q])
      9000000000000
      (model13.caps 6)
      (model13.ord 6)
      12
      (.witnessedFan (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([2625000000000, 0], [5475000000000,
      -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next ([2625000000000], [6825000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1275000000000, -9000000000000], [8175000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1350000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-5475000000000,
      9000000000000], [8100000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-6825000000000], [9450000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-8175000000000,
      -9000000000000], [9450000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 3)) (some (3, 1, 3)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded13_7 :
    ExclusionHint.check
      (model13.B 7 ++ [step13.q])
      9000000000000
      (model13.caps 7)
      (model13.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded13_8 :
    ExclusionHint.check
      (model13.B 8 ++ [step13.q])
      9000000000000
      (model13.caps 8)
      (model13.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded13_9 :
    ExclusionHint.check
      (model13.B 9 ++ [step13.q])
      9000000000000
      (model13.caps 9)
      (model13.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded14_0 :
    ExclusionHint.check
      (model14.B 0 ++ [step14.q])
      9000000000000
      (model14.caps 0)
      (model14.ord 0)
      12
      (.witnessedFan (.next ([4881000000000, 5040000000000], [72000000000,
      -2520000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([4428000000000, 2520000000000],
      [144000000000, -5040000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([3978000000000,
      2520000000000], [144000000000, -5040000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next
      ([4806000000000, 5040000000000], [522000000000, -2520000000000]) (some (8, 8, 4)) (some (8, 8,
      4)) (.next ([4356000000000, 5040000000000], [522000000000, -2520000000000]) (some (8, 8, 4))
      (some (8, 8, 4)) (.next ([450000000000], [75000000000]) (some (8, 8, 4)) (some (8, 8, 4))
      (.next ([4428000000000, 2520000000000], [753000000000, 2520000000000]) (some (8, 8, 4)) (some
      (8, 8, 4)) (.next ([4503000000000, 2520000000000], [828000000000, 2520000000000]) (some (8, 8,
      4)) (some (8, 8, 4)) (.next ([375000000000], [75000000000]) (some (8, 8, 4)) (some (8, 8, 4))
      fan14Owner0Part1))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded14_1 :
    ExclusionHint.check
      (model14.B 1 ++ [step14.q])
      9000000000000
      (model14.caps 1)
      (model14.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint150000160000
end ConwaySoifer.Simplified.Certificates
