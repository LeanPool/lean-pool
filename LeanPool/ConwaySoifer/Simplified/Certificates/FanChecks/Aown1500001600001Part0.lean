/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1500001600001
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown1500001600001Part0. -/

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

theorem checkedWitnessForExcluded8_0 :
    ExclusionHint.check
      (model8.B 0 ++ [step8.q])
      9000000000000
      (model8.caps 0)
      (model8.ord
    0)
      12
      (.witnessedFan (.next ([1056000000000, 5040000000000], [72000000000,
      -2520000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([1128000000000, 2520000000000],
      [78000000000, 2520000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([1728000000000,
      2520000000000], [378000000000, 2520000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next
      ([1650000000000], [450000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([6528000000000,
      2520000000000], [2094000000000, -5040000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next
      ([6906000000000, 5040000000000], [2472000000000, -2520000000000]) (some (8, 2, 6)) (some (8,
      2, 6)) (.next ([6900000000000], [2550000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next
      ([5772000000000, -2520000000000], [2472000000000, -2520000000000]) (some (8, 2, 6)) (some (8,
      2, 6)) (.next ([6600000000000], [3150000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next
      ([6528000000000, 2520000000000], [3228000000000, 2520000000000]) (some (8, 2, 6)) (some (8, 2,
      6)) (.next ([1050000000000], [750000000000]) (some (8, 2, 6)) (some (8, 3, 6)) (.next
      ([972000000000, -2520000000000], [756000000000, 5040000000000]) (some (8, 3, 6)) (some (8, 3,
      6)) (.next ([4800000000000], [4200000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
      ([378000000000, 2520000000000], [378000000000, 2520000000000]) (some (8, 3, 6)) (some (8, 3,
      8)) (.next ([756000000000, 5040000000000], [972000000000, -2520000000000]) (some (8, 3, 8))
      (some (8, 4, 8)) fan8Owner0Part0))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded8_1 :
    ExclusionHint.check
      (model8.B 1 ++ [step8.q])
      9000000000000
      (model8.caps 1)
      (model8.ord
    1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded8_2 :
    ExclusionHint.check
      (model8.B 2 ++ [step8.q])
      9000000000000
      (model8.caps 2)
      (model8.ord
    2)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded8_4 :
    ExclusionHint.check
      (model8.B 4 ++ [step8.q])
      9000000000000
      (model8.caps 4)
      (model8.ord
    4)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded8_5 :
    ExclusionHint.check
      (model8.B 5 ++ [step8.q])
      9000000000000
      (model8.caps 5)
      (model8.ord
    5)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded8_6 :
    ExclusionHint.check
      (model8.B 6 ++ [step8.q])
      9000000000000
      (model8.caps 6)
      (model8.ord
    6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded8_7 :
    ExclusionHint.check
      (model8.B 7 ++ [step8.q])
      9000000000000
      (model8.caps 7)
      (model8.ord
    7)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded8_8 :
    ExclusionHint.check
      (model8.B 8 ++ [step8.q])
      9000000000000
      (model8.caps 8)
      (model8.ord
    8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Aown150000160000
end ConwaySoifer.Simplified.Certificates
