/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2300002400003
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2300002400003Part7. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint230000240000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint230000240000

theorem checkedWitnessForExcluded30_2 :
    ExclusionHint.check
      (model30.B 2 ++ [step30.q])
      9000000000000
      (model30.caps 2)
      (model30.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded30_3 :
    ExclusionHint.check
      (model30.B 3 ++ [step30.q])
      9000000000000
      (model30.caps 3)
      (model30.ord 3)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded30_4 :
    ExclusionHint.check
      (model30.B 4 ++ [step30.q])
      9000000000000
      (model30.caps 4)
      (model30.ord 4)
      12
      (.witnessedFan (.next ([285000000000], [15000000000]) (some (5, 0, 6))
      (some (5, 1, 6)) (.next ([4500000000000], [360000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([4014000000000], [486000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([3624000000000], [516000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3339000000000],
      [501000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4140000000000], [750000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3840000000000], [1035000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([6759000000000], [2241000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([4374000000000, 0], [2070000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([3420000000000], [1740000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([3135000000000], [1725000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2745000000000],
      [1755000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2430000000000, -9000000000000],
      [2430000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2070000000000,
      -9000000000000], [2820000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([1770000000000, -9000000000000], [3105000000000, 9000000000000]) (some (5, 1, 6)) (some (5,
      1, 6)) fan30Owner4Part0))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded30_6 :
    ExclusionHint.check
      (model30.B 6 ++ [step30.q])
      9000000000000
      (model30.caps 6)
      (model30.ord 6)
      12
      (.split (0) (1) (2) (200) (.witnessedFan (.next ([6615000000000, 0],
      [315000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 4)) fan30Owner6Part0))
      (.witnessedFan (.next ([6615000000000, 0], [315000000000, -9000000000000]) (some (5, 1, 3))
      (some (5, 1, 4)) (.next ([3450000000000], [375000000000]) (some (5, 1, 4)) (some (5, 1, 4))
      (.next ([2280000000000], [450000000000]) (some (5, 1, 4)) (some (5, 1, 4))
      fan30Owner6Part1)))))
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded30_7 :
    ExclusionHint.check
      (model30.B 7 ++ [step30.q])
      9000000000000
      (model30.caps 7)
      (model30.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded30_8 :
    ExclusionHint.check
      (model30.B 8 ++ [step30.q])
      9000000000000
      (model30.caps 8)
      (model30.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded30_9 :
    ExclusionHint.check
      (model30.B 9 ++ [step30.q])
      9000000000000
      (model30.caps 9)
      (model30.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded31_1 :
    ExclusionHint.check
      (model31.B 1 ++ [step31.q])
      9000000000000
      (model31.caps 1)
      (model31.ord 1)
      12
      (.witnessedFan (.next ([8310000000000], [1125000000000]) (some (0, 3,
      1)) (some (0, 3, 2)) (.next ([6240000000000, -9000000000000], [3195000000000, 9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2070000000000, 9000000000000], [2070000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([945000000000, 9000000000000],
      [7365000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next ([0, 0],
      [2070000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1125000000000],
      [9435000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-3195000000000, -9000000000000],
      [9435000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2070000000000,
      -9000000000000], [4140000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-7365000000000, 9000000000000], [8310000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0)))))))))))))
      0
      1
      100 = true := by
  certify_fan

end Sint230000240000
end ConwaySoifer.Simplified.Certificates
