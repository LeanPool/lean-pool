/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint1500001600001
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint1500001600001Part8. -/

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

theorem checkedWitnessForExcluded15_2 :
    ExclusionHint.check
      (model15.B 2 ++ [step15.q])
      9000000000000
      (model15.caps 2)
      (model15.ord 2)
      12
      (.witnessedFan (.next ([3600000000000, -9000000000000], [225000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([7650000000000, -9000000000000],
      [1350000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3825000000000,
      -9000000000000], [4950000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([1125000000000], [3825000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-225000000000,
      -9000000000000], [3825000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-1350000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (3, 1, 2)) (.next
      ([-4950000000000, 0], [8775000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-3825000000000], [4950000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some
      (3, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded15_3 :
    ExclusionHint.check
      (model15.B 3 ++ [step15.q])
      9000000000000
      (model15.caps 3)
      (model15.ord 3)
      12
      (.split (0) (1) (14) (1400) (.witnessedFan (.next ([6600000000000],
      [1350000000000, 9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([6150000000000],
      [1575000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next ([1125000000000], [450000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([2550000000000], [1275000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([225000000000, -9000000000000], [225000000000, 9000000000000]) (some
      (3, 0, 2)) (some (3, 0, 2)) (.next ([3825000000000], [4050000000000]) (some (3, 0, 2)) (some
      (3, 1, 2)) (.next ([2475000000000, -9000000000000], [5400000000000, 9000000000000]) (some (3,
      1, 2)) (some (3, 1, 2)) (.next ([2250000000000], [5175000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([0], [1350000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 4, 2)) (.next
      ([-1350000000000, -9000000000000], [7950000000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-1575000000000], [7725000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-450000000000], [1575000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1275000000000],
      [3825000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-225000000000, -9000000000000],
      [450000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4050000000000], [7875000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5400000000000, -9000000000000], [7875000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5175000000000], [7425000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4,
      2))))))))))))))))))))) (.split (33) (455) (462) (46200) (.witnessedFan (.next
      ([6600000000000], [1350000000000, 9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next
      ([6150000000000], [1575000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next ([1125000000000],
      [450000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next ([2550000000000], [1275000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([3825000000000], [4050000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([225000000000, -9000000000000], [225000000000, 9000000000000]) (some
      (3, 0, 2)) (some (3, 0, 2)) (.next ([2475000000000, -9000000000000], [5400000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([2250000000000], [5175000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0], [1350000000000, 9000000000000]) (some (3, 1,
      2)) (some (3, 4, 2)) (.next ([-1350000000000, -9000000000000], [7950000000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1575000000000], [7725000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-450000000000], [1575000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-1275000000000], [3825000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4050000000000], [7875000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-225000000000,
      -9000000000000], [450000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5400000000000,
      -9000000000000], [7875000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5175000000000],
      [7425000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 4,
      2)) (some (0, 4, 2))))))))))))))))))))) (.witnessedFan (.next ([6600000000000],
      [1350000000000, 9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([6150000000000],
      [1575000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next ([1125000000000], [450000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([2550000000000], [1275000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([3825000000000], [4050000000000]) (some (3, 0, 2)) (some (3, 0, 2))
      (.next ([2250000000000], [5175000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([2475000000000, -9000000000000], [5400000000000, 9000000000000]) (some (3, 0, 2)) (some (3,
      0, 2)) (.next ([225000000000, -9000000000000], [225000000000, 9000000000000]) (some (3, 0, 2))
      (some (3, 4, 2)) (.next ([0], [1350000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4,
      2)) (.next ([-1350000000000, -9000000000000], [7950000000000, 9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-1575000000000], [7725000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-450000000000], [1575000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1275000000000], [3825000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4050000000000], [7875000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-5175000000000], [7425000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5400000000000,
      -9000000000000], [7875000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-225000000000,
      -9000000000000], [450000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4, 2))
      (some (0, 4, 2)) (some (0, 4, 2)))))))))))))))))))))))
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded15_4 :
    ExclusionHint.check
      (model15.B 4 ++ [step15.q])
      9000000000000
      (model15.caps 4)
      (model15.ord 4)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded15_5 :
    ExclusionHint.check
      (model15.B 5 ++ [step15.q])
      9000000000000
      (model15.caps 5)
      (model15.ord 5)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded15_6 :
    ExclusionHint.check
      (model15.B 6 ++ [step15.q])
      9000000000000
      (model15.caps 6)
      (model15.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded15_7 :
    ExclusionHint.check
      (model15.B 7 ++ [step15.q])
      9000000000000
      (model15.caps 7)
      (model15.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded15_8 :
    ExclusionHint.check
      (model15.B 8 ++ [step15.q])
      9000000000000
      (model15.caps 8)
      (model15.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded15_9 :
    ExclusionHint.check
      (model15.B 9 ++ [step15.q])
      9000000000000
      (model15.caps 9)
      (model15.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint150000160000
end ConwaySoifer.Simplified.Certificates
