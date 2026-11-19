/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2300002400003
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2300002400003Part8. -/

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

theorem checkedWitnessForExcluded31_2 :
    ExclusionHint.check
      (model31.B 2 ++ [step31.q])
      9000000000000
      (model31.caps 2)
      (model31.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded31_3 :
    ExclusionHint.check
      (model31.B 3 ++ [step31.q])
      9000000000000
      (model31.caps 3)
      (model31.ord 3)
      12
      (.pair 4 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded31_4 :
    ExclusionHint.check
      (model31.B 4 ++ [step31.q])
      9000000000000
      (model31.caps 4)
      (model31.ord 4)
      12
      (.pair 0 6)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded31_5 :
    ExclusionHint.check
      (model31.B 5 ++ [step31.q])
      9000000000000
      (model31.caps 5)
      (model31.ord 5)
      12
      (.witnessedFan (.next ([6495000000000, -9000000000000], [1380000000000,
      9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) fan31Owner5Part0))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded31_6 :
    ExclusionHint.check
      (model31.B 6 ++ [step31.q])
      9000000000000
      (model31.caps 6)
      (model31.ord 6)
      12
      (.witnessedFan (.next ([4425000000000], [60000000000]) (some (5, 1, 3))
      (some (5, 1, 4)) (.next ([7875000000000], [435000000000]) (some (5, 1, 4)) (some (5, 1, 4))
      (.next ([3450000000000], [375000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
      ([2280000000000], [450000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([3375000000000],
      [1350000000000, 9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([5805000000000,
      -9000000000000], [2505000000000, 9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
      ([720000000000, 0], [585000000000, -9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
      ([1695000000000, 9000000000000], [1755000000000, -9000000000000]) (some (5, 1, 4)) (some (5,
      2, 4)) (.next ([1380000000000, -9000000000000], [2445000000000, 9000000000000]) (some (5, 2,
      4)) (some (5, 2, 4)) (.next ([2220000000000], [4935000000000]) (some (5, 2, 4)) (some (5, 2,
      4)) (.next ([720000000000], [2655000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([0, 0],
      [2070000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-60000000000],
      [4485000000000]) (some (5, 2, 4)) (some (5, 3, 4)) (.next ([-435000000000], [8310000000000])
      (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-375000000000], [3825000000000]) (some (5, 3, 4))
      (some (5, 3, 4)) (.next ([-450000000000], [2730000000000]) (some (5, 3, 4)) (some (5, 3, 4))
      (.next ([-1350000000000, -9000000000000], [4725000000000, 9000000000000]) (some (5, 3, 4))
      (some (5, 3, 4)) (.next ([-2505000000000, -9000000000000], [8310000000000]) (some (5, 3, 4))
      (some (5, 3, 4)) (.next ([-585000000000, 9000000000000], [1305000000000, -9000000000000])
      (some (5, 3, 4)) (some (5, 3, 5)) (.next ([-1755000000000, 9000000000000], [3450000000000])
      (some (5, 3, 5)) (some (5, 3, 5)) (.next ([-2445000000000, -9000000000000], [3825000000000])
      (some (5, 3, 5)) (some (5, 3, 5)) (.next ([-4935000000000], [7155000000000]) (some (5, 3, 5))
      (some (5, 3, 5)) (.next ([-2655000000000], [3375000000000]) (some (1, 3, 5)) (some (1, 3, 5))
      (.terminal (some (1, 3, 5)) (some (1, 3, 5)) (some (1, 3, 5)))))))))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded31_7 :
    ExclusionHint.check
      (model31.B 7 ++ [step31.q])
      9000000000000
      (model31.caps 7)
      (model31.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded31_8 :
    ExclusionHint.check
      (model31.B 8 ++ [step31.q])
      9000000000000
      (model31.caps 8)
      (model31.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded31_9 :
    ExclusionHint.check
      (model31.B 9 ++ [step31.q])
      9000000000000
      (model31.caps 9)
      (model31.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint230000240000
end ConwaySoifer.Simplified.Certificates
