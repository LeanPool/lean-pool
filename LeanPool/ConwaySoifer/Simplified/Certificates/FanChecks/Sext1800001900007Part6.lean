/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1800001900007
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sext1800001900007Part6. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sext180000190000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sext180000190000

theorem checkedWitnessForExcluded61_3 :
    ExclusionHint.check
      (model61.B 3 ++ [step61.q])
      9000000000000
      (model61.caps 3)
      (model61.ord 3)
      12
      (.witnessedFan (.next ([4950000000000], [675000000000]) (some (4, 0, 6))
      (some (5, 0, 6)) (.next ([1995000000000], [330000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([3375000000000], [1005000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([1380000000000], [675000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next ([3000000000000],
      [1620000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next ([4620000000000], [3000000000000])
      (some (5, 0, 3)) (some (5, 0, 3)) (.next ([1710000000000], [1425000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([3510000000000], [3240000000000]) (some (5, 0, 3)) (some (5, 0, 3))
      (.next ([3375000000000, 9000000000000], [4005000000000, -9000000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([1995000000000, 9000000000000], [3330000000000, -9000000000000])
      (some (5, 0, 3)) (some (5, 0, 3)) (.next ([1380000000000], [3750000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([630000000000], [1755000000000]) (some (5, 0, 3)) (some (5, 0, 3))
      (.next ([1380000000000], [4245000000000]) (some (5, 0, 3)) (some (5, 0, 3))
      fan61Owner3Part0))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded61_5 :
    ExclusionHint.check
      (model61.B 5 ++ [step61.q])
      9000000000000
      (model61.caps 5)
      (model61.ord 5)
      12
      (.pair 1 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded61_6 :
    ExclusionHint.check
      (model61.B 6 ++ [step61.q])
      9000000000000
      (model61.caps 6)
      (model61.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded61_7 :
    ExclusionHint.check
      (model61.B 7 ++ [step61.q])
      9000000000000
      (model61.caps 7)
      (model61.ord 7)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded61_8 :
    ExclusionHint.check
      (model61.B 8 ++ [step61.q])
      9000000000000
      (model61.caps 8)
      (model61.ord 8)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded61_9 :
    ExclusionHint.check
      (model61.B 9 ++ [step61.q])
      9000000000000
      (model61.caps 9)
      (model61.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded62_1 :
    ExclusionHint.check
      (model62.B 1 ++ [step62.q])
      9000000000000
      (model62.caps 1)
      (model62.ord 1)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded62_2 :
    ExclusionHint.check
      (model62.B 2 ++ [step62.q])
      9000000000000
      (model62.caps 2)
      (model62.ord 2)
      12
      (.witnessedFan (.next ([4950000000000], [1245000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([1995000000000, 9000000000000], [3330000000000, -9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([2970000000000], [5280000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([2910000000000, 9000000000000], [6630000000000, -9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([915000000000], [3300000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([1620000000000, 9000000000000], [6570000000000, 0]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([1290000000000], [8250000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([375000000000], [4950000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0],
      [6570000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1245000000000], [6195000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-3330000000000, 9000000000000], [5325000000000, 0])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-5280000000000], [8250000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-6630000000000, 9000000000000], [9540000000000, 0]) (some (0, 4, 3))
      (some (4, 4, 3)) (.next ([-3300000000000], [4215000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-6570000000000, 0], [8190000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-8250000000000], [9540000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-4950000000000], [5325000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3)))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

end Sext180000190000
end ConwaySoifer.Simplified.Certificates
