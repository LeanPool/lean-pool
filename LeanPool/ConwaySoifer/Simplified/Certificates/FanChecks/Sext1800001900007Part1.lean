/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1800001900007
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sext1800001900007Part1. -/

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

theorem checkedWitnessForExcluded56_9 :
    ExclusionHint.check
      (model56.B 9 ++ [step56.q])
      9000000000000
      (model56.caps 9)
      (model56.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded57_0 :
    ExclusionHint.check
      (model57.B 0 ++ [step57.q])
      9000000000000
      (model57.caps 0)
      (model57.ord 0)
      12
      (.pair 2 12)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded57_1 :
    ExclusionHint.check
      (model57.B 1 ++ [step57.q])
      9000000000000
      (model57.caps 1)
      (model57.ord 1)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded57_2 :
    ExclusionHint.check
      (model57.B 2 ++ [step57.q])
      9000000000000
      (model57.caps 2)
      (model57.ord 2)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded57_4 :
    ExclusionHint.check
      (model57.B 4 ++ [step57.q])
      9000000000000
      (model57.caps 4)
      (model57.ord 4)
      12
      (.witnessedFan (.next ([4875000000000], [1920000000000]) (some (5, 0,
      2)) (some (5, 1, 2)) (.next ([3255000000000], [1620000000000]) (some (5, 1, 2)) (some (5, 1,
      2)) (.next ([1620000000000], [1875000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([3000000000000], [3750000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1380000000000],
      [1875000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3000000000000], [5175000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1620000000000, 9000000000000], [5130000000000,
      -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1620000000000, 9000000000000],
      [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1575000000000], [5175000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([0, 9000000000000], [3255000000000, -9000000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([0], [5175000000000]) (some (5, 1, 2)) (some (5, 1,
      2)) (.next ([-1920000000000], [6795000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-1620000000000], [4875000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-1875000000000], [3495000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-3750000000000], [6750000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next
      ([-1875000000000], [3255000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-5175000000000], [8175000000000]) (some (0, 1, 3)) (some (0, 1, 5)) (.next ([-5130000000000,
      9000000000000], [6750000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5175000000000],
      [6795000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5175000000000],
      [6750000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3255000000000, 9000000000000],
      [3255000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2,
      5)) (some (0, 2, 5)))))))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded57_5 :
    ExclusionHint.check
      (model57.B 5 ++ [step57.q])
      9000000000000
      (model57.caps 5)
      (model57.ord 5)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded57_6 :
    ExclusionHint.check
      (model57.B 6 ++ [step57.q])
      9000000000000
      (model57.caps 6)
      (model57.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded57_7 :
    ExclusionHint.check
      (model57.B 7 ++ [step57.q])
      9000000000000
      (model57.caps 7)
      (model57.ord 7)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

end Sext180000190000
end ConwaySoifer.Simplified.Certificates
