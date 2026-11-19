/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1800001900007
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sext1800001900007Part4. -/

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

theorem checkedWitnessForExcluded59_6 :
    ExclusionHint.check
      (model59.B 6 ++ [step59.q])
      9000000000000
      (model59.caps 6)
      (model59.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded59_7 :
    ExclusionHint.check
      (model59.B 7 ++ [step59.q])
      9000000000000
      (model59.caps 7)
      (model59.ord 7)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded59_8 :
    ExclusionHint.check
      (model59.B 8 ++ [step59.q])
      9000000000000
      (model59.caps 8)
      (model59.ord 8)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded59_9 :
    ExclusionHint.check
      (model59.B 9 ++ [step59.q])
      9000000000000
      (model59.caps 9)
      (model59.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded60_0 :
    ExclusionHint.check
      (model60.B 0 ++ [step60.q])
      9000000000000
      (model60.caps 0)
      (model60.ord 0)
      12
      (.pair 2 12)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded60_1 :
    ExclusionHint.check
      (model60.B 1 ++ [step60.q])
      9000000000000
      (model60.caps 1)
      (model60.ord 1)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded60_2 :
    ExclusionHint.check
      (model60.B 2 ++ [step60.q])
      9000000000000
      (model60.caps 2)
      (model60.ord 2)
      12
      (.witnessedFan (.next ([6000000000000, 9000000000000], [1380000000000,
      -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4950000000000], [1245000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4380000000000], [3000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([1950000000000], [2055000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([1995000000000, 9000000000000], [3330000000000, -9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([810000000000], [2190000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([1620000000000, 9000000000000], [6570000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([375000000000], [4950000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [6570000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1380000000000, 9000000000000],
      [7380000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-1245000000000],
      [6195000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3000000000000], [7380000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2055000000000], [4005000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-3330000000000, 9000000000000], [5325000000000, 0]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-2190000000000], [3000000000000]) (some (0, 1, 3)) (some (0, 2, 3))
      (.next ([-6570000000000, 0], [8190000000000, 9000000000000]) (some (0, 2, 3)) (some (4, 2, 3))
      (.next ([-4950000000000], [5325000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some
      (4, 2, 3)) (some (4, 2, 0)) (some (4, 2, 3)))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded60_4 :
    ExclusionHint.check
      (model60.B 4 ++ [step60.q])
      9000000000000
      (model60.caps 4)
      (model60.ord 4)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

end Sext180000190000
end ConwaySoifer.Simplified.Certificates
