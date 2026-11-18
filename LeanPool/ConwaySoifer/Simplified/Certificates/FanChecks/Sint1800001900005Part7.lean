/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint1800001900005
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint1800001900005Part7. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint180000190000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint180000190000

theorem checkedWitnessForExcluded46_3 :
    ExclusionHint.check
      (model46.B 3 ++ [step46.q])
      9000000000000
      (model46.caps 3)
      (model46.ord 3)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded46_4 :
    ExclusionHint.check
      (model46.B 4 ++ [step46.q])
      9000000000000
      (model46.caps 4)
      (model46.ord 4)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded46_5 :
    ExclusionHint.check
      (model46.B 5 ++ [step46.q])
      9000000000000
      (model46.caps 5)
      (model46.ord 5)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded46_6 :
    ExclusionHint.check
      (model46.B 6 ++ [step46.q])
      9000000000000
      (model46.caps 6)
      (model46.ord 6)
      12
      (.pair 0 7)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded46_7 :
    ExclusionHint.check
      (model46.B 7 ++ [step46.q])
      9000000000000
      (model46.caps 7)
      (model46.ord 7)
      12
      (.pair 2 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded46_8 :
    ExclusionHint.check
      (model46.B 8 ++ [step46.q])
      9000000000000
      (model46.caps 8)
      (model46.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded46_9 :
    ExclusionHint.check
      (model46.B 9 ++ [step46.q])
      9000000000000
      (model46.caps 9)
      (model46.ord 9)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded47_0 :
    ExclusionHint.check
      (model47.B 0 ++ [step47.q])
      9000000000000
      (model47.caps 0)
      (model47.ord 0)
      12
      (.witnessedFan (.next ([6855000000000], [165000000000]) (some (8, 2, 9))
      (some (8, 2, 9)) (.next ([4470000000000], [195000000000]) (some (8, 2, 9)) (some (8, 2, 9))
      (.next ([4305000000000], [195000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next
      ([6195000000000], [345000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([6105000000000],
      [540000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([4065000000000], [435000000000])
      (some (8, 2, 9)) (some (8, 2, 9)) (.next ([5595000000000], [870000000000]) (some (8, 2, 9))
      (some (8, 2, 9)) (.next ([4380000000000], [810000000000]) (some (8, 2, 9)) (some (8, 2, 9))
      (.next ([1290000000000], [270000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next
      ([1290000000000], [435000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([2610000000000],
      [885000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([2190000000000], [1125000000000])
      (some (8, 2, 9)) (some (8, 2, 9)) (.next ([3795000000000], [1995000000000]) (some (8, 2, 9))
      (some (8, 2, 9)) (.next ([3630000000000], [2160000000000]) (some (8, 2, 9)) (some (8, 2, 9))
      (.next ([1995000000000], [1230000000000]) (some (8, 2, 9)) (some (8, 2, 9))
      fan47Owner0Part2))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

end Sint180000190000
end ConwaySoifer.Simplified.Certificates
