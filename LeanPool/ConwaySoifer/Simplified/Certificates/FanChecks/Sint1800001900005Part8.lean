/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint1800001900005
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint1800001900005Part8. -/

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

theorem checkedWitnessForExcluded47_2 :
    ExclusionHint.check
      (model47.B 2 ++ [step47.q])
      9000000000000
      (model47.caps 2)
      (model47.ord 2)
      12
      (.witnessedFan (.next ([7380000000000, -9000000000000], [1620000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2535000000000, -9000000000000],
      [2340000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3255000000000,
      -9000000000000], [6465000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0,
      0], [1620000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-1620000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 3, 1)) (some (0, 3, 2)) (.next
      ([-2340000000000, -9000000000000], [4875000000000, 0]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-6465000000000, -9000000000000], [9720000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2)))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded47_3 :
    ExclusionHint.check
      (model47.B 3 ++ [step47.q])
      9000000000000
      (model47.caps 3)
      (model47.ord 3)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded47_4 :
    ExclusionHint.check
      (model47.B 4 ++ [step47.q])
      9000000000000
      (model47.caps 4)
      (model47.ord 4)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded47_5 :
    ExclusionHint.check
      (model47.B 5 ++ [step47.q])
      9000000000000
      (model47.caps 5)
      (model47.ord 5)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded47_6 :
    ExclusionHint.check
      (model47.B 6 ++ [step47.q])
      9000000000000
      (model47.caps 6)
      (model47.ord 6)
      12
      (.split (0) (265) (933) (93300) (.witnessedFan (.next ([4320000000000],
      [15000000000]) (some (7, 1, 4)) (some (7, 2, 5)) fan47Owner6Part1)) (.witnessedFan (.next
      ([4320000000000], [15000000000]) (some (7, 1, 4)) (some (7, 2, 5)) fan47Owner6Part3)))
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded47_7 :
    ExclusionHint.check
      (model47.B 7 ++ [step47.q])
      9000000000000
      (model47.caps 7)
      (model47.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded47_8 :
    ExclusionHint.check
      (model47.B 8 ++ [step47.q])
      9000000000000
      (model47.caps 8)
      (model47.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded47_9 :
    ExclusionHint.check
      (model47.B 9 ++ [step47.q])
      9000000000000
      (model47.caps 9)
      (model47.ord 9)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

end Sint180000190000
end ConwaySoifer.Simplified.Certificates
