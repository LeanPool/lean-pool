/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1400001500006
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sext1400001500006Part3. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sext140000150000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sext140000150000

theorem checkedWitnessForExcluded50_7 :
    ExclusionHint.check
      (model50.B 7 ++ [step50.q])
      9000000000000
      (model50.caps 7)
      (model50.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded50_8 :
    ExclusionHint.check
      (model50.B 8 ++ [step50.q])
      9000000000000
      (model50.caps 8)
      (model50.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded50_9 :
    ExclusionHint.check
      (model50.B 9 ++ [step50.q])
      9000000000000
      (model50.caps 9)
      (model50.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded51_0 :
    ExclusionHint.check
      (model51.B 0 ++ [step51.q])
      9000000000000
      (model51.caps 0)
      (model51.ord 0)
      12
      (.pair 4 8)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded51_1 :
    ExclusionHint.check
      (model51.B 1 ++ [step51.q])
      9000000000000
      (model51.caps 1)
      (model51.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded51_2 :
    ExclusionHint.check
      (model51.B 2 ++ [step51.q])
      9000000000000
      (model51.caps 2)
      (model51.ord 2)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded51_3 :
    ExclusionHint.check
      (model51.B 3 ++ [step51.q])
      9000000000000
      (model51.caps 3)
      (model51.ord 3)
      12
      (.pair 7 10)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded51_5 :
    ExclusionHint.check
      (model51.B 5 ++ [step51.q])
      9000000000000
      (model51.caps 5)
      (model51.ord 5)
      12
      (.witnessedFan (.next ([4995000000000], [630000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([1830000000000], [375000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([630000000000], [1107000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([3465000000000], [6732000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2835000000000],
      [5625000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([375000000000], [1260000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1635000000000], [6357000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([1260000000000, 9000000000000], [6732000000000, 0]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([630000000000, 9000000000000], [5625000000000, 0]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1,
      2)) (.next ([-630000000000], [5625000000000]) (some (5, 1, 2)) (some (5, 2, 2)) (.next
      ([-375000000000], [2205000000000]) (some (5, 2, 2)) (some (5, 2, 2)) (.next ([-1107000000000],
      [1737000000000]) (some (5, 2, 2)) (some (5, 2, 2)) (.next ([-6732000000000], [10197000000000])
      (some (5, 2, 2)) (some (5, 2, 3)) (.next ([-5625000000000], [8460000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([-1260000000000], [1635000000000]) (some (5, 2, 3)) (some (5, 2, 5))
      (.next ([-6357000000000], [7992000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next
      ([-6732000000000, 0], [7992000000000, 9000000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next
      ([-5625000000000, 0], [6255000000000, 9000000000000]) (some (5, 2, 5)) (some (5, 2, 5))
      (.terminal (some (5, 2, 5)) (some (0, 2, 5)) (some (5, 2, 5)))))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

end Sext140000150000
end ConwaySoifer.Simplified.Certificates
