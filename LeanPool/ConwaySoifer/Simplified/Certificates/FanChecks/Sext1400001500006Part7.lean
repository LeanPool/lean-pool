/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1400001500006
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sext1400001500006Part7. -/

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

theorem checkedWitnessForExcluded54_2 :
    ExclusionHint.check
      (model54.B 2 ++ [step54.q])
      9000000000000
      (model54.caps 2)
      (model54.ord 2)
      12
      (.pair 2 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded54_3 :
    ExclusionHint.check
      (model54.B 3 ++ [step54.q])
      9000000000000
      (model54.caps 3)
      (model54.ord 3)
      12
      (.witnessedFan (.next ([3360000000000], [15000000000]) (some (8, 0, 6))
      (some (10, 0, 6)) (.next ([2790000000000], [45000000000]) (some (10, 0, 6)) (some (10, 0, 6))
      (.next ([3540000000000], [60000000000]) (some (10, 0, 6)) (some (10, 0, 6)) (.next
      ([2970000000000], [90000000000]) (some (10, 0, 6)) (some (10, 0, 6)) (.next ([1080000000000],
      [45000000000]) (some (10, 0, 6)) (some (10, 0, 6)) (.next ([3690000000000], [180000000000])
      (some (10, 0, 6)) (some (10, 0, 6)) (.next ([5760000000000, 9000000000000], [420000000000,
      -9000000000000]) (some (10, 0, 6)) (some (10, 0, 6)) (.next ([6120000000000], [630000000000])
      (some (10, 0, 6)) (some (10, 0, 6)) (.next ([1410000000000], [210000000000]) (some (10, 0, 6))
      (some (10, 0, 6)) (.next ([6000000000000], [900000000000]) (some (10, 0, 6)) (some (10, 0, 6))
      (.next ([5220000000000, 9000000000000], [990000000000, -9000000000000]) (some (10, 0, 6))
      (some (10, 0, 6)) (.next ([180000000000], [45000000000]) (some (10, 0, 6)) (some (10, 0, 6))
      (.next ([4470000000000], [1530000000000]) (some (10, 0, 6)) (some (10, 0, 6)) (.next
      ([4500000000000], [1680000000000]) (some (10, 0, 6)) (some (10, 0, 6)) (.next ([330000000000],
      [165000000000]) (some (10, 0, 6)) (some (10, 0, 6)) fan54Owner3Part2))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded54_4 :
    ExclusionHint.check
      (model54.B 4 ++ [step54.q])
      9000000000000
      (model54.caps 4)
      (model54.ord 4)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded54_5 :
    ExclusionHint.check
      (model54.B 5 ++ [step54.q])
      9000000000000
      (model54.caps 5)
      (model54.ord 5)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded54_6 :
    ExclusionHint.check
      (model54.B 6 ++ [step54.q])
      9000000000000
      (model54.caps 6)
      (model54.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded54_7 :
    ExclusionHint.check
      (model54.B 7 ++ [step54.q])
      9000000000000
      (model54.caps 7)
      (model54.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded54_9 :
    ExclusionHint.check
      (model54.B 9 ++ [step54.q])
      9000000000000
      (model54.caps 9)
      (model54.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded55_0 :
    ExclusionHint.check
      (model55.B 0 ++ [step55.q])
      9000000000000
      (model55.caps 0)
      (model55.ord 0)
      12
      (.pair 2 8)
      0
      1
      100 = true := by
  decide +kernel

end Sext140000150000
end ConwaySoifer.Simplified.Certificates
