/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2800002900002
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2800002900002Part4. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint280000290000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint280000290000

theorem checkedWitnessForExcluded19_6 :
    ExclusionHint.check
      (model19.B 6 ++ [step19.q])
      9000000000000
      (model19.caps 6)
      (model19.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded19_7 :
    ExclusionHint.check
      (model19.B 7 ++ [step19.q])
      9000000000000
      (model19.caps 7)
      (model19.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded19_8 :
    ExclusionHint.check
      (model19.B 8 ++ [step19.q])
      9000000000000
      (model19.caps 8)
      (model19.ord 8)
      12
      (.witnessedFan (.next ([6405000000000], [720000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([2880000000000], [2040000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([1485000000000], [3600000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([2880000000000], [7125000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [3600000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-720000000000], [7125000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2040000000000], [4920000000000]) (some (0, 1, 3))
      (some (0, 3, 3)) (.next ([-3600000000000], [5085000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-7125000000000], [10005000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded19_9 :
    ExclusionHint.check
      (model19.B 9 ++ [step19.q])
      9000000000000
      (model19.caps 9)
      (model19.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded20_0 :
    ExclusionHint.check
      (model20.B 0 ++ [step20.q])
      9000000000000
      (model20.caps 0)
      (model20.ord 0)
      12
      (.witnessedFan (.next ([6090000000000], [165000000000]) (some (9, 12,
      6)) (some (9, 12, 7)) (.next ([5625000000000], [255000000000]) (some (9, 12, 7)) (some (9, 12,
      7)) (.next ([1856400000000, 2130000000000], [86400000000, 2130000000000]) (some (9, 12, 7))
      (some (9, 12, 7)) fan20Owner0Part4))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded20_1 :
    ExclusionHint.check
      (model20.B 1 ++ [step20.q])
      9000000000000
      (model20.caps 1)
      (model20.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded20_2 :
    ExclusionHint.check
      (model20.B 2 ++ [step20.q])
      9000000000000
      (model20.caps 2)
      (model20.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded20_3 :
    ExclusionHint.check
      (model20.B 3 ++ [step20.q])
      9000000000000
      (model20.caps 3)
      (model20.ord 3)
      12
      (.pair 3 5)
      0
      1
      100 = true := by
  decide +kernel

end Sint280000290000
end ConwaySoifer.Simplified.Certificates
