/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2800002900002
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2800002900002Part0. -/

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

theorem checkedWitnessForExcluded16_0 :
    ExclusionHint.check
      (model16.B 0 ++ [step16.q])
      9000000000000
      (model16.caps 0)
      (model16.ord 0)
      12
      (.pair 8 12)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded16_1 :
    ExclusionHint.check
      (model16.B 1 ++ [step16.q])
      9000000000000
      (model16.caps 1)
      (model16.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded16_2 :
    ExclusionHint.check
      (model16.B 2 ++ [step16.q])
      9000000000000
      (model16.caps 2)
      (model16.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded16_3 :
    ExclusionHint.check
      (model16.B 3 ++ [step16.q])
      9000000000000
      (model16.caps 3)
      (model16.ord 3)
      12
      (.pair 2 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded16_5 :
    ExclusionHint.check
      (model16.B 5 ++ [step16.q])
      9000000000000
      (model16.caps 5)
      (model16.ord 5)
      12
      (.witnessedFan (.next ([4464000000000, 0], [2355000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([2520000000000, 9000000000000],
      [2520000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4464000000000],
      [4875000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1944000000000, -9000000000000],
      [7395000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [2520000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-2355000000000,
      9000000000000], [6819000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 2, 3)) (.next
      ([-2520000000000, -9000000000000], [5040000000000, 18000000000000]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-4875000000000], [9339000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-7395000000000, -9000000000000], [9339000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.terminal (some (0, 2, 3)) (some (0, 2, 3)) (some (0, 2, 3)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded16_6 :
    ExclusionHint.check
      (model16.B 6 ++ [step16.q])
      9000000000000
      (model16.caps 6)
      (model16.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded16_7 :
    ExclusionHint.check
      (model16.B 7 ++ [step16.q])
      9000000000000
      (model16.caps 7)
      (model16.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded16_8 :
    ExclusionHint.check
      (model16.B 8 ++ [step16.q])
      9000000000000
      (model16.caps 8)
      (model16.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint280000290000
end ConwaySoifer.Simplified.Certificates
