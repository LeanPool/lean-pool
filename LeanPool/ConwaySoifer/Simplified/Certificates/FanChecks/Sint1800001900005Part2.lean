/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint1800001900005
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint1800001900005Part2. -/

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

theorem checkedWitnessForExcluded41_8 :
    ExclusionHint.check
      (model41.B 8 ++ [step41.q])
      9000000000000
      (model41.caps 8)
      (model41.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded41_9 :
    ExclusionHint.check
      (model41.B 9 ++ [step41.q])
      9000000000000
      (model41.caps 9)
      (model41.ord 9)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded42_0 :
    ExclusionHint.check
      (model42.B 0 ++ [step42.q])
      9000000000000
      (model42.caps 0)
      (model42.ord 0)
      12
      (.pair 0 9)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded42_1 :
    ExclusionHint.check
      (model42.B 1 ++ [step42.q])
      9000000000000
      (model42.caps 1)
      (model42.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded42_2 :
    ExclusionHint.check
      (model42.B 2 ++ [step42.q])
      9000000000000
      (model42.caps 2)
      (model42.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded42_3 :
    ExclusionHint.check
      (model42.B 3 ++ [step42.q])
      9000000000000
      (model42.caps 3)
      (model42.ord 3)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded42_4 :
    ExclusionHint.check
      (model42.B 4 ++ [step42.q])
      9000000000000
      (model42.caps 4)
      (model42.ord 4)
      12
      (.witnessedFan (.next ([5559000000000], [201000000000]) (some (3, 0, 2))
      (some (3, 4, 2)) (.next ([4140000000000, -9000000000000], [1245000000000, 9000000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([5184000000000, 0], [1620000000000, 9000000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([5184000000000], [3666000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([2094000000000], [3291000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([375000000000], [5385000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0, 0],
      [1620000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-201000000000],
      [5760000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1245000000000, -9000000000000],
      [5385000000000, 0]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-1620000000000,
      -9000000000000], [6804000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3666000000000], [8850000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3291000000000], [5385000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-5385000000000], [5760000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3)))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded42_6 :
    ExclusionHint.check
      (model42.B 6 ++ [step42.q])
      9000000000000
      (model42.caps 6)
      (model42.ord 6)
      12
      (.pair 3 7)
      0
      1
      100 = true := by
  decide +kernel

end Sint180000190000
end ConwaySoifer.Simplified.Certificates
