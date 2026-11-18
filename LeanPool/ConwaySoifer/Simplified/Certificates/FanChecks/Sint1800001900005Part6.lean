/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint1800001900005
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint1800001900005Part6. -/

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

theorem checkedWitnessForExcluded45_4 :
    ExclusionHint.check
      (model45.B 4 ++ [step45.q])
      9000000000000
      (model45.caps 4)
      (model45.ord 4)
      12
      (.witnessedFan (.next ([2880000000000, -9000000000000], [0,
      9000000000000]) (some (4, 0, 5)) (some (4, 1, 5)) fan45Owner4Part0))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded45_5 :
    ExclusionHint.check
      (model45.B 5 ++ [step45.q])
      9000000000000
      (model45.caps 5)
      (model45.ord 5)
      12
      (.witnessedFan (.next ([4860000000000], [414000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([7875000000000], [810000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([3015000000000], [396000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([5334000000000, 0], [1620000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([6255000000000, -9000000000000], [2430000000000, 9000000000000]) (some (4, 1, 2)) (some (4,
      1, 2)) (.next ([3240000000000, -9000000000000], [2034000000000, 9000000000000]) (some (4, 1,
      2)) (some (4, 1, 4)) (.next ([4524000000000], [3351000000000]) (some (4, 1, 4)) (some (4, 1,
      4)) (.next ([60000000000], [4860000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [5334000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-414000000000], [5274000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-810000000000], [8685000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-396000000000], [3411000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-1620000000000, -9000000000000], [6954000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2430000000000, -9000000000000], [8685000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2034000000000, -9000000000000], [5274000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-3351000000000], [7875000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-4860000000000], [4920000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4)))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded45_6 :
    ExclusionHint.check
      (model45.B 6 ++ [step45.q])
      9000000000000
      (model45.caps 6)
      (model45.ord 6)
      12
      (.pair 4 7)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded45_7 :
    ExclusionHint.check
      (model45.B 7 ++ [step45.q])
      9000000000000
      (model45.caps 7)
      (model45.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded45_8 :
    ExclusionHint.check
      (model45.B 8 ++ [step45.q])
      9000000000000
      (model45.caps 8)
      (model45.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded45_9 :
    ExclusionHint.check
      (model45.B 9 ++ [step45.q])
      9000000000000
      (model45.caps 9)
      (model45.ord 9)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded46_1 :
    ExclusionHint.check
      (model46.B 1 ++ [step46.q])
      9000000000000
      (model46.caps 1)
      (model46.ord 1)
      12
      (.witnessedFan (.next ([5760000000000], [2250000000000]) none none
      (.next ([4140000000000, -9000000000000], [2250000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([2370000000000, 0], [1620000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([120000000000], [8010000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [1620000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2250000000000],
      [8010000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2250000000000, 0],
      [6390000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1620000000000,
      -9000000000000], [3990000000000, 9000000000000]) (some (3, 1, 0)) (some (3, 1, 3)) (.next
      ([-8010000000000], [8130000000000]) (some (3, 1, 3)) none (.terminal none none none)))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded46_2 :
    ExclusionHint.check
      (model46.B 2 ++ [step46.q])
      9000000000000
      (model46.caps 2)
      (model46.ord 2)
      12
      (.witnessedFan (.next ([7380000000000, -9000000000000], [1620000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2250000000000], [990000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4140000000000, -9000000000000], [2250000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([630000000000, -9000000000000], [2610000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [1620000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1620000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-990000000000],
      [3240000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2250000000000, 0],
      [6390000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2610000000000,
      -9000000000000], [3240000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2)))))))))))))
      0
      1
      100 = true := by
  certify_fan

end Sint180000190000
end ConwaySoifer.Simplified.Certificates
