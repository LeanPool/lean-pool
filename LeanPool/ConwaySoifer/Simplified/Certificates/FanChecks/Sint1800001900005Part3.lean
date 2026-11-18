/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint1800001900005
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint1800001900005Part3. -/

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

theorem checkedWitnessForExcluded42_7 :
    ExclusionHint.check
      (model42.B 7 ++ [step42.q])
      9000000000000
      (model42.caps 7)
      (model42.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded42_8 :
    ExclusionHint.check
      (model42.B 8 ++ [step42.q])
      9000000000000
      (model42.caps 8)
      (model42.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded42_9 :
    ExclusionHint.check
      (model42.B 9 ++ [step42.q])
      9000000000000
      (model42.caps 9)
      (model42.ord 9)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded43_0 :
    ExclusionHint.check
      (model43.B 0 ++ [step43.q])
      9000000000000
      (model43.caps 0)
      (model43.ord 0)
      12
      (.pair 7 9)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded43_1 :
    ExclusionHint.check
      (model43.B 1 ++ [step43.q])
      9000000000000
      (model43.caps 1)
      (model43.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded43_2 :
    ExclusionHint.check
      (model43.B 2 ++ [step43.q])
      9000000000000
      (model43.caps 2)
      (model43.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded43_3 :
    ExclusionHint.check
      (model43.B 3 ++ [step43.q])
      9000000000000
      (model43.caps 3)
      (model43.ord 3)
      12
      (.pair 2 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded43_5 :
    ExclusionHint.check
      (model43.B 5 ++ [step43.q])
      9000000000000
      (model43.caps 5)
      (model43.ord 5)
      12
      (.witnessedFan (.next ([4860000000000], [414000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([5334000000000, 0], [1620000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([3240000000000, -9000000000000], [2034000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2106000000000], [1980000000000]) (some (4, 1, 2))
      (some (4, 1, 3)) (.next ([2880000000000], [4500000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([834000000000], [2046000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([1260000000000, -9000000000000], [6120000000000, 9000000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([60000000000], [4860000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [5334000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-414000000000], [5274000000000])
      (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-1620000000000, -9000000000000], [6954000000000,
      9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2034000000000, -9000000000000],
      [5274000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1980000000000], [4086000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-4500000000000], [7380000000000]) (some (0, 2, 3))
      (some (0, 2, 4)) (.next ([-2046000000000], [2880000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-6120000000000, -9000000000000], [7380000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-4860000000000], [4920000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4)))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

end Sint180000190000
end ConwaySoifer.Simplified.Certificates
