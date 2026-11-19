/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown2100002200005
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown2100002200005Part3. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Aown210000220000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Aown210000220000

theorem checkedWitnessForExcluded42_6 :
    ExclusionHint.check
      (model42.B 6 ++ [step42.q])
      9000000000000
      (model42.caps 6)
      (model42.ord 6)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded42_7 :
    ExclusionHint.check
      (model42.B 7 ++ [step42.q])
      9000000000000
      (model42.caps 7)
      (model42.ord 7)
      12
      (.pair 0 4)
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
      (.pair 0 4)
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
      (.pair 5 11)
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
      (.pair 0 4)
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
      (.pair 0 6)
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
      (.witnessedFan (.next ([3000000000000], [330000000000]) (some (2, 4, 2))
      (some (3, 4, 2)) (.next ([4275000000000], [750000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([2385000000000, -9000000000000], [750000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([5820000000000], [1890000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([2580000000000], [2025000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([5070000000000], [5025000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([2490000000000],
      [3000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1110000000000, -9000000000000],
      [2220000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0], [1890000000000,
      9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-330000000000], [3330000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-750000000000], [5025000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-750000000000], [3135000000000, -9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-1890000000000, -9000000000000], [7710000000000, 9000000000000])
      (some (0, 4, 2)) (some (4, 4, 2)) (.next ([-2025000000000], [4605000000000]) (some (4, 4, 2))
      (some (4, 4, 2)) (.next ([-5025000000000], [10095000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([-3000000000000], [5490000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-2220000000000, -9000000000000], [3330000000000]) (some (4, 1, 2)) (some (4, 2, 2))
      (.terminal (some (4, 2, 2)) (some (4, 2, 2)) (some (4, 2, 2)))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded43_5 :
    ExclusionHint.check
      (model43.B 5 ++ [step43.q])
      9000000000000
      (model43.caps 5)
      (model43.ord 5)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

end Aown210000220000
end ConwaySoifer.Simplified.Certificates
