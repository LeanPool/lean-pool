/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint1800001900005
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint1800001900005Part5. -/

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

theorem checkedWitnessForExcluded44_5 :
    ExclusionHint.check
      (model44.B 5 ++ [step44.q])
      9000000000000
      (model44.caps 5)
      (model44.ord 5)
      12
      (.witnessedFan (.next ([4860000000000], [414000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([8190000000000], [1185000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([3330000000000], [771000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([5334000000000, 0], [1620000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([6570000000000, -9000000000000], [2805000000000, 9000000000000]) (some (4, 1, 2)) (some (4,
      1, 2)) (.next ([3240000000000, -9000000000000], [2034000000000, 9000000000000]) (some (4, 1,
      2)) (some (4, 1, 4)) (.next ([4149000000000], [4041000000000]) (some (4, 1, 4)) (some (4, 1,
      4)) (.next ([60000000000], [4860000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [5334000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-414000000000], [5274000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1185000000000], [9375000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-771000000000], [4101000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-1620000000000, -9000000000000], [6954000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2805000000000, -9000000000000], [9375000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2034000000000, -9000000000000], [5274000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-4041000000000], [8190000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-4860000000000], [4920000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4)))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded44_6 :
    ExclusionHint.check
      (model44.B 6 ++ [step44.q])
      9000000000000
      (model44.caps 6)
      (model44.ord 6)
      12
      (.pair 4 7)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded44_7 :
    ExclusionHint.check
      (model44.B 7 ++ [step44.q])
      9000000000000
      (model44.caps 7)
      (model44.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded44_8 :
    ExclusionHint.check
      (model44.B 8 ++ [step44.q])
      9000000000000
      (model44.caps 8)
      (model44.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded44_9 :
    ExclusionHint.check
      (model44.B 9 ++ [step44.q])
      9000000000000
      (model44.caps 9)
      (model44.ord 9)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded45_1 :
    ExclusionHint.check
      (model45.B 1 ++ [step45.q])
      9000000000000
      (model45.caps 1)
      (model45.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded45_2 :
    ExclusionHint.check
      (model45.B 2 ++ [step45.q])
      9000000000000
      (model45.caps 2)
      (model45.ord 2)
      12
      (.pair 1 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded45_3 :
    ExclusionHint.check
      (model45.B 3 ++ [step45.q])
      9000000000000
      (model45.caps 3)
      (model45.ord 3)
      12
      (.witnessedFan (.next ([750000000000, -9000000000000], [0,
      9000000000000]) (some (3, 0, 5)) (some (4, 0, 5)) (.next ([5760000000000], [735000000000,
      9000000000000]) (some (4, 0, 5)) (some (4, 5, 5)) (.next ([6210000000000], [1620000000000,
      9000000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next ([5010000000000], [1485000000000])
      (some (4, 5, 5)) (some (4, 5, 3)) (.next ([6000000000000], [2430000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([5460000000000], [2370000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([1620000000000], [750000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([450000000000], [885000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([885000000000],
      [4875000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1125000000000], [8190000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [1620000000000, 9000000000000]) (some (4, 5,
      3)) (some (4, 5, 3)) (.next ([0, -9000000000000], [750000000000]) (some (0, 5, 3)) (some (0,
      5, 3)) (.next ([-735000000000, -9000000000000], [6495000000000, 9000000000000]) (some (0, 5,
      3)) (some (0, 5, 3)) (.next ([-1620000000000, -9000000000000], [7830000000000, 9000000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1485000000000], [6495000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-2430000000000], [8430000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-2370000000000], [7830000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-750000000000], [2370000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-885000000000],
      [1335000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4875000000000], [5760000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-8190000000000], [9315000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5,
      3)))))))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

end Sint180000190000
end ConwaySoifer.Simplified.Certificates
