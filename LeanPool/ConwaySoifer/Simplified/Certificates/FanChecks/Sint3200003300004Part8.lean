/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint3200003300004
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint3200003300004Part8. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint320000330000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint320000330000

theorem checkedWitnessForExcluded39_2 :
    ExclusionHint.check
      (model39.B 2 ++ [step39.q])
      9000000000000
      (model39.caps 2)
      (model39.ord 2)
      12
      (.pair 1 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded39_3 :
    ExclusionHint.check
      (model39.B 3 ++ [step39.q])
      9000000000000
      (model39.caps 3)
      (model39.ord 3)
      12
      (.witnessedFan (.next ([4809000000000], [1146000000000]) (some (3, 0,
      5)) (some (4, 0, 5)) (.next ([5670000000000], [1410000000000]) (some (4, 0, 5)) (some (4, 0,
      5)) (.next ([861000000000], [264000000000]) (some (4, 0, 5)) (some (4, 5, 5))
      fan39Owner3Part0))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded39_4 :
    ExclusionHint.check
      (model39.B 4 ++ [step39.q])
      9000000000000
      (model39.caps 4)
      (model39.ord 4)
      12
      (.witnessedFan (.next ([4320000000000], [180000000000]) (some (7, 0, 8))
      (some (7, 1, 8)) (.next ([7080000000000], [375000000000]) (some (7, 1, 8)) (some (7, 1, 8))
      (.next ([5745000000000], [375000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next
      ([1365000000000], [180000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([2265000000000],
      [375000000000]) (some (7, 1, 8)) (some (7, 2, 8)) (.next ([3165000000000], [705000000000])
      (some (7, 2, 8)) (some (7, 2, 8)) (.next ([4995000000000], [1185000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([3495000000000], [1320000000000]) (some (7, 2, 8)) (some (7, 2, 8))
      (.next ([3225000000000], [1455000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
      ([2190000000000], [1050000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([1365000000000],
      [1080000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([4125000000000], [3330000000000])
      (some (7, 2, 8)) (some (7, 2, 8)) (.next ([3240000000000], [2625000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([3495000000000], [2955000000000]) (some (7, 2, 8)) (some (7, 2, 8))
      (.next ([3120000000000], [3960000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
      ([1620000000000], [2070000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([3315000000000],
      [4500000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([945000000000], [1305000000000])
      (some (7, 2, 8)) (some (7, 2, 8)) (.next ([1860000000000], [2955000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) fan39Owner4Part1))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded39_5 :
    ExclusionHint.check
      (model39.B 5 ++ [step39.q])
      9000000000000
      (model39.caps 5)
      (model39.ord 5)
      12
      (.witnessedFan (.next ([3390000000000], [360000000000]) (some (6, 0, 3))
      (some (6, 1, 3)) (.next ([3375000000000], [441000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([66000000000], [15000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([7455000000000], [1920000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([4380000000000],
      [1785000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4380000000000, 0], [2880000000000,
      9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([510000000000, -9000000000000],
      [360000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3285000000000, -9000000000000],
      [2880000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4020000000000],
      [3750000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3939000000000], [3816000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4575000000000, -9000000000000], [4800000000000,
      9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) fan39Owner5Part0))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded39_6 :
    ExclusionHint.check
      (model39.B 6 ++ [step39.q])
      9000000000000
      (model39.caps 6)
      (model39.ord 6)
      12
      (.pair 3 7)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded39_7 :
    ExclusionHint.check
      (model39.B 7 ++ [step39.q])
      9000000000000
      (model39.caps 7)
      (model39.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded39_8 :
    ExclusionHint.check
      (model39.B 8 ++ [step39.q])
      9000000000000
      (model39.caps 8)
      (model39.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded39_9 :
    ExclusionHint.check
      (model39.B 9 ++ [step39.q])
      9000000000000
      (model39.caps 9)
      (model39.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

end Sint320000330000
end ConwaySoifer.Simplified.Certificates
