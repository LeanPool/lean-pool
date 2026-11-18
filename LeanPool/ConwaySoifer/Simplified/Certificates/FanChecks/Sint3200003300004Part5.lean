/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint3200003300004
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint3200003300004Part5. -/

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

theorem checkedWitnessForExcluded36_4 :
    ExclusionHint.check
      (model36.B 4 ++ [step36.q])
      9000000000000
      (model36.caps 4)
      (model36.ord 4)
      12
      (.witnessedFan (.next ([1500000000000], [15000000000]) (some (6, 0, 4))
      (some (6, 7, 4)) (.next ([4320000000000], [180000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([5745000000000], [375000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([1365000000000], [180000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3165000000000],
      [705000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([4995000000000], [1185000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3495000000000], [1170000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([3225000000000], [1455000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([180000000000], [120000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([3495000000000], [2955000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1620000000000],
      [2070000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3495000000000], [4620000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3315000000000], [4500000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([1500000000000], [2370000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([1680000000000], [2820000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([2250000000000], [3870000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1710000000000],
      [2955000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([795000000000], [1455000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1560000000000], [3120000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([1500000000000], [4680000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([60000000000], [750000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([165000000000], [4320000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([45000000000],
      [4620000000000]) (some (6, 7, 4)) (some (6, 7, 4)) fan36Owner4Part0))))))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded36_6 :
    ExclusionHint.check
      (model36.B 6 ++ [step36.q])
      9000000000000
      (model36.caps 6)
      (model36.ord 6)
      12
      (.pair 2 7)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded36_7 :
    ExclusionHint.check
      (model36.B 7 ++ [step36.q])
      9000000000000
      (model36.caps 7)
      (model36.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded36_8 :
    ExclusionHint.check
      (model36.B 8 ++ [step36.q])
      9000000000000
      (model36.caps 8)
      (model36.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded36_9 :
    ExclusionHint.check
      (model36.B 9 ++ [step36.q])
      9000000000000
      (model36.caps 9)
      (model36.ord 9)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded37_0 :
    ExclusionHint.check
      (model37.B 0 ++ [step37.q])
      9000000000000
      (model37.caps 0)
      (model37.ord 0)
      12
      (.witnessedFan (.next ([5145000000000], [480000000000]) (some (5, 6, 3))
      (some (5, 6, 3)) (.next ([6000000000000], [600000000000]) (some (5, 6, 3)) (some (5, 6, 4))
      (.next ([2745000000000], [690000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([4560000000000], [1350000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([750000000000],
      [690000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([5145000000000], [4875000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) (.next ([690000000000], [690000000000]) (some (5, 6, 4))
      (some (5, 6, 4)) (.next ([4275000000000], [5160000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      (.next ([2400000000000], [4185000000000]) (some (5, 6, 4)) (some (6, 6, 4)) (.next
      ([285000000000], [585000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next ([1440000000000],
      [3435000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next ([1530000000000], [4470000000000])
      (some (6, 2, 4)) (some (6, 2, 4)) (.next ([1710000000000], [5565000000000]) (some (6, 2, 4))
      (some (6, 2, 4)) fan37Owner0Part0))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded37_1 :
    ExclusionHint.check
      (model37.B 1 ++ [step37.q])
      9000000000000
      (model37.caps 1)
      (model37.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded37_2 :
    ExclusionHint.check
      (model37.B 2 ++ [step37.q])
      9000000000000
      (model37.caps 2)
      (model37.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint320000330000
end ConwaySoifer.Simplified.Certificates
