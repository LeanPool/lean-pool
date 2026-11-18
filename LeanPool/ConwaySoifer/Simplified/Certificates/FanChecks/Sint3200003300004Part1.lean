/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint3200003300004
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint3200003300004Part1. -/

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

theorem checkedWitnessForExcluded32_9 :
    ExclusionHint.check
      (model32.B 9 ++ [step32.q])
      9000000000000
      (model32.caps 9)
      (model32.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded33_0 :
    ExclusionHint.check
      (model33.B 0 ++ [step33.q])
      9000000000000
      (model33.caps 0)
      (model33.ord 0)
      12
      (.pair 2 6)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded33_1 :
    ExclusionHint.check
      (model33.B 1 ++ [step33.q])
      9000000000000
      (model33.caps 1)
      (model33.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded33_2 :
    ExclusionHint.check
      (model33.B 2 ++ [step33.q])
      9000000000000
      (model33.caps 2)
      (model33.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded33_3 :
    ExclusionHint.check
      (model33.B 3 ++ [step33.q])
      9000000000000
      (model33.caps 3)
      (model33.ord 3)
      12
      (.pair 2 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded33_4 :
    ExclusionHint.check
      (model33.B 4 ++ [step33.q])
      9000000000000
      (model33.caps 4)
      (model33.ord 4)
      12
      (.witnessedFan (.next ([2229000000000], [21000000000]) (some (6, 0, 4))
      (some (6, 1, 4)) (.next ([1500000000000], [15000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([5745000000000], [375000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
      ([2415000000000], [519000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3165000000000],
      [705000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4995000000000], [1185000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3495000000000], [1170000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([3225000000000], [1455000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([4449000000000], [2250000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
      ([936000000000], [684000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2934000000000],
      [2250000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3495000000000], [2955000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3765000000000], [3870000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([1515000000000], [1980000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([996000000000], [1434000000000]) (some (6, 1, 4)) (some (7, 1, 4)) (.next
      ([3015000000000], [4680000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([2250000000000],
      [3870000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([1710000000000], [2955000000000])
      (some (7, 1, 4)) (some (7, 1, 4)) (.next ([795000000000], [1455000000000]) (some (7, 1, 4))
      (some (7, 1, 4)) (.next ([1515000000000], [4665000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([1500000000000], [4680000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([1245000000000], [5184000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([60000000000],
      [750000000000]) (some (7, 1, 4)) (some (7, 1, 4)) fan33Owner4Part0))))))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded33_5 :
    ExclusionHint.check
      (model33.B 5 ++ [step33.q])
      9000000000000
      (model33.caps 5)
      (model33.ord 5)
      12
      (.pair 1 6)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded33_6 :
    ExclusionHint.check
      (model33.B 6 ++ [step33.q])
      9000000000000
      (model33.caps 6)
      (model33.ord 6)
      12
      (.pair 0 7)
      0
      1
      100 = true := by
  decide +kernel

end Sint320000330000
end ConwaySoifer.Simplified.Certificates
