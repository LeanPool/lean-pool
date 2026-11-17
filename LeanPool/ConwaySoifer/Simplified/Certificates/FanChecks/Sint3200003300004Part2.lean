/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint3200003300004
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint3200003300004Part2. -/

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

theorem checkedWitnessForExcluded33_7 :
    ExclusionHint.check
      (model33.B 7 ++ [step33.q])
      9000000000000
      (model33.caps 7)
      (model33.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded33_9 :
    ExclusionHint.check
      (model33.B 9 ++ [step33.q])
      9000000000000
      (model33.caps 9)
      (model33.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded34_0 :
    ExclusionHint.check
      (model34.B 0 ++ [step34.q])
      9000000000000
      (model34.caps 0)
      (model34.ord 0)
      12
      (.witnessedFan (.next ([5145000000000], [480000000000]) (some (6, 6, 3))
      (some (6, 6, 3)) (.next ([6000000000000], [600000000000]) (some (6, 6, 3)) (some (6, 6, 4))
      (.next ([5874000000000], [1251000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
      ([6624000000000], [1941000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4560000000000],
      [1350000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4494000000000], [1941000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([5934000000000], [3381000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([750000000000], [690000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([690000000000], [690000000000]) (some (6, 1, 4)) (some (6, 2, 4)) (.next
      ([2400000000000], [4185000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([285000000000],
      [585000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([1530000000000], [4470000000000])
      (some (6, 2, 4)) (some (6, 2, 4)) (.next ([1710000000000], [5565000000000]) (some (6, 2, 4))
      (some (6, 2, 4)) fan34Owner0Part0))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded34_1 :
    ExclusionHint.check
      (model34.B 1 ++ [step34.q])
      9000000000000
      (model34.caps 1)
      (model34.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded34_2 :
    ExclusionHint.check
      (model34.B 2 ++ [step34.q])
      9000000000000
      (model34.caps 2)
      (model34.ord 2)
      12
      (.pair 1 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded34_4 :
    ExclusionHint.check
      (model34.B 4 ++ [step34.q])
      9000000000000
      (model34.caps 4)
      (model34.ord 4)
      12
      (.witnessedFan (.next ([2229000000000], [21000000000]) (some (7, 0, 4))
      (some (7, 1, 4)) (.next ([1500000000000], [15000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([5745000000000], [375000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      fan34Owner4Part1))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded34_5 :
    ExclusionHint.check
      (model34.B 5 ++ [step34.q])
      9000000000000
      (model34.caps 5)
      (model34.ord 5)
      12
      (.pair 0 6)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded34_6 :
    ExclusionHint.check
      (model34.B 6 ++ [step34.q])
      9000000000000
      (model34.caps 6)
      (model34.ord 6)
      12
      (.pair 0 7)
      0
      1
      100 = true := by
  decide +kernel

end Sint320000330000
end ConwaySoifer.Simplified.Certificates
