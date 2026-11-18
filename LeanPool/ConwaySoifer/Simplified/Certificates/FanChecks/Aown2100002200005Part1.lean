/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown2100002200005
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown2100002200005Part1. -/

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

theorem checkedWitnessForExcluded40_9 :
    ExclusionHint.check
      (model40.B 9 ++ [step40.q])
      9000000000000
      (model40.caps 9)
      (model40.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded41_0 :
    ExclusionHint.check
      (model41.B 0 ++ [step41.q])
      9000000000000
      (model41.caps 0)
      (model41.ord 0)
      12
      (.pair 0 11)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded41_1 :
    ExclusionHint.check
      (model41.B 1 ++ [step41.q])
      9000000000000
      (model41.caps 1)
      (model41.ord 1)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded41_2 :
    ExclusionHint.check
      (model41.B 2 ++ [step41.q])
      9000000000000
      (model41.caps 2)
      (model41.ord 2)
      12
      (.pair 0 6)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded41_3 :
    ExclusionHint.check
      (model41.B 3 ++ [step41.q])
      9000000000000
      (model41.caps 3)
      (model41.ord 3)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded41_4 :
    ExclusionHint.check
      (model41.B 4 ++ [step41.q])
      9000000000000
      (model41.caps 4)
      (model41.ord 4)
      12
      (.witnessedFan (.next ([4275000000000], [225000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([3570000000000, 0], [945000000000, 9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([2400000000000], [930000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([3708000000000, -9000000000000], [1890000000000, 9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([945000000000], [735000000000, -9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([5373000000000], [4500000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([2385000000000, -9000000000000], [2115000000000, 9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([1890000000000, 9000000000000], [1890000000000, 9000000000000]) (some
      (5, 1, 2)) (some (5, 1, 2)) (.next ([2973000000000], [3570000000000]) (some (5, 1, 2)) (some
      (5, 1, 2)) (.next ([1665000000000, 9000000000000], [2610000000000, -9000000000000]) (some (5,
      1, 2)) (some (5, 1, 2)) (.next ([945000000000], [2625000000000]) (some (5, 1, 2)) (some (5, 1,
      2)) (.next ([0, 0], [1890000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([-225000000000], [4500000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([-945000000000,
      -9000000000000], [4515000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([-930000000000], [3330000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([-1890000000000,
      -9000000000000], [5598000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([-735000000000,
      9000000000000], [1680000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([-4500000000000], [9873000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-2115000000000,
      -9000000000000], [4500000000000, 0]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([-1890000000000, -9000000000000], [3780000000000, 18000000000000]) (some (5, 1, 3)) (some (5,
      2, 3)) (.next ([-3570000000000], [6543000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-2610000000000, 9000000000000], [4275000000000]) (some (5, 2, 3)) (some (5, 2, 5)) (.next
      ([-2625000000000], [3570000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.terminal (some (5, 2,
      5)) (some (0, 2, 5)) (some (5, 2, 5)))))))))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded41_5 :
    ExclusionHint.check
      (model41.B 5 ++ [step41.q])
      9000000000000
      (model41.caps 5)
      (model41.ord 5)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded41_6 :
    ExclusionHint.check
      (model41.B 6 ++ [step41.q])
      9000000000000
      (model41.caps 6)
      (model41.ord 6)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

end Aown210000220000
end ConwaySoifer.Simplified.Certificates
