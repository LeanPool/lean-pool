/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown2100002200005
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown2100002200005Part5. -/

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

theorem checkedWitnessForExcluded44_5 :
    ExclusionHint.check
      (model44.B 5 ++ [step44.q])
      9000000000000
      (model44.caps 5)
      (model44.ord 5)
      12
      (.witnessedFan (.next ([3780000000000], [750000000000]) (some (5, 0, 3))
      (some (5, 1, 3)) (.next ([5415000000000, 0], [1890000000000, 9000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([1890000000000, -9000000000000], [750000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([2835000000000, -9000000000000], [1290000000000, 9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2490000000000, 9000000000000], [2235000000000,
      -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4665000000000], [4530000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1890000000000, 9000000000000], [1890000000000,
      9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1290000000000], [4725000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1140000000000, 9000000000000], [4530000000000, 0])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([600000000000], [4125000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([195000000000], [3180000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([0, 0], [1890000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 4)) (.next
      ([-750000000000], [4530000000000]) (some (5, 1, 4)) (some (5, 2, 4)) (.next ([-1890000000000,
      -9000000000000], [7305000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-750000000000, 0], [2640000000000, -9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-1290000000000, -9000000000000], [4125000000000]) (some (5, 2, 4)) (some (5, 3, 4)) (.next
      ([-2235000000000, 9000000000000], [4725000000000, 0]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
      ([-4530000000000], [9195000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-1890000000000,
      -9000000000000], [3780000000000, 18000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
      ([-4725000000000], [6015000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4530000000000,
      0], [5670000000000, 9000000000000]) (some (5, 3, 4)) (some (5, 3, 5)) (.next
      ([-4125000000000], [4725000000000]) (some (5, 3, 5)) (some (5, 3, 5)) (.next
      ([-3180000000000], [3375000000000]) (some (5, 3, 5)) (some (5, 3, 5)) (.terminal (some (5, 3,
      5)) (some (0, 3, 5)) (some (5, 3, 5)))))))))))))))))))))))))))
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
      (.pair 0 4)
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
      (.pair 0 4)
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
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded45_0 :
    ExclusionHint.check
      (model45.B 0 ++ [step45.q])
      9000000000000
      (model45.caps 0)
      (model45.ord 0)
      12
      (.pair 5 11)
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
      (.pair 0 4)
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
      (.pair 0 6)
      0
      1
      100 = true := by
  decide +kernel

end Aown210000220000
end ConwaySoifer.Simplified.Certificates
