/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown2100002200005
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown2100002200005Part8. -/

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

theorem checkedWitnessForExcluded47_1 :
    ExclusionHint.check
      (model47.B 1 ++ [step47.q])
      9000000000000
      (model47.caps 1)
      (model47.ord 1)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded47_2 :
    ExclusionHint.check
      (model47.B 2 ++ [step47.q])
      9000000000000
      (model47.caps 2)
      (model47.ord 2)
      12
      (.pair 0 6)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded47_3 :
    ExclusionHint.check
      (model47.B 3 ++ [step47.q])
      9000000000000
      (model47.caps 3)
      (model47.ord 3)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded47_4 :
    ExclusionHint.check
      (model47.B 4 ++ [step47.q])
      9000000000000
      (model47.caps 4)
      (model47.ord 4)
      12
      (.witnessedFan (.next ([5625000000000], [45000000000]) (some (3, 0, 5))
      (some (3, 5, 5)) (.next ([5670000000000], [777000000000]) (some (3, 5, 5)) (some (3, 5, 5))
      (.next ([3930000000000], [945000000000]) (some (3, 5, 2)) (some (3, 5, 2)) (.next
      ([4725000000000], [2835000000000]) (some (3, 5, 2)) (some (3, 5, 2)) (.next ([4725000000000],
      [5652000000000]) (some (3, 5, 2)) (some (3, 5, 2)) (.next ([2040000000000], [3630000000000])
      (some (3, 5, 2)) (some (3, 5, 2)) (.next ([1890000000000, 9000000000000], [3585000000000])
      (some (3, 5, 2)) (some (3, 5, 2)) (.next ([1845000000000, 9000000000000], [3780000000000,
      -9000000000000]) (some (3, 5, 2)) (some (3, 5, 2)) (.next ([750000000000], [2085000000000,
      -9000000000000]) (some (3, 5, 2)) (some (3, 5, 2)) (.next ([1890000000000, 9000000000000],
      [6402000000000]) (some (3, 5, 2)) (some (4, 5, 2)) (.next ([750000000000], [3975000000000])
      (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0], [3585000000000]) (some (4, 5, 2)) (some (4, 5,
      2)) (.next ([-45000000000], [5670000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next
      ([-777000000000], [6447000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([-945000000000],
      [4875000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([-2835000000000], [7560000000000])
      (some (0, 5, 2)) (some (0, 5, 3)) (.next ([-5652000000000], [10377000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-3630000000000], [5670000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-3585000000000], [5475000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-3780000000000, 9000000000000], [5625000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-2085000000000, 9000000000000], [2835000000000, -9000000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-6402000000000], [8292000000000, 9000000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-3975000000000], [4725000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded47_6 :
    ExclusionHint.check
      (model47.B 6 ++ [step47.q])
      9000000000000
      (model47.caps 6)
      (model47.ord 6)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded47_7 :
    ExclusionHint.check
      (model47.B 7 ++ [step47.q])
      9000000000000
      (model47.caps 7)
      (model47.ord 7)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded47_8 :
    ExclusionHint.check
      (model47.B 8 ++ [step47.q])
      9000000000000
      (model47.caps 8)
      (model47.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded47_9 :
    ExclusionHint.check
      (model47.B 9 ++ [step47.q])
      9000000000000
      (model47.caps 9)
      (model47.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

end Aown210000220000
end ConwaySoifer.Simplified.Certificates
