/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1600001700000
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown1600001700000Part8. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Aown160000170000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Aown160000170000

theorem checkedWitnessForExcluded7_1 :
    ExclusionHint.check
      (model7.B 1 ++ [step7.q])
      9000000000000
      (model7.caps 1)
      (model7.ord
    1)
      12
      (.witnessedFan (.next ([435000000000, -9000000000000], [45000000000,
      9000000000000]) none none (.next ([1440000000000, 9000000000000], [1440000000000,
      9000000000000]) none none (.next ([1875000000000], [3105000000000]) none none (.next
      ([960000000000, 9000000000000], [1875000000000]) none none (.next ([1440000000000,
      9000000000000], [3060000000000, -9000000000000]) none none (.next ([0], [5940000000000,
      9000000000000]) none none (.next ([-45000000000, -9000000000000], [480000000000, 0]) none none
      (.next ([-1440000000000, -9000000000000], [2880000000000, 18000000000000]) none none (.next
      ([-3105000000000], [4980000000000]) none none (.next ([-1875000000000], [2835000000000,
      9000000000000]) none none (.next ([-3060000000000, 9000000000000], [4500000000000, 0]) none
      none (.terminal none none none)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded7_3 :
    ExclusionHint.check
      (model7.B 3 ++ [step7.q])
      9000000000000
      (model7.caps 3)
      (model7.ord
    3)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded7_4 :
    ExclusionHint.check
      (model7.B 4 ++ [step7.q])
      9000000000000
      (model7.caps 4)
      (model7.ord
    4)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded7_5 :
    ExclusionHint.check
      (model7.B 5 ++ [step7.q])
      9000000000000
      (model7.caps 5)
      (model7.ord
    5)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded7_6 :
    ExclusionHint.check
      (model7.B 6 ++ [step7.q])
      9000000000000
      (model7.caps 6)
      (model7.ord
    6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded7_7 :
    ExclusionHint.check
      (model7.B 7 ++ [step7.q])
      9000000000000
      (model7.caps 7)
      (model7.ord
    7)
      12
      (.split (0) (388) (757) (75700) (.witnessedFan (.next ([435000000000,
      -9000000000000], [45000000000, 9000000000000]) (some (2, 4, 1)) (some (3, 4, 2)) (.next
      ([1875000000000], [6165000000000, -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([1875000000000], [7605000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1440000000000,
      9000000000000], [6120000000000, -18000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([1440000000000, 9000000000000], [7560000000000, -9000000000000]) (some (3, 4, 2)) (some (3,
      4, 2)) (.next ([435000000000, -9000000000000], [7605000000000]) (some (3, 4, 2)) (some (3, 4,
      2)) (.next ([0, 0], [7560000000000, -9000000000000]) (some (3, 4, 2)) (some (4, 4, 2)) (.next
      ([-45000000000, -9000000000000], [480000000000, 0]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([-6165000000000, 9000000000000], [8040000000000, -9000000000000]) (some (4, 0, 2)) (some (4,
      0, 2)) (.next ([-7605000000000], [9480000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-6120000000000, 18000000000000], [7560000000000, -9000000000000]) (some (4, 0, 2)) (some (4,
      0, 2)) (.next ([-7560000000000, 9000000000000], [9000000000000, 0]) (some (4, 0, 2)) (some (4,
      1, 2)) (.next ([-7605000000000, 0], [8040000000000, -9000000000000]) (some (4, 1, 2)) (some
      (4, 1, 2)) (.terminal (some (4, 1, 2)) (some (4, 1, 2)) (some (4, 1, 2)))))))))))))))))
      (.witnessedFan (.next ([435000000000, -9000000000000], [45000000000, 9000000000000]) (some (2,
      4, 1)) (some (3, 4, 2)) (.next ([1875000000000], [6165000000000, -9000000000000]) (some (3, 4,
      2)) (some (3, 4, 2)) (.next ([1440000000000, 9000000000000], [6120000000000, -18000000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1875000000000], [7605000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([1440000000000, 9000000000000], [7560000000000, -9000000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([435000000000, -9000000000000], [7605000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0, 0], [7560000000000, -9000000000000]) (some (3,
      4, 2)) (some (4, 4, 2)) (.next ([-45000000000, -9000000000000], [480000000000, 0]) (some (4,
      4, 2)) (some (4, 4, 2)) (.next ([-6165000000000, 9000000000000], [8040000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-6120000000000, 18000000000000],
      [7560000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-7605000000000],
      [9480000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-7560000000000, 9000000000000],
      [9000000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-7605000000000, 0],
      [8040000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2))
      (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))))
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded7_8 :
    ExclusionHint.check
      (model7.B 8 ++ [step7.q])
      9000000000000
      (model7.caps 8)
      (model7.ord
    8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded7_9 :
    ExclusionHint.check
      (model7.B 9 ++ [step7.q])
      9000000000000
      (model7.caps 9)
      (model7.ord
    9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Aown160000170000
end ConwaySoifer.Simplified.Certificates
