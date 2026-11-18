/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1500001600003
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown1500001600003Part3. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Aown150000160000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Aown150000160000

theorem checkedWitnessForExcluded27_1 :
    ExclusionHint.check
      (model27.B 1 ++ [step27.q])
      9000000000000
      (model27.caps 1)
      (model27.ord 1)
      12
      (.witnessedFan (.next ([675000000000, -9000000000000], [75000000000,
      9000000000000]) none none (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) none none (.next ([2025000000000], [3450000000000]) none none (.next
      ([1350000000000, 9000000000000], [3375000000000, -9000000000000]) none none (.next
      ([600000000000, 9000000000000], [2025000000000]) none none (.next ([0], [6075000000000,
      9000000000000]) none none (.next ([-75000000000, -9000000000000], [750000000000, 0]) none none
      (.next ([-1350000000000, -9000000000000], [2700000000000, 18000000000000]) none none (.next
      ([-3450000000000], [5475000000000]) none none (.next ([-3375000000000, 9000000000000],
      [4725000000000, 0]) none none (.next ([-2025000000000], [2625000000000, 9000000000000]) none
      none (.terminal none none none)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded27_3 :
    ExclusionHint.check
      (model27.B 3 ++ [step27.q])
      9000000000000
      (model27.caps 3)
      (model27.ord 3)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded27_4 :
    ExclusionHint.check
      (model27.B 4 ++ [step27.q])
      9000000000000
      (model27.caps 4)
      (model27.ord 4)
      12
      (.pair 0 6)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded27_5 :
    ExclusionHint.check
      (model27.B 5 ++ [step27.q])
      9000000000000
      (model27.caps 5)
      (model27.ord 5)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded27_6 :
    ExclusionHint.check
      (model27.B 6 ++ [step27.q])
      9000000000000
      (model27.caps 6)
      (model27.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded27_7 :
    ExclusionHint.check
      (model27.B 7 ++ [step27.q])
      9000000000000
      (model27.caps 7)
      (model27.ord 7)
      12
      (.witnessedFan (.next ([675000000000, -9000000000000], [75000000000,
      9000000000000]) (some (2, 4, 1)) (some (3, 4, 2)) (.next ([675000000000, -9000000000000],
      [1350000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([2025000000000],
      [5700000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([2025000000000], [7725000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1350000000000, 9000000000000], [5625000000000,
      -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1350000000000, 9000000000000],
      [7650000000000, -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([675000000000,
      -9000000000000], [7725000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0, 0],
      [7650000000000, -9000000000000]) (some (3, 4, 2)) (some (4, 4, 2)) (.next ([-75000000000,
      -9000000000000], [750000000000, 0]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-1350000000000,
      -9000000000000], [2025000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-5700000000000],
      [7725000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-7725000000000], [9750000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-5625000000000, 9000000000000], [6975000000000, 0])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-7650000000000, 9000000000000], [9000000000000, 0])
      (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-7725000000000, 0], [8400000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2)) (some (4, 1,
      2)) (some (4, 1, 2)))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded27_8 :
    ExclusionHint.check
      (model27.B 8 ++ [step27.q])
      9000000000000
      (model27.caps 8)
      (model27.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded27_9 :
    ExclusionHint.check
      (model27.B 9 ++ [step27.q])
      9000000000000
      (model27.caps 9)
      (model27.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

end Aown150000160000
end ConwaySoifer.Simplified.Certificates
