/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1500001600003
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown1500001600003Part7. -/

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

theorem checkedWitnessForExcluded31_0 :
    ExclusionHint.check
      (model31.B 0 ++ [step31.q])
      9000000000000
      (model31.caps 0)
      (model31.ord 0)
      12
      (.pair 6 11)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded31_1 :
    ExclusionHint.check
      (model31.B 1 ++ [step31.q])
      9000000000000
      (model31.caps 1)
      (model31.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded31_2 :
    ExclusionHint.check
      (model31.B 2 ++ [step31.q])
      9000000000000
      (model31.caps 2)
      (model31.ord 2)
      12
      (.pair 0 7)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded31_3 :
    ExclusionHint.check
      (model31.B 3 ++ [step31.q])
      9000000000000
      (model31.caps 3)
      (model31.ord 3)
      12
      (.witnessedFan (.next ([4200000000000], [675000000000]) (some (2, 4, 2))
      (some (3, 4, 2)) (.next ([6150000000000], [1350000000000, 9000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([2850000000000], [750000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([1500000000000, -9000000000000], [750000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([5400000000000], [3600000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([2850000000000, -9000000000000], [2025000000000, 9000000000000]) (some (3, 4, 2)) (some (3,
      4, 2)) (.next ([1275000000000], [4200000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([600000000000], [3525000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [1350000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-675000000000],
      [4875000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1350000000000, -9000000000000],
      [7500000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-750000000000],
      [3600000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-750000000000], [2250000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3600000000000], [9000000000000])
      (some (0, 1, 2)) (some (4, 1, 2)) (.next ([-2025000000000, -9000000000000], [4875000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-4200000000000], [5475000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([-3525000000000], [4125000000000]) (some (4, 1, 2)) (some (4, 2, 2))
      (.terminal (some (4, 2, 2)) (some (4, 2, 2)) (some (4, 2, 2)))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded31_5 :
    ExclusionHint.check
      (model31.B 5 ++ [step31.q])
      9000000000000
      (model31.caps 5)
      (model31.ord 5)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded31_6 :
    ExclusionHint.check
      (model31.B 6 ++ [step31.q])
      9000000000000
      (model31.caps 6)
      (model31.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded31_7 :
    ExclusionHint.check
      (model31.B 7 ++ [step31.q])
      9000000000000
      (model31.caps 7)
      (model31.ord 7)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded31_8 :
    ExclusionHint.check
      (model31.B 8 ++ [step31.q])
      9000000000000
      (model31.caps 8)
      (model31.ord 8)
      12
      (.witnessedFan (.next ([5100000000000], [1050000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([3600000000000], [6150000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1500000000000], [4650000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [4650000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1050000000000], [6150000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6150000000000], [9750000000000]) (some (0, 1, 2))
      (some (0, 3, 2)) (.next ([-4650000000000], [6150000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.terminal (some (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2)))))))))))
      0
      1
      100 = true := by
  certify_fan

end Aown150000160000
end ConwaySoifer.Simplified.Certificates
