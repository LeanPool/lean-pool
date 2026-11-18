/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1600001700001
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown1600001700001Part4. -/

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

theorem checkedWitnessForExcluded11_8 :
    ExclusionHint.check
      (model11.B 8 ++ [step11.q])
      9000000000000
      (model11.caps 8)
      (model11.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded11_9 :
    ExclusionHint.check
      (model11.B 9 ++ [step11.q])
      9000000000000
      (model11.caps 9)
      (model11.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded12_1 :
    ExclusionHint.check
      (model12.B 1 ++ [step12.q])
      9000000000000
      (model12.caps 1)
      (model12.ord 1)
      12
      (.pair 2 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded12_2 :
    ExclusionHint.check
      (model12.B 2 ++ [step12.q])
      9000000000000
      (model12.caps 2)
      (model12.ord 2)
      12
      (.witnessedFan (.next ([7560000000000, -9000000000000], [0,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7605000000000, 0], [960000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7560000000000, -9000000000000],
      [1440000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6120000000000,
      -9000000000000], [1440000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next
      ([3000000000000, 0], [1440000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next
      ([3000000000000], [4560000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([480000000000],
      [4125000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([480000000000], [7125000000000])
      (some (0, 4, 1)) (some (0, 4, 2)) (.next ([45000000000], [7080000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([0, 0], [1440000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([0, -9000000000000], [7560000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3)) (.next
      ([-960000000000, -9000000000000], [8565000000000, 9000000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([-1440000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some
      (0, 1, 3)) (.next ([-1440000000000, -9000000000000], [7560000000000]) (some (0, 1, 3)) (some
      (0, 1, 3)) (.next ([-1440000000000, -9000000000000], [4440000000000, 9000000000000]) (some (0,
      1, 3)) (some (4, 1, 3)) (.next ([-4560000000000], [7560000000000]) (some (4, 1, 3)) (some (4,
      1, 3)) (.next ([-4125000000000], [4605000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-7125000000000], [7605000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-7080000000000], [7125000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3)))))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded12_3 :
    ExclusionHint.check
      (model12.B 3 ++ [step12.q])
      9000000000000
      (model12.caps 3)
      (model12.ord 3)
      12
      (.witnessedFan (.next ([7560000000000], [1440000000000]) (some (1, 0,
      3)) (some (2, 0, 3)) (.next ([6180000000000], [1440000000000, 9000000000000]) (some (2, 0, 3))
      (some (2, 0, 3)) (.next ([6120000000000, -9000000000000], [2880000000000, 9000000000000])
      (some (2, 0, 3)) (some (2, 0, 3)) (.next ([4740000000000], [2820000000000]) (some (2, 0, 3))
      (some (2, 3, 3)) (.next ([0], [1440000000000, 9000000000000]) (some (2, 3, 1)) (some (2, 3,
      1)) (.next ([-1440000000000], [9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-1440000000000, -9000000000000], [7620000000000, 9000000000000]) (some (0, 3, 1)) (some (0,
      3, 1)) (.next ([-2880000000000, -9000000000000], [9000000000000]) (some (0, 3, 1)) (some (0,
      3, 1)) (.next ([-2820000000000], [7560000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal
      (some (0, 3, 1)) (some (0, 3, 1)) (some (0, 3, 1)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded12_4 :
    ExclusionHint.check
      (model12.B 4 ++ [step12.q])
      9000000000000
      (model12.caps 4)
      (model12.ord 4)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded12_5 :
    ExclusionHint.check
      (model12.B 5 ++ [step12.q])
      9000000000000
      (model12.caps 5)
      (model12.ord 5)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded12_6 :
    ExclusionHint.check
      (model12.B 6 ++ [step12.q])
      9000000000000
      (model12.caps 6)
      (model12.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Aown160000170000
end ConwaySoifer.Simplified.Certificates
