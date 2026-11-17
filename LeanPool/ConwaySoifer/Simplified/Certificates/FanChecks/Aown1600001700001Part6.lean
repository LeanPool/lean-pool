/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1600001700001
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown1600001700001Part6. -/

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

theorem checkedWitnessForExcluded13_6 :
    ExclusionHint.check
      (model13.B 6 ++ [step13.q])
      9000000000000
      (model13.caps 6)
      (model13.ord 6)
      12
      (.pair 2 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded13_7 :
    ExclusionHint.check
      (model13.B 7 ++ [step13.q])
      9000000000000
      (model13.caps 7)
      (model13.ord 7)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded13_8 :
    ExclusionHint.check
      (model13.B 8 ++ [step13.q])
      9000000000000
      (model13.caps 8)
      (model13.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded13_9 :
    ExclusionHint.check
      (model13.B 9 ++ [step13.q])
      9000000000000
      (model13.caps 9)
      (model13.ord 9)
      12
      (.witnessedFan (.next ([1920000000000, 0], [6390000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 1, 2)) (.next ([1920000000000], [7830000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([480000000000, -9000000000000], [7830000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1440000000000, 9000000000000]) (some (3, 1,
      2)) (some (3, 1, 3)) (.next ([-6390000000000, 9000000000000], [8310000000000, -9000000000000])
      (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-7830000000000], [9750000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-7830000000000], [8310000000000, -9000000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3)))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded14_1 :
    ExclusionHint.check
      (model14.B 1 ++ [step14.q])
      9000000000000
      (model14.caps 1)
      (model14.ord 1)
      12
      (.witnessedFan (.next ([6408000000000], [3147000000000]) (some (2, 3,
      1)) none (.next ([1440000000000, 9000000000000], [1440000000000, 9000000000000]) none none
      (.next ([2973000000000, 9000000000000], [3435000000000, -9000000000000]) (some (3, 3, 2))
      (some (3, 3, 2)) (.next ([1440000000000, 9000000000000], [3240000000000, -9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([93000000000, -9000000000000], [4875000000000, 0])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0], [6120000000000, 9000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-3147000000000], [9555000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([-1440000000000, -9000000000000], [2880000000000, 18000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-3435000000000, 9000000000000], [6408000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-3240000000000, 9000000000000], [4680000000000, 0]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-4875000000000, 0], [4968000000000, -9000000000000]) (some (3,
      1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1, 2)) (some (3, 1,
      2)))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded14_2 :
    ExclusionHint.check
      (model14.B 2 ++ [step14.q])
      9000000000000
      (model14.caps 2)
      (model14.ord 2)
      12
      (.witnessedFan (.next ([7605000000000, 0], [960000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7560000000000, -9000000000000],
      [1440000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3000000000000, 0],
      [1440000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([4875000000000],
      [2592000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3435000000000, -9000000000000],
      [4032000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([480000000000],
      [4125000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([408000000000], [4467000000000])
      (some (0, 4, 1)) (some (0, 4, 2)) (.next ([480000000000], [7125000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([138000000000], [4395000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([93000000000, -9000000000000], [4875000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([0, 0], [1440000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-960000000000, -9000000000000], [8565000000000, 9000000000000]) (some (0, 1, 2)) (some (0,
      1, 3)) (.next ([-1440000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some
      (0, 1, 3)) (.next ([-1440000000000, -9000000000000], [4440000000000, 9000000000000]) (some (0,
      1, 3)) (some (0, 1, 3)) (.next ([-2592000000000], [7467000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([-4032000000000, -9000000000000], [7467000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([-4125000000000], [4605000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([-4467000000000], [4875000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-7125000000000], [7605000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-4395000000000], [4533000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-4875000000000,
      0], [4968000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3)))))))))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded14_3 :
    ExclusionHint.check
      (model14.B 3 ++ [step14.q])
      9000000000000
      (model14.caps 3)
      (model14.ord 3)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded14_4 :
    ExclusionHint.check
      (model14.B 4 ++ [step14.q])
      9000000000000
      (model14.caps 4)
      (model14.ord 4)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Aown160000170000
end ConwaySoifer.Simplified.Certificates
