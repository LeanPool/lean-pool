/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint1500001600001
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint1500001600001Part5. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint150000160000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint150000160000

theorem checkedWitnessForExcluded12_4 :
    ExclusionHint.check
      (model12.B 4 ++ [step12.q])
      9000000000000
      (model12.caps 4)
      (model12.ord 4)
      12
      (.witnessedFan (.next ([3375000000000, 0], [0, 9000000000000]) (some (4,
      0, 6)) (some (4, 6, 6)) (.next ([3375000000000, 0], [450000000000, 9000000000000]) (some (4,
      6, 6)) (some (4, 6, 6)) (.next ([2430000000000], [570000000000]) (some (4, 6, 6)) (some (4, 6,
      6)) (.next ([1350000000000], [675000000000, -9000000000000]) (some (4, 6, 6)) (some (4, 6, 6))
      (.next ([1350000000000, 9000000000000], [1350000000000, 9000000000000]) (some (4, 6, 6)) (some
      (4, 6, 6)) fan12Owner4Part0))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded12_6 :
    ExclusionHint.check
      (model12.B 6 ++ [step12.q])
      9000000000000
      (model12.caps 6)
      (model12.ord 6)
      12
      (.pair 1 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded12_7 :
    ExclusionHint.check
      (model12.B 7 ++ [step12.q])
      9000000000000
      (model12.caps 7)
      (model12.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded12_8 :
    ExclusionHint.check
      (model12.B 8 ++ [step12.q])
      9000000000000
      (model12.caps 8)
      (model12.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded12_9 :
    ExclusionHint.check
      (model12.B 9 ++ [step12.q])
      9000000000000
      (model12.caps 9)
      (model12.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded13_0 :
    ExclusionHint.check
      (model13.B 0 ++ [step13.q])
      9000000000000
      (model13.caps 0)
      (model13.ord 0)
      12
      (.pair 0 8)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded13_1 :
    ExclusionHint.check
      (model13.B 1 ++ [step13.q])
      9000000000000
      (model13.caps 1)
      (model13.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded13_2 :
    ExclusionHint.check
      (model13.B 2 ++ [step13.q])
      9000000000000
      (model13.caps 2)
      (model13.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint150000160000
end ConwaySoifer.Simplified.Certificates
