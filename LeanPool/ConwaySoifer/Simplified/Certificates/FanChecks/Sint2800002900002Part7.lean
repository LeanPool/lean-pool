/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2800002900002
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2800002900002Part7. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint280000290000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint280000290000

theorem checkedWitnessForExcluded22_2 :
    ExclusionHint.check
      (model22.B 2 ++ [step22.q])
      9000000000000
      (model22.caps 2)
      (model22.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded22_3 :
    ExclusionHint.check
      (model22.B 3 ++ [step22.q])
      9000000000000
      (model22.caps 3)
      (model22.ord 3)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded22_4 :
    ExclusionHint.check
      (model22.B 4 ++ [step22.q])
      9000000000000
      (model22.caps 4)
      (model22.ord 4)
      12
      (.witnessedFan (.next ([2730000000000, -9000000000000], [0,
      9000000000000]) (some (4, 0, 6)) (some (4, 6, 6)) (.next ([2145000000000], [375000000000])
      (some (4, 6, 6)) (some (4, 6, 6)) (.next ([4875000000000], [1245000000000]) (some (4, 6, 6))
      (some (4, 6, 6)) (.next ([2730000000000], [870000000000]) (some (4, 6, 3)) (some (4, 6, 3))
      (.next ([3030000000000], [1095000000000]) (some (4, 6, 3)) (some (4, 6, 3))
      fan22Owner4Part0))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded22_6 :
    ExclusionHint.check
      (model22.B 6 ++ [step22.q])
      9000000000000
      (model22.caps 6)
      (model22.ord 6)
      12
      (.pair 1 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded22_7 :
    ExclusionHint.check
      (model22.B 7 ++ [step22.q])
      9000000000000
      (model22.caps 7)
      (model22.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded22_8 :
    ExclusionHint.check
      (model22.B 8 ++ [step22.q])
      9000000000000
      (model22.caps 8)
      (model22.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded22_9 :
    ExclusionHint.check
      (model22.B 9 ++ [step22.q])
      9000000000000
      (model22.caps 9)
      (model22.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded23_0 :
    ExclusionHint.check
      (model23.B 0 ++ [step23.q])
      9000000000000
      (model23.caps 0)
      (model23.ord 0)
      12
      (.witnessedFan (.next ([6090000000000], [165000000000]) (some (9, 12,
      6)) (some (9, 12, 7)) (.next ([3480000000000], [105000000000]) (some (9, 12, 7)) (some (9, 12,
      7)) (.next ([3015000000000], [105000000000]) (some (9, 12, 7)) (some (9, 12, 7))
      fan23Owner0Part4))))
      0
      1
      100 = true := by
  certify_fan

end Sint280000290000
end ConwaySoifer.Simplified.Certificates
