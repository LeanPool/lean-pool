/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1800001900007
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sext1800001900007Part5. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sext180000190000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sext180000190000

theorem checkedWitnessForExcluded60_5 :
    ExclusionHint.check
      (model60.B 5 ++ [step60.q])
      9000000000000
      (model60.caps 5)
      (model60.ord 5)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded60_6 :
    ExclusionHint.check
      (model60.B 6 ++ [step60.q])
      9000000000000
      (model60.caps 6)
      (model60.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded60_7 :
    ExclusionHint.check
      (model60.B 7 ++ [step60.q])
      9000000000000
      (model60.caps 7)
      (model60.ord 7)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded60_8 :
    ExclusionHint.check
      (model60.B 8 ++ [step60.q])
      9000000000000
      (model60.caps 8)
      (model60.ord 8)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded60_9 :
    ExclusionHint.check
      (model60.B 9 ++ [step60.q])
      9000000000000
      (model60.caps 9)
      (model60.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded61_0 :
    ExclusionHint.check
      (model61.B 0 ++ [step61.q])
      9000000000000
      (model61.caps 0)
      (model61.ord 0)
      12
      (.pair 5 12)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded61_1 :
    ExclusionHint.check
      (model61.B 1 ++ [step61.q])
      9000000000000
      (model61.caps 1)
      (model61.ord 1)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded61_2 :
    ExclusionHint.check
      (model61.B 2 ++ [step61.q])
      9000000000000
      (model61.caps 2)
      (model61.ord 2)
      12
      (.pair 2 4)
      0
      1
      100 = true := by
  decide +kernel

end Sext180000190000
end ConwaySoifer.Simplified.Certificates
