/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1500001600003
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown1500001600003Part6. -/

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

theorem checkedWitnessForExcluded30_0 :
    ExclusionHint.check
      (model30.B 0 ++ [step30.q])
      9000000000000
      (model30.caps 0)
      (model30.ord 0)
      12
      (.pair 0 11)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded30_1 :
    ExclusionHint.check
      (model30.B 1 ++ [step30.q])
      9000000000000
      (model30.caps 1)
      (model30.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded30_2 :
    ExclusionHint.check
      (model30.B 2 ++ [step30.q])
      9000000000000
      (model30.caps 2)
      (model30.ord 2)
      12
      (.pair 0 7)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded30_3 :
    ExclusionHint.check
      (model30.B 3 ++ [step30.q])
      9000000000000
      (model30.caps 3)
      (model30.ord 3)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded30_5 :
    ExclusionHint.check
      (model30.B 5 ++ [step30.q])
      9000000000000
      (model30.caps 5)
      (model30.ord 5)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded30_6 :
    ExclusionHint.check
      (model30.B 6 ++ [step30.q])
      9000000000000
      (model30.caps 6)
      (model30.ord 6)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded30_7 :
    ExclusionHint.check
      (model30.B 7 ++ [step30.q])
      9000000000000
      (model30.caps 7)
      (model30.ord 7)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded30_9 :
    ExclusionHint.check
      (model30.B 9 ++ [step30.q])
      9000000000000
      (model30.caps 9)
      (model30.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

end Aown150000160000
end ConwaySoifer.Simplified.Certificates
