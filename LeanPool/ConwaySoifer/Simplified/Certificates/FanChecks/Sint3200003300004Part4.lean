/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint3200003300004
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint3200003300004Part4. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint320000330000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint320000330000

theorem checkedWitnessForExcluded35_6 :
    ExclusionHint.check
      (model35.B 6 ++ [step35.q])
      9000000000000
      (model35.caps 6)
      (model35.ord 6)
      12
      (.pair 2 7)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded35_7 :
    ExclusionHint.check
      (model35.B 7 ++ [step35.q])
      9000000000000
      (model35.caps 7)
      (model35.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded35_8 :
    ExclusionHint.check
      (model35.B 8 ++ [step35.q])
      9000000000000
      (model35.caps 8)
      (model35.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded35_9 :
    ExclusionHint.check
      (model35.B 9 ++ [step35.q])
      9000000000000
      (model35.caps 9)
      (model35.ord 9)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded36_0 :
    ExclusionHint.check
      (model36.B 0 ++ [step36.q])
      9000000000000
      (model36.caps 0)
      (model36.ord 0)
      12
      (.pair 4 6)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded36_1 :
    ExclusionHint.check
      (model36.B 1 ++ [step36.q])
      9000000000000
      (model36.caps 1)
      (model36.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded36_2 :
    ExclusionHint.check
      (model36.B 2 ++ [step36.q])
      9000000000000
      (model36.caps 2)
      (model36.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded36_3 :
    ExclusionHint.check
      (model36.B 3 ++ [step36.q])
      9000000000000
      (model36.caps 3)
      (model36.ord 3)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

end Sint320000330000
end ConwaySoifer.Simplified.Certificates
