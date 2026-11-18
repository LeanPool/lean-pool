/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1800001900007
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sext1800001900007Part3. -/

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

theorem checkedWitnessForExcluded58_7 :
    ExclusionHint.check
      (model58.B 7 ++ [step58.q])
      9000000000000
      (model58.caps 7)
      (model58.ord 7)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded58_8 :
    ExclusionHint.check
      (model58.B 8 ++ [step58.q])
      9000000000000
      (model58.caps 8)
      (model58.ord 8)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded58_9 :
    ExclusionHint.check
      (model58.B 9 ++ [step58.q])
      9000000000000
      (model58.caps 9)
      (model58.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded59_0 :
    ExclusionHint.check
      (model59.B 0 ++ [step59.q])
      9000000000000
      (model59.caps 0)
      (model59.ord 0)
      12
      (.pair 3 12)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded59_1 :
    ExclusionHint.check
      (model59.B 1 ++ [step59.q])
      9000000000000
      (model59.caps 1)
      (model59.ord 1)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded59_2 :
    ExclusionHint.check
      (model59.B 2 ++ [step59.q])
      9000000000000
      (model59.caps 2)
      (model59.ord 2)
      12
      (.pair 2 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded59_4 :
    ExclusionHint.check
      (model59.B 4 ++ [step59.q])
      9000000000000
      (model59.caps 4)
      (model59.ord 4)
      12
      (.witnessedFan (.next ([615000000000], [15000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) fan59Owner4Part0))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded59_5 :
    ExclusionHint.check
      (model59.B 5 ++ [step59.q])
      9000000000000
      (model59.caps 5)
      (model59.ord 5)
      12
      (.pair 1 5)
      0
      1
      100 = true := by
  decide +kernel

end Sext180000190000
end ConwaySoifer.Simplified.Certificates
