/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1800001900004
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown1800001900004Part8. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Aown180000190000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Aown180000190000

theorem checkedWitnessForExcluded39_1 :
    ExclusionHint.check
      (model39.B 1 ++ [step39.q])
      9000000000000
      (model39.caps 1)
      (model39.ord 1)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded39_2 :
    ExclusionHint.check
      (model39.B 2 ++ [step39.q])
      9000000000000
      (model39.caps 2)
      (model39.ord 2)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded39_3 :
    ExclusionHint.check
      (model39.B 3 ++ [step39.q])
      9000000000000
      (model39.caps 3)
      (model39.ord 3)
      12
      (.witnessedFan (.next ([6570000000000], [180000000000]) (some (2, 4, 1))
      (some (4, 4, 1)) (.next ([5820000000000], [750000000000]) (some (4, 4, 1)) (some (4, 4, 1))
      (.next ([6000000000000], [1620000000000, 9000000000000]) (some (4, 4, 1)) (some (4, 4, 2))
      (.next ([4950000000000, -9000000000000], [1800000000000, 9000000000000]) (some (4, 4, 2))
      (some (4, 4, 2)) (.next ([6570000000000], [2721000000000]) (some (4, 4, 2)) (some (4, 4, 2))
      (.next ([1620000000000, 9000000000000], [921000000000, -9000000000000]) (some (4, 1, 2)) (some
      (4, 1, 2)) (.next ([0], [1620000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([-180000000000], [6750000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-750000000000], [6570000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-1620000000000,
      -9000000000000], [7620000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-1800000000000, -9000000000000], [6750000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-2721000000000], [9291000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-921000000000,
      9000000000000], [2541000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2))
      (some (4, 1, 2)) (some (4, 1, 2)))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded39_4 :
    ExclusionHint.check
      (model39.B 4 ++ [step39.q])
      9000000000000
      (model39.caps 4)
      (model39.ord 4)
      12
      (.pair 1 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded39_5 :
    ExclusionHint.check
      (model39.B 5 ++ [step39.q])
      9000000000000
      (model39.caps 5)
      (model39.ord 5)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded39_6 :
    ExclusionHint.check
      (model39.B 6 ++ [step39.q])
      9000000000000
      (model39.caps 6)
      (model39.ord 6)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded39_7 :
    ExclusionHint.check
      (model39.B 7 ++ [step39.q])
      9000000000000
      (model39.caps 7)
      (model39.ord 7)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded39_9 :
    ExclusionHint.check
      (model39.B 9 ++ [step39.q])
      9000000000000
      (model39.caps 9)
      (model39.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

end Aown180000190000
end ConwaySoifer.Simplified.Certificates
