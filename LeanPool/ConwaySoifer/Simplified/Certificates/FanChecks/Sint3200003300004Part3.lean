/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint3200003300004
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint3200003300004Part3. -/

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

theorem checkedWitnessForExcluded34_7 :
    ExclusionHint.check
      (model34.B 7 ++ [step34.q])
      9000000000000
      (model34.caps 7)
      (model34.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded34_8 :
    ExclusionHint.check
      (model34.B 8 ++ [step34.q])
      9000000000000
      (model34.caps 8)
      (model34.ord 8)
      12
      (.witnessedFan (.next ([3816000000000], [1629000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([4680000000000], [2805000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([2640000000000], [3669000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([3816000000000], [6309000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [7485000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1629000000000], [5445000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2805000000000], [7485000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-3669000000000], [6309000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-6309000000000], [10125000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded34_9 :
    ExclusionHint.check
      (model34.B 9 ++ [step34.q])
      9000000000000
      (model34.caps 9)
      (model34.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded35_0 :
    ExclusionHint.check
      (model35.B 0 ++ [step35.q])
      9000000000000
      (model35.caps 0)
      (model35.ord 0)
      12
      (.pair 4 6)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded35_1 :
    ExclusionHint.check
      (model35.B 1 ++ [step35.q])
      9000000000000
      (model35.caps 1)
      (model35.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded35_2 :
    ExclusionHint.check
      (model35.B 2 ++ [step35.q])
      9000000000000
      (model35.caps 2)
      (model35.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded35_3 :
    ExclusionHint.check
      (model35.B 3 ++ [step35.q])
      9000000000000
      (model35.caps 3)
      (model35.ord 3)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded35_5 :
    ExclusionHint.check
      (model35.B 5 ++ [step35.q])
      9000000000000
      (model35.caps 5)
      (model35.ord 5)
      12
      (.witnessedFan (.next ([3390000000000], [360000000000]) (some (5, 0, 3))
      (some (5, 1, 3)) (.next ([3375000000000], [441000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([66000000000], [15000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([4500000000000], [1485000000000]) (some (5, 1, 3)) (some (5, 1, 4)) (.next ([4680000000000,
      0], [2700000000000, 9000000000000]) (some (5, 1, 4)) (some (6, 1, 4)) (.next ([510000000000,
      -9000000000000], [360000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4239000000000],
      [3636000000000]) (some (6, 1, 4)) (some (6, 1, 4)) fan35Owner5Part0))))))))
      0
      1
      100 = true := by
  certify_fan

end Sint320000330000
end ConwaySoifer.Simplified.Certificates
