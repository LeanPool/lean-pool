/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1800001900004
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown1800001900004Part5. -/

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

theorem checkedWitnessForExcluded36_4 :
    ExclusionHint.check
      (model36.B 4 ++ [step36.q])
      9000000000000
      (model36.caps 4)
      (model36.ord 4)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded36_6 :
    ExclusionHint.check
      (model36.B 6 ++ [step36.q])
      9000000000000
      (model36.caps 6)
      (model36.ord 6)
      12
      (.pair 2 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded36_7 :
    ExclusionHint.check
      (model36.B 7 ++ [step36.q])
      9000000000000
      (model36.caps 7)
      (model36.ord 7)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded36_8 :
    ExclusionHint.check
      (model36.B 8 ++ [step36.q])
      9000000000000
      (model36.caps 8)
      (model36.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded36_9 :
    ExclusionHint.check
      (model36.B 9 ++ [step36.q])
      9000000000000
      (model36.caps 9)
      (model36.ord 9)
      12
      (.witnessedFan (.next ([2520000000000], [750000000000]) (some (4, 0, 1))
      (some (4, 1, 2)) (.next ([900000000000, -9000000000000], [750000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([4125000000000, 0], [4140000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 3)) (.next ([4125000000000], [5760000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([870000000000, 9000000000000], [1650000000000, -9000000000000]) (some (4, 1, 3)) (some
      (4, 1, 3)) (.next ([2505000000000, -9000000000000], [5760000000000]) (some (4, 1, 3)) (some
      (4, 1, 3)) (.next ([1605000000000], [5010000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([0, 0], [1620000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.next
      ([-750000000000], [3270000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-750000000000],
      [1650000000000, -9000000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-4140000000000,
      9000000000000], [8265000000000, -9000000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next
      ([-5760000000000], [9885000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1650000000000,
      9000000000000], [2520000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-5760000000000], [8265000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-5010000000000], [6615000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal (some (0, 1,
      4)) (some (0, 1, 4)) (some (0, 1, 4)))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded37_1 :
    ExclusionHint.check
      (model37.B 1 ++ [step37.q])
      9000000000000
      (model37.caps 1)
      (model37.ord 1)
      12
      (.witnessedFan (.next ([4620000000000, 9000000000000], [540000000000,
      -9000000000000]) none none (.next ([5160000000000], [1710000000000]) none none (.next
      ([2580000000000], [1080000000000]) none none (.next ([1620000000000, 9000000000000],
      [1620000000000, 9000000000000]) none none (.next ([1380000000000, -9000000000000],
      [2160000000000, 0]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([1620000000000, 9000000000000],
      [3090000000000, -9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([540000000000,
      9000000000000], [1500000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([1500000000000],
      [4290000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([0], [6330000000000,
      9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-540000000000, 9000000000000],
      [5160000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-1710000000000], [6870000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-1080000000000], [3660000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-1620000000000, -9000000000000], [3240000000000, 18000000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-2160000000000, 0], [3540000000000,
      -9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-3090000000000, 9000000000000],
      [4710000000000, 0]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-1500000000000],
      [2040000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-4290000000000],
      [5790000000000]) (some (4, 2, 3)) none (.terminal none none none)))))))))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded37_2 :
    ExclusionHint.check
      (model37.B 2 ++ [step37.q])
      9000000000000
      (model37.caps 2)
      (model37.ord 2)
      12
      (.split (0) (38) (123) (12300) (.witnessedFan (.next ([630000000000,
      -9000000000000], [0, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([7380000000000,
      0], [990000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([7500000000000,
      0], [1080000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([7380000000000,
      -9000000000000], [1620000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next
      ([5925000000000, 0], [1620000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next
      ([420000000000, -9000000000000], [120000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5,
      2)) (.next ([120000000000], [90000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next
      ([1500000000000], [1620000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([1380000000000],
      [1530000000000]) (some (0, 2, 2)) (some (0, 2, 2)) fan37Owner2Part0)))))))))) (.witnessedFan
      (.next ([2085000000000], [75000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next
      ([630000000000, -9000000000000], [0, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next
      ([7380000000000, -9000000000000], [1620000000000, 9000000000000]) (some (0, 5, 2)) (some (0,
      5, 2)) (.next ([5925000000000, 0], [1620000000000, 9000000000000]) (some (0, 5, 2)) (some (0,
      5, 2)) (.next ([420000000000, -9000000000000], [120000000000, 9000000000000]) (some (0, 5, 2))
      (some (0, 5, 2)) (.next ([120000000000], [90000000000]) (some (0, 5, 2)) (some (0, 5, 2))
      (.next ([1500000000000], [1620000000000]) (some (0, 5, 2)) (some (0, 5, 2))
      fan37Owner2Part1)))))))))
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded37_3 :
    ExclusionHint.check
      (model37.B 3 ++ [step37.q])
      9000000000000
      (model37.caps 3)
      (model37.ord 3)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

end Aown180000190000
end ConwaySoifer.Simplified.Certificates
