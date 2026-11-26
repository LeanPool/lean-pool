/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint3200003300004
import LeanPool.ConwaySoifer.Certificates.FanCertificate
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sint3200003300004Part0RightIntervals

/-! Kernel-checked fan certificates for Sint3200003300004Part0. -/

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

theorem checkedWitnessForExcluded32_0 :
    ExclusionHint.check
      (model32.B 0 ++ [step32.q])
      9000000000000
      (model32.caps 0)
      (model32.ord 0)
      12
      (.pair 0 6)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded32_2 :
    ExclusionHint.check
      (model32.B 2 ++ [step32.q])
      9000000000000
      (model32.caps 2)
      (model32.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded32_3 :
    ExclusionHint.check
      (model32.B 3 ++ [step32.q])
      9000000000000
      (model32.caps 3)
      (model32.ord 3)
      12
      (.pair 0 5)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded32_4 :
    ExclusionHint.check
      (model32.B 4 ++ [step32.q])
      9000000000000
      (model32.caps 4)
      (model32.ord 4)
      12
      (.pair 0 7)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded32_5 :
    ExclusionHint.check
      (model32.B 5 ++ [step32.q])
      9000000000000
      (model32.caps 5)
      (model32.ord 5)
      12
      (.pair 0 6)
      0
      1
      100 = true := by
  decide +kernel

private theorem checkedWitnessForExcluded32_6Left :
    ExclusionHint.check
      (model32.B 6 ++ [step32.q])
      9000000000000
      (model32.caps 6)
      (model32.ord 6)
      12
      (.witnessedFan (.next ([900000000000, 0],
      [60000000000, -9000000000000]) (some (7, 1, 3)) (some (7, 1, 7)) (.next ([3840000000000],
      [285000000000]) (some (7, 1, 7)) (some (7, 2, 7)) (.next ([2655000000000], [285000000000])
      (some (7, 2, 7)) (some (7, 2, 7)) (.next ([5760000000000], [1935000000000]) (some (7, 2, 7))
      (some (7, 2, 7)) (.next ([6120000000000], [2190000000000]) (some (6, 2, 7)) (some (6, 2, 7))
      (.next ([4125000000000], [1635000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([2595000000000, 9000000000000], [1245000000000, -9000000000000]) (some (6, 2, 7)) (some (6,
      2, 7)) (.next ([3840000000000], [1980000000000, 9000000000000]) (some (6, 2, 7)) (some (6, 2,
      7)) (.next ([4125000000000], [2220000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([3870000000000], [2250000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([360000000000],
      [255000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([2880000000000, 9000000000000],
      [2880000000000, 9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([3840000000000],
      [5160000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([1305000000000], [1920000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([2880000000000, 9000000000000], [6060000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([1245000000000, 9000000000000], [2880000000000,
      -9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([900000000000], [2940000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([690000000000], [2280000000000]) (some (0, 2, 7))
      (some (0, 2, 7)) (.next ([1245000000000, -9000000000000], [4515000000000, 9000000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([285000000000], [1350000000000]) (some (0, 2, 7))
      (some (0, 2, 7)) (.next ([630000000000, 9000000000000], [3240000000000, -9000000000000]) (some
      (0, 2, 7)) (some (0, 2, 7)) (.next ([990000000000, -9000000000000], [5130000000000,
      9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([30000000000], [1965000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) fan32Owner6Part0))))))))))))))))))))))))
      (0) (54) (10900) = true := by
  certify_fan

private theorem checkedWitnessForExcluded32_6Right :
    ExclusionHint.check
      (model32.B 6 ++ [step32.q])
      9000000000000
      (model32.caps 6)
      (model32.ord 6)
      12
      (.split (21546)
      (35534) (43491) (4349100) (.split (21546) (28994) (35534) (4349100) (.witnessedFan (.next
      ([900000000000, 0], [60000000000, -9000000000000]) (some (7, 1, 3)) (some (7, 1, 7))
      fan32Owner6Part2)) (.witnessedFan (.next ([3840000000000], [285000000000]) (some (7, 2, 3))
      (some (7, 2, 7)) fan32Owner6Part4))) (.witnessedFan (.next ([3840000000000], [285000000000])
      (some (7, 2, 3)) (some (7, 2, 7)) (.next ([2655000000000], [285000000000]) (some (7, 2, 7))
      (some (7, 2, 7)) (.next ([5760000000000], [1935000000000]) (some (7, 2, 7)) (some (7, 2, 7))
      (.next ([6120000000000], [2190000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([4125000000000], [1635000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([2595000000000,
      9000000000000], [1245000000000, -9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([3840000000000], [1980000000000, 9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([3870000000000], [2250000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([360000000000],
      [255000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([2880000000000, 9000000000000],
      [2880000000000, 9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([3840000000000],
      [5160000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([1305000000000], [1920000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([2880000000000, 9000000000000], [6060000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([1245000000000, 9000000000000], [2880000000000,
      -9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([900000000000], [2940000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([690000000000], [2280000000000]) (some (0, 2, 7))
      (some (0, 2, 7)) (.next ([960000000000, -9000000000000], [3165000000000, 9000000000000]) (some
      (0, 2, 7)) (some (0, 2, 7)) (.next ([1245000000000, -9000000000000], [4515000000000,
      9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([630000000000, 9000000000000],
      [3240000000000, -9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([285000000000],
      [1350000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([990000000000, -9000000000000],
      [5130000000000, 9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-60000000000,
      9000000000000], [960000000000, -9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
      ([30000000000], [1965000000000]) (some (0, 2, 7)) (some (0, 2, 7))
      fan32Owner6Part5)))))))))))))))))))))))))
      (54) (109) (10900) = true := by
  refine split_check_of_checks ?_ ?_ ?_ ?_ ?_
  · decide
  · rfl
  · rfl
  · refine split_check_of_checks ?_ ?_ ?_ ?_ ?_
    · decide
    · rfl
    · rfl
    · exact checkedWitnessForExcluded32_6RightLeaf1
    · exact checkedWitnessForExcluded32_6RightLeaf2
  · exact checkedWitnessForExcluded32_6RightLeaf3

theorem checkedWitnessForExcluded32_6 :
    ExclusionHint.check
      (model32.B 6 ++ [step32.q])
      9000000000000
      (model32.caps 6)
      (model32.ord 6)
      12
      (.split (0) (54) (109) (10900) (.witnessedFan (.next ([900000000000, 0],
      [60000000000, -9000000000000]) (some (7, 1, 3)) (some (7, 1, 7)) (.next ([3840000000000],
      [285000000000]) (some (7, 1, 7)) (some (7, 2, 7)) (.next ([2655000000000], [285000000000])
      (some (7, 2, 7)) (some (7, 2, 7)) (.next ([5760000000000], [1935000000000]) (some (7, 2, 7))
      (some (7, 2, 7)) (.next ([6120000000000], [2190000000000]) (some (6, 2, 7)) (some (6, 2, 7))
      (.next ([4125000000000], [1635000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([2595000000000, 9000000000000], [1245000000000, -9000000000000]) (some (6, 2, 7)) (some (6,
      2, 7)) (.next ([3840000000000], [1980000000000, 9000000000000]) (some (6, 2, 7)) (some (6, 2,
      7)) (.next ([4125000000000], [2220000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([3870000000000], [2250000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([360000000000],
      [255000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([2880000000000, 9000000000000],
      [2880000000000, 9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([3840000000000],
      [5160000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([1305000000000], [1920000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([2880000000000, 9000000000000], [6060000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([1245000000000, 9000000000000], [2880000000000,
      -9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([900000000000], [2940000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([690000000000], [2280000000000]) (some (0, 2, 7))
      (some (0, 2, 7)) (.next ([1245000000000, -9000000000000], [4515000000000, 9000000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([285000000000], [1350000000000]) (some (0, 2, 7))
      (some (0, 2, 7)) (.next ([630000000000, 9000000000000], [3240000000000, -9000000000000]) (some
      (0, 2, 7)) (some (0, 2, 7)) (.next ([990000000000, -9000000000000], [5130000000000,
      9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([30000000000], [1965000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) fan32Owner6Part0)))))))))))))))))))))))) (.split (21546)
      (35534) (43491) (4349100) (.split (21546) (28994) (35534) (4349100) (.witnessedFan (.next
      ([900000000000, 0], [60000000000, -9000000000000]) (some (7, 1, 3)) (some (7, 1, 7))
      fan32Owner6Part2)) (.witnessedFan (.next ([3840000000000], [285000000000]) (some (7, 2, 3))
      (some (7, 2, 7)) fan32Owner6Part4))) (.witnessedFan (.next ([3840000000000], [285000000000])
      (some (7, 2, 3)) (some (7, 2, 7)) (.next ([2655000000000], [285000000000]) (some (7, 2, 7))
      (some (7, 2, 7)) (.next ([5760000000000], [1935000000000]) (some (7, 2, 7)) (some (7, 2, 7))
      (.next ([6120000000000], [2190000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([4125000000000], [1635000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([2595000000000,
      9000000000000], [1245000000000, -9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([3840000000000], [1980000000000, 9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([3870000000000], [2250000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([360000000000],
      [255000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([2880000000000, 9000000000000],
      [2880000000000, 9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([3840000000000],
      [5160000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([1305000000000], [1920000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([2880000000000, 9000000000000], [6060000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([1245000000000, 9000000000000], [2880000000000,
      -9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([900000000000], [2940000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([690000000000], [2280000000000]) (some (0, 2, 7))
      (some (0, 2, 7)) (.next ([960000000000, -9000000000000], [3165000000000, 9000000000000]) (some
      (0, 2, 7)) (some (0, 2, 7)) (.next ([1245000000000, -9000000000000], [4515000000000,
      9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([630000000000, 9000000000000],
      [3240000000000, -9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([285000000000],
      [1350000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([990000000000, -9000000000000],
      [5130000000000, 9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-60000000000,
      9000000000000], [960000000000, -9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
      ([30000000000], [1965000000000]) (some (0, 2, 7)) (some (0, 2, 7))
      fan32Owner6Part5))))))))))))))))))))))))))
      0
      1
      100 = true := by
  as_aux_lemma =>
    exact split_check_of_checks (by decide) (by decide) (by decide)
      checkedWitnessForExcluded32_6Left checkedWitnessForExcluded32_6Right

theorem checkedWitnessForExcluded32_7 :
    ExclusionHint.check
      (model32.B 7 ++ [step32.q])
      9000000000000
      (model32.caps 7)
      (model32.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded32_8 :
    ExclusionHint.check
      (model32.B 8 ++ [step32.q])
      9000000000000
      (model32.caps 8)
      (model32.ord 8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint320000330000
end ConwaySoifer.Simplified.Certificates
