/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1500001600000
import LeanPool.ConwaySoifer.Certificates.FanCertificate
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sext1500001600000Part5SplitIntervals

/-! Kernel-checked fan certificates for Sext1500001600000Part5. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sext150000160000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sext150000160000

theorem checkedWitnessForExcluded4_4 :
    ExclusionHint.check
      (model4.B 4 ++ [step4.q])
      9000000000000
      (model4.caps 4)
      (model4.ord
    4)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded4_6 :
    ExclusionHint.check
      (model4.B 6 ++ [step4.q])
      9000000000000
      (model4.caps 6)
      (model4.ord
    6)
      12
      (.pair 2 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded4_7 :
    ExclusionHint.check
      (model4.B 7 ++ [step4.q])
      9000000000000
      (model4.caps 7)
      (model4.ord
    7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded4_8 :
    ExclusionHint.check
      (model4.B 8 ++ [step4.q])
      9000000000000
      (model4.caps 8)
      (model4.ord
    8)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded4_9 :
    ExclusionHint.check
      (model4.B 9 ++ [step4.q])
      9000000000000
      (model4.caps 9)
      (model4.ord
    9)
      12
      (.witnessedFan (.next ([6600000000000, 0], [1050000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 1, 2)) (.next ([6600000000000], [2400000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([825000000000], [1575000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1350000000000, 9000000000000], [6825000000000, -9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1350000000000, 9000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-1050000000000, 9000000000000], [7650000000000, -9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2400000000000], [9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-1575000000000], [2400000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-6825000000000, 9000000000000], [8175000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3))
      (.terminal (some (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded5_0 :
    ExclusionHint.check
      (model5.B 0 ++ [step5.q])
      9000000000000
      (model5.caps 0)
      (model5.ord
    0)
      12
      (.split (0) (10) (21) (2100) (.witnessedFan (.next ([1056000000000,
      5040000000000], [72000000000, -2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next
      ([1728000000000, 2520000000000], [378000000000, 2520000000000]) (some (4, 6, 2)) (some (4, 6,
      2)) (.next ([6750000000000], [2250000000000]) (some (4, 6, 2)) (some (5, 6, 2)) (.next
      ([5022000000000, -2520000000000], [3222000000000, -2520000000000]) (some (5, 6, 2)) (some (5,
      6, 2)) (.next ([5850000000000], [3975000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([972000000000, -2520000000000], [756000000000, 5040000000000]) (some (5, 6, 2)) (some (5, 6,
      2)) (.next ([4644000000000, -5040000000000], [3978000000000, 2520000000000]) (some (5, 6, 2))
      (some (5, 6, 2)) (.next ([5022000000000, -2520000000000], [4356000000000, 5040000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([4950000000000], [4350000000000]) (some (5, 6, 2))
      (some (5, 6, 2)) (.next ([828000000000, 2520000000000], [753000000000, 2520000000000]) (some
      (5, 6, 2)) (some (6, 6, 2)) (.next ([378000000000, 2520000000000], [378000000000,
      2520000000000]) (some (6, 6, 2)) (some (6, 6, 2)) fan5Owner0Part0)))))))))))) (.split (170)
      (270) (357) (35700) (.witnessedFan (.next ([1056000000000, 5040000000000], [72000000000,
      -2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([1728000000000, 2520000000000],
      [378000000000, 2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([6750000000000],
      [2250000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([5022000000000, -2520000000000],
      [3222000000000, -2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([5850000000000],
      [3975000000000]) (some (4, 6, 2)) (some (5, 6, 2)) (.next ([972000000000, -2520000000000],
      [756000000000, 5040000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([4644000000000,
      -5040000000000], [3978000000000, 2520000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([5022000000000, -2520000000000], [4356000000000, 5040000000000]) (some (5, 6, 2)) (some (5,
      6, 2)) (.next ([4950000000000], [4350000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([828000000000, 2520000000000], [753000000000, 2520000000000]) (some (5, 6, 2)) (some (6, 6,
      2)) (.next ([378000000000, 2520000000000], [378000000000, 2520000000000]) (some (6, 6, 2))
      (some (6, 6, 2)) (.next ([381000000000, 5040000000000], [447000000000, -2520000000000]) (some
      (6, 6, 2)) (some (6, 6, 2)) (.next ([306000000000, 5040000000000], [372000000000,
      -2520000000000]) (some (6, 6, 2)) (some (6, 6, 2)) fan5Owner0Part1))))))))))))))
      (.witnessedFan (.next ([1056000000000, 5040000000000], [72000000000, -2520000000000]) (some
      (4, 6, 2)) (some (4, 6, 2)) (.next ([1728000000000, 2520000000000], [378000000000,
      2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([6750000000000], [2250000000000])
      (some (4, 6, 2)) (some (4, 6, 2)) (.next ([5022000000000, -2520000000000], [3222000000000,
      -2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([5850000000000], [3975000000000])
      (some (4, 6, 2)) (some (4, 6, 2)) (.next ([972000000000, -2520000000000], [756000000000,
      5040000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([4644000000000, -5040000000000],
      [3978000000000, 2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) fan5Owner0Part2))))))))))
      0
      1
      100 = true := by
  as_aux_lemma =>
    refine split_check_of_checks ?_ ?_ ?_ ?_ ?_
    · decide
    · rfl
    · rfl
    · exact checkedWitnessForExcluded5_0Leaf1
    · refine split_check_of_checks ?_ ?_ ?_ ?_ ?_
      · decide
      · rfl
      · rfl
      · exact checkedWitnessForExcluded5_0Leaf2
      · exact checkedWitnessForExcluded5_0Leaf3

theorem checkedWitnessForExcluded5_1 :
    ExclusionHint.check
      (model5.B 1 ++ [step5.q])
      9000000000000
      (model5.caps 1)
      (model5.ord
    1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded5_2 :
    ExclusionHint.check
      (model5.B 2 ++ [step5.q])
      9000000000000
      (model5.caps 2)
      (model5.ord
    2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sext150000160000
end ConwaySoifer.Simplified.Certificates
