/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2800002900002
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Sint2800002900002Part1. -/

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

theorem checkedWitnessForExcluded16_9 :
    ExclusionHint.check
      (model16.B 9 ++ [step16.q])
      9000000000000
      (model16.caps 9)
      (model16.ord 9)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

private theorem checkedWitnessForExcluded17_0Left :
    ExclusionHint.check
      (model17.B 0 ++ [step17.q])
      9000000000000
      (model17.caps 0)
      (model17.ord 0)
      12
      (.witnessedFan (.next
      ([6090000000000], [165000000000]) (some (9, 12, 6)) (some (9, 12, 7)) (.next ([5625000000000],
      [255000000000]) (some (9, 12, 7)) (some (9, 12, 7)) (.next ([1856400000000, 2130000000000],
      [86400000000, 2130000000000]) (some (9, 12, 7)) (some (9, 12, 7)) (.next ([5490000000000],
      [300000000000]) (some (9, 12, 7)) (some (9, 12, 7)) (.next ([5250000000000], [300000000000])
      (some (9, 12, 7)) (some (9, 12, 7)) (.next ([1965000000000], [135000000000]) (some (9, 12, 7))
      (some (9, 12, 8)) (.next ([6015000000000], [465000000000]) (some (9, 12, 8)) (some (9, 12, 8))
      (.next ([5625000000000], [630000000000]) (some (9, 12, 8)) (some (9, 12, 8)) (.next
      ([5265000000000], [840000000000]) (some (9, 12, 8)) (some (9, 12, 8))
      fan17Owner0Part4))))))))))
      (0) (604) (120700) = true := by
  certify_fan

private theorem checkedWitnessForExcluded17_0Right :
    ExclusionHint.check
      (model17.B 0 ++ [step17.q])
      9000000000000
      (model17.caps 0)
      (model17.ord 0)
      12
      (.witnessedFan (.next ([6090000000000], [165000000000]) (some (9,
      12, 6)) (some (9, 12, 7)) (.next ([5625000000000], [255000000000]) (some (9, 12, 7)) (some (9,
      12, 7)) (.next ([5490000000000], [300000000000]) (some (9, 12, 7)) (some (9, 12, 7)) (.next
      ([5250000000000], [300000000000]) (some (9, 12, 7)) (some (9, 12, 7)) (.next ([1965000000000],
      [135000000000]) (some (9, 12, 7)) (some (9, 12, 8)) fan17Owner0Part9))))))
      (604) (1207) (120700) = true := by
  certify_fan

theorem checkedWitnessForExcluded17_0 :
    ExclusionHint.check
      (model17.B 0 ++ [step17.q])
      9000000000000
      (model17.caps 0)
      (model17.ord 0)
      12
      (.split (0) (604) (1207) (120700) (.witnessedFan (.next
      ([6090000000000], [165000000000]) (some (9, 12, 6)) (some (9, 12, 7)) (.next ([5625000000000],
      [255000000000]) (some (9, 12, 7)) (some (9, 12, 7)) (.next ([1856400000000, 2130000000000],
      [86400000000, 2130000000000]) (some (9, 12, 7)) (some (9, 12, 7)) (.next ([5490000000000],
      [300000000000]) (some (9, 12, 7)) (some (9, 12, 7)) (.next ([5250000000000], [300000000000])
      (some (9, 12, 7)) (some (9, 12, 7)) (.next ([1965000000000], [135000000000]) (some (9, 12, 7))
      (some (9, 12, 8)) (.next ([6015000000000], [465000000000]) (some (9, 12, 8)) (some (9, 12, 8))
      (.next ([5625000000000], [630000000000]) (some (9, 12, 8)) (some (9, 12, 8)) (.next
      ([5265000000000], [840000000000]) (some (9, 12, 8)) (some (9, 12, 8))
      fan17Owner0Part4)))))))))) (.witnessedFan (.next ([6090000000000], [165000000000]) (some (9,
      12, 6)) (some (9, 12, 7)) (.next ([5625000000000], [255000000000]) (some (9, 12, 7)) (some (9,
      12, 7)) (.next ([5490000000000], [300000000000]) (some (9, 12, 7)) (some (9, 12, 7)) (.next
      ([5250000000000], [300000000000]) (some (9, 12, 7)) (some (9, 12, 7)) (.next ([1965000000000],
      [135000000000]) (some (9, 12, 7)) (some (9, 12, 8)) fan17Owner0Part9)))))))
      0
      1
      100 = true := by
  as_aux_lemma =>
    exact split_check_of_checks (by decide) (by decide) (by decide)
      checkedWitnessForExcluded17_0Left checkedWitnessForExcluded17_0Right

theorem checkedWitnessForExcluded17_1 :
    ExclusionHint.check
      (model17.B 1 ++ [step17.q])
      9000000000000
      (model17.caps 1)
      (model17.ord 1)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded17_2 :
    ExclusionHint.check
      (model17.B 2 ++ [step17.q])
      9000000000000
      (model17.caps 2)
      (model17.ord 2)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded17_3 :
    ExclusionHint.check
      (model17.B 3 ++ [step17.q])
      9000000000000
      (model17.caps 3)
      (model17.ord 3)
      12
      (.pair 1 4)
      0
      1
      100 = true := by
  decide +kernel

private theorem checkedWitnessForExcluded17_4Left :
    ExclusionHint.check
      (model17.B 4 ++ [step17.q])
      9000000000000
      (model17.caps 4)
      (model17.ord 4)
      12
      (.witnessedFan (.next ([4125000000000],
      [339000000000]) (some (4, 0, 6)) (some (4, 1, 6)) (.next ([3780000000000], [720000000000])
      (some (4, 1, 6)) (some (4, 1, 6)) (.next ([2691000000000], [684000000000]) (some (4, 1, 6))
      (some (4, 1, 6)) (.next ([2310000000000], [720000000000]) (some (4, 1, 6)) (some (4, 1, 6))
      (.next ([5610000000000], [2640000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next
      ([3300000000000], [1920000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([750000000000],
      [510000000000, -9000000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([5100000000000,
      9000000000000], [3900000000000, -9000000000000]) (some (4, 1, 6)) (some (5, 1, 6)) (.next
      ([2181000000000, 9000000000000], [1944000000000, -9000000000000]) (some (5, 1, 6)) (some (5,
      1, 6)) (.next ([2520000000000, 9000000000000], [2520000000000, 9000000000000]) (some (5, 1,
      6)) (some (5, 1, 6)) (.next ([1800000000000, 9000000000000], [1980000000000, -9000000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) fan17Owner4Part0))))))))))))
      (0) (2) (300) = true := by
  certify_fan

private theorem checkedWitnessForExcluded17_4Right :
    ExclusionHint.check
      (model17.B 4 ++ [step17.q])
      9000000000000
      (model17.caps 4)
      (model17.ord 4)
      12
      (.witnessedFan (.next
      ([6480000000000, -9000000000000], [-60000000000, 9000000000000]) (some (4, 0, 6)) (some (4, 1,
      6)) (.next ([4125000000000], [339000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next
      ([3780000000000], [720000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([2691000000000],
      [684000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([2310000000000], [720000000000])
      (some (4, 1, 6)) (some (4, 1, 6)) (.next ([5610000000000], [2640000000000]) (some (4, 1, 6))
      (some (4, 1, 6)) (.next ([3780000000000, 0], [1770000000000, 9000000000000]) (some (4, 1, 6))
      (some (4, 1, 6)) (.next ([750000000000], [510000000000, -9000000000000]) (some (4, 1, 6))
      (some (4, 1, 6)) (.next ([2919000000000], [1956000000000]) (some (4, 1, 6)) (some (5, 1, 6))
      (.next ([5100000000000, 9000000000000], [3900000000000, -9000000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([2181000000000, 9000000000000], [1944000000000, -9000000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2520000000000, 9000000000000], [2520000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1800000000000, 9000000000000],
      [1980000000000, -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      fan17Owner4Part1))))))))))))))
      (2) (3) (300) = true := by
  certify_fan

theorem checkedWitnessForExcluded17_4 :
    ExclusionHint.check
      (model17.B 4 ++ [step17.q])
      9000000000000
      (model17.caps 4)
      (model17.ord 4)
      12
      (.split (0) (2) (3) (300) (.witnessedFan (.next ([4125000000000],
      [339000000000]) (some (4, 0, 6)) (some (4, 1, 6)) (.next ([3780000000000], [720000000000])
      (some (4, 1, 6)) (some (4, 1, 6)) (.next ([2691000000000], [684000000000]) (some (4, 1, 6))
      (some (4, 1, 6)) (.next ([2310000000000], [720000000000]) (some (4, 1, 6)) (some (4, 1, 6))
      (.next ([5610000000000], [2640000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next
      ([3300000000000], [1920000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([750000000000],
      [510000000000, -9000000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([5100000000000,
      9000000000000], [3900000000000, -9000000000000]) (some (4, 1, 6)) (some (5, 1, 6)) (.next
      ([2181000000000, 9000000000000], [1944000000000, -9000000000000]) (some (5, 1, 6)) (some (5,
      1, 6)) (.next ([2520000000000, 9000000000000], [2520000000000, 9000000000000]) (some (5, 1,
      6)) (some (5, 1, 6)) (.next ([1800000000000, 9000000000000], [1980000000000, -9000000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) fan17Owner4Part0)))))))))))) (.witnessedFan (.next
      ([6480000000000, -9000000000000], [-60000000000, 9000000000000]) (some (4, 0, 6)) (some (4, 1,
      6)) (.next ([4125000000000], [339000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next
      ([3780000000000], [720000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([2691000000000],
      [684000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([2310000000000], [720000000000])
      (some (4, 1, 6)) (some (4, 1, 6)) (.next ([5610000000000], [2640000000000]) (some (4, 1, 6))
      (some (4, 1, 6)) (.next ([3780000000000, 0], [1770000000000, 9000000000000]) (some (4, 1, 6))
      (some (4, 1, 6)) (.next ([750000000000], [510000000000, -9000000000000]) (some (4, 1, 6))
      (some (4, 1, 6)) (.next ([2919000000000], [1956000000000]) (some (4, 1, 6)) (some (5, 1, 6))
      (.next ([5100000000000, 9000000000000], [3900000000000, -9000000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([2181000000000, 9000000000000], [1944000000000, -9000000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2520000000000, 9000000000000], [2520000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1800000000000, 9000000000000],
      [1980000000000, -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      fan17Owner4Part1)))))))))))))))
      0
      1
      100 = true := by
  as_aux_lemma =>
    exact split_check_of_checks (by decide) (by decide) (by decide)
      checkedWitnessForExcluded17_4Left checkedWitnessForExcluded17_4Right

private theorem checkedWitnessForExcluded17_6Left :
    ExclusionHint.check
      (model17.B 6 ++ [step17.q])
      9000000000000
      (model17.caps 6)
      (model17.ord 6)
      12
      (.witnessedFan (.next ([6420000000000, 0],
      [60000000000, -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([6420000000000],
      [2580000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2520000000000, 9000000000000],
      [2520000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([3900000000000,
      -9000000000000], [5100000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0,
      0], [2520000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-60000000000,
      9000000000000], [6480000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next
      ([-2580000000000], [9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2520000000000,
      -9000000000000], [5040000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-5100000000000, -9000000000000], [9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.terminal (some (3, 1, 2)) (some (3, 1, 3)) (some (3, 1, 3)))))))))))))
      (0) (2) (300) = true := by
  certify_fan

private theorem checkedWitnessForExcluded17_6Right :
    ExclusionHint.check
      (model17.B 6 ++ [step17.q])
      9000000000000
      (model17.caps 6)
      (model17.ord 6)
      12
      (.witnessedFan (.next
      ([6420000000000], [2580000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([2520000000000,
      9000000000000], [2520000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([3900000000000, -9000000000000], [5100000000000, 9000000000000]) (some (3, 0, 2)) (some (3,
      0, 2)) (.next ([-60000000000, 9000000000000], [6480000000000, -9000000000000]) (some (3, 0,
      2)) (some (3, 0, 2)) (.next ([0, 0], [2520000000000, 9000000000000]) (some (3, 0, 2)) (some
      (3, 0, 2)) (.next ([-2580000000000], [9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [5040000000000, 18000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-5100000000000, -9000000000000], [9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-6480000000000, 9000000000000], [6420000000000]) (some (3, 1, 2)) (some (3, 1,
      3)) (.terminal (some (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3)))))))))))))
      (2) (3) (300) = true := by
  certify_fan

theorem checkedWitnessForExcluded17_6 :
    ExclusionHint.check
      (model17.B 6 ++ [step17.q])
      9000000000000
      (model17.caps 6)
      (model17.ord 6)
      12
      (.split (0) (2) (3) (300) (.witnessedFan (.next ([6420000000000, 0],
      [60000000000, -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([6420000000000],
      [2580000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2520000000000, 9000000000000],
      [2520000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([3900000000000,
      -9000000000000], [5100000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0,
      0], [2520000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-60000000000,
      9000000000000], [6480000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next
      ([-2580000000000], [9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2520000000000,
      -9000000000000], [5040000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-5100000000000, -9000000000000], [9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.terminal (some (3, 1, 2)) (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (.witnessedFan (.next
      ([6420000000000], [2580000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([2520000000000,
      9000000000000], [2520000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([3900000000000, -9000000000000], [5100000000000, 9000000000000]) (some (3, 0, 2)) (some (3,
      0, 2)) (.next ([-60000000000, 9000000000000], [6480000000000, -9000000000000]) (some (3, 0,
      2)) (some (3, 0, 2)) (.next ([0, 0], [2520000000000, 9000000000000]) (some (3, 0, 2)) (some
      (3, 0, 2)) (.next ([-2580000000000], [9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [5040000000000, 18000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-5100000000000, -9000000000000], [9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-6480000000000, 9000000000000], [6420000000000]) (some (3, 1, 2)) (some (3, 1,
      3)) (.terminal (some (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))))
      0
      1
      100 = true := by
  as_aux_lemma =>
    exact split_check_of_checks (by decide) (by decide) (by decide)
      checkedWitnessForExcluded17_6Left checkedWitnessForExcluded17_6Right

theorem checkedWitnessForExcluded17_7 :
    ExclusionHint.check
      (model17.B 7 ++ [step17.q])
      9000000000000
      (model17.caps 7)
      (model17.ord 7)
      12
      (.pair 0 3)
      0
      1
      100 = true := by
  decide +kernel

end Sint280000290000
end ConwaySoifer.Simplified.Certificates
