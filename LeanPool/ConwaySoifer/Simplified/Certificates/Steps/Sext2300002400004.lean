/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

import LeanPool.ConwaySoifer.Certificates.FanCertificate

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext230000240000
public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext2300002400004

/-!
# Sext 230000 240000 4

Kernel-checked forced assignments and closed-interval exclusions.
-/

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

@[expose] public section

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sext230000240000.model0

-- Generated checkpoints are proposals; all acceptance proofs are checked by the kernel.

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sext230000240000

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 4 15) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6405000000000], [720000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([2370000000000], [720000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([2445000000000, 9000000000000], [1656000000000, -9000000000000]) (some (0, 4, 2))
      (some (4, 4, 2)) (.next ([3006000000000], [3024000000000]) (some (4, 4, 2)) (some (4, 4, 2))
      (.next ([2070000000000, 9000000000000], [4035000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([1350000000000, 9000000000000], [7125000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([375000000000], [3726000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([66000000000], [3660000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0],
      [4035000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-720000000000], [7125000000000])
      (some (4, 1, 2)) (some (4, 1, 3)) (.next ([-720000000000], [3090000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-1656000000000, 9000000000000], [4101000000000, 0]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-3024000000000], [6030000000000]) (some (4, 1, 3)) (some (4, 2, 3))
      (.next ([-4035000000000, 0], [6105000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-7125000000000, 0], [8475000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-3726000000000], [4101000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3660000000000], [3726000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded32_7 : ExcludedOn (model32.B 7 ++ [step32.q]) 9000000000000 (model32.caps 7)
    (model32.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded32_8 : ExcludedOn (model32.B 8 ++ [step32.q]) 9000000000000 (model32.caps 8)
    (model32.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked32 : StepValid model32 9000000000000 step32 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded32_0
    · exact excluded32_1
    · exact excluded32_2
    · exact (hj rfl).elim
    · exact excluded32_4
    · exact excluded32_5
    · exact excluded32_6
    · exact excluded32_7
    · exact excluded32_8
    · exact excluded32_9
theorem next32 : model32.insert step32 = model33 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6555000000000], [60000000000]) (some (10, 15,
      6)) (some (11, 15, 6)) (.next ([1755000000000], [60000000000]) (some (11, 15, 6)) (some (11,
      15, 6)) (.next ([1410000000000], [60000000000]) (some (11, 15, 6)) (some (11, 15, 6)) (.next
      ([6555000000000], [375000000000]) (some (11, 15, 6)) (some (11, 15, 6)) (.next
      ([6525000000000], [465000000000]) (some (11, 15, 6)) (some (11, 15, 6)) (.next
      ([375000000000], [30000000000]) (some (11, 15, 6)) (some (11, 15, 6)) (.next ([1725000000000],
      [150000000000]) (some (11, 15, 6)) (some (11, 15, 6)) (.next ([6375000000000], [555000000000])
      (some (11, 15, 6)) (some (11, 15, 6)) (.next ([6315000000000], [645000000000]) (some (11, 15,
      6)) (some (11, 15, 6)) (.next ([2826000000000], [399000000000]) (some (11, 15, 6)) (some (11,
      15, 6)) (.next ([1035000000000], [150000000000]) (some (11, 15, 6)) (some (11, 15, 6)) (.next
      ([6000000000000], [960000000000]) (some (11, 15, 6)) (some (11, 15, 6)) (.next
      ([6240000000000], [1035000000000]) (some (11, 15, 6)) (some (11, 15, 6)) (.next
      ([5910000000000], [1020000000000]) (some (11, 15, 6)) (some (11, 15, 6)) (.next
      ([6180000000000], [1125000000000]) (some (11, 15, 6)) (some (11, 15, 6)) (.next
      ([4416000000000], [834000000000]) (some (11, 15, 6)) (some (11, 15, 6)) (.next
      ([1065000000000], [210000000000]) (some (11, 15, 6)) (some (11, 15, 6)) (.next
      ([5625000000000], [1170000000000]) (some (11, 15, 6)) (some (11, 15, 6)) (.next
      ([1440000000000], [315000000000]) (some (11, 15, 6)) (some (11, 15, 6))
      fan33Owner0Part7))))))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([4524000000000], [60000000000]) (some (6, 2, 8))
      (some (7, 2, 8)) (.next ([3726000000000], [99000000000]) (some (7, 2, 8)) (some (7, 8, 8))
      (.next ([3135000000000], [150000000000]) (some (7, 8, 8)) (some (7, 8, 8)) (.next
      ([1656000000000, -9000000000000], [99000000000]) (some (7, 8, 8)) (some (7, 8, 8)) (.next
      ([3450000000000], [249000000000]) (some (7, 8, 8)) (some (7, 8, 8)) (.next ([4185000000000],
      [690000000000]) (some (7, 8, 8)) (some (7, 8, 8)) (.next ([3639000000000], [1134000000000])
      (some (7, 8, 8)) (some (7, 8, 8)) (.next ([315000000000], [99000000000]) (some (7, 8, 4))
      (some (7, 8, 4)) (.next ([2115000000000, -9000000000000], [690000000000]) (some (7, 8, 4))
      (some (7, 8, 4)) (.next ([2775000000000], [1230000000000]) (some (7, 8, 4)) (some (7, 8, 4))
      (.next ([6000000000000], [2679000000000]) (some (7, 8, 4)) (some (7, 8, 4))
      fan33Owner3Part1)))))))))))) (den := 9000000000000) (fuel
      := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded33_8 : ExcludedOn (model33.B 8 ++ [step33.q]) 9000000000000 (model33.caps 8)
    (model33.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded33_9 : ExcludedOn (model33.B 9 ++ [step33.q]) 9000000000000 (model33.caps 9)
    (model33.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked33 : StepValid model33 9000000000000 step33 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded33_0
    · exact excluded33_1
    · exact excluded33_2
    · exact excluded33_3
    · exact (hj rfl).elim
    · exact excluded33_5
    · exact excluded33_6
    · exact excluded33_7
    · exact excluded33_8
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded34_0 : ExcludedOn (model34.B 0 ++ [step34.q]) 9000000000000 (model34.caps 0)
    (model34.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6555000000000], [60000000000]) (some (15, 4, 6))
      (some (15, 4, 6)) (.next ([8010000000000], [270000000000]) (some (15, 4, 6)) (some (15, 4, 6))
      (.next ([1755000000000], [60000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next
      ([1410000000000], [60000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next ([6555000000000],
      [375000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next ([6525000000000], [465000000000])
      (some (15, 4, 6)) (some (15, 4, 6)) (.next ([375000000000], [30000000000]) (some (15, 4, 6))
      (some (15, 4, 6)) (.next ([1725000000000], [150000000000]) (some (15, 4, 6)) (some (15, 4, 6))
      (.next ([6375000000000], [555000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next
      ([7875000000000], [750000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next ([6315000000000],
      [645000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next ([1035000000000], [150000000000])
      (some (15, 4, 6)) (some (15, 4, 6)) (.next ([6000000000000], [960000000000]) (some (15, 4, 6))
      (some (15, 4, 6)) (.next ([6240000000000], [1035000000000]) (some (15, 4, 6)) (some (15, 4,
      6)) (.next ([5910000000000], [1020000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next
      ([6180000000000], [1125000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next
      ([1065000000000], [210000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next ([5625000000000],
      [1170000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next ([1350000000000], [285000000000])
      (some (15, 4, 6)) (some (15, 4, 6)) fan34Owner0Part7))))))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([4965000000000], [1650000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([2445000000000, 9000000000000], [1656000000000, -9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4455000000000, 9000000000000], [4545000000000,
      -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([2010000000000], [2889000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([2070000000000, 9000000000000], [4035000000000, 0])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([2385000000000], [6615000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([375000000000], [3726000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([66000000000], [3660000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0],
      [4035000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1650000000000], [6615000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-1656000000000, 9000000000000], [4101000000000, 0])
      (some (0, 4, 3)) (some (4, 4, 3)) (.next ([-4545000000000, 9000000000000], [9000000000000, 0])
      (some (4, 4, 3)) (some (4, 4, 3)) (.next ([-2889000000000], [4899000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-4035000000000, 0], [6105000000000, 9000000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-6615000000000], [9000000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-3726000000000], [4101000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3660000000000], [3726000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6615000000000], [315000000000, -9000000000000])
      (some (4, 0, 4)) (some (4, 1, 4)) (.next ([6615000000000], [2385000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([2469000000000, 9000000000000], [2805000000000, -9000000000000])
      (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2070000000000, 9000000000000], [4365000000000])
      (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2250000000000], [6750000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([909000000000], [3966000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([399000000000], [4875000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [4365000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-315000000000, 9000000000000],
      [6930000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2385000000000],
      [9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2805000000000, 9000000000000],
      [5274000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-4365000000000], [6435000000000,
      9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-6750000000000], [9000000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3966000000000], [4875000000000]) (some (0, 1, 4))
      (some (0, 4, 4)) (.next ([-4875000000000], [5274000000000]) (some (0, 4, 4)) (some (0, 4, 4))
      (.terminal (some (0, 4, 4)) (some (0, 4, 4)) (some (0, 4, 4))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded34_7 : ExcludedOn (model34.B 7 ++ [step34.q]) 9000000000000 (model34.caps 7)
    (model34.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded34_8 : ExcludedOn (model34.B 8 ++ [step34.q]) 9000000000000 (model34.caps 8)
    (model34.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded34_9 : ExcludedOn (model34.B 9 ++ [step34.q]) 9000000000000 (model34.caps 9)
    (model34.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked34 : StepValid model34 9000000000000 step34 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded34_0
    · exact excluded34_1
    · exact excluded34_2
    · exact (hj rfl).elim
    · exact excluded34_4
    · exact excluded34_5
    · exact excluded34_6
    · exact excluded34_7
    · exact excluded34_8
    · exact excluded34_9
theorem next34 : model34.insert step34 = model35 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7365000000000, -9000000000000], [945000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2070000000000, 9000000000000],
      [2070000000000, 9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([3195000000000,
      9000000000000], [6240000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next
      ([1125000000000], [8310000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [2070000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-945000000000,
      -9000000000000], [8310000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-2070000000000, -9000000000000], [4140000000000, 18000000000000]) (some (3, 1, 0)) (some (3,
      1, 0)) (.next ([-6240000000000, 9000000000000], [9435000000000]) (some (3, 1, 0)) (some (3, 1,
      0)) (.next ([-8310000000000], [9435000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal
      (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel :=
      12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([2445000000000, 9000000000000], [1656000000000,
      -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4275000000000], [3600000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([2070000000000, 9000000000000], [4035000000000, 0])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([2505000000000, 9000000000000], [5805000000000,
      -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([375000000000], [3726000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([435000000000], [7875000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([66000000000], [3660000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([60000000000], [4149000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0],
      [4035000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1656000000000, 9000000000000],
      [4101000000000, 0]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-3600000000000],
      [7875000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4035000000000, 0],
      [6105000000000, 9000000000000]) (some (0, 4, 3)) (some (4, 4, 3)) (.next ([-5805000000000,
      9000000000000], [8310000000000, 0]) (some (4, 4, 3)) (some (4, 4, 3)) (.next
      ([-3726000000000], [4101000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-7875000000000], [8310000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3660000000000], [3726000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-4149000000000], [4209000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([3726000000000], [99000000000]) (some (5, 2, 7))
      (some (6, 2, 7)) (.next ([1656000000000, -9000000000000], [99000000000]) (some (6, 2, 7))
      (some (6, 2, 7)) (.next ([7875000000000], [690000000000]) (some (6, 2, 7)) (some (6, 2, 7))
      (.next ([4185000000000], [690000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([2115000000000, -9000000000000], [690000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([4545000000000, -9000000000000], [2070000000000, 9000000000000]) (some (6, 2, 7)) (some (6,
      2, 7)) (.next ([5805000000000, -9000000000000], [2760000000000, 9000000000000]) (some (6, 2,
      7)) (some (6, 2, 7)) (.next ([2595000000000], [1350000000000, 9000000000000]) (some (6, 2, 7))
      (some (6, 2, 7)) (.next ([2070000000000, 9000000000000], [2070000000000, 9000000000000]) (some
      (6, 2, 7)) (some (6, 2, 7)) (.next ([4050000000000], [4416000000000]) (some (6, 2, 7)) (some
      (6, 2, 7)) (.next ([2496000000000], [3105000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([459000000000], [591000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([2790000000000],
      [3726000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3000000000000], [4875000000000])
      (some (6, 2, 7)) (some (6, 2, 7)) (.next ([1971000000000, 9000000000000], [3825000000000])
      (some (6, 2, 7)) (some (6, 7, 7)) (.next ([2070000000000, 9000000000000], [4545000000000,
      -9000000000000]) (some (6, 7, 7)) (some (6, 7, 7)) (.next ([1740000000000], [4185000000000])
      (some (6, 7, 7)) (some (6, 7, 7)) (.next ([720000000000], [1875000000000]) (some (6, 7, 7))
      (some (6, 7, 7)) (.next ([1380000000000, 9000000000000], [4875000000000]) (some (6, 7, 7))
      (some (6, 7, 7)) fan35Owner3Part0)))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded35_7 : ExcludedOn (model35.B 7 ++ [step35.q]) 9000000000000 (model35.caps 7)
    (model35.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded35_8 : ExcludedOn (model35.B 8 ++ [step35.q]) 9000000000000 (model35.caps 8)
    (model35.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded35_9 : ExcludedOn (model35.B 9 ++ [step35.q]) 9000000000000 (model35.caps 9)
    (model35.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked35 : StepValid model35 9000000000000 step35 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded35_1
    · exact excluded35_2
    · exact excluded35_3
    · exact excluded35_4
    · exact excluded35_5
    · exact excluded35_6
    · exact excluded35_7
    · exact excluded35_8
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded36_0 : ExcludedOn (model36.B 0 ++ [step36.q]) 9000000000000 (model36.caps 0)
    (model36.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 15) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([2445000000000, 9000000000000], [1656000000000,
      -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([5280000000000], [3726000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([2835000000000, -9000000000000], [2070000000000,
      9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([2070000000000, 9000000000000],
      [4035000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([375000000000], [3726000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([66000000000], [3660000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([0], [4035000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-1656000000000, 9000000000000], [4101000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-3726000000000], [9006000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-2070000000000,
      -9000000000000], [4905000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-4035000000000, 0], [6105000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 4, 4)) (.next
      ([-3726000000000], [4101000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next
      ([-3660000000000], [3726000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.terminal (some (0, 4,
      4)) (some (1, 4, 0)) (some (1, 4, 4))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 7) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_8 : ExcludedOn (model36.B 8 ++ [step36.q]) 9000000000000 (model36.caps 8)
    (model36.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_9 : ExcludedOn (model36.B 9 ++ [step36.q]) 9000000000000 (model36.caps 9)
    (model36.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked36 : StepValid model36 9000000000000 step36 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded36_0
    · exact excluded36_1
    · exact excluded36_2
    · exact excluded36_3
    · exact excluded36_4
    · exact excluded36_5
    · exact excluded36_6
    · exact (hj rfl).elim
    · exact excluded36_8
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded37_0 : ExcludedOn (model37.B 0 ++ [step37.q]) 9000000000000 (model37.caps 0)
    (model37.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6615000000000], [60000000000]) (some (15, 4, 6))
      (some (15, 4, 6)) (.next ([1755000000000], [60000000000]) (some (15, 4, 6)) (some (15, 4, 6))
      (.next ([1410000000000], [60000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next
      ([6555000000000], [375000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next ([6525000000000],
      [465000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next ([375000000000], [30000000000])
      (some (15, 4, 6)) (some (15, 4, 6)) (.next ([1725000000000], [150000000000]) (some (15, 4, 6))
      (some (15, 4, 6)) (.next ([6375000000000], [555000000000]) (some (15, 4, 6)) (some (15, 4, 6))
      (.next ([7980000000000], [750000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next
      ([6315000000000], [645000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next ([1035000000000],
      [150000000000]) (some (15, 4, 6)) (some (15, 4, 6)) (.next ([7500000000000], [1095000000000])
      (some (15, 4, 6)) (some (15, 4, 6)) (.next ([6000000000000], [960000000000]) (some (15, 4, 6))
      (some (15, 4, 15)) (.next ([6240000000000], [1035000000000]) (some (15, 4, 15)) (some (15, 4,
      15)) (.next ([5910000000000], [1020000000000]) (some (15, 4, 15)) (some (15, 4, 15))
      fan37Owner0Part7))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([5895000000000], [3285000000000]) (some (0, 1,
      4)) (some (0, 1, 4)) (.next ([2445000000000, 9000000000000], [1656000000000, -9000000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([2169000000000], [3351000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([2070000000000, 9000000000000], [4035000000000, 0]) (some (0, 1, 4))
      (some (0, 4, 4)) (.next ([750000000000, 0], [3075000000000, -9000000000000]) (some (0, 4, 4))
      (some (0, 4, 4)) (.next ([750000000000], [5145000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([375000000000], [3726000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([66000000000], [3660000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0],
      [4035000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-3285000000000], [9180000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-1656000000000, 9000000000000], [4101000000000, 0])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3351000000000], [5520000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-4035000000000, 0], [6105000000000, 9000000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-3075000000000, 9000000000000], [3825000000000, -9000000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-5145000000000], [5895000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-3726000000000], [4101000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-3660000000000], [3726000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some
      (0, 4, 3)) (some (1, 4, 0)) (some (1, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 7) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([5655000000000], [240000000000]) (some (0, 3, 1))
      (some (0, 3, 2)) (.next ([2070000000000, 9000000000000], [2025000000000, -9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3855000000000], [3825000000000, -9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3855000000000], [5895000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([0], [4095000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([-240000000000], [5895000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-2025000000000,
      9000000000000], [4095000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-3825000000000,
      9000000000000], [7680000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next
      ([-5895000000000], [9750000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded37_8 : ExcludedOn (model37.B 8 ++ [step37.q]) 9000000000000 (model37.caps 8)
    (model37.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded37_9 : ExcludedOn (model37.B 9 ++ [step37.q]) 9000000000000 (model37.caps 9)
    (model37.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked37 : StepValid model37 9000000000000 step37 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded37_0
    · exact (hj rfl).elim
    · exact excluded37_2
    · exact excluded37_3
    · exact excluded37_4
    · exact excluded37_5
    · exact excluded37_6
    · exact excluded37_7
    · exact excluded37_8
    · exact excluded37_9
theorem next37 : model37.insert step37 = model38 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded38_0 : ExcludedOn (model38.B 0 ++ [step38.q]) 9000000000000 (model38.caps 0)
    (model38.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 15) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_1 : ExcludedOn (model38.B 1 ++ [step38.q]) 9000000000000 (model38.caps 1)
    (model38.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_2 : ExcludedOn (model38.B 2 ++ [step38.q]) 9000000000000 (model38.caps 2)
    (model38.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_3 : ExcludedOn (model38.B 3 ++ [step38.q]) 9000000000000 (model38.caps 3)
    (model38.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 3 7) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_4 : ExcludedOn (model38.B 4 ++ [step38.q]) 9000000000000 (model38.caps 4)
    (model38.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([2469000000000, 9000000000000], [2805000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([2070000000000, 9000000000000],
      [4365000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([909000000000], [3966000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([399000000000], [4875000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([0], [4365000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-2805000000000, 9000000000000], [5274000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-4365000000000], [6435000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 4)) (.next
      ([-3966000000000], [4875000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next
      ([-4875000000000], [5274000000000]) (some (4, 1, 4)) (some (4, 2, 4)) (.terminal (some (4, 2,
      4)) (some (0, 2, 4)) (some (4, 2, 4))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_7 : ExcludedOn (model38.B 7 ++ [step38.q]) 9000000000000 (model38.caps 7)
    (model38.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_9 : ExcludedOn (model38.B 9 ++ [step38.q]) 9000000000000 (model38.caps 9)
    (model38.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked38 : StepValid model38 9000000000000 step38 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded38_0
    · exact excluded38_1
    · exact excluded38_2
    · exact excluded38_3
    · exact excluded38_4
    · exact excluded38_5
    · exact excluded38_6
    · exact excluded38_7
    · exact (hj rfl).elim
    · exact excluded38_9
theorem next38 : model38.insert step38 = model39 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded39_0 : ExcludedOn (model39.B 0 ++ [step39.q]) 9000000000000 (model39.caps 0)
    (model39.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 15) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_1 : ExcludedOn (model39.B 1 ++ [step39.q]) 9000000000000 (model39.caps 1)
    (model39.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_2 : ExcludedOn (model39.B 2 ++ [step39.q]) 9000000000000 (model39.caps 2)
    (model39.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_3 : ExcludedOn (model39.B 3 ++ [step39.q]) 9000000000000 (model39.caps 3)
    (model39.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([3726000000000], [99000000000]) (some (5, 2, 3))
      (some (7, 2, 3)) (.next ([1656000000000, -9000000000000], [99000000000]) (some (7, 2, 3))
      (some (7, 2, 3)) (.next ([4185000000000], [690000000000]) (some (7, 2, 3)) (some (7, 2, 3))
      (.next ([6615000000000], [1800000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next
      ([2115000000000, -9000000000000], [690000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next
      ([4545000000000, -9000000000000], [2070000000000, 9000000000000]) (some (7, 2, 3)) (some (7,
      2, 3)) (.next ([2595000000000], [1350000000000, 9000000000000]) (some (7, 2, 3)) (some (7, 2,
      3)) (.next ([1926000000000], [1899000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next
      ([2070000000000, 9000000000000], [2070000000000, 9000000000000]) (some (7, 2, 3)) (some (7, 2,
      3)) (.next ([2385000000000], [2490000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next
      ([2496000000000], [3105000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([459000000000],
      [591000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([2790000000000], [3726000000000])
      (some (7, 2, 3)) (some (7, 2, 3)) (.next ([1971000000000, 9000000000000], [3825000000000])
      (some (7, 2, 3)) (some (7, 2, 3)) (.next ([2070000000000, 9000000000000], [4545000000000,
      -9000000000000]) (some (7, 2, 3)) (some (7, 2, 4)) fan39Owner3Part0)))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded39_4 : ExcludedOn (model39.B 4 ++ [step39.q]) 9000000000000 (model39.caps 4)
    (model39.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_6 : ExcludedOn (model39.B 6 ++ [step39.q]) 9000000000000 (model39.caps 6)
    (model39.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_7 : ExcludedOn (model39.B 7 ++ [step39.q]) 9000000000000 (model39.caps 7)
    (model39.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_9 : ExcludedOn (model39.B 9 ++ [step39.q]) 9000000000000 (model39.caps 9)
    (model39.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked39 : StepValid model39 9000000000000 step39 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded39_0
    · exact excluded39_1
    · exact excluded39_2
    · exact excluded39_3
    · exact excluded39_4
    · exact excluded39_5
    · exact excluded39_6
    · exact excluded39_7
    · exact (hj rfl).elim
    · exact excluded39_9
theorem next39 : model39.insert step39 = model40 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

end Sext230000240000
end ConwaySoifer.Simplified.Certificates
