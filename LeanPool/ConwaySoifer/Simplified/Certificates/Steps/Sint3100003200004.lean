/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

import LeanPool.ConwaySoifer.Certificates.FanCertificate

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint310000320000
public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint3100003200004

/-!
# Sint 310000 320000 4

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint310000320000.model0

-- Generated checkpoints are proposals; all acceptance proofs are checked by the kernel.

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint310000320000

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 6 11) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([5280000000000], [90000000000]) (some (10, 0, 6))
      (some (10, 1, 6)) (.next ([1980000000000], [45000000000]) (some (10, 1, 6)) (some (10, 1, 6))
      (.next ([2520000000000], [105000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next
      ([2685000000000], [165000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([5085000000000],
      [495000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([540000000000], [60000000000])
      (some (10, 1, 6)) (some (10, 1, 6)) (.next ([1395000000000], [165000000000]) (some (10, 1, 6))
      (some (10, 1, 6)) (.next ([5070000000000, 9000000000000], [930000000000, -9000000000000])
      (some (10, 1, 6)) (some (10, 1, 6)) (.next ([3105000000000], [615000000000]) (some (10, 1, 6))
      (some (10, 1, 6)) (.next ([3315000000000], [810000000000]) (some (10, 1, 6)) (some (10, 1, 6))
      (.next ([2475000000000], [630000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next
      ([4395000000000], [1245000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next
      ([2085000000000], [705000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([3000000000000],
      [1080000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([3375000000000], [1500000000000])
      (some (10, 1, 6)) (some (10, 1, 6)) (.next ([6105000000000], [2895000000000]) (some (10, 1,
      6)) (some (10, 1, 6)) (.next ([1125000000000], [570000000000]) (some (10, 1, 6)) (some (10, 1,
      6)) (.next ([1335000000000], [765000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next
      ([3630000000000], [2265000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([2790000000000,
      9000000000000], [1920000000000, -9000000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next
      ([2850000000000], [2025000000000]) (some (10, 1, 6)) (some (10, 1, 6))
      fan32Owner4Part2))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.witnessedFan (.next ([4515000000000], [300000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([2895000000000], [1350000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([4755000000000], [2685000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([2625000000000], [4515000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([2895000000000],
      [6105000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1560000000000], [4545000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([270000000000], [1590000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([240000000000], [2385000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([0], [7440000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-300000000000],
      [4815000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1350000000000], [4245000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2685000000000], [7440000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-4515000000000], [7140000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-6105000000000], [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-4545000000000], [6105000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1590000000000], [1860000000000]) (some (0, 1, 3)) (some (0, 4, 3)) (.next
      ([-2385000000000], [2625000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.witnessedFan (.next ([2040000000000], [105000000000]) (some (11, 11,
      6)) (some (11, 11, 7)) (.next ([5925000000000], [492000000000]) (some (11, 11, 7)) (some (11,
      11, 7)) (.next ([5160000000000], [465000000000]) (some (11, 11, 7)) (some (11, 11, 7)) (.next
      ([5055000000000], [465000000000]) (some (11, 11, 7)) (some (11, 11, 7)) (.next
      ([5820000000000], [597000000000]) (some (11, 11, 7)) (some (11, 11, 8)) (.next
      ([5127000000000], [645000000000]) (some (11, 11, 8)) (some (11, 11, 8)) (.next
      ([5022000000000], [645000000000]) (some (11, 11, 8)) (some (11, 11, 8)) (.next
      ([6330000000000], [900000000000]) (some (11, 11, 8)) (some (11, 11, 8)) (.next
      ([6660000000000], [1215000000000]) (some (11, 2, 8)) (some (11, 2, 8)) (.next
      ([5580000000000], [1215000000000]) (some (11, 2, 8)) (some (11, 2, 8)) (.next
      ([6975000000000], [1545000000000]) (some (11, 2, 8)) (some (11, 2, 8)) (.next ([147000000000],
      [33000000000]) (some (11, 2, 8)) (some (11, 2, 8)) (.next ([1395000000000], [330000000000])
      (some (11, 2, 8)) (some (11, 2, 8)) (.next ([4530000000000], [1242000000000]) (some (11, 2,
      8)) (some (11, 2, 8)) (.next ([4425000000000], [1242000000000]) (some (11, 2, 8)) (some (11,
      2, 8)) (.next ([1395000000000], [435000000000]) (some (11, 2, 8)) (some (11, 2, 8)) (.next
      ([4935000000000], [1545000000000]) (some (11, 2, 8)) (some (11, 2, 8)) (.next
      ([6330000000000], [2940000000000]) (some (11, 2, 8)) (some (11, 2, 8)) (.next
      ([6225000000000], [3045000000000]) (some (11, 2, 8)) (some (11, 2, 8)) (.next ([750000000000],
      [645000000000]) (some (11, 2, 8)) (some (11, 2, 8)) (.next ([330000000000], [315000000000])
      (some (11, 2, 8)) (some (11, 2, 8)) (.next ([1395000000000], [1395000000000]) (some (11, 2,
      8)) (some (11, 3, 8)) (.next ([315000000000], [330000000000]) (some (11, 3, 8)) (some (11, 3,
      8)) fan33Owner0Part2))))))))))))))))))))))))
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
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([5280000000000], [90000000000]) (some (10, 0, 6))
      (some (10, 1, 6)) (.next ([1980000000000], [45000000000]) (some (10, 1, 6)) (some (10, 1, 6))
      (.next ([2520000000000], [105000000000]) (some (10, 1, 6)) (some (10, 1, 6))
      fan33Owner4Part3))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.witnessedFan (.next ([4515000000000], [300000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([4755000000000], [2685000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([3420000000000], [1950000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([2685000000000], [4020000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([2625000000000],
      [4515000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([3420000000000], [6705000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([795000000000], [2190000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([240000000000], [2385000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([0], [7440000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-300000000000],
      [4815000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2685000000000], [7440000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1950000000000], [5370000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-4020000000000], [6705000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-4515000000000], [7140000000000]) (some (0, 1, 3)) (some (0, 4, 3)) (.next
      ([-6705000000000], [10125000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-2190000000000], [2985000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-2385000000000], [2625000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded33_9 : ExcludedOn (model33.B 9 ++ [step33.q]) 9000000000000 (model33.caps 9)
    (model33.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
    · exact (hj rfl).elim
    · exact excluded33_4
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
  refine exclude_checkpoint (.pair 8 11) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([5280000000000], [90000000000]) (some (8, 0, 6))
      (some (8, 10, 6)) (.next ([1980000000000], [45000000000]) (some (8, 10, 6)) (some (8, 10, 6))
      (.next ([2520000000000], [105000000000]) (some (8, 10, 6)) (some (8, 10, 6)) (.next
      ([2685000000000], [165000000000]) (some (8, 10, 6)) (some (8, 10, 6)) (.next ([5085000000000],
      [495000000000]) (some (8, 10, 6)) (some (8, 10, 6)) (.next ([540000000000], [60000000000])
      (some (8, 10, 6)) (some (8, 10, 6)) (.next ([1395000000000], [165000000000]) (some (8, 10, 6))
      (some (8, 10, 6)) (.next ([5070000000000, 9000000000000], [930000000000, -9000000000000])
      (some (8, 10, 6)) (some (8, 10, 6)) (.next ([3105000000000], [615000000000]) (some (8, 10, 6))
      (some (8, 10, 6)) (.next ([3315000000000], [810000000000]) (some (8, 10, 6)) (some (8, 10, 6))
      (.next ([4875000000000, 9000000000000], [1335000000000, -9000000000000]) (some (8, 10, 6))
      (some (8, 10, 6)) (.next ([4395000000000], [1245000000000]) (some (9, 10, 6)) (some (9, 10,
      6)) (.next ([2085000000000], [705000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next
      ([3000000000000], [1080000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next
      ([3375000000000], [1500000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next ([4185000000000,
      9000000000000], [2085000000000, -9000000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next
      ([1125000000000], [570000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next ([1335000000000],
      [765000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next ([3630000000000], [2265000000000])
      (some (9, 10, 6)) (some (9, 10, 6)) (.next ([2790000000000, 9000000000000], [1920000000000,
      -9000000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next ([2850000000000], [2025000000000])
      (some (9, 10, 6)) (some (9, 10, 6)) (.next ([585000000000], [510000000000]) (some (9, 10, 6))
      (some (9, 10, 6)) (.next ([795000000000], [705000000000]) (some (9, 10, 6)) (some (9, 10, 6))
      fan34Owner4Part2))))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 5) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded34_9 : ExcludedOn (model34.B 9 ++ [step34.q]) 9000000000000 (model34.caps 9)
    (model34.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
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
    · exact excluded34_3
    · exact excluded34_4
    · exact (hj rfl).elim
    · exact excluded34_6
    · exact excluded34_7
    · exact excluded34_8
    · exact excluded34_9
theorem next34 : model34.insert step34 = model35 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([5010000000000], [1365000000000]) (some (3, 0,
      5)) (some (4, 0, 5)) (.next ([5535000000000], [1965000000000]) (some (4, 0, 5)) (some (4, 0,
      5)) (.next ([4728000000000], [2145000000000]) (some (4, 0, 5)) (some (4, 5, 5))
      fan35Owner3Part0))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([5280000000000], [90000000000]) (some (8, 0, 10))
      (some (8, 1, 10)) (.next ([1980000000000], [45000000000]) (some (8, 1, 10)) (some (8, 1, 10))
      (.next ([2520000000000], [105000000000]) (some (8, 1, 10)) (some (8, 1, 10)) (.next
      ([2685000000000], [165000000000]) (some (8, 1, 10)) (some (8, 1, 10)) (.next ([7500000000000],
      [570000000000]) (some (8, 1, 10)) (some (8, 1, 10)) fan35Owner4Part3))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([8070000000000], [1500000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([4380000000000], [1890000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([4380000000000, 0], [2790000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([3480000000000, -9000000000000], [2790000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([2880000000000], [5190000000000]) (some (4, 1, 2)) (some (4, 1, 4))
      (.next ([0], [4380000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1500000000000],
      [9570000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1890000000000], [6270000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2790000000000, -9000000000000], [7170000000000,
      9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2790000000000, -9000000000000],
      [6270000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-5190000000000], [8070000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2,
      4))))))))))))))) (den := 9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 5) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded35_9 : ExcludedOn (model35.B 9 ++ [step35.q]) 9000000000000 (model35.caps 9)
    (model35.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7965000000000, 9000000000000], [930000000000,
      -9000000000000]) none none (.next ([5175000000000], [3720000000000]) none none (.next
      ([2790000000000, 9000000000000], [2790000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([2385000000000, -9000000000000], [3720000000000, 0]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([0, 0], [2790000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-930000000000, 9000000000000], [8895000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-3720000000000], [8895000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2790000000000,
      -9000000000000], [5580000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-3720000000000, 0], [6105000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.terminal (some (3, 1, 0)) none none))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([3720000000000], [105000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([6210000000000, -9000000000000], [2790000000000, 9000000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2385000000000, -9000000000000], [3720000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([930000000000, -9000000000000], [2895000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [2790000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-105000000000], [3825000000000])
      (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-2790000000000, -9000000000000], [9000000000000,
      0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3720000000000, 0], [6105000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2895000000000, -9000000000000],
      [3825000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([3825000000000], [510000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) (.next ([3075000000000], [1302000000000]) (some (4, 0, 5)) (some (4, 0, 5))
      (.next ([4728000000000], [2145000000000]) (some (4, 0, 5)) (some (4, 0, 5))
      fan36Owner3Part0)))) (den := 9000000000000)
      (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 10) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_7 : ExcludedOn (model36.B 7 ++ [step36.q]) 9000000000000 (model36.caps 7)
    (model36.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_8 : ExcludedOn (model36.B 8 ++ [step36.q]) 9000000000000 (model36.caps 8)
    (model36.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_9 : ExcludedOn (model36.B 9 ++ [step36.q]) 9000000000000 (model36.caps 9)
    (model36.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
    · exact (hj rfl).elim
    · exact excluded36_1
    · exact excluded36_2
    · exact excluded36_3
    · exact excluded36_4
    · exact excluded36_5
    · exact excluded36_6
    · exact excluded36_7
    · exact excluded36_8
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded37_0 : ExcludedOn (model37.B 0 ++ [step37.q]) 9000000000000 (model37.caps 0)
    (model37.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 7 10) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded37_1 : ExcludedOn (model37.B 1 ++ [step37.q]) 9000000000000 (model37.caps 1)
    (model37.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 10) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([2937000000000], [210000000000]) (some (0, 5, 2))
      (some (0, 5, 3)) (.next ([4125000000000], [690000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([6000000000000], [1812000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([4125000000000], [2085000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([2100000000000, 9000000000000], [2025000000000, -9000000000000]) (some (0, 5, 3)) (some (0,
      5, 3)) (.next ([2790000000000, 9000000000000], [2790000000000, 9000000000000]) (some (0, 5,
      3)) (some (0, 5, 3)) (.next ([978000000000, 0], [2232000000000, -9000000000000]) (some (0, 5,
      3)) (some (0, 5, 3)) (.next ([1185000000000], [3147000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1335000000000, -9000000000000], [4875000000000, 9000000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([705000000000, 9000000000000], [3420000000000, -9000000000000]) (some
      (0, 1, 3)) (some (0, 1, 3)) (.next ([978000000000], [5022000000000]) (some (0, 1, 3)) (some
      (0, 1, 3)) (.next ([0], [1395000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-210000000000], [3147000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-690000000000],
      [4815000000000]) (some (0, 2, 3)) (some (5, 2, 3)) (.next ([-1812000000000, -9000000000000],
      [7812000000000, 9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2085000000000],
      [6210000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2025000000000, 9000000000000],
      [4125000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2790000000000, -9000000000000],
      [5580000000000, 18000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2232000000000,
      9000000000000], [3210000000000, -9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-3147000000000], [4332000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-4875000000000,
      -9000000000000], [6210000000000]) (some (5, 2, 3)) (some (5, 2, 4)) (.next ([-3420000000000,
      9000000000000], [4125000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-5022000000000],
      [6000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.terminal (some (5, 2, 4)) (some (5, 2,
      0)) (some (5, 2, 4))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded37_8 : ExcludedOn (model37.B 8 ++ [step37.q]) 9000000000000 (model37.caps 8)
    (model37.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded37_9 : ExcludedOn (model37.B 9 ++ [step37.q]) 9000000000000 (model37.caps 9)
    (model37.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([3978000000000], [495000000000]) (some (3, 0, 1))
      (some (3, 1, 2)) (.next ([2715000000000, -9000000000000], [2790000000000, 9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3978000000000], [6000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1188000000000, -9000000000000], [6000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([0], [5505000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next
      ([-495000000000], [4473000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-2790000000000,
      -9000000000000], [5505000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6000000000000],
      [9978000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6000000000000], [7188000000000,
      -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1,
      3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem checked37 : StepValid model37 9000000000000 step37 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded37_0
    · exact excluded37_1
    · exact excluded37_2
    · exact excluded37_3
    · exact excluded37_4
    · exact (hj rfl).elim
    · exact excluded37_6
    · exact excluded37_7
    · exact excluded37_8
    · exact excluded37_9
theorem next37 : model37.insert step37 = model38 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded38_0 : ExcludedOn (model38.B 0 ++ [step38.q]) 9000000000000 (model38.caps 0)
    (model38.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 10) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_1 : ExcludedOn (model38.B 1 ++ [step38.q]) 9000000000000 (model38.caps 1)
    (model38.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_2 : ExcludedOn (model38.B 2 ++ [step38.q]) 9000000000000 (model38.caps 2)
    (model38.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_3 : ExcludedOn (model38.B 3 ++ [step38.q]) 9000000000000 (model38.caps 3)
    (model38.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_4 : ExcludedOn (model38.B 4 ++ [step38.q]) 9000000000000 (model38.caps 4)
    (model38.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 10) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([4125000000000], [690000000000]) (some (0, 5, 2))
      (some (0, 5, 3)) (.next ([4125000000000], [2085000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([2100000000000, 9000000000000], [2025000000000, -9000000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([2790000000000, 9000000000000], [2790000000000, 9000000000000]) (some
      (0, 5, 3)) (some (0, 5, 3)) (.next ([4590000000000], [4815000000000]) (some (0, 5, 3)) (some
      (0, 5, 3)) (.next ([2490000000000, -9000000000000], [2790000000000, 9000000000000]) (some (0,
      5, 3)) (some (0, 5, 3)) (.next ([3195000000000], [6210000000000]) (some (0, 5, 3)) (some (0,
      5, 3)) (.next ([1335000000000, -9000000000000], [3480000000000, 9000000000000]) (some (0, 5,
      3)) (some (0, 5, 3)) (.next ([1335000000000, -9000000000000], [4875000000000, 9000000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([705000000000, 9000000000000], [3420000000000,
      -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0], [1395000000000]) (some (0, 5,
      3)) (some (0, 5, 3)) (.next ([-690000000000], [4815000000000]) (some (0, 5, 3)) (some (0, 5,
      3)) (.next ([-2085000000000], [6210000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-2025000000000, 9000000000000], [4125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-2790000000000, -9000000000000], [5580000000000, 18000000000000]) (some (0, 5, 3)) (some (0,
      5, 3)) (.next ([-4815000000000], [9405000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-2790000000000, -9000000000000], [5280000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-6210000000000], [9405000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3480000000000,
      -9000000000000], [4815000000000]) (some (0, 5, 3)) (some (5, 5, 3)) (.next ([-4875000000000,
      -9000000000000], [6210000000000]) (some (5, 5, 3)) (some (5, 5, 4)) (.next ([-3420000000000,
      9000000000000], [4125000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.terminal (some (5, 5, 4))
      (some (5, 2, 0)) (some (5, 5, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded38_7 : ExcludedOn (model38.B 7 ++ [step38.q]) 9000000000000 (model38.caps 7)
    (model38.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_8 : ExcludedOn (model38.B 8 ++ [step38.q]) 9000000000000 (model38.caps 8)
    (model38.ord 8) 0 1 100 := by
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
    · exact excluded38_8
    · exact (hj rfl).elim
theorem next38 : model38.insert step38 = model39 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded39_0 : ExcludedOn (model39.B 0 ++ [step39.q]) 9000000000000 (model39.caps 0)
    (model39.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 5 10) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_1 : ExcludedOn (model39.B 1 ++ [step39.q]) 9000000000000 (model39.caps 1)
    (model39.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_2 : ExcludedOn (model39.B 2 ++ [step39.q]) 9000000000000 (model39.caps 2)
    (model39.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_3 : ExcludedOn (model39.B 3 ++ [step39.q]) 9000000000000 (model39.caps 3)
    (model39.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([4728000000000], [2145000000000]) (some (3, 5,
      3)) (some (4, 5, 3)) (.next ([2295000000000], [1125000000000]) (some (4, 5, 3)) (some (4, 5,
      3)) (.next ([4770000000000], [2895000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([3603000000000], [2670000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([3645000000000],
      [3420000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([4728000000000], [4647000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([4770000000000], [5397000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([525000000000], [600000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([1125000000000], [1977000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([750000000000], [3978000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([42000000000],
      [750000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [2895000000000]) (some (4, 5,
      3)) (some (4, 5, 3)) (.next ([-2145000000000], [6873000000000]) (some (0, 5, 3)) (some (5, 5,
      3)) (.next ([-1125000000000], [3420000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
      ([-2895000000000], [7665000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
      ([-2670000000000], [6273000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
      ([-3420000000000], [7065000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
      ([-4647000000000], [9375000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
      ([-5397000000000], [10167000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-600000000000], [1125000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1977000000000],
      [3102000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-3978000000000], [4728000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-750000000000], [792000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.terminal (some (5, 2, 3)) (some (5, 3, 3)) (some (5, 3,
      3))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_6 : ExcludedOn (model39.B 6 ++ [step39.q]) 9000000000000 (model39.caps 6)
    (model39.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_7 : ExcludedOn (model39.B 7 ++ [step39.q]) 9000000000000 (model39.caps 7)
    (model39.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_8 : ExcludedOn (model39.B 8 ++ [step39.q]) 9000000000000 (model39.caps 8)
    (model39.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([4515000000000], [300000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([4755000000000], [2685000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([5397000000000], [3603000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([1560000000000], [2043000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([2625000000000],
      [4515000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([912000000000], [1860000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1152000000000], [4245000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([240000000000], [2385000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([0], [7440000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-300000000000],
      [4815000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2685000000000], [7440000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3603000000000], [9000000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-2043000000000], [3603000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-4515000000000], [7140000000000]) (some (0, 1, 3)) (some (0, 4, 3)) (.next
      ([-1860000000000], [2772000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-4245000000000], [5397000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-2385000000000], [2625000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded39_9 : ExcludedOn (model39.B 9 ++ [step39.q]) 9000000000000 (model39.caps 9)
    (model39.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
    · exact (hj rfl).elim
    · exact excluded39_5
    · exact excluded39_6
    · exact excluded39_7
    · exact excluded39_8
    · exact excluded39_9
theorem next39 : model39.insert step39 = model40 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

end Sint310000320000
end ConwaySoifer.Simplified.Certificates
