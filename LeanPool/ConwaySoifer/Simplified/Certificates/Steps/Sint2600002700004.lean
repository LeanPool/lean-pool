/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

import LeanPool.ConwaySoifer.Certificates.FanCertificate

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint260000270000
public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2600002700004

/-!
# Sint 260000 270000 4

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint260000270000.model0

-- Generated checkpoints are proposals; all acceptance proofs are checked by the kernel.

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint260000270000

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 6 9) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 6) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([4590000000000], [195000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([1980000000000, -9000000000000], [90000000000, 9000000000000]) (some
      (6, 1, 2)) (some (6, 1, 2)) (.next ([2160000000000, -9000000000000], [180000000000,
      9000000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next ([4680000000000], [1815000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([180000000000], [90000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([4680000000000, 0], [2340000000000, 9000000000000]) (some (6, 1, 3))
      (some (6, 1, 4)) (.next ([4155000000000, -9000000000000], [2340000000000, 9000000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4125000000000], [2535000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([2250000000000], [2070000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([2145000000000], [1980000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
      ([2175000000000], [2250000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      fan32Owner5Part0)))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 5) (den := 9000000000000) (fuel := 12)
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
    · exact excluded32_3
    · exact (hj rfl).elim
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
  refine exclude_checkpoint (.witnessedFan (.next ([6405000000000], [15000000000]) (some (9, 1, 4))
      (some (9, 1, 5)) (.next ([6285000000000], [135000000000]) (some (9, 1, 5)) (some (9, 1, 5))
      (.next ([6225000000000], [420000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next
      ([5655000000000], [390000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next ([5235000000000],
      [390000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next ([5865000000000], [555000000000])
      (some (9, 1, 5)) (some (9, 1, 6)) (.next ([5397000000000], [603000000000]) (some (9, 1, 6))
      (some (9, 1, 6)) (.next ([5475000000000], [795000000000]) (some (9, 1, 6)) (some (9, 1, 6))
      (.next ([5055000000000], [795000000000]) (some (9, 1, 6)) (some (9, 1, 6))
      fan33Owner0Part2)))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([2448000000000, -9000000000000], [177000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([6660000000000, -9000000000000],
      [2340000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4035000000000,
      -9000000000000], [4788000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0],
      [2340000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-177000000000,
      -9000000000000], [2625000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-2340000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (3, 1, 2)) (.next
      ([-4788000000000, 0], [8823000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.terminal (some (3, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))) (den := 9000000000000)
      (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 7) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 6) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

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
  refine exclude_checkpoint (.pair 6 9) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 3 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([1980000000000, -9000000000000], [90000000000,
      9000000000000]) (some (6, 0, 2)) (some (6, 1, 2)) (.next ([2160000000000, -9000000000000],
      [180000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next ([4680000000000],
      [1815000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4680000000000], [2070000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([180000000000], [90000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([4680000000000, 0], [2340000000000, 9000000000000]) (some (6, 1, 3))
      (some (6, 1, 4)) (.next ([4155000000000, -9000000000000], [2340000000000, 9000000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2610000000000], [2070000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([2250000000000], [2070000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([2175000000000], [2250000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([1995000000000], [2160000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      fan34Owner5Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 5) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
    · exact (hj rfl).elim
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
  refine exclude_checkpoint (.witnessedFan (.next ([6120000000000], [240000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) fan35Owner3Part0)) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0
      1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([4125000000000, -9000000000000], [0,
      9000000000000]) (some (6, 0, 7)) (some (6, 1, 7)) (.next ([4590000000000, -9000000000000],
      [90000000000, 9000000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([4413000000000],
      [375000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([6240000000000], [690000000000])
      (some (6, 1, 7)) (some (6, 1, 7)) (.next ([375000000000], [57000000000]) (some (6, 1, 7))
      (some (6, 1, 7)) (.next ([465000000000], [90000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      (.next ([3990000000000], [855000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([3615000000000], [798000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([4920000000000,
      -9000000000000], [2340000000000, 9000000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([3990000000000, 0], [2340000000000, 9000000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([3990000000000], [3270000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([2505000000000,
      -9000000000000], [2340000000000, 9000000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([2073000000000, -9000000000000], [2715000000000, 9000000000000]) (some (6, 1, 7)) (some (6,
      1, 7)) (.next ([2340000000000], [4125000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([2250000000000], [4680000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([720000000000],
      [1620000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([795000000000], [2340000000000])
      (some (6, 1, 7)) (some (6, 1, 7)) (.next ([663000000000], [2052000000000]) (some (6, 1, 7))
      (some (6, 1, 7)) (.next ([375000000000], [2472000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      (.next ([330000000000], [2250000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([165000000000], [2085000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      fan35Owner4Part0)))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([1980000000000, -9000000000000], [90000000000,
      9000000000000]) (some (6, 0, 2)) (some (6, 1, 2)) (.next ([2160000000000, -9000000000000],
      [180000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next ([7260000000000],
      [1740000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4680000000000], [1815000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([180000000000], [90000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([4680000000000, 0], [2340000000000, 9000000000000]) (some (6, 1, 3))
      (some (6, 1, 4)) (.next ([4155000000000, -9000000000000], [2340000000000, 9000000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4920000000000, -9000000000000], [4080000000000,
      9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2250000000000], [2070000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2175000000000], [2250000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([1995000000000], [2160000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([2160000000000], [2340000000000]) (some (6, 1, 4)) (some (6, 1, 5)) (.next
      ([2940000000000], [3990000000000]) (some (6, 1, 5)) (some (6, 1, 5))
      fan35Owner5Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
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
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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

theorem excluded36_0 : ExcludedOn (model36.B 0 ++ [step36.q]) 9000000000000 (model36.caps 0)
    (model36.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6405000000000], [15000000000]) (some (7, 9, 4))
      (some (7, 9, 5)) (.next ([6285000000000], [135000000000]) (some (7, 9, 5)) (some (7, 9, 5))
      (.next ([6225000000000], [420000000000]) (some (7, 9, 5)) (some (7, 9, 5)) (.next
      ([5655000000000], [390000000000]) (some (7, 9, 5)) (some (7, 9, 5)) (.next ([5235000000000],
      [390000000000]) (some (7, 9, 5)) (some (7, 9, 5)) (.next ([5865000000000], [555000000000])
      (some (7, 9, 5)) (some (7, 9, 6)) (.next ([1635000000000], [180000000000]) (some (7, 9, 6))
      (some (7, 9, 6)) (.next ([5475000000000], [795000000000]) (some (7, 9, 6)) (some (7, 9, 6))
      (.next ([5055000000000], [795000000000]) (some (7, 9, 6)) (some (7, 9, 6))
      fan36Owner0Part2)))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 3 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([1980000000000, -9000000000000], [90000000000,
      9000000000000]) (some (6, 0, 2)) (some (6, 1, 2)) (.next ([2160000000000, -9000000000000],
      [180000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next ([5625000000000],
      [1560000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4680000000000], [1815000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([180000000000], [90000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([4680000000000, 0], [2340000000000, 9000000000000]) (some (6, 1, 3))
      (some (6, 1, 4)) (.next ([4155000000000, -9000000000000], [2340000000000, 9000000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3120000000000], [2505000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([2250000000000], [2070000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([2175000000000], [2250000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([1995000000000], [2160000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([2160000000000],
      [2340000000000]) (some (0, 1, 4)) (some (0, 1, 5)) (.next ([3285000000000, -9000000000000],
      [3900000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      fan36Owner5Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded36_7 : ExcludedOn (model36.B 7 ++ [step36.q]) 9000000000000 (model36.caps 7)
    (model36.ord 7) 0 1 100 := by
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
    · exact excluded36_0
    · exact excluded36_1
    · exact excluded36_2
    · exact excluded36_3
    · exact (hj rfl).elim
    · exact excluded36_5
    · exact excluded36_6
    · exact excluded36_7
    · exact excluded36_8
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

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
  refine exclude_checkpoint (.pair 4 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([4125000000000, -9000000000000], [0,
      9000000000000]) (some (5, 0, 6)) (some (5, 1, 6)) (.next ([4590000000000, -9000000000000],
      [90000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([6240000000000],
      [690000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([465000000000], [90000000000]) (some
      (5, 1, 6)) (some (5, 1, 6)) (.next ([6000000000000, -9000000000000], [1440000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([5805000000000], [1635000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([975000000000], [525000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([3990000000000, 0], [2340000000000, 9000000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([4890000000000], [3450000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([1875000000000], [1440000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([510000000000], [435000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      fan37Owner4Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([1980000000000, -9000000000000], [90000000000,
      9000000000000]) (some (6, 0, 2)) (some (6, 1, 2)) (.next ([2160000000000, -9000000000000],
      [180000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next ([4680000000000],
      [1815000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([180000000000], [90000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4680000000000, 0], [2340000000000, 9000000000000])
      (some (6, 1, 3)) (some (6, 1, 4)) (.next ([4155000000000, -9000000000000], [2340000000000,
      9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([5100000000000, -9000000000000],
      [3000000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([945000000000],
      [660000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4020000000000], [3420000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2250000000000], [2070000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([3120000000000], [2910000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      fan37Owner5Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([4320000000000], [375000000000]) (some (5, 1, 2))
      (some (5, 1, 3)) (.next ([8100000000000], [1560000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([3780000000000], [1185000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      fan37Owner6Part0)))) (den := 9000000000000)
      (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded37_8 : ExcludedOn (model37.B 8 ++ [step37.q]) 9000000000000 (model37.caps 8)
    (model37.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded37_9 : ExcludedOn (model37.B 9 ++ [step37.q]) 9000000000000 (model37.caps 9)
    (model37.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
    · exact (hj rfl).elim
    · exact excluded37_1
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
  refine exclude_checkpoint (.pair 0 9) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 0 6) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

private theorem excluded38_5CheckLeft :
    ExclusionHint.check
      (model38.B 5 ++ [step38.q])
      9000000000000
      (model38.caps 5)
      (model38.ord 5)
      12
      (.witnessedFan (.next ([1980000000000,
      -9000000000000], [90000000000, 9000000000000]) (some (5, 0, 6)) (some (5, 6, 6)) (.next
      ([2160000000000, -9000000000000], [180000000000, 9000000000000]) (some (5, 6, 6)) (some (5, 6,
      6)) (.next ([4320000000000], [510000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next
      ([4500000000000], [600000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([2340000000000,
      9000000000000], [420000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([4680000000000], [1815000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([6495000000000],
      [2760000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([180000000000], [90000000000])
      (some (0, 6, 3)) (some (0, 6, 3)) (.next ([4680000000000, 0], [2340000000000, 9000000000000])
      (some (0, 6, 3)) (some (0, 6, 4)) fan38Owner5Part0))))))))))
      (0) (120) (16100) = true := by
  certify_fan

private theorem excluded38_5CheckRight :
    ExclusionHint.check
      (model38.B 5 ++ [step38.q])
      9000000000000
      (model38.caps 5)
      (model38.ord 5)
      12
      (.witnessedFan (.next
      ([1980000000000, -9000000000000], [90000000000, 9000000000000]) (some (5, 0, 6)) (some (5, 6,
      6)) (.next ([4320000000000], [510000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next
      ([2160000000000, -9000000000000], [180000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6,
      3)) (.next ([4500000000000], [600000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([2340000000000, 9000000000000], [420000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6,
      3)) (.next ([4680000000000], [1815000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([6495000000000], [2760000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([180000000000],
      [90000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([4680000000000, 0], [2340000000000,
      9000000000000]) (some (0, 6, 3)) (some (0, 6, 4)) fan38Owner5Part1))))))))))
      (120) (161) (16100) = true := by
  certify_fan

private theorem excluded38_5Check :
    ExclusionHint.check
      (model38.B 5 ++ [step38.q])
      9000000000000
      (model38.caps 5)
      (model38.ord 5)
      12
      (.split (0) (120) (161) (16100) (.witnessedFan (.next ([1980000000000,
      -9000000000000], [90000000000, 9000000000000]) (some (5, 0, 6)) (some (5, 6, 6)) (.next
      ([2160000000000, -9000000000000], [180000000000, 9000000000000]) (some (5, 6, 6)) (some (5, 6,
      6)) (.next ([4320000000000], [510000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next
      ([4500000000000], [600000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([2340000000000,
      9000000000000], [420000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([4680000000000], [1815000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([6495000000000],
      [2760000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([180000000000], [90000000000])
      (some (0, 6, 3)) (some (0, 6, 3)) (.next ([4680000000000, 0], [2340000000000, 9000000000000])
      (some (0, 6, 3)) (some (0, 6, 4)) fan38Owner5Part0)))))))))) (.witnessedFan (.next
      ([1980000000000, -9000000000000], [90000000000, 9000000000000]) (some (5, 0, 6)) (some (5, 6,
      6)) (.next ([4320000000000], [510000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next
      ([2160000000000, -9000000000000], [180000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6,
      3)) (.next ([4500000000000], [600000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([2340000000000, 9000000000000], [420000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6,
      3)) (.next ([4680000000000], [1815000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([6495000000000], [2760000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([180000000000],
      [90000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([4680000000000, 0], [2340000000000,
      9000000000000]) (some (0, 6, 3)) (some (0, 6, 4)) fan38Owner5Part1)))))))))))
      0 1 100 = true := by
  as_aux_lemma =>
    exact split_check_of_checks (by decide) (by decide) (by decide)
      excluded38_5CheckLeft excluded38_5CheckRight

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.split (0) (120) (161) (16100) (.witnessedFan (.next ([1980000000000,
      -9000000000000], [90000000000, 9000000000000]) (some (5, 0, 6)) (some (5, 6, 6)) (.next
      ([2160000000000, -9000000000000], [180000000000, 9000000000000]) (some (5, 6, 6)) (some (5, 6,
      6)) (.next ([4320000000000], [510000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next
      ([4500000000000], [600000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([2340000000000,
      9000000000000], [420000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([4680000000000], [1815000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([6495000000000],
      [2760000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([180000000000], [90000000000])
      (some (0, 6, 3)) (some (0, 6, 3)) (.next ([4680000000000, 0], [2340000000000, 9000000000000])
      (some (0, 6, 3)) (some (0, 6, 4)) fan38Owner5Part0)))))))))) (.witnessedFan (.next
      ([1980000000000, -9000000000000], [90000000000, 9000000000000]) (some (5, 0, 6)) (some (5, 6,
      6)) (.next ([4320000000000], [510000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next
      ([2160000000000, -9000000000000], [180000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6,
      3)) (.next ([4500000000000], [600000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([2340000000000, 9000000000000], [420000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6,
      3)) (.next ([4680000000000], [1815000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([6495000000000], [2760000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([180000000000],
      [90000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([4680000000000, 0], [2340000000000,
      9000000000000]) (some (0, 6, 3)) (some (0, 6, 4)) fan38Owner5Part1))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact excluded38_5Check

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 3 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_7 : ExcludedOn (model38.B 7 ++ [step38.q]) 9000000000000 (model38.caps 7)
    (model38.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded38_8 : ExcludedOn (model38.B 8 ++ [step38.q]) 9000000000000 (model38.caps 8)
    (model38.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 6 9) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_4 : ExcludedOn (model39.B 4 ++ [step39.q]) 9000000000000 (model39.caps 4)
    (model39.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 6) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([1980000000000, -9000000000000], [90000000000,
      9000000000000]) (some (5, 0, 6)) (some (5, 1, 6)) (.next ([2160000000000, -9000000000000],
      [180000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4680000000000],
      [1815000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([180000000000], [90000000000])
      (some (0, 1, 6)) (some (0, 1, 6)) (.next ([4680000000000, 0], [2340000000000, 9000000000000])
      (some (0, 1, 6)) (some (0, 1, 6)) (.next ([4155000000000, -9000000000000], [2340000000000,
      9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([4680000000000], [3435000000000])
      (some (0, 1, 6)) (some (0, 1, 6)) (.next ([2250000000000], [2070000000000]) (some (0, 1, 6))
      (some (0, 1, 6)) (.next ([2175000000000], [2250000000000]) (some (0, 1, 6)) (some (0, 1, 6))
      fan39Owner5Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded39_7 : ExcludedOn (model39.B 7 ++ [step39.q]) 9000000000000 (model39.caps 7)
    (model39.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_8 : ExcludedOn (model39.B 8 ++ [step39.q]) 9000000000000 (model39.caps 8)
    (model39.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded39_9 : ExcludedOn (model39.B 9 ++ [step39.q]) 9000000000000 (model39.caps 9)
    (model39.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([5415000000000], [150000000000]) (some (3, 0, 1))
      (some (3, 1, 2)) (.next ([2655000000000], [3585000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([3435000000000], [5565000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([675000000000], [2760000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [6240000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-150000000000], [5565000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3585000000000], [6240000000000]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([-5565000000000], [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-2760000000000], [3435000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some
      (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

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
    · exact (hj rfl).elim
    · exact excluded39_7
    · exact excluded39_8
    · exact excluded39_9
theorem next39 : model39.insert step39 = model40 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

end Sint260000270000
end ConwaySoifer.Simplified.Certificates
