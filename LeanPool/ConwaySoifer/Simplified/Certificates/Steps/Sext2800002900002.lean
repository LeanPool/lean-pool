/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

import LeanPool.ConwaySoifer.Certificates.FanCertificate

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext280000290000
public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext2800002900002

/-!
# Sext 280000 290000 2

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sext280000290000.model0

-- Generated checkpoints are proposals; all acceptance proofs are checked by the kernel.

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sext280000290000

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 11) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([2520000000000, 9000000000000], [1155000000000,
      -9000000000000]) (some (2, 4, 1)) (some (4, 4, 1)) (.next ([6420000000000], [3675000000000])
      (some (4, 0, 1)) (some (4, 0, 1)) (.next ([3900000000000, -9000000000000], [2520000000000,
      9000000000000]) (some (4, 0, 1)) (some (4, 0, 1)) (.next ([2520000000000, 9000000000000],
      [2520000000000, 9000000000000]) (some (4, 0, 1)) (some (4, 1, 1)) (.next ([2520000000000,
      9000000000000], [3900000000000, -9000000000000]) (some (4, 1, 1)) (some (4, 1, 1)) (.next
      ([0], [2520000000000, 9000000000000]) (some (4, 1, 1)) (some (4, 1, 2)) (.next
      ([-1155000000000, 9000000000000], [3675000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-3675000000000], [10095000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [6420000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [5040000000000, 18000000000000]) (some (4, 1, 2)) (some (4,
      1, 2)) (.next ([-3900000000000, 9000000000000], [6420000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.terminal (some (4, 1, 2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded16_6 : ExcludedOn (model16.B 6 ++ [step16.q]) 9000000000000 (model16.caps 6)
    (model16.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded16_7 : ExcludedOn (model16.B 7 ++ [step16.q]) 9000000000000 (model16.caps 7)
    (model16.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded16_9 : ExcludedOn (model16.B 9 ++ [step16.q]) 9000000000000 (model16.caps 9)
    (model16.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked16 : StepValid model16 9000000000000 step16 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded16_0
    · exact excluded16_1
    · exact excluded16_2
    · exact excluded16_3
    · exact excluded16_4
    · exact excluded16_5
    · exact excluded16_6
    · exact excluded16_7
    · exact (hj rfl).elim
    · exact excluded16_9
theorem next16 : model16.insert step16 = model17 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded17_0 : ExcludedOn (model17.B 0 ++ [step17.q]) 9000000000000 (model17.caps 0)
    (model17.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 3 11) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([3690000000000], [60000000000]) (some (2, 4, 1))
      (some (3, 4, 1)) (.next ([6270000000000, 9000000000000], [210000000000, -9000000000000]) (some
      (3, 4, 1)) (some (3, 4, 1)) (.next ([3900000000000, -9000000000000], [2520000000000,
      9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([3750000000000], [2730000000000])
      (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2520000000000, 9000000000000], [2520000000000,
      9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2520000000000, 9000000000000],
      [3900000000000, -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([1230000000000,
      -9000000000000], [2730000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([0],
      [2520000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-60000000000],
      [3750000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-210000000000, 9000000000000],
      [6480000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2520000000000, -9000000000000],
      [6420000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2730000000000], [6480000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2520000000000, -9000000000000], [5040000000000,
      18000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3900000000000, 9000000000000],
      [6420000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2730000000000], [3960000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (4, 1,
      2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide)
      0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded17_6 : ExcludedOn (model17.B 6 ++ [step17.q]) 9000000000000 (model17.caps 6)
    (model17.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded17_8 : ExcludedOn (model17.B 8 ++ [step17.q]) 9000000000000 (model17.caps 8)
    (model17.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded17_9 : ExcludedOn (model17.B 9 ++ [step17.q]) 9000000000000 (model17.caps 9)
    (model17.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked17 : StepValid model17 9000000000000 step17 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded17_0
    · exact excluded17_1
    · exact excluded17_2
    · exact excluded17_3
    · exact (hj rfl).elim
    · exact excluded17_5
    · exact excluded17_6
    · exact excluded17_7
    · exact excluded17_8
    · exact excluded17_9
theorem next17 : model17.insert step17 = model18 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded18_0 : ExcludedOn (model18.B 0 ++ [step18.q]) 9000000000000 (model18.caps 0)
    (model18.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 3 11) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([375000000000], [30000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([4665000000000], [375000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([5220000000000], [5070000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([4845000000000], [5040000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2520000000000,
      9000000000000], [5070000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2145000000000,
      9000000000000], [5040000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0, 0],
      [2520000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-30000000000],
      [405000000000]) (some (4, 1, 2)) (some (4, 2, 2)) (.next ([-375000000000], [5040000000000])
      (some (4, 2, 2)) (some (4, 2, 3)) (.next ([-5070000000000], [10290000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-5040000000000], [9885000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-5070000000000, 0], [7590000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 4))
      (.next ([-5040000000000, 0], [7185000000000, 9000000000000]) (some (4, 2, 4)) (some (4, 2, 4))
      (.terminal (some (4, 2, 4)) (some (0, 2, 4)) (some (4, 2, 4))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded18_6 : ExcludedOn (model18.B 6 ++ [step18.q]) 9000000000000 (model18.caps 6)
    (model18.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded18_7 : ExcludedOn (model18.B 7 ++ [step18.q]) 9000000000000 (model18.caps 7)
    (model18.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded18_8 : ExcludedOn (model18.B 8 ++ [step18.q]) 9000000000000 (model18.caps 8)
    (model18.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded18_9 : ExcludedOn (model18.B 9 ++ [step18.q]) 9000000000000 (model18.caps 9)
    (model18.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked18 : StepValid model18 9000000000000 step18 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded18_0
    · exact excluded18_1
    · exact excluded18_2
    · exact excluded18_3
    · exact (hj rfl).elim
    · exact excluded18_5
    · exact excluded18_6
    · exact excluded18_7
    · exact excluded18_8
    · exact excluded18_9
theorem next18 : model18.insert step18 = model19 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded19_0 : ExcludedOn (model19.B 0 ++ [step19.q]) 9000000000000 (model19.caps 0)
    (model19.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 4 11) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([1956000000000], [669000000000]) (some (2, 4, 1))
      (some (3, 4, 1)) (.next ([5145000000000, 9000000000000], [1944000000000, -9000000000000])
      (some (3, 4, 1)) (some (3, 4, 1)) (.next ([3900000000000, -9000000000000], [2520000000000,
      9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2520000000000, 9000000000000],
      [2520000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2520000000000,
      9000000000000], [3900000000000, -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next
      ([2625000000000], [4464000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([105000000000,
      -9000000000000], [4464000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [2520000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-669000000000],
      [2625000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1944000000000, 9000000000000],
      [7089000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2520000000000, -9000000000000],
      [6420000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2520000000000, -9000000000000],
      [5040000000000, 18000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3900000000000,
      9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4464000000000],
      [7089000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4464000000000], [4569000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (4, 1,
      2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide)
      0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded19_8 : ExcludedOn (model19.B 8 ++ [step19.q]) 9000000000000 (model19.caps 8)
    (model19.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded19_9 : ExcludedOn (model19.B 9 ++ [step19.q]) 9000000000000 (model19.caps 9)
    (model19.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked19 : StepValid model19 9000000000000 step19 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded19_0
    · exact excluded19_1
    · exact excluded19_2
    · exact excluded19_3
    · exact (hj rfl).elim
    · exact excluded19_5
    · exact excluded19_6
    · exact excluded19_7
    · exact excluded19_8
    · exact excluded19_9
theorem next19 : model19.insert step19 = model20 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded20_0 : ExcludedOn (model20.B 0 ++ [step20.q]) 9000000000000 (model20.caps 0)
    (model20.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([1635000000000], [90000000000]) (some (8, 11, 5))
      (some (8, 11, 5)) (.next ([6300000000000], [450000000000]) (some (8, 11, 5)) (some (8, 11, 5))
      (.next ([5880000000000], [585000000000]) (some (8, 11, 5)) (some (8, 11, 5)) (.next
      ([4875000000000], [510000000000]) (some (8, 11, 5)) (some (8, 11, 5)) (.next ([6105000000000],
      [750000000000]) (some (8, 11, 5)) (some (8, 11, 5)) (.next ([5790000000000], [720000000000])
      (some (8, 11, 5)) (some (8, 11, 5)) (.next ([330000000000], [45000000000]) (some (8, 11, 5))
      (some (8, 11, 5)) (.next ([6015000000000], [885000000000]) (some (8, 11, 5)) (some (8, 11, 5))
      (.next ([5550000000000], [960000000000]) (some (8, 11, 5)) (some (8, 11, 5)) (.next
      ([2865000000000], [510000000000]) (some (8, 11, 5)) (some (8, 11, 5)) (.next ([4500000000000],
      [840000000000]) (some (8, 11, 5)) (some (8, 11, 5)) (.next ([5775000000000], [1125000000000])
      (some (8, 11, 5)) (some (8, 11, 5)) (.next ([1635000000000], [330000000000]) (some (8, 11, 5))
      (some (8, 11, 5)) (.next ([5880000000000], [1335000000000]) (some (8, 11, 5)) (some (8, 11,
      5)) (.next ([5790000000000], [1470000000000]) (some (8, 11, 5)) (some (8, 11, 5))
      fan20Owner0Part3))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6645000000000, 9000000000000], [2355000000000,
      -9000000000000]) (some (2, 4, 1)) (some (3, 4, 1)) (.next ([3900000000000, -9000000000000],
      [2520000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2520000000000,
      9000000000000], [2520000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next
      ([4125000000000], [4875000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2520000000000,
      9000000000000], [3900000000000, -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next
      ([1545000000000], [2580000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([1605000000000,
      -9000000000000], [4875000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [2520000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-2355000000000,
      9000000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2520000000000,
      -9000000000000], [6420000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2520000000000,
      -9000000000000], [5040000000000, 18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4875000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-3900000000000,
      9000000000000], [6420000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2580000000000],
      [4125000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4875000000000], [6480000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (4, 1,
      2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide)
      0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded20_6 : ExcludedOn (model20.B 6 ++ [step20.q]) 9000000000000 (model20.caps 6)
    (model20.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded20_8 : ExcludedOn (model20.B 8 ++ [step20.q]) 9000000000000 (model20.caps 8)
    (model20.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded20_9 : ExcludedOn (model20.B 9 ++ [step20.q]) 9000000000000 (model20.caps 9)
    (model20.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked20 : StepValid model20 9000000000000 step20 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded20_0
    · exact excluded20_1
    · exact excluded20_2
    · exact excluded20_3
    · exact (hj rfl).elim
    · exact excluded20_5
    · exact excluded20_6
    · exact excluded20_7
    · exact excluded20_8
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([1635000000000], [90000000000]) (some (11, 2, 5))
      (some (11, 2, 5)) (.next ([6300000000000], [450000000000]) (some (11, 2, 5)) (some (11, 2, 5))
      (.next ([5880000000000], [585000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next
      ([6105000000000], [750000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([5790000000000],
      [720000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([330000000000], [45000000000])
      (some (11, 2, 5)) (some (11, 2, 5)) (.next ([6015000000000], [885000000000]) (some (11, 2, 5))
      (some (11, 2, 5)) (.next ([5550000000000], [960000000000]) (some (11, 2, 5)) (some (11, 2, 5))
      (.next ([3375000000000], [651000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next
      ([5775000000000], [1125000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next
      ([1635000000000], [330000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([3135000000000],
      [651000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([5880000000000], [1335000000000])
      (some (11, 2, 5)) (some (11, 2, 5)) (.next ([3000000000000], [696000000000]) (some (11, 2, 5))
      (some (11, 2, 5)) (.next ([5790000000000], [1470000000000]) (some (11, 2, 5)) (some (11, 2,
      5)) fan21Owner0Part3))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([4464000000000, 0], [105000000000,
      -9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([4464000000000], [2625000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([3900000000000, -9000000000000], [2520000000000,
      9000000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next ([2520000000000, 9000000000000],
      [2520000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next ([2520000000000,
      9000000000000], [3900000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([1944000000000, -9000000000000], [5145000000000, 9000000000000]) (some (3, 1, 4)) (some (3,
      1, 4)) (.next ([669000000000], [1956000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [2520000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-105000000000,
      9000000000000], [4569000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-2625000000000], [7089000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2520000000000,
      -9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2520000000000,
      -9000000000000], [5040000000000, 18000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-3900000000000, 9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-5145000000000, -9000000000000], [7089000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-1956000000000], [2625000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 6) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded21_6 : ExcludedOn (model21.B 6 ++ [step21.q]) 9000000000000 (model21.caps 6)
    (model21.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded21_8 : ExcludedOn (model21.B 8 ++ [step21.q]) 9000000000000 (model21.caps 8)
    (model21.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded21_9 : ExcludedOn (model21.B 9 ++ [step21.q]) 9000000000000 (model21.caps 9)
    (model21.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked21 : StepValid model21 9000000000000 step21 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded21_0
    · exact excluded21_1
    · exact (hj rfl).elim
    · exact excluded21_3
    · exact excluded21_4
    · exact excluded21_5
    · exact excluded21_6
    · exact excluded21_7
    · exact excluded21_8
    · exact excluded21_9
theorem next21 : model21.insert step21 = model22 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded22_0 : ExcludedOn (model22.B 0 ++ [step22.q]) 9000000000000 (model22.caps 0)
    (model22.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([1635000000000], [90000000000]) (some (11, 2, 5))
      (some (11, 2, 5)) (.next ([6300000000000], [450000000000]) (some (11, 2, 5)) (some (11, 2, 5))
      (.next ([5880000000000], [585000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next
      ([6105000000000], [750000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([5790000000000],
      [720000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([330000000000], [45000000000])
      (some (11, 2, 5)) (some (11, 2, 5)) (.next ([6015000000000], [885000000000]) (some (11, 2, 5))
      (some (11, 2, 5)) (.next ([5550000000000], [960000000000]) (some (11, 2, 5)) (some (11, 2, 5))
      (.next ([3339000000000], [615000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next
      ([5775000000000], [1125000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next
      ([3099000000000], [615000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([1635000000000],
      [330000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([2964000000000], [660000000000])
      (some (11, 2, 5)) (some (11, 2, 5)) (.next ([5880000000000], [1335000000000]) (some (11, 2,
      5)) (some (11, 2, 5)) (.next ([5790000000000], [1470000000000]) (some (11, 2, 5)) (some (11,
      2, 5)) fan22Owner0Part3))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

private theorem excluded22_3CheckLeft :
    ExclusionHint.check
      (model22.B 3 ++ [step22.q])
      9000000000000
      (model22.caps 3)
      (model22.ord 3)
      12
      (.witnessedFan (.next ([4536000000000, 0],
      [69000000000, -9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([4536000000000],
      [2589000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next ([3900000000000, -9000000000000],
      [2520000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next ([2520000000000,
      9000000000000], [2520000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next
      ([2520000000000, 9000000000000], [3900000000000, -9000000000000]) (some (3, 1, 4)) (some (3,
      1, 4)) (.next ([2016000000000, -9000000000000], [5109000000000, 9000000000000]) (some (3, 1,
      4)) (some (3, 1, 4)) (.next ([705000000000], [1884000000000]) (some (3, 1, 4)) (some (3, 1,
      4)) (.next ([0], [2520000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([-69000000000, 9000000000000], [4605000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([-2589000000000], [7125000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [5040000000000, 18000000000000]) (some (0, 1, 2)) (some (0,
      1, 2)) (.next ([-3900000000000, 9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([-5109000000000, -9000000000000], [7125000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([-1884000000000], [2589000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal
      (some (0, 1, 2)) (some (0, 4, 2)) (some (0, 4, 2)))))))))))))))))))
      (0) (23) (3000) = true := by
  certify_fan

private theorem excluded22_3CheckRight :
    ExclusionHint.check
      (model22.B 3 ++ [step22.q])
      9000000000000
      (model22.caps 3)
      (model22.ord 3)
      12
      (.witnessedFan (.next
      ([4536000000000], [2589000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([3900000000000,
      -9000000000000], [2520000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next
      ([2520000000000, 9000000000000], [2520000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 1,
      4)) (.next ([2520000000000, 9000000000000], [3900000000000, -9000000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([705000000000], [1884000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([-69000000000, 9000000000000], [4605000000000, -9000000000000]) (some (3, 1, 4)) (some
      (3, 1, 4)) (.next ([0], [2520000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-2589000000000], [7125000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [5040000000000, 18000000000000]) (some (0, 1, 2)) (some (0,
      1, 2)) (.next ([-3900000000000, 9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([-1884000000000], [2589000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-4605000000000, 9000000000000], [4536000000000]) (some (0, 1, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2)))))))))))))))))
      (23) (30) (3000) = true := by
  certify_fan

private theorem excluded22_3Check :
    ExclusionHint.check
      (model22.B 3 ++ [step22.q])
      9000000000000
      (model22.caps 3)
      (model22.ord 3)
      12
      (.split (0) (23) (30) (3000) (.witnessedFan (.next ([4536000000000, 0],
      [69000000000, -9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([4536000000000],
      [2589000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next ([3900000000000, -9000000000000],
      [2520000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next ([2520000000000,
      9000000000000], [2520000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next
      ([2520000000000, 9000000000000], [3900000000000, -9000000000000]) (some (3, 1, 4)) (some (3,
      1, 4)) (.next ([2016000000000, -9000000000000], [5109000000000, 9000000000000]) (some (3, 1,
      4)) (some (3, 1, 4)) (.next ([705000000000], [1884000000000]) (some (3, 1, 4)) (some (3, 1,
      4)) (.next ([0], [2520000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([-69000000000, 9000000000000], [4605000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([-2589000000000], [7125000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [5040000000000, 18000000000000]) (some (0, 1, 2)) (some (0,
      1, 2)) (.next ([-3900000000000, 9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([-5109000000000, -9000000000000], [7125000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([-1884000000000], [2589000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal
      (some (0, 1, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (.witnessedFan (.next
      ([4536000000000], [2589000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([3900000000000,
      -9000000000000], [2520000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next
      ([2520000000000, 9000000000000], [2520000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 1,
      4)) (.next ([2520000000000, 9000000000000], [3900000000000, -9000000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([705000000000], [1884000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([-69000000000, 9000000000000], [4605000000000, -9000000000000]) (some (3, 1, 4)) (some
      (3, 1, 4)) (.next ([0], [2520000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-2589000000000], [7125000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [5040000000000, 18000000000000]) (some (0, 1, 2)) (some (0,
      1, 2)) (.next ([-3900000000000, 9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([-1884000000000], [2589000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-4605000000000, 9000000000000], [4536000000000]) (some (0, 1, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))
      0 1 100 = true := by
  as_aux_lemma =>
    exact split_check_of_checks (by decide) (by decide) (by decide)
      excluded22_3CheckLeft excluded22_3CheckRight

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.split (0) (23) (30) (3000) (.witnessedFan (.next ([4536000000000, 0],
      [69000000000, -9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([4536000000000],
      [2589000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next ([3900000000000, -9000000000000],
      [2520000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next ([2520000000000,
      9000000000000], [2520000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next
      ([2520000000000, 9000000000000], [3900000000000, -9000000000000]) (some (3, 1, 4)) (some (3,
      1, 4)) (.next ([2016000000000, -9000000000000], [5109000000000, 9000000000000]) (some (3, 1,
      4)) (some (3, 1, 4)) (.next ([705000000000], [1884000000000]) (some (3, 1, 4)) (some (3, 1,
      4)) (.next ([0], [2520000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([-69000000000, 9000000000000], [4605000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([-2589000000000], [7125000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [5040000000000, 18000000000000]) (some (0, 1, 2)) (some (0,
      1, 2)) (.next ([-3900000000000, 9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([-5109000000000, -9000000000000], [7125000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([-1884000000000], [2589000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal
      (some (0, 1, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (.witnessedFan (.next
      ([4536000000000], [2589000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([3900000000000,
      -9000000000000], [2520000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next
      ([2520000000000, 9000000000000], [2520000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 1,
      4)) (.next ([2520000000000, 9000000000000], [3900000000000, -9000000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([705000000000], [1884000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([-69000000000, 9000000000000], [4605000000000, -9000000000000]) (some (3, 1, 4)) (some
      (3, 1, 4)) (.next ([0], [2520000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-2589000000000], [7125000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2520000000000, -9000000000000], [5040000000000, 18000000000000]) (some (0, 1, 2)) (some (0,
      1, 2)) (.next ([-3900000000000, 9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([-1884000000000], [2589000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-4605000000000, 9000000000000], [4536000000000]) (some (0, 1, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2)))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact excluded22_3Check

theorem excluded22_4 : ExcludedOn (model22.B 4 ++ [step22.q]) 9000000000000 (model22.caps 4)
    (model22.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 6) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded22_9 : ExcludedOn (model22.B 9 ++ [step22.q]) 9000000000000 (model22.caps 9)
    (model22.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked22 : StepValid model22 9000000000000 step22 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded22_0
    · exact excluded22_1
    · exact (hj rfl).elim
    · exact excluded22_3
    · exact excluded22_4
    · exact excluded22_5
    · exact excluded22_6
    · exact excluded22_7
    · exact excluded22_8
    · exact excluded22_9
theorem next22 : model22.insert step22 = model23 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded23_0 : ExcludedOn (model23.B 0 ++ [step23.q]) 9000000000000 (model23.caps 0)
    (model23.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([1635000000000], [90000000000]) (some (11, 2, 5))
      (some (11, 2, 5)) (.next ([3726000000000], [228000000000]) (some (11, 2, 5)) (some (11, 2, 5))
      (.next ([3486000000000], [228000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next
      ([6300000000000], [450000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([3351000000000],
      [273000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([5880000000000], [585000000000])
      (some (11, 2, 5)) (some (11, 2, 5)) (.next ([6105000000000], [750000000000]) (some (11, 2, 5))
      (some (11, 2, 5)) (.next ([5790000000000], [720000000000]) (some (11, 2, 5)) (some (11, 2, 5))
      (.next ([330000000000], [45000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next
      ([6015000000000], [885000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([4191000000000],
      [648000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([5550000000000], [960000000000])
      (some (11, 2, 5)) (some (11, 2, 5)) (.next ([4236000000000], [738000000000]) (some (11, 2, 5))
      (some (11, 2, 5)) (.next ([5775000000000], [1125000000000]) (some (11, 2, 5)) (some (11, 2,
      5)) (.next ([1635000000000], [330000000000]) (some (11, 2, 5)) (some (11, 2, 5))
      fan23Owner0Part3))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([4536000000000, 0], [456000000000,
      -9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([4536000000000], [2976000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([2520000000000, 9000000000000], [2520000000000,
      9000000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next ([2520000000000, 9000000000000],
      [3900000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([1092000000000],
      [1884000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2016000000000, -9000000000000],
      [5496000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0], [2520000000000,
      9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-456000000000, 9000000000000],
      [4992000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2976000000000],
      [7512000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2520000000000, -9000000000000],
      [5040000000000, 18000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3900000000000,
      9000000000000], [6420000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1884000000000],
      [2976000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5496000000000, -9000000000000],
      [7512000000000]) (some (0, 1, 2)) (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 4,
      2)) (some (0, 4, 2))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0
      1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 6) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded23_6 : ExcludedOn (model23.B 6 ++ [step23.q]) 9000000000000 (model23.caps 6)
    (model23.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded23_8 : ExcludedOn (model23.B 8 ++ [step23.q]) 9000000000000 (model23.caps 8)
    (model23.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded23_9 : ExcludedOn (model23.B 9 ++ [step23.q]) 9000000000000 (model23.caps 9)
    (model23.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked23 : StepValid model23 9000000000000 step23 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded23_0
    · exact excluded23_1
    · exact (hj rfl).elim
    · exact excluded23_3
    · exact excluded23_4
    · exact excluded23_5
    · exact excluded23_6
    · exact excluded23_7
    · exact excluded23_8
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

end Sext280000290000
end ConwaySoifer.Simplified.Certificates
