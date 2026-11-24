/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

import LeanPool.ConwaySoifer.Certificates.FanCertificate

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown140000150000
public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1400001500002

/-!
# Aown 140000 150000 2

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Aown140000150000.model0

-- Generated checkpoints are proposals; all acceptance proofs are checked by the kernel.

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Aown140000150000

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7590000000000, 9000000000000], [990000000000,
      -9000000000000]) none none (.next ([5070000000000, -9000000000000], [2250000000000, 0]) none
      none (.next ([1260000000000, 9000000000000], [1260000000000, 9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1260000000000, 9000000000000], [3405000000000, -9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1665000000000], [6915000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([0], [5925000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([-990000000000, 9000000000000], [8580000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-2250000000000, 0], [7320000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([-1260000000000, -9000000000000], [2520000000000, 18000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-3405000000000, 9000000000000], [4665000000000, 0]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-6915000000000], [8580000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.terminal (some (3, 1, 2)) none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7875000000000, 0], [840000000000,
      9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7560000000000, 0], [885000000000,
      9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7740000000000, -9000000000000],
      [1260000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([2250000000000],
      [420000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([5205000000000], [1830000000000])
      (some (0, 5, 1)) (some (0, 5, 1)) (.next ([4890000000000], [1875000000000]) (some (0, 1, 1))
      (some (0, 1, 1)) (.next ([5070000000000, -9000000000000], [2250000000000, 0]) (some (0, 1, 1))
      (some (0, 1, 1)) (.next ([285000000000, -9000000000000], [135000000000, 9000000000000]) (some
      (0, 1, 1)) (some (0, 1, 1)) (.next ([990000000000, -9000000000000], [1680000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) fan16Owner2Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([1260000000000, 9000000000000], [1260000000000,
      9000000000000]) (some (1, 0, 3)) (some (2, 0, 3)) (.next ([2670000000000, 0], [5490000000000,
      -9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([2670000000000], [6750000000000])
      (some (2, 0, 3)) (some (2, 0, 3)) (.next ([1410000000000, -9000000000000], [8010000000000,
      9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([0], [1260000000000, 9000000000000])
      (some (2, 0, 3)) (some (2, 3, 3)) (.next ([-1260000000000, -9000000000000], [2520000000000,
      18000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-5490000000000, 9000000000000],
      [8160000000000, -9000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-6750000000000],
      [9420000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-8010000000000, -9000000000000],
      [9420000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal (some (0, 3, 1)) (some (0, 3,
      1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 2 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded16_8 : ExcludedOn (model16.B 8 ++ [step16.q]) 9000000000000 (model16.caps 8)
    (model16.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded16_9 : ExcludedOn (model16.B 9 ++ [step16.q]) 9000000000000 (model16.caps 9)
    (model16.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
    · exact (hj rfl).elim
    · exact excluded16_1
    · exact excluded16_2
    · exact excluded16_3
    · exact excluded16_4
    · exact excluded16_5
    · exact excluded16_6
    · exact excluded16_7
    · exact excluded16_8
    · exact excluded16_9
theorem next16 : model16.insert step16 = model17 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([5955000000000, 9000000000000], [420000000000,
      -9000000000000]) none none (.next ([3435000000000, -9000000000000], [1680000000000, 0]) none
      none (.next ([1260000000000, 9000000000000], [1260000000000, 9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1260000000000, 9000000000000], [3405000000000, -9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([30000000000], [6345000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([0], [5925000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([-420000000000, 9000000000000], [6375000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-1680000000000, 0], [5115000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([-1260000000000, -9000000000000], [2520000000000, 18000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-3405000000000, 9000000000000], [4665000000000, 0]) (some (3, 1,
      2)) none (.next ([-6345000000000], [6375000000000]) none none (.terminal none none
      none))))))))))))) (den := 9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

private theorem excluded17_2CheckLeft :
    ExclusionHint.check
      (model17.B 2 ++ [step17.q])
      9000000000000
      (model17.caps 2)
      (model17.ord 2)
      12
      (.witnessedFan (.next ([7875000000000,
      0], [840000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7560000000000,
      0], [885000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7740000000000,
      -9000000000000], [1260000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next
      ([3570000000000], [1260000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([3255000000000],
      [1305000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([2895000000000, 0], [1260000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([3435000000000, -9000000000000],
      [1680000000000, 0]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([1680000000000],
      [2625000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([180000000000, -9000000000000],
      [375000000000, 0]) (some (0, 1, 1)) (some (0, 1, 1)) fan17Owner2Part0))))))))))
      (0) (105) (16600) = true := by
  certify_fan

private theorem excluded17_2CheckRight :
    ExclusionHint.check
      (model17.B 2 ++ [step17.q])
      9000000000000
      (model17.caps 2)
      (model17.ord 2)
      12
      (.witnessedFan
      (.next ([7875000000000, 0], [840000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1))
      (.next ([7560000000000, 0], [885000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1))
      (.next ([7740000000000, -9000000000000], [1260000000000, 9000000000000]) (some (0, 5, 1))
      (some (0, 5, 1)) (.next ([3570000000000], [1260000000000]) (some (0, 5, 1)) (some (0, 5, 1))
      (.next ([3255000000000], [1305000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next
      ([2895000000000, 0], [1260000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next
      ([3435000000000, -9000000000000], [1680000000000, 0]) (some (0, 1, 1)) (some (0, 1, 1)) (.next
      ([285000000000, -9000000000000], [135000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1,
      1)) (.next ([1680000000000], [2625000000000]) (some (0, 1, 1)) (some (0, 1, 1))
      fan17Owner2Part1))))))))))
      (105) (166) (16600) = true := by
  certify_fan

private theorem excluded17_2Check :
    ExclusionHint.check
      (model17.B 2 ++ [step17.q])
      9000000000000
      (model17.caps 2)
      (model17.ord 2)
      12
      (.split (0) (105) (166) (16600) (.witnessedFan (.next ([7875000000000,
      0], [840000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7560000000000,
      0], [885000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7740000000000,
      -9000000000000], [1260000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next
      ([3570000000000], [1260000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([3255000000000],
      [1305000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([2895000000000, 0], [1260000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([3435000000000, -9000000000000],
      [1680000000000, 0]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([1680000000000],
      [2625000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([180000000000, -9000000000000],
      [375000000000, 0]) (some (0, 1, 1)) (some (0, 1, 1)) fan17Owner2Part0)))))))))) (.witnessedFan
      (.next ([7875000000000, 0], [840000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1))
      (.next ([7560000000000, 0], [885000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1))
      (.next ([7740000000000, -9000000000000], [1260000000000, 9000000000000]) (some (0, 5, 1))
      (some (0, 5, 1)) (.next ([3570000000000], [1260000000000]) (some (0, 5, 1)) (some (0, 5, 1))
      (.next ([3255000000000], [1305000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next
      ([2895000000000, 0], [1260000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next
      ([3435000000000, -9000000000000], [1680000000000, 0]) (some (0, 1, 1)) (some (0, 1, 1)) (.next
      ([285000000000, -9000000000000], [135000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1,
      1)) (.next ([1680000000000], [2625000000000]) (some (0, 1, 1)) (some (0, 1, 1))
      fan17Owner2Part1)))))))))))
      0 1 100 = true := by
  as_aux_lemma =>
    exact split_check_of_checks (by decide) (by decide) (by decide)
      excluded17_2CheckLeft excluded17_2CheckRight

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.split (0) (105) (166) (16600) (.witnessedFan (.next ([7875000000000,
      0], [840000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7560000000000,
      0], [885000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7740000000000,
      -9000000000000], [1260000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next
      ([3570000000000], [1260000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([3255000000000],
      [1305000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([2895000000000, 0], [1260000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([3435000000000, -9000000000000],
      [1680000000000, 0]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([1680000000000],
      [2625000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([180000000000, -9000000000000],
      [375000000000, 0]) (some (0, 1, 1)) (some (0, 1, 1)) fan17Owner2Part0)))))))))) (.witnessedFan
      (.next ([7875000000000, 0], [840000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1))
      (.next ([7560000000000, 0], [885000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1))
      (.next ([7740000000000, -9000000000000], [1260000000000, 9000000000000]) (some (0, 5, 1))
      (some (0, 5, 1)) (.next ([3570000000000], [1260000000000]) (some (0, 5, 1)) (some (0, 5, 1))
      (.next ([3255000000000], [1305000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next
      ([2895000000000, 0], [1260000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next
      ([3435000000000, -9000000000000], [1680000000000, 0]) (some (0, 1, 1)) (some (0, 1, 1)) (.next
      ([285000000000, -9000000000000], [135000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1,
      1)) (.next ([1680000000000], [2625000000000]) (some (0, 1, 1)) (some (0, 1, 1))
      fan17Owner2Part1))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact excluded17_2Check

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded17_4 : ExcludedOn (model17.B 4 ++ [step17.q]) 9000000000000 (model17.caps 4)
    (model17.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 2 4) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
    · exact (hj rfl).elim
    · exact excluded17_1
    · exact excluded17_2
    · exact excluded17_3
    · exact excluded17_4
    · exact excluded17_5
    · exact excluded17_6
    · exact excluded17_7
    · exact excluded17_8
    · exact excluded17_9
theorem next17 : model17.insert step17 = model18 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([3330000000000, 9000000000000], [420000000000,
      -9000000000000]) none none (.next ([3750000000000], [2595000000000]) none none (.next
      ([1260000000000, 9000000000000], [1260000000000, 9000000000000]) none none (.next
      ([810000000000, -9000000000000], [1680000000000, 0]) none none (.next ([1260000000000,
      9000000000000], [3405000000000, -9000000000000]) none none (.next ([0], [5925000000000,
      9000000000000]) none none (.next ([-420000000000, 9000000000000], [3750000000000]) (some (3,
      1, 2)) (some (3, 1, 2)) (.next ([-2595000000000], [6345000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-1260000000000, -9000000000000], [2520000000000, 18000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-1680000000000, 0], [2490000000000, -9000000000000]) (some (3,
      1, 2)) none (.next ([-3405000000000, 9000000000000], [4665000000000, 0]) none none (.terminal
      none none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7875000000000, 0], [840000000000,
      9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7560000000000, 0], [885000000000,
      9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7740000000000, -9000000000000],
      [1260000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([2895000000000, 0],
      [1260000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([285000000000,
      -9000000000000], [135000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1))
      fan18Owner2Part0)))))) (den := 9000000000000)
      (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded18_6 : ExcludedOn (model18.B 6 ++ [step18.q]) 9000000000000 (model18.caps 6)
    (model18.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded18_7 : ExcludedOn (model18.B 7 ++ [step18.q]) 9000000000000 (model18.caps 7)
    (model18.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 4) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
    · exact (hj rfl).elim
    · exact excluded18_1
    · exact excluded18_2
    · exact excluded18_3
    · exact excluded18_4
    · exact excluded18_5
    · exact excluded18_6
    · exact excluded18_7
    · exact excluded18_8
    · exact excluded18_9
theorem next18 : model18.insert step18 = model19 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([1740000000000, -9000000000000], [0,
      9000000000000]) none none (.next ([2520000000000, 9000000000000], [480000000000,
      -9000000000000]) none none (.next ([1260000000000, 9000000000000], [1260000000000,
      9000000000000]) none none (.next ([3000000000000], [3405000000000]) none none (.next
      ([1260000000000, 9000000000000], [3405000000000, -9000000000000]) none none (.next ([0],
      [5925000000000, 9000000000000]) none none (.next ([0, -9000000000000], [1740000000000, 0])
      none none (.next ([-480000000000, 9000000000000], [3000000000000]) none none (.next
      ([-1260000000000, -9000000000000], [2520000000000, 18000000000000]) (some (3, 1, 2)) none
      (.next ([-3405000000000], [6405000000000]) none none (.next ([-3405000000000, 9000000000000],
      [4665000000000, 0]) none none (.terminal none none none))))))))))))) (den := 9000000000000)
      (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([1740000000000, -9000000000000], [0,
      9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7875000000000, 0], [840000000000,
      9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7560000000000, 0], [885000000000,
      9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([1185000000000], [180000000000])
      (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7740000000000, -9000000000000], [1260000000000,
      9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([2895000000000, 0], [1260000000000,
      9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([285000000000, -9000000000000],
      [135000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) fan19Owner2Part0))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 2 4) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
    · exact (hj rfl).elim
    · exact excluded19_1
    · exact excluded19_2
    · exact excluded19_3
    · exact excluded19_4
    · exact excluded19_5
    · exact excluded19_6
    · exact excluded19_7
    · exact excluded19_8
    · exact excluded19_9
theorem next19 : model19.insert step19 = model20 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([1680000000000, 9000000000000], [570000000000,
      -9000000000000]) none none (.next ([990000000000, -9000000000000], [840000000000,
      9000000000000]) none none (.next ([2250000000000], [4245000000000]) none none (.next
      ([1260000000000, 9000000000000], [3405000000000, -9000000000000]) none none (.next ([0],
      [5925000000000, 9000000000000]) none none (.next ([-570000000000, 9000000000000],
      [2250000000000]) none none (.next ([-840000000000, -9000000000000], [1830000000000, 0]) none
      none (.next ([-4245000000000], [6495000000000]) none none (.next ([-3405000000000,
      9000000000000], [4665000000000, 0]) none none (.terminal none none none))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7875000000000, 0], [840000000000,
      9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7560000000000, 0], [885000000000,
      9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7740000000000, -9000000000000],
      [1260000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([2895000000000, 0],
      [1260000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([285000000000,
      -9000000000000], [135000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1))
      fan20Owner2Part0)))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded20_6 : ExcludedOn (model20.B 6 ++ [step20.q]) 9000000000000 (model20.caps 6)
    (model20.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([8430000000000, 9000000000000], [990000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([7170000000000], [2250000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([4560000000000], [2250000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([1260000000000, 9000000000000], [2610000000000]) (some (3, 0, 2))
      (some (3, 0, 3)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (3, 0, 3)) (some (3, 0,
      3)) (.next ([-990000000000, 9000000000000], [9420000000000]) (some (3, 0, 3)) (some (3, 1, 3))
      (.next ([-2250000000000], [9420000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2250000000000], [6810000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2610000000000,
      0], [3870000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 4) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
    · exact (hj rfl).elim
    · exact excluded20_1
    · exact excluded20_2
    · exact excluded20_3
    · exact excluded20_4
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
  refine exclude_checkpoint (.witnessedFan (.next ([7500000000000], [90000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([5910000000000], [420000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      (.next ([6750000000000], [510000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
      ([1080000000000], [90000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([5070000000000],
      [510000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([7170000000000], [750000000000])
      (some (8, 1, 4)) (some (8, 1, 4)) (.next ([6750000000000], [840000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([4260000000000], [570000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      (.next ([6750000000000], [930000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
      ([6420000000000], [1170000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([6330000000000],
      [1170000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([5820000000000], [1350000000000])
      (some (8, 1, 4)) (some (8, 1, 4)) (.next ([1350000000000], [330000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([6420000000000], [1590000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      (.next ([6000000000000], [1650000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
      ([6000000000000], [1740000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([1260000000000],
      [420000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([1635000000000], [570000000000])
      (some (8, 1, 4)) (some (8, 1, 4)) (.next ([5670000000000], [2010000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([5580000000000], [2010000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      (.next ([5670000000000], [2400000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      fan21Owner0Part2))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded21_2 : ExcludedOn (model21.B 2 ++ [step21.q]) 9000000000000 (model21.caps 2)
    (model21.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7740000000000, -9000000000000], [330000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([1260000000000, 9000000000000],
      [1260000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([2190000000000,
      9000000000000], [6810000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next
      ([930000000000], [8070000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [1260000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-330000000000,
      -9000000000000], [8070000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-1260000000000,
      -9000000000000], [2520000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-6810000000000, 9000000000000], [9000000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-8070000000000], [9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
    · exact excluded21_2
    · exact excluded21_3
    · exact excluded21_4
    · exact excluded21_5
    · exact (hj rfl).elim
    · exact excluded21_7
    · exact excluded21_8
    · exact excluded21_9
theorem next21 : model21.insert step21 = model22 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded22_0 : ExcludedOn (model22.B 0 ++ [step22.q]) 9000000000000 (model22.caps 0)
    (model22.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7500000000000], [90000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([5910000000000], [420000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      (.next ([1080000000000], [90000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
      ([5070000000000], [510000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([7170000000000],
      [750000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([6750000000000], [840000000000])
      (some (8, 1, 4)) (some (8, 1, 4)) (.next ([4260000000000], [570000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([6750000000000], [930000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      (.next ([6420000000000], [1170000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
      ([6330000000000], [1170000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([6420000000000],
      [1590000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([6000000000000], [1650000000000])
      (some (8, 1, 4)) (some (8, 1, 4)) (.next ([6000000000000], [1740000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([1635000000000], [570000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      (.next ([5670000000000], [2010000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
      ([5580000000000], [2010000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([5670000000000],
      [2400000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([4920000000000], [2820000000000])
      (some (8, 1, 4)) (some (8, 1, 4)) (.next ([4830000000000], [2820000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([3570000000000], [2385000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      (.next ([420000000000], [330000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      fan22Owner0Part2))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([2730000000000, -9000000000000], [2520000000000,
      9000000000000]) (some (2, 3, 1)) (some (2, 3, 2)) (.next ([1260000000000, 9000000000000],
      [1260000000000, 9000000000000]) (some (2, 3, 2)) (some (2, 3, 2)) (.next ([3990000000000],
      [5925000000000]) (some (2, 3, 2)) none (.next ([1260000000000, 9000000000000], [3405000000000,
      -9000000000000]) none none (.next ([0, 9000000000000], [3990000000000, -9000000000000]) (some
      (3, 3, 2)) (some (3, 3, 2)) (.next ([0], [5925000000000, 9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-2520000000000, -9000000000000], [5250000000000, 0]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-1260000000000, -9000000000000], [2520000000000,
      18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-5925000000000], [9915000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3405000000000, 9000000000000], [4665000000000, 0])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3990000000000, 9000000000000], [3990000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1, 2)) (some (3, 1,
      2))))))))))))))) (den := 9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded22_2 : ExcludedOn (model22.B 2 ++ [step22.q]) 9000000000000 (model22.caps 2)
    (model22.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7875000000000, 0], [840000000000,
      9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7560000000000, 0], [885000000000,
      9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([7740000000000, -9000000000000],
      [1260000000000, 9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([5250000000000],
      [2115000000000]) (some (0, 5, 1)) (some (0, 5, 1)) (.next ([2895000000000, 0], [1260000000000,
      9000000000000]) (some (0, 5, 1)) (some (0, 5, 1)) fan22Owner2Part0))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded22_4 : ExcludedOn (model22.B 4 ++ [step22.q]) 9000000000000 (model22.caps 4)
    (model22.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
    · exact excluded22_2
    · exact excluded22_3
    · exact excluded22_4
    · exact excluded22_5
    · exact (hj rfl).elim
    · exact excluded22_7
    · exact excluded22_8
    · exact excluded22_9
theorem next22 : model22.insert step22 = model23 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded23_0 : ExcludedOn (model23.B 0 ++ [step23.q]) 9000000000000 (model23.caps 0)
    (model23.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7500000000000], [90000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([5910000000000], [420000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      (.next ([1080000000000], [90000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
      ([5070000000000], [510000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([7170000000000],
      [750000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([6750000000000], [840000000000])
      (some (8, 1, 4)) (some (8, 1, 4)) (.next ([4260000000000], [570000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([6750000000000], [930000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      (.next ([2325000000000], [375000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
      ([6420000000000], [1170000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([6330000000000],
      [1170000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([6420000000000], [1590000000000])
      (some (8, 1, 4)) (some (8, 1, 4)) (.next ([6000000000000], [1650000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([6000000000000], [1740000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      (.next ([1635000000000], [570000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
      ([5670000000000], [2010000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([5580000000000],
      [2010000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([5670000000000], [2400000000000])
      (some (8, 1, 4)) (some (8, 1, 4)) (.next ([2385000000000], [1125000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([4920000000000], [2820000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      (.next ([4830000000000], [2820000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      fan23Owner0Part2))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([2625000000000], [180000000000, -9000000000000])
      none none (.next ([1260000000000, 9000000000000], [1260000000000, 9000000000000]) none none
      (.next ([1365000000000, -9000000000000], [2700000000000, 9000000000000]) none none (.next
      ([2625000000000], [6105000000000]) none none (.next ([1260000000000, 9000000000000],
      [3405000000000, -9000000000000]) none none (.next ([0], [5925000000000, 9000000000000]) none
      none (.next ([-180000000000, 9000000000000], [2805000000000, -9000000000000]) none none (.next
      ([-1260000000000, -9000000000000], [2520000000000, 18000000000000]) none none (.next
      ([-2700000000000, -9000000000000], [4065000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-6105000000000], [8730000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3405000000000, 9000000000000], [4665000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2))
      (.terminal (some (3, 1, 2)) none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
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
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
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
    · exact excluded23_2
    · exact excluded23_3
    · exact excluded23_4
    · exact excluded23_5
    · exact (hj rfl).elim
    · exact excluded23_7
    · exact excluded23_8
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

end Aown140000150000
end ConwaySoifer.Simplified.Certificates
