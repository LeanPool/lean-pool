/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

import LeanPool.ConwaySoifer.Certificates.CheckpointOwnerProofs
import LeanPool.ConwaySoifer.Certificates.FanCertificate

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown160000170000
public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1600001700005

/-!
# Aown 160000 170000 5

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Aown160000170000.model0

-- Generated checkpoints are proposals; all acceptance proofs are checked by the kernel.

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Aown160000170000

theorem excluded40_0 : ExcludedOn (model40.B 0 ++ [step40.q]) 9000000000000 (model40.caps 0)
    (model40.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 5 8) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded40_1 : ExcludedOn (model40.B 1 ++ [step40.q]) 9000000000000 (model40.caps 1)
    (model40.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 7) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded40_4 : ExcludedOn (model40.B 4 ++ [step40.q]) 9000000000000 (model40.caps 4)
    (model40.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([5250000000000], [480000000000]) (some (3, 0, 2))
      (some (3, 1, 2)) (.next ([6375000000000], [915000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([3720000000000], [2010000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([2145000000000], [1650000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1485000000000],
      [1500000000000]) (some (3, 1, 2)) (some (3, 1, 5)) (.next ([3600000000000], [4275000000000])
      (some (3, 1, 5)) (some (3, 1, 5)) (.next ([2070000000000], [5805000000000]) (some (3, 1, 5))
      (some (3, 1, 5)) (.next ([960000000000, 9000000000000], [4290000000000, -9000000000000]) (some
      (3, 1, 5)) (some (3, 1, 5)) (.next ([615000000000], [4320000000000, -9000000000000]) (some (3,
      1, 5)) (some (3, 1, 5)) (.next ([645000000000], [4635000000000]) (some (3, 1, 5)) (some (4, 1,
      5)) (.next ([615000000000], [5760000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0],
      [1530000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([-480000000000], [5730000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-915000000000], [7290000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([-2010000000000], [5730000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([-1650000000000], [3795000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
      ([-1500000000000], [2985000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-4275000000000], [7875000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-5805000000000], [7875000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-4290000000000,
      9000000000000], [5250000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-4320000000000,
      9000000000000], [4935000000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-4635000000000], [5280000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-5760000000000], [6375000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded40_5 : ExcludedOn (model40.B 5 ++ [step40.q]) 9000000000000 (model40.caps 5)
    (model40.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded40_7 : ExcludedOn (model40.B 7 ++ [step40.q]) 9000000000000 (model40.caps 7)
    (model40.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded40_8 : ExcludedOn (model40.B 8 ++ [step40.q]) 9000000000000 (model40.caps 8)
    (model40.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded40_9 : ExcludedOn (model40.B 9 ++ [step40.q]) 9000000000000 (model40.caps 9)
    (model40.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked40 : StepValid model40 9000000000000 step40 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact excluded40_0
    · exact excluded40_1
    · exact excluded40_2
    · exact (hj rfl).elim
    · exact excluded40_4
    · exact excluded40_5
    · exact excluded40_6
    · exact excluded40_7
    · exact excluded40_8
    · exact excluded40_9
theorem next40 : model40.insert step40 = model41 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

theorem excluded41_0 : ExcludedOn (model41.B 0 ++ [step41.q]) 9000000000000 (model41.caps 0)
    (model41.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 5 8) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded41_1 : ExcludedOn (model41.B 1 ++ [step41.q]) 9000000000000 (model41.caps 1)
    (model41.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded41_2 : ExcludedOn (model41.B 2 ++ [step41.q]) 9000000000000 (model41.caps 2)
    (model41.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 7) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded41_3 : ExcludedOn (model41.B 3 ++ [step41.q]) 9000000000000 (model41.caps 3)
    (model41.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded41_4 : ExcludedOn (model41.B 4 ++ [step41.q]) 9000000000000 (model41.caps 4)
    (model41.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 3 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded41_7 : ExcludedOn (model41.B 7 ++ [step41.q]) 9000000000000 (model41.caps 7)
    (model41.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded41_8 : ExcludedOn (model41.B 8 ++ [step41.q]) 9000000000000 (model41.caps 8)
    (model41.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded41_9 : ExcludedOn (model41.B 9 ++ [step41.q]) 9000000000000 (model41.caps 9)
    (model41.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked41 : StepValid model41 9000000000000 step41 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact excluded41_0
    · exact excluded41_1
    · exact excluded41_2
    · exact excluded41_3
    · exact excluded41_4
    · exact (hj rfl).elim
    · exact excluded41_6
    · exact excluded41_7
    · exact excluded41_8
    · exact excluded41_9
theorem next41 : model41.insert step41 = model42 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

-- Verify the shared tails in one proof to bound the kernel working set.
private theorem checkedFan42Owner0Part1Checks :
    (fan42Owner0Part0.check (model42.B 0 ++ [step42.q]) 9000000000000
      (model42.caps 0) 0 1 100 12
      ([-630000000000], [5895000000000]) = true) ∧
    (fan42Owner0Part1.check (model42.B 0 ++ [step42.q]) 9000000000000
      (model42.caps 0) 0 1 100 12
      ([796800000000, 4980000000000], [261600000000, -2490000000000]) = true) := by
  have checkedTail0 :
      fan42Owner0Part0.check (model42.B 0 ++ [step42.q]) 9000000000000
        (model42.caps 0) 0 1 100 12
        ([-630000000000], [5895000000000]) = true := by
    decide +kernel
  have checkedTail1 :
      fan42Owner0Part1.check (model42.B 0 ++ [step42.q]) 9000000000000
        (model42.caps 0) 0 1 100 12
        ([796800000000, 4980000000000], [261600000000, -2490000000000]) = true := by
    delta fan42Owner0Part1
    simp only [FanWitness.check, checkedTail0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  exact ⟨checkedTail0, checkedTail1⟩

private theorem checkedFan42Owner0Part1 :
    fan42Owner0Part1.check (model42.B 0 ++ [step42.q]) 9000000000000
      (model42.caps 0) 0 1 100 12
      ([796800000000, 4980000000000], [261600000000, -2490000000000]) = true := by
  exact checkedFan42Owner0Part1Checks.2

theorem excluded42_0 : ExcludedOn (model42.B 0 ++ [step42.q]) 9000000000000 (model42.caps 0)
    (model42.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([8640000000000], [210000000000]) (some (8, 2, 5))
      (some (8, 2, 5)) (.next ([7050000000000], [360000000000]) (some (8, 2, 5)) (some (8, 2, 5))
      (.next ([4875000000000], [540000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
      ([6788400000000, 2490000000000], [758400000000, 2490000000000]) (some (8, 2, 5)) (some (8, 2,
      5)) (.next ([5265000000000], [630000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
      ([6390000000000], [1020000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([5991600000000,
      -2490000000000], [1156800000000, 4980000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
      ([6938400000000, 2490000000000], [1663200000000, -4980000000000]) (some (8, 2, 5)) (some (8,
      2, 5)) (.next ([7200000000000], [1800000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
      ([7336800000000, 4980000000000], [2061600000000, -2490000000000]) (some (8, 2, 5)) (some (8,
      2, 5)) (.next ([796800000000, 4980000000000], [261600000000, -2490000000000]) (some (8, 2, 5))
      (some (8, 2, 5)) fan42Owner0Part1)))))))))))) (den := 9000000000000) (fuel
      := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan42Owner0Part1,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded42_1 : ExcludedOn (model42.B 1 ++ [step42.q]) 9000000000000 (model42.caps 1)
    (model42.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

-- Limit kernel memory by checking this fan tail separately.
private theorem checkedFan42Owner2Part0 :
    fan42Owner2Part0.check (model42.B 2 ++ [step42.q]) 9000000000000
      (model42.caps 2) 0 1 100 12
      ([435000000000], [7125000000000]) = true := by
  decide +kernel

theorem excluded42_2 : ExcludedOn (model42.B 2 ++ [step42.q]) 9000000000000 (model42.caps 2)
    (model42.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6480000000000, 0], [210000000000,
      9000000000000]) (some (0, 7, 3)) (some (7, 7, 4)) (.next ([7875000000000, 0], [480000000000,
      9000000000000]) (some (7, 7, 4)) (some (7, 7, 4)) (.next ([7605000000000, 0], [960000000000,
      9000000000000]) (some (7, 7, 4)) (some (7, 7, 4)) (.next ([7560000000000, 0], [1005000000000,
      9000000000000]) (some (7, 7, 4)) (some (7, 7, 4)) (.next ([6480000000000], [1230000000000])
      (some (7, 7, 4)) (some (7, 7, 4)) (.next ([7875000000000], [1500000000000]) (some (7, 1, 4))
      (some (7, 1, 4)) (.next ([1395000000000], [270000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([5790000000000, 0], [1440000000000, 9000000000000]) (some (7, 1, 4)) (some (7, 2, 4))
      (.next ([7560000000000], [2025000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
      ([7560000000000, -9000000000000], [2460000000000, 0]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
      ([5790000000000], [2460000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([645000000000,
      -9000000000000], [315000000000, 9000000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
      ([1080000000000], [795000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([960000000000],
      [1125000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([540000000000], [690000000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([210000000000], [270000000000]) (some (7, 2, 4))
      (some (7, 2, 4)) (.next ([210000000000], [315000000000]) (some (7, 2, 4)) (some (7, 2, 4))
      (.next ([480000000000], [1335000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
      ([435000000000], [1335000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([1230000000000],
      [5250000000000]) (some (7, 2, 4)) (some (7, 2, 5)) (.next ([960000000000], [6915000000000])
      (some (7, 2, 5)) (some (7, 2, 5)) (.next ([480000000000], [7125000000000]) (some (7, 2, 5))
      (some (7, 2, 5)) (.next ([435000000000], [7125000000000]) (some (7, 2, 5)) (some (7, 2, 5))
      fan42Owner2Part0)))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan42Owner2Part0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded42_4 : ExcludedOn (model42.B 4 ++ [step42.q]) 9000000000000 (model42.caps 4)
    (model42.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded42_5 : ExcludedOn (model42.B 5 ++ [step42.q]) 9000000000000 (model42.caps 5)
    (model42.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded42_6 : ExcludedOn (model42.B 6 ++ [step42.q]) 9000000000000 (model42.caps 6)
    (model42.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded42_7 : ExcludedOn (model42.B 7 ++ [step42.q]) 9000000000000 (model42.caps 7)
    (model42.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded42_8 : ExcludedOn (model42.B 8 ++ [step42.q]) 9000000000000 (model42.caps 8)
    (model42.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded42_9 : ExcludedOn (model42.B 9 ++ [step42.q]) 9000000000000 (model42.caps 9)
    (model42.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked42 : StepValid model42 9000000000000 step42 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact excluded42_0
    · exact excluded42_1
    · exact excluded42_2
    · exact (hj rfl).elim
    · exact excluded42_4
    · exact excluded42_5
    · exact excluded42_6
    · exact excluded42_7
    · exact excluded42_8
    · exact excluded42_9
theorem next42 : model42.insert step42 = model43 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

theorem excluded43_1 : ExcludedOn (model43.B 1 ++ [step43.q]) 9000000000000 (model43.caps 1)
    (model43.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

-- Verify the shared tails in one proof to bound the kernel working set.
private theorem checkedFan43Owner2Part1Checks :
    (fan43Owner2Part0.check (model43.B 2 ++ [step43.q]) 9000000000000
      (model43.caps 2) 0 1 100 12
      ([0, -9000000000000], [3375000000000]) = true) ∧
    (fan43Owner2Part1.check (model43.B 2 ++ [step43.q]) 9000000000000
      (model43.caps 2) 0 1 100 12
      ([7875000000000, 0], [480000000000, 9000000000000]) = true) := by
  have checkedTail0 :
      fan43Owner2Part0.check (model43.B 2 ++ [step43.q]) 9000000000000
        (model43.caps 2) 0 1 100 12
        ([0, -9000000000000], [3375000000000]) = true := by
    decide +kernel
  have checkedTail1 :
      fan43Owner2Part1.check (model43.B 2 ++ [step43.q]) 9000000000000
        (model43.caps 2) 0 1 100 12
        ([7875000000000, 0], [480000000000, 9000000000000]) = true := by
    delta fan43Owner2Part1
    simp only [FanWitness.check, checkedTail0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  exact ⟨checkedTail0, checkedTail1⟩

private theorem checkedFan43Owner2Part1 :
    fan43Owner2Part1.check (model43.B 2 ++ [step43.q]) 9000000000000
      (model43.caps 2) 0 1 100 12
      ([7875000000000, 0], [480000000000, 9000000000000]) = true := by
  exact checkedFan43Owner2Part1Checks.2

theorem excluded43_2 : ExcludedOn (model43.B 2 ++ [step43.q]) 9000000000000 (model43.caps 2)
    (model43.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([3375000000000, -9000000000000], [0,
      9000000000000]) (some (0, 7, 3)) (some (0, 7, 4)) (.next ([6480000000000, 0], [210000000000,
      9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([7875000000000, 0], [480000000000,
      9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) fan43Owner2Part1))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan43Owner2Part1,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

-- Limit kernel memory by checking this fan tail separately.
private theorem checkedFan43Owner3Part0 :
    fan43Owner3Part0.check (model43.B 3 ++ [step43.q]) 9000000000000
      (model43.caps 3) 0 1 100 12
      ([5820000000000], [210000000000]) = true := by
  decide +kernel

theorem excluded43_3 : ExcludedOn (model43.B 3 ++ [step43.q]) 9000000000000 (model43.caps 3)
    (model43.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([5820000000000], [210000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) fan43Owner3Part0)) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0
      1 100
      (by as_aux_lemma => decide) ?_
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan43Owner3Part0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded43_4 : ExcludedOn (model43.B 4 ++ [step43.q]) 9000000000000 (model43.caps 4)
    (model43.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded43_5 : ExcludedOn (model43.B 5 ++ [step43.q]) 9000000000000 (model43.caps 5)
    (model43.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded43_6 : ExcludedOn (model43.B 6 ++ [step43.q]) 9000000000000 (model43.caps 6)
    (model43.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded43_7 : ExcludedOn (model43.B 7 ++ [step43.q]) 9000000000000 (model43.caps 7)
    (model43.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded43_8 : ExcludedOn (model43.B 8 ++ [step43.q]) 9000000000000 (model43.caps 8)
    (model43.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded43_9 : ExcludedOn (model43.B 9 ++ [step43.q]) 9000000000000 (model43.caps 9)
    (model43.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked43 : StepValid model43 9000000000000 step43 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact (hj rfl).elim
    · exact excluded43_1
    · exact excluded43_2
    · exact excluded43_3
    · exact excluded43_4
    · exact excluded43_5
    · exact excluded43_6
    · exact excluded43_7
    · exact excluded43_8
    · exact excluded43_9
theorem next43 : model43.insert step43 = model44 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

theorem excluded44_1 : ExcludedOn (model44.B 1 ++ [step44.q]) 9000000000000 (model44.caps 1)
    (model44.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

-- Verify the shared tails in one proof to bound the kernel working set.
private theorem checkedFan44Owner2Part7Checks :
    (fan44Owner2Part0.check (model44.B 2 ++ [step44.q]) 9000000000000
      (model44.caps 2) 0 4464 2064600 12
      ([-1440000000000, -9000000000000], [9000000000000, 0]) = true) ∧
    (fan44Owner2Part1.check (model44.B 2 ++ [step44.q]) 9000000000000
      (model44.caps 2) 0 4464 2064600 12
      ([6165000000000], [2145000000000]) = true) ∧
    (fan44Owner2Part2.check (model44.B 2 ++ [step44.q]) 9000000000000
      (model44.caps 2) 4464 7533 2064600 12
      ([-45000000000, -9000000000000], [480000000000, 0]) = true) ∧
    (fan44Owner2Part3.check (model44.B 2 ++ [step44.q]) 9000000000000
      (model44.caps 2) 4464 7533 2064600 12
      ([5040000000000], [1395000000000]) = true) ∧
    (fan44Owner2Part4.check (model44.B 2 ++ [step44.q]) 9000000000000
      (model44.caps 2) 7533 10619 2064600 12
      ([-1005000000000, -9000000000000], [8565000000000, 9000000000000]) = true) ∧
    (fan44Owner2Part5.check (model44.B 2 ++ [step44.q]) 9000000000000
      (model44.caps 2) 7533 10619 2064600 12
      ([6165000000000], [2145000000000]) = true) ∧
    (fan44Owner2Part6.check (model44.B 2 ++ [step44.q]) 9000000000000
      (model44.caps 2) 287 558 55800 12
      ([-210000000000, -9000000000000], [6690000000000, 9000000000000]) = true) ∧
    (fan44Owner2Part7.check (model44.B 2 ++ [step44.q]) 9000000000000
      (model44.caps 2) 287 558 55800 12
      ([7605000000000, 0], [960000000000, 9000000000000]) = true) := by
  have checkedTail0 :
      fan44Owner2Part0.check (model44.B 2 ++ [step44.q]) 9000000000000
        (model44.caps 2) 0 4464 2064600 12
        ([-1440000000000, -9000000000000], [9000000000000, 0]) = true := by
    decide +kernel
  have checkedTail1 :
      fan44Owner2Part1.check (model44.B 2 ++ [step44.q]) 9000000000000
        (model44.caps 2) 0 4464 2064600 12
        ([6165000000000], [2145000000000]) = true := by
    delta fan44Owner2Part1
    simp only [FanWitness.check, checkedTail0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail2 :
      fan44Owner2Part2.check (model44.B 2 ++ [step44.q]) 9000000000000
        (model44.caps 2) 4464 7533 2064600 12
        ([-45000000000, -9000000000000], [480000000000, 0]) = true := by
    decide +kernel
  have checkedTail3 :
      fan44Owner2Part3.check (model44.B 2 ++ [step44.q]) 9000000000000
        (model44.caps 2) 4464 7533 2064600 12
        ([5040000000000], [1395000000000]) = true := by
    delta fan44Owner2Part3
    simp only [FanWitness.check, checkedTail2,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail4 :
      fan44Owner2Part4.check (model44.B 2 ++ [step44.q]) 9000000000000
        (model44.caps 2) 7533 10619 2064600 12
        ([-1005000000000, -9000000000000], [8565000000000, 9000000000000]) = true := by
    decide +kernel
  have checkedTail5 :
      fan44Owner2Part5.check (model44.B 2 ++ [step44.q]) 9000000000000
        (model44.caps 2) 7533 10619 2064600 12
        ([6165000000000], [2145000000000]) = true := by
    delta fan44Owner2Part5
    simp only [FanWitness.check, checkedTail4,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail6 :
      fan44Owner2Part6.check (model44.B 2 ++ [step44.q]) 9000000000000
        (model44.caps 2) 287 558 55800 12
        ([-210000000000, -9000000000000], [6690000000000, 9000000000000]) = true := by
    decide +kernel
  have checkedTail7 :
      fan44Owner2Part7.check (model44.B 2 ++ [step44.q]) 9000000000000
        (model44.caps 2) 287 558 55800 12
        ([7605000000000, 0], [960000000000, 9000000000000]) = true := by
    delta fan44Owner2Part7
    simp only [FanWitness.check, checkedTail6,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  exact ⟨checkedTail0, checkedTail1, checkedTail2, checkedTail3, checkedTail4, checkedTail5,
    checkedTail6, checkedTail7⟩

private theorem checkedFan44Owner2Part1 :
    fan44Owner2Part1.check (model44.B 2 ++ [step44.q]) 9000000000000
      (model44.caps 2) 0 4464 2064600 12
      ([6165000000000], [2145000000000]) = true := by
  exact checkedFan44Owner2Part7Checks.2.1

private theorem checkedFan44Owner2Part3 :
    fan44Owner2Part3.check (model44.B 2 ++ [step44.q]) 9000000000000
      (model44.caps 2) 4464 7533 2064600 12
      ([5040000000000], [1395000000000]) = true := by
  exact checkedFan44Owner2Part7Checks.2.2.2.1

private theorem checkedFan44Owner2Part5 :
    fan44Owner2Part5.check (model44.B 2 ++ [step44.q]) 9000000000000
      (model44.caps 2) 7533 10619 2064600 12
      ([6165000000000], [2145000000000]) = true := by
  exact checkedFan44Owner2Part7Checks.2.2.2.2.2.1

private theorem checkedFan44Owner2Part7 :
    fan44Owner2Part7.check (model44.B 2 ++ [step44.q]) 9000000000000
      (model44.caps 2) 287 558 55800 12
      ([7605000000000, 0], [960000000000, 9000000000000]) = true := by
  exact checkedFan44Owner2Part7Checks.2.2.2.2.2.2.2

theorem excluded44_2 : ExcludedOn (model44.B 2 ++ [step44.q]) 9000000000000 (model44.caps 2)
    (model44.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.split (0) (287) (558) (55800) (.split (0) (4464) (10619) (2064600)
      (.witnessedFan (.next ([435000000000, -9000000000000], [0, 9000000000000]) (some (0, 7, 3))
      (some (0, 7, 4)) (.next ([7875000000000, 0], [480000000000, 9000000000000]) (some (0, 7, 4))
      (some (0, 7, 4)) (.next ([7605000000000, 0], [960000000000, 9000000000000]) (some (0, 7, 4))
      (some (0, 7, 4)) (.next ([7560000000000, 0], [1005000000000, 9000000000000]) (some (0, 7, 4))
      (some (0, 7, 4)) (.next ([7560000000000, -9000000000000], [1440000000000, 9000000000000])
      (some (0, 7, 4)) (some (0, 7, 4)) (.next ([1395000000000], [270000000000]) (some (0, 7, 4))
      (some (0, 7, 4)) (.next ([1185000000000, -9000000000000], [255000000000, 9000000000000]) (some
      (0, 7, 4)) (some (0, 7, 4)) (.next ([5790000000000, 0], [1440000000000, 9000000000000]) (some
      (0, 7, 4)) (some (0, 7, 4)) (.next ([6435000000000], [1665000000000]) (some (0, 7, 4)) (some
      (0, 7, 4)) (.next ([5040000000000], [1395000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([6165000000000], [2145000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      fan44Owner2Part1)))))))))))) (.split (4464) (7533) (10619) (2064600) (.witnessedFan (.next
      ([6480000000000, 0], [210000000000, 9000000000000]) (some (0, 7, 3)) (some (0, 7, 4)) (.next
      ([435000000000, -9000000000000], [0, 9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([7605000000000, 0], [960000000000, 9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([7560000000000, 0], [1005000000000, 9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([435000000000, -9000000000000], [45000000000, 9000000000000]) (some (0, 7, 4)) (some (0, 7,
      4)) (.next ([1395000000000], [270000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([7560000000000, -9000000000000], [1440000000000, 9000000000000]) (some (0, 7, 4)) (some (0,
      7, 4)) (.next ([1185000000000, -9000000000000], [255000000000, 9000000000000]) (some (0, 7,
      4)) (some (0, 7, 4)) (.next ([5790000000000, 0], [1440000000000, 9000000000000]) (some (0, 7,
      4)) (some (0, 7, 4)) (.next ([6435000000000], [1665000000000]) (some (0, 7, 4)) (some (0, 7,
      4)) (.next ([5040000000000], [1395000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      fan44Owner2Part3)))))))))))) (.witnessedFan (.next ([6480000000000, 0], [210000000000,
      9000000000000]) (some (0, 7, 3)) (some (0, 7, 4)) (.next ([7875000000000, 0], [480000000000,
      9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([435000000000, -9000000000000], [0,
      9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([7605000000000, 0], [960000000000,
      9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([7560000000000, 0], [1005000000000,
      9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([1395000000000], [270000000000])
      (some (0, 7, 4)) (some (0, 7, 4)) (.next ([7560000000000, -9000000000000], [1440000000000,
      9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([5790000000000, 0], [1440000000000,
      9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([6435000000000], [1665000000000])
      (some (0, 7, 4)) (some (0, 7, 4)) (.next ([5040000000000], [1395000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([6165000000000], [2145000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      fan44Owner2Part5)))))))))))))) (.witnessedFan (.next ([6480000000000, 0], [210000000000,
      9000000000000]) (some (0, 7, 3)) (some (0, 7, 4)) (.next ([7875000000000, 0], [480000000000,
      9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([7605000000000, 0], [960000000000,
      9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) fan44Owner2Part7)))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan44Owner2Part1, checkedFan44Owner2Part3, checkedFan44Owner2Part5,
      checkedFan44Owner2Part7,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

-- Limit kernel memory by checking this fan tail separately.
private theorem checkedFan44Owner3Part0 :
    fan44Owner3Part0.check (model44.B 3 ++ [step44.q]) 9000000000000
      (model44.caps 3) 0 1 100 12
      ([7815000000000], [0, 9000000000000]) = true := by
  decide +kernel

theorem excluded44_3 : ExcludedOn (model44.B 3 ++ [step44.q]) 9000000000000 (model44.caps 3)
    (model44.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7815000000000], [0, 9000000000000]) (some (3, 0,
      5)) (some (4, 0, 5)) fan44Owner3Part0)) (den := 9000000000000) (fuel
      := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan44Owner3Part0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded44_4 : ExcludedOn (model44.B 4 ++ [step44.q]) 9000000000000 (model44.caps 4)
    (model44.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded44_5 : ExcludedOn (model44.B 5 ++ [step44.q]) 9000000000000 (model44.caps 5)
    (model44.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded44_6 : ExcludedOn (model44.B 6 ++ [step44.q]) 9000000000000 (model44.caps 6)
    (model44.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded44_7 : ExcludedOn (model44.B 7 ++ [step44.q]) 9000000000000 (model44.caps 7)
    (model44.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded44_8 : ExcludedOn (model44.B 8 ++ [step44.q]) 9000000000000 (model44.caps 8)
    (model44.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded44_9 : ExcludedOn (model44.B 9 ++ [step44.q]) 9000000000000 (model44.caps 9)
    (model44.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked44 : StepValid model44 9000000000000 step44 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact (hj rfl).elim
    · exact excluded44_1
    · exact excluded44_2
    · exact excluded44_3
    · exact excluded44_4
    · exact excluded44_5
    · exact excluded44_6
    · exact excluded44_7
    · exact excluded44_8
    · exact excluded44_9
theorem next44 : model44.insert step44 = model45 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

-- Verify the shared tails in one proof to bound the kernel working set.
private theorem checkedFan45Owner0Part1Checks :
    (fan45Owner0Part0.check (model45.B 0 ++ [step45.q]) 9000000000000
      (model45.caps 0) 0 1 100 12
      ([-1185000000000], [8895000000000]) = true) ∧
    (fan45Owner0Part1.check (model45.B 0 ++ [step45.q]) 9000000000000
      (model45.caps 0) 0 1 100 12
      ([6390000000000], [1695000000000]) = true) := by
  have checkedTail0 :
      fan45Owner0Part0.check (model45.B 0 ++ [step45.q]) 9000000000000
        (model45.caps 0) 0 1 100 12
        ([-1185000000000], [8895000000000]) = true := by
    decide +kernel
  have checkedTail1 :
      fan45Owner0Part1.check (model45.B 0 ++ [step45.q]) 9000000000000
        (model45.caps 0) 0 1 100 12
        ([6390000000000], [1695000000000]) = true := by
    delta fan45Owner0Part1
    simp only [FanWitness.check, checkedTail0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  exact ⟨checkedTail0, checkedTail1⟩

private theorem checkedFan45Owner0Part1 :
    fan45Owner0Part1.check (model45.B 0 ++ [step45.q]) 9000000000000
      (model45.caps 0) 0 1 100 12
      ([6390000000000], [1695000000000]) = true := by
  exact checkedFan45Owner0Part1Checks.2

theorem excluded45_0 : ExcludedOn (model45.B 0 ++ [step45.q]) 9000000000000 (model45.caps 0)
    (model45.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7050000000000], [360000000000]) (some (8, 9, 6))
      (some (8, 9, 6)) (.next ([7200000000000], [375000000000]) (some (8, 9, 6)) (some (8, 9, 6))
      (.next ([7035000000000], [525000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
      ([7171800000000, 4980000000000], [786600000000, -2490000000000]) (some (8, 9, 6)) (some (8, 9,
      6)) (.next ([6788400000000, 2490000000000], [758400000000, 2490000000000]) (some (8, 9, 6))
      (some (8, 9, 6)) (.next ([4583400000000, 2490000000000], [643200000000, -4980000000000]) (some
      (8, 9, 6)) (some (8, 9, 6)) (.next ([7710000000000], [1185000000000]) (some (8, 9, 6)) (some
      (8, 9, 6)) (.next ([6390000000000], [1020000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
      ([4845000000000], [780000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([7035000000000],
      [1185000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([5991600000000, -2490000000000],
      [1156800000000, 4980000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([3435000000000],
      [705000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([6773400000000, 2490000000000],
      [1583400000000, 2490000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([5520000000000],
      [1440000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([6390000000000], [1695000000000])
      (some (8, 9, 6)) (some (8, 9, 6)) fan45Owner0Part1)))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan45Owner0Part1,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded45_1 : ExcludedOn (model45.B 1 ++ [step45.q]) 9000000000000 (model45.caps 1)
    (model45.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded45_2 : ExcludedOn (model45.B 2 ++ [step45.q]) 9000000000000 (model45.caps 2)
    (model45.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 7) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded45_3 : ExcludedOn (model45.B 3 ++ [step45.q]) 9000000000000 (model45.caps 3)
    (model45.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 3 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

-- Limit kernel memory by checking this fan tail separately.
private theorem checkedFan45Owner4Part0 :
    fan45Owner4Part0.check (model45.B 4 ++ [step45.q]) 9000000000000
      (model45.caps 4) 0 1 100 12
      ([6375000000000], [915000000000]) = true := by
  decide +kernel

theorem excluded45_4 : ExcludedOn (model45.B 4 ++ [step45.q]) 9000000000000 (model45.caps 4)
    (model45.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7470000000000], [195000000000]) (some (3, 0, 5))
      (some (3, 1, 5)) (.next ([5250000000000], [480000000000]) (some (3, 1, 5)) (some (3, 1, 5))
      (.next ([6375000000000], [915000000000]) (some (3, 1, 5)) (some (3, 1, 5))
      fan45Owner4Part0)))) (den := 9000000000000)
      (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan45Owner4Part0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded45_6 : ExcludedOn (model45.B 6 ++ [step45.q]) 9000000000000 (model45.caps 6)
    (model45.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([5190000000000, 9000000000000], [720000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([7665000000000], [1335000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([3750000000000], [2160000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([1755000000000], [5085000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([1980000000000], [7020000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([1440000000000, 9000000000000], [5685000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([225000000000], [1935000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([105000000000,
      9000000000000], [7560000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0,
      0], [1440000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-720000000000,
      9000000000000], [5910000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next ([-1335000000000],
      [9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-2160000000000], [5910000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-5085000000000], [6840000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-7020000000000], [9000000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-5685000000000, 0], [7125000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 4))
      (.next ([-1935000000000], [2160000000000]) (some (4, 2, 4)) (some (4, 2, 4)) (.next
      ([-7560000000000, 9000000000000], [7665000000000]) (some (4, 2, 4)) (some (4, 2, 4))
      (.terminal (some (1, 2, 4)) (some (1, 2, 4)) (some (1, 2, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded45_7 : ExcludedOn (model45.B 7 ++ [step45.q]) 9000000000000 (model45.caps 7)
    (model45.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded45_8 : ExcludedOn (model45.B 8 ++ [step45.q]) 9000000000000 (model45.caps 8)
    (model45.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded45_9 : ExcludedOn (model45.B 9 ++ [step45.q]) 9000000000000 (model45.caps 9)
    (model45.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked45 : StepValid model45 9000000000000 step45 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact excluded45_0
    · exact excluded45_1
    · exact excluded45_2
    · exact excluded45_3
    · exact excluded45_4
    · exact (hj rfl).elim
    · exact excluded45_6
    · exact excluded45_7
    · exact excluded45_8
    · exact excluded45_9
theorem next45 : model45.insert step45 = model46 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

-- Verify the shared tails in one proof to bound the kernel working set.
private theorem checkedFan46Owner0Part1Checks :
    (fan46Owner0Part0.check (model46.B 0 ++ [step46.q]) 9000000000000
      (model46.caps 0) 0 1 100 12
      ([-780000000000], [5625000000000]) = true) ∧
    (fan46Owner0Part1.check (model46.B 0 ++ [step46.q]) 9000000000000
      (model46.caps 0) 0 1 100 12
      ([4583400000000, 2490000000000], [1838400000000, 2490000000000]) = true) := by
  have checkedTail0 :
      fan46Owner0Part0.check (model46.B 0 ++ [step46.q]) 9000000000000
        (model46.caps 0) 0 1 100 12
        ([-780000000000], [5625000000000]) = true := by
    decide +kernel
  have checkedTail1 :
      fan46Owner0Part1.check (model46.B 0 ++ [step46.q]) 9000000000000
        (model46.caps 0) 0 1 100 12
        ([4583400000000, 2490000000000], [1838400000000, 2490000000000]) = true := by
    delta fan46Owner0Part1
    simp only [FanWitness.check, checkedTail0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  exact ⟨checkedTail0, checkedTail1⟩

private theorem checkedFan46Owner0Part1 :
    fan46Owner0Part1.check (model46.B 0 ++ [step46.q]) 9000000000000
      (model46.caps 0) 0 1 100 12
      ([4583400000000, 2490000000000], [1838400000000, 2490000000000]) = true := by
  exact checkedFan46Owner0Part1Checks.2

theorem excluded46_0 : ExcludedOn (model46.B 0 ++ [step46.q]) 9000000000000 (model46.caps 0)
    (model46.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7050000000000], [360000000000]) (some (8, 3, 6))
      (some (8, 3, 6)) (.next ([7200000000000], [375000000000]) (some (8, 3, 6)) (some (8, 3, 6))
      (.next ([7035000000000], [525000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
      ([7171800000000, 4980000000000], [786600000000, -2490000000000]) (some (8, 3, 6)) (some (8, 3,
      6)) (.next ([6788400000000, 2490000000000], [758400000000, 2490000000000]) (some (8, 3, 6))
      (some (8, 3, 6)) (.next ([4583400000000, 2490000000000], [643200000000, -4980000000000]) (some
      (8, 3, 6)) (some (8, 3, 6)) (.next ([6390000000000], [1020000000000]) (some (8, 3, 6)) (some
      (8, 3, 6)) (.next ([4845000000000], [780000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
      ([7035000000000], [1185000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([5991600000000,
      -2490000000000], [1156800000000, 4980000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
      ([3435000000000], [705000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([6773400000000,
      2490000000000], [1583400000000, 2490000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
      ([1673400000000, 2490000000000], [398400000000, 2490000000000]) (some (8, 3, 6)) (some (8, 3,
      6)) (.next ([4845000000000], [1440000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
      ([5115000000000], [1635000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([6375000000000],
      [2460000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([4583400000000, 2490000000000],
      [1838400000000, 2490000000000]) (some (8, 3, 6)) (some (8, 3, 6))
      fan46Owner0Part1)))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan46Owner0Part1,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded46_1 : ExcludedOn (model46.B 1 ++ [step46.q]) 9000000000000 (model46.caps 1)
    (model46.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded46_2 : ExcludedOn (model46.B 2 ++ [step46.q]) 9000000000000 (model46.caps 2)
    (model46.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 7) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded46_3 : ExcludedOn (model46.B 3 ++ [step46.q]) 9000000000000 (model46.caps 3)
    (model46.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded46_4 : ExcludedOn (model46.B 4 ++ [step46.q]) 9000000000000 (model46.caps 4)
    (model46.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

-- Limit kernel memory by checking this fan tail separately.
private theorem checkedFan46Owner5Part0 :
    fan46Owner5Part0.check (model46.B 5 ++ [step46.q]) 9000000000000
      (model46.caps 5) 0 1 100 12
      ([7560000000000, -9000000000000], [165000000000, 9000000000000]) = true := by
  decide +kernel

theorem excluded46_5 : ExcludedOn (model46.B 5 ++ [step46.q]) 9000000000000 (model46.caps 5)
    (model46.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7560000000000, -9000000000000], [165000000000,
      9000000000000]) (some (5, 0, 3)) (some (5, 1, 3)) fan46Owner5Part0)) (den
      := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan46Owner5Part0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded46_7 : ExcludedOn (model46.B 7 ++ [step46.q]) 9000000000000 (model46.caps 7)
    (model46.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded46_8 : ExcludedOn (model46.B 8 ++ [step46.q]) 9000000000000 (model46.caps 8)
    (model46.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded46_9 : ExcludedOn (model46.B 9 ++ [step46.q]) 9000000000000 (model46.caps 9)
    (model46.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked46 : StepValid model46 9000000000000 step46 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact excluded46_0
    · exact excluded46_1
    · exact excluded46_2
    · exact excluded46_3
    · exact excluded46_4
    · exact excluded46_5
    · exact (hj rfl).elim
    · exact excluded46_7
    · exact excluded46_8
    · exact excluded46_9
theorem next46 : model46.insert step46 = model47 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

theorem excluded47_0 : ExcludedOn (model47.B 0 ++ [step47.q]) 9000000000000 (model47.caps 0)
    (model47.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 9) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded47_1 : ExcludedOn (model47.B 1 ++ [step47.q]) 9000000000000 (model47.caps 1)
    (model47.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded47_2 : ExcludedOn (model47.B 2 ++ [step47.q]) 9000000000000 (model47.caps 2)
    (model47.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 7) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded47_3 : ExcludedOn (model47.B 3 ++ [step47.q]) 9000000000000 (model47.caps 3)
    (model47.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded47_4 : ExcludedOn (model47.B 4 ++ [step47.q]) 9000000000000 (model47.caps 4)
    (model47.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded47_6 : ExcludedOn (model47.B 6 ++ [step47.q]) 9000000000000 (model47.caps 6)
    (model47.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([3915000000000], [2850000000000]) (some (0, 4,
      2)) (some (0, 4, 3)) (.next ([4875000000000], [4725000000000]) (some (0, 4, 3)) (some (0, 4,
      3)) (.next ([960000000000, 0], [2475000000000, -9000000000000]) (some (0, 4, 3)) (some (0, 4,
      3)) (.next ([2040000000000], [5685000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1440000000000, 9000000000000], [5685000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([960000000000], [3915000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [7725000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2850000000000], [6765000000000])
      (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-4725000000000], [9600000000000]) (some (0, 2, 3))
      (some (4, 2, 3)) (.next ([-2475000000000, 9000000000000], [3435000000000, -9000000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-5685000000000], [7725000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-5685000000000, 0], [7125000000000, 9000000000000]) (some (4, 2, 0))
      (some (4, 2, 0)) (.next ([-3915000000000], [4875000000000]) (some (4, 2, 0)) (some (4, 2, 0))
      (.terminal (some (4, 2, 0)) (some (4, 2, 0)) (some (4, 2, 0))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded47_7 : ExcludedOn (model47.B 7 ++ [step47.q]) 9000000000000 (model47.caps 7)
    (model47.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded47_8 : ExcludedOn (model47.B 8 ++ [step47.q]) 9000000000000 (model47.caps 8)
    (model47.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded47_9 : ExcludedOn (model47.B 9 ++ [step47.q]) 9000000000000 (model47.caps 9)
    (model47.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([2625000000000], [615000000000]) (some (4, 0, 1))
      (some (4, 1, 2)) (.next ([1185000000000, -9000000000000], [615000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([5085000000000, 0], [3435000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 3)) (.next ([5085000000000], [4875000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([3645000000000, -9000000000000], [4875000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([2460000000000], [4260000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([825000000000, 9000000000000], [1800000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1,
      4)) (.next ([0, 0], [1440000000000, 9000000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next
      ([-615000000000], [3240000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-615000000000],
      [1800000000000, -9000000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-3435000000000,
      9000000000000], [8520000000000, -9000000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next
      ([-4875000000000], [9960000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-4875000000000], [8520000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-4260000000000], [6720000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1800000000000,
      9000000000000], [2625000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal (some (0, 1,
      4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem checked47 : StepValid model47 9000000000000 step47 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact excluded47_0
    · exact excluded47_1
    · exact excluded47_2
    · exact excluded47_3
    · exact excluded47_4
    · exact (hj rfl).elim
    · exact excluded47_6
    · exact excluded47_7
    · exact excluded47_8
    · exact excluded47_9
theorem next47 : model47.insert step47 = model48 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

end Aown160000170000
end ConwaySoifer.Simplified.Certificates
