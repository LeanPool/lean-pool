/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across042500047500
import Mathlib.Tactic.FinCases

/-!
# Across 042500 047500 0

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

-- Generated checkpoints are proposals; all acceptance proofs are checked by the kernel.

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Across042500047500

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan3Owner7Part0 : FanWitness := (.next ([688500000000, 0], [804000000000, -9000000000000]) (some
    (4, 1, 3)) (some (4, 1, 3)) (.next ([191250000000, -9000000000000], [382500000000,
    9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1186500000000], [6551250000000])
    (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1316250000000], [7301250000000]) (some (4, 1, 3))
    (some (4, 1, 3)) (.next ([129750000000], [750000000000]) (some (4, 1, 3)) (some (4, 1, 3))
    (.next ([1316250000000], [7875000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
    ([1186500000000], [7125000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([933750000000,
    -9000000000000], [7875000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([804000000000,
    -9000000000000], [7125000000000]) (some (4, 1, 3)) (some (5, 1, 3)) (.next ([382500000000,
    9000000000000], [8043750000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([382500000000, 9000000000000], [8617500000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([0, 0], [8617500000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([-191250000000, 0], [933750000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([-804000000000, 9000000000000], [1492500000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([-382500000000, -9000000000000], [573750000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([-6551250000000], [7737750000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([-7301250000000], [8617500000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-750000000000],
    [879750000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-7875000000000], [9191250000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-7125000000000], [8311500000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([-7875000000000, 0], [8808750000000, -9000000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([-7125000000000, 0], [7929000000000, -9000000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([-8043750000000, 9000000000000], [8426250000000, 0]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([-8617500000000, 9000000000000], [9000000000000, 0]) (some (5, 1, 3))
    (some (5, 2, 3)) (.terminal (some (5, 2, 3)) (some (5, 2, 3)) (some (5, 2,
    3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan4Owner7Part0 : FanWitness := (.next ([879750000000], [620250000000]) (some (4, 5, 3)) (some
    (4, 5, 3)) (.next ([688500000000, 0], [804000000000, -9000000000000]) (some (4, 5, 3)) (some (4,
    5, 3)) (.next ([191250000000, -9000000000000], [382500000000, 9000000000000]) (some (4, 5, 3))
    (some (4, 5, 3)) (.next ([1186500000000], [6551250000000]) (some (4, 5, 3)) (some (4, 5, 3))
    (.next ([1186500000000], [7125000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([804000000000, -9000000000000], [7125000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([566250000000], [8051250000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([566250000000],
    [8625000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([382500000000, 9000000000000],
    [8043750000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([382500000000,
    9000000000000], [8617500000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([183750000000, -9000000000000], [8625000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0,
    0], [8617500000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-7500000000,
    -9000000000000], [191250000000, 0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-620250000000],
    [1500000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-804000000000, 9000000000000],
    [1492500000000, -9000000000000]) (some (0, 1, 3)) (some (5, 1, 3)) (.next ([-382500000000,
    -9000000000000], [573750000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-6551250000000],
    [7737750000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-7125000000000], [8311500000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-7125000000000, 0], [7929000000000, -9000000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-8051250000000], [8617500000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([-8625000000000], [9191250000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([-8043750000000, 9000000000000], [8426250000000, 0]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([-8617500000000, 9000000000000], [9000000000000, 0]) (some (5, 1, 3)) (some (5, 2, 3))
    (.next ([-8625000000000, 0], [8808750000000, -9000000000000]) (some (5, 2, 3)) (some (5, 2, 3))
    (.terminal (some (5, 2, 3)) (some (5, 2, 3)) (some (5, 2, 3)))))))))))))))))))))))))))

theorem excluded0_0 : ExcludedOn (model0.B 0 ++ [step0.q]) 9000000000000 (model0.caps 0) (model0.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_1 : ExcludedOn (model0.B 1 ++ [step0.q]) 9000000000000 (model0.caps 1) (model0.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([382500000000, 9000000000000], [382500000000,
      9000000000000]) none none (.next ([1071000000000, 9000000000000], [1186500000000]) none none
      (.next ([688500000000, 0], [804000000000, -9000000000000]) none none (.next ([688500000000],
      [1186500000000]) none none (.next ([0, 0], [382500000000, 9000000000000]) none none (.next
      ([-382500000000, -9000000000000], [765000000000, 18000000000000]) none none (.next
      ([-1186500000000], [2257500000000, 9000000000000]) none none (.next ([-804000000000,
      9000000000000], [1492500000000, -9000000000000]) none none (.next ([-1186500000000],
      [1875000000000]) none none (.terminal none none none))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded0_2 : ExcludedOn (model0.B 2 ++ [step0.q]) 9000000000000 (model0.caps 2) (model0.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8617500000000, -9000000000000], [382500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7125000000000], [688500000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([6742500000000, -9000000000000], [688500000000, 0])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7125000000000, 0], [1071000000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([382500000000, 9000000000000], [382500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [4882500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4117500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1186500000000],
      [2625000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([382500000000, 9000000000000],
      [4117500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [382500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-382500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-688500000000], [7813500000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-688500000000,
      0], [7431000000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1071000000000, -9000000000000], [8196000000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-382500000000, -9000000000000], [765000000000, 18000000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([-4882500000000, -9000000000000], [9382500000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8617500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-2625000000000], [3811500000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4117500000000, 9000000000000], [4500000000000, 0])
      (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2, 3)) (some (0, 2, 0)) (some (0, 2,
      3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
  decide +kernel

theorem excluded0_3 : ExcludedOn (model0.B 3 ++ [step0.q]) 9000000000000 (model0.caps 3) (model0.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_4 : ExcludedOn (model0.B 4 ++ [step0.q]) 9000000000000 (model0.caps 4) (model0.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_5 : ExcludedOn (model0.B 5 ++ [step0.q]) 9000000000000 (model0.caps 5) (model0.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_6 : ExcludedOn (model0.B 6 ++ [step0.q]) 9000000000000 (model0.caps 6) (model0.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_8 : ExcludedOn (model0.B 8 ++ [step0.q]) 9000000000000 (model0.caps 8) (model0.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_9 : ExcludedOn (model0.B 9 ++ [step0.q]) 9000000000000 (model0.caps 9) (model0.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked0 : StepValid model0 9000000000000 step0 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded0_0
    · exact excluded0_1
    · exact excluded0_2
    · exact excluded0_3
    · exact excluded0_4
    · exact excluded0_5
    · exact excluded0_6
    · exact (hj rfl).elim
    · exact excluded0_8
    · exact excluded0_9
theorem next0 : model0.insert step0 = model1 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded1_0 : ExcludedOn (model1.B 0 ++ [step1.q]) 9000000000000 (model1.caps 0) (model1.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_2 : ExcludedOn (model1.B 2 ++ [step1.q]) 9000000000000 (model1.caps 2) (model1.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8617500000000, -9000000000000], [382500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([6690000000000], [2310000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([6307500000000, -9000000000000], [2310000000000, 0])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([6690000000000, 0], [2692500000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([382500000000, 9000000000000], [382500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [4882500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4117500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([382500000000, 9000000000000],
      [1927500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([382500000000,
      9000000000000], [4117500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0,
      0], [382500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-382500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-2310000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2310000000000,
      0], [8617500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-2692500000000, -9000000000000], [9382500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-382500000000, -9000000000000], [765000000000, 18000000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([-4882500000000, -9000000000000], [9382500000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8617500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1927500000000, 9000000000000],
      [2310000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4117500000000, 9000000000000],
      [4500000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4, 3)) (some (0, 2,
      0)) (some (0, 4, 3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded1_3 : ExcludedOn (model1.B 3 ++ [step1.q]) 9000000000000 (model1.caps 3) (model1.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_4 : ExcludedOn (model1.B 4 ++ [step1.q]) 9000000000000 (model1.caps 4) (model1.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_5 : ExcludedOn (model1.B 5 ++ [step1.q]) 9000000000000 (model1.caps 5) (model1.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_6 : ExcludedOn (model1.B 6 ++ [step1.q]) 9000000000000 (model1.caps 6) (model1.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_7 : ExcludedOn (model1.B 7 ++ [step1.q]) 9000000000000 (model1.caps 7) (model1.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6307500000000, -9000000000000], [382500000000,
      9000000000000]) (some (3, 1, 2)) (some (4, 1, 3)) (.next ([1186500000000], [435000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([688500000000, 0], [804000000000, -9000000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([382500000000, 9000000000000], [1927500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1186500000000], [6742500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1186500000000], [7125000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([804000000000, -9000000000000], [7125000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([382500000000, 9000000000000], [8235000000000,
      -18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([382500000000, 9000000000000],
      [8617500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [8617500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-382500000000,
      -9000000000000], [6690000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-435000000000],
      [1621500000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-804000000000, 9000000000000],
      [1492500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1927500000000,
      9000000000000], [2310000000000, 0]) (some (0, 1, 3)) (some (1, 1, 3)) (.next ([-6742500000000,
      9000000000000], [7929000000000, -9000000000000]) (some (1, 1, 3)) (some (1, 5, 3)) (.next
      ([-7125000000000], [8311500000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-7125000000000,
      0], [7929000000000, -9000000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next
      ([-8235000000000, 18000000000000], [8617500000000, -9000000000000]) (some (1, 5, 3)) (some (1,
      5, 3)) (.next ([-8617500000000, 9000000000000], [9000000000000, 0]) (some (1, 5, 3)) (some (1,
      5, 3)) (.terminal (some (1, 5, 3)) (some (1, 2, 3)) (some (1, 5, 3))))))))))))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded1_8 : ExcludedOn (model1.B 8 ++ [step1.q]) 9000000000000 (model1.caps 8) (model1.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_9 : ExcludedOn (model1.B 9 ++ [step1.q]) 9000000000000 (model1.caps 9) (model1.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked1 : StepValid model1 9000000000000 step1 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded1_0
    · exact (hj rfl).elim
    · exact excluded1_2
    · exact excluded1_3
    · exact excluded1_4
    · exact excluded1_5
    · exact excluded1_6
    · exact excluded1_7
    · exact excluded1_8
    · exact excluded1_9
theorem next1 : model1.insert step1 = model2 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded2_0 : ExcludedOn (model2.B 0 ++ [step2.q]) 9000000000000 (model2.caps 0) (model2.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded2_1 : ExcludedOn (model2.B 1 ++ [step2.q]) 9000000000000 (model2.caps 1) (model2.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([382500000000, 9000000000000], [382500000000,
      9000000000000]) none none (.next ([382500000000, 9000000000000], [1927500000000,
      -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([382500000000, 9000000000000],
      [8043750000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([0],
      [2692500000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-382500000000,
      -9000000000000], [765000000000, 18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1927500000000, 9000000000000], [2310000000000, 0]) (some (0, 1, 3)) (some (1, 1, 3)) (.next
      ([-8043750000000, 9000000000000], [8426250000000, 0]) (some (1, 1, 3)) (some (1, 1, 3))
      (.terminal (some (1, 1, 3)) none none))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded2_2 : ExcludedOn (model2.B 2 ++ [step2.q]) 9000000000000 (model2.caps 2) (model2.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded2_3 : ExcludedOn (model2.B 3 ++ [step2.q]) 9000000000000 (model2.caps 3) (model2.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded2_4 : ExcludedOn (model2.B 4 ++ [step2.q]) 9000000000000 (model2.caps 4) (model2.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded2_5 : ExcludedOn (model2.B 5 ++ [step2.q]) 9000000000000 (model2.caps 5) (model2.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded2_6 : ExcludedOn (model2.B 6 ++ [step2.q]) 9000000000000 (model2.caps 6) (model2.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded2_8 : ExcludedOn (model2.B 8 ++ [step2.q]) 9000000000000 (model2.caps 8) (model2.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded2_9 : ExcludedOn (model2.B 9 ++ [step2.q]) 9000000000000 (model2.caps 9) (model2.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked2 : StepValid model2 9000000000000 step2 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded2_0
    · exact excluded2_1
    · exact excluded2_2
    · exact excluded2_3
    · exact excluded2_4
    · exact excluded2_5
    · exact excluded2_6
    · exact (hj rfl).elim
    · exact excluded2_8
    · exact excluded2_9
theorem next2 : model2.insert step2 = model3 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded3_1 : ExcludedOn (model3.B 1 ++ [step3.q]) 9000000000000 (model3.caps 1) (model3.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([742500000000, -9000000000000], [191250000000,
      0]) none none (.next ([1316250000000], [1185000000000]) none none (.next ([382500000000,
      9000000000000], [382500000000, 9000000000000]) none none (.next ([382500000000,
      9000000000000], [1927500000000, -9000000000000]) none none (.next ([191250000000,
      9000000000000], [1316250000000]) none none (.next ([0], [2692500000000, 9000000000000]) none
      none (.next ([-191250000000, 0], [933750000000, -9000000000000]) none none (.next
      ([-1185000000000], [2501250000000]) none none (.next ([-382500000000, -9000000000000],
      [765000000000, 18000000000000]) none none (.next ([-1927500000000, 9000000000000],
      [2310000000000, 0]) none none (.next ([-1316250000000], [1507500000000, 9000000000000]) none
      none (.terminal none none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded3_2 : ExcludedOn (model3.B 2 ++ [step3.q]) 9000000000000 (model3.caps 2) (model3.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7875000000000, 0], [191250000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([8617500000000, -9000000000000],
      [382500000000, 9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([742500000000,
      -9000000000000], [191250000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([382500000000,
      9000000000000], [382500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([4500000000000, 0], [4882500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([4117500000000, -9000000000000], [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([1316250000000], [3375000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([382500000000,
      9000000000000], [4117500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([191250000000, 0], [7301250000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([191250000000], [7683750000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [382500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-191250000000,
      -9000000000000], [8066250000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-382500000000, -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-191250000000, 0], [933750000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-382500000000, -9000000000000], [765000000000, 18000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-4882500000000, -9000000000000], [9382500000000, 9000000000000]) (some (0, 4,
      2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8617500000000, -9000000000000]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-3375000000000], [4691250000000]) (some (0, 4, 3)) (some (0,
      4, 3)) (.next ([-4117500000000, 9000000000000], [4500000000000, 0]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-7301250000000, 9000000000000], [7492500000000, -9000000000000]) (some (0, 2,
      3)) (some (0, 2, 3)) (.next ([-7683750000000], [7875000000000]) (some (0, 2, 3)) (some (0, 2,
      3)) (.terminal (some (0, 2, 3)) (some (0, 2, 0)) (some (0, 2, 3))))))))))))))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded3_3 : ExcludedOn (model3.B 3 ++ [step3.q]) 9000000000000 (model3.caps 3) (model3.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded3_4 : ExcludedOn (model3.B 4 ++ [step3.q]) 9000000000000 (model3.caps 4) (model3.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded3_5 : ExcludedOn (model3.B 5 ++ [step3.q]) 9000000000000 (model3.caps 5) (model3.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded3_6 : ExcludedOn (model3.B 6 ++ [step3.q]) 9000000000000 (model3.caps 6) (model3.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded3_7 : ExcludedOn (model3.B 7 ++ [step3.q]) 9000000000000 (model3.caps 7) (model3.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([742500000000, -9000000000000], [191250000000,
      0]) (some (3, 5, 2)) (some (4, 5, 3)) fan3Owner7Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded3_8 : ExcludedOn (model3.B 8 ++ [step3.q]) 9000000000000 (model3.caps 8) (model3.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded3_9 : ExcludedOn (model3.B 9 ++ [step3.q]) 9000000000000 (model3.caps 9) (model3.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked3 : StepValid model3 9000000000000 step3 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded3_1
    · exact excluded3_2
    · exact excluded3_3
    · exact excluded3_4
    · exact excluded3_5
    · exact excluded3_6
    · exact excluded3_7
    · exact excluded3_8
    · exact excluded3_9
theorem next3 : model3.insert step3 = model4 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded4_1 : ExcludedOn (model4.B 1 ++ [step4.q]) 9000000000000 (model4.caps 1) (model4.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([183750000000, -9000000000000], [7500000000,
      9000000000000]) none none (.next ([382500000000, 9000000000000], [382500000000,
      9000000000000]) none none (.next ([191250000000, 9000000000000], [566250000000]) none none
      (.next ([566250000000], [1935000000000]) none none (.next ([382500000000, 9000000000000],
      [1927500000000, -9000000000000]) none none (.next ([0], [2692500000000, 9000000000000]) none
      none (.next ([-7500000000, -9000000000000], [191250000000, 0]) none none (.next
      ([-382500000000, -9000000000000], [765000000000, 18000000000000]) none none (.next
      ([-566250000000], [757500000000, 9000000000000]) none none (.next ([-1935000000000],
      [2501250000000]) none none (.next ([-1927500000000, 9000000000000], [2310000000000, 0]) none
      none (.terminal none none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded4_2 : ExcludedOn (model4.B 2 ++ [step4.q]) 9000000000000 (model4.caps 2) (model4.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8625000000000, 0], [191250000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([8617500000000, -9000000000000],
      [382500000000, 9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([382500000000,
      9000000000000], [382500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([4500000000000, 0], [4882500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([4117500000000, -9000000000000], [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([566250000000], [4125000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([382500000000,
      9000000000000], [4117500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([191250000000, 0], [8051250000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([191250000000], [8433750000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [382500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-191250000000,
      -9000000000000], [8816250000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-382500000000, -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-382500000000, -9000000000000], [765000000000, 18000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-4882500000000, -9000000000000], [9382500000000, 9000000000000]) (some (0, 4,
      2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8617500000000, -9000000000000]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-4125000000000], [4691250000000]) (some (0, 4, 3)) (some (0,
      4, 3)) (.next ([-4117500000000, 9000000000000], [4500000000000, 0]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-8051250000000, 9000000000000], [8242500000000, -9000000000000]) (some (0, 2,
      3)) (some (0, 2, 3)) (.next ([-8433750000000], [8625000000000]) (some (0, 2, 3)) (some (0, 2,
      3)) (.terminal (some (0, 2, 3)) (some (0, 2, 0)) (some (0, 2, 3))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded4_3 : ExcludedOn (model4.B 3 ++ [step4.q]) 9000000000000 (model4.caps 3) (model4.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded4_4 : ExcludedOn (model4.B 4 ++ [step4.q]) 9000000000000 (model4.caps 4) (model4.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded4_5 : ExcludedOn (model4.B 5 ++ [step4.q]) 9000000000000 (model4.caps 5) (model4.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded4_6 : ExcludedOn (model4.B 6 ++ [step4.q]) 9000000000000 (model4.caps 6) (model4.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded4_7 : ExcludedOn (model4.B 7 ++ [step4.q]) 9000000000000 (model4.caps 7) (model4.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([183750000000, -9000000000000], [7500000000,
      9000000000000]) (some (3, 5, 2)) (some (4, 5, 3)) fan4Owner7Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded4_8 : ExcludedOn (model4.B 8 ++ [step4.q]) 9000000000000 (model4.caps 8) (model4.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded4_9 : ExcludedOn (model4.B 9 ++ [step4.q]) 9000000000000 (model4.caps 9) (model4.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked4 : StepValid model4 9000000000000 step4 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded4_1
    · exact excluded4_2
    · exact excluded4_3
    · exact excluded4_4
    · exact excluded4_5
    · exact excluded4_6
    · exact excluded4_7
    · exact excluded4_8
    · exact excluded4_9
theorem next4 : model4.insert step4 = model5 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Across042500047500
end ConwaySoifer.Simplified.Certificates
