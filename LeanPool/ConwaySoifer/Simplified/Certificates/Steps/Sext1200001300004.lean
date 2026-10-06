/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext120000130000
import Mathlib.Tactic.FinCases

/-!
# Sext 120000 130000 4

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
namespace Sext120000130000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner2Part0 : FanWitness := (.next ([2700000000000], [225000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([4005000000000], [2175000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([3930000000000], [2175000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([5760000000000,
    9000000000000], [3795000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([1830000000000, 9000000000000], [1620000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([1755000000000, 9000000000000], [1620000000000, -9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([4680000000000], [4875000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([1080000000000, 9000000000000], [3600000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([750000000000], [2700000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([675000000000], [2700000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1080000000000],
    [4875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0], [3600000000000]) (some (0, 5,
    3)) (some (5, 5, 3)) (.next ([-150000000000], [2850000000000]) (some (5, 5, 3)) (some (5, 5, 4))
    (.next ([-225000000000], [2925000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next
    ([-2175000000000], [6180000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-2175000000000],
    [6105000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-3795000000000, 9000000000000],
    [9555000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-1620000000000, 9000000000000],
    [3450000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-1620000000000, 9000000000000],
    [3375000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-4875000000000], [9555000000000])
    (some (5, 2, 4)) (some (5, 3, 4)) (.next ([-3600000000000, 0], [4680000000000, 9000000000000])
    (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-2700000000000], [3450000000000]) (some (5, 3, 4))
    (some (5, 3, 4)) (.next ([-2700000000000], [3375000000000]) (some (5, 3, 4)) (some (5, 3, 4))
    (.next ([-4875000000000], [5955000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.terminal (some
    (5, 3, 4)) (some (5, 3, 0)) (some (5, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner0Part0 : FanWitness := (.next ([453600000000, -5220000000000], [5608200000000,
    2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([118200000000, 2610000000000],
    [3693600000000, -5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([0, 0],
    [939600000000, 7830000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-13200000000,
    -2610000000000], [6626400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-326400000000, -5220000000000], [6313200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-75000000000], [780000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-508200000000, -2610000000000], [4946400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 4,
    5)) (.next ([-508200000000, -2610000000000], [4006800000000, -2610000000000]) (some (7, 4, 5))
    (some (7, 4, 5)) (.next ([-821400000000, -5220000000000], [4633200000000, 2610000000000]) (some
    (7, 4, 5)) (some (7, 4, 5)) (.next ([-3240000000000], [9420000000000]) (some (7, 4, 5)) (some
    (7, 4, 5)) (.next ([-3240000000000], [8220000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next
    ([-4020000000000], [10125000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-780000000000],
    [1905000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-313200000000, -2610000000000],
    [626400000000, 5220000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-3781800000000,
    2610000000000], [5488200000000, 2610000000000]) (some (7, 4, 5)) (some (7, 4, 6)) (.next
    ([-4981800000000, 2610000000000], [6688200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-4408200000000, -2610000000000], [5801400000000, 5220000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-5608200000000, -2610000000000], [7001400000000, 5220000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.next ([-5686800000000, 2610000000000], [6613200000000,
    2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4721400000000, -5220000000000],
    [5488200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5921400000000,
    -5220000000000], [6688200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-6313200000000, -2610000000000], [6926400000000, 5220000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-5608200000000, -2610000000000], [6061800000000, -2610000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-3693600000000, 5220000000000], [3811800000000, -2610000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.terminal (some (7, 4, 6)) (some (7, 4, 6)) (some (7, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner3Part0 : FanWitness := (.next ([4320000000000], [945000000000]) (some (4, 0, 1)) (some
    (4, 0, 1)) (.next ([3375000000000], [1500000000000]) (some (4, 0, 1)) (some (4, 0, 1)) (.next
    ([5139000000000], [2931000000000]) (some (4, 0, 1)) (some (4, 5, 1)) (.next ([5400000000000,
    9000000000000], [3795000000000, -9000000000000]) (some (4, 5, 1)) (some (4, 5, 1)) (.next
    ([1125000000000], [819000000000]) (some (4, 5, 1)) (some (4, 5, 1)) (.next ([4320000000000],
    [4875000000000]) (some (4, 5, 1)) (some (4, 5, 1)) (.next ([1374000000000], [2376000000000])
    (some (4, 5, 1)) (some (4, 5, 1)) (.next ([1635000000000, 9000000000000], [3240000000000,
    -9000000000000]) (some (4, 5, 1)) (some (4, 5, 2)) (.next ([1944000000000], [4695000000000])
    (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1080000000000, 9000000000000], [5820000000000]) (some
    (4, 5, 2)) (some (4, 5, 3)) (.next ([555000000000], [4320000000000]) (some (4, 5, 3)) (some (4,
    5, 3)) (.next ([0], [5820000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-555000000000],
    [4320000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-945000000000], [5265000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1500000000000], [4875000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-2931000000000], [8070000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-3795000000000, 9000000000000], [9195000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-819000000000], [1944000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-4875000000000], [9195000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2376000000000],
    [3750000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3240000000000, 9000000000000],
    [4875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4695000000000], [6639000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5820000000000, 0], [6900000000000, 9000000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4320000000000], [4875000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5,
    3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner0Part0 : FanWitness := (.next ([613200000000, 2610000000000], [6313200000000,
    2610000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([705000000000], [8295000000000]) (some
    (0, 3, 7)) (some (0, 3, 7)) (.next ([453600000000, -5220000000000], [5608200000000,
    2610000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([0, 0], [939600000000, 7830000000000])
    (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-13200000000, -2610000000000], [6626400000000,
    5220000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-326400000000, -5220000000000],
    [6313200000000, 2610000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-75000000000],
    [780000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-1293600000000, 5220000000000],
    [7606800000000, -2610000000000]) (some (0, 3, 7)) (some (0, 4, 7)) (.next ([-1606800000000,
    2610000000000], [8233200000000, 2610000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next
    ([-1606800000000, 2610000000000], [7293600000000, -5220000000000]) (some (0, 4, 7)) (some (0, 4,
    7)) (.next ([-2233200000000, -2610000000000], [8546400000000, 5220000000000]) (some (0, 4, 7))
    (some (0, 4, 7)) (.next ([-780000000000], [1905000000000]) (some (0, 4, 7)) (some (0, 4, 7))
    (.next ([-313200000000, -2610000000000], [626400000000, 5220000000000]) (some (0, 4, 7)) (some
    (0, 4, 7)) (.next ([-3781800000000, 2610000000000], [5488200000000, 2610000000000]) (some (0, 4,
    7)) (some (1, 4, 7)) (.next ([-4981800000000, 2610000000000], [6688200000000, 2610000000000])
    (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-4408200000000, -2610000000000], [5801400000000,
    5220000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-7095000000000], [9000000000000])
    (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-5608200000000, -2610000000000], [7001400000000,
    5220000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-5686800000000, 2610000000000],
    [6613200000000, 2610000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-4721400000000,
    -5220000000000], [5488200000000, 2610000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-5921400000000, -5220000000000], [6688200000000, 2610000000000]) (some (1, 4, 7)) (some (1, 4,
    7)) (.next ([-6313200000000, -2610000000000], [6926400000000, 5220000000000]) (some (1, 4, 7))
    (some (1, 4, 7)) (.next ([-8295000000000], [9000000000000]) (some (1, 4, 7)) (some (2, 4, 7))
    (.next ([-5608200000000, -2610000000000], [6061800000000, -2610000000000]) (some (2, 4, 7))
    (some (2, 4, 7)) (.terminal (some (2, 4, 7)) (some (2, 4, 7)) (some (2, 4,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan38Owner3Part0 : FanWitness := (.next ([4320000000000], [945000000000]) (some (4, 0, 1)) (some
    (4, 0, 1)) (.next ([3525000000000, 9000000000000], [1875000000000]) (some (4, 0, 1)) (some (4,
    0, 1)) (.next ([1125000000000], [819000000000]) (some (4, 0, 1)) (some (4, 0, 1)) (.next
    ([2445000000000], [1875000000000]) (some (4, 0, 1)) (some (4, 0, 1)) (.next ([3000000000000],
    [3765000000000]) (some (4, 0, 1)) (some (5, 0, 1)) (.next ([1500000000000], [2445000000000])
    (some (5, 0, 1)) (some (5, 0, 1)) (.next ([1374000000000], [2376000000000]) (some (5, 0, 1))
    (some (5, 0, 1)) (.next ([1635000000000, 9000000000000], [3240000000000, -9000000000000]) (some
    (5, 0, 1)) (some (5, 0, 2)) (.next ([1944000000000], [4695000000000]) (some (5, 0, 2)) (some (5,
    0, 2)) (.next ([1080000000000, 9000000000000], [5820000000000]) (some (5, 0, 2)) (some (5, 0,
    3)) (.next ([555000000000], [4320000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next ([0],
    [5820000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next ([-750000000000], [5139000000000])
    (some (5, 0, 3)) (some (5, 0, 3)) (.next ([-945000000000], [5265000000000]) (some (5, 0, 3))
    (some (5, 0, 3)) (.next ([-1875000000000, 0], [5400000000000, 9000000000000]) (some (5, 0, 3))
    (some (5, 1, 3)) (.next ([-819000000000], [1944000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([-1875000000000], [4320000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([-3765000000000], [6765000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-2445000000000],
    [3945000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-2376000000000], [3750000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3240000000000, 9000000000000], [4875000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4695000000000], [6639000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-5820000000000, 0], [6900000000000, 9000000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-4320000000000], [4875000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.terminal (some (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2700000000000], [150000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) fan32Owner2Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_7 : ExcludedOn (model32.B 7 ++ [step32.q]) 9000000000000 (model32.caps 7)
    (model32.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_8 : ExcludedOn (model32.B 8 ++ [step32.q]) 9000000000000 (model32.caps 8)
    (model32.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked32 : StepValid model32 9000000000000 step32 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
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
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_8 : ExcludedOn (model33.B 8 ++ [step33.q]) 9000000000000 (model33.caps 8)
    (model33.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_9 : ExcludedOn (model33.B 9 ++ [step33.q]) 9000000000000 (model33.caps 9)
    (model33.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked33 : StepValid model33 9000000000000 step33 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded33_0
    · exact excluded33_1
    · exact (hj rfl).elim
    · exact excluded33_3
    · exact excluded33_4
    · exact excluded33_5
    · exact excluded33_6
    · exact excluded33_7
    · exact excluded33_8
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded34_0 : ExcludedOn (model34.B 0 ++ [step34.q]) 9000000000000 (model34.caps 0)
    (model34.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6613200000000, 2610000000000], [13200000000,
      2610000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([5986800000000, -2610000000000],
      [326400000000, 5220000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([705000000000],
      [75000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([4438200000000, 2610000000000],
      [508200000000, 2610000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3498600000000,
      -5220000000000], [508200000000, 2610000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([3811800000000, -2610000000000], [821400000000, 5220000000000]) (some (6, 7, 4)) (some (6, 7,
      4)) (.next ([6180000000000], [3240000000000]) (some (6, 7, 4)) (some (7, 7, 4)) (.next
      ([4980000000000], [3240000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([6105000000000],
      [4020000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([1125000000000], [780000000000])
      (some (7, 3, 4)) (some (7, 3, 4)) (.next ([313200000000, 2610000000000], [313200000000,
      2610000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([1706400000000, 5220000000000],
      [3781800000000, -2610000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([1706400000000,
      5220000000000], [4981800000000, -2610000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next
      ([1393200000000, 2610000000000], [4408200000000, 2610000000000]) (some (7, 3, 4)) (some (7, 3,
      4)) (.next ([1393200000000, 2610000000000], [5608200000000, 2610000000000]) (some (7, 3, 4))
      (some (7, 3, 4)) (.next ([926400000000, 5220000000000], [5686800000000, -2610000000000]) (some
      (7, 3, 4)) (some (7, 3, 4)) (.next ([766800000000, -2610000000000], [4721400000000,
      5220000000000]) (some (7, 3, 4)) (some (7, 3, 5)) (.next ([766800000000, -2610000000000],
      [5921400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([613200000000,
      2610000000000], [6313200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3, 5))
      fan34Owner0Part0)))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3765000000000], [555000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) fan34Owner3Part0)) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_7 : ExcludedOn (model34.B 7 ++ [step34.q]) 9000000000000 (model34.caps 7)
    (model34.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_8 : ExcludedOn (model34.B 8 ++ [step34.q]) 9000000000000 (model34.caps 8)
    (model34.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_9 : ExcludedOn (model34.B 9 ++ [step34.q]) 9000000000000 (model34.caps 9)
    (model34.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked34 : StepValid model34 9000000000000 step34 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
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
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded35_0 : ExcludedOn (model35.B 0 ++ [step35.q]) 9000000000000 (model35.caps 0)
    (model35.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6840000000000, 9000000000000], [2910000000000,
      -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([5760000000000], [3990000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4680000000000, -9000000000000], [3990000000000, 0])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1080000000000, 9000000000000], [1080000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1080000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2910000000000, 9000000000000],
      [9750000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-3990000000000], [9750000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-3990000000000, 0], [8670000000000,
      -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1080000000000, -9000000000000],
      [2160000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 3)) (.terminal (some (3, 1, 3))
      (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_7 : ExcludedOn (model35.B 7 ++ [step35.q]) 9000000000000 (model35.caps 7)
    (model35.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_8 : ExcludedOn (model35.B 8 ++ [step35.q]) 9000000000000 (model35.caps 8)
    (model35.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_9 : ExcludedOn (model35.B 9 ++ [step35.q]) 9000000000000 (model35.caps 9)
    (model35.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked35 : StepValid model35 9000000000000 step35 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded35_0
    · exact excluded35_1
    · exact (hj rfl).elim
    · exact excluded35_3
    · exact excluded35_4
    · exact excluded35_5
    · exact excluded35_6
    · exact excluded35_7
    · exact excluded35_8
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded36_0 : ExcludedOn (model36.B 0 ++ [step36.q]) 9000000000000 (model36.caps 0)
    (model36.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5580000000000, 0], [2340000000000,
      -9000000000000]) (some (3, 1, 1)) (some (3, 1, 2)) (.next ([6660000000000, 9000000000000],
      [3420000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([5580000000000], [3420000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1080000000000, 9000000000000], [1080000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([0, 0], [1080000000000,
      9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-2340000000000, 9000000000000],
      [7920000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-3420000000000],
      [10080000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3420000000000],
      [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1080000000000, -9000000000000],
      [2160000000000, 18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3))
      (some (1, 1, 3)) (some (1, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_8 : ExcludedOn (model36.B 8 ++ [step36.q]) 9000000000000 (model36.caps 8)
    (model36.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_9 : ExcludedOn (model36.B 9 ++ [step36.q]) 9000000000000 (model36.caps 9)
    (model36.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked36 : StepValid model36 9000000000000 step36 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
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
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded37_0 : ExcludedOn (model37.B 0 ++ [step37.q]) 9000000000000 (model37.caps 0)
    (model37.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6613200000000, 2610000000000], [13200000000,
      2610000000000]) (some (7, 2, 4)) (some (7, 3, 7)) (.next ([5986800000000, -2610000000000],
      [326400000000, 5220000000000]) (some (7, 3, 7)) (some (7, 3, 7)) (.next ([705000000000],
      [75000000000]) (some (7, 3, 7)) (some (7, 3, 7)) (.next ([6313200000000, 2610000000000],
      [1293600000000, -5220000000000]) (some (7, 3, 7)) (some (7, 3, 7)) (.next ([6626400000000,
      5220000000000], [1606800000000, -2610000000000]) (some (6, 3, 7)) (some (6, 3, 7)) (.next
      ([5686800000000, -2610000000000], [1606800000000, -2610000000000]) (some (6, 3, 7)) (some (6,
      3, 7)) (.next ([6313200000000, 2610000000000], [2233200000000, 2610000000000]) (some (6, 3,
      7)) (some (6, 3, 7)) (.next ([1125000000000], [780000000000]) (some (6, 3, 7)) (some (6, 3,
      7)) (.next ([313200000000, 2610000000000], [313200000000, 2610000000000]) (some (6, 3, 7))
      (some (6, 3, 7)) (.next ([1706400000000, 5220000000000], [3781800000000, -2610000000000])
      (some (0, 3, 7)) (some (0, 3, 7)) (.next ([1706400000000, 5220000000000], [4981800000000,
      -2610000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([1393200000000, 2610000000000],
      [4408200000000, 2610000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([1905000000000],
      [7095000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([1393200000000, 2610000000000],
      [5608200000000, 2610000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([926400000000,
      5220000000000], [5686800000000, -2610000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
      ([766800000000, -2610000000000], [4721400000000, 5220000000000]) (some (0, 3, 7)) (some (0, 3,
      7)) (.next ([766800000000, -2610000000000], [5921400000000, 5220000000000]) (some (0, 3, 7))
      (some (0, 3, 7)) fan37Owner0Part0)))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6660000000000], [420000000000]) (some (0, 3, 1))
      (some (0, 3, 2)) (.next ([3000000000000], [6000000000000, -9000000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([3000000000000], [7080000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([0], [3420000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-420000000000],
      [7080000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-6000000000000, 9000000000000],
      [9000000000000, -9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-7080000000000],
      [10080000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded37_8 : ExcludedOn (model37.B 8 ++ [step37.q]) 9000000000000 (model37.caps 8)
    (model37.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_9 : ExcludedOn (model37.B 9 ++ [step37.q]) 9000000000000 (model37.caps 9)
    (model37.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked37 : StepValid model37 9000000000000 step37 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
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
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded38_0 : ExcludedOn (model38.B 0 ++ [step38.q]) 9000000000000 (model38.caps 0)
    (model38.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_1 : ExcludedOn (model38.B 1 ++ [step38.q]) 9000000000000 (model38.caps 1)
    (model38.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_2 : ExcludedOn (model38.B 2 ++ [step38.q]) 9000000000000 (model38.caps 2)
    (model38.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_3 : ExcludedOn (model38.B 3 ++ [step38.q]) 9000000000000 (model38.caps 3)
    (model38.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4389000000000], [750000000000]) (some (3, 0, 1))
      (some (4, 0, 1)) fan38Owner3Part0)) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded38_4 : ExcludedOn (model38.B 4 ++ [step38.q]) 9000000000000 (model38.caps 4)
    (model38.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_7 : ExcludedOn (model38.B 7 ++ [step38.q]) 9000000000000 (model38.caps 7)
    (model38.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_9 : ExcludedOn (model38.B 9 ++ [step38.q]) 9000000000000 (model38.caps 9)
    (model38.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked38 : StepValid model38 9000000000000 step38 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
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
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded39_0 : ExcludedOn (model39.B 0 ++ [step39.q]) 9000000000000 (model39.caps 0)
    (model39.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_1 : ExcludedOn (model39.B 1 ++ [step39.q]) 9000000000000 (model39.caps 1)
    (model39.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_2 : ExcludedOn (model39.B 2 ++ [step39.q]) 9000000000000 (model39.caps 2)
    (model39.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_4 : ExcludedOn (model39.B 4 ++ [step39.q]) 9000000000000 (model39.caps 4)
    (model39.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4680000000000], [960000000000]) (some (4, 0, 1))
      (some (4, 1, 1)) (.next ([3360000000000], [1515000000000]) (some (4, 1, 1)) (some (4, 1, 2))
      (.next ([3165000000000], [5835000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1275000000000, 9000000000000], [3600000000000, -9000000000000]) (some (4, 1, 2)) (some (4,
      1, 2)) (.next ([1080000000000, 9000000000000], [5835000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([195000000000], [4680000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0],
      [5835000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-960000000000], [5640000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1515000000000], [4875000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-5835000000000], [9000000000000]) (some (0, 1, 2)) (some (0, 1, 4))
      (.next ([-3600000000000, 9000000000000], [4875000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-5835000000000], [6915000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-4680000000000], [4875000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal (some
      (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_6 : ExcludedOn (model39.B 6 ++ [step39.q]) 9000000000000 (model39.caps 6)
    (model39.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_7 : ExcludedOn (model39.B 7 ++ [step39.q]) 9000000000000 (model39.caps 7)
    (model39.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_8 : ExcludedOn (model39.B 8 ++ [step39.q]) 9000000000000 (model39.caps 8)
    (model39.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1875000000000], [945000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([5835000000000], [3165000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([3735000000000], [2070000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([1515000000000], [2445000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1875000000000],
      [4680000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([750000000000], [3930000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([570000000000], [5265000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([30000000000], [3165000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([0], [5805000000000]) (some (0, 1, 2)) (some (0, 4, 2)) (.next ([-945000000000],
      [2820000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-3165000000000], [9000000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-2070000000000], [5805000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-2445000000000], [3960000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-4680000000000], [6555000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3930000000000], [4680000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-5265000000000], [5835000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3165000000000], [3195000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_9 : ExcludedOn (model39.B 9 ++ [step39.q]) 9000000000000 (model39.caps 9)
    (model39.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked39 : StepValid model39 9000000000000 step39 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded39_0
    · exact excluded39_1
    · exact excluded39_2
    · exact (hj rfl).elim
    · exact excluded39_4
    · exact excluded39_5
    · exact excluded39_6
    · exact excluded39_7
    · exact excluded39_8
    · exact excluded39_9
theorem next39 : model39.insert step39 = model40 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext120000130000
end ConwaySoifer.Simplified.Certificates
