/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.ThreeCentral
public import LeanPool.ConwaySoifer.Simplified.Geometry.ThreeWitnesses
import Mathlib.Tactic

/-!
# CentralWitnesses

Geometry and verified arithmetic for the Conway–Soifer covering theorem at n = 3.
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

noncomputable section
namespace ConwaySoifer.Simplified

/-- The three new points, together with the already known adaptive core,
force side at least one. No enlarged nine-point core is involved. -/
theorem three_witness_central {Q : EquilateralTriangle} {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ 1 / 10) (hQ : 0 < Q.side)
    (h0 : (0 : Point) ∈ Q.carrier) (hK : ∀ j, coreVertex s j ∈ Q.carrier)
    (hw : ∀ j, witness s j ∈ Q.carrier) : 1 ≤ Q.side := by
  have hs1 : 0 < 1 - s := by
    linarith
  have hkpos : 0 < s * (1 - s) / 3 := by
    positivity
  have hklow : 3 * s / 10 ≤ s * (1 - s) / 3 := by
    nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hs)]
  have inner (j : Fin 6) : (3 * s / 10) • coreDir j ∈ Q.carrier := by
    have ht : (3 * s / 10) / (s * (1 - s) / 3) ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨div_nonneg (by positivity) hkpos.le, (div_le_one hkpos).mpr hklow⟩
    have hm := Q.convex_carrier.smul_mem_of_zero_mem h0 (hK j) ht
    convert hm using 1
    rw [coreVertex, smul_smul, div_mul_cancel₀ _ hkpos.ne']
  apply threeCentral_obstruction hs0 hs hQ
  intro j
  fin_cases j
  · convert inner 2 using 1; ext <;> simp [threeCentralPoint, coreDir] <;> ring
  · convert inner 3 using 1; ext <;> simp [threeCentralPoint, coreDir] <;> ring
  · convert inner 4 using 1; ext <;> simp [threeCentralPoint, coreDir] <;> ring
  · convert hw 0 using 1; ext <;> simp [threeCentralPoint, witness] <;> ring
  · convert hw 2 using 1; ext <;> simp [threeCentralPoint, witness]; ring
  · convert hw 1 using 1; ext <;> simp [threeCentralPoint, witness] <;> ring

end ConwaySoifer.Simplified
