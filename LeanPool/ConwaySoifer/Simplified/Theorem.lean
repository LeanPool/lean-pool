/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Normalization
public import LeanPool.ConwaySoifer.Simplified.Complements.SextSmall
public import LeanPool.ConwaySoifer.Simplified.Complements.SintSmall
public import LeanPool.ConwaySoifer.Simplified.Complements.AownSmall
public import LeanPool.ConwaySoifer.Simplified.Complements.AownLarge
public import LeanPool.ConwaySoifer.Simplified.Complements.AcrossSmall
public import LeanPool.ConwaySoifer.Simplified.Complements.AcrossLarge
public import LeanPool.ConwaySoifer.Geometry.Scaling
import Mathlib.Tactic

/-! The independent, unconditional assembly of the third-pass simplified proof. -/

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
namespace ConwaySoifer
open scoped Pointwise

theorem Simplified.canonical_impossible {c : ContactCase} {T : Configuration} {r s : ℝ}
    (H : Canonical c T r s) : False := by
  cases c with
  | Sext =>
    rcases Simplified.Certificates.ranges_complete .Sext H.s_pos with hs | ⟨hlo, hhi⟩ | hs
    · apply Simplified.sext_small H
      simpa [Simplified.Certificates.caseStart] using hs
    · exact Simplified.Certificates.caseExcluded .Sext H hlo hhi
    · linarith [Simplified.sext_upper H]
  | Sint =>
    rcases Simplified.Certificates.ranges_complete .Sint H.s_pos with hs | ⟨hlo, hhi⟩ | hs
    · apply Simplified.sint_small H
      simpa [Simplified.Certificates.caseStart] using hs
    · exact Simplified.Certificates.caseExcluded .Sint H hlo hhi
    · linarith [Simplified.sint_upper H]
  | Aown =>
    rcases Simplified.Certificates.ranges_complete .Aown H.s_pos with hs | ⟨hlo, hhi⟩ | hs
    · apply Simplified.aown_small H
      simpa [Simplified.Certificates.caseStart] using hs
    · exact Simplified.Certificates.caseExcluded .Aown H hlo hhi
    · exact Simplified.aown_large H hs
  | Across =>
    rcases Simplified.Certificates.ranges_complete .Across H.s_pos with hs | ⟨hlo, hhi⟩ | hs
    · apply Simplified.across_small H
      simpa [Simplified.Certificates.caseStart] using hs
    · exact Simplified.Certificates.caseExcluded .Across H hlo hhi
    · exact Simplified.across_large H hs

/-- Ten congruent closed equilateral triangles covering the whole side-three
triangle have common side at least one, by the simplified proof. -/
theorem lowerBound_simplified : LowerBound := by
  intro r T hside hcover
  by_contra hnot
  obtain ⟨c, U, s, H⟩ := Simplified.exists_canonical r T hside hcover (lt_of_not_ge hnot)
  exact Simplified.canonical_impossible H

theorem one_le_side_of_cover_simplified (r : ℝ) (T : Configuration)
    (hside : CommonSide T r) (hcover : Covers T) : 1 ≤ r :=
  lowerBound_simplified r T hside hcover

/-- The scaled consequence for ten unit triangles and target side `3 + ε`. -/
theorem no_ten_unit_triangle_cover_simplified (ε : ℝ) (hε : 0 < ε) (T : Configuration)
    (hs : ∀ i, (T i).side = 1)
    (hcover : ∀ p ∈ (1 + ε / 3) • target, ∃ i, p ∈ (T i).carrier) : False :=
  no_ten_unit_triangle_cover_of_lowerBound lowerBound_simplified ε hε T hs hcover

end ConwaySoifer
