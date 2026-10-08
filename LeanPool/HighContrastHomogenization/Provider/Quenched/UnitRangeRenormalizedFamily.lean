/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeRenormalizedScale
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeStoppingScaleDatum

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeRenormalizedFamily

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The renormalized minimal scales as a generation-indexed family

The endgame replays the renormalization of ellipticity once for every base
generation, against a reference block that changes with the generation, and feeds
the resulting family of minimal scales to the bad-tail engine.  This file records
the family, the existence of the buffer that absorbs the union-bound prefactor,
the deterministic conclusion below a minimal scale, and the composition with the
engine.

The tail constant is `c_fr(d)` throughout: it is fixed before the exponent and
before every datum of the law.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

open Book.Ch05.Section57

noncomputable section

variable {d : ℕ}

/-! ## The buffer -/

/-! ## The deterministic conclusion below the minimal scale -/

/-- **The window range of the renormalized ellipticity conclusion.**  Below the
minimal scale of the base generation, and on the event that the source has burnt
in, every cell of every scale in the window obeys the additive comparison with
the reference block. -/
theorem blockMatLoewnerLE_of_renormRadius_le {S : CoeffSpace d → ℝ}
    {Ahat : BlockMat d} {delta rho : ℝ} {h n : ℕ} {a : CoeffSpace d} {m : ℤ}
    (hfin : renormScale S Ahat delta rho h n a ≠ ⊤) (hnm : (n : ℤ) ≤ m)
    (hle : renormRadius S Ahat delta rho h n a ≤ (3 : ℝ) ^ m)
    (hsrc : S a ≤ (3 : ℝ) ^ m) :
    ∀ k : ℤ, m - (h : ℤ) + 1 ≤ k → k ≤ m → ∀ w : Fin d → ℤ,
      standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale (1 + delta * (3 : ℝ) ^ (rho * ((m : ℝ) - (k : ℝ)))) Ahat) := by
  intro k hk1 hk2 w hw
  have hpos : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have htoReal : (renormScale S Ahat delta rho h n a).toReal < (3 : ℝ) ^ m := by
    rw [renormRadius] at hle
    have hmaxle : max 1 (renormScale S Ahat delta rho h n a).toReal ≤
        (3 : ℝ) ^ m / 3 := by
      linarith only [hle]
    have hsplit : (3 : ℝ) ^ m / 3 < (3 : ℝ) ^ m := by linarith only [hpos]
    exact lt_of_le_of_lt (le_trans (le_max_right _ _) hmaxle) hsplit
  have hnotbad : a ∉ renormBadGeneration S Ahat delta rho h m := by
    intro hbad
    have hterm : ENNReal.ofReal ((3 : ℝ) ^ m) ≤ renormScale S Ahat delta rho h n a := by
      rw [renormScale]
      exact le_iSup_of_le m (le_iSup_of_le ⟨hnm, hbad⟩ le_rfl)
    have hcontra : (3 : ℝ) ^ m ≤ (renormScale S Ahat delta rho h n a).toReal := by
      have := ENNReal.toReal_mono hfin hterm
      rwa [ENNReal.toReal_ofReal hpos.le] at this
    exact absurd hcontra (not_le.2 htoReal)
  have hcellnot : a ∉ renormBadCell S Ahat delta rho m k w := by
    intro hmem
    refine hnotbad ?_
    rw [renormBadGeneration]
    refine Set.mem_biUnion (Finset.mem_Icc.2 ⟨hk1, hk2⟩) ?_
    exact Set.mem_biUnion ((mem_centredIndexFinset_iff hk2).2 hw) hmem
  by_contra hcon
  exact hcellnot ⟨hsrc, hcon⟩

/-! ## The family and the engine composition -/

end

end Quenched
end HighContrast
end HCPolySupport
