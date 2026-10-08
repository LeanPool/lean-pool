/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRowEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValue
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdjointMirrors
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAverageDrops
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastFusionIsotropy
public import LeanPool.HighContrastHomogenization.Provider.Quenched.EndpointRelativeBlockRow
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMaximumEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastIsotropyCarriers

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastIsotropyPack

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The isotropy discharge pack

`exists_one_step_family_of_block_var_at_level_conv_family_split` is `Π`-free but
takes six hypotheses at the abstract block.  This file produces the four with
content from their near-reference producers; the remaining two are `hFeq`, which is `rfl`
at `isotropyReference`, and `hcDeep`, which is the scale threshold.

Everything here turns on one scale: the **split point**

```
k₀ = kEnt + tiltGap Cd g (cEnt/2) nu (Gacc+1)
```

where the entry depth is past `euclideanEntryThreshold K (cEnt/2) sK`.  Above `k₀`
the near-reference comparison's `adaptedMean_near_reference` applies at every scale and every
cell, at
the dimension-only constant `nearIdentityDefect cEnt sigma`.  Both thresholds
are `⌈log₃ ·⌉`-shaped — `euclideanEntryThreshold` logarithmic in the source gauge
and `tiltGap` logarithmic in `boundaryConst · 3^{gG}` — so `k₀` costs a delay
logarithmic in the law parameters, which is precisely what's
`three_mul_max_one_le_rpow` converts into a law-free exponent.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The two thresholds are at least one step -/

theorem add_one_le_euclideanEntryThreshold (K cEnt : ℝ) (sK : ℤ) :
    sK + 1 ≤ euclideanEntryThreshold K cEnt sK := by
  rw [euclideanEntryThreshold]
  have h : (1 : ℤ) ≤ max 1 ⌈Real.logb 3 (sourceMomentTwo K / cEnt)⌉ :=
    le_max_left _ _
  omega

theorem one_le_tiltGap (Cd g cEnt : ℝ) (m : Mat d) (G : ℕ) :
    1 ≤ tiltGap Cd g cEnt m G := by
  rw [tiltGap]
  exact le_max_left _ _

/-- **The split point.**  Past it, the near-reference comparison's comparison holds at every
scale. -/
@[expose]
def isotropySplit (K cEnt Cd g : ℝ) (nu : Mat d) (G : ℕ) (sK : ℤ) : ℤ :=
  euclideanEntryThreshold K cEnt sK + tiltGap Cd g cEnt nu G

theorem le_isotropySplit (K cEnt Cd g : ℝ) (nu : Mat d) (G : ℕ) (sK : ℤ) :
    sK + 2 ≤ isotropySplit K cEnt Cd g nu G sK := by
  have h1 := add_one_le_euclideanEntryThreshold K cEnt sK
  have h2 := one_le_tiltGap (d := d) Cd g cEnt nu G
  rw [isotropySplit]
  omega

/-! ## The four members with content -/

/-- **Member 1: the isotropy family the split row cap consumes.**  Above the
split point every aligned cell's annealed block sits below `(1+cIso)𝐄`. -/
theorem hiso_of_isotropySplit [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {nu : Mat d} (hnu : nu.PosDef)
    {Gacc : ℕ}
    (hqnorm : ‖roundedGrid l nu‖ * Real.sqrt d ≤ (3 : ℝ) ^ Gacc)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    {sigma cEnt : ℝ} (hsigma : refContrast E - 1 ≤ sigma) (hsigma0 : 0 ≤ sigma)
    (hcEnt : 0 < cEnt)
    (hkEnt0 : 0 ≤ euclideanEntryThreshold K (cEnt / 2) sK)
    (hlsplit : l ≤ isotropySplit K (cEnt / 2) Cd g nu (Gacc + 1) sK)
    (hentry0 : sourceMomentTwo K ≤ (3 : ℝ) ^
      (isotropySplit K (cEnt / 2) Cd g nu (Gacc + 1) sK +
        ((Gacc + 1 : ℕ) : ℤ) - sK)) :
    ∀ k : ℤ, isotropySplit K (cEnt / 2) Cd g nu (Gacc + 1) sK ≤ k →
      ∀ w : Fin d → ℤ,
        BlockMatLoewnerLE
          (annealedBlock P (adaptedCellAt (roundedGrid l nu) k w))
          (blockScale (1 + nearIdentityDefect cEnt sigma) E) := by
  intro k hk w
  have hd1 : 1 ≤ d := by omega
  have hq : (roundedGrid l nu).PosDef := Recurrence.posDef_roundedGrid hl hnu
  have hsplit2 := le_isotropySplit (d := d) K (cEnt / 2) Cd g nu (Gacc + 1) sK
  have hcEnt2 : (0 : ℝ) < cEnt / 2 := by linarith only [hcEnt]
  have hsub : adaptedCell (roundedGrid l nu) k ⊆
      centeredCube d (k + ((Gacc + 1 : ℕ) : ℤ)) := by
    refine (Selection.adaptedCell_subset_centeredCube_add hd1 hqnorm).trans
      (Window.centeredCube_mono ?_)
    omega
  have hentry : sourceMomentTwo K ≤
      (3 : ℝ) ^ (k + ((Gacc + 1 : ℕ) : ℤ) - sK) := by
    refine le_trans hentry0 ?_
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hres := annealedBlock_adaptedCellAt_le_isotropy hd hg hdag hstat hl hCd
    hnu hsK (k := euclideanEntryThreshold K (cEnt / 2) sK) (r := k)
    (G := Gacc + 1) hkEnt0 (by omega) hsigma hsigma0 hcEnt le_rfl
    (by rw [isotropySplit] at hk; omega) (by omega) hentry hsub
    (finite_adaptedMean_of_coarseEllipticityDagger hdag hq k).1 w
  rw [isotropyReference_eq_blockScale] at hres
  exact hres

/-- **Members 2 and 3: the envelope and the comparability.**  Above the split
point the adapted mean is within `(1 ± cIso)` of the reference, so it sits below
`isotropyReference cIso 𝐄` and dominates `𝐄` at `isotropyKap2 cIso`. -/
theorem isotropy_carriers_of_isotropySplit [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {nu : Mat d} (hnu : nu.PosDef)
    {Gacc : ℕ}
    (hqnorm : ‖roundedGrid l nu‖ * Real.sqrt d ≤ (3 : ℝ) ^ Gacc)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    {sigma cEnt : ℝ} (hsigma : refContrast E - 1 ≤ sigma) (hsigma0 : 0 ≤ sigma)
    (hcEnt : 0 < cEnt) (hsmall : nearIdentityDefect cEnt sigma < 1)
    (hkEnt0 : 0 ≤ euclideanEntryThreshold K (cEnt / 2) sK)
    (hentry0 : sourceMomentTwo K ≤ (3 : ℝ) ^
      (isotropySplit K (cEnt / 2) Cd g nu (Gacc + 1) sK +
        ((Gacc + 1 : ℕ) : ℤ) - sK)) :
    ∀ r : ℤ, isotropySplit K (cEnt / 2) Cd g nu (Gacc + 1) sK ≤ r →
      BlockMatLoewnerLE (adaptedMean P (roundedGrid l nu) r)
          (isotropyReference (nearIdentityDefect cEnt sigma) E) ∧
        BlockMatLoewnerLE E
          (blockScale (isotropyKap2 (nearIdentityDefect cEnt sigma))
            (adaptedMean P (roundedGrid l nu) r)) := by
  intro r hr
  have hd1 : 1 ≤ d := by omega
  have hq : (roundedGrid l nu).PosDef := Recurrence.posDef_roundedGrid hl hnu
  have hsplit2 := le_isotropySplit (d := d) K (cEnt / 2) Cd g nu (Gacc + 1) sK
  have hsub : adaptedCell (roundedGrid l nu) r ⊆
      centeredCube d (r + ((Gacc + 1 : ℕ) : ℤ)) := by
    refine (Selection.adaptedCell_subset_centeredCube_add hd1 hqnorm).trans
      (Window.centeredCube_mono ?_)
    omega
  have hentry : sourceMomentTwo K ≤
      (3 : ℝ) ^ (r + ((Gacc + 1 : ℕ) : ℤ) - sK) := by
    refine le_trans hentry0 ?_
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  obtain ⟨h1, h2, -⟩ := isotropy_carriers_at_terminal hd hg hdag hstat hl hCd
    hnu hsK (k := euclideanEntryThreshold K (cEnt / 2) sK) (r := r)
    (G := Gacc + 1) hkEnt0 hsigma hsigma0 hcEnt hsmall le_rfl
    (by rw [isotropySplit] at hr; omega) (by omega) hentry hsub
    (finite_adaptedMean_of_coarseEllipticityDagger hdag hq r).1
  exact ⟨h1, h2⟩

/-! ## Member 4: the maximal envelope at the isotropy block -/

end

end HCPolySupport.HighContrast.Quenched
