/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakGroups

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSlotAlgebra

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The slot algebra of the per-generation discharge

Two things the slot instantiation of needs, both purely algebraic.

**1. The supply value.**  `entry_lagged_variance_supply_of_block_split` delivers, at base `j_b`
and depth scale `p`, a value of the shape

  `dd · cN · ((2 + 4(1+c)²)·X + 4(1+c)²·36·(Y + Z) + c)`

with `c = 4d(Θ̂_{j_b} − Θ̂_p)` the mean drop, `X` the decayed subdivision term,
`Y = d(Θ̂_{j_b} − 1)` the base-scale excess and `Z = ½·3^{−(p−j_b)}`.  Under the
drop smallness `c ≤ 1` and `c ≤ 4Y`, this is at most

  `dd·cN·(18X + 576Z)  +  dd·cN·580·Y`,

i.e. exactly the `vsrc + cV·F(j_b)` shape the three-group split consumes.
The decay lives entirely in `X` and `Z`.

**2. The summed split.**  The uniform hypothesis `V j ≤ vsrc + cV·F(j_b)` of
`weakValueSharpMajorant_le_three_group_summed_at_level` is too coarse for the source group: a
*uniform* `vsrc` produces a source group that does not decay in the
generation, which is what stopped on.  The refined statement here takes
the hypothesis already summed against the linear weight,

  `∑_{j ≤ H_w} 3^{−j/2}(V j + V0) ≤ vsum + cVsum·F(j_b)`,

so that the depth structure — the deep legs carrying weight `3^{−j/2}` with
`j > t − j_b`, and the shallow legs carrying the subdivision decay
`3^{−d(p−j_b)/2}` — is visible in `vsum` and can decay with the generation.

**3. The recursion rate.** fixed `ρ = (1+g)/2` and the rooted-drop
weight `ν = (1−g)/4`.  The *recursion* rate must additionally beat the deep-leg
source rate, which is `3^{−J₀}` with `J₀ = n − ⌊3n/4⌋ ≥ n/4`; taking
`α_rec := (1−g)/16` gives `α_rec ≤ ν` (so the rooted conversion applies through
`iterationDropSum_mono_r`) and `α_rec ≤ 1/16 < 1/4` with strict room for the
deep-leg source.

The value is `(1−g)/16` and not `(1−g)/8`: at `(1−g)/8` the deep-leg
source rate `1/2` in the lag `J ≤ n/4` gives exactly `n/8` per generation, which
*equals* `α_rec` at `g = 0`, leaving no margin for the entry delay — the source
group can then only be fitted under `δ·3^{−α n}` by a pure constant inequality,
with no gain from the delayed start.  Halving `α_rec` opens a margin
`min((1+g)/8, 3(1−g)/8)·n`, strictly positive for every `g ∈ [0,1)`, so the
delayed start absorbs any `Π`-polynomial source constant.  The only cost is that
the endpoint rate `α_rec/(640·A)` halves, which is free: `alpha` is existential
in the frozen `hcore` binder.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The recursion rate -/

/-- The recursion rate `α_rec = (1-g)/16`: a quarter of the rooted-drop rate, so
that it beats the deep-leg source rate `1/4` strictly *and* leaves a margin for
the entry delay at every `g ∈ [0,1)`. -/
@[expose]
def recursionAlpha (g : ℝ) : ℝ := (1 - g) / 16

theorem recursionAlpha_pos {g : ℝ} (hg1 : g < 1) : 0 < recursionAlpha g := by
  rw [recursionAlpha]; linarith only [hg1]

theorem recursionAlpha_le_contrastAlpha (g : ℝ) (hg1 : g ≤ 1) :
    recursionAlpha g ≤ contrastAlpha g := by
  rw [recursionAlpha, contrastAlpha]; linarith only [hg1]

/-! ## The supply value -/

/-- **The entry lagged supply's value, in slot shape.**  Under the drop
smallness the supply value splits into a source part (carrying all the decay)
and a part linear in the base-scale excess. -/
theorem supply_value_bound {X Y Z c cN dd : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hcY : c ≤ 4 * Y)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hZ0 : 0 ≤ Z)
    (hcN0 : 0 ≤ cN) (hdd0 : 0 ≤ dd) :
    dd * cN * ((2 + 4 * (1 + c) ^ 2) * X + 4 * (1 + c) ^ 2 * (36 * (Y + Z)) + c) ≤
      dd * cN * (18 * X + 576 * Z) + dd * cN * 580 * Y := by
  have hfac : 0 ≤ dd * cN := mul_nonneg hdd0 hcN0
  have hsq : (1 + c) ^ 2 ≤ 4 := by nlinarith only [hc0, hc1]
  have hinner : (2 + 4 * (1 + c) ^ 2) * X + 4 * (1 + c) ^ 2 * (36 * (Y + Z)) + c ≤
      (18 * X + 576 * Z) + 580 * Y := by
    have h1 : (2 + 4 * (1 + c) ^ 2) * X ≤ 18 * X := by nlinarith only [hsq, hX0]
    have h2 : 4 * (1 + c) ^ 2 * (36 * (Y + Z)) ≤ 576 * Y + 576 * Z := by
      nlinarith only [hsq, hY0, hZ0]
    linarith only [h1, h2, hcY]
  have := mul_le_mul_of_nonneg_left hinner hfac
  nlinarith only [this]

/-! ## The summed three-group split -/

/-- The source group of the summed split. -/
@[expose]
def weakSourceGroupSummed (M L rho vsum vmsrc bsrc : ℝ) : ℝ :=
  16 * M * Real.sqrt L * vsum +
    Response.constantSeminormCoefficient * M * Real.sqrt 7 * vmsrc +
    16 * M / (2 * ((1 - rho) / 2)) * bsrc

/-- The base-scale coefficient of the summed split. -/
@[expose]
def weakBaseCoefficientSummed (M L cVsum cVm : ℝ) : ℝ :=
  16 * M * Real.sqrt L * cVsum +
    Response.constantSeminormCoefficient * M * Real.sqrt 7 * cVm

end

end HCPolySupport.HighContrast.Quenched
