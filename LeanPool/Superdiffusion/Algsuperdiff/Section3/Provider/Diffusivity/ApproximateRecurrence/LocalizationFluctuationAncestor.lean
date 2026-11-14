/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationPerCube
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationParams
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound

/-!
# LocalizationFluctuationAncestor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The ancestor-cube transfer

The `cu_m` sub-mesh is a fraction `3^{-d(K-m)}` of the `cu_K` mesh, so the
boundary-strip bound
(`LocalizationFluctuationMeshTransfer.cubeFamilyAverage_le_add_sqrt_boundaryFraction`)
gives nothing here; and a descendant ellipticity display gated by a literal cap
`2 gamma (Q.scale - k) <= 16` is **violated** at `Q = originCube d Kc`, where
`2 gamma (Kc - n) >= 2 * 10^10`.

## What is proved

* `ancestorAtDepth` / `ancestorAtScale` -- the missing geometry.
  CoarseGraining supplies `parentCube`
  (`Homogenization/Geometry/TriadicCube.lean`) and the child/parent interface
  of `Homogenization/Geometry/TriadicPartition.lean`, but no iterated ancestor.
  `ancestorAtDepth R k` is `parentCube` iterated `k` times, and
  `ancestorAtScale R m` is the ancestor at absolute scale `m`.
  `mem_descendantsAtScale_ancestorAtScale` is the descendant relation the
  ellipticity display consumes.
* `gaugedEllipticitySum_descendant_le_of_gap` -- the descendant display at a
  **free** cap `B` on the scaled gap `2 gamma (Q.scale - k)`, in place of a
  literal `16`.  The printed constant is the case `B = 16`, and nothing in the
  proof depends on the numeral.
* `gaugedEllipticitySum_le_ancestorAtScale` and
  `doubledPoincareEllipticityFactor_sq_le_ancestorAtScale_gaugedEllipticitySum`
  -- the per-cell transfer: the ellipticity content of the mesoscopic cell `R`
  is controlled by the gauged ellipticity sum of `R`'s own scale-`m` ancestor,
  at the exponent `gamma`.
* `two_mul_gamma_mul_recurrenceGap_le` and its numerical specialization
  `..._le_twentyTwo` -- the gate really holds at the recurrence's own scales.
  `LocalizationParams.recurrenceMesoScale_budget` gives `m - n <= (6 c_star +
  2) gamma^{-1}`, hence `2 gamma (m - n) <= 12 c_star + 4`, and the proved
  `Provider.Disorder.cstar_le_three_halves` caps that at `22`.

## D against the printed constant
 ABK26 quotes `m - n <= 8 gamma^{-1}`, i.e. `2 gamma (m - n) <= 16`, which is
 the
manuscript's `c_star <= 1`.  This is why the display is restated at a free cap
`B`: the constant `3^B` is an absolute constant that the annealed Hoelder fold
absorbs into its own `C`, and
`LocalizationFluctuationSplitFoldArithmetic.exists_gamma_threshold_regime_holder_fold`
accepts every nonnegative pair of constants.  No sharpening of `c_star` is
assumed anywhere below.

## Binders

Geometry: `hm : R.scale <= m` (the ancestor exists).  Ellipticity: the exponent
window `0 < gamma < s`, the gauge positivity `0 < sigmaBar`, and the scale gap
`hgap` -- all three are source data.  Gate: the shell-width cap `h <= 6 c_star
gamma^{-1}` and the coverage threshold `hcover`, which
`cover_of_gamma_le` produces from `gamma <= 1/1089`; the latter is a produced
`gamma`-threshold, the machine-checked form of "a sufficiently large choice of
`M` in `e.cgamma.constraints`".  No smallness, moment, measurability or
integrability proposition occurs: everything below is cube combinatorics,
deterministic ellipticity arithmetic, or real arithmetic.

## Scope

There is no `sorry`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2, display;
  `e.ellipticities.monotone.ordered`; `e.bound.one.cube.by.lambdas`;
  `e.recurrence.params`; for the `8 gamma^{-1}` budget.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.CoarseEllipticity

noncomputable section

variable {d : ℕ}

/-! ## The iterated ancestor -/

/-- **The depth-`k` ancestor of a triadic cube**: `parentCube` iterated `k` times.
CoarseGraining supplies `parentCube` only. -/
def ancestorAtDepth (R : TriadicCube d) : ℕ → TriadicCube d
  | 0 => R
  | k + 1 => ancestorAtDepth (parentCube R) k

@[simp] theorem ancestorAtDepth_zero (R : TriadicCube d) : ancestorAtDepth R 0 = R := rfl

theorem ancestorAtDepth_succ (R : TriadicCube d) (k : ℕ) :
    ancestorAtDepth R (k + 1) = ancestorAtDepth (parentCube R) k := rfl

theorem ancestorAtDepth_scale (R : TriadicCube d) (k : ℕ) :
    (ancestorAtDepth R k).scale = R.scale + (k : ℤ) := by
  induction k generalizing R with
  | zero => simp
  | succ k ih =>
      rw [ancestorAtDepth_succ, ih (parentCube R), parentCube_scale]
      push_cast
      ring

/-- Every triadic cube is a child of its parent.  Unconditional. -/
theorem mem_childCubes_parentCube (R : TriadicCube d) : R ∈ childCubes (parentCube R) := by
  refine mem_childCubes_iff.mpr ⟨fun i => ⟨((R.index i + 1) % 3).toNat, ?_⟩, ?_⟩
  · have h : (R.index i + 1) % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  · have hdiv : ∀ x : ℤ, Int.ediv x 3 = x / 3 := fun _ => rfl
    cases R with
    | mk scale index =>
        refine congrArg₂ TriadicCube.mk (by simp [parentCube]) ?_
        funext i
        have hdm : 3 * ((index i + 1) / 3) + (index i + 1) % 3 = index i + 1 :=
          Int.mul_ediv_add_emod (index i + 1) 3
        have hnn : 0 ≤ (index i + 1) % 3 := Int.emod_nonneg _ (by norm_num)
        simp only [parentCube, hdiv]
        omega

/-- A cube is a depth-`k` descendant of its depth-`k` ancestor.  Unconditional. -/
theorem mem_descendantsAtDepth_ancestorAtDepth (R : TriadicCube d) (k : ℕ) :
    R ∈ descendantsAtDepth (ancestorAtDepth R k) k := by
  induction k generalizing R with
  | zero => simp
  | succ k ih =>
      rw [ancestorAtDepth_succ, mem_descendantsAtDepth_succ_iff]
      exact ⟨parentCube R, ih (parentCube R), mem_childCubes_parentCube R⟩

/-- **The scale-`m` ancestor of a triadic cube.**  For `R.scale <= m` this is the
unique scale-`m` cube of which `R` is a descendant; for `m < R.scale` it is `R`
itself and no statement below refers to that branch. -/
def ancestorAtScale (R : TriadicCube d) (m : ℤ) : TriadicCube d :=
  ancestorAtDepth R (m - R.scale).toNat

theorem ancestorAtScale_scale (R : TriadicCube d) {m : ℤ} (hm : R.scale ≤ m) :
    (ancestorAtScale R m).scale = m := by
  rw [ancestorAtScale, ancestorAtDepth_scale]
  omega

/-- **The descendant relation the ellipticity display consumes.**  Unconditional
apart from the existence of the ancestor. -/
theorem mem_descendantsAtScale_ancestorAtScale (R : TriadicCube d) {m : ℤ}
    (hm : R.scale ≤ m) : R ∈ descendantsAtScale (ancestorAtScale R m) R.scale := by
  have hsc : (ancestorAtScale R m).scale = m := ancestorAtScale_scale R hm
  rw [descendantsAtScale_eq_descendantsAtDepth _
      (by omega : R.scale ≤ (ancestorAtScale R m).scale), hsc]
  exact mem_descendantsAtDepth_ancestorAtDepth R _

/-! ## The ellipticity display at a free cap on the scale gap -/

/-- **The ellipticity display of Step 2 at a free cap.**  The manuscript's
literal `16` rests on `c_star <= 1`.  Only `c_star <= 3/2` is available here,
so the cap is carried as a parameter `B`; the printed statement is the case
`B = 16` and nothing in the proof depends on the numeral.

The exponent drop `s -> gamma` is the `s`-monotonicity half of
`e.ellipticities.monotone.ordered`; the cube step is
`e.bound.one.cube.by.lambdas`; and the descendant weight `3^{2 gamma (Q.scale-k)}`
is capped by `hgap`. -/
theorem gaugedEllipticitySum_descendant_le_of_gap [NeZero d] {Q R : TriadicCube d} {k : ℤ}
    (a : Ch02.TriadicCoeffFamily d) {gamma s sigmaBar B : ℝ}
    (hgamma : 0 < gamma) (hgs : gamma < s) (hsig : 0 < sigmaBar)
    (hR : R ∈ descendantsAtScale Q k)
    (hgap : 2 * gamma * (((Q.scale - k : ℤ) : ℝ)) ≤ B) :
    gaugedEllipticitySum sigmaBar R s a ≤
      Real.rpow (3 : ℝ) B * gaugedEllipticitySum sigmaBar Q gamma a := by
  set W : ℝ := Ch02.multiscaleDescendantWeight Q k gamma with hW
  have hq : (Ch02.MultiscaleExponent.finite 2).IsAdmissible := by norm_num
  have hs : 0 < s := lt_trans hgamma hgs
  have hUp1 : Ch02.LambdaSq R s (.finite 2) a ≤ Ch02.LambdaSq R gamma (.finite 2) a :=
    Ch02.LambdaSq_antitone R a hgamma hgs hq
  have hUp2 : Ch02.LambdaSq R gamma (.finite 2) a ≤
      W * Ch02.LambdaSq Q gamma (.finite 2) a :=
    Ch02.descendant_LambdaSq_le a hR hgamma hq
  have hlamR : 0 < Ch02.lambdaSq R gamma (.finite 2) a :=
    Ch02.lambdaSq_pos R a hgamma hq
  have hLo1 : (Ch02.lambdaSq R s (.finite 2) a)⁻¹ ≤
      (Ch02.lambdaSq R gamma (.finite 2) a)⁻¹ :=
    inv_anti₀ hlamR (Ch02.lambdaSq_mono R a hgamma hgs hq)
  have hLo2 : (Ch02.lambdaSq R gamma (.finite 2) a)⁻¹ ≤
      W * (Ch02.lambdaSq Q gamma (.finite 2) a)⁻¹ :=
    Ch02.descendant_lambdaSq_inv_le a hR hgamma hq
  have hWle : W ≤ Real.rpow (3 : ℝ) B := by
    rw [hW, Ch02.multiscaleDescendantWeight]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hgap
  have hsiginv : 0 ≤ sigmaBar⁻¹ := inv_nonneg.mpr hsig.le
  have hstep : gaugedEllipticitySum sigmaBar R s a ≤
      W * gaugedEllipticitySum sigmaBar Q gamma a := by
    unfold gaugedEllipticitySum
    have hA : sigmaBar⁻¹ * Ch02.LambdaSq R s (.finite 2) a ≤
        sigmaBar⁻¹ * (W * Ch02.LambdaSq Q gamma (.finite 2) a) :=
      mul_le_mul_of_nonneg_left (hUp1.trans hUp2) hsiginv
    have hB : sigmaBar * (Ch02.lambdaSq R s (.finite 2) a)⁻¹ ≤
        sigmaBar * (W * (Ch02.lambdaSq Q gamma (.finite 2) a)⁻¹) :=
      mul_le_mul_of_nonneg_left (hLo1.trans hLo2) hsig.le
    calc
      sigmaBar⁻¹ * Ch02.LambdaSq R s (.finite 2) a +
          sigmaBar * (Ch02.lambdaSq R s (.finite 2) a)⁻¹
          ≤ sigmaBar⁻¹ * (W * Ch02.LambdaSq Q gamma (.finite 2) a) +
              sigmaBar * (W * (Ch02.lambdaSq Q gamma (.finite 2) a)⁻¹) := add_le_add hA hB
      _ = W * (sigmaBar⁻¹ * Ch02.LambdaSq Q gamma (.finite 2) a +
              sigmaBar * (Ch02.lambdaSq Q gamma (.finite 2) a)⁻¹) := by ring
  have hsum_nn : 0 ≤ gaugedEllipticitySum sigmaBar Q gamma a :=
    gaugedEllipticitySum_nonneg Q a hsig.le hgamma
  exact hstep.trans (mul_le_mul_of_nonneg_right hWle hsum_nn)

/-! ## The per-cell transfer -/

/-- **The ancestor transfer, at the gauged sum.**  The gauged ellipticity sum of
a mesoscopic cell `R` at exponent `s` is controlled by that of `R`'s **own**
scale-`m` ancestor at exponent `gamma`, at the cost of `3^B` with `B` any cap on
the scaled gap `2 gamma (m - R.scale)`. -/
theorem gaugedEllipticitySum_le_ancestorAtScale [NeZero d] (R : TriadicCube d) {m : ℤ}
    (a : Ch02.TriadicCoeffFamily d) {gamma s sigmaBar B : ℝ}
    (hgamma : 0 < gamma) (hgs : gamma < s) (hsig : 0 < sigmaBar) (hm : R.scale ≤ m)
    (hgap : 2 * gamma * (((m - R.scale : ℤ) : ℝ)) ≤ B) :
    gaugedEllipticitySum sigmaBar R s a ≤
      Real.rpow (3 : ℝ) B *
        gaugedEllipticitySum sigmaBar (ancestorAtScale R m) gamma a := by
  refine gaugedEllipticitySum_descendant_le_of_gap a hgamma hgs hsig
    (mem_descendantsAtScale_ancestorAtScale R hm) ?_
  rwa [ancestorAtScale_scale R hm]

/-- **The composed Step-2 ellipticity input.**  The square of the per-cell
Poincare ellipticity factor is bounded by an absolute constant times the gauged
ellipticity sum of the cell's **own scale-`m` ancestor** at exponent `gamma`.

This is the shape the annealed Hoelder fold integrates once the stationarity
transport has moved the ancestor's moment back to `cu_m`; that transport is a
separate obligation and is not asserted here. -/
theorem doubledPoincareEllipticityFactor_sq_le_ancestorAtScale_gaugedEllipticitySum
    [NeZero d] (R : TriadicCube d) {m : ℤ} (a : Ch02.TriadicCoeffFamily d)
    {gamma s sig0 B : ℝ} (hgamma : 0 < gamma) (hgs : gamma < s) (hsig0 : 0 < sig0)
    (hm : R.scale ≤ m) (hgap : 2 * gamma * (((m - R.scale : ℤ) : ℝ)) ≤ B) :
    doubledPoincareEllipticityFactor sig0 R a s *
        doubledPoincareEllipticityFactor sig0 R a s ≤
      32 * (Ch03.poincareDiscountFactor s (.finite 2) *
          Ch03.poincareDiscountFactor s (.finite 2)) *
        (Real.rpow (3 : ℝ) B *
          gaugedEllipticitySum sig0 (ancestorAtScale R m) gamma a) := by
  have hs : 0 < s := lt_trans hgamma hgs
  have hstep := doubledPoincareEllipticityFactor_sq_le_gaugedEllipticitySum R a hs hsig0
  have htrans := gaugedEllipticitySum_le_ancestorAtScale R a hgamma hgs hsig0 hm hgap
  have hconst : (0 : ℝ) ≤ 32 * (Ch03.poincareDiscountFactor s (.finite 2) *
      Ch03.poincareDiscountFactor s (.finite 2)) := by
    have hc : (0 : ℝ) ≤ Ch03.poincareDiscountFactor s (.finite 2) *
        Ch03.poincareDiscountFactor s (.finite 2) := mul_self_nonneg _
    linarith
  exact hstep.trans (mul_le_mul_of_nonneg_left htrans hconst)

/-! ## The gate really holds at the recurrence's own scales -/

/-- **The scaled recurrence gap, in `c_star`-carrying form.**  From
`LocalizationParams.recurrenceMesoScale_budget`, `m - n <= (6 c_star + 2) gamma^{-1}`
at the corrected buffer `n = m - h - 32 ceil|log_3 gamma|`, hence
`2 gamma (m - n) <= 12 c_star + 4`.

Conditional on the source premise `h <= 6 c_star gamma^{-1}` and the coverage threshold
`hcover`.  `gamma <= 1` is derived from the standing
`ShellLawPrefix.gamma_le_quarter` and is not a binder. -/
theorem two_mul_gamma_mul_recurrenceGap_le (M : ABKModel d) (m : ℤ) (h : ℕ)
    (hcover : (((recurrenceGapMultiplier : ℕ) : ℝ) + 1) ^ 2 ≤ M.gamma⁻¹)
    (hshell : (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹) :
    2 * M.gamma *
        (((m - recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ) : ℤ)) : ℝ) ≤
      12 * Disorder.cstar M + 4 := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgamma1 : M.gamma ≤ 1 := le_trans M.shellPrefix.gamma_le_quarter (by norm_num)
  have hbudget := recurrenceMesoScale_budget (a := recurrenceGapMultiplier)
    (gamma := M.gamma) (cstar := Disorder.cstar M) m (h : ℤ) hgamma0 hgamma1 hcover hshell
  have hmul : 2 * M.gamma *
      (((m - recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ) : ℤ)) : ℝ) ≤
      2 * M.gamma * ((6 * Disorder.cstar M + 2) * M.gamma⁻¹) :=
    mul_le_mul_of_nonneg_left hbudget (by positivity)
  have hcancel : 2 * M.gamma * ((6 * Disorder.cstar M + 2) * M.gamma⁻¹) =
      12 * Disorder.cstar M + 4 := by
    field_simp
    ring
  linarith [hmul, hcancel.le, hcancel.ge]

/-- **The numerical gate of the ancestor transfer.**  With the proved
`Provider.Disorder.cstar_le_three_halves` the scaled recurrence gap is at most
`22`. -/
theorem two_mul_gamma_mul_recurrenceGap_le_twentyTwo (M : ABKModel d) (m : ℤ) (h : ℕ)
    (hcover : (((recurrenceGapMultiplier : ℕ) : ℝ) + 1) ^ 2 ≤ M.gamma⁻¹)
    (hshell : (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹) :
    2 * M.gamma *
        (((m - recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ) : ℤ)) : ℝ) ≤
      22 := by
  have h1 := two_mul_gamma_mul_recurrenceGap_le M m h hcover hshell
  have h2 := Provider.Disorder.cstar_le_three_halves M
  linarith

/-- **The per-cell transfer at the recurrence's own carriers.**  On a mesoscopic
cell `R` of the depth-`j` family of `cu_{Kc}` -- i.e. at the buffer scale `n =
recurrenceMesoScale 32 gamma m h` -- the square of the Poincare ellipticity
factor is `32 c_{s,2}^2 3^22` times the gauged ellipticity sum of `R`'s own
scale-`m` ancestor at exponent `gamma`. -/
theorem doubledPoincareEllipticityFactor_sq_le_recurrenceAncestor [NeZero d]
    (M : ABKModel d) (R : TriadicCube d) (m : ℤ) (h : ℕ)
    (a : Ch02.TriadicCoeffFamily d) {s sig0 : ℝ}
    (hsc : R.scale = recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ))
    (hgs : M.gamma < s) (hsig0 : 0 < sig0)
    (hcover : (((recurrenceGapMultiplier : ℕ) : ℝ) + 1) ^ 2 ≤ M.gamma⁻¹)
    (hshell : (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹) :
    doubledPoincareEllipticityFactor sig0 R a s *
        doubledPoincareEllipticityFactor sig0 R a s ≤
      32 * (Ch03.poincareDiscountFactor s (.finite 2) *
          Ch03.poincareDiscountFactor s (.finite 2)) *
        (Real.rpow (3 : ℝ) 22 *
          gaugedEllipticitySum sig0 (ancestorAtScale R m) M.gamma a) := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgap : 2 * M.gamma * (((m - R.scale : ℤ) : ℝ)) ≤ 22 := by
    rw [hsc]
    exact two_mul_gamma_mul_recurrenceGap_le_twentyTwo M m h hcover hshell
  have hm : R.scale ≤ m := by
    rw [hsc]
    have := recurrenceMesoScale_le recurrenceGapMultiplier M.gamma m (h : ℤ)
    omega
  exact doubledPoincareEllipticityFactor_sq_le_ancestorAtScale_gaugedEllipticitySum R a
    hgamma0 hgs hsig0 hm hgap

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
