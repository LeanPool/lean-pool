/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.IteratedDerivBridge
public import LeanPool.CIVAxisymmetric.Reduction.AnalyticPredicates
public import LeanPool.CIVAxisymmetric.Reduction.AxisymmetryFromCore
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Exterior vanishing and analyticity (`rem:exterior:nonanalytic`)

A second obstruction to the analyticity of the force, using neither the anisotropic bounds
nor the axisymmetric core: only an open set off the axis on which the meridional velocity
vanishes.

Let `(u, π)` solve `eq:nse:forced` on `B(R) × (−δ, 0)`, smooth on compact subsets, and let
`E ⊆ B(R) ∩ {r > 0}` be a nonempty open set on which `u_r = u_z = 0` at every time of
`(−δ, 0)` (`eq:exterior:vanishing`). If `u_z(0, t₀) ≠ 0` at some `t₀ ∈ (−δ, 0)`, then on every
ball `B(R')` with `0 < R' ≤ R` meeting `E`, and for every `t₁ ∈ (−δ, t₀)`, the force admits no
constants `M`, `a > 0` in the factorial bound `eq:exterior:force:analytic:local`; in
particular `f` does not vanish identically on `B(R') × (t₁, t₀)`.

The proof is the printed one. If the factorial bound held, `lem:analytic:slice` would make
`u(·, t)` real analytic on `B(R')` for every `t ∈ (t₁, t₀)`. At each such `t` the scalar
`u_z(·, t)` vanishes on the nonempty open set `E ∩ B(R')`, hence on all of `B(R')` by the
identity theorem, and in particular `u_z(0, t) = 0`. Letting `t ↑ t₀` and using the continuity
of `u_z(0, ·)` gives `u_z(0, t₀) = 0`, a contradiction.

The cylindrical coefficients are read in the Cartesian frame as in design note R7: `u_z` is
the third Cartesian component, and `r u_r = x₀u₀ + x₁u₁` with `r = √(x₀² + x₁²)`, so that the
first half of `eq:exterior:vanishing` reads `(x₀u₀ + x₁u₁)/r = 0`.

`thm:analytic:interior` — the input of `lem:analytic:slice` — is the hypothesis `hinterior`,
which is exactly the statement of `CIV.interiorAnalyticity` for the triple `(u, π, f)`; it is
carried as a hypothesis here; `CIV.exteriorNonanalytic`
(CIV/Reduction/ExteriorNonanalyticUnconditional.lean) discharges it with
`CIV.Main.interiorAnalyticity`.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Continuity of a time slice -/

/-- A component of a field that is smooth on an open space-time set is continuous in time at
every point of that set. -/
private theorem continuousAt_timeSlice_component {g : ParabolicPoint → Vec3}
    {S : Set (Vec3 × ℝ)} (hS : IsOpen S)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => g w) S) {x : Vec3} {t : ℝ}
    (hmem : (x, t) ∈ S) (i : Fin 3) :
    ContinuousAt (fun s : ℝ => g (x, s) i) t := by
  have hjoint : ContinuousAt (fun w : Vec3 × ℝ => g w) (x, t) :=
    (hg.contDiffAt (hS.mem_nhds hmem)).continuousAt
  have hline : ContinuousAt (fun s : ℝ => ((x, s) : Vec3 × ℝ)) t :=
    (continuous_const.prodMk continuous_id).continuousAt
  exact ((continuous_apply i).continuousAt).comp (hjoint.comp hline)

/-- A function that is continuous at a point of `[t₁, t₀]` and vanishes on `(t₁, t₀)` vanishes
at that point as well: the open interval is dense in the closed one. -/
private theorem eq_zero_of_continuousAt_of_eqOn_zero_Ioo {F : ℝ → ℝ} {t₁ t₀ t : ℝ}
    (hlt : t₁ < t₀) (hc : ContinuousAt F t) (ht : t ∈ Icc t₁ t₀)
    (hz : ∀ s ∈ Ioo t₁ t₀, F s = 0) : F t = 0 := by
  have hcl : t ∈ closure (Ioo t₁ t₀) := by
    rw [closure_Ioo hlt.ne]
    exact ht
  have hne : (𝓝[Ioo t₁ t₀] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have h1 : Tendsto F (𝓝[Ioo t₁ t₀] t) (𝓝 (F t)) := hc.continuousWithinAt.tendsto
  have h2 : Tendsto F (𝓝[Ioo t₁ t₀] t) (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs using (hz s hs).symm
  exact tendsto_nhds_unique h1 h2

/-! ### The identity theorem on a ball centred on the axis -/

/-- **The identity theorem on a ball centred on the axis** (`the source`). A real analytic scalar on
`B(R')` which vanishes on a nonempty open subset of `B(R')` vanishes on all of `B(R')`; the
ball is convex, hence preconnected. -/
theorem eqOn_zero_vec3Ball_of_analyticOnNhd {g : Vec3 → ℝ} {R' : ℝ} {V : Set Vec3}
    (hg : AnalyticOnNhd ℝ g (vec3Ball 0 R')) (hV : IsOpen V) (hVsub : V ⊆ vec3Ball 0 R')
    (hVne : V.Nonempty) (hzero : ∀ x ∈ V, g x = 0) :
    ∀ x ∈ vec3Ball (0 : Vec3) R', g x = 0 := by
  obtain ⟨x₀, hx₀⟩ := hVne
  have hev : g =ᶠ[𝓝 x₀] 0 := by
    filter_upwards [hV.mem_nhds hx₀] with y hy using hzero y hy
  have hEq := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isPreconnected_vec3Ball_zero R') (hVsub hx₀) hev
  intro x hx
  simpa using hEq hx

/-! ### Derivatives of a field vanishing on a spatial ball -/

/-- Iterated spatial partial derivatives in one fixed direction vanish on a ball on which the
field vanishes at the given time. -/
private theorem iterate_spatialPartial_eq_zero_of_eqOn_zero_ball {g : ParabolicPoint → ℝ}
    {R' t : ℝ} (h : ∀ y ∈ vec3Ball (0 : Vec3) R', g (y, t) = 0) (i : Fin 3) (n : ℕ) :
    ∀ y ∈ vec3Ball (0 : Vec3) R', ((fun k => spatialPartial k i)^[n] g) (y, t) = 0 := by
  induction n with
  | zero => simpa using h
  | succ m ih =>
    intro y hy
    have hstep : ((fun k => spatialPartial k i)^[m + 1] g) (y, t)
        = spatialPartial ((fun k => spatialPartial k i)^[m] g) i (y, t) := by
      rw [Function.iterate_succ']
      rfl
    rw [hstep]
    show fderiv ℝ (fun w : Vec3 => ((fun k => spatialPartial k i)^[m] g) (w, t)) y
      (basisVec i) = 0
    have hev : (fun w : Vec3 => ((fun k => spatialPartial k i)^[m] g) (w, t))
        =ᶠ[𝓝 y] (fun _ : Vec3 => (0 : ℝ)) := by
      filter_upwards [(isOpen_vec3Ball (0 : Vec3) R').mem_nhds hy] with w hw using ih w hw
    rw [hev.fderiv_eq]
    simp

/-- Every multi-index spatial derivative of a field vanishes on a ball on which the field
vanishes at the given time. -/
private theorem multiPartial_eq_zero_of_eqOn_zero_ball {g : ParabolicPoint → ℝ} {R' t : ℝ}
    (h : ∀ y ∈ vec3Ball (0 : Vec3) R', g (y, t) = 0) (α : Fin 3 → ℕ) {x : Vec3}
    (hx : x ∈ vec3Ball (0 : Vec3) R') :
    multiPartial g α (x, t) = 0 := by
  have h2 := iterate_spatialPartial_eq_zero_of_eqOn_zero_ball h 2 (α 2)
  have h1 := iterate_spatialPartial_eq_zero_of_eqOn_zero_ball h2 1 (α 1)
  exact iterate_spatialPartial_eq_zero_of_eqOn_zero_ball h1 0 (α 0) x hx

/-! ### The obstruction -/

/-- **Exterior vanishing and analyticity** (`rem:exterior:nonanalytic`,
`eq:exterior:force:analytic:local`). Let `(u, π)` be a solution of `eq:nse:forced` on
`B(R) × (−δ, 0)`, smooth on compact subsets, and let `E` be a nonempty open subset of
`B(R) ∩ {r > 0}` on which `u_r = u_z = 0` at every time of `(−δ, 0)`. Suppose `u_z(0, t₀) ≠ 0`
for some `t₀ ∈ (−δ, 0)`. Then on every ball `B(R')` with `0 < R' ≤ R` which meets `E`, and for
every `t₁ ∈ (−δ, t₀)`, there are no constants `M` and `a > 0` with

`sup_{t ∈ [t₁, t₀]} ‖∂_x^α f(·, t)‖_{L^∞(B(R'))} ≤ M a^{−|α|} |α|!` for all `α`.

The hypothesis `hinterior` is `thm:analytic:interior` for the triple `(u, π, f)`, the input of
`lem:analytic:slice`; it is discharged by `CIV.interiorAnalyticity`. -/
theorem not_exists_analyticBoundOn_of_exteriorVanishing
    {R δ t₀ R' t₁ : ℝ} {E : Set Vec3} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f (spaceTimeSet (vec3Ball 0 R) (Ioo (-δ) 0)))
    (hEopen : IsOpen E)
    (hvanish : ∀ x ∈ E, ∀ t ∈ Ioo (-δ) 0,
      (x 0 * u (x, t) 0 + x 1 * u (x, t) 1) / Real.sqrt (x 0 ^ 2 + x 1 ^ 2) = 0
        ∧ u (x, t) 2 = 0)
    (ht₀ : t₀ ∈ Ioo (-δ) 0) (haxis : u ((0 : Vec3), t₀) 2 ≠ 0)
    (hR' : 0 < R') (hR'R : R' ≤ R) (hmeet : (E ∩ vec3Ball (0 : Vec3) R').Nonempty)
    (ht₁ : t₁ ∈ Ioo (-δ) t₀)
    (hinterior : ∀ S s₁ s₂ : ℝ, 0 < S → s₁ < s₂ →
      IsClassicalSolutionOn u p f (spaceTimeSet (vec3Ball 0 S) (Ioo s₁ s₂)) →
      LocallyUniformlyAnalyticOn f S s₁ s₂ → LocallyUniformlyAnalyticOn u S s₁ s₂) :
    ¬ ∃ M a : ℝ, 0 < a ∧ AnalyticBoundOn f R' (Icc t₁ t₀) M a := by
  rintro ⟨M, a, ha, hbound⟩
  have hR : 0 < R := lt_of_lt_of_le hR' hR'R
  have hsubsmall : ∀ t ∈ Icc t₁ t₀, t ∈ Ioo (-δ) 0 := fun t ht =>
    ⟨lt_of_lt_of_le ht₁.1 ht.1, lt_of_le_of_lt ht.2 ht₀.2⟩
  have hsub : spaceTimeSet (vec3Ball 0 R') (Ioo t₁ t₀)
      ⊆ spaceTimeSet (vec3Ball 0 R) (Ioo (-δ) 0) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨vec3Ball_mono hR'R hx, hsubsmall t (Ioo_subset_Icc_self ht)⟩
  have hsol' := hsol.mono hsub
  have hLUu : LocallyUniformlyAnalyticOn u R' t₁ t₀ :=
    hinterior R' t₁ t₀ hR' ht₁.2 hsol'
      (locallyUniformlyAnalyticOn_of_analyticBoundOn hbound ha)
  have hanalytic : ∀ t ∈ Ioo t₁ t₀, ∀ i : Fin 3,
      AnalyticOnNhd ℝ (fun x : Vec3 => u (x, t) i) (vec3Ball 0 R') :=
    analyticOnNhd_slice_of_locallyUniformlyAnalyticOn hsol'.1 hLUu
  have hzero : ∀ t ∈ Ioo t₁ t₀, u ((0 : Vec3), t) 2 = 0 := by
    intro t ht
    refine eqOn_zero_vec3Ball_of_analyticOnNhd (hanalytic t ht 2)
      (hEopen.inter (isOpen_vec3Ball 0 R')) inter_subset_right hmeet
      (fun x hx => (hvanish x hx.1 t (hsubsmall t (Ioo_subset_Icc_self ht))).2)
      0 (zero_mem_vec3Ball_zero hR')
  have hopen : IsOpen ((vec3Ball (0 : Vec3) R) ×ˢ (Ioo (-δ) 0) : Set (Vec3 × ℝ)) :=
    (isOpen_vec3Ball 0 R).prod isOpen_Ioo
  have hu' : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w)
      ((vec3Ball (0 : Vec3) R) ×ˢ (Ioo (-δ) 0) : Set (Vec3 × ℝ)) := hsol.1
  have hcont : ContinuousAt (fun s : ℝ => u ((0 : Vec3), s) 2) t₀ :=
    continuousAt_timeSlice_component hopen hu' ⟨zero_mem_vec3Ball_zero hR, ht₀⟩ 2
  exact haxis (eq_zero_of_continuousAt_of_eqOn_zero_Ioo ht₁.2 hcont
    (right_mem_Icc.2 ht₁.2.le) hzero)

/-- The force of `rem:exterior:nonanalytic` does not vanish identically on `B(R') × (t₁, t₀)`,
since the zero force satisfies `eq:exterior:force:analytic:local` with `M = 0` and `a = 1`. -/
theorem not_eqOn_zero_of_exteriorVanishing
    {R δ t₀ R' t₁ : ℝ} {E : Set Vec3} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f (spaceTimeSet (vec3Ball 0 R) (Ioo (-δ) 0)))
    (hEopen : IsOpen E)
    (hvanish : ∀ x ∈ E, ∀ t ∈ Ioo (-δ) 0,
      (x 0 * u (x, t) 0 + x 1 * u (x, t) 1) / Real.sqrt (x 0 ^ 2 + x 1 ^ 2) = 0
        ∧ u (x, t) 2 = 0)
    (ht₀ : t₀ ∈ Ioo (-δ) 0) (haxis : u ((0 : Vec3), t₀) 2 ≠ 0)
    (hR' : 0 < R') (hR'R : R' ≤ R) (hmeet : (E ∩ vec3Ball (0 : Vec3) R').Nonempty)
    (ht₁ : t₁ ∈ Ioo (-δ) t₀)
    (hinterior : ∀ S s₁ s₂ : ℝ, 0 < S → s₁ < s₂ →
      IsClassicalSolutionOn u p f (spaceTimeSet (vec3Ball 0 S) (Ioo s₁ s₂)) →
      LocallyUniformlyAnalyticOn f S s₁ s₂ → LocallyUniformlyAnalyticOn u S s₁ s₂) :
    ¬ ∀ z ∈ spaceTimeSet (vec3Ball 0 R') (Ioo t₁ t₀), f z = 0 := by
  intro hf0
  refine not_exists_analyticBoundOn_of_exteriorVanishing hsol hEopen hvanish
    ht₀ haxis hR' hR'R hmeet ht₁ hinterior ⟨0, 1, one_pos, ?_⟩
  have hR : 0 < R := lt_of_lt_of_le hR' hR'R
  have hsubsmall : ∀ t ∈ Icc t₁ t₀, t ∈ Ioo (-δ) 0 := fun t ht =>
    ⟨lt_of_lt_of_le ht₁.1 ht.1, lt_of_le_of_lt ht.2 ht₀.2⟩
  have hopen : IsOpen ((vec3Ball (0 : Vec3) R) ×ˢ (Ioo (-δ) 0) : Set (Vec3 × ℝ)) :=
    (isOpen_vec3Ball 0 R).prod isOpen_Ioo
  have hf' : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => f w)
      ((vec3Ball (0 : Vec3) R) ×ˢ (Ioo (-δ) 0) : Set (Vec3 × ℝ)) := hsol.2.2.1
  intro α t ht x hx i
  have hslice : ∀ y ∈ vec3Ball (0 : Vec3) R', (fun w : ParabolicPoint => f w i) (y, t) = 0 := by
    intro y hy
    have hyR : y ∈ vec3Ball (0 : Vec3) R := vec3Ball_mono hR'R hy
    have hcont : ContinuousAt (fun s : ℝ => f (y, s) i) t :=
      continuousAt_timeSlice_component hopen hf' ⟨hyR, hsubsmall t ht⟩ i
    refine eq_zero_of_continuousAt_of_eqOn_zero_Ioo ht₁.2 hcont ht fun s hs => ?_
    exact congrFun (hf0 ((y, s) : ParabolicPoint) ⟨hy, hs⟩) i
  rw [multiPartial_eq_zero_of_eqOn_zero_ball hslice α hx]
  simp

end CIV
