/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DiagonalMass
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DominationPrincipleBarrier
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.Envelopes

/-!
# The global Monge--Ampere capacity of a big class

[Xia's capacity definition](https://github.com/MingchenXia/SGPT/blob/4390e77497d699ac3a4f878b97c34fc867513add/author/chapter_npp.tex#L299-L306)
associates a Monge–Ampère capacity with a closed real `(1,1)`-form `theta`:

  `Cap_theta(E) = sup { int_E theta^n_u : u in PSH(X, theta), V_theta - 1 <= u <= V_theta }`,

This module proves monotonicity, countable subadditivity and a domination
bound for `diagonalPotentialMeasure` using a fixed explicit reference. The
scaling estimate is related to [Xia's envelope concentration proof](https://github.com/MingchenXia/SGPT/blob/4390e77497d699ac3a4f878b97c34fc867513add/author/chapter_npp.tex#L769-L796),
where the background in the capacity is rescaled by `C⁻¹`.

The reference potential is an explicit argument `V` rather than hard-wired to
`V_theta`.  Xia's `Cap_theta` is the instance `V = thetaPshSupremum theta`,
which `Pending.thetaPshSupremum_isThetaPshPotential` makes a genuine
`theta`-PSH potential as soon as `PSH(X, theta)` is nonempty. The normalization is written
`u <= V` together with `V <= u + 1` instead of `V - 1 <= u <= V`, so that no
subtraction of extended reals occurs: on the pole set of `V` both readings
degenerate to `u = V = -infinity`.

The only analytic input is the diagonal domination along a convex combination,
`Pending.GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le`.
Everything here is `sorry`-free.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ThetaCapacity

open FirstPass FirstPass.PositiveClasses
open GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **The Monge--Ampere capacity of `E` relative to the reference potential
`V`.**  The competitors are the genuine `theta`-PSH potentials squeezed
between `V - 1` and `V`.  Xia's `Cap_theta` is the case `V = V_theta`. -/
def thetaCapacity (theta : ClosedRealOneOneForm n M) (V : M → EReal)
    (E : Set M) : ℝ≥0∞ :=
  ⨆ (u : M → EReal) (hu : IsThetaPshPotential theta.val u) (_ : u ≤ V)
    (_ : ∀ x, V x ≤ u x + 1), diagonalPotentialMeasure theta u hu E

omit [BorelSpace M] in
/-- Every competitor is bounded by the capacity. -/
theorem diagonalPotentialMeasure_le_thetaCapacity
    {theta : ClosedRealOneOneForm n M} {V u : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (h1 : u ≤ V)
    (h2 : ∀ x, V x ≤ u x + 1) (E : Set M) :
    diagonalPotentialMeasure theta u hu E ≤ thetaCapacity theta V E :=
  le_iSup₂_of_le (f := fun u hu => ⨆ (_ : u ≤ V) (_ : ∀ x, V x ≤ u x + 1),
    diagonalPotentialMeasure theta u hu E) u hu
    (le_iSup_of_le h1 (le_iSup_of_le h2 le_rfl))

omit [BorelSpace M] in
/-- The universal property of the capacity. -/
theorem thetaCapacity_le_of_forall {theta : ClosedRealOneOneForm n M}
    {V : M → EReal} {E : Set M} {c : ℝ≥0∞}
    (h : ∀ (u : M → EReal) (hu : IsThetaPshPotential theta.val u), u ≤ V →
      (∀ x, V x ≤ u x + 1) → diagonalPotentialMeasure theta u hu E ≤ c) :
    thetaCapacity theta V E ≤ c :=
  iSup₂_le fun u hu => iSup_le fun h1 => iSup_le fun h2 => h u hu h1 h2

omit [BorelSpace M] in
/-- Monotonicity in the set. -/
theorem thetaCapacity_mono {theta : ClosedRealOneOneForm n M} {V : M → EReal}
    {E F : Set M} (hEF : E ⊆ F) :
    thetaCapacity theta V E ≤ thetaCapacity theta V F :=
  thetaCapacity_le_of_forall fun _u hu h1 h2 =>
    (measure_mono hEF).trans (diagonalPotentialMeasure_le_thetaCapacity hu h1 h2 F)

omit [BorelSpace M] in
@[simp] theorem thetaCapacity_empty (theta : ClosedRealOneOneForm n M)
    (V : M → EReal) : thetaCapacity theta V (∅ : Set M) = 0 :=
  le_antisymm (thetaCapacity_le_of_forall fun _u _hu _ _ => by simp) zero_le

omit [BorelSpace M] in
/-- Countable subadditivity. -/
theorem thetaCapacity_iUnion_le {ι : Type*} [Countable ι]
    (theta : ClosedRealOneOneForm n M) (V : M → EReal) (E : ι → Set M) :
    thetaCapacity theta V (⋃ i, E i) ≤ ∑' i, thetaCapacity theta V (E i) :=
  thetaCapacity_le_of_forall fun _u hu h1 h2 =>
    (measure_iUnion_le E).trans (tsum_le_tsum fun i =>
      diagonalPotentialMeasure_le_thetaCapacity hu h1 h2 (E i))

omit [BorelSpace M] in
theorem thetaCapacity_union_le (theta : ClosedRealOneOneForm n M)
    (V : M → EReal) (E F : Set M) :
    thetaCapacity theta V (E ∪ F) ≤
      thetaCapacity theta V E + thetaCapacity theta V F :=
  thetaCapacity_le_of_forall fun _u hu h1 h2 =>
    (measure_union_le E F).trans (add_le_add
      (diagonalPotentialMeasure_le_thetaCapacity hu h1 h2 E)
      (diagonalPotentialMeasure_le_thetaCapacity hu h1 h2 F))

/-! ## Domination of bounded potentials -/

/-- A convex combination of a potential with itself is that potential. -/
theorem convexComb_self {N : Type*} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (v : N → EReal) : convexComb t v v = v := by
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  funext x
  rw [convexComb_apply]
  induction v x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos ht0, EReal.coe_mul_bot_of_pos ht1']; simp
  | top => rw [EReal.coe_mul_top_of_pos ht0, EReal.coe_mul_top_of_pos ht1']; simp
  | coe r =>
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    ring

/-- **Domination of the non-pluripolar measure by the capacity.**  If `u` is a
genuine `theta`-PSH potential with `V - C <= u <= V` for some `C >= 1`, then
`theta^n_u(E) <= C^n Cap_theta(E, V)` for every `E`. This is an explicit-reference
estimate in the original background, related to the use of the rescaled capacity in
[Xia's envelope concentration proof](https://github.com/MingchenXia/SGPT/blob/4390e77497d699ac3a4f878b97c34fc867513add/author/chapter_npp.tex#L769-L796).

The competitor is `C^{-1} u + (1 - C^{-1}) V`, which is squeezed between
`V - 1` and `V`; the scaling
`C^{-n} theta^n_u <= theta^n_{C^{-1} u + (1 - C^{-1}) V}` is the diagonal
convex-combination domination. -/
theorem diagonalPotentialMeasure_le_thetaCapacity_of_bounds
    {theta : ClosedRealOneOneForm n M} {V u : M → EReal}
    (hV : IsThetaPshPotential theta.val V) (hu : IsThetaPshPotential theta.val u)
    {C : ℝ} (hC : 1 ≤ C) (hle : u ≤ V) (hlb : ∀ x, V x ≤ u x + (C : EReal))
    (E : Set M) :
    diagonalPotentialMeasure theta u hu E ≤
      ENNReal.ofReal (C ^ n) * thetaCapacity theta V E := by
  rcases eq_or_lt_of_le hC with hC1 | hC1
  · -- `C = 1`: `u` is itself a competitor.
    have hone : (C : EReal) = 1 := by rw [← hC1]; norm_num
    have h2 : ∀ x, V x ≤ u x + 1 := by
      intro x; simpa [hone] using hlb x
    have := diagonalPotentialMeasure_le_thetaCapacity hu hle h2 E
    simpa [← hC1] using this
  · have hC0 : 0 < C := lt_trans zero_lt_one hC1
    set t : ℝ := C⁻¹ with ht_def
    have ht0 : 0 < t := inv_pos.mpr hC0
    have ht1 : t < 1 := by
      rw [ht_def, inv_lt_one_iff₀]; exact Or.inr hC1
    have htC : t * C = 1 := inv_mul_cancel₀ hC0.ne'
    have hw : IsThetaPshPotential theta.val (convexComb t u V) :=
      isThetaPshPotential_convexComb hu hV ht0 ht1
    have hwV : convexComb t u V ≤ V := by
      refine le_trans (convexComb_mono ht0.le ht1.le hle le_rfl) ?_
      rw [convexComb_self ht0 ht1]
    have hVw : ∀ x, V x ≤ convexComb t u V x + 1 := by
      have ht1' : (0 : ℝ) < 1 - t := by linarith
      intro x
      rcases eq_or_ne (u x) ⊥ with hbot | hbot
      · have hVbot : V x = ⊥ := by
          have h := hlb x
          rw [hbot] at h
          simpa using h
        rw [convexComb_apply, hbot, hVbot, EReal.coe_mul_bot_of_pos ht0,
          EReal.coe_mul_bot_of_pos ht1']
        simp
      · have hutop : u x ≠ ⊤ :=
          Pending.DominationPrincipleBarrier.ne_top_of_isThetaPshPotential hu x
        have hVtop : V x ≠ ⊤ :=
          Pending.DominationPrincipleBarrier.ne_top_of_isThetaPshPotential hV x
        have hVbot : V x ≠ ⊥ := fun h => hbot (le_bot_iff.mp (h ▸ hle x))
        obtain ⟨r, hr⟩ : ∃ r : ℝ, u x = (r : EReal) :=
          ⟨(u x).toReal, (EReal.coe_toReal hutop hbot).symm⟩
        obtain ⟨s, hs⟩ : ∃ s : ℝ, V x = (s : EReal) :=
          ⟨(V x).toReal, (EReal.coe_toReal hVtop hVbot).symm⟩
        have hrs : r ≤ s := by
          have h := hle x; rw [hr, hs] at h; exact EReal.coe_le_coe_iff.mp h
        have hsr : s ≤ r + C := by
          have h := hlb x; rw [hr, hs, ← EReal.coe_add] at h
          exact EReal.coe_le_coe_iff.mp h
        rw [convexComb_apply, hr, hs, ← EReal.coe_mul, ← EReal.coe_mul,
          ← EReal.coe_add, ← EReal.coe_one, ← EReal.coe_add, EReal.coe_le_coe_iff]
        nlinarith [mul_le_mul_of_nonneg_left hsr ht0.le]
    have key := globalMixedMeasure_diagonal_convexComb_le hu hV ht0 ht1 E
    have hcap : diagonalPotentialMeasure theta (convexComb t u V) hw E ≤
        thetaCapacity theta V E :=
      diagonalPotentialMeasure_le_thetaCapacity hw hwV hVw E
    have hstep : ENNReal.ofReal (t ^ n) * diagonalPotentialMeasure theta u hu E ≤
        thetaCapacity theta V E := le_trans key hcap
    have hunit : ENNReal.ofReal (C ^ n) * ENNReal.ofReal (t ^ n) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow, mul_comm C t, htC,
        one_pow, ENNReal.ofReal_one]
    calc diagonalPotentialMeasure theta u hu E
        = ENNReal.ofReal (C ^ n) * (ENNReal.ofReal (t ^ n) *
            diagonalPotentialMeasure theta u hu E) := by
          rw [← mul_assoc, hunit, one_mul]
      _ ≤ ENNReal.ofReal (C ^ n) * thetaCapacity theta V E := by gcongr

/-- **Pluripolar sets have zero capacity.**  Every competitor measure is a
non-pluripolar product, so it gives no mass to a manifold-locally-pluripolar
set. -/
theorem thetaCapacity_eq_zero_of_manifoldLocallyPluripolar
    {theta : ClosedRealOneOneForm n M} (V : M → EReal) {E : Set M}
    (hE : FirstPass.ManifoldLocallyPluripolar (n := n) E) :
    thetaCapacity theta V E = 0 :=
  le_antisymm (thetaCapacity_le_of_forall fun _u hu _ _ =>
    le_of_eq (globalMixedMeasure_doesNotChargeManifoldPluripolar
      (fun _ : Fin n => hu.1) E hE)) zero_le

/-! ## Xia's `Cap_theta` -/

/-- **Xia's Monge--Ampere capacity `Cap_theta`**, the capacity relative to the
canonical least singular potential `V_theta = thetaPshSupremum theta`. -/
def thetaCapacityV (theta : ClosedRealOneOneForm n M) (E : Set M) : ℝ≥0∞ :=
  thetaCapacity theta (thetaPshSupremum theta.val) E

/-- **Domination by `Cap_theta`.**  A normalized `theta`-PSH potential within
distance `C` of `V_theta` has `theta^n_u(E) <= C^n Cap_theta(E)`.  No smooth
local potential hypothesis is needed: the `theta`-PSH potential `u` supplies
one, and `theta` already carries closedness and type `(1,1)`. -/
theorem diagonalPotentialMeasure_le_thetaCapacityV [Nonempty M]
    {theta : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hu0 : u ≤ 0) {C : ℝ} (hC : 1 ≤ C)
    (hlb : ∀ x, thetaPshSupremum theta.val x ≤ u x + (C : EReal)) (E : Set M) :
    diagonalPotentialMeasure theta u hu E ≤
      ENNReal.ofReal (C ^ n) * thetaCapacityV theta E := by
  have hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val) :=
    SGPT.Foundations.Analysis.Pending.thetaPshSupremum_isThetaPshPotential theta.val
      hu.1.hasSmoothLocalPotentials ⟨u, hu⟩
  exact diagonalPotentialMeasure_le_thetaCapacity_of_bounds hV hu hC
    (le_thetaPshSupremum hu hu0) hlb E

/-- A set of zero capacity carries no mass for any potential within a finite
distance of the reference. -/
theorem diagonalPotentialMeasure_eq_zero_of_thetaCapacity_eq_zero
    {theta : ClosedRealOneOneForm n M} {V u : M → EReal}
    (hV : IsThetaPshPotential theta.val V) (hu : IsThetaPshPotential theta.val u)
    {C : ℝ} (hC : 1 ≤ C) (hle : u ≤ V) (hlb : ∀ x, V x ≤ u x + (C : EReal))
    {E : Set M} (hE : thetaCapacity theta V E = 0) :
    diagonalPotentialMeasure theta u hu E = 0 := by
  refine le_antisymm ?_ zero_le
  simpa [hE] using
    diagonalPotentialMeasure_le_thetaCapacity_of_bounds hV hu hC hle hlb E

end

end SGPT.Foundations.Analysis.Pending.ThetaCapacity
