/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PartTorsion

/-!
# PartGreenPotential

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The vanishing-shift limit of the Dirichlet resolvents of a bounded part domain

The Dirichlet resolvents `R^V_lam f` of a fixed bounded measurable datum on a bounded open convex
domain converge as the shift decreases to zero.  The two inputs are the shift-uniform bound and
the Lipschitz estimate in the shift of `PartTorsion.lean`; a Lipschitz real family on the
positive half-line converges as its argument decreases to zero, with an error proportional to
the argument.

The limit is `partGreenPotential`; it vanishes off the domain, obeys the same uniform bound, is
measurable, and is continuous on the domain, being a uniform limit there of the Dirichlet
resolvents.

This is the statement of `ExitMeanValueHarmonicPotential.lean` with the exhaustion cube replaced
by an arbitrary bounded open convex domain.  The identification of `partGreenPotential` with the
zero-trace weak solution of the unshifted Dirichlet problem is a separate question and is not
addressed here.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- A quantity below a fixed bound plus an arbitrarily small multiple of a nonnegative constant
is below the fixed bound. -/
private theorem le_of_forall_pos_add_mul_part {a B K : ℝ} (hK : 0 ≤ K)
    (h : ∀ lam : ℝ, 0 < lam → a ≤ B + K * lam) : a ≤ B := by
  refine le_of_forall_pos_le_add fun eps heps ↦ ?_
  have hlam : (0 : ℝ) < eps / (K + 1) := by positivity
  have hstep := h _ hlam
  have hKle : K * (eps / (K + 1)) ≤ eps := by
    have hrw : K * (eps / (K + 1)) = K * eps / (K + 1) := by ring
    rw [hrw, div_le_iff₀ (by positivity : (0 : ℝ) < K + 1)]
    linarith only [heps.le, mul_nonneg hK heps.le]
  linarith only [hstep, hKle]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-! ## The shift-indexed Dirichlet resolvent -/

/-- **The Dirichlet resolvent of a bounded measurable datum on a bounded part domain**, as a
function of the shift; the value at a non-positive shift is zero. -/
def partShiftResolvent {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) (f : Vec d → ℝ)
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (lam : ℝ) (x : Vec d) : ℝ :=
  if h : 0 < lam then A.partC0Resolvent hV ⟨lam, h⟩ f hf hfD x else 0

theorem partShiftResolvent_of_pos {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) {lam : ℝ}
    (hlam : 0 < lam) (x : Vec d) :
    A.partShiftResolvent hV f hf hfD lam x = A.partC0Resolvent hV ⟨lam, hlam⟩ f hf hfD x := by
  rw [partShiftResolvent, dite_eq_left hlam]

theorem abs_partShiftResolvent_le {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D)
    (lam : ℝ) (x : Vec d) :
    |A.partShiftResolvent hV f hf hfD lam x| ≤ D * A.partTorsionBound hV := by
  rw [partShiftResolvent]
  split_ifs with hlam
  · exact A.abs_partC0Resolvent_le_partTorsionBound hV ⟨lam, hlam⟩ hf hD hfD x
  · rw [abs_zero]
    exact mul_nonneg hD (A.partTorsionBound_nonneg hV)

theorem partShiftResolvent_of_notMem {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (lam : ℝ)
    {x : Vec d} (hx : x ∉ V) :
    A.partShiftResolvent hV f hf hfD lam x = 0 := by
  rw [partShiftResolvent]
  split_ifs with hlam
  · exact A.partC0Resolvent_of_notMem hV ⟨lam, hlam⟩ f hf hfD hx
  · rfl

theorem partShiftResolvent_nonneg {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (lam : ℝ) (x : Vec d) :
    0 ≤ A.partShiftResolvent hV f hf hfD lam x := by
  rw [partShiftResolvent]
  split_ifs with hlam
  · exact A.partC0Resolvent_nonneg hV ⟨lam, hlam⟩ f hf hf0 hfD x
  · exact le_rfl

theorem partShiftResolvent_eq_of_eqOn {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E) (hfg : Set.EqOn f g V) (lam : ℝ)
    (x : Vec d) :
    A.partShiftResolvent hV f hf hfD lam x = A.partShiftResolvent hV g hg hgE lam x := by
  rw [partShiftResolvent, partShiftResolvent]
  split_ifs with hlam
  · exact A.partC0Resolvent_eq_of_eqOn hV ⟨lam, hlam⟩ hf hg hfD hgE hfg x
  · rfl

/-- The Lipschitz constant in the shift of the Dirichlet resolvents of a datum bounded by `D` on
a bounded part domain. -/
def partGreenRate {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) (D : ℝ) : ℝ :=
  D * (A.partTorsionBound hV * A.partTorsionBound hV)

theorem partGreenRate_nonneg {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) {D : ℝ}
    (hD : 0 ≤ D) : 0 ≤ A.partGreenRate hV D :=
  mul_nonneg hD (mul_nonneg (A.partTorsionBound_nonneg hV) (A.partTorsionBound_nonneg hV))

/-- **The Dirichlet resolvents of a fixed bounded datum on a bounded part domain converge as the
shift decreases to zero.**  The limit is approached at a rate proportional to the shift. -/
theorem exists_forall_abs_partShiftResolvent_sub_le {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    ∃ c : ℝ, ∀ lam : ℝ, 0 < lam →
      |A.partShiftResolvent hV f hf hfD lam x - c| ≤ A.partGreenRate hV D * lam := by
  refine exists_forall_abs_sub_le_of_lipschitz (A.partGreenRate_nonneg hV hD)
    fun lam nu hlam hnu ↦ ?_
  rw [A.partShiftResolvent_of_pos hV hf hfD hlam, A.partShiftResolvent_of_pos hV hf hfD hnu]
  exact A.abs_partC0Resolvent_sub_le hV ⟨lam, hlam⟩ ⟨nu, hnu⟩ hf hD hfD x

/-! ## The Green potential -/

/-- **The Green potential of a bounded measurable datum on a bounded part domain**: the limit of
its Dirichlet resolvents as the shift decreases to zero. -/
def partGreenPotential {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) (f : Vec d → ℝ)
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (x : Vec d) : ℝ :=
  Classical.choose (A.exists_forall_abs_partShiftResolvent_sub_le hV hf hD hfD x)

theorem abs_partShiftResolvent_sub_partGreenPotential_le {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (x : Vec d) {lam : ℝ} (hlam : 0 < lam) :
    |A.partShiftResolvent hV f hf hfD lam x - A.partGreenPotential hV f hf hD hfD x| ≤
      A.partGreenRate hV D * lam :=
  Classical.choose_spec (A.exists_forall_abs_partShiftResolvent_sub_le hV hf hD hfD x) lam hlam

/-- **The Dirichlet resolvents converge to the Green potential as the shift decreases to
zero.** -/
theorem tendsto_partShiftResolvent_nhdsGT_zero {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    Tendsto (fun lam : ℝ ↦ A.partShiftResolvent hV f hf hfD lam x) (𝓝[>] (0 : ℝ))
      (𝓝 (A.partGreenPotential hV f hf hD hfD x)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (g := fun lam : ℝ ↦ A.partGreenRate hV D * lam)
    (Eventually.of_forall fun lam ↦ dist_nonneg) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with lam hlam
    rw [Real.dist_eq]
    exact A.abs_partShiftResolvent_sub_partGreenPotential_le hV hf hD hfD x hlam
  · have hcont : Tendsto (fun lam : ℝ ↦ A.partGreenRate hV D * lam) (𝓝 (0 : ℝ))
        (𝓝 (A.partGreenRate hV D * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at hcont
    exact hcont.mono_left nhdsWithin_le_nhds

theorem partGreenPotential_of_notMem {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D)
    {x : Vec d} (hx : x ∉ V) :
    A.partGreenPotential hV f hf hD hfD x = 0 := by
  have habs : |A.partGreenPotential hV f hf hD hfD x| ≤ 0 := by
    refine le_of_forall_pos_add_mul_part (K := A.partGreenRate hV D)
      (A.partGreenRate_nonneg hV hD) fun lam hlam ↦ ?_
    have h := A.abs_partShiftResolvent_sub_partGreenPotential_le hV hf hD hfD x hlam
    rw [A.partShiftResolvent_of_notMem hV hf hfD lam hx, zero_sub, abs_neg] at h
    linarith only [h]
  exact abs_nonpos_iff.mp habs

theorem abs_partGreenPotential_le {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D)
    (x : Vec d) :
    |A.partGreenPotential hV f hf hD hfD x| ≤ D * A.partTorsionBound hV := by
  refine le_of_forall_pos_add_mul_part (K := A.partGreenRate hV D)
    (A.partGreenRate_nonneg hV hD) fun lam hlam ↦ ?_
  have h := A.abs_partShiftResolvent_sub_partGreenPotential_le hV hf hD hfD x hlam
  have hbd := A.abs_partShiftResolvent_le hV hf hD hfD lam x
  have hsplit := abs_sub_abs_le_abs_sub (A.partGreenPotential hV f hf hD hfD x)
    (A.partShiftResolvent hV f hf hfD lam x)
  rw [abs_sub_comm] at hsplit
  linarith only [hsplit, h, hbd]

theorem partGreenPotential_nonneg {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    0 ≤ A.partGreenPotential hV f hf hD hfD x := by
  refine ge_of_tendsto (A.tendsto_partShiftResolvent_nhdsGT_zero hV hf hD hfD x) ?_
  filter_upwards [self_mem_nhdsWithin] with lam _
  exact A.partShiftResolvent_nonneg hV hf hf0 hfD lam x

/-- **The Green potential of a part domain sees only the values of its datum on that domain.** -/
theorem partGreenPotential_eq_of_eqOn {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g) {D E : ℝ} (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E) (hfg : Set.EqOn f g V)
    (x : Vec d) :
    A.partGreenPotential hV f hf hD hfD x = A.partGreenPotential hV g hg hE hgE x := by
  refine tendsto_nhds_unique (A.tendsto_partShiftResolvent_nhdsGT_zero hV hf hD hfD x) ?_
  refine (A.tendsto_partShiftResolvent_nhdsGT_zero hV hg hE hgE x).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with lam _
  exact (A.partShiftResolvent_eq_of_eqOn hV hf hg hfD hgE hfg lam x).symm

/-! ## Regularity of the Green potential -/

/-- **The Dirichlet resolvents converge to the Green potential uniformly on the domain.**  The
rate of `abs_partShiftResolvent_sub_partGreenPotential_le` does not depend on the point. -/
theorem tendstoUniformlyOn_partShiftResolvent {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    TendstoUniformlyOn (fun n : ℕ ↦ A.partShiftResolvent hV f hf hfD ((n : ℝ) + 1)⁻¹)
      (A.partGreenPotential hV f hf hD hfD) atTop V := by
  have hzero : Tendsto (fun n : ℕ ↦ A.partGreenRate hV D * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := A.partGreenRate hV D) (f := (atTop : Filter ℕ))).mul hb
  refine Metric.tendstoUniformlyOn_iff.mpr fun eps heps ↦ ?_
  filter_upwards [hzero.eventually_lt_const heps] with n hn x _
  have hbound := A.abs_partShiftResolvent_sub_partGreenPotential_le hV hf hD hfD x
    (show (0 : ℝ) < ((n : ℝ) + 1)⁻¹ by positivity)
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt hbound hn

/-- **The Green potential is continuous on the domain**, being a uniform limit of the Dirichlet
resolvents, which are continuous there. -/
theorem continuousOn_partGreenPotential {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    ContinuousOn (A.partGreenPotential hV f hf hD hfD) V := by
  have hcont : ∀ n : ℕ, ContinuousOn (A.partShiftResolvent hV f hf hfD ((n : ℝ) + 1)⁻¹) V := by
    intro n
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have hfun : A.partShiftResolvent hV f hf hfD ((n : ℝ) + 1)⁻¹ =
        A.partC0Resolvent hV ⟨((n : ℝ) + 1)⁻¹, hpos⟩ f hf hfD :=
      funext fun x ↦ A.partShiftResolvent_of_pos hV hf hfD hpos x
    rw [hfun]
    exact A.continuousOn_partC0Resolvent hV _ f hf hfD
  exact (A.tendstoUniformlyOn_partShiftResolvent hV hf hD hfD).continuousOn
    (Filter.Eventually.frequently (Filter.Eventually.of_forall hcont))

theorem measurable_partGreenPotential {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    Measurable (A.partGreenPotential hV f hf hD hfD) := by
  have hstep : ∀ n : ℕ, Measurable fun x ↦
      A.partShiftResolvent hV f hf hfD ((n : ℝ) + 1)⁻¹ x := by
    intro n
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have hfun : (fun x ↦ A.partShiftResolvent hV f hf hfD ((n : ℝ) + 1)⁻¹ x) =
        A.partC0Resolvent hV ⟨((n : ℝ) + 1)⁻¹, hpos⟩ f hf hfD :=
      funext fun x ↦ A.partShiftResolvent_of_pos hV hf hfD hpos x
    rw [hfun]
    exact A.measurable_partC0Resolvent hV _ f hf hfD
  refine measurable_of_tendsto_metrizable' atTop hstep (tendsto_pi_nhds.mpr fun x ↦ ?_)
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun n : ℕ ↦ A.partGreenRate hV D * ((n : ℝ) + 1)⁻¹)
    (fun n ↦ dist_nonneg) (fun n ↦ ?_) ?_
  · rw [Real.dist_eq]
    exact A.abs_partShiftResolvent_sub_partGreenPotential_le hV hf hD hfD x (by positivity)
  · have hzero : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := A.partGreenRate hV D) (f := (atTop : Filter ℕ))).mul hzero

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
