/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ManifoldPluripolar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PshConvexCone
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.BottChern
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentials

/-!
# Convex combinations of theta-PSH potentials

`PSH(X, θ)` is a convex set: for `t ∈ (0,1)` and `u`, `v` genuine `θ`-PSH
potentials, `t·u + (1-t)·v` is again one.  This is the elementary closure
property behind Xia's `ε`-barrier constructions (SGPT, Corollary 2.4.3,
`xia-sgpt:page-0087`), which produce a
common lower barrier for two potentials as an explicit convex combination.

Two points need care in this formalization.

* The local smooth potentials `ρ₁`, `ρ₂` supplied by the two hypotheses are
  different functions on different chart neighbourhoods.  Their convex
  combination `t·ρ₁ + (1-t)·ρ₂` is again a local potential of the same form,
  by linearity of `smoothDDC` (`FirstPass.smoothDDC_add`,
  `FirstPass.smoothDDC_smul`) together with `t + (1-t) = 1`; no pluriharmonic
  comparison of `ρ₁` and `ρ₂` is needed.
* Local nondegeneracy is not inherited pointwise.  The pole set of the
  combination is contained in the union of the two pole sets, which is locally
  pluripolar and hence has Haar measure zero in every chart; a nonempty open
  set therefore contains a non-pole point.
-/

@[expose] public section

open Set MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The pointwise convex combination of two extended-real potentials. -/
def convexComb (t : ℝ) (u v : M → EReal) : M → EReal :=
  fun x => (t : EReal) * u x + ((1 - t : ℝ) : EReal) * v x

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem convexComb_apply (t : ℝ) (u v : M → EReal) (x : M) :
    convexComb t u v x = (t : EReal) * u x + ((1 - t : ℝ) : EReal) * v x := rfl

/-- Positive scaling distributes over the addition of a finite real shift. -/
theorem coe_mul_add_coe {c : ℝ} (hc : 0 < c) (a : EReal) (r : ℝ) :
    (c : EReal) * (a + (r : EReal)) = (c : EReal) * a + ((c * r : ℝ) : EReal) := by
  induction a with
  | bot => simp [EReal.coe_mul_bot_of_pos hc]
  | top =>
    rw [EReal.top_add_coe, EReal.coe_mul_top_of_pos hc, EReal.top_add_coe]
  | coe a => rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, mul_add]

/-- Positive scaling does not create poles. -/
theorem eq_bot_of_coe_mul_eq_bot {c : ℝ} (hc : 0 < c) {a : EReal}
    (h : (c : EReal) * a = ⊥) : a = ⊥ := by
  induction a with
  | bot => rfl
  | top => rw [EReal.coe_mul_top_of_pos hc] at h; exact absurd h (by simp)
  | coe a => rw [← EReal.coe_mul] at h; exact absurd h (EReal.coe_ne_bot _)

omit [TopologicalSpace M] [IsComplexManifold n M] in
/-- The pole set of a convex combination with positive weights is contained in
the union of the two pole sets. -/
theorem poles_convexComb_subset {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (u v : M → EReal) :
    {x | convexComb t u v x = ⊥} ⊆ {x | u x = ⊥} ∪ {x | v x = ⊥} := by
  intro x hx
  rcases EReal.add_eq_bot_iff.mp hx with h | h
  · exact Or.inl (eq_bot_of_coe_mul_eq_bot ht0 h)
  · exact Or.inr (eq_bot_of_coe_mul_eq_bot (by linarith) h)

omit [IsComplexManifold n M] in
/-- A function whose pole set is locally pluripolar is locally nondegenerate:
in every chart the pole set has Haar measure zero, while a nonempty open set
has positive measure. -/
theorem locallyNondegenerate_of_poles_pluripolar {w : M → EReal}
    (h : ManifoldLocallyPluripolar (n := n) {x | w x = ⊥}) :
    LocallyNondegenerate w := by
  intro x U hU hxU
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  set V : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' U with hV
  have hVopen : IsOpen V := e.val.isOpen_inter_preimage_symm hU
  have hzV : e.val x ∈ V := by
    refine ⟨e.val.map_source hxs, ?_⟩
    change e.val.symm (e.val x) ∈ U
    rwa [e.val.left_inv hxs]
  have hmeas : volume (pluripolarChartSet {x | w x = ⊥} e) = 0 :=
    h.chart_measure_eq_zero e volume
  have hpos : 0 < volume V := hVopen.measure_pos volume ⟨_, hzV⟩
  have hnot : ¬ V ⊆ pluripolarChartSet {x | w x = ⊥} e := by
    intro hsub
    exact hpos.ne' (measure_mono_null hsub hmeas)
  obtain ⟨y, hyV, hy⟩ := not_subset.mp hnot
  refine ⟨e.val.symm y, hyV.2, fun hbot => hy ⟨hyV.1, hbot⟩⟩

/-- **`PSH(X, θ)` is convex.**  For `0 < t < 1` the pointwise convex
combination of two genuine `θ`-PSH potentials is a genuine `θ`-PSH potential. -/
theorem isThetaPshPotential_convexComb {theta : SmoothRealForm n M 2}
    {u v : M → EReal} (hu : IsThetaPshPotential theta u)
    (hv : IsThetaPshPotential theta v) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    IsThetaPshPotential theta (convexComb t u v) := by
  have ht1' : 0 < 1 - t := by linarith
  constructor
  · intro e z hz
    obtain ⟨W₁, rho₁, hzW₁, hrho₁, hpsh₁⟩ := hu.1 e z hz
    obtain ⟨W₂, rho₂, hzW₂, hrho₂, hpsh₂⟩ := hv.1 e z hz
    refine ⟨W₁ ∩ W₂, fun y => t * rho₁ y + (1 - t) * rho₂ y, ⟨hzW₁, hzW₂⟩, ?_, ?_⟩
    · refine ⟨hrho₁.1.inter hrho₂.1, inter_subset_left.trans hrho₁.2.1, ?_, ?_⟩
      · exact ((contDiffOn_const (c := t)).mul
          (hrho₁.2.2.1.mono inter_subset_left)).add
          ((contDiffOn_const (c := 1 - t)).mul
            (hrho₂.2.2.1.mono inter_subset_right))
      · intro y hy
        have h₁ : ContDiffOn ℝ ∞ (fun w => t * rho₁ w) (W₁ ∩ W₂) :=
          (contDiffOn_const (c := t)).mul (hrho₁.2.2.1.mono inter_subset_left)
        have h₂ : ContDiffOn ℝ ∞ (fun w => (1 - t) * rho₂ w) (W₁ ∩ W₂) :=
          (contDiffOn_const (c := 1 - t)).mul (hrho₂.2.2.1.mono inter_subset_right)
        have hopen := hrho₁.1.inter hrho₂.1
        rw [smoothDDC_add hopen h₁ h₂ hy]
        rw [show (fun w => t * rho₁ w) = (fun w => t • rho₁ w) by
              funext w; exact (smul_eq_mul _ _).symm,
          show (fun w => (1 - t) * rho₂ w) = (fun w => (1 - t) • rho₂ w) by
              funext w; exact (smul_eq_mul _ _).symm]
        rw [smoothDDC_smul hopen (hrho₁.2.2.1.mono inter_subset_left) t hy,
          smoothDDC_smul hopen (hrho₂.2.2.1.mono inter_subset_right) (1 - t) hy,
          hrho₁.2.2.2 hy.1, hrho₂.2.2.2 hy.2, ← add_smul]
        simp
    · have heq : ∀ y, chartFunction (convexComb t u v) e y +
          ((t * rho₁ y + (1 - t) * rho₂ y : ℝ) : EReal) =
          (t : EReal) * (chartFunction u e y + (rho₁ y : EReal)) +
            ((1 - t : ℝ) : EReal) * (chartFunction v e y + (rho₂ y : EReal)) := by
        intro y
        rw [coe_mul_add_coe ht0, coe_mul_add_coe ht1', EReal.coe_add]
        simp only [chartFunction, convexComb]
        abel
      simp only [heq]
      exact ((hpsh₁.mono inter_subset_left).const_mul ht0).add
        ((hpsh₂.mono inter_subset_right).const_mul ht1')
  · apply locallyNondegenerate_of_poles_pluripolar (n := n)
    exact (manifoldLocallyPluripolar_union
      (quasiPsh_poles_manifoldLocallyPluripolar hu.quasiPshPotential)
      (quasiPsh_poles_manifoldLocallyPluripolar hv.quasiPshPotential)).mono
      (poles_convexComb_subset ht0 ht1 u v)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Convex combinations with fixed weights are monotone in both arguments. -/
theorem convexComb_mono {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {a b c d : M → EReal}
    (hac : a ≤ c) (hbd : b ≤ d) : convexComb t a b ≤ convexComb t c d := by
  intro x
  exact add_le_add (mul_le_mul_of_nonneg_left (hac x) (EReal.coe_nonneg.mpr ht0))
    (mul_le_mul_of_nonneg_left (hbd x) (EReal.coe_nonneg.mpr (by linarith)))

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- At the balanced weight the two arguments may be exchanged. -/
theorem convexComb_half_comm (a b : M → EReal) :
    convexComb (1 / 2 : ℝ) a b = convexComb (1 / 2 : ℝ) b a := by
  funext x
  simp only [convexComb]
  norm_num
  exact add_comm _ _

end

end SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
