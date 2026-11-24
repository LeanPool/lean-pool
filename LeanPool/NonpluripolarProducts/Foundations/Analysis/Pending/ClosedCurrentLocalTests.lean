/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothCurrentClosedness
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CoordinateWedgeFamilyPairing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.KahlerDomination

/-!
# Closedness of a positive current may be tested locally, with semipositive slots

A current `T` of bidimension `(k+1, k+1)` is closed (`ClosedProductCurrents.IsClosedCurrent`) when
`T (Π₁₁ d(f dg) ∧ β₁ ∧ ⋯ ∧ β_k) = 0` for all chart-smooth `f, g` and all closed real `(1,1)`-forms
`βⱼ`.  For a POSITIVE current on a compact Kähler manifold it suffices to test

* with `f` supported in a member of any given open cover (`f = ∑ₐ χₐ f` for a chart-smooth
  partition of unity, and the test form is linear in `f` at every chart point; positive currents
  only see coefficients on chart targets), and
* with closed SEMIPOSITIVE slots `βⱼ` (the test form is multilinear in the slots, and
  `β = (β + A ω) - A ω` with `β + A ω` semipositive for large `A`, `KahlerDomination`).

This is the form in which the Skoda--El Mir theorem and the support theorem on the diagonal
(TN.4 step B4, `demailly-cadg:III.2.3`, `III.2.13`) test closedness: in a small chart, against a
positive current `T ∧ β₁ ∧ ⋯ ∧ β_k` of bidimension `(1,1)`.

## Main results

* `wedgeProd_update_add`, `wedgeProd_update_smul`, `wedgeProd_update_sum` (slotwise linearity).
* `closedTestForm_update_add`, `closedTestForm_update_smul` (linearity in each closed slot),
  `exactPair_coeff_sum`, `closedTestForm_coeff_sum` (linearity in `f` at chart points).
* `isClosedCurrent_of_semipositive_slots`, `isClosedCurrent_of_local`.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.ClosedCurrentLocalTests

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents TopDegreeDensity ClosedProductCurrents
  SmoothCurrentClosedness ChartPartition CurrentTraceMeasure

/-! ### Slotwise linearity of products of two-forms -/

section Wedge

variable {n : ℕ}

theorem wedgeProd_update_add (q : ℕ) (β : Fin q → RealForm n 2) (j : Fin q)
    (a b : RealForm n 2) :
    wedgeProd q (Function.update β j (a + b)) =
      wedgeProd q (Function.update β j a) + wedgeProd q (Function.update β j b) := by
  ext v
  rw [ContinuousAlternatingMap.add_apply, wedgeProd_apply, wedgeProd_apply, wedgeProd_apply,
    coordinateWedgeFamily_apply_eq_pairingSum, coordinateWedgeFamily_apply_eq_pairingSum,
    coordinateWedgeFamily_apply_eq_pairingSum, coordinatePairingSumFamily_update_add]
  ring

theorem wedgeProd_update_smul (q : ℕ) (β : Fin q → RealForm n 2) (j : Fin q) (r : ℝ)
    (a : RealForm n 2) :
    wedgeProd q (Function.update β j (r • a)) = r • wedgeProd q (Function.update β j a) := by
  ext v
  rw [ContinuousAlternatingMap.smul_apply, wedgeProd_apply, wedgeProd_apply,
    coordinateWedgeFamily_apply_eq_pairingSum, coordinateWedgeFamily_apply_eq_pairingSum,
    coordinatePairingSumFamily_update_smul, smul_eq_mul]
  ring

theorem wedgeProd_update_zero (q : ℕ) (β : Fin q → RealForm n 2) (j : Fin q) :
    wedgeProd q (Function.update β j 0) = 0 := by
  have h := wedgeProd_update_smul q β j 0 0
  rw [zero_smul, zero_smul] at h
  exact h

theorem wedgeProd_update_sum {ι : Type*} (s : Finset ι) (q : ℕ) (β : Fin q → RealForm n 2)
    (j : Fin q) (a : ι → RealForm n 2) :
    wedgeProd q (Function.update β j (∑ i ∈ s, a i)) =
      ∑ i ∈ s, wedgeProd q (Function.update β j (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wedgeProd_update_zero]
  | insert a' s ha ih =>
    rw [Finset.sum_insert ha, wedgeProd_update_add, ih, Finset.sum_insert ha]

end Wedge

/-! ### Linearity of the closed test forms -/

section ClosedTest

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem slot_update_coeff {k : ℕ} (β : Fin k → ClosedRealOneOneForm n M) (j : Fin k)
    (c : ClosedRealOneOneForm n M) (e : ComplexChart n M) (z : ComplexModel n) :
    (fun i => (Function.update β j c i).val.coeff e z) =
      Function.update (fun i => (β i).val.coeff e z) j (c.val.coeff e z) := by
  classical
  funext i
  by_cases h : i = j
  · subst h
    simp
  · simp [Function.update_of_ne h]

theorem coeff_sum {k : ℕ} {ι : Type*} (s : Finset ι) (φ : ι → SmoothRealForm n M k)
    (e : ComplexChart n M) (z : ComplexModel n) :
    (∑ i ∈ s, φ i).coeff e z = ∑ i ∈ s, (φ i).coeff e z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, coeff_add, ih, Finset.sum_insert ha]

/-- **The closed test form is additive in each slot.** -/
theorem closedTestForm_update_add {f g : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hg : ChartSmooth (n := n) g) (k : ℕ) (β : Fin k → ClosedRealOneOneForm n M) (j : Fin k)
    (a b : ClosedRealOneOneForm n M) :
    closedTestForm f g hf hg k (Function.update β j (a + b)) =
      closedTestForm f g hf hg k (Function.update β j a) +
        closedTestForm f g hf hg k (Function.update β j b) := by
  refine Subtype.ext (smoothRealForm_ext fun e z => ?_)
  rw [Submodule.coe_add, coeff_add, closedTestForm_coeff, closedTestForm_coeff,
    closedTestForm_coeff, slot_update_coeff, slot_update_coeff, slot_update_coeff,
    Fin.cons_update, Fin.cons_update, Fin.cons_update]
  exact wedgeProd_update_add _ _ _ _ _

/-- **The closed test form is homogeneous in each slot.** -/
theorem closedTestForm_update_smul {f g : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hg : ChartSmooth (n := n) g) (k : ℕ) (β : Fin k → ClosedRealOneOneForm n M) (j : Fin k)
    (r : ℝ) (a : ClosedRealOneOneForm n M) :
    closedTestForm f g hf hg k (Function.update β j (r • a)) =
      r • closedTestForm f g hf hg k (Function.update β j a) := by
  refine Subtype.ext (smoothRealForm_ext fun e z => ?_)
  rw [Submodule.coe_smul, coeff_smul, closedTestForm_coeff, closedTestForm_coeff,
    slot_update_coeff, slot_update_coeff, Fin.cons_update, Fin.cons_update]
  exact wedgeProd_update_smul _ _ _ _ _

/-- `d(f dg)` is additive in `f` along a partition of unity, at chart points. -/
theorem exactPair_coeff_sum {f g : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hg : ChartSmooth (n := n) g) {r : ℕ} (χ : Fin r → M → ℝ)
    (hχ : ∀ a, ChartSmooth (n := n) (χ a)) (hsum : ∀ x, ∑ a, χ a x = 1)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    (exactPair f g hf hg).coeff e z =
      ∑ a, (exactPair (fun x => χ a x * f x) g (chartSmooth_mul (hχ a) hf) hg).coeff e z := by
  have hnhds : e.val.target ∈ 𝓝 z := e.val.open_target.mem_nhds hz
  have hfun : (fun y => f (e.val.symm y)) =
      fun y => ∑ a, (fun y => χ a (e.val.symm y) * f (e.val.symm y)) y := by
    funext y
    rw [← Finset.sum_mul, hsum, one_mul]
  have hfd : fderiv ℝ (fun y => f (e.val.symm y)) z =
      ∑ a, fderiv ℝ (fun y => χ a (e.val.symm y) * f (e.val.symm y)) z := by
    rw [hfun, fderiv_fun_sum fun a _ =>
      (((chartSmooth_mul (hχ a) hf) e).contDiffAt hnhds).differentiableAt (by simp)]
  ext w
  rw [eq_vec_two' w, ContinuousAlternatingMap.sum_apply, exactPair_coeff_apply f g hf hg e hz]
  simp only [exactPair_coeff_apply _ g (chartSmooth_mul (hχ _) hf) hg e hz, hfd, _root_.sum_apply,
    Finset.sum_mul, ← Finset.sum_sub_distrib]

/-- **The closed test form is additive in `f` along a partition of unity**, at chart points. -/
theorem closedTestForm_coeff_sum {f g : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hg : ChartSmooth (n := n) g) (k : ℕ) (β : Fin k → ClosedRealOneOneForm n M) {r : ℕ}
    (χ : Fin r → M → ℝ) (hχ : ∀ a, ChartSmooth (n := n) (χ a)) (hsum : ∀ x, ∑ a, χ a x = 1)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    ((closedTestForm f g hf hg k β : testSpace n M (k + 1)) :
        SmoothRealForm n M (2 * (k + 1))).coeff e z =
      ((∑ a, closedTestForm (fun x => χ a x * f x) g (chartSmooth_mul (hχ a) hf) hg k β :
        testSpace n M (k + 1)) : SmoothRealForm n M (2 * (k + 1))).coeff e z := by
  classical
  set βc : Fin k → RealForm n 2 := fun j => (β j).val.coeff e z
  have hcons : ∀ x : RealForm n 2,
      (Fin.cons x βc : Fin (k + 1) → RealForm n 2) = Function.update (Fin.cons 0 βc) 0 x :=
    fun x => (Fin.update_cons_zero _ _ _).symm
  have hpi : pi11 (∑ a, (exactPair (fun x => χ a x * f x) g (chartSmooth_mul (hχ a) hf)
    hg).coeff e z)
      = ∑ a, pi11 ((exactPair (fun x => χ a x * f x) g (chartSmooth_mul (hχ a) hf) hg).coeff e z)
        := by
    rw [← pi11CLM_apply, map_sum]
    rfl
  rw [Submodule.coe_sum, coeff_sum]
  simp only [closedTestForm_coeff]
  rw [exactPair_coeff_sum hf hg χ hχ hsum e hz, hpi, hcons, wedgeProd_update_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [Fin.update_cons_zero]

end ClosedTest

/-! ### Testing closedness -/

section Tests

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]

/-- **Closed semipositive slots suffice**, for fixed `f, g`: on a compact Kähler manifold every
closed real `(1,1)`-form is `(β + A ω) - A ω` with `β + A ω` semipositive. -/
theorem apply_closedTestForm_eq_zero_of_semipositive (w : KahlerBackground n M) {k : ℕ}
    (S : ProductCurrent n M (k + 1)) {f g : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hg : ChartSmooth (n := n) g)
    (h : ∀ β : Fin k → ClosedRealOneOneForm n M, (∀ j, (β j).val.IsSemipositive) →
      S (closedTestForm f g hf hg k β) = 0)
    (β : Fin k → ClosedRealOneOneForm n M) : S (closedTestForm f g hf hg k β) = 0 := by
  classical
  have key : ∀ (B : Finset (Fin k)) (β : Fin k → ClosedRealOneOneForm n M),
      (∀ j, j ∉ B → (β j).val.IsSemipositive) → S (closedTestForm f g hf hg k β) = 0 := by
    intro B
    induction B using Finset.induction_on with
    | empty => exact fun β hβ => h β fun j => hβ j (Finset.notMem_empty j)
    | insert j B hj ih =>
      intro β hβ
      obtain ⟨A, -, hApos⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul w (β j)
      have hdec : (β j + A • w.form) + (-A) • w.form = β j := by
        apply Subtype.ext
        apply smoothRealForm_ext
        intro e z
        change ((β j).val.coeff e z + A • w.form.val.coeff e z) + (-A) • w.form.val.coeff e z =
          (β j).val.coeff e z
        ext v
        simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul]
        ring
      have hβeq : β = Function.update β j ((β j + A • w.form) + (-A) • w.form) := by
        rw [hdec, Function.update_eq_self]
      have hgood : ∀ c : ClosedRealOneOneForm n M, c.val.IsSemipositive → ∀ i, i ∉ B →
          (Function.update β j c i).val.IsSemipositive := by
        intro c hc i hi
        by_cases hij : i = j
        · subst hij
          simpa using hc
        · rw [Function.update_of_ne hij]
          exact hβ i (by simp [hij, hi])
      rw [hβeq, closedTestForm_update_add, closedTestForm_update_smul, map_add, map_smul,
        ih _ (hgood _ hApos), ih _ (hgood _ w.isSemipositive), smul_zero, add_zero]
  exact key Finset.univ β fun j hj => absurd (Finset.mem_univ j) hj

/-- **Closedness of a positive current can be tested locally, with semipositive slots**: if
`T (Π₁₁ d(f dg) ∧ β₁ ∧ ⋯ ∧ β_k) = 0` whenever `f` is supported (compactly) in one of the open sets
`U x` and the `βⱼ` are closed and semipositive, then `T` is closed. -/
theorem isClosedCurrent_of_local (w : KahlerBackground n M) {k : ℕ}
    {S : ProductCurrent n M (k + 1)} (hS : IsPositive S) (U : M → Set M)
    (hUo : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x)
    (h : ∀ (x : M) (f g : M → ℝ) (hf : ChartSmooth (n := n) f) (hg : ChartSmooth (n := n) g),
      tsupport f ⊆ U x → IsCompact (tsupport f) → ∀ β : Fin k → ClosedRealOneOneForm n M,
        (∀ j, (β j).val.IsSemipositive) → S (closedTestForm f g hf hg k β) = 0) :
    IsClosedCurrent S := by
  classical
  intro f g hf hg β
  obtain ⟨r, χ, idx, hχs, -, hχS, hχK, hsum⟩ := exists_chartSmooth_partitionOfUnity (n := n)
    (fun x => (⟨U x, hUo x⟩ : TopologicalSpace.Opens M)) fun x => ⟨x, hxU x⟩
  have hχf : ∀ a, ChartSmooth (n := n) (fun x => χ a x * f x) := fun a =>
    chartSmooth_mul (hχs a) hf
  rw [hS.apply_eq_of_coeff_eqOn fun e z hz => closedTestForm_coeff_sum hf hg k β χ hχs hsum e hz,
    map_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  exact apply_closedTestForm_eq_zero_of_semipositive w S (hχf a) hg
    (h (idx a) _ g (hχf a) hg (tsupport_mul_subset_left.trans (hχS a))
      ((hχK a).of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left)) β

end Tests

end SGPT.Foundations.Analysis.Pending.ClosedCurrentLocalTests
