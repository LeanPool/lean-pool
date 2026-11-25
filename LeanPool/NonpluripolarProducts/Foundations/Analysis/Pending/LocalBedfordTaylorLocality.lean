/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentRestriction
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorProducts

/-!
# Locality of the recursive Bedford--Taylor product

For open `V ≤ U ⊆ ℂⁿ`, the restriction `T|_V` of a current of bidimension `(q,q)` on `U` is
`γ ↦ T(γ) ∘ (extension of test functions by zero)`.  Restriction preserves positivity and
closedness and commutes with `dd^c`, with the trace measure (`traceMeasure_restrict`), with the
coefficient densities and with multiplication by locally bounded Borel functions
(`mulBorel_restrict`).  Hence **the recursive product is local on open subsets**
(`btProduct_restrict`, `bt:recursive-product`):
`B(u₁, …, u_q; T)|_V = B(u₁, …, u_q; T|_V)`.

* `eq_of_forall_testFunction_integral_eq` — two measures on `ℂⁿ` carried by `U`, finite on
  the compact subsets of `U`, with the same integrals of all test functions on `U`, are equal.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Manifold Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts

variable {n : ℕ}

local notation "E" => ComplexModel n

variable {U V : Opens (ComplexModel n)}

theorem dTest_extTest (hVU : V ≤ U) (v : E) (φ : 𝓓(V, ℝ)) :
    dTest v (extTest hVU φ) = extTest hVU (dTest v φ) := by
  ext x
  have hf : (extTest hVU φ : E → ℝ) = (φ : E → ℝ) := funext (extTest_apply hVU φ)
  rw [dTest_apply, extTest_apply, dTest_apply, hf]

/-- Test functions supported in a compact set share a finite nonnegative partition
subordinate to any open cover of that set. -/
theorem exists_weighted_test_partition {ι α : Type*}
    (V : ι → Opens E) (hVU : ∀ i, V i ≤ U) {K : Set E} (hK : IsCompact K)
    (hcover : K ⊆ ⋃ i, (V i : Set E)) (φ : α → 𝓓(U, ℝ))
    (hφK : ∀ j, tsupport (φ j) ⊆ K) :
    ∃ (s : Finset ι) (ρ : ι → E → ℝ) (ψ : ∀ i, α → 𝓓(V i, ℝ)),
      (∀ i x, 0 ≤ ρ i x) ∧ (∀ i j x, ψ i j x = ρ i x * φ j x) ∧
      ∀ j, φ j = ∑ i ∈ s, extTest (hVU i) (ψ i j) := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, E)) hK.isClosed (fun i ↦ (V i : Set E)) (fun i ↦ (V i).isOpen) hcover
  let active : Set ι := {i | (Function.support (ρ i) ∩ K).Nonempty}
  have hactive : active.Finite := ρ.locallyFinite.finite_nonempty_inter_compact hK
  let ψ (i : ι) (j : α) : 𝓓(V i, ℝ) :=
    ⟨fun x ↦ ρ i x * φ j x, (ρ i).contMDiff.contDiff.mul (φ j).contDiff,
      (φ j).hasCompactSupport.mul_left, tsupport_mul_subset_left.trans (hρ i)⟩
  refine ⟨hactive.toFinset, fun i x ↦ ρ i x, ψ, ρ.nonneg, fun _ _ _ ↦ rfl, fun j ↦ ?_⟩
  apply TestFunction.ext
  intro x
  have hsum_apply : ∀ s : Finset ι,
      (∑ i ∈ s, extTest (hVU i) (ψ i j)) x = ∑ i ∈ s, ρ i x * φ j x := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert i s hi hs =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        change (extTest (hVU i) (ψ i j)) x + (∑ a ∈ s, extTest (hVU a) (ψ a j)) x =
          ρ i x * φ j x + ∑ a ∈ s, ρ a x * φ j x
        rw [hs, extTest_apply]
        rfl
  rw [hsum_apply]
  by_cases hx : x ∈ K
  · have hsupp : Function.support (fun i ↦ ρ i x) ⊆ active := fun i hi => ⟨x, hi, hx⟩
    rw [← Finset.sum_mul, ← finsum_eq_finsetSum_of_support_subset (fun i ↦ ρ i x)
      (by simpa only [Set.Finite.coe_toFinset] using hsupp), ρ.sum_eq_one hx, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφK j h))]
    simp

/-- Full variable-test positivity is local. -/
theorem isPositive_of_local_restrict {q : ℕ} {S : LocalProductCurrent n U q}
    (hloc : ∀ x ∈ U, ∃ (V : Opens (ComplexModel n)) (hVU : V ≤ U),
      x ∈ V ∧ IsPositive (restrict hVU S)) : IsPositive S := by
  classical
  intro ι _ γ φ hγ
  let K : Set E := ⋃ i : ι, tsupport (φ i)
  have hK : IsCompact K := isCompact_iUnion fun i => (φ i).hasCompactSupport
  have hKU : K ⊆ U := iUnion_subset fun i => (φ i).tsupport_subset
  choose W hWU hxW hpos using fun x : U => hloc x x.property
  have hcover : K ⊆ ⋃ a : U, (W a : Set E) := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hKU hx⟩, hxW ⟨x, hKU hx⟩⟩
  obtain ⟨s, ρ, ψ, hρ, hψ, hsum⟩ := exists_weighted_test_partition W hWU hK hcover φ
    (fun i => subset_iUnion (fun j => tsupport (φ j)) i)
  have hnonneg (a : U) : 0 ≤ ∑ i, S (γ i) (extTest (hWU a) (ψ a i)) := by
    apply hpos a ι γ (ψ a)
    intro x
    simp_rw [hψ]
    have heq : (∑ i, (ρ a x * φ i x) • (γ i : RealForm n (2 * q))) =
        ρ a x • (∑ i, φ i x • (γ i : RealForm n (2 * q))) := by
      simp only [Finset.smul_sum, smul_smul]
    rw [heq]
    exact smul_mem_spCone (hγ x) (hρ a x)
  have heq : (∑ i, S (γ i) (φ i)) = ∑ a ∈ s, ∑ i, S (γ i) (extTest (hWU a) (ψ a i)) := by
    simp only [hsum, map_sum]
    exact Finset.sum_comm
  rw [heq]
  exact Finset.sum_nonneg fun a _ => hnonneg a

theorem ddc_restrict (hVU : V ≤ U) (S : LocalProductCurrent n U (q + 1)) :
    ddc (restrict hVU S) = restrict hVU (ddc S) := by
  ext γ φ
  simp only [ddc_apply_apply, restrict_apply, dTest_extTest]

theorem isClosedCurrent_restrict {S : LocalProductCurrent n U (q + 1)} (hS : IsClosedCurrent S)
    (hVU : V ≤ U) : IsClosedCurrent (restrict hVU S) := by
  intro ℓ γ
  ext φ
  have h := hS.apply_eq_zero ℓ γ (extTest hVU φ)
  simp only [_root_.sum_apply, dDist_apply, restrict_apply, ← dTest_extTest,
    Finset.sum_neg_distrib, _root_.zero_apply, neg_eq_zero]
  exact h

theorem isClosedAny_restrict {k : ℕ} {S : LocalProductCurrent n U k} (hS : IsClosedAny k S)
    (hVU : V ≤ U) : IsClosedAny k (restrict hVU S) := by
  cases k with
  | zero => trivial
  | succ k => exact isClosedCurrent_restrict hS hVU

/-- A locally bounded PSH function on `U` is locally bounded PSH on `V ≤ U`. -/
theorem isLocallyBoundedPshOn_mono {u : E → ℝ} (hu : IsLocallyBoundedPshOn U u) (hVU : V ≤ U) :
    IsLocallyBoundedPshOn V u :=
  hu.mono hVU

/-- **One step of the recursion commutes with restriction.** -/
theorem ddcMul_restrict {m : ℕ} {S : LocalProductCurrent n U (m + 1)} (hS : IsPositive S)
    (hVU : V ≤ U) {u : E → ℝ} (hu : IsLocallyBoundedPshOn U u) :
    ddcMul (restrict hVU S) u = restrict hVU (ddcMul S u) := by
  have huV := isLocallyBoundedPshOn_mono hu hVU
  rw [ddcMul, ddcMul, ← ddc_restrict, ← mulBorel_restrict hS hVU
    (measurable_indicator_of_isLocallyBoundedPshOn hu) (isLocallyBoundedOn_indicator hu)]
  congr 1
  refine mulBorel_congr (isPositive_restrict hS hVU)
    (measurable_indicator_of_isLocallyBoundedPshOn huV) (isLocallyBoundedOn_indicator huV)
    (measurable_indicator_of_isLocallyBoundedPshOn hu)
    (isLocallyBoundedOn_mono (isLocallyBoundedOn_indicator hu) hVU) fun x hx => ?_
  rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hVU hx)]

/-- **Locality of the recursive Bedford--Taylor product** (`bt:recursive-product`): for open
`V ≤ U`, `B(u₁, …, u_q; T)|_V = B(u₁, …, u_q; T|_V)`. -/
theorem btProduct_restrict (hVU : V ≤ U) : ∀ (q r : ℕ) (u : Fin q → E → ℝ)
    (T : LocalProductCurrent n U (r + q)), IsPositive T → IsClosedAny (r + q) T →
    (∀ i, IsLocallyBoundedPshOn U (u i)) →
    btProduct q r u (restrict hVU T) = restrict hVU (btProduct q r u T)
  | 0, _, _, _, _, _, _ => rfl
  | q + 1, r, u, T, hT, hTc, hu => by
    rw [btProduct_succ, btProduct_succ, ddcMul_restrict (m := r + q) hT hVU (hu (Fin.last q))]
    obtain ⟨h1, h2⟩ := isPositive_ddcMul (m := r + q) hT hTc (hu (Fin.last q))
    exact btProduct_restrict hVU q r (Fin.init u) _ h1 h2 fun i => hu _

/-- `[1]|_V = [1]`. -/
theorem restrict_oneCurrent {n : ℕ} {U V : Opens (ComplexModel n)} (hVU : V ≤ U) :
    LocalBedfordTaylorLocality.restrict hVU (oneCurrent U) = oneCurrent V := by
  ext γ φ
  rw [LocalBedfordTaylorLocality.restrict_apply, oneCurrent_apply, oneCurrent_apply]
  have hf : (extTest hVU φ : ComplexModel n → ℝ) = (φ : ComplexModel n → ℝ) := funext
    (extTest_apply hVU φ)
  rw [hf]

/-- The degree-indexed unit current restricts to the unit on the smaller open set. -/
theorem restrict_oneCurrentOf {n degree : ℕ} {U V : Opens (ComplexModel n)} (hVU : V ≤ U)
    (hdegree : degree = n) :
    restrict hVU (oneCurrentOf (U := U) hdegree) = oneCurrentOf (U := V) hdegree := by
  subst hdegree
  exact restrict_oneCurrent hVU

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
