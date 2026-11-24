/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DistributionTranslationRemainder
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DistributionPairingDifferentiability

/-!
# Seminorm Taylor remainders for translated distribution kernels

Pointwise Taylor estimates for the spatial derivatives of a translated kernel
are upgraded here to fixed-support test-function seminorm estimates.  This is
one compatibility step between translation differentiation and the finite-order
continuity estimate for distributions; instantiating the raw derivative bounds
still requires the finite-order Schwarz-symmetry bridge recorded below.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace Filter Asymptotics
open scoped ContDiff Distributions Topology

namespace SGPT.Foundations.Analysis.Pending

/-- The scalar first-order remainder before multiplication by the fixed
cutoff. -/
noncomputable def translationFirstRemainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : E → ℝ) (z h y : E) : ℝ :=
  κ (y - (z + h)) - κ (y - z) - fderiv ℝ κ (y - z) (-h)

/-- Smoothness in the spatial variable of the scalar translation remainder. -/
theorem translationFirstRemainder_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : E → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (z h : E) :
    ContDiff ℝ (⊤ : ℕ∞)
      (translationFirstRemainder κ z h) := by
  have hκz : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ κ (y - z)) :=
    hκ.comp (contDiff_id.sub contDiff_const)
  have hκzh : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ κ (y - (z + h))) :=
    hκ.comp (contDiff_id.sub contDiff_const)
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ κ) :=
    hκ.fderiv_right (by simp)
  have hjet : ContDiff ℝ (⊤ : ℕ∞)
      (fun y ↦ fderiv ℝ κ (y - z) (-h)) :=
    (hfd.comp (contDiff_id.sub contDiff_const)).clm_apply contDiff_const
  exact (hκzh.sub hκz).sub hjet

/-- The fixed-support first-order translation remainder as an element of the
common test-function space. -/
noncomputable def cutoffTranslationFirstRemainderSupportedIn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (z h : E) :
    ContDiffMapSupportedIn E ℝ ⊤ K :=
  cutoffTranslatedKernelSupportedIn χ κ hκ K hχK (z + h) -
    cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z -
    cutoffTranslatedKernelFirstJetLM χ κ hκ K hχK z h

@[simp]
theorem cutoffTranslationFirstRemainderSupportedIn_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (z h y : E) :
    cutoffTranslationFirstRemainderSupportedIn χ κ hκ K hχK z h y =
      χ y * translationFirstRemainder κ z h y := by
  simp [cutoffTranslationFirstRemainderSupportedIn,
    cutoffTranslatedKernelSupportedIn_apply,
    cutoffTranslatedKernelFirstJetLM_apply,
    cutoffTranslatedKernelJetSupportedIn_apply,
    translationFirstRemainder, iteratedFDeriv_one_apply]
  ring

/-- A quantitative Leibniz estimate for one seminorm of the cutoff translation
remainder.  The arrays `A` and `B` may be any uniform derivative bounds for the
cutoff and the uncut scalar remainder on `K`. -/
theorem cutoffTranslationFirstRemainder_seminorm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (z h : E) (r : ℕ)
    (A B : ℕ → ℝ)
    (hA0 : ∀ i ≤ r, 0 ≤ A i) (hB0 : ∀ j ≤ r, 0 ≤ B j)
    (hA : ∀ i ≤ r, ∀ y ∈ (K : Set E),
      ‖iteratedFDeriv ℝ i (χ : E → ℝ) y‖ ≤ A i)
    (hB : ∀ j ≤ r, ∀ y ∈ (K : Set E),
      ‖iteratedFDeriv ℝ j (translationFirstRemainder κ z h) y‖ ≤ B j) :
    ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K r
        (cutoffTranslationFirstRemainderSupportedIn χ κ hκ K hχK z h) ≤
      ∑ i ∈ Finset.range (r + 1),
        (r.choose i : ℝ) * A i * B (r - i) := by
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range (r + 1),
      (r.choose i : ℝ) * A i * B (r - i) := by
    apply Finset.sum_nonneg
    intro i hi
    have hir : i ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hri : r - i ≤ r := Nat.sub_le r i
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hA0 i hir)) (hB0 (r - i) hri)
  rw [ContDiffMapSupportedIn.seminorm_top_le_iff ℝ hsum0]
  intro y hy
  have hfun :
      (cutoffTranslationFirstRemainderSupportedIn χ κ hκ K hχK z h : E → ℝ) =
        fun q ↦ χ q * translationFirstRemainder κ z h q := by
    funext q
    exact cutoffTranslationFirstRemainderSupportedIn_apply
      χ κ hκ K hχK z h q
  rw [hfun]
  refine (norm_iteratedFDeriv_mul_le χ.contDiff
    (translationFirstRemainder_contDiff κ hκ z h) y (by
      change ((↑r : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  have hir : i ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hri : r - i ≤ r := Nat.sub_le r i
  calc
    (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i (χ : E → ℝ) y‖ *
        ‖iteratedFDeriv ℝ (r - i) (translationFirstRemainder κ z h) y‖ ≤
      (r.choose i : ℝ) * A i *
        ‖iteratedFDeriv ℝ (r - i) (translationFirstRemainder κ z h) y‖ := by
      gcongr
      exact hA i hir y hy
    _ ≤ (r.choose i : ℝ) * A i * B (r - i) := by
      exact mul_le_mul_of_nonneg_left (hB (r - i) hri y hy)
        (mul_nonneg (Nat.cast_nonneg _) (hA0 i hir))

/-- Little-o bounds for the finitely many uncut spatial derivatives pass
through multiplication by the fixed cutoff to each fixed-support seminorm. -/
theorem cutoffTranslationFirstRemainder_seminorm_isLittleO
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (z : E) (r : ℕ)
    (A : ℕ → ℝ) (B : ℕ → E → ℝ)
    (hA0 : ∀ i ≤ r, 0 ≤ A i)
    (hA : ∀ i ≤ r, ∀ y ∈ (K : Set E),
      ‖iteratedFDeriv ℝ i (χ : E → ℝ) y‖ ≤ A i)
    (hB0 : ∀ j ≤ r, ∀ h, 0 ≤ B j h)
    (hB : ∀ j ≤ r, ∀ h, ∀ y ∈ (K : Set E),
      ‖iteratedFDeriv ℝ j (translationFirstRemainder κ z h) y‖ ≤ B j h)
    (hBo : ∀ j ≤ r, (B j) =o[𝓝 0] (fun h : E ↦ h)) :
    (fun h : E ↦
      ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K r
        (cutoffTranslationFirstRemainderSupportedIn χ κ hκ K hχK z h))
      =o[𝓝 0] (fun h : E ↦ h) := by
  let Q : E → ℝ := fun h ↦ ∑ i ∈ Finset.range (r + 1),
    (r.choose i : ℝ) * A i * B (r - i) h
  have hQo : Q =o[𝓝 0] (fun h : E ↦ h) := by
    dsimp only [Q]
    have hterms : ∀ i ∈ Finset.range (r + 1),
        (fun h ↦ (r.choose i : ℝ) * A i * B (r - i) h)
          =o[𝓝 0] (fun h : E ↦ h) := by
      intro i hi
      have hir : i ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hri : r - i ≤ r := Nat.sub_le r i
      exact (hBo (r - i) hri).const_mul_left ((r.choose i : ℝ) * A i)
    refine (IsLittleO.sum hterms).congr ?_ (fun _ ↦ rfl)
    intro h
    simp
  have hdom :
      (fun h : E ↦
        ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K r
          (cutoffTranslationFirstRemainderSupportedIn χ κ hκ K hχK z h))
        =O[𝓝 0] Q := by
    apply (IsBigOWith.of_bound (c := (1 : ℝ)) ?_).isBigO
    filter_upwards with h
    have hQ0 : 0 ≤ Q h := by
      dsimp only [Q]
      apply Finset.sum_nonneg
      intro i hi
      have hir : i ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hri : r - i ≤ r := Nat.sub_le r i
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hA0 i hir))
        (hB0 (r - i) hri h)
    have hle := cutoffTranslationFirstRemainder_seminorm_le
      χ κ hκ K hχK z h r A (fun j ↦ B j h) hA0
      (fun j hj ↦ hB0 j hj h) hA (fun j hj ↦ hB j hj h)
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (apply_nonneg
        (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K r) _),
      abs_of_nonneg hQ0, one_mul, Q] using hle
  exact hdom.trans_isLittleO hQo

end SGPT.Foundations.Analysis.Pending
