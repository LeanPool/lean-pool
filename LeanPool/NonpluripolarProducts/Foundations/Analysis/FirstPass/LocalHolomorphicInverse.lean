/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ComplexAnalyticSubvarieties
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicContDiff
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Local holomorphic equivalences from the inverse function theorem

* `LocalHolomorphicEquivAt.restrict`: shrink a local holomorphic equivalence to an open
  subset of its source, recentred at any point of the smaller source.
* `exists_localHolomorphicEquivAt`: a map `F : ℂ^n → ℂ^n`, holomorphic on an open set `N`
  with injective complex derivative at `p ∈ N`, is a local holomorphic equivalence near
  `p` whose source lies in `N` and on which the derivative stays injective.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ}

namespace LocalHolomorphicEquivAt

/-- Restriction of a local holomorphic equivalence to the open set `Φ.source ∩ s`,
recentred at a point `q` of that set. -/
def restrict {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p)
    (s : Set (ComplexModel n)) (hs : IsOpen s) (q : ComplexModel n)
    (hq : q ∈ Φ.source ∩ s) : LocalHolomorphicEquivAt (n := n) q where
  source := Φ.source ∩ s
  target := Φ.target ∩ Φ.invFun ⁻¹' s
  isOpen_source := Φ.isOpen_source.inter hs
  isOpen_target :=
    Φ.invFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_target hs
  center_mem_source := hq
  toFun := Φ.toFun
  invFun := Φ.invFun
  toFun_holomorphic := Φ.toFun_holomorphic.mono inter_subset_left
  invFun_holomorphic := Φ.invFun_holomorphic.mono inter_subset_left
  mapsTo_toFun z hz := ⟨Φ.mapsTo_toFun hz.1, by
    simpa only [mem_preimage, Φ.left_inv z hz.1] using hz.2⟩
  mapsTo_invFun w hw := ⟨Φ.mapsTo_invFun hw.1, hw.2⟩
  left_inv z hz := Φ.left_inv z hz.1
  right_inv w hw := Φ.right_inv w hw.1

@[simp] theorem restrict_source {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p)
    (s : Set (ComplexModel n)) (hs : IsOpen s) (q : ComplexModel n)
    (hq : q ∈ Φ.source ∩ s) : (Φ.restrict s hs q hq).source = Φ.source ∩ s := rfl

@[simp] theorem restrict_toFun {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p)
    (s : Set (ComplexModel n)) (hs : IsOpen s) (q : ComplexModel n)
    (hq : q ∈ Φ.source ∩ s) : (Φ.restrict s hs q hq).toFun = Φ.toFun := rfl

@[simp] theorem restrict_invFun {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p)
    (s : Set (ComplexModel n)) (hs : IsOpen s) (q : ComplexModel n)
    (hq : q ∈ Φ.source ∩ s) : (Φ.restrict s hs q hq).invFun = Φ.invFun := rfl

end LocalHolomorphicEquivAt

/-- **Holomorphic inverse function theorem.** -/
theorem exists_localHolomorphicEquivAt {F : ComplexModel n → ComplexModel n}
    {N : Set (ComplexModel n)} (hN : IsOpen N) {p : ComplexModel n} (hp : p ∈ N)
    (hF : DifferentiableOn ℂ F N) (hinj : Function.Injective (fderiv ℂ F p)) :
    ∃ Φ : LocalHolomorphicEquivAt (n := n) p, Φ.source ⊆ N ∧ Φ.toFun = F ∧
      ∀ z ∈ Φ.source, Function.Injective (fderiv ℂ F z) := by
  have hsmooth : ContDiffOn ℂ ∞ F N := contDiffOn_of_differentiableOn_complex hF hN
  -- the open set of points of `N` where the derivative is invertible
  set W : Set (ComplexModel n) := N ∩ fderiv ℂ F ⁻¹'
    range ((↑) : (ComplexModel n ≃L[ℂ] ComplexModel n) → ComplexModel n →L[ℂ] ComplexModel n)
  have hWo : IsOpen W :=
    (hsmooth.continuousOn_fderiv_of_isOpen hN (by simp)).isOpen_inter_preimage hN
      ContinuousLinearEquiv.isOpen
  set L : ComplexModel n ≃L[ℂ] ComplexModel n :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℂ F p : ComplexModel n →ₗ[ℂ] ComplexModel n)
      hinj).toContinuousLinearEquiv
  have hL : (L : ComplexModel n →L[ℂ] ComplexModel n) = fderiv ℂ F p := by ext; rfl
  have hstrict : HasStrictFDerivAt F (L : ComplexModel n →L[ℂ] ComplexModel n) p := by
    rw [hL]; exact (hsmooth.contDiffAt (hN.mem_nhds hp)).hasStrictFDerivAt_fderiv (by simp)
  set e := HasStrictFDerivAt.toOpenPartialHomeomorph F hstrict
  have he : (e : ComplexModel n → ComplexModel n) = F :=
    HasStrictFDerivAt.toOpenPartialHomeomorph_coe hstrict
  have hWsub : ∀ z ∈ W, ∃ M : ComplexModel n ≃L[ℂ] ComplexModel n,
      HasFDerivAt F (M : ComplexModel n →L[ℂ] ComplexModel n) z := by
    rintro z ⟨hzN, M, hM⟩
    exact ⟨M, hM ▸ (hF.differentiableAt (hN.mem_nhds hzN)).hasFDerivAt⟩
  refine ⟨{
    source := e.source ∩ W
    target := e.target ∩ e.symm ⁻¹' W
    isOpen_source := e.open_source.inter hWo
    isOpen_target := e.isOpen_inter_preimage_symm hWo
    center_mem_source :=
      ⟨HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hstrict, hp, L, hL⟩
    toFun := F
    invFun := e.symm
    toFun_holomorphic := hF.mono fun z hz => hz.2.1
    invFun_holomorphic := fun w hw => by
      obtain ⟨M, hM⟩ := hWsub _ hw.2
      rw [← he] at hM
      exact (e.hasFDerivAt_symm hw.1 hM).differentiableAt.differentiableWithinAt
    mapsTo_toFun := fun z hz => ⟨e.map_source hz.1, by
      simpa only [mem_preimage, ← he, e.left_inv hz.1] using hz.2⟩
    mapsTo_invFun := fun w hw => ⟨e.map_target hw.1, hw.2⟩
    left_inv := fun z hz => e.left_inv hz.1
    right_inv := fun w hw => e.right_inv hw.1 }, fun z hz => hz.2.1, rfl, ?_⟩
  rintro z ⟨-, -, M, hM⟩
  rw [← hM]
  exact M.injective

end

end SGPT.Foundations.Analysis.FirstPass
