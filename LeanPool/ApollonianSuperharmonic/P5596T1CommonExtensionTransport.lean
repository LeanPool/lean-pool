/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryGlobalOdometerTransport
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerActionFormulas
public import LeanPool.ApollonianSuperharmonic.P4055T1PackingGridEquivalence

-- [TABLET NODE: P5596T1CommonExtensionTransport]

/-!
# P5596T1CommonExtensionTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5596T1CommonExtensionTransport
    (s : BandPackingSymmetry) (g : IntegerLatticeFunction)
    (h k : PartialOdometer) (x : GaussianInt)
    (hg : GlobalOdometerExtends g h) (kg : GlobalOdometerExtends g k)
    (hx : x ∈ h.domain) (kx : x ∈ k.domain)
    (hstar : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
      y ∈ h.domain ∨ y ∈ k.domain) :
    ∃ g' : IntegerLatticeFunction,
      GlobalOdometerExtends g' (BandPackingSymmetryPartialOdometerAction s h) ∧
      GlobalOdometerExtends g' (BandPackingSymmetryPartialOdometerAction s k) ∧
      FourNeighborLaplacian g' (BandPackingSymmetryVectorAction s x) =
        FourNeighborLaplacian g x ∧
      BandPackingSymmetryVectorAction s x ∈
        (BandPackingSymmetryPartialOdometerAction s h).domain ∧
      BandPackingSymmetryVectorAction s x ∈
        (BandPackingSymmetryPartialOdometerAction s k).domain ∧
      ∀ y, y = BandPackingSymmetryVectorAction s x ∨
          y = BandPackingSymmetryVectorAction s x + 1 ∨
          y = BandPackingSymmetryVectorAction s x - 1 ∨
          y = BandPackingSymmetryVectorAction s x + ⟨0, 1⟩ ∨
          y = BandPackingSymmetryVectorAction s x - ⟨0, 1⟩ →
        y ∈ (BandPackingSymmetryPartialOdometerAction s h).domain ∨
          y ∈ (BandPackingSymmetryPartialOdometerAction s k).domain := by
-- BODY
  classical
  let H : PartialOdometer :=
    { domain := h.domain ∪ k.domain
      value := fun y => if y ∈ h.domain ∪ k.domain then g y else 0
      value_outside := by intro y hy; simp [hy] }
  have hH : GlobalOdometerExtends g H :=
    ⟨0, by intro y hy; simp only [H, ite_eq_left hy, add_zero]⟩
  obtain ⟨g', hglobal, hlap⟩ :=
    BandPackingSymmetryGlobalOdometerTransport s g H x hH
  obtain ⟨f, hf, _, hback⟩ := P4055T1PackingGridEquivalence s
  have membership (a : PartialOdometer) (z : GaussianInt) :
      BandPackingSymmetryVectorAction s z ∈
          (BandPackingSymmetryPartialOdometerAction s a).domain ↔ z ∈ a.domain := by
    change _ ∈ ((BandPackingSymmetryPartialOdometerAction s a).domain : Set GaussianInt) ↔ _
    rw [(BandPackingSymmetryPartialOdometerActionFormulas s a a).1]
    constructor
    · rintro ⟨w, hw, he⟩
      have hwz : w = z := f.injective (by simpa only [hf] using he)
      exact hwz ▸ hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have restrict (a : PartialOdometer) (ha : a.domain ⊆ H.domain)
      (hext : GlobalOdometerExtends g a) (hxa : x ∈ a.domain) :
      GlobalOdometerExtends g' (BandPackingSymmetryPartialOdometerAction s a) := by
    obtain ⟨c, hc⟩ := hext
    have hcompatible : OdometerCompatibility a H := by
      right
      refine ⟨c, ?_⟩
      intro y hy hyH
      simp only [H, ite_eq_left hyH]
      rw [hc y hy]
      ring
    have hc' := (BandPackingSymmetryPartialOdometerActionFormulas s a H).2.2.2.2.2.2.1.mpr
      hcompatible
    have subset : (BandPackingSymmetryPartialOdometerAction s a).domain ⊆
        (BandPackingSymmetryPartialOdometerAction s H).domain := by
      intro y hy
      change y ∈ ((BandPackingSymmetryPartialOdometerAction s a).domain : Set GaussianInt) at hy
      rw [(BandPackingSymmetryPartialOdometerActionFormulas s a a).1] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact (membership H z).mpr (ha hz)
    rcases hc' with hd | ⟨d, hd⟩
    · exact (Set.disjoint_left.mp hd ((membership a x).mpr hxa)
        ((membership H x).mpr (ha hxa))).elim
    · obtain ⟨b, hb⟩ := hglobal
      refine ⟨d + b, ?_⟩
      intro y hy
      have hv := hd y hy (subset hy)
      rw [hb y (subset hy)]
      omega
  refine ⟨g', restrict h (by intro y hy; exact Finset.mem_union_left _ hy) hg hx,
    restrict k (by intro y hy; exact Finset.mem_union_right _ hy) kg kx,
    hlap, (membership h x).mpr hx, (membership k x).mpr kx, ?_⟩
  intro y hy
  have hy' : f.symm y = x ∨ f.symm y = x + 1 ∨ f.symm y = x - 1 ∨
      f.symm y = x + ⟨0, 1⟩ ∨ f.symm y = x - ⟨0, 1⟩ := by
    rcases hy with he | hn
    · left
      rw [← hf x] at he
      simp [he]
    · right
      have hn' : y = f x + 1 ∨ y = f x - 1 ∨
          y = f x + ⟨0, 1⟩ ∨ y = f x - ⟨0, 1⟩ := by simpa only [hf] using hn
      simpa using hback (f x) y hn'
  rcases hstar (f.symm y) hy' with hh | hk
  · left
    simpa only [← hf, Equiv.apply_symm_apply] using (membership h (f.symm y)).mpr hh
  · right
    simpa only [← hf, Equiv.apply_symm_apply] using (membership k (f.symm y)).mpr hk

end ApollonianSuperharmonic

end
