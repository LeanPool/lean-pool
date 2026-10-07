/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGain
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingStrongFamily

/-!
# Calculus of space-time Sobolev families on slabs

`prop:lps-smoothing`: elementary operations on `L²(I; H^m(ℝ³))` families used by the regularity
ladder: lowering the order, restricting to a smaller time interval, differentiating once (the
shifted family), and finite sums, together with the restriction of the distributional heat
equation to a smaller time interval.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- An `L²(I; H^m)` family is a space-time derivative family on the slab. -/
theorem lps_l2Family_toSpaceTime {m : ℕ} {I : Set ℝ} {z : Vec3 × ℝ → ℝ}
    {D : List (Fin 3) → Vec3 × ℝ → ℝ}
    (h : IsL2SobolevFamilyOn m (Set.univ : Set Vec3) I z D) :
    IsSpaceTimeFamily m ((Set.univ : Set Vec3) ×ˢ I) D :=
  ⟨h.memL2, h.weak⟩

/-- A space-time derivative family on a slab whose zeroth member represents `z` is an
`L²(I; H^m)` family of `z`. -/
theorem lps_spaceTimeFamily_toL2 {m : ℕ} {I : Set ℝ} {z : Vec3 × ℝ → ℝ}
    {D : List (Fin 3) → Vec3 × ℝ → ℝ}
    (h : IsSpaceTimeFamily m ((Set.univ : Set Vec3) ×ˢ I) D)
    (hz : D [] =ᵐ[volume.restrict ((Set.univ : Set Vec3) ×ˢ I)] z) :
    IsL2SobolevFamilyOn m (Set.univ : Set Vec3) I z D :=
  ⟨h.memL2, hz, h.weak⟩

/-- An `L²(I; H^m)` family is an `L²(I; H^{m'})` family for every `m' ≤ m`. -/
theorem lps_l2Family_of_le {m m' : ℕ} {I : Set ℝ} {z : Vec3 × ℝ → ℝ}
    {D : List (Fin 3) → Vec3 × ℝ → ℝ}
    (h : IsL2SobolevFamilyOn m (Set.univ : Set Vec3) I z D) (hm : m' ≤ m) :
    IsL2SobolevFamilyOn m' (Set.univ : Set Vec3) I z D :=
  ⟨fun α hα => h.memL2 α (hα.trans hm), h.zero, fun α j hα => h.weak α j (lt_of_lt_of_le hα hm)⟩

/-- An `L²(I; H^m)` family restricts to every measurable subinterval `J ⊆ I`. -/
theorem lps_l2Family_mono_interval {m : ℕ} {I J : Set ℝ} (hI : MeasurableSet I) (hJI : J ⊆ I)
    {z : Vec3 × ℝ → ℝ} {D : List (Fin 3) → Vec3 × ℝ → ℝ}
    (h : IsL2SobolevFamilyOn m (Set.univ : Set Vec3) I z D) :
    IsL2SobolevFamilyOn m (Set.univ : Set Vec3) J z D := by
  have hmono : (volume.restrict ((Set.univ : Set Vec3) ×ˢ J) : Measure (Vec3 × ℝ)) ≤
      volume.restrict ((Set.univ : Set Vec3) ×ˢ I) :=
    Measure.restrict_mono (prod_mono subset_rfl hJI) le_rfl
  refine ⟨fun α hα => (h.memL2 α hα).mono_measure hmono, ae_mono hmono h.zero, ?_⟩
  intro α j hα
  exact IsSpaceTimeWeakPartial.mono (h.weak α j hα) (MeasurableSet.univ.prod hI)
    (prod_mono subset_rfl hJI)

/-- Differentiating once: the words of an `L²(I; H^{m+1})` family that start with `j` form an
`L²(I; H^m)` family of any representative `g` of `D [j]`. -/
theorem lps_l2Family_shift {m : ℕ} {I : Set ℝ} {z g : Vec3 × ℝ → ℝ}
    {D : List (Fin 3) → Vec3 × ℝ → ℝ}
    (h : IsL2SobolevFamilyOn (m + 1) (Set.univ : Set Vec3) I z D) (j : Fin 3)
    (hg : D [j] =ᵐ[volume.restrict ((Set.univ : Set Vec3) ×ˢ I)] g) :
    IsL2SobolevFamilyOn m (Set.univ : Set Vec3) I g (fun γ => D (j :: γ)) := by
  refine ⟨fun γ hγ => h.memL2 (j :: γ) (by simp only [List.length_cons]; omega), hg, ?_⟩
  intro γ k hγ
  exact h.weak (j :: γ) k (by simp only [List.length_cons]; omega)

/-- Finite sums of `L²(I; H^m)` families over the three coordinates. -/
theorem lps_l2Family_sum {m : ℕ} {I : Set ℝ} {f : Fin 3 → Vec3 × ℝ → ℝ}
    {D : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ}
    (h : ∀ j, IsL2SobolevFamilyOn m (Set.univ : Set Vec3) I (f j) (D j)) :
    IsL2SobolevFamilyOn m (Set.univ : Set Vec3) I (fun z => ∑ j, f j z)
      (fun α z => ∑ j, D j α z) := by
  refine lps_spaceTimeFamily_toL2
    (IsSpaceTimeFamily.finset_sum Finset.univ fun j _ => lps_l2Family_toSpaceTime (h j)) ?_
  have hall : ∀ᵐ p ∂(volume.restrict ((Set.univ : Set Vec3) ×ˢ I)), ∀ j, D j [] p = f j p :=
    ae_all_iff.mpr fun j => (h j).zero
  filter_upwards [hall] with p hp
  exact Finset.sum_congr rfl fun j _ => hp j

/-- The distributional heat equation restricts to a measurable subinterval. -/
theorem lps_heat_mono_interval {I J : Set ℝ} (hI : MeasurableSet I) (hJI : J ⊆ I)
    {z G : Vec3 × ℝ → ℝ} (h : IsHeatSolutionOn (Set.univ : Set Vec3) I z G) :
    IsHeatSolutionOn (Set.univ : Set Vec3) J z G := by
  intro ψ hψ hψc hψJ
  have hkey := h ψ hψ hψc (hψJ.trans (prod_mono subset_rfl hJI))
  have hV : MeasurableSet ((Set.univ : Set Vec3) ×ˢ I) := MeasurableSet.univ.prod hI
  have hWV : (Set.univ : Set Vec3) ×ˢ J ⊆ (Set.univ : Set Vec3) ×ˢ I :=
    prod_mono subset_rfl hJI
  have h1 : ∀ p, p ∉ (Set.univ : Set Vec3) ×ˢ J →
      z p * (-timePartial ψ p - ∑ j : Fin 3, spatialSecondPartial ψ j j p) = 0 := by
    intro p hp
    have hp' : p ∉ tsupport ψ := fun hm => hp (hψJ hm)
    rw [CKN.timePartial_eq_zero_off_tsupport hp']
    simp only [CKN.spatialSecondPartial_eq_zero_off_tsupport hp', Finset.sum_const_zero,
      neg_zero, sub_zero, mul_zero]
  have h2 : ∀ p, p ∉ (Set.univ : Set Vec3) ×ˢ J → G p * ψ p = 0 := by
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (fun hm => hp (hψJ hm)), mul_zero]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hV hWV fun p hp => h1 p hp.2,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hV hWV fun p hp => h2 p hp.2] at hkey
  exact hkey

/-- The sum over the words of length at most two, written out. -/
theorem lps_sum_sobolevWords_two (φ : List (Fin 3) → ℝ) :
    ∑ α ∈ sobolevWords 2, φ α = φ [] + ∑ j, φ [j] + ∑ j, ∑ k, φ [j, k] := by
  have hset : sobolevWords 2 = insert [] ((Finset.univ.image fun j : Fin 3 => [j]) ∪
      (Finset.univ.image fun p : Fin 3 × Fin 3 => [p.1, p.2])) := by
    ext α
    simp only [mem_sobolevWords, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · intro h
      match α, h with
      | [], _ => exact Or.inl rfl
      | [j], _ => exact Or.inr (Or.inl ⟨j, rfl⟩)
      | [j, k], _ => exact Or.inr (Or.inr ⟨(j, k), rfl⟩)
      | _ :: _ :: _ :: _, h => simp at h
    · rintro (rfl | ⟨j, rfl⟩ | ⟨p, rfl⟩) <;> simp
  rw [hset, Finset.sum_insert (by simp), Finset.sum_union, Finset.sum_image, Finset.sum_image,
    Fintype.sum_prod_type]
  · ring
  · intro p _ q _ h
    simpa [Prod.ext_iff] using h
  · intro j _ k _ h
    simpa using h
  · rw [Finset.disjoint_left]
    intro α h1 h2
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨j, rfl⟩ := h1
    obtain ⟨p, hp⟩ := h2
    simp at hp

end ESS
