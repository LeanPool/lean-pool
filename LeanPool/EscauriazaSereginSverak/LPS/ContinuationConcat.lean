/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationConcatEq

/-!
# Concatenating a Leray–Hopf solution with a strong solution

A Leray–Hopf solution on `(0, T)`, followed after a time `s ≤ T` at which it
satisfies the energy equality by a strong solution with the same slice at `s`,
is a Leray–Hopf solution on `(0, s')` (`lem:lps-continuation`). This lets a
strong continuation be compared with the original solution through
uniqueness of Leray–Hopf solutions.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The field equal to `f` strictly before time `b` and to `g` from time `b` on. -/
@[expose] def lpsCat {α : Type} (b : ℝ) (f g : ParabolicPoint → α) (z : ParabolicPoint) : α :=
  if z.2 < b then f z else g z

theorem lpsCat_of_lt {α : Type} {b : ℝ} {f g : ParabolicPoint → α} {z : ParabolicPoint}
    (h : z.2 < b) : lpsCat b f g z = f z := by
  simp [lpsCat, h]

theorem lpsCat_of_ge {α : Type} {b : ℝ} {f g : ParabolicPoint → α} {z : ParabolicPoint}
    (h : b ≤ z.2) : lpsCat b f g z = g z := by
  simp [lpsCat, not_lt.mpr h]

/-- The two ways of gluing differ only on the null slice at the gluing time. -/
theorem lpsCat_ae_eq_glue {α : Type} (b : ℝ) (f g : ParabolicPoint → α) :
    ∀ᵐ z : ParabolicPoint ∂(volume : Measure ParabolicPoint), lpsCat b f g z = lpsGlue b f g z := by
  have hnull : (volume : Measure ParabolicPoint) (spaceTimeSet (Set.univ : Set Vec3) {b}) = 0 := by
    change (volume : Measure (Vec3 × ℝ)) ((Set.univ : Set Vec3) ×ˢ ({b} : Set ℝ)) = 0
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  rw [ae_iff]
  refine measure_mono_null (fun z hz => ?_) hnull
  refine ⟨mem_univ _, ?_⟩
  by_contra hne
  apply hz
  rcases lt_or_gt_of_ne hne with h | h
  · rw [lpsCat_of_lt h, lpsGlue_of_le h.le]
  · rw [lpsCat_of_ge h.le, lpsGlue_of_gt h]

/-- Concatenation of a Leray–Hopf solution with a strong continuation from a
time of energy equality (`lem:lps-continuation`). -/
theorem lps_leray_hopf_concat {T s s' : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {W : ParabolicPoint → Vec3}
    {DW : ParabolicPoint → Fin 3 → Vec3} {pW : ParabolicPoint → ℝ}
    (hLH : IsLerayHopfSolution T a u Du) (hs0 : 0 < s) (hsT : s ≤ T)
    (hW : IsLpsStrongSolution s s' W DW pW)
    (hweakEq : ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      (∫ x : Vec3, ∑ i : Fin 3, W (x, s) i * w x i) = ∫ x : Vec3, ∑ i : Fin 3, u (x, s) i * w x i)
    (hEnergy : ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (W (x, s))) ^ (2 : ℝ)) +
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s),
        ENNReal.ofReal (spatialGradientSq u Du z)) =
      ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ)) :
    IsLerayHopfSolution s' a (lpsCat s u W) (lpsCat s Du DW) := by
  have hLH' := hLH
  obtain ⟨-, ha, hmu, hmDu, hess, hL2, hgrad, hdiv, hweak, hmom, hineq, hinit⟩ := hLH'
  have hW' := hW
  obtain ⟨hss', hS₂, hC₂, ⟨D2, Dt, hD, hWu, hWDu, -, -⟩, hWp, hE₂⟩ := hW'
  obtain ⟨hu2, hDu2⟩ := lps_lh_memLp_slab hLH
  have hsub : Ioo (0 : ℝ) s ⊆ Ioo 0 T := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hsT⟩
  have hQsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := fun z hz => ⟨hz.1, hsub hz.2⟩
  have hu1 : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) :=
    hu2.mono_measure (Measure.restrict_mono hQsub le_rfl)
  have hDu1 : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) :=
    hDu2.mono_measure (Measure.restrict_mono hQsub le_rfl)
  have hVuG : MemLp (lpsGlue s u W) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s'))) :=
    lps_memLp_slab_glue hu1 hWu (fun z hz => lpsGlue_of_le hz) (fun z hz => lpsGlue_of_gt hz)
  have hVDuG : MemLp (lpsGlue s Du DW) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s'))) :=
    lps_memLp_slab_glue hDu1 hWDu (fun z hz => lpsGlue_of_le hz) (fun z hz => lpsGlue_of_gt hz)
  have hae1 := ae_restrict_of_ae (μ := (volume : Measure ParabolicPoint))
    (s := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s')) (lpsCat_ae_eq_glue s u W)
  have hae2 := ae_restrict_of_ae (μ := (volume : Measure ParabolicPoint))
    (s := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s')) (lpsCat_ae_eq_glue s Du DW)
  have hVu : MemLp (lpsCat s u W) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s'))) :=
    (memLp_congr_ae hae1).mpr hVuG
  have hVDu : MemLp (lpsCat s Du DW) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s'))) :=
    (memLp_congr_ae hae2).mpr hVDuG
  have hsIcc : s ∈ Icc s s' := ⟨le_rfl, hss'.le⟩
  refine ⟨hs0.trans hss', ha, hVu.aestronglyMeasurable, hVDu.aestronglyMeasurable, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- the slice bound
    have hC₂top : (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (W (x, s))) ^ (2 : ℝ)) < ⊤ := by
      rw [serrin_lintegral_eucl_sq (lps_strong_solution_slice_memLp_two hW hsIcc).1]
      exact ENNReal.ofReal_lt_top
    set C₁ : ℝ≥0∞ := essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo 0 T)) with hC₁
    set C₂ : ℝ≥0∞ := ∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (W (x, s))) ^ (2 : ℝ)
      with hC₂def
    have hae : ∀ᵐ t ∂(volume.restrict (Ioo 0 s')),
        ∫⁻ x : Vec3, ‖lpsCat s u W (x, t)‖ₑ ^ (2 : ℝ) ≤ max C₁ C₂ := by
      refine lps_ae_restrict_Ioo_union hs0.le hss'.le (P := fun t =>
        ∫⁻ x : Vec3, ‖lpsCat s u W (x, t)‖ₑ ^ (2 : ℝ) ≤ max C₁ C₂) ?_ ?_
      · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (ENNReal.ae_le_essSup
          (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))),
          ae_restrict_mem measurableSet_Ioo] with t h1 ht
        have e : ∀ x : Vec3, lpsCat s u W (x, t) = u (x, t) := fun x => lpsCat_of_lt ht.2
        simp only [e]
        exact h1.trans (le_max_left _ _)
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        have e : ∀ x : Vec3, lpsCat s u W (x, t) = W (x, t) := fun x => lpsCat_of_ge ht.1.le
        simp only [e]
        have hWe := lps_strong_energy_ennreal hW (t := t) ⟨ht.1.le, ht.2.le⟩
        have h1 : ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (W (x, t))) ^ (2 : ℝ)) ≤
            ENNReal.ofReal (1 / 2 : ℝ) * C₂ := by
          rw [hC₂def]
          exact le_trans le_self_add (le_of_eq hWe)
        have h2 := (ENNReal.mul_le_mul_iff_right (by simp) ENNReal.ofReal_ne_top).mp h1
        exact (lintegral_mono fun x => CKN.enorm_sq_le_vec3Euclidean_sq _).trans
          (h2.trans (le_max_right _ _))
    exact lt_of_le_of_lt (essSup_le_of_ae_le _ hae) (max_lt hess hC₂top)
  · -- joint square integrability
    have h1 : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s'),
        ‖lpsCat s u W z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num) hVu
      simpa using this
    have h2 : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s'),
        ‖lpsCat s Du DW z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num) hVDu
      simpa using this
    rw [lintegral_add_left' (hVu.aestronglyMeasurable.enorm.pow_const _)]
    exact ENNReal.add_lt_top.2 ⟨h1, h2⟩
  · -- weak gradients
    refine lps_ae_restrict_Ioo_union hs0.le hss'.le (P := fun t => ∀ i : Fin 3,
      HasWeakGradientOn (Set.univ : Set Vec3) (fun x => lpsCat s u W (x, t) i)
        (fun x => lpsCat s Du DW (x, t) i)) ?_ ?_
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hgrad,
        ae_restrict_mem measurableSet_Ioo] with t ht htI i
      have e : ∀ x : Vec3, lpsCat s u W (x, t) = u (x, t) := fun x => lpsCat_of_lt htI.2
      have e' : ∀ x : Vec3, lpsCat s Du DW (x, t) = Du (x, t) := fun x => lpsCat_of_lt htI.2
      simp only [e, e']
      exact ht i
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t htI i
      have e : ∀ x : Vec3, lpsCat s u W (x, t) = W (x, t) := fun x => lpsCat_of_ge htI.1.le
      have e' : ∀ x : Vec3, lpsCat s Du DW (x, t) = DW (x, t) := fun x => lpsCat_of_ge htI.1.le
      simp only [e, e']
      exact lps_strong_solution_slice_weak_gradient hW ⟨htI.1.le, htI.2.le⟩ i
  · -- solenoidal slices
    refine lps_ae_restrict_Ioo_union hs0.le hss'.le (P := fun t =>
      ∀ ψ : WeakTestFunction (Set.univ : Set Vec3),
        ∫ x : Vec3, ∑ i : Fin 3, lpsCat s u W (x, t) i * ψ.partialDeriv i x = 0) ?_ ?_
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hdiv,
        ae_restrict_mem measurableSet_Ioo] with t ht htI ψ
      have e : ∀ x : Vec3, lpsCat s u W (x, t) = u (x, t) := fun x => lpsCat_of_lt htI.2
      simp only [e]
      exact ht ψ
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t htI ψ
      have e : ∀ x : Vec3, lpsCat s u W (x, t) = W (x, t) := fun x => lpsCat_of_ge htI.1.le
      simp only [e]
      exact (lps_strong_solution_slice_weak_div_free hW ⟨htI.1.le, htI.2.le⟩).2 ψ
  · -- weak continuity
    intro w hw
    rw [← Icc_union_Icc_eq_Icc hs0.le hss'.le]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · refine ((hweak w hw).mono (Icc_subset_Icc_right hsT)).congr fun t ht => ?_
      rcases eq_or_lt_of_le ht.2 with h | h
      · subst h
        have e : ∀ x : Vec3, lpsCat t u W (x, t) = W (x, t) := fun x => lpsCat_of_ge le_rfl
        simp only [e]
        exact hweakEq w hw
      · have e : ∀ x : Vec3, lpsCat s u W (x, t) = u (x, t) := fun x => lpsCat_of_lt h
        simp only [e]
    · refine (lps_pairing_continuousOn_of_l2 (α := s) (β := s') (u := W)
        (fun t ht => (lps_strong_solution_slice_memLp_two hW ht).1)
        (fun t ht => (hC₂ t ht).1) hw).congr fun t ht => ?_
      have e : ∀ x : Vec3, lpsCat s u W (x, t) = W (x, t) := fun x => lpsCat_of_ge ht.1
      simp only [e]
  · -- the momentum equation
    intro φ hφ hdivφ
    have hEqG := lps_concat_equation hLH hs0 hsT hW hweakEq φ hφ hdivφ
    refine Eq.trans ?_ hEqG
    refine integral_congr_ae ?_
    filter_upwards [hae1, hae2] with z h1 h2
    simp only [h1, h2]
  · -- the energy inequality
    intro t₀ ht₀
    have hmeas : ∀ {c d : ℝ}, MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d)) :=
      fun {c d} => MeasurableSet.univ.prod measurableSet_Ioo
    by_cases h : t₀ < s
    · have e : ∀ x : Vec3, lpsCat s u W (x, t₀) = u (x, t₀) := fun x => lpsCat_of_lt h
      have hg : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
          ENNReal.ofReal (spatialGradientSq (lpsCat s u W) (lpsCat s Du DW) z)) =
          ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
            ENNReal.ofReal (spatialGradientSq u Du z) := by
        refine setLIntegral_congr_fun hmeas fun z hz => ?_
        unfold spatialGradientSq
        simp only [lpsCat_of_lt (hz.2.2.trans h)]
      show ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (lpsCat s u W (x, t₀))) ^ (2 : ℝ)) +
        (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
          ENNReal.ofReal (spatialGradientSq (lpsCat s u W) (lpsCat s Du DW) z)) ≤ _
      simp only [e]
      rw [hg]
      exact hineq t₀ ⟨ht₀.1, h.le.trans hsT⟩
    · have hge : s ≤ t₀ := not_lt.mp h
      have e : ∀ x : Vec3, lpsCat s u W (x, t₀) = W (x, t₀) := fun x => lpsCat_of_ge hge
      have hWe := lps_strong_energy_ennreal hW (t := t₀) ⟨hge, ht₀.2⟩
      have hsplit := lps_lintegral_slab_split hs0.le hge
        (fun z => ENNReal.ofReal (spatialGradientSq (lpsCat s u W) (lpsCat s Du DW) z))
        (a := 0) (c := t₀)
      have hg1 : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s),
          ENNReal.ofReal (spatialGradientSq (lpsCat s u W) (lpsCat s Du DW) z)) =
          ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s),
            ENNReal.ofReal (spatialGradientSq u Du z) := by
        refine setLIntegral_congr_fun hmeas fun z hz => ?_
        unfold spatialGradientSq
        simp only [lpsCat_of_lt hz.2.2]
      have hg2 : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t₀),
          ENNReal.ofReal (spatialGradientSq (lpsCat s u W) (lpsCat s Du DW) z)) =
          ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t₀),
            ENNReal.ofReal (spatialGradientSq W DW z) := by
        refine setLIntegral_congr_fun hmeas fun z hz => ?_
        unfold spatialGradientSq
        simp only [lpsCat_of_ge hz.2.1.le]
      show ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (lpsCat s u W (x, t₀))) ^ (2 : ℝ)) +
        (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
          ENNReal.ofReal (spatialGradientSq (lpsCat s u W) (lpsCat s Du DW) z)) ≤ _
      simp only [e]
      rw [hsplit, hg1, hg2]
      refine le_of_eq ?_
      rw [← hEnergy, ← hWe]
      ring
  · -- the initial trace
    refine hinit.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hs0] with t ht
    have e : ∀ x : Vec3, lpsCat s u W (x, t) = u (x, t) := fun x => lpsCat_of_lt ht.2
    simp only [e]

end ESS

end
