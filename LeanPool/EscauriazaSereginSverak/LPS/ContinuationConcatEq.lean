/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationConcatAux
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationEquation
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationStrongGlue

/-!
# The momentum equation for concatenated solutions

A Leray–Hopf solution on `(0, T)` followed after time `s ≤ T` by a strong
solution with the same slice at `s` satisfies the divergence-free weak momentum
equation across `s`, since the boundary terms at `s` cancel
(`lem:lps-continuation`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A test field supported before `s` has vanishing derivatives from time `s` on. -/
theorem lps_test_partials_zero {a s : ℝ} {ψ : Vec3 × ℝ → Vec3}
    (hψ : ψ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo a s))
    {z : ParabolicPoint} (hz : s ≤ z.2) :
    (∀ i : Fin 3, timePartial (fun y => ψ y i) z = 0) ∧
      ∀ i j : Fin 3, spatialPartial (fun y => ψ y i) j z = 0 := by
  let z' : Vec3 × ℝ := z
  have hzφ : z' ∉ tsupport ψ := fun hmem => absurd (hψ.2.2 hmem).2.2 (not_lt.2 hz)
  have hcomp (i : Fin 3) : z' ∉ tsupport (fun y : Vec3 × ℝ => ψ y i) := by
    intro hmem
    apply hzφ
    refine closure_mono ?_ hmem
    intro y hy hzero
    apply hy
    simp [hzero]
  have hsm (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 × ℝ => ψ y i) :=
    contDiff_pi.mp hψ.1 i
  exact ⟨fun i => CKN.timePartial_zero_of_not_mem_tsupport_public (hsm i) (hcomp i),
    fun i j => CKN.spatialPartial_zero_of_not_mem_tsupport_public (hsm i) (hcomp i) j⟩

/-- The divergence-free weak equation of a Leray–Hopf solution for a test field
supported before `s ≤ T`, over the slab `(0, s)`. -/
theorem lps_lh_equation_restrict {T s : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} (hLH : IsLerayHopfSolution T a u Du) (hsT : s ≤ T)
    {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 s))
    (hdiv : ∀ z : ParabolicPoint, ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z = 0) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s),
      lpsEqIntegrand u Du (fun _ => 0) φ z = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hmom, -, -⟩ := hLH
  have hQsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) :=
    fun z hz => ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 hsT⟩
  have hφT : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) :=
    ⟨hφ.1, hφ.2.1, hφ.2.2.trans hQsub⟩
  have h := hmom φ hφT hdiv
  have hpt : ∀ z : ParabolicPoint, lpsEqIntegrand u Du (fun _ => 0) φ z =
      (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
        - ∑ i : Fin 3, ∑ j : Fin 3, u z i * u z j * spatialPartial (fun y => φ y i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3, Du z i j * spatialPartial (fun y => φ y i) j z := by
    intro z
    simp [lpsEqIntegrand]
  have hms : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  simp only [← hpt] at h
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hms hQsub] at h
  · exact h
  intro z hz
  have hz2 : s ≤ z.2 := by
    by_contra hlt
    exact hz.2 ⟨hz.1.1, hz.1.2.1, not_le.mp hlt⟩
  obtain ⟨ht, hs⟩ := lps_test_partials_zero hφ hz2
  simp [lpsEqIntegrand, ht, hs]

/-- A Leray–Hopf solution is in `L²(0,T; L²)` and its almost every slice has
uniformly bounded `L²` norm. -/
theorem lps_lh_memLp_slab {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} (hLH : IsLerayHopfSolution T a u Du) :
    MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  obtain ⟨-, -, hmu, hmDu, -, hL2, -⟩ := hLH
  exact ⟨lps_memLp_two_of_lintegral_lt_top hmu
      (lt_of_le_of_lt (lintegral_mono fun z => le_self_add) hL2),
    lps_memLp_two_of_lintegral_lt_top hmDu
      (lt_of_le_of_lt (lintegral_mono fun z => le_add_self) hL2)⟩

/-- Almost every slice of a Leray–Hopf solution on `(0, s)` is square integrable
with a uniform bound. -/
theorem lps_lh_slice_bound {T s : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} (hLH : IsLerayHopfSolution T a u Du) (hsT : s ≤ T) :
    ∃ M : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo 0 s)), MemLp (fun x : Vec3 => u (x, t)) 2 volume ∧
      (eLpNorm (fun x : Vec3 => u (x, t)) 2 volume).toReal ≤ M := by
  have hu2 := (lps_lh_memLp_slab hLH).1
  obtain ⟨-, -, -, -, hess, -⟩ := hLH
  have hsub : Ioo (0 : ℝ) s ⊆ Ioo 0 T := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hsT⟩
  have hQsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) :=
    fun z hz => ⟨hz.1, hsub hz.2⟩
  have hu2s : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) :=
    hu2.mono_measure (Measure.restrict_mono hQsub le_rfl)
  set K : ℝ≥0∞ := essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
    (volume.restrict (Ioo 0 T)) with hK
  have hKtop : K < ⊤ := hess
  refine ⟨(K ^ (1 / 2 : ℝ)).toReal, ?_⟩
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo 0 s)), ∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ (2 : ℝ) ≤ K :=
    ae_restrict_of_ae_restrict_of_subset hsub (ENNReal.ae_le_essSup _)
  filter_upwards [lps_slice_memLp_two_ae_slab hu2s, hae] with t hm hb
  refine ⟨hm, ?_⟩
  refine ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKtop.ne) ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_le_rpow hb (by norm_num)

/-- The divergence-free weak momentum equation holds across the junction of a
Leray–Hopf solution and a strong solution with the same slice
(`lem:lps-continuation`). -/
theorem lps_concat_equation {T s s' : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {W : ParabolicPoint → Vec3}
    {DW : ParabolicPoint → Fin 3 → Vec3} {pW : ParabolicPoint → ℝ}
    (hLH : IsLerayHopfSolution T a u Du) (hs0 : 0 < s) (hsT : s ≤ T)
    (hW : IsLpsStrongSolution s s' W DW pW)
    (hweakEq : ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      (∫ x : Vec3, ∑ i : Fin 3, W (x, s) i * w x i) = ∫ x : Vec3, ∑ i : Fin 3, u (x, s) i * w x i) :
    ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 s') →
      (∀ z : ParabolicPoint, ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z = 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s'),
        (-(∑ i : Fin 3, lpsGlue s u W z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              lpsGlue s u W z i * lpsGlue s u W z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              lpsGlue s Du DW z i j * spatialPartial (fun y => φ y i) j z = 0 := by
  have hW' := hW
  obtain ⟨hss', hS₂, hC₂, ⟨D2, Dt, hD, hWu, hWDu, -, -⟩, hWp, hE₂⟩ := hW'
  obtain ⟨hu2, hDu2⟩ := lps_lh_memLp_slab hLH
  have hQsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) :=
    fun z hz => ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 hsT⟩
  have hu1 : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) :=
    hu2.mono_measure (Measure.restrict_mono hQsub le_rfl)
  have hDu1 : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) :=
    hDu2.mono_measure (Measure.restrict_mono hQsub le_rfl)
  have hp0 : MemLp (fun _ : ParabolicPoint => (0 : ℝ)) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) := MemLp.zero'
  have hVu : MemLp (lpsGlue s u W) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s'))) :=
    lps_memLp_slab_glue hu1 hWu (fun z hz => lpsGlue_of_le hz) (fun z hz => lpsGlue_of_gt hz)
  have hVDu : MemLp (lpsGlue s Du DW) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s'))) :=
    lps_memLp_slab_glue hDu1 hWDu (fun z hz => lpsGlue_of_le hz) (fun z hz => lpsGlue_of_gt hz)
  have hVp : MemLp (lpsGlue s (fun _ => (0 : ℝ)) pW) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s'))) :=
    lps_memLp_slab_glue hp0 hWp (fun z hz => lpsGlue_of_le hz) (fun z hz => lpsGlue_of_gt hz)
  obtain ⟨M, hM⟩ := lps_lh_slice_bound hLH hsT
  have hweak := hLH.2.2.2.2.2.2.2.2.1
  -- the class of test fields
  let S : (Vec3 × ℝ → Vec3) → Prop := fun φ => ContDiff ℝ (⊤ : ℕ∞) φ ∧
    ∀ z : ParabolicPoint, ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z = 0
  have hS : ∀ (φ : Vec3 × ℝ → Vec3) (η : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → S φ →
      S (fun z => η z.2 • φ z) := by
    intro φ η hη hφ
    refine ⟨(hη.comp contDiff_snd).smul hφ.1, fun z => ?_⟩
    have hφi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 × ℝ => φ y i) :=
      contDiff_pi.mp hφ.1 i
    have h1 : ∀ i : Fin 3, spatialPartial (fun y : ParabolicPoint => (η y.2 • φ y) i) i z =
        η z.2 * spatialPartial (fun y => φ y i) i z := fun i =>
      lps_cutoff_spatialPartial (η := η) (hφi i) i z
    rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.mul_sum, hφ.2 z, mul_zero]
  intro φ hφ hdiv
  have hφ' := hφ
  obtain ⟨hφs, hφc, -⟩ := hφ
  have hSφ : S φ := ⟨hφs, hdiv⟩
  obtain ⟨hI, -⟩ := lps_eqIntegrand_integrable hVu hVDu hVp hφ'
  have hpt : ∀ z : ParabolicPoint,
      lpsEqIntegrand (lpsGlue s u W) (lpsGlue s Du DW) (lpsGlue s (fun _ => (0 : ℝ)) pW) φ z =
      (-(∑ i : Fin 3, lpsGlue s u W z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              lpsGlue s u W z i * lpsGlue s u W z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              lpsGlue s Du DW z i j * spatialPartial (fun y => φ y i) j z := by
    intro z
    unfold lpsEqIntegrand
    rw [hdiv z, mul_zero, sub_zero]
  simp only [← hpt]
  rw [lps_slab_integral_split hs0.le hss'.le hI]
  have hmeas1 : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hmeas2 : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo s s')) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have c1 : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s),
      lpsEqIntegrand (lpsGlue s u W) (lpsGlue s Du DW) (lpsGlue s (fun _ => (0 : ℝ)) pW) φ z) =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s),
        lpsEqIntegrand u Du (fun _ => 0) φ z :=
    setIntegral_congr_fun hmeas1 fun z hz => lpsEqIntegrand_glue_of_le hz.2.2.le
  have c2 : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo s s'),
      lpsEqIntegrand (lpsGlue s u W) (lpsGlue s Du DW) (lpsGlue s (fun _ => (0 : ℝ)) pW) φ z) =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo s s'), lpsEqIntegrand W DW pW φ z :=
    setIntegral_congr_fun hmeas2 fun z hz => lpsEqIntegrand_glue_of_gt hz.2.1
  have hG₁ := lps_weak_pairing_test_hG (α := 0) (s := s) hs0.le hφs hφc
    (fun w hw => (hweak w hw).mono (Icc_subset_Icc_right hsT)) hM
  have hlim₂ := lps_vector_pairing_tendsto (S := Icc s s') (t₀ := s) hφs hφc
    (hC₂ s ⟨le_rfl, hss'.le⟩).1
    (fun r hr => (lps_strong_solution_slice_memLp_two hW hr).1)
    (lps_strong_solution_slice_memLp_two hW ⟨le_rfl, hss'.le⟩).1
  have hR := lps_equation_boundary_right (S := S) hs0 hS hu1 hDu1 hp0
    (fun ψ hψ hSψ => lps_lh_equation_restrict hLH hsT hψ hSψ.2) hφ' hSφ hG₁
  have hL := lps_equation_boundary_left (S := S) hss' hS hWu hWDu hWp
    (fun ψ hψ _ => hE₂ ψ hψ) hφ' hSφ (lps_slice_limit_left hlim₂)
  have hℓ : (∫ x : Vec3, ∑ i : Fin 3, W (x, s) i * φ (x, s) i) =
      ∫ x : Vec3, ∑ i : Fin 3, u (x, s) i * φ (x, s) i := by
    have hφmemS (i : Fin 3) : MemLp (fun x : Vec3 => φ (x, s) i) 2 volume :=
      ((contDiff_pi.mp hφs i).continuous.comp (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport (by
        refine IsCompact.of_isClosed_subset
          ((hφc.comp_left (g := fun v : Vec3 => v i) (by simp)).image continuous_fst)
          (isClosed_tsupport _) ?_
        refine closure_minimal ?_
          ((hφc.comp_left (g := fun v : Vec3 => v i) (by simp)).image continuous_fst).isClosed
        intro x hx
        exact ⟨(x, s), subset_tsupport _ hx, rfl⟩)
    exact hweakEq (fun x => φ (x, s)) (memLp_pi_iff.2 hφmemS)
  rw [c1, c2, hR, hL, hℓ]
  ring

end ESS

end
