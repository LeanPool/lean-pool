/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationSpatialGlue
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationEquation
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationSliceLimit
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongHopf

/-!
# Gluing strong solutions

Two strong solutions on `[a, b]` and `[b, c]` whose slices at `b` agree, together
with their gradients, glue to a strong solution on `[a, c]`
(`lem:lps-continuation`). The spatial weak derivatives glue by a time cutoff, the
weak time derivative and the momentum equation through the boundary terms at the
junction, which cancel because the two slices agree.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The field equal to `f` up to and including time `b` and to `g` afterwards. -/
@[expose] def lpsGlue {α : Type} (b : ℝ) (f g : ParabolicPoint → α) (z : ParabolicPoint) : α :=
  if z.2 ≤ b then f z else g z

theorem lpsGlue_of_le {α : Type} {b : ℝ} {f g : ParabolicPoint → α} {z : ParabolicPoint}
    (h : z.2 ≤ b) : lpsGlue b f g z = f z := by
  simp [lpsGlue, h]

theorem lpsGlue_of_gt {α : Type} {b : ℝ} {f g : ParabolicPoint → α} {z : ParabolicPoint}
    (h : b < z.2) : lpsGlue b f g z = g z := by
  simp [lpsGlue, not_le.mpr h]

theorem lpsEqIntegrand_glue_of_le {b : ℝ} {U W : ParabolicPoint → Vec3}
    {DU DW : ParabolicPoint → Fin 3 → Vec3} {pU pW : ParabolicPoint → ℝ}
    {φ : Vec3 × ℝ → Vec3} {z : ParabolicPoint} (h : z.2 ≤ b) :
    lpsEqIntegrand (lpsGlue b U W) (lpsGlue b DU DW) (lpsGlue b pU pW) φ z =
      lpsEqIntegrand U DU pU φ z := by
  unfold lpsEqIntegrand
  simp only [lpsGlue_of_le h]

theorem lpsEqIntegrand_glue_of_gt {b : ℝ} {U W : ParabolicPoint → Vec3}
    {DU DW : ParabolicPoint → Fin 3 → Vec3} {pU pW : ParabolicPoint → ℝ}
    {φ : Vec3 × ℝ → Vec3} {z : ParabolicPoint} (h : b < z.2) :
    lpsEqIntegrand (lpsGlue b U W) (lpsGlue b DU DW) (lpsGlue b pU pW) φ z =
      lpsEqIntegrand W DW pW φ z := by
  unfold lpsEqIntegrand
  simp only [lpsGlue_of_gt h]

/-- Componentwise slice facts of a strong solution at a time of its interval. -/
theorem lps_strong_component_slice_facts {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p) {t : ℝ} (ht : t ∈ Icc t₀ T) (i : Fin 3) :
    Tendsto (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) i - u (x, t) i) 2 volume)
        (nhdsWithin t (Icc t₀ T)) (nhds 0) ∧
      MemLp (fun x : Vec3 => u (x, t) i) 2 volume ∧
      ∀ s ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, s) i) 2 volume := by
  refine ⟨?_, memLp_pi_iff.1 (lps_strong_solution_slice_memLp_two hU ht).1 i,
    fun s hs => memLp_pi_iff.1 (lps_strong_solution_slice_memLp_two hU hs).1 i⟩
  refine lps_component_l2_tendsto (f := fun s x => u (x, s)) ?_ (hU.2.2.1 t ht).1 i
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (((lps_strong_solution_slice_memLp_two hU hs).1).sub
    (lps_strong_solution_slice_memLp_two hU ht).1).aestronglyMeasurable

/-- Two strong solutions with the same terminal and initial slice glue to a strong
solution on the union of the intervals (`lem:lps-continuation`). -/
theorem lps_strong_solution_glue {a b c : ℝ}
    {U W : ParabolicPoint → Vec3} {DU DW : ParabolicPoint → Fin 3 → Vec3}
    {pU pW : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution a b U DU pU) (hW : IsLpsStrongSolution b c W DW pW)
    (htrace : (fun x : Vec3 => W (x, b)) =ᵐ[volume] (fun x : Vec3 => U (x, b)))
    (hgrad : (fun x : Vec3 => DW (x, b)) =ᵐ[volume] (fun x : Vec3 => DU (x, b))) :
    IsLpsStrongSolution a c (lpsGlue b U W) (lpsGlue b DU DW) (lpsGlue b pU pW) := by
  have hU' := hU
  have hW' := hW
  obtain ⟨hab, hS₁, hC₁, ⟨D2₁, Dt₁, hD₁, hu₁, hDu₁, hD2₁, hDt₁⟩, hp₁, hE₁⟩ := hU'
  obtain ⟨hbc, hS₂, hC₂, ⟨D2₂, Dt₂, hD₂, hu₂, hDu₂, hD2₂, hDt₂⟩, hp₂, hE₂⟩ := hW'
  have hu : MemLp (lpsGlue b U W) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a c))) :=
    lps_memLp_slab_glue hu₁ hu₂ (fun z hz => lpsGlue_of_le hz) (fun z hz => lpsGlue_of_gt hz)
  have hDu : MemLp (lpsGlue b DU DW) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a c))) :=
    lps_memLp_slab_glue hDu₁ hDu₂ (fun z hz => lpsGlue_of_le hz) (fun z hz => lpsGlue_of_gt hz)
  have hD2 : MemLp (lpsGlue b D2₁ D2₂) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a c))) :=
    lps_memLp_slab_glue hD2₁ hD2₂ (fun z hz => lpsGlue_of_le hz) (fun z hz => lpsGlue_of_gt hz)
  have hDt : MemLp (lpsGlue b Dt₁ Dt₂) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a c))) :=
    lps_memLp_slab_glue hDt₁ hDt₂ (fun z hz => lpsGlue_of_le hz) (fun z hz => lpsGlue_of_gt hz)
  have hp : MemLp (lpsGlue b pU pW) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a c))) :=
    lps_memLp_slab_glue hp₁ hp₂ (fun z hz => lpsGlue_of_le hz) (fun z hz => lpsGlue_of_gt hz)
  refine ⟨hab.trans hbc, ?_, ?_, ⟨lpsGlue b D2₁ D2₂, lpsGlue b Dt₁ Dt₂, ?_, hu, hDu, hD2, hDt⟩,
    hp, ?_⟩
  · intro t ht
    by_cases h : t ≤ b
    · have e : ∀ x : Vec3, lpsGlue b U W (x, t) = U (x, t) := fun x => lpsGlue_of_le h
      have e' : ∀ x : Vec3, lpsGlue b DU DW (x, t) = DU (x, t) := fun x => lpsGlue_of_le h
      simp only [e, e']
      exact hS₁ t ⟨ht.1, h⟩
    · have hgt : b < t := not_le.mp h
      have e : ∀ x : Vec3, lpsGlue b U W (x, t) = W (x, t) := fun x => lpsGlue_of_gt hgt
      have e' : ∀ x : Vec3, lpsGlue b DU DW (x, t) = DW (x, t) := fun x => lpsGlue_of_gt hgt
      simp only [e, e']
      exact hS₂ t ⟨hgt.le, ht.2⟩
  · intro t ht
    exact ⟨lps_glue_l2_continuity hab hbc (F := lpsGlue b U W) (fun z hz => lpsGlue_of_le hz)
        (fun z hz => lpsGlue_of_gt hz) (fun t ht => (hC₁ t ht).1) (fun t ht => (hC₂ t ht).1)
        htrace t ht,
      lps_glue_l2_continuity hab hbc (F := lpsGlue b DU DW) (fun z hz => lpsGlue_of_le hz)
        (fun z hz => lpsGlue_of_gt hz) (fun t ht => (hC₁ t ht).2) (fun t ht => (hC₂ t ht).2)
        hgrad t ht⟩
  · refine ⟨ESS.LPS.lps_locallyIntegrableOn_of_memLp hu,
    ESS.LPS.lps_locallyIntegrableOn_of_memLp hDu,
      ESS.LPS.lps_locallyIntegrableOn_of_memLp hD2, ESS.LPS.lps_locallyIntegrableOn_of_memLp
        hDt, ?_⟩
    intro φ hφ
    refine ⟨fun i j => ?_, fun i j k => ?_, fun i => ?_⟩
    · exact lps_spatial_weak_glue hab hbc (F₁ := fun z => U z i) (F₂ := fun z => W z i)
        (F := fun z => lpsGlue b U W z i) (G₁ := fun z => DU z i j) (G₂ := fun z => DW z i j)
        (G := fun z => lpsGlue b DU DW z i j) (j := j)
        (memLp_pi_iff.1 hu₁ i) (memLp_pi_iff.1 (memLp_pi_iff.1 hDu₁ i) j)
        (memLp_pi_iff.1 hu₂ i) (memLp_pi_iff.1 (memLp_pi_iff.1 hDu₂ i) j)
        (fun φ hφ => (hD₁.2.2.2.2 φ hφ).1 i j) (fun φ hφ => (hD₂.2.2.2.2 φ hφ).1 i j)
        (fun z hz => by simp only [lpsGlue_of_le hz]) (fun z hz => by simp only [lpsGlue_of_gt hz])
        (fun z hz => by simp only [lpsGlue_of_le hz]) (fun z hz => by simp only [lpsGlue_of_gt hz])
        hφ
    · exact lps_spatial_weak_glue hab hbc (F₁ := fun z => DU z i j) (F₂ := fun z => DW z i j)
        (F := fun z => lpsGlue b DU DW z i j) (G₁ := fun z => D2₁ z i j k)
        (G₂ := fun z => D2₂ z i j k) (G := fun z => lpsGlue b D2₁ D2₂ z i j k) (j := k)
        (memLp_pi_iff.1 (memLp_pi_iff.1 hDu₁ i) j)
        (memLp_pi_iff.1 (memLp_pi_iff.1 (memLp_pi_iff.1 hD2₁ i) j) k)
        (memLp_pi_iff.1 (memLp_pi_iff.1 hDu₂ i) j)
        (memLp_pi_iff.1 (memLp_pi_iff.1 (memLp_pi_iff.1 hD2₂ i) j) k)
        (fun φ hφ => (hD₁.2.2.2.2 φ hφ).2.1 i j k) (fun φ hφ => (hD₂.2.2.2.2 φ hφ).2.1 i j k)
        (fun z hz => by simp only [lpsGlue_of_le hz]) (fun z hz => by simp only [lpsGlue_of_gt hz])
        (fun z hz => by simp only [lpsGlue_of_le hz]) (fun z hz => by simp only [lpsGlue_of_gt hz])
        hφ
    · obtain ⟨hc₁, hb₁, hs₁⟩ := lps_strong_component_slice_facts hU ⟨hab.le, le_rfl⟩ i
      obtain ⟨hc₂, hb₂, hs₂⟩ := lps_strong_component_slice_facts hW ⟨le_rfl, hbc.le⟩ i
      have htr : (fun x : Vec3 => W (x, b) i) =ᵐ[volume] (fun x : Vec3 => U (x, b) i) := by
        filter_upwards [htrace] with x hx
        rw [hx]
      exact lps_time_weak_glue hab hbc (F₁ := fun z => U z i) (F₂ := fun z => W z i)
        (F := fun z => lpsGlue b U W z i) (G₁ := fun z => Dt₁ z i) (G₂ := fun z => Dt₂ z i)
        (G := fun z => lpsGlue b Dt₁ Dt₂ z i)
        (memLp_pi_iff.1 hu₁ i) (memLp_pi_iff.1 hDt₁ i)
        (memLp_pi_iff.1 hu₂ i) (memLp_pi_iff.1 hDt₂ i)
        (fun φ hφ => (hD₁.2.2.2.2 φ hφ).2.2 i) (fun φ hφ => (hD₂.2.2.2.2 φ hφ).2.2 i)
        hc₁ hc₂ hb₁ hs₁ hb₂ hs₂ htr
        (fun z hz => by simp only [lpsGlue_of_le hz]) (fun z hz => by simp only [lpsGlue_of_gt hz])
        (fun z hz => by simp only [lpsGlue_of_le hz]) (fun z hz => by simp only [lpsGlue_of_gt hz])
        hφ
  · intro φ hφ
    change ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a c),
      lpsEqIntegrand (lpsGlue b U W) (lpsGlue b DU DW) (lpsGlue b pU pW) φ z = 0
    have hφ' := hφ
    obtain ⟨hφs, hφc, -⟩ := hφ
    obtain ⟨hI, -⟩ := lps_eqIntegrand_integrable hu hDu hp hφ'
    rw [lps_slab_integral_split hab.le hbc.le hI]
    have hmeas1 : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)) :=
      MeasurableSet.univ.prod measurableSet_Ioo
    have hmeas2 : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c)) :=
      MeasurableSet.univ.prod measurableSet_Ioo
    have c1 : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b),
        lpsEqIntegrand (lpsGlue b U W) (lpsGlue b DU DW) (lpsGlue b pU pW) φ z) =
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), lpsEqIntegrand U DU pU φ z :=
      setIntegral_congr_fun hmeas1 fun z hz => lpsEqIntegrand_glue_of_le hz.2.2.le
    have c2 : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c),
        lpsEqIntegrand (lpsGlue b U W) (lpsGlue b DU DW) (lpsGlue b pU pW) φ z) =
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c), lpsEqIntegrand W DW pW φ z :=
      setIntegral_congr_fun hmeas2 fun z hz => lpsEqIntegrand_glue_of_gt hz.2.1
    have hlim₁ := lps_vector_pairing_tendsto (S := Icc a b) (t₀ := b) hφs hφc
      (hC₁ b ⟨hab.le, le_rfl⟩).1
      (fun s hs => (lps_strong_solution_slice_memLp_two hU hs).1)
      (lps_strong_solution_slice_memLp_two hU ⟨hab.le, le_rfl⟩).1
    have hlim₂ := lps_vector_pairing_tendsto (S := Icc b c) (t₀ := b) hφs hφc
      (hC₂ b ⟨le_rfl, hbc.le⟩).1
      (fun s hs => (lps_strong_solution_slice_memLp_two hW hs).1)
      (lps_strong_solution_slice_memLp_two hW ⟨le_rfl, hbc.le⟩).1
    have hR := lps_equation_boundary_right (S := fun _ => True) hab (fun _ _ _ _ => trivial)
      hu₁ hDu₁ hp₁ (fun ψ hψ _ => hE₁ ψ hψ) hφ' trivial (lps_slice_limit_right hlim₁)
    have hL := lps_equation_boundary_left (S := fun _ => True) hbc (fun _ _ _ _ => trivial)
      hu₂ hDu₂ hp₂ (fun ψ hψ _ => hE₂ ψ hψ) hφ' trivial (lps_slice_limit_left hlim₂)
    have hℓ : (∫ x : Vec3, ∑ i : Fin 3, W (x, b) i * φ (x, b) i) =
        ∫ x : Vec3, ∑ i : Fin 3, U (x, b) i * φ (x, b) i := by
      refine integral_congr_ae ?_
      filter_upwards [htrace] with x hx
      rw [hx]
    rw [c1, c2, hR, hL, hℓ]
    ring

end ESS

end
