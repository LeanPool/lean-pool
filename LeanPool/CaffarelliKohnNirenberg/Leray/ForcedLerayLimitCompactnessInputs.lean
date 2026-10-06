/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitTenThirds

/-!
# The uniform slice and gradient bounds for the forced compactness argument

In the proof of `prop:forced-limit`, `lem:forced-energy-bounds` supplies the
uniform slice and gradient bounds required by `lem:compactness`: along any
sequence of positive regularization parameters, on every compact spatial set
and every compact time interval of `(0,∞)`, the local kinetic energies and the
local dissipations of the forced regularized solutions are bounded
independently of the sequence index.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The uniform slice and gradient bounds of `lem:compactness` for the forced
regularized solutions (`lem:forced-energy-bounds`), on compact subsets of
`ℝ³ × (0,∞)`. -/
theorem forcedLerayLimit_compactness_bounds
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n) :
    (∀ C : Set Vec3, IsCompact C → C ⊆ (Set.univ : Set Vec3) →
      ∀ a' b : ℝ, Icc a' b ⊆ Ioi 0 →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t, t ∈ Icc a' b →
        (∫⁻ x in C, ENNReal.ofReal
          (vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf (εseq n) (x, t))) ^ (2 : ℝ)
            ∂volume) ≤ M) ∧
    (∀ C : Set Vec3, IsCompact C → C ⊆ (Set.univ : Set Vec3) →
      ∀ a' b : ℝ, Icc a' b ⊆ Ioi 0 →
      ∃ G : ℝ≥0∞, G < ⊤ ∧ ∀ n,
        (∫⁻ t in Icc a' b, ∫⁻ x in C,
          ENNReal.ofReal (CKN.spatialGradientSq (forcedRegVelocity ρ a ha f hf (εseq n))
            (forcedRegGradient ρ a ha f hf (εseq n)) (x, t)) ∂volume) ≤ G) := by
  -- the energy constants on `[0,T]`
  have hEnergy : ∀ T : ℝ, 0 < T → ∃ E G : ℝ, ∀ n,
      (∀ t ∈ Icc 0 T, ∑ i : Fin 3, ∫ x : Vec3,
        forcedRegVelocity ρ a ha f hf (εseq n) (x, t) i ^ 2 ≤ E) ∧
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        forcedRegGradient ρ a ha f hf (εseq n) z i j ^ 2 ≤ G := by
    intro T hT
    refine ⟨Real.exp T * ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
        ∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2),
      ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
        (∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2) +
        T * (Real.exp T * ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
          ∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2))) / 2,
      fun n => ?_⟩
    have hε := hseq n
    obtain ⟨⟨hSlice, hcont, -, -⟩, -, hR2, -, hE⟩ := forcedRegularised ρ a ha f hf (εseq n) hε
    obtain ⟨hkin, hgrad⟩ := forcedLerayLimit_energy_bounds ρ (εseq n) hε a ha.1 f hf
      (forcedRegVelocity ρ a ha f hf (εseq n)) (forcedRegGradient ρ a ha f hf (εseq n))
      hSlice hcont (fun S hS => (forcedRegVelocity_memLp_slab ρ a ha f hf (εseq n) hε S hS).1)
      (fun S hS => (hR2 S hS).1) (fun t ht => (hE t ht).2) T hT
    exact ⟨hkin, by linarith only [hgrad]⟩
  refine ⟨fun C _ _ a' b hab => ?_, fun C _ _ a' b hab => ?_⟩
  · obtain ⟨E, G, hEG⟩ := hEnergy (max b 0 + 1) (by positivity)
    refine ⟨ENNReal.ofReal E, ENNReal.ofReal_lt_top, fun n t ht => ?_⟩
    have hε := hseq n
    obtain ⟨⟨hSlice, -, -, -⟩, -, -, -, -⟩ := forcedRegularised ρ a ha f hf (εseq n) hε
    have ht0 : 0 < t := hab ht
    have hmem := hSlice t ht0.le
    have hpt : ∀ x : Vec3, ENNReal.ofReal
        (vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf (εseq n) (x, t))) ^ (2 : ℝ) =
        ENNReal.ofReal (∑ i : Fin 3, forcedRegVelocity ρ a ha f hf (εseq n) (x, t) i ^ 2) := by
      intro x
      have hnn : 0 ≤ vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf (εseq n) (x, t)) :=
        Real.sqrt_nonneg _
      rw [ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num)]
      congr 1
      rw [vec3EuclideanNorm, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    have hint : Integrable (fun x : Vec3 =>
        ∑ i : Fin 3, forcedRegVelocity ρ a ha f hf (εseq n) (x, t) i ^ 2) :=
      integrable_finsetSum _ fun i _ => (hmem.eval i).integrable_sq
    calc (∫⁻ x in C, ENNReal.ofReal
          (vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf (εseq n) (x, t))) ^ (2 : ℝ))
        ≤ ∫⁻ x, ENNReal.ofReal
          (vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf (εseq n) (x, t))) ^ (2 : ℝ) :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (∫ x, ∑ i : Fin 3,
            forcedRegVelocity ρ a ha f hf (εseq n) (x, t) i ^ 2) := by
          simp only [hpt]
          exact (ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal E := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_finsetSum _ fun i _ => (hmem.eval i).integrable_sq]
          exact (hEG n).1 t ⟨ht0.le, ht.2.trans ((le_max_left b 0).trans (le_add_of_nonneg_right
            zero_le_one))⟩
  · obtain ⟨E, G, hEG⟩ := hEnergy (max b 0 + 1) (by positivity)
    refine ⟨ENNReal.ofReal G, ENNReal.ofReal_lt_top, fun n => ?_⟩
    have hε := hseq n
    obtain ⟨-, -, hR2, -, -⟩ := forcedRegularised ρ a ha f hf (εseq n) hε
    set T : ℝ := max b 0 + 1 with hTdef
    have hT : 0 < T := by positivity
    have hsub : Icc a' b ⊆ Ioo 0 T := fun t ht =>
      ⟨hab ht, ht.2.trans_lt ((le_max_left b 0).trans_lt (lt_add_one _))⟩
    let u := forcedRegVelocity ρ a ha f hf (εseq n)
    let Du := forcedRegGradient ρ a ha f hf (εseq n)
    have hgm : Measurable fun z : ParabolicPoint =>
        ENNReal.ofReal (CKN.spatialGradientSq u Du z) := by
      have hDm : Measurable Du := by
        change Measurable (forcedMollifiedGrad (forcedRegVelocity ρ a ha f hf (εseq n)))
        rw [forcedRegVelocity_eq ρ ha hf hε]
        exact measurable_forcedMollifiedGrad (forcedRegRep_stronglyMeasurable ρ (εseq n) hε ha hf)
          (fun t i => forcedRegRep_locallyIntegrable ρ (εseq n) hε ha hf t i)
      apply ENNReal.measurable_ofReal.comp
      unfold CKN.spatialGradientSq
      fun_prop
    calc (∫⁻ t in Icc a' b, ∫⁻ x in C, ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)))
        ≤ ∫⁻ t in Ioo 0 T, ∫⁻ x, ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) :=
          (lintegral_mono fun t => setLIntegral_le_lintegral _ _).trans
            (lintegral_mono_set hsub)
      _ = ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
            ENNReal.ofReal (CKN.spatialGradientSq u Du z) :=
          ((lintegral_slab_eq_prod _ (Ioo 0 T)).trans
            (lintegral_prod_symm _ hgm.aemeasurable)).symm
      _ = ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3,
            ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), Du z i j ^ 2) := by
          rw [← regUniformDissipation_eq_slab, forcedHopf_dissipation_eq_ofReal u Du T
            (hR2 T hT).1]
      _ ≤ ENNReal.ofReal G := ENNReal.ofReal_le_ofReal ((hEG n).2)

end CKN.Leray

end
