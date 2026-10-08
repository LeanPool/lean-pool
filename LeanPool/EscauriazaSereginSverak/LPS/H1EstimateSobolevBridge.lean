/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityL2Tools
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevMollify
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateNonlinearity
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTimeRegularity
public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution

/-!
# The whole-space weak `H²` Hessian and Laplacian identity

Smooth compactly supported Sobolev approximations extend the Hessian/Laplacian
identity to the whole-space order-two class used by `lem:lps-H1-estimate`.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

private theorem lps_h1_compact_word_derivatives
    {g : Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) :
    ∀ α : List (Fin 3), HasCompactSupport (wordDeriv α g) := by
  intro α
  induction α generalizing g with
  | nil => simpa [wordDeriv] using hgc
  | cons j α ih =>
      have hderiv : HasCompactSupport (spatialDeriv g j) := by
        change HasCompactSupport (fun x => (fderiv ℝ g x) (basisVec j))
        exact hgc.fderiv_apply (𝕜 := ℝ) (basisVec j)
      exact ih (contDiff_wordDeriv hg [j]) hderiv

private theorem lps_h1_integral_sq_tendsto
    {f : ℕ → Vec3 → ℝ} {g : Vec3 → ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (h : Tendsto (fun n => eLpNorm (f n - g) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x : Vec3, (f n x) ^ (2 : ℕ)) atTop
      (𝓝 (∫ x : Vec3, (g x) ^ (2 : ℕ))) :=
  CKN.vorticity_tendsto_integral_sq hf hg h

private theorem lps_h1_weak_hessian_sq_limit
    {f : Vec3 → ℝ} {D : List (Fin 3) → Vec3 → ℝ}
    (hD : CKN.IsSobolevFamilyOn 2 Set.univ f D)
    {g : ℕ → Vec3 → ℝ}
    (hg : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n))
    (hgc : ∀ n, HasCompactSupport (g n))
    (hconv : ∀ α : List (Fin 3), α.length ≤ 2 →
      Tendsto (fun n => eLpNorm (wordDeriv α (g n) - D α) 2 volume)
        atTop (𝓝 0)) :
    Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ x : Vec3, (wordDeriv [i, j] (g n) x) ^ (2 : ℕ)) atTop
      (𝓝 (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x : Vec3, (D [i, j] x) ^ (2 : ℕ))) := by
  have hentry (i j : Fin 3) :
      Tendsto (fun n => ∫ x : Vec3,
        (wordDeriv [i, j] (g n) x) ^ (2 : ℕ)) atTop
        (𝓝 (∫ x : Vec3, (D [i, j] x) ^ (2 : ℕ))) := by
    have hmemD : MemLp (D [i, j]) 2 volume := by
      simpa only [Measure.restrict_univ] using hD.memL2 [i, j] (by simp)
    have hmemg (n : ℕ) : MemLp (wordDeriv [i, j] (g n)) 2 volume := by
      exact ((contDiff_wordDeriv (hg n) [i, j]).continuous.memLp_of_hasCompactSupport
        (lps_h1_compact_word_derivatives (hg n) (hgc n) [i, j]))
    exact lps_h1_integral_sq_tendsto hmemg hmemD (hconv [i, j] (by simp))
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact hentry i j

private theorem lps_h1_weak_laplacian_sq_limit
    {f : Vec3 → ℝ} {D : List (Fin 3) → Vec3 → ℝ}
    (hD : CKN.IsSobolevFamilyOn 2 Set.univ f D)
    {g : ℕ → Vec3 → ℝ}
    (hg : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n))
    (hgc : ∀ n, HasCompactSupport (g n))
    (hconv : ∀ α : List (Fin 3), α.length ≤ 2 →
      Tendsto (fun n => eLpNorm (wordDeriv α (g n) - D α) 2 volume)
        atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x : Vec3,
      (∑ i : Fin 3, wordDeriv [i, i] (g n) x) ^ (2 : ℕ)) atTop
      (𝓝 (∫ x : Vec3, (∑ i : Fin 3, D [i, i] x) ^ (2 : ℕ))) := by
  let L : Vec3 → ℝ := fun x => ∑ i : Fin 3, D [i, i] x
  let Ln : ℕ → Vec3 → ℝ := fun n x => ∑ i : Fin 3, wordDeriv [i, i] (g n) x
  have hmemL : MemLp L 2 volume := by
    dsimp [L]
    apply memLp_finsetSum Finset.univ
    intro i _
    simpa only [Measure.restrict_univ] using hD.memL2 [i, i] (by simp)
  have hmemLn (n : ℕ) : MemLp (Ln n) 2 volume := by
    dsimp [Ln]
    apply memLp_finsetSum Finset.univ
    intro i _
    exact (contDiff_wordDeriv (hg n) [i, i]).continuous.memLp_of_hasCompactSupport
      (lps_h1_compact_word_derivatives (hg n) (hgc n) [i, i])
  have hsum : Tendsto (fun n => ∑ i : Fin 3,
      eLpNorm (fun x : Vec3 => wordDeriv [i, i] (g n) x - D [i, i] x)
        2 volume) atTop (𝓝 0) := by
    have hsum' := tendsto_finsetSum
      (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i n => eLpNorm
        (fun x : Vec3 => wordDeriv [i, i] (g n) x - D [i, i] x) 2 volume)
      (x := atTop) (a := fun _ => (0 : ℝ≥0∞))
      (by
        intro i hi
        exact hconv [i, i] (by simp))
    simpa using hsum'
  have hbound (n : ℕ) : eLpNorm (Ln n - L) 2 volume ≤
      ∑ i : Fin 3,
        eLpNorm (fun x : Vec3 => wordDeriv [i, i] (g n) x - D [i, i] x)
          2 volume := by
    have heq : Ln n - L = fun x : Vec3 =>
        ∑ i : Fin 3, (wordDeriv [i, i] (g n) x - D [i, i] x) := by
      funext x
      simp [Ln, L, Finset.sum_sub_distrib]
    rw [heq]
    exact eLpNorm_sum_le (μ := volume) (p := (2 : ℝ≥0∞))
      (f := fun i : Fin 3 => fun x : Vec3 =>
        wordDeriv [i, i] (g n) x - D [i, i] x)
      (s := Finset.univ) (by norm_num)
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ eLpNorm (Ln n - L) 2 volume :=
    Filter.Eventually.of_forall fun _ => bot_le
  have hLconv : Tendsto (fun n => eLpNorm (Ln n - L) 2 volume) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hsum hnonneg (Filter.Eventually.of_forall hbound)
  exact lps_h1_integral_sq_tendsto hmemLn hmemL hLconv

/-- The order-zero, first and second spatial derivative fields of a component of a
strong solution, indexed by derivative words. -/
@[expose] def lpsH1SpatialFamily (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (i : Fin 3) : List (Fin 3) → ParabolicPoint → ℝ
  | [] => fun z => u z i
  | [j] => fun z => Du z i j
  | [j, k] => fun z => D2u z i j k
  | _ => fun _ => 0

/-- Space-time weak derivatives with square-integrable fields give spatial
order-two Sobolev families on almost every time slice
(`lem:lps-H1-estimate`). -/
theorem lps_spatial_sobolev_slices_ae_of_weak_derivs
    {a b : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (hDerivs : HasSpaceTimeWeakDerivs Set.univ (Ioo a b) u Du D2u Dtu)
    (hMemU : MemLp u 2
      (volume.restrict (spaceTimeSet Set.univ (Ioo a b))))
    (hMemDu : MemLp Du 2
      (volume.restrict (spaceTimeSet Set.univ (Ioo a b))))
    (hMemD2u : MemLp D2u 2
      (volume.restrict (spaceTimeSet Set.univ (Ioo a b)))) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      ∀ i : Fin 3,
        CKN.IsSobolevFamilyOn 2 Set.univ (fun x : Vec3 => u (x, t) i)
          (fun α x => lpsH1SpatialFamily u Du D2u i α (x, t)) := by
  have hSmeas : MeasurableSet (spaceTimeSet Set.univ (Ioo a b)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hpre : parabolicHomeomorph.symm ⁻¹'
      spaceTimeSet Set.univ (Ioo a b) =
        (Set.univ : Set Vec3) ×ˢ Ioo a b := by
    ext z
    rfl
  have hmp := CKN.parabolicHomeomorphSymm_measurePreserving.restrict_preimage hSmeas
  rw [hpre] at hmp
  have hMemUprod : MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z))
      2 (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)) :=
    hMemU.comp_measurePreserving hmp
  have hMemDuprod : MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z))
      2 (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)) :=
    hMemDu.comp_measurePreserving hmp
  have hMemD2uprod : MemLp (fun z : Vec3 × ℝ => D2u (parabolicHomeomorph.symm z))
      2 (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)) :=
    hMemD2u.comp_measurePreserving hmp
  have htest {φ : Vec3 × ℝ → ℝ}
      (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
      (hφsupp : tsupport φ ⊆ (Set.univ : Set Vec3) ×ˢ Ioo a b) :
      φ ∈ spaceTimeTestFunction (Set.univ : Set Vec3) (Ioo a b) := by
    refine ⟨hφ, hφc, ?_⟩
    change tsupport φ ⊆ (Set.univ : Set Vec3) ×ˢ Ioo a b
    exact hφsupp
  have hFamily (i : Fin 3) :
      CKN.IsL2SobolevFamilyOn 2 Set.univ (Ioo a b)
        (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i)
        (fun α z => lpsH1SpatialFamily u Du D2u i α
          (parabolicHomeomorph.symm z)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro α hα
      cases α with
      | nil =>
          exact (memLp_pi_iff.mp hMemUprod) i
      | cons j rest =>
          cases rest with
          | nil =>
              exact ((memLp_pi_iff.mp hMemDuprod) i).eval j
          | cons k rest' =>
              cases rest' with
              | nil =>
                  exact (((memLp_pi_iff.mp hMemD2uprod) i).eval j).eval k
              | cons l rest'' =>
                  simp only [List.length_cons, Nat.add_comm] at hα
                  have : False := by omega
                  exact this.elim
    · rfl
    · intro α j hα φ hφ hφc hφsupp
      let ψ : ParabolicPoint → ℝ := φ
      cases α with
      | nil =>
          have hψ : ψ ∈ spaceTimeTestFunction Set.univ (Ioo a b) :=
            htest hφ hφc hφsupp
          have hweak := (hDerivs.2.2.2.2 ψ hψ).1 i j
          rw [CKN.setIntegral_parabolic_to_product] at hweak
          rw [CKN.setIntegral_parabolic_to_product] at hweak
          simpa [ψ, parabolicHomeomorph_symm_apply,
            lpsH1SpatialFamily] using hweak
      | cons k rest =>
          cases rest with
          | nil =>
              have hψ : ψ ∈ spaceTimeTestFunction Set.univ (Ioo a b) :=
                htest hφ hφc hφsupp
              have hweak := (hDerivs.2.2.2.2 ψ hψ).2.1 i k j
              rw [CKN.setIntegral_parabolic_to_product] at hweak
              rw [CKN.setIntegral_parabolic_to_product] at hweak
              simpa [ψ, parabolicHomeomorph_symm_apply,
                lpsH1SpatialFamily] using hweak
          | cons l rest' =>
              have : False := by
                simp only [List.length_cons] at hα
                omega
              exact this.elim
  -- The finite component type lets the scalar slice theorem be intersected
  -- over all three components without changing its exceptional set.
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      ∀ i : Fin 3,
        CKN.IsSobolevFamilyOn 2 Set.univ (fun x : Vec3 => u (x, t) i)
          (fun α x => lpsH1SpatialFamily u Du D2u i α (x, t)) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [ESS.LPS.lps_sobolevFamily_spatialSlices_ae (hFamily i)] with t ht
    simpa only [parabolicHomeomorph_symm_apply] using ht
  exact hslice

/-- The space-time derivative witnesses in the strong class give spatial
order-two Sobolev families on almost every time slice
(`lem:lps-H1-estimate`). -/
theorem lps_strong_solution_h2_slices_ae
    {a b : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : ESS.IsLpsStrongSolution a b u Du p) :
    ∃ D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3,
      ∃ Dtu : ParabolicPoint → Vec3,
        HasSpaceTimeWeakDerivs Set.univ (Ioo a b) u Du D2u Dtu ∧
        ∀ᵐ t ∂(volume.restrict (Ioo a b)),
          ∀ i : Fin 3,
            CKN.IsSobolevFamilyOn 2 Set.univ (fun x : Vec3 => u (x, t) i)
              (fun α x => lpsH1SpatialFamily u Du D2u i α (x, t)) := by
  rcases hU with ⟨_hab, _hslices, _hcont, hHigher, _hp, _heq⟩
  rcases hHigher with ⟨D2u, Dtu, hDerivs, hMemU, hMemDu, hMemD2u, hMemDtu⟩
  exact ⟨D2u, Dtu, hDerivs,
    lps_spatial_sobolev_slices_ae_of_weak_derivs hDerivs hMemU hMemDu hMemD2u⟩

/-- For a scalar whole-space order-two Sobolev family, the `L²` Hessian square
equals the `L²` Laplacian square (`lem:lps-H1-estimate`). -/
theorem lps_h1_sobolev_hessian_eq_laplacian
    {f : Vec3 → ℝ} {D : List (Fin 3) → Vec3 → ℝ}
    (hD : CKN.IsSobolevFamilyOn 2 Set.univ f D) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      ∫ x : Vec3, (D [i, j] x) ^ (2 : ℕ)) =
      ∫ x : Vec3, (∑ i : Fin 3, D [i, i] x) ^ (2 : ℕ) := by
  obtain ⟨g, hg, hgc, hconv, _hbound⟩ :=
    CKN.sobolevFamily_smooth_approx (m := 2)
      (f := fun _ : Unit => f) (D := fun α _ => D α)
      (by intro _; exact hD)
  let g' : ℕ → Vec3 → ℝ := fun n => g n ()
  have hg' : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (g' n) := fun n => hg n ()
  have hgc' : ∀ n, HasCompactSupport (g' n) := fun n => hgc n ()
  have hconv' : ∀ α : List (Fin 3), α.length ≤ 2 →
      Tendsto (fun n => eLpNorm (wordDeriv α (g' n) - D α) 2 volume)
        atTop (𝓝 0) := by
    intro α hα
    exact hconv () α hα
  have hleft := lps_h1_weak_hessian_sq_limit hD hg' hgc' hconv'
  have hright := lps_h1_weak_laplacian_sq_limit hD hg' hgc' hconv'
  have hsmooth (n : ℕ) :
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x : Vec3, (wordDeriv [i, j] (g' n) x) ^ (2 : ℕ)) =
      ∫ x : Vec3,
        (∑ i : Fin 3, wordDeriv [i, i] (g' n) x) ^ (2 : ℕ) := by
    have hswap :
        (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x : Vec3, (wordDeriv [i, j] (g' n) x) ^ (2 : ℕ)) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x : Vec3, (mixedSecond (g' n) i j x) ^ (2 : ℕ) := by
      simp only [wordDeriv, mixedSecond]
      rw [Finset.sum_comm]
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x : Vec3, (mixedSecond (g' n) i j x) ^ (2 : ℕ) := hswap
      _ = ∫ x : Vec3, (∑ i : Fin 3, mixedSecond (g' n) i i x) ^ (2 : ℕ) :=
        CKN.hessian_l2_eq_laplacian_l2 (hg' n) (hgc' n)
      _ = ∫ x : Vec3,
          (∑ i : Fin 3, wordDeriv [i, i] (g' n) x) ^ (2 : ℕ) := by
        simp only [wordDeriv, mixedSecond]
  have hleft' : Tendsto
      (fun n => ∫ x : Vec3, (∑ i : Fin 3,
        wordDeriv [i, i] (g' n) x) ^ (2 : ℕ)) atTop
      (𝓝 (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x : Vec3, (D [i, j] x) ^ (2 : ℕ))) :=
    hleft.congr' (Filter.Eventually.of_forall fun n => hsmooth n)
  exact tendsto_nhds_unique hleft' hright

/-- The componentwise whole-space order-two Sobolev bridge identifies the
integrated Hessian square with the vector Laplacian square
(`lem:lps-H1-estimate`). -/
theorem lps_h1_vector_sobolev_hessian_eq_laplacian
    {D : Fin 3 → List (Fin 3) → Vec3 → ℝ}
    (hD : ∀ i : Fin 3,
      CKN.IsSobolevFamilyOn 2 Set.univ (D i []) (D i)) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      ∫ x : Vec3, (D i [j, k] x) ^ (2 : ℕ)) =
      ∫ x : Vec3,
        ∑ i : Fin 3, (∑ j : Fin 3, D i [j, j] x) ^ (2 : ℕ) := by
  let L : Vec3 → Vec3 := fun x i => ∑ j : Fin 3, D i [j, j] x
  have hLmem : MemLp L 2 volume := by
    apply memLp_pi_iff.mpr
    intro i
    apply memLp_finsetSum Finset.univ
    intro j _
    simpa only [Measure.restrict_univ] using
      (hD i).memL2 [j, j] (by simp)
  have hsum :
      (∑ i : Fin 3, ∫ x : Vec3, (L x i) ^ (2 : ℕ)) =
        ∫ x : Vec3, ∑ i : Fin 3, (L x i) ^ (2 : ℕ) := by
    symm
    exact integral_finsetSum (μ := volume) Finset.univ
      (f := fun (i : Fin 3) (x : Vec3) => (L x i) ^ (2 : ℕ))
      (by
        intro i hi
        exact ((hLmem.eval i).integrable_sq))
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        ∫ x : Vec3, (D i [j, k] x) ^ (2 : ℕ)) =
      ∑ i : Fin 3, ∫ x : Vec3, (∑ j : Fin 3, D i [j, j] x) ^ (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact lps_h1_sobolev_hessian_eq_laplacian (hD i)
    _ = ∑ i : Fin 3, ∫ x : Vec3, (L x i) ^ (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
    _ = ∫ x : Vec3, ∑ i : Fin 3, (L x i) ^ (2 : ℕ) := hsum
    _ = ∫ x : Vec3,
          ∑ i : Fin 3, (∑ j : Fin 3, D i [j, j] x) ^ (2 : ℕ) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp [L]

end ESS.LPS

end
