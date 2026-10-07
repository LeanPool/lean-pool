/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossLimitTerms
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossRegularized

/-!
# The limit of the cross densities

As the mollification radius tends to zero and the cutoff radius to infinity,
the space-time integral of a cross density converges to minus the convection
pairing and the gradient pairing. This is the limit passage on the right side
of the cross-testing identity in `lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Integrability and the limit of the space-time integral of a cross density. -/
theorem serrinCrossDensity_limit {t T : ℝ} (ht : t ≤ T)
    {w z : ParabolicPoint → Vec3} {Dw Dz : ParabolicPoint → Fin 3 → Vec3}
    {pw : ParabolicPoint → ℝ}
    {p1 q1 p4 q4 : ℝ≥0∞} [ENNReal.HolderTriple p1 q1 1] [ENNReal.HolderTriple p4 q4 1]
    (hp1 : 1 ≤ p1) (hp1t : p1 ≠ ⊤) (hq1 : 1 ≤ q1) (hq1t : q1 ≠ ⊤)
    (hp4 : 1 ≤ p4) (hp4t : p4 ≠ ⊤) (hq4 : 1 ≤ q4) (hq4t : q4 ≠ ⊤)
    (hz1 : ∀ k, MemLp (fun r => z r k) p1
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hN : ∀ k, MemLp (fun r => ∑ j : Fin 3, w r j * Dw r k j) q1
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hDz : ∀ k j, MemLp (fun r => Dz r k j) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hDw : ∀ k j, MemLp (fun r => Dw r k j) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hz2 : ∀ k, MemLp (fun r => z r k) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hz4 : ∀ k, MemLp (fun r => z r k) p4
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hpw : MemLp pw q4
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    (∀ᶠ n in atTop, Integrable (serrinCrossDensity w Dw pw z Dz n (serrinCutoff n))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) ∧
    Tendsto (fun n => ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        serrinCrossDensity w Dw pw z Dz n (serrinCutoff n) q) atTop
      (𝓝 (-(∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, z q k * ∑ j : Fin 3, w q j * Dw q k j)
        - ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Dz q k j * Dw q k j)) := by
  set μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))
  obtain ⟨C, hC0, hCb⟩ := serrinCutoff_deriv_bound
  have hη (n : ℕ) : Continuous (serrinCutoff n) := (serrinCutoff_contDiff n).continuous
  have hηb (n : ℕ) : ∃ B, ∀ y, |serrinCutoff n y| ≤ B := ⟨1, serrinCutoff_abs_le_one n⟩
  have hdη (n : ℕ) (j : Fin 3) : Continuous (spatialDeriv (serrinCutoff n) j) :=
    ((serrinCutoff_contDiff n).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdηb (j : Fin 3) (n : ℕ) : ∃ B, ∀ y, |spatialDeriv (serrinCutoff n) j y| ≤ B :=
    ⟨C * (1 / ((n : ℝ) + 1)), fun y => hCb n j y⟩
  -- the four families of terms
  let A1 : ℕ → Fin 3 → ParabolicPoint → ℝ := fun n k q =>
    serrinCutoff n q.1 * serrinSM (fun r => z r k) n q *
      serrinSM (fun r => ∑ j : Fin 3, w r j * Dw r k j) n q
  let A2 : ℕ → Fin 3 → Fin 3 → ParabolicPoint → ℝ := fun n k j q =>
    serrinCutoff n q.1 * serrinSM (fun r => Dz r k j) n q * serrinSM (fun r => Dw r k j) n q
  let A3 : ℕ → Fin 3 → Fin 3 → ParabolicPoint → ℝ := fun n k j q =>
    spatialDeriv (serrinCutoff n) j q.1 * serrinSM (fun r => z r k) n q *
      serrinSM (fun r => Dw r k j) n q
  let A4 : ℕ → Fin 3 → ParabolicPoint → ℝ := fun n k q =>
    spatialDeriv (serrinCutoff n) k q.1 * serrinSM (fun r => z r k) n q * serrinSM pw n q
  have hdens (n : ℕ) (q : ParabolicPoint) :
      serrinCrossDensity w Dw pw z Dz n (serrinCutoff n) q =
        -(∑ k : Fin 3, A1 n k q) - (∑ k : Fin 3, ∑ j : Fin 3, A2 n k j q)
          - (∑ k : Fin 3, ∑ j : Fin 3, A3 n k j q) + ∑ k : Fin 3, A4 n k q := by
    simp only [serrinCrossDensity, A1, A2, A3, A4, Finset.mul_sum, mul_assoc]
  -- eventual integrability of each term
  have hI1 : ∀ᶠ n in atTop, ∀ k, Integrable (A1 n k) μ := by
    rw [eventually_all]
    exact fun k => serrin_weighted_term_integrable ht hp1 hp1t hq1 hq1t (hz1 k) (hN k) hη hηb
  have hI2 : ∀ᶠ n in atTop, ∀ k j, Integrable (A2 n k j) μ := by
    rw [eventually_all]
    intro k
    rw [eventually_all]
    exact fun j => serrin_weighted_term_integrable (p := 2) (q := 2) ht (by norm_num) (by simp)
      (by norm_num) (by simp) (hDz k j) (hDw k j) hη hηb
  have hI3 : ∀ᶠ n in atTop, ∀ k j, Integrable (A3 n k j) μ := by
    rw [eventually_all]
    intro k
    rw [eventually_all]
    exact fun j => serrin_weighted_term_integrable (p := 2) (q := 2) ht (by norm_num) (by simp)
      (by norm_num) (by simp) (hz2 k) (hDw k j) (fun n => hdη n j) (hdηb j)
  have hI4 : ∀ᶠ n in atTop, ∀ k, Integrable (A4 n k) μ := by
    rw [eventually_all]
    exact fun k => serrin_weighted_term_integrable ht hp4 hp4t hq4 hq4t (hz4 k) hpw
      (fun n => hdη n k) (hdηb k)
  have hdensf (n : ℕ) : serrinCrossDensity w Dw pw z Dz n (serrinCutoff n) =
      fun q => -(∑ k : Fin 3, A1 n k q) - (∑ k : Fin 3, ∑ j : Fin 3, A2 n k j q)
          - (∑ k : Fin 3, ∑ j : Fin 3, A3 n k j q) + ∑ k : Fin 3, A4 n k q :=
    funext (hdens n)
  have hIall : ∀ᶠ n in atTop, Integrable (serrinCrossDensity w Dw pw z Dz n (serrinCutoff n)) μ
      ∧ (∫ q, serrinCrossDensity w Dw pw z Dz n (serrinCutoff n) q ∂μ) =
        -(∑ k : Fin 3, ∫ q, A1 n k q ∂μ) - (∑ k : Fin 3, ∑ j : Fin 3, ∫ q, A2 n k j q ∂μ)
          - (∑ k : Fin 3, ∑ j : Fin 3, ∫ q, A3 n k j q ∂μ) + ∑ k : Fin 3, ∫ q, A4 n k q ∂μ := by
    filter_upwards [hI1, hI2, hI3, hI4] with n h1 h2 h3 h4
    have i1 : Integrable (fun q => ∑ k : Fin 3, A1 n k q) μ :=
      integrable_finsetSum _ fun k _ => h1 k
    have i2 : Integrable (fun q => ∑ k : Fin 3, ∑ j : Fin 3, A2 n k j q) μ :=
      integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => h2 k j
    have i3 : Integrable (fun q => ∑ k : Fin 3, ∑ j : Fin 3, A3 n k j q) μ :=
      integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => h3 k j
    have i4 : Integrable (fun q => ∑ k : Fin 3, A4 n k q) μ :=
      integrable_finsetSum _ fun k _ => h4 k
    have i1n : Integrable (fun q => -(∑ k : Fin 3, A1 n k q)) μ := i1.neg
    have i12 : Integrable (fun q => -(∑ k : Fin 3, A1 n k q) -
        ∑ k : Fin 3, ∑ j : Fin 3, A2 n k j q) μ := i1n.sub i2
    have i123 : Integrable (fun q => -(∑ k : Fin 3, A1 n k q) -
        (∑ k : Fin 3, ∑ j : Fin 3, A2 n k j q) - ∑ k : Fin 3, ∑ j : Fin 3, A3 n k j q) μ :=
      i12.sub i3
    rw [hdensf n]
    refine ⟨i123.add i4, ?_⟩
    rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1n i2, integral_neg,
      integral_finsetSum _ fun k _ => h1 k, integral_finsetSum _ fun k _ => h4 k,
      integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => h2 k j,
      integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => h3 k j]
    simp only [integral_finsetSum _ fun j _ => h2 _ j, integral_finsetSum _ fun j _ => h3 _ j]
  refine ⟨hIall.mono fun n h => h.1, ?_⟩
  have hL1 (k : Fin 3) := serrin_cutoff_pairing_limit ht hp1 hp1t hq1 hq1t (hz1 k) (hN k)
  have hL2 (k j : Fin 3) := serrin_cutoff_pairing_limit (p := 2) (q := 2) ht (by norm_num)
    (by simp) (by norm_num) (by simp) (hDz k j) (hDw k j)
  have hL3 (k j : Fin 3) := serrin_cutoff_deriv_pairing_limit (p := 2) (q := 2) ht
    (by norm_num) (by simp) (by norm_num) (by simp) (hz2 k) (hDw k j) j
  have hL4 (k : Fin 3) := serrin_cutoff_deriv_pairing_limit ht hp4 hp4t hq4 hq4t (hz4 k) hpw k
  have hlim := (((tendsto_finsetSum Finset.univ fun k _ => hL1 k).neg.sub
    (tendsto_finsetSum Finset.univ fun k _ =>
      tendsto_finsetSum Finset.univ fun j _ => hL2 k j)).sub
    (tendsto_finsetSum Finset.univ fun k _ =>
      tendsto_finsetSum Finset.univ fun j _ => hL3 k j)).add
    (tendsto_finsetSum Finset.univ fun k _ => hL4 k)
  simp only [Finset.sum_const_zero, sub_zero, add_zero] at hlim
  have hint1 (k : Fin 3) : Integrable (fun q => z q k * ∑ j : Fin 3, w q j * Dw q k j) μ :=
    memLp_one_iff_integrable.mp (((hz1 k).mono_measure (serrin_slab_restrict_le ht)).mul
      (r := 1) ((hN k).mono_measure (serrin_slab_restrict_le ht)))
  have hint2 (k j : Fin 3) : Integrable (fun q => Dz q k j * Dw q k j) μ :=
    memLp_one_iff_integrable.mp (((hDz k j).mono_measure (serrin_slab_restrict_le ht)).mul
      (r := 1) ((hDw k j).mono_measure (serrin_slab_restrict_le ht)))
  rw [integral_finsetSum _ fun k _ => hint1 k,
    integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hint2 k j]
  simp only [integral_finsetSum _ fun j _ => hint2 _ j]
  refine hlim.congr' ?_
  filter_upwards [hIall] with n hn
  exact hn.2.symm

end ESS
