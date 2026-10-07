/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossIdentity
public import LeanPool.EscauriazaSereginSverak.LPS.MixedCrossDensityLimit

/-!
# Assembly of mixed-norm cross-testing limits

The regularized weak identity passes to the limit once both oriented
cross-density limits are available. The finite mixed-norm and endpoint
providers supply these limits separately.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Cross-testing identity from the two oriented mixed-norm density limits. -/
theorem lps_cross_identity_from_density_limits {T : ℝ} {a b : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3} {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu) (hV : IsSerrinWeakSolution T b v Dv pv)
    (hDensityVU : ∀ t, t ∈ Ioo (0 : ℝ) T →
      (∀ᶠ n in atTop, Integrable (serrinCrossDensity v Dv pv u Du n (serrinCutoff n))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) ∧
      Tendsto (fun n => ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        serrinCrossDensity v Dv pv u Du n (serrinCutoff n) q) atTop
        (𝓝 (-(∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, u q k * ∑ j : Fin 3, v q j * Dv q k j)
          - ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Dv q k j)))
    (hDensityUV : ∀ t, t ∈ Ioo (0 : ℝ) T →
      (∀ᶠ n in atTop, Integrable (serrinCrossDensity u Du pu v Dv n (serrinCutoff n))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) ∧
      Tendsto (fun n => ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        serrinCrossDensity u Du pu v Dv n (serrinCutoff n) q) atTop
        (𝓝 (-(∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, v q k * ∑ j : Fin 3, u q j * Du q k j)
          - ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Dv q k j * Du q k j))) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, b x k * a x k) =
        (-(∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, u q k * ∑ j : Fin 3, v q j * Dv q k j)
          - ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Dv q k j) +
        (-(∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, v q k * ∑ j : Fin 3, u q j * Du q k j)
          - ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Dv q k j * Du q k j) := by
  have hgood := (ae_restrict_iff' measurableSet_Ioo).mp
    ((serrinWeak_slices_ae hU).and (serrinWeak_slices_ae hV))
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hgood] with t hgt ht
  obtain ⟨⟨hut, -, -, -, -⟩, ⟨hvt, -, -, -, -⟩⟩ := hgt ht
  have htT : t ≤ T := ht.2.le
  -- the two oriented density limits
  obtain ⟨hIvu, hLvu⟩ := hDensityVU t ht
  obtain ⟨hIuv, hLuv⟩ := hDensityUV t ht
  set M : (Vec3 → ℝ) → ℕ → Vec3 → ℝ := fun f n =>
    CKN.mollify f (serrinRadius n) (serrinRadius_pos n) with hMdef
  have hMc (f : Vec3 → ℝ) (hf : MemLp f 2 volume) (n : ℕ) : Continuous (M f n) :=
    CKN.mollify_continuous (serrinRadius_pos n) (hf.locallyIntegrable (by norm_num))
  have hvk (k : Fin 3) : MemLp (fun x => v (x, t) k) 2 volume := hvt.eval k
  have huk (k : Fin 3) : MemLp (fun x => u (x, t) k) 2 volume := hut.eval k
  have hbk (k : Fin 3) : MemLp (fun x => b x k) 2 volume := hV.datum.eval k
  have hak (k : Fin 3) : MemLp (fun x => a x k) 2 volume := hU.datum.eval k
  -- the left side
  have hLform (n : ℕ) :
      (∫ y, serrinCutoff n y * ((∑ k : Fin 3, serrinMol v (serrinKernel n) k y t *
          serrinMol u (serrinKernel n) k y t) -
        ∑ k : Fin 3, serrinMol v (serrinKernel n) k y 0 * serrinMol u (serrinKernel n) k y 0)) =
      (∑ k : Fin 3, ∫ y, serrinCutoff n y * M (fun x => v (x, t) k) n y *
          M (fun x => u (x, t) k) n y) -
        ∑ k : Fin 3, ∫ y, serrinCutoff n y * M (fun x => b x k) n y * M (fun x => a x k) n y := by
    have hint (f g : Vec3 → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
        Integrable (fun y => serrinCutoff n y * M f n y * M g n y) volume :=
      (((serrinCutoff_contDiff n).continuous.mul (hMc f hf n)).mul
        (hMc g hg n)).integrable_of_hasCompactSupport
        ((serrinCutoff_hasCompactSupport n).mul_right.mul_right)
    rw [← integral_finsetSum _ fun k _ => hint _ _ (hvk k) (huk k),
      ← integral_finsetSum _ fun k _ => hint _ _ (hbk k) (hak k),
      ← integral_sub (integrable_finsetSum _ fun k _ => hint _ _ (hvk k) (huk k))
        (integrable_finsetSum _ fun k _ => hint _ _ (hbk k) (hak k))]
    congr 1
    funext y
    simp only [serrinMol_initial hU, serrinMol_initial hV, mul_sub, Finset.mul_sum, hMdef]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [serrinMol_kernel_eq, serrinMol_kernel_eq]
      simp only [serrinSM]
      ring
    · exact Finset.sum_congr rfl fun k _ => by ring
  have hL : Tendsto (fun n => ∫ y, serrinCutoff n y * ((∑ k : Fin 3,
        serrinMol v (serrinKernel n) k y t * serrinMol u (serrinKernel n) k y t) -
        ∑ k : Fin 3, serrinMol v (serrinKernel n) k y 0 * serrinMol u (serrinKernel n) k y 0))
      atTop (𝓝 ((∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * u (x, t) k) -
        (∫ x : Vec3, ∑ k : Fin 3, b x k * a x k))) := by
    simp_rw [hLform]
    have hi1 (k : Fin 3) : Integrable (fun x : Vec3 => v (x, t) k * u (x, t) k) volume :=
      (hvk k).integrable_mul (huk k)
    have hi2 (k : Fin 3) : Integrable (fun x : Vec3 => b x k * a x k) volume :=
      (hbk k).integrable_mul (hak k)
    rw [integral_finsetSum _ fun k _ => hi1 k, integral_finsetSum _ fun k _ => hi2 k]
    exact (tendsto_finsetSum _ fun k _ => serrin_slice_pairing_limit (hvk k) (huk k)).sub
      (tendsto_finsetSum _ fun k _ => serrin_slice_pairing_limit (hbk k) (hak k))
  -- the right side
  have hR : Tendsto (fun n => ∫ τ in (0 : ℝ)..t,
        ((∫ y, serrinCrossDensity v Dv pv u Du n (serrinCutoff n) (y, τ)) +
          ∫ y, serrinCrossDensity u Du pu v Dv n (serrinCutoff n) (y, τ))) atTop
      (𝓝 ((-(∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, u q k * ∑ j : Fin 3, v q j * Dv q k j)
          - ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Dv q k j) +
        (-(∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, v q k * ∑ j : Fin 3, u q j * Du q k j)
          - ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Dv q k j * Du q k j))) := by
    refine (hLvu.add hLuv).congr' ?_
    filter_upwards [hIvu, hIuv] with n h1 h2
    rw [intervalIntegral.integral_add (serrin_intervalIntegrable_of_slab ht.1.le h1)
      (serrin_intervalIntegrable_of_slab ht.1.le h2),
      serrin_intervalIntegral_eq_slab ht.1.le h1, serrin_intervalIntegral_eq_slab ht.1.le h2]
  have hLR := fun n => serrin_cross_regularized hU hV n (serrinCutoff_contDiff n)
    (serrinCutoff_hasCompactSupport n) ⟨ht.1.le, htT⟩
  exact tendsto_nhds_unique hL (hR.congr fun n => (hLR n).symm)

end ESS
