/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossDensityLimit
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakSlices

/-!
# The cross-testing identity

For two finite-energy weak solutions with pressures, one of which lies in
space-time `L⁵`, the pairing of their slices at almost every time equals the
initial pairing minus the time integrals of the convection and gradient
pairings. This is the cross-testing identity of `lem:pv-serrin-uniqueness`,
obtained here without Serrin regularity: the pairing is computed on
mollified slices and the mollification and cutoff are removed.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A time integral of spatial integrals is the space-time integral over the
slab, for an integrable density. -/
theorem serrin_intervalIntegral_eq_slab {t : ℝ} (ht : 0 ≤ t) {F : ParabolicPoint → ℝ}
    (hF : Integrable F (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) :
    (∫ τ in (0 : ℝ)..t, ∫ y : Vec3, F (y, τ)) =
      ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), F q := by
  rw [intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]
  rw [serrin_slab_measure_eq] at hF ⊢
  exact (integral_prod_symm (fun q : Vec3 × ℝ => F q) hF).symm

/-- Conjugate real exponents give a Hölder triple of ENNReal.ofReal exponents. -/
theorem serrin_holder_ofReal {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : p⁻¹ + q⁻¹ = 1) :
    ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 1 := by
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_inv_of_pos hq,
    ← ENNReal.ofReal_add (by positivity) (by positivity), h, ENNReal.ofReal_one, inv_one]

/-- Real exponents with `1/p + 1/q = 1/r` give a Hölder triple. -/
theorem serrin_holder_ofReal3 {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : p⁻¹ + q⁻¹ = r⁻¹) :
    ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) (ENNReal.ofReal r) := by
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_inv_of_pos hq,
    ← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_add (by positivity) (by positivity), h]

/-- `1 ≤ ofReal p` for `1 ≤ p`. -/
theorem serrin_one_le_ofReal {p : ℝ} (hp : 1 ≤ p) : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal hp

/-- Convection terms `∑ⱼ wⱼ ∂ⱼ zₖ` of a field in `L^r` with a square-integrable
gradient. -/
theorem serrin_convection_memLp {T r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hrs : r⁻¹ + (2 : ℝ)⁻¹ = s⁻¹)
    {w : ParabolicPoint → Vec3} {Dz : ParabolicPoint → Fin 3 → Vec3}
    (hw : MemLp w (ENNReal.ofReal r)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hDz : MemLp Dz 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (k : Fin 3) :
    MemLp (fun q => ∑ j : Fin 3, w q j * Dz q k j) (ENNReal.ofReal s)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  have hH : ENNReal.HolderTriple (ENNReal.ofReal r) (ENNReal.ofReal 2) (ENNReal.ofReal s) :=
    serrin_holder_ofReal3 hr (by norm_num) hs hrs
  refine memLp_finsetSum (f := fun j q => w q j * Dz q k j) _ fun j _ => ?_
  have h2 : MemLp (fun q => Dz q k j) (ENNReal.ofReal 2)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    rw [ENNReal.ofReal_ofNat]
    exact (hDz.eval k).eval j
  exact (hw.eval j).mul h2

/-- The spatial integrals of an integrable slab density are interval integrable. -/
theorem serrin_intervalIntegrable_of_slab {t : ℝ} (ht : 0 ≤ t) {F : ParabolicPoint → ℝ}
    (hF : Integrable F (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) :
    IntervalIntegrable (fun τ => ∫ y : Vec3, F (y, τ)) volume 0 t := by
  rw [serrin_slab_measure_eq] at hF
  have h := hF.integral_prod_right
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  exact (integrableOn_Ioc_iff_integrableOn_Ioo).mpr h

/-- The initial mollified components are the mollified datum. -/
theorem serrinMol_initial {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du p) (n : ℕ) (k : Fin 3) (y : Vec3) :
    serrinMol u (serrinKernel n) k y 0 =
      CKN.mollify (fun x => a x k) (serrinRadius n) (serrinRadius_pos n) y := by
  have hρ : ContDiff ℝ (⊤ : ℕ∞) (serrinKernel n) :=
    CKN.mollifier_contDiff (d := 3) (serrinRadius_pos n)
  have hρc : HasCompactSupport (serrinKernel n) :=
    CKN.mollifier_hasCompactSupport (d := 3) (serrinRadius_pos n)
  have h := hU.initial _ (serrinKernelTest_contDiff hρ k y)
    (serrinKernelTest_hasCompactSupport hρc k y)
  have hleft : (∫ x : Vec3, ∑ i : Fin 3, u (x, 0) i * serrinKernelTest (serrinKernel n) k y x i) =
      serrinMol u (serrinKernel n) k y 0 := by
    simp only [serrinMol, serrinPairing_kernelTest]
  have hright : (∫ x : Vec3, ∑ i : Fin 3, a x i * serrinKernelTest (serrinKernel n) k y x i) =
      ∫ x : Vec3, a x k * serrinKernel n (y - x) := by
    congr 1
    funext x
    simp [serrinKernelTest]
  rw [← hleft, h, hright]
  exact (serrin_mollify_eq_integral _ _ y).symm

/-- Cutoff-weighted pairings of mollified square-integrable fields converge. -/
theorem serrin_slice_pairing_limit {f g : Vec3 → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    Tendsto (fun n => ∫ y : Vec3, serrinCutoff n y *
        CKN.mollify f (serrinRadius n) (serrinRadius_pos n) y *
        CKN.mollify g (serrinRadius n) (serrinRadius_pos n) y) atTop
      (𝓝 (∫ y : Vec3, f y * g y)) := by
  have h := serrin_weighted_pairing_tendsto (μ := (volume : Measure Vec3)) (p := 2) (q := 2)
    (by norm_num) hf hg
    (Eventually.of_forall fun n => (CKN.mollify_continuous (serrinRadius_pos n)
      (hf.locallyIntegrable (by norm_num))).aestronglyMeasurable)
    (Eventually.of_forall fun n => (CKN.mollify_continuous (serrinRadius_pos n)
      (hg.locallyIntegrable (by norm_num))).aestronglyMeasurable)
    (CKN.tendsto_eLpNorm_sub_zero_mollify (by norm_num) (by simp) hf serrinRadius_tendsto
      serrinRadius_pos)
    (CKN.tendsto_eLpNorm_sub_zero_mollify (by norm_num) (by simp) hg serrinRadius_tendsto
      serrinRadius_pos)
    (cs := fun n y => serrinCutoff n y) (c := fun _ => 1)
    (fun n => (serrinCutoff_contDiff n).continuous.aestronglyMeasurable)
    (fun n y => serrinCutoff_abs_le_one n y) aestronglyMeasurable_const (fun _ => by simp)
    (Eventually.of_forall fun y => serrinCutoff_tendsto_one y)
  simpa only [one_mul] using h

/-- The cross-testing identity for two finite-energy weak solutions with
pressures, the first in space-time `L⁵` and the second in `L^{10/3}`. -/
theorem serrin_cross_identity {T : ℝ} {a b : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3} {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu) (hV : IsSerrinWeakSolution T b v Dv pv)
    (hu5 : MemLp u (ENNReal.ofReal 5)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hv103 : MemLp v (ENNReal.ofReal (10 / 3))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
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
  -- space-time memberships
  have hu2 := serrinWeak_velocity_memLp_two hU
  have hv2 := serrinWeak_velocity_memLp_two hV
  have hDu2 := serrinWeak_gradient_memLp_two hU
  have hDv2 := serrinWeak_gradient_memLp_two hV
  have hu52 : MemLp u (ENNReal.ofReal (5 / 2))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    serrin_memLp_interpolate (p := 2) (q := ENNReal.ofReal 5) (by norm_num) (by simp)
      (by rw [← ENNReal.ofReal_ofNat 2]; exact ENNReal.ofReal_le_ofReal (by norm_num))
      (ENNReal.ofReal_le_ofReal (by norm_num)) hu2 hu5
  have hv52 : MemLp v (ENNReal.ofReal (5 / 2))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    serrin_memLp_interpolate (p := 2) (q := ENNReal.ofReal (10 / 3)) (by norm_num) (by simp)
      (by rw [← ENNReal.ofReal_ofNat 2]; exact ENNReal.ofReal_le_ofReal (by norm_num))
      (ENNReal.ofReal_le_ofReal (by norm_num)) hv2 hv103
  have hNv (k : Fin 3) := serrin_convection_memLp (r := 10 / 3) (s := 5 / 4) (by norm_num)
    (by norm_num) (by norm_num) hv103 hDv2 k
  have hNu (k : Fin 3) := serrin_convection_memLp (r := 5) (s := 10 / 7) (by norm_num)
    (by norm_num) (by norm_num) hu5 hDu2 k
  have H1 : ENNReal.HolderTriple (ENNReal.ofReal 5) (ENNReal.ofReal (5 / 4)) 1 :=
    serrin_holder_ofReal (by norm_num) (by norm_num) (by norm_num)
  have H2 : ENNReal.HolderTriple (ENNReal.ofReal (10 / 3)) (ENNReal.ofReal (10 / 7)) 1 :=
    serrin_holder_ofReal (by norm_num) (by norm_num) (by norm_num)
  have H4 : ENNReal.HolderTriple (ENNReal.ofReal (5 / 2)) (ENNReal.ofReal (5 / 3)) 1 :=
    serrin_holder_ofReal (by norm_num) (by norm_num) (by norm_num)
  have hgood := (ae_restrict_iff' measurableSet_Ioo).mp
    ((serrinWeak_slices_ae hU).and (serrinWeak_slices_ae hV))
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hgood] with t hgt ht
  obtain ⟨⟨hut, -, -, -, -⟩, ⟨hvt, -, -, -, -⟩⟩ := hgt ht
  have htT : t ≤ T := ht.2.le
  -- the limits of the two cross densities
  obtain ⟨hIvu, hLvu⟩ := serrinCrossDensity_limit (w := v) (z := u) (Dw := Dv) (Dz := Du)
    (pw := pv) htT (by simp) (by simp) (ENNReal.one_le_ofReal.mpr (by norm_num)) (by simp)
    (ENNReal.one_le_ofReal.mpr (by norm_num)) (by simp)
    (ENNReal.one_le_ofReal.mpr (by norm_num)) (by simp)
    (fun k => hu5.eval k) hNv (fun k j => (hDu2.eval k).eval j)
    (fun k j => (hDv2.eval k).eval j) (fun k => hu2.eval k) (fun k => hu52.eval k)
    hV.pressure
  obtain ⟨hIuv, hLuv⟩ := serrinCrossDensity_limit (w := u) (z := v) (Dw := Du) (Dz := Dv)
    (pw := pu) htT (ENNReal.one_le_ofReal.mpr (by norm_num)) (by simp)
    (ENNReal.one_le_ofReal.mpr (by norm_num)) (by simp)
    (ENNReal.one_le_ofReal.mpr (by norm_num)) (by simp)
    (ENNReal.one_le_ofReal.mpr (by norm_num)) (by simp)
    (fun k => hv103.eval k) hNu (fun k j => (hDv2.eval k).eval j)
    (fun k j => (hDu2.eval k).eval j) (fun k => hv2.eval k) (fun k => hv52.eval k)
    hU.pressure
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
