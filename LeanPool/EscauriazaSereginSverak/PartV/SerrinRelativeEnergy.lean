/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinGronwallInputs

/-!
# The relative energy inequality

For a finite-energy weak solution `u` with pressure in space-time `L⁵` and a
finite-energy weak solution `v` in `L^{10/3}` satisfying the energy inequality,
the squared `L²` distance `E(t) = ‖v(t) - u(t)‖₂²` obeys
`E(t) ≤ C ∫₀ᵗ ‖u(τ)‖₅⁵ E(τ) dτ` at almost every time. This is the zero-start
energy comparison of `lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- At almost every time, the slice difference obeys the fixed-time relative
convection bound. -/
theorem serrin_relative_slice_bound_ae {T : ℝ} {a b : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3} {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu) (hV : IsSerrinWeakSolution T b v Dv pv)
    (hu5 : MemLp u (ENNReal.ofReal 5)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    {K : ℝ} (hK : ∀ {u w : Vec3 → Vec3} {Dw : Vec3 → Fin 3 → Vec3},
      MemLp u (ENNReal.ofReal 5) volume → MemLp w 2 volume → MemLp Dw 2 volume →
      (∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => w x i) (fun x => Dw x i)) →
      |∫ x : Vec3, ∑ k : Fin 3, u x k * ∑ j : Fin 3, w x j * Dw x k j| ≤
        (1 / 2 : ℝ) * (∫ x : Vec3, ∑ k : Fin 3, ∑ j : Fin 3, Dw x k j ^ 2) +
          K * (eLpNorm u (ENNReal.ofReal 5) volume).toReal ^ 5 *
            ∫ x : Vec3, ∑ k : Fin 3, w x k ^ 2) :
    ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, u (x, τ) k * ∑ j : Fin 3,
          (v (x, τ) j - u (x, τ) j) * (Dv (x, τ) k j - Du (x, τ) k j)) ≤
        (1 / 2 : ℝ) * (∫ x : Vec3, ∑ k : Fin 3, ∑ j : Fin 3,
            (Dv (x, τ) k j - Du (x, τ) k j) ^ 2) +
          K * (eLpNorm (fun x : Vec3 => u (x, τ)) (ENNReal.ofReal 5) volume).toReal ^ 5 *
            ∫ x : Vec3, ∑ k : Fin 3, (v (x, τ) k - u (x, τ) k) ^ 2 := by
  filter_upwards [serrinWeak_slices_ae hU, serrinWeak_slices_ae hV,
    serrin_slice_memLp_ae (by simp) (by simp) hu5] with τ hu hv h5
  obtain ⟨hu2, hDu2, hug, -, -⟩ := hu
  obtain ⟨hv2, hDv2, hvg, -, -⟩ := hv
  have hwg : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => (fun x => v (x, τ) - u (x, τ)) x i)
      (fun x => (fun x => Dv (x, τ) - Du (x, τ)) x i) := by
    intro i j
    have h := serrin_weakPartialDeriv_sub (hv2.eval i) (hu2.eval i)
      ((hDv2.eval i).eval j) ((hDu2.eval i).eval j) (hvg i j) (hug i j)
    exact h
  have h := hK h5 (hv2.sub hu2) (hDv2.sub hDu2) hwg
  refine (le_abs_self _).trans (h.trans_eq ?_)
  simp only [Pi.sub_apply]

/-- The relative energy inequality at almost every time. -/
theorem serrin_relative_energy_inequality {T : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3} {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu) (hV : IsSerrinWeakSolution T a v Dv pv)
    (hu5 : MemLp u (ENNReal.ofReal 5)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hv103 : MemLp v (ENNReal.ofReal (10 / 3))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hvE : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * v (x, t) k) ≤
        (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) -
          2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Dv q k j * Dv q k j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, (v (x, t) k - u (x, t) k) ^ 2) ≤
        C * ∫ τ in (0 : ℝ)..t,
          (eLpNorm (fun x : Vec3 => u (x, τ)) (ENNReal.ofReal 5) volume).toReal ^ 5 *
            ∫ x : Vec3, ∑ k : Fin 3, (v (x, τ) k - u (x, τ) k) ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := serrin_slice_relative_bound
  refine ⟨2 * K, by positivity, ?_⟩
  set m : ℝ → ℝ := fun τ =>
    (eLpNorm (fun x : Vec3 => u (x, τ)) (ENNReal.ofReal 5) volume).toReal ^ 5 with hmdef
  set E : ℝ → ℝ := fun τ => ∫ x : Vec3, ∑ k : Fin 3, (v (x, τ) k - u (x, τ) k) ^ 2 with hEdef
  -- space-time memberships
  have hu2 := serrinWeak_velocity_memLp_two hU
  have hv2 := serrinWeak_velocity_memLp_two hV
  have hDu2 := serrinWeak_gradient_memLp_two hU
  have hDv2 := serrinWeak_gradient_memLp_two hV
  have hu103 : MemLp u (ENNReal.ofReal (10 / 3))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    serrin_memLp_interpolate (p := 2) (q := ENNReal.ofReal 5) (by norm_num) (by simp)
      (by rw [← ENNReal.ofReal_ofNat 2]; exact ENNReal.ofReal_le_ofReal (by norm_num))
      (ENNReal.ofReal_le_ofReal (by norm_num)) hu2 hu5
  have hNv (k : Fin 3) := serrin_convection_memLp (r := 10 / 3) (s := 5 / 4) (by norm_num)
    (by norm_num) (by norm_num) hv103 hDv2 k
  have hNu (k : Fin 3) := serrin_convection_memLp (r := 5) (s := 10 / 7) (by norm_num)
    (by norm_num) (by norm_num) hu5 hDu2 k
  have hNw (k : Fin 3) := serrin_convection_memLp (r := 10 / 3) (s := 5 / 4) (by norm_num)
    (by norm_num) (by norm_num) (hv103.sub hu103) (hDv2.sub hDu2) k
  have H1 : ENNReal.HolderTriple (ENNReal.ofReal 5) (ENNReal.ofReal (5 / 4)) 1 :=
    serrin_holder_ofReal (by norm_num) (by norm_num) (by norm_num)
  have H2 : ENNReal.HolderTriple (ENNReal.ofReal (10 / 3)) (ENNReal.ofReal (10 / 7)) 1 :=
    serrin_holder_ofReal (by norm_num) (by norm_num) (by norm_num)
  set μT : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) with hμT
  have hFN1 : Integrable (fun q : ParabolicPoint =>
      ∑ k : Fin 3, u q k * ∑ j : Fin 3, v q j * Dv q k j) μT :=
    integrable_finsetSum _ fun k _ => memLp_one_iff_integrable.mp
      ((hu5.eval k).mul (r := 1) (hNv k))
  have hFN2 : Integrable (fun q : ParabolicPoint =>
      ∑ k : Fin 3, v q k * ∑ j : Fin 3, u q j * Du q k j) μT :=
    integrable_finsetSum _ fun k _ => memLp_one_iff_integrable.mp
      ((hv103.eval k).mul (r := 1) (hNu k))
  have hFY : Integrable (fun q : ParabolicPoint =>
      ∑ k : Fin 3, u q k * ∑ j : Fin 3, (v q j - u q j) * (Dv q k j - Du q k j)) μT :=
    integrable_finsetSum _ fun k _ => memLp_one_iff_integrable.mp
      ((hu5.eval k).mul (r := 1) (hNw k))
  have hG (f g : ParabolicPoint → Fin 3 → Vec3) (hf : MemLp f 2 μT) (hg : MemLp g 2 μT) :
      Integrable (fun q => ∑ k : Fin 3, ∑ j : Fin 3, f q k j * g q k j) μT :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
      memLp_one_iff_integrable.mp (((hf.eval k).eval j).mul (r := 1) ((hg.eval k).eval j))
  have hGww : Integrable (fun q : ParabolicPoint =>
      ∑ k : Fin 3, ∑ j : Fin 3, (Dv q k j - Du q k j) ^ 2) μT :=
    (hG _ _ (hDv2.sub hDu2) (hDv2.sub hDu2)).congr (Eventually.of_forall fun q => by
      simp only [Pi.sub_apply, sq])
  -- almost every time slice identities
  have hrel : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      ∫ y : Vec3, (fun q : ParabolicPoint =>
        (∑ k : Fin 3, u q k * ∑ j : Fin 3, v q j * Dv q k j) +
        (∑ k : Fin 3, v q k * ∑ j : Fin 3, u q j * Du q k j) -
        ∑ k : Fin 3, u q k * ∑ j : Fin 3, (v q j - u q j) * (Dv q k j - Du q k j)) (y, τ) = 0 := by
    filter_upwards [serrinWeak_slice_ae hU, serrinWeak_slice_ae hV,
      serrin_slice_memLp_ae (by simp) (by simp) hu5,
      serrin_slice_memLp_ae (by simp) (by simp) hv103] with τ hsu hsv h5 h103
    exact serrin_slice_relative hsu h5 hsv h103
  have hbd := serrin_relative_slice_bound_ae hU hV hu5 hK
  -- the time functions
  have hm : IntegrableOn m (Ioo 0 T) := serrin_slice_norm5_integrable hu5
  have hEm := serrin_distance_aestronglyMeasurable hU hV
  obtain ⟨Bu, hBu⟩ := serrinWeak_slice_energy_bound hU
  obtain ⟨Bv, hBv⟩ := serrinWeak_slice_energy_bound hV
  have hEb : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)), ‖E τ‖ ≤ 2 * (Bu + Bv) := by
    filter_upwards [hBu, hBv, serrinWeak_slices_ae hU, serrinWeak_slices_ae hV]
      with τ hu hv hsu hsv
    have hu2' := hsu.1
    have hv2' := hsv.1
    have hiu : Integrable (fun x => ∑ k : Fin 3, u (x, τ) k ^ 2) volume :=
      integrable_finsetSum _ fun k _ => (memLp_two_iff_integrable_sq_norm
        (hu2'.eval k).aestronglyMeasurable).mp (hu2'.eval k) |>.congr
          (Eventually.of_forall fun x => by simp)
    have hiv : Integrable (fun x => ∑ k : Fin 3, v (x, τ) k ^ 2) volume :=
      integrable_finsetSum _ fun k _ => (memLp_two_iff_integrable_sq_norm
        (hv2'.eval k).aestronglyMeasurable).mp (hv2'.eval k) |>.congr
          (Eventually.of_forall fun x => by simp)
    have hE0 : 0 ≤ E τ := integral_nonneg fun x => Finset.sum_nonneg fun k _ => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hE0]
    calc
      E τ ≤ ∫ x : Vec3, 2 * (∑ k : Fin 3, u (x, τ) k ^ 2) + 2 * ∑ k : Fin 3, v (x, τ) k ^ 2 := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x =>
          Finset.sum_nonneg fun k _ => sq_nonneg _) ((hiu.const_mul 2).add (hiv.const_mul 2))
          (Eventually.of_forall fun x => ?_)
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun k _ => by nlinarith only [sq_nonneg (v (x, τ) k + u (x, τ) k)]
      _ = 2 * (∫ x : Vec3, ∑ k : Fin 3, u (x, τ) k ^ 2) +
          2 * ∫ x : Vec3, ∑ k : Fin 3, v (x, τ) k ^ 2 := by
        rw [integral_add (hiu.const_mul 2) (hiv.const_mul 2), integral_const_mul,
          integral_const_mul]
      _ ≤ 2 * (Bu + Bv) := by linarith only [hu, hv]
  have hmE : IntegrableOn (fun τ => m τ * E τ) (Ioo 0 T) :=
    hm.mul_bdd (c := 2 * (Bu + Bv)) hEm hEb
  have hcross := serrin_cross_identity hU hV hu5 hv103
  have heu := serrin_energy_equality hU hu5
  rw [ae_restrict_iff' measurableSet_Ioo] at hcross heu hvE ⊢
  have hsl := (ae_restrict_iff' measurableSet_Ioo).mp
    ((serrinWeak_slices_ae hU).and (serrinWeak_slices_ae hV))
  filter_upwards [hcross, heu, hvE, hsl] with t hc he hve hs htI
  obtain ⟨⟨hut, -, -, -, -⟩, ⟨hvt, -, -, -, -⟩⟩ := hs htI
  specialize hc htI
  specialize he htI
  specialize hve htI
  have ht0 : 0 ≤ t := htI.1.le
  have hQ := serrin_slab_restrict_le htI.2.le
  set μt : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)) with hμt
  -- (a) the convection pairings equal the relative convection form
  have hFall : Integrable (fun q : ParabolicPoint =>
      (∑ k : Fin 3, u q k * ∑ j : Fin 3, v q j * Dv q k j) +
      (∑ k : Fin 3, v q k * ∑ j : Fin 3, u q j * Du q k j) -
      ∑ k : Fin 3, u q k * ∑ j : Fin 3, (v q j - u q j) * (Dv q k j - Du q k j)) μT :=
    (hFN1.add hFN2).sub hFY
  have hsum0 := serrin_slab_integral_eq_zero ht0 htI.2.le (hFall.mono_measure hQ) hrel
  have hFN1t := hFN1.mono_measure hQ
  have hFN2t := hFN2.mono_measure hQ
  have hFYt := hFY.mono_measure hQ
  have hFN12t : Integrable (fun q : ParabolicPoint =>
      (∑ k : Fin 3, u q k * ∑ j : Fin 3, v q j * Dv q k j) +
      ∑ k : Fin 3, v q k * ∑ j : Fin 3, u q j * Du q k j) μt := hFN1t.add hFN2t
  rw [integral_sub hFN12t hFYt, integral_add hFN1t hFN2t] at hsum0
  -- (b) the gradient pairings
  have hGuv := (hG Du Dv hDu2 hDv2).mono_measure hQ
  have hGuu := (hG Du Du hDu2 hDu2).mono_measure hQ
  have hGvv := (hG Dv Dv hDv2 hDv2).mono_measure hQ
  have hGwwt := hGww.mono_measure hQ
  have hGvu : (∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
      ∑ k : Fin 3, ∑ j : Fin 3, Dv q k j * Du q k j) =
      ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Dv q k j := by
    congr 1
    funext q
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hGexp : (∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
      ∑ k : Fin 3, ∑ j : Fin 3, (Dv q k j - Du q k j) ^ 2) =
      (∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        ∑ k : Fin 3, ∑ j : Fin 3, Dv q k j * Dv q k j) -
      2 * (∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Dv q k j) +
      ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j := by
    have h2uv : Integrable (fun q : ParabolicPoint =>
        2 * ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Dv q k j) μt := hGuv.const_mul 2
    have hA : Integrable (fun q : ParabolicPoint =>
        (∑ k : Fin 3, ∑ j : Fin 3, Dv q k j * Dv q k j) -
          2 * ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Dv q k j) μt := hGvv.sub h2uv
    calc
      (∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, (Dv q k j - Du q k j) ^ 2) =
          ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ((∑ k : Fin 3, ∑ j : Fin 3, Dv q k j * Dv q k j) -
              2 * ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Dv q k j) +
            ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j := by
        congr 1
        funext q
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by
        rw [integral_add hA hGuu, integral_sub hGvv h2uv, integral_const_mul]
  have hGww0 : 0 ≤ ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
      ∑ k : Fin 3, ∑ j : Fin 3, (Dv q k j - Du q k j) ^ 2 :=
    integral_nonneg fun q => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ =>
      sq_nonneg _
  -- (c) the relative convection bound, integrated in time
  have hii1 := serrin_intervalIntegrable_of_slab ht0 hFYt
  have hii2 := serrin_intervalIntegrable_of_slab ht0 hGwwt
  have hmEt : IntervalIntegrable (fun τ => m τ * E τ) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht0]
    exact hmE.mono_set fun τ hτ => ⟨hτ.1, lt_of_le_of_lt hτ.2 htI.2⟩
  have hbdt : ∀ᵐ τ ∂(volume.restrict (Icc 0 t)),
      (∫ y : Vec3, (fun q : ParabolicPoint =>
        ∑ k : Fin 3, u q k * ∑ j : Fin 3, (v q j - u q j) * (Dv q k j - Du q k j)) (y, τ)) ≤
      (1 / 2 : ℝ) * (∫ y : Vec3, (fun q : ParabolicPoint =>
        ∑ k : Fin 3, ∑ j : Fin 3, (Dv q k j - Du q k j) ^ 2) (y, τ)) + K * (m τ * E τ) := by
    have h' := (ae_restrict_iff' measurableSet_Ioo).mp hbd
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h', Measure.ae_ne volume 0] with τ hτ hτ0 hτI
    have hτ' := hτ ⟨lt_of_le_of_ne hτI.1 (Ne.symm hτ0), lt_of_le_of_lt hτI.2 htI.2⟩
    simp only [hmdef, hEdef]
    rw [← mul_assoc]
    exact hτ'
  have hmono := intervalIntegral.integral_mono_ae_restrict ht0 hii1
    ((hii2.const_mul (1 / 2 : ℝ)).add (hmEt.const_mul K)) hbdt
  rw [intervalIntegral.integral_add (hii2.const_mul (1 / 2 : ℝ)) (hmEt.const_mul K),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    serrin_intervalIntegral_eq_slab ht0 hFYt, serrin_intervalIntegral_eq_slab ht0 hGwwt] at hmono
  -- (d) the squared distance in terms of pairings
  have hiv : ∀ k : Fin 3, Integrable (fun x => v (x, t) k * v (x, t) k) volume :=
    fun k => (hvt.eval k).integrable_mul (hvt.eval k)
  have hiu : ∀ k : Fin 3, Integrable (fun x => u (x, t) k * u (x, t) k) volume :=
    fun k => (hut.eval k).integrable_mul (hut.eval k)
  have hivu : ∀ k : Fin 3, Integrable (fun x => v (x, t) k * u (x, t) k) volume :=
    fun k => (hvt.eval k).integrable_mul (hut.eval k)
  have hsv : Integrable (fun x => ∑ k : Fin 3, v (x, t) k * v (x, t) k) volume :=
    integrable_finsetSum _ fun k _ => hiv k
  have hsu : Integrable (fun x => ∑ k : Fin 3, u (x, t) k * u (x, t) k) volume :=
    integrable_finsetSum _ fun k _ => hiu k
  have hsvu : Integrable (fun x => ∑ k : Fin 3, v (x, t) k * u (x, t) k) volume :=
    integrable_finsetSum _ fun k _ => hivu k
  have hEt : E t = (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * v (x, t) k) -
      2 * (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * u (x, t) k) +
      ∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k := by
    have h2 : Integrable (fun x => 2 * ∑ k : Fin 3, v (x, t) k * u (x, t) k) volume :=
      hsvu.const_mul 2
    have hA : Integrable (fun x => (∑ k : Fin 3, v (x, t) k * v (x, t) k) -
        2 * ∑ k : Fin 3, v (x, t) k * u (x, t) k) volume := hsv.sub h2
    rw [← integral_const_mul, ← integral_sub hsv h2, ← integral_add hA hsu]
    simp only [hEdef]
    congr 1
    funext x
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- (e) conclusion
  change E t ≤ 2 * K * ∫ τ in (0 : ℝ)..t, m τ * E τ
  rw [hEt]
  rw [hGvu] at hc
  linarith only [hc, he, hve, hsum0, hmono, hGexp, hGww0]

end ESS
