/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatOrbitSolutionDuality
public import LeanPool.EscauriazaSereginSverak.PartV.HeatOrbitSolutionEnergy

/-!
# The weak heat equation for the heat orbit of a datum in `J`

At each positive time the spatial gradient of the heat orbit is a weak
gradient, so the gradient pairing `∫ ∇h : ∇φ` equals `-∫ h · Δφ` slice by
slice.  The remaining space-time pairing `∫∫ h · (-∂ₜφ - Δφ)` vanishes by
`heatConv_backwardHeatOp_integral_eq_zero`.  This is the weak heat equation
clause of the heat orbit in `prop:pv-local-solution`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

private theorem integrable_mul_of_bound_on_support {μ : Measure (Vec3 × ℝ)}
    {F g : Vec3 × ℝ → ℝ} (hF : AEStronglyMeasurable F μ) (hg : Integrable g μ) {M : ℝ}
    (hM : ∀ z, g z ≠ 0 → |F z| ≤ M) : Integrable (fun z => F z * g z) μ := by
  refine (hg.norm.const_mul M).mono' (hF.mul hg.aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  by_cases hz : g z = 0
  · simp [hz]
  · rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM z hz) (norm_nonneg _)

private theorem mem_tsupport_of_fderiv_apply_ne_zero {f : Vec3 × ℝ → ℝ} {z v : Vec3 × ℝ}
    (h : fderiv ℝ f z v ≠ 0) : z ∈ tsupport f :=
  support_fderiv_subset ℝ (Function.mem_support.2 fun h0 => h (by rw [h0]; rfl))

private theorem mem_tsupport_of_second_fderiv_ne_zero {f : Vec3 × ℝ → ℝ} {z v w : Vec3 × ℝ}
    (h : fderiv ℝ (fun q => fderiv ℝ f q v) z w ≠ 0) : z ∈ tsupport f := by
  have h1 := mem_tsupport_of_fderiv_apply_ne_zero h
  have h2 : tsupport (fun q => fderiv ℝ f q v) ⊆ tsupport (fderiv ℝ f) :=
    tsupport_comp_subset (g := fun L : (Vec3 × ℝ) →L[ℝ] ℝ => L v) rfl (fderiv ℝ f)
  exact tsupport_fderiv_subset ℝ (h2 h1)

/-- Fubini on a slab `ℝ³ × I`: the space-time integral of an integrable
function is the time integral of its spatial integrals. -/
theorem integral_spaceTimeSet_univ_eq {I : Set ℝ} {G : ParabolicPoint → ℝ}
    (hG : Integrable G (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I))) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) I, G z = ∫ t in I, ∫ x : Vec3, G (x, t) := by
  have hG' : Integrable (fun z : Vec3 × ℝ => G (z.1, z.2))
      ((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict I)) := by
    rw [Measure.prod_restrict]
    exact hG
  change (∫ z : Vec3 × ℝ in (Set.univ : Set Vec3) ×ˢ I,
    G (z.1, z.2) ∂((volume : Measure Vec3).prod (volume : Measure ℝ))) = _
  rw [← Measure.prod_restrict, integral_prod_symm _ hG', Measure.restrict_univ]

/-- (h6) The heat orbit of a datum in `J` solves the heat equation weakly on
every slab `ℝ³ × (0, τ)`. -/
theorem heatOrbit_weak_heat_equation {a : Vec3 → Vec3} (ha : IsInJ a) {τ : ℝ}
    {φ : Vec3 × ℝ → Vec3}
    (hφmem : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 τ)) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
      (-(∑ i : Fin 3, heatOrbit a z i * timePartial (fun y => φ y i) z)) +
        ∑ i : Fin 3, ∑ j : Fin 3,
          spatialDeriv (fun y => heatOrbit a (y, z.2) i) j z.1 *
            spatialPartial (fun y => φ y i) j z = 0 := by
  obtain ⟨hφ, hφc, hφs⟩ := hφmem
  set Q := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) with hQdef
  have hQ : MeasurableSet Q := MeasurableSet.univ.prod measurableSet_Ioo
  have hai (i : Fin 3) : MemLp (fun y => a y i) 2 volume := memLp_pi_iff.1 ha.1 i
  let φi : Fin 3 → Vec3 × ℝ → ℝ := fun i y => φ y i
  have hφi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (φi i) := contDiff_pi.1 hφ i
  have hφic (i : Fin 3) : HasCompactSupport (φi i) := hφc.comp_left (g := fun v : Vec3 => v i) rfl
  have hφis (i : Fin 3) : tsupport (φi i) ⊆ tsupport φ :=
    tsupport_comp_subset (g := fun v : Vec3 => v i) rfl φ
  have hQpos : Q ⊆ {z : Vec3 × ℝ | 0 < z.2} := fun z hz => hz.2.1
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_snd_of_isCompact hφc.isCompact (hφs.trans hQpos)
  have hsupp (i : Fin 3) {z : Vec3 × ℝ} (hz : z ∈ tsupport (φi i)) : δ ≤ z.2 :=
    hδle z (hφis i hz)
  choose M hM0 hM using fun i => heatConv_heatConvGrad_bound hδ (hai i)
  obtain ⟨hmh, hmD⟩ := heatOrbit_grad_aestronglyMeasurable ha τ
  -- the pieces of the integrand
  let T : Fin 3 → Vec3 × ℝ → ℝ := fun i z => fderiv ℝ (φi i) z (0, 1)
  let S : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j z => fderiv ℝ (φi i) z (basisVec j, 0)
  let S2 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j z =>
    fderiv ℝ (fun q => fderiv ℝ (φi i) q (basisVec j, 0)) z (basisVec j, 0)
  let H : Fin 3 → Vec3 × ℝ → ℝ := fun i z => heatOrbit a z i
  let DH : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j z =>
    spatialDeriv (fun y => heatOrbit a (y, z.2) i) j z.1
  have hTcont (i : Fin 3) : Continuous (T i) :=
    ((hφi i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hScont (i j : Fin 3) : Continuous (S i j) :=
    ((hφi i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hS2smooth (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (S i j) :=
    contDiff_fderiv_apply_const (hφi i) _
  have hS2cont (i j : Fin 3) : Continuous (S2 i j) :=
    ((hS2smooth i j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hTcs (i : Fin 3) : HasCompactSupport (T i) := (hφic i).fderiv_apply (𝕜 := ℝ) _
  have hScs (i j : Fin 3) : HasCompactSupport (S i j) := (hφic i).fderiv_apply (𝕜 := ℝ) _
  have hS2cs (i j : Fin 3) : HasCompactSupport (S2 i j) :=
    ((hφic i).fderiv_apply (𝕜 := ℝ) _).fderiv_apply (𝕜 := ℝ) _
  have hHm (i : Fin 3) : AEStronglyMeasurable (H i) (volume.restrict Q) :=
    (continuous_apply i).comp_aestronglyMeasurable hmh
  have hDHm (i j : Fin 3) : AEStronglyMeasurable (DH i j) (volume.restrict Q) :=
    (continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hmD)
  have hHb (i : Fin 3) (z : Vec3 × ℝ) (hz : δ ≤ z.2) : |H i z| ≤ M i :=
    (hM i z.2 hz z.1).1
  have hDHb (i j : Fin 3) (z : Vec3 × ℝ) (hz : δ ≤ z.2) : |DH i j z| ≤ M i := by
    change |spatialDeriv (fun y => heatOrbit a (y, z.2) i) j z.1| ≤ M i
    rw [heatOrbit_spatialDeriv_eq ha.1 (lt_of_lt_of_le hδ hz) z.1 i j]
    exact (hM i z.2 hz z.1).2 j
  have hIQ (g : Vec3 × ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
      Integrable g (volume.restrict Q) :=
    (hg.integrable_of_hasCompactSupport hgc).restrict
  -- integrability of the individual products on the slab
  have hIT (i : Fin 3) : Integrable (fun z => H i z * T i z) (volume.restrict Q) :=
    integrable_mul_of_bound_on_support (hHm i) (hIQ _ (hTcont i) (hTcs i)) fun z hz =>
      hHb i z (hsupp i (mem_tsupport_of_fderiv_apply_ne_zero hz))
  have hIS (i j : Fin 3) : Integrable (fun z => DH i j z * S i j z) (volume.restrict Q) :=
    integrable_mul_of_bound_on_support (hDHm i j) (hIQ _ (hScont i j) (hScs i j)) fun z hz =>
      hDHb i j z (hsupp i (mem_tsupport_of_fderiv_apply_ne_zero hz))
  have hIS2 (i j : Fin 3) : Integrable (fun z => H i z * S2 i j z) (volume.restrict Q) :=
    integrable_mul_of_bound_on_support (hHm i) (hIQ _ (hS2cont i j) (hS2cs i j)) fun z hz =>
      hHb i z (hsupp i (mem_tsupport_of_second_fderiv_ne_zero hz))
  -- rewrite the integrand with directional derivatives
  let A : Vec3 × ℝ → ℝ := fun z =>
    -(∑ i : Fin 3, H i z * T i z) + ∑ i : Fin 3, ∑ j : Fin 3, DH i j z * S i j z
  let Bf : Vec3 × ℝ → ℝ := fun z => ∑ i : Fin 3, H i z * backwardHeatOp (φi i) z
  have hA : (fun z : ParabolicPoint =>
      (-(∑ i : Fin 3, heatOrbit a z i * timePartial (fun y => φ y i) z)) +
        ∑ i : Fin 3, ∑ j : Fin 3, spatialDeriv (fun y => heatOrbit a (y, z.2) i) j z.1 *
          spatialPartial (fun y => φ y i) j z) = A := by
    funext z
    have hT (i : Fin 3) : timePartial (fun y => φ y i) z = T i z :=
      timePartial_eq_fderiv_apply (hφi i) z.1 z.2
    have hS (i j : Fin 3) : spatialPartial (fun y => φ y i) j z = S i j z :=
      spatialPartial_eq_fderiv_apply (hφi i) j z.1 z.2
    simp only [hT, hS, A, H, DH]
  have hAI : Integrable A (volume.restrict Q) :=
    ((integrable_finsetSum _ fun i _ => hIT i).neg).add
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hIS i j)
  have hBpt (z : Vec3 × ℝ) : Bf z = ∑ i : Fin 3, (-(H i z * T i z) -
      ∑ j : Fin 3, H i z * S2 i j z) := by
    simp only [Bf, backwardHeatOp, mul_sub, mul_neg, Finset.mul_sum]
    rfl
  have hBI : Integrable Bf (volume.restrict Q) := by
    have h : Integrable (fun z => ∑ i : Fin 3, (-(H i z * T i z) -
        ∑ j : Fin 3, H i z * S2 i j z)) (volume.restrict Q) :=
      integrable_finsetSum _ fun i _ => (hIT i).neg.sub
        (integrable_finsetSum _ fun j _ => hIS2 i j)
    exact h.congr (Eventually.of_forall fun z => (hBpt z).symm)
  -- the slice identity from the weak gradient
  have hslice (t : ℝ) (ht : 0 < t) : ∫ x : Vec3, (A - Bf) (x, t) = 0 := by
    have hpt (x : Vec3) : (A - Bf) (x, t) = ∑ i : Fin 3, ∑ j : Fin 3,
        (DH i j (x, t) * S i j (x, t) + H i (x, t) * S2 i j (x, t)) := by
      simp only [Pi.sub_apply, A, hBpt, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_neg_distrib]
      ring
    have hterm (i j : Fin 3) :
        Integrable (fun x : Vec3 => DH i j (x, t) * S i j (x, t)) volume ∧
          Integrable (fun x : Vec3 => H i (x, t) * S2 i j (x, t)) volume ∧
          ∫ x : Vec3, (DH i j (x, t) * S i j (x, t) + H i (x, t) * S2 i j (x, t)) = 0 := by
      obtain ⟨Mt, -, hMt⟩ := heatConv_heatConvGrad_bound ht (hai i)
      have hsl (g : Vec3 × ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
          Integrable (fun x : Vec3 => g (x, t)) volume :=
        (hg.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
          (hasCompactSupport_time_slice hgc t)
      have hHd : Differentiable ℝ (fun x : Vec3 => H i (x, t)) := fun x =>
        (heatConv_hasFDerivAt_of_memLp (hai i) ht x).differentiableAt
      have h1 : Integrable (fun x : Vec3 => DH i j (x, t) * S i j (x, t)) volume := by
        refine (hsl _ (hScont i j) (hScs i j)).bdd_mul (c := Mt)
          (measurable_fderiv_apply_const ℝ (fun y => heatOrbit a (y, t) i)
            (basisVec j)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs]
        change |spatialDeriv (fun y => heatOrbit a (y, t) i) j x| ≤ Mt
        rw [heatOrbit_spatialDeriv_eq ha.1 ht x i j]
        exact (hMt t le_rfl x).2 j
      have h2 : Integrable (fun x : Vec3 => H i (x, t) * S2 i j (x, t)) volume := by
        refine (hsl _ (hS2cont i j) (hS2cs i j)).bdd_mul (c := Mt)
          hHd.continuous.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs]
        exact (hMt t le_rfl x).1
      refine ⟨h1, h2, ?_⟩
      have hθ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => S i j (x, t)) :=
        (hS2smooth i j).comp (contDiff_id.prodMk contDiff_const)
      have hw := heatOrbit_hasWeakGradientOn ha ht i j (fun x : Vec3 => S i j (x, t)) hθ
        (hasCompactSupport_time_slice (hScs i j) t) (subset_univ _)
      simp only [Measure.restrict_univ] at hw
      have hθd (x : Vec3) : fderiv ℝ (fun x : Vec3 => S i j (x, t)) x (basisVec j) =
          S2 i j (x, t) :=
        spatialPartial_eq_fderiv_apply (hS2smooth i j) j x t
      simp only [hθd] at hw
      rw [integral_add h1 h2]
      change (∫ x : Vec3, DH i j (x, t) * S i j (x, t)) +
        ∫ x : Vec3, heatOrbit a (x, t) i * S2 i j (x, t) = 0
      rw [hw]
      change (∫ x : Vec3, DH i j (x, t) * S i j (x, t)) -
        ∫ x : Vec3, DH i j (x, t) * S i j (x, t) = 0
      ring
    have hI (i j : Fin 3) : Integrable (fun x : Vec3 =>
        DH i j (x, t) * S i j (x, t) + H i (x, t) * S2 i j (x, t)) volume :=
      (hterm i j).1.add (hterm i j).2.1
    have hIs (i : Fin 3) : Integrable (fun x : Vec3 => ∑ j : Fin 3,
        (DH i j (x, t) * S i j (x, t) + H i (x, t) * S2 i j (x, t))) volume :=
      integrable_finsetSum _ fun j _ => hI i j
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_finsetSum (f := fun i (x : Vec3) => ∑ j : Fin 3,
        (DH i j (x, t) * S i j (x, t) + H i (x, t) * S2 i j (x, t))) _ fun i _ => hIs i]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finsetSum (f := fun j (x : Vec3) =>
        DH i j (x, t) * S i j (x, t) + H i (x, t) * S2 i j (x, t)) _ fun j _ => hI i j]
    exact Finset.sum_eq_zero fun j _ => (hterm i j).2.2
  have hdiff : ∫ z in Q, (A - Bf) z = 0 := by
    rw [integral_spaceTimeSet_univ_eq (hAI.sub hBI)]
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))
      fun t ht => hslice t ht.1]
    simp
  have hBzero : ∫ z in Q, Bf z = 0 := by
    have hLc (i : Fin 3) : Continuous (backwardHeatOp (φi i)) :=
      backwardHeatOp_continuous (hφi i)
    have hLcs (i : Fin 3) : HasCompactSupport (backwardHeatOp (φi i)) :=
      HasCompactSupport.intro (hφic i).isCompact fun z hz => backwardHeatOp_eq_zero_of_notMem hz
    have hIL (i : Fin 3) : Integrable (fun z => H i z * backwardHeatOp (φi i) z)
        (volume.restrict Q) :=
      integrable_mul_of_bound_on_support (hHm i) (hIQ _ (hLc i) (hLcs i)) fun z hz =>
        hHb i z (hsupp i (by
          by_contra hmem
          exact hz (backwardHeatOp_eq_zero_of_notMem hmem)))
    have hBsum : ∫ z in Q, Bf z = ∑ i : Fin 3, ∫ z in Q, H i z * backwardHeatOp (φi i) z :=
      integral_finsetSum _ fun i _ => hIL i
    rw [hBsum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_]
    · exact heatConv_backwardHeatOp_integral_eq_zero (hai i) (hφi i) (hφic i)
        ((hφis i).trans (hφs.trans hQpos))
    · have hnot : z ∉ tsupport (φi i) := fun hmem => hz (hφs (hφis i hmem))
      simp only [backwardHeatOp_eq_zero_of_notMem hnot, mul_zero]
  have hsub := integral_sub hAI hBI
  rw [hA]
  have h1 : (∫ z in Q, A z) - ∫ z in Q, Bf z = 0 := hsub.symm.trans hdiff
  linarith only [h1, hBzero]

end ESS

end
