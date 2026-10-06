/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSliceTest
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSpaceTimeHilbert
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSobolevBridge
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateGoodSlices
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateTestField
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevMollify

/-!
# The slice energy balance of a linear Stokes-type system

Let `v` solve `∂ₜv - Δv + div H + ∇q = 0` weakly on `ℝ³ × (c, d)`, tested against
smooth compactly supported vector fields, with `div v = 0` and all fields square
integrable. At almost every time the equation holds against every spatial test field;
approximating the slice `v(t) ∈ H¹` by smooth compactly supported fields shows that it
may be tested with `v(t)` itself, and the pressure drops out because `div v(t) = 0`.
This gives `∫ v · ∂ₜv = -∫ |∇v|² + ∫ H : ∇v` at almost every time
(`prop:lps-smoothing`).
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The slice identity for a linear family of tests whose data are indexed by a finite
type. -/
private theorem lps_ae_slice_test_eq_zero_fintype {a b : ℝ} {κ : Type*} [Fintype κ]
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    (A : κ → Vec3 × ℝ → ℝ)
    (hA : ∀ k, MemLp (A k) 2 (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)))
    (ι : T →ₗ[ℝ] (κ → Vec3 → ℝ))
    (hι : ∀ ψ k, MemLp (ι ψ k) 2 volume)
    (hzero : ∀ (ψ : T) (χ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      tsupport χ ⊆ Ioo a b →
      ∫ t in Ioo a b, χ t * ∫ x, ∑ k, A k (x, t) * ι ψ k x = 0) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ ψ : T, ∫ x, ∑ k, A k (x, t) * ι ψ k x = 0 := by
  classical
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let ι' : T →ₗ[ℝ] (Fin (Fintype.card κ) → Vec3 → ℝ) :=
    (LinearMap.funLeft ℝ (Vec3 → ℝ) e.symm).comp ι
  have hsum : ∀ (ψ : T) (t : ℝ),
      (fun x => ∑ k', A (e.symm k') (x, t) * ι' ψ k' x) =
        fun x => ∑ k, A k (x, t) * ι ψ k x := fun ψ t => funext fun x =>
    e.symm.sum_comp (fun k => A k (x, t) * ι ψ k x)
  have h := lps_ae_slice_test_eq_zero (fun k' => A (e.symm k')) (fun k' => hA _) ι'
    (fun ψ k' => hι ψ _) (by
      intro ψ χ h1 h2 h3
      have hz := hzero ψ χ h1 h2 h3
      simpa only [hsum] using hz)
  filter_upwards [h] with t ht ψ
  have hz := ht ψ
  simpa only [hsum] using hz

/-- Almost every time slice of a square-integrable function on the product slab is
square integrable. -/
private theorem lps_prod_slice_memLp_ae {c d : ℝ} {F : Vec3 × ℝ → ℝ}
    (hF : MemLp F 2 ((volume : Measure Vec3).prod (volume.restrict (Ioo c d)))) :
    ∀ᵐ t ∂(volume.restrict (Ioo c d)), MemLp (fun x => F (x, t)) 2 volume := by
  have hsq : Integrable (fun y => ‖F y‖ ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo c d))) :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF
  filter_upwards [hF.aestronglyMeasurable.prodMk_right, hsq.prod_left_ae] with t h1 h2
  exact (memLp_two_iff_integrable_sq_norm h1).2 h2

/-- Smooth compactly supported vector fields on `ℝ³`, as a real vector space. -/
@[expose] def lpsSmoothCompactFields : Submodule ℝ (Vec3 → Vec3) where
  carrier := {ψ | ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun a _ hx =>
    ⟨contDiff_const.smul hx.1, hx.2.mono (Function.support_const_smul_subset a _)⟩

theorem lpsSmoothCompactFields_component (ψ : lpsSmoothCompactFields) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (ψ : Vec3 → Vec3) x i) ∧
      HasCompactSupport (fun x => (ψ : Vec3 → Vec3) x i) :=
  ⟨contDiff_pi.1 ψ.2.1 i, ψ.2.2.comp_left (g := fun w : Vec3 => w i) rfl⟩

/-- The test data of a vector field: its components and their first partials. -/
@[expose] def lpsTestData :
    lpsSmoothCompactFields →ₗ[ℝ] (Fin 3 ⊕ (Fin 3 × Fin 3) → Vec3 → ℝ) where
  toFun ψ := Sum.elim (fun i x => (ψ : Vec3 → Vec3) x i)
    (fun ij => spatialDeriv (fun x => (ψ : Vec3 → Vec3) x ij.1) ij.2)
  map_add' ψ ψ' := by
    funext k
    cases k with
    | inl i => rfl
    | inr ij =>
      exact spatialDeriv_add_smooth (lpsSmoothCompactFields_component ψ ij.1).1
        (lpsSmoothCompactFields_component ψ' ij.1).1 ij.2
  map_smul' a ψ := by
    funext k
    cases k with
    | inl i => rfl
    | inr ij =>
      funext x
      have hd : DifferentiableAt ℝ (fun x => (ψ : Vec3 → Vec3) x ij.1) x :=
        ((lpsSmoothCompactFields_component ψ ij.1).1.differentiable (by simp)) x
      change (fderiv ℝ (fun x => a * (ψ : Vec3 → Vec3) x ij.1) x) (basisVec ij.2) =
        a * (fderiv ℝ (fun x => (ψ : Vec3 → Vec3) x ij.1) x) (basisVec ij.2)
      rw [fderiv_const_mul hd]
      rfl

private theorem lpsTestData_memLp (ψ : lpsSmoothCompactFields)
    (k : Fin 3 ⊕ (Fin 3 × Fin 3)) : MemLp (lpsTestData ψ k) 2 volume := by
  cases k with
  | inl i =>
    exact (lpsSmoothCompactFields_component ψ i).1.continuous.memLp_of_hasCompactSupport
      (lpsSmoothCompactFields_component ψ i).2
  | inr ij =>
    exact (contDiff_spatialDeriv_smooth (lpsSmoothCompactFields_component ψ ij.1).1
      ij.2).continuous.memLp_of_hasCompactSupport
      ((lpsSmoothCompactFields_component ψ ij.1).2.fderiv_apply ℝ (basisVec ij.2))

/-- The separated vector test field `χ(t) ψ(x)` on a whole-space slab. -/
private theorem lps_separated_smul_test_mem {c d : ℝ} {χ : ℝ → ℝ} {ψ : Vec3 → Vec3}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo c d)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    (fun z : Vec3 × ℝ => χ z.2 • ψ z.1) ∈
      spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo c d) := by
  have hsub : tsupport (fun z : Vec3 × ℝ => χ z.2 • ψ z.1) ⊆ tsupport ψ ×ˢ tsupport χ := by
    refine closure_minimal ?_ ((isClosed_tsupport ψ).prod (isClosed_tsupport χ))
    intro z hz
    have hz' : χ z.2 • ψ z.1 ≠ 0 := hz
    exact ⟨subset_tsupport _ (right_ne_zero_of_smul hz'),
      subset_tsupport _ (left_ne_zero_of_smul hz')⟩
  refine ⟨(hχ.comp contDiff_snd).smul (hψ.comp contDiff_fst), ?_, ?_⟩
  · exact IsCompact.of_isClosed_subset (hψc.prod hχc) (isClosed_tsupport _) hsub
  · intro z hz
    exact ⟨mem_univ _, hχs (hsub hz).2⟩

/-- `∑ᵢ ∑ⱼ δᵢⱼ p aᵢⱼ = p ∑ᵢ aᵢᵢ`. -/
private theorem lps_pressure_delta_sum (a : Fin 3 → Fin 3 → ℝ) (p : ℝ) :
    ∑ i, ∑ j, (if i = j then p else 0) * a i j = p * ∑ i, a i i := by
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]

/-- The integrand of the equation against a separated test field, regrouped by
test data. -/
private theorem lps_separated_integrand_eq (χ p : ℝ) (Dt w : Fin 3 → ℝ)
    (G H s : Fin 3 → Fin 3 → ℝ) :
    ∑ i, Dt i * (χ * w i) - ∑ i, ∑ j, H i j * (χ * s i j)
        + ∑ i, ∑ j, G i j * (χ * s i j) - p * ∑ i, χ * s i i =
      χ * (∑ i, Dt i * w i
        + ∑ i, ∑ j, (G i j - H i j - if i = j then p else 0) * s i j) := by
  have hδ : ∑ i, ∑ j, (G i j - H i j - if i = j then p else 0) * s i j =
      ∑ i, ∑ j, G i j * s i j - ∑ i, ∑ j, H i j * s i j - p * ∑ i, s i i := by
    simp only [sub_mul, Finset.sum_sub_distrib, lps_pressure_delta_sum]
  rw [hδ]
  simp only [Fin.sum_univ_three]
  ring

/-- The integrand tested with the field itself, for a divergence-free gradient. -/
private theorem lps_self_integrand_eq (p : ℝ) (Dt w : Fin 3 → ℝ) (G H : Fin 3 → Fin 3 → ℝ)
    (hdiv : ∑ i, G i i = 0) :
    ∑ i, Dt i * w i + ∑ i, ∑ j, (G i j - H i j - if i = j then p else 0) * G i j =
      ∑ i, w i * Dt i + ∑ i, ∑ j, G i j ^ 2 - ∑ i, ∑ j, H i j * G i j := by
  have hδ : ∑ i, ∑ j, (G i j - H i j - if i = j then p else 0) * G i j =
      ∑ i, ∑ j, G i j * G i j - ∑ i, ∑ j, H i j * G i j - p * ∑ i, G i i := by
    simp only [sub_mul, Finset.sum_sub_distrib, lps_pressure_delta_sum]
  rw [hδ, hdiv]
  simp only [Fin.sum_univ_three]
  ring

/-- At almost every time, a weak solution of `∂ₜv - Δv + div H + ∇q = 0` on
`ℝ³ × (c, d)` with `div v = 0` satisfies the slice energy balance
`∫ v · ∂ₜv = -∫ |∇v|² + ∫ H : ∇v` (`prop:lps-smoothing`). -/
theorem lps_linearStokes_slice_balance_ae {c d : ℝ}
    {v : ParabolicPoint → Vec3} {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtv : ParabolicPoint → Vec3}
    {H : ParabolicPoint → Fin 3 → Fin 3 → ℝ} {q : ParabolicPoint → ℝ}
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo c d) v Dv D2v Dtv)
    (hv : MemLp v 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hDv : MemLp Dv 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hD2v : MemLp D2v 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hDtv : MemLp Dtv 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hH : ∀ i j, MemLp (fun z => H z i j) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hq : MemLp q 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hdiv : ∀ᵐ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))),
      ∑ i, Dv z i i = 0)
    (heq : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo c d) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo c d),
        (∑ i, Dtv z i * φ z i
          - ∑ i, ∑ j, H z i j * spatialPartial (fun y => φ y i) j z
          + ∑ i, ∑ j, Dv z i j * spatialPartial (fun y => φ y i) j z
          - q z * ∑ i, spatialPartial (fun y => φ y i) i z) = 0) :
    ∀ᵐ t ∂(volume.restrict (Ioo c d)),
      2 * ∫ x : Vec3, ∑ i, v (x, t) i * Dtv (x, t) i =
        -2 * (∫ x : Vec3, ∑ i, ∑ j, (Dv (x, t) i j) ^ 2)
          + 2 * (∫ x : Vec3, ∑ i, ∑ j, H (x, t) i j * Dv (x, t) i j) := by
  classical
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo c d))
    with hν
  have hνslab : (volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo c d) = ν :=
    lps_measure_slab_eq_prod c d
  -- the coefficient fields of the equation, in product coordinates
  let A : Fin 3 ⊕ (Fin 3 × Fin 3) → Vec3 × ℝ → ℝ := Sum.elim
    (fun i y => Dtv (parabolicHomeomorph.symm y) i)
    (fun ij y => Dv (parabolicHomeomorph.symm y) ij.1 ij.2
      - H (parabolicHomeomorph.symm y) ij.1 ij.2
      - (if ij.1 = ij.2 then q (parabolicHomeomorph.symm y) else 0))
  have hAν : ∀ k, MemLp (A k) 2 ν := by
    intro k
    cases k with
    | inl i => exact (memLp_pi_iff.1 (lps_memLp_slab_to_prod hDtv)) i
    | inr ij =>
      have h1 : MemLp (fun y : Vec3 × ℝ => Dv (parabolicHomeomorph.symm y) ij.1 ij.2) 2 ν :=
        (memLp_pi_iff.1 ((memLp_pi_iff.1 (lps_memLp_slab_to_prod hDv)) ij.1)) ij.2
      have h2 : MemLp (fun y : Vec3 × ℝ => H (parabolicHomeomorph.symm y) ij.1 ij.2) 2 ν :=
        lps_memLp_slab_to_prod (hH ij.1 ij.2)
      have h3 : MemLp (fun y : Vec3 × ℝ =>
          if ij.1 = ij.2 then q (parabolicHomeomorph.symm y) else 0) 2 ν := by
        by_cases hij : ij.1 = ij.2
        · have hfun : (fun y : Vec3 × ℝ =>
              if ij.1 = ij.2 then q (parabolicHomeomorph.symm y) else 0) =
              fun y => q (parabolicHomeomorph.symm y) := funext fun y => by simp [hij]
          rw [hfun]
          exact lps_memLp_slab_to_prod hq
        · have hfun : (fun y : Vec3 × ℝ =>
              if ij.1 = ij.2 then q (parabolicHomeomorph.symm y) else 0) =
              fun _ => 0 := funext fun y => by simp [hij]
          rw [hfun]
          exact MemLp.zero
      exact (h1.sub h2).sub h3
  have hA : ∀ k, MemLp (A k) 2 (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo c d)) := by
    rw [hνslab]
    exact hAν
  -- the equation against separated tests
  have hzero : ∀ (ψ : lpsSmoothCompactFields) (χ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ →
      HasCompactSupport χ → tsupport χ ⊆ Ioo c d →
      ∫ t in Ioo c d, χ t * ∫ x, ∑ k, A k (x, t) * lpsTestData ψ k x = 0 := by
    intro ψ χ hχ hχc hχs
    let Ψ : Vec3 → Vec3 := ψ
    let φ : ParabolicPoint → Vec3 := fun z => χ z.2 • Ψ z.1
    have hφ : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo c d) :=
      lps_separated_smul_test_mem hχ hχc hχs ψ.2.1 ψ.2.2
    have hsp : ∀ (i j : Fin 3) (z : ParabolicPoint),
        spatialPartial (fun y => φ y i) j z = χ z.2 * spatialDeriv (fun x => Ψ x i) j z.1 :=
      fun i j z => lps_separated_spatialPartial (lpsSmoothCompactFields_component ψ i).1 j z
    have hval : ∀ (i : Fin 3) (z : ParabolicPoint), φ z i = χ z.2 * Ψ z.1 i := fun _ _ => rfl
    have hE := heq φ hφ
    simp only [hsp] at hE
    simp only [hval] at hE
    rw [lps_setIntegral_slab_to_prod] at hE
    have hJ : Integrable (fun y : Vec3 × ℝ => χ y.2 * ∑ k, A k y * lpsTestData ψ k y.1) ν := by
      obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hχc
      exact (integrable_finsetSum _ fun k _ =>
        lps_integrable_slice_pairing (hA k) (lpsTestData_memLp ψ k)).bdd_mul
          (hχ.continuous.comp continuous_snd).aestronglyMeasurable
          (ae_of_all _ fun y => hC y.2)
    have key : ∫ y, χ y.2 * ∑ k, A k y * lpsTestData ψ k y.1 ∂ν = 0 := by
      rw [← hE]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [A, lpsTestData, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_sum_type,
        Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type]
      exact (lps_separated_integrand_eq (χ y.2) (q (parabolicHomeomorph.symm y))
        (fun i => Dtv (parabolicHomeomorph.symm y) i) (fun i => Ψ y.1 i)
        (fun i j => Dv (parabolicHomeomorph.symm y) i j)
        (fun i j => H (parabolicHomeomorph.symm y) i j)
        (fun i j => spatialDeriv (fun x => Ψ x i) j y.1)).symm
    rw [integral_prod_symm _ hJ] at key
    dsimp only at key
    simpa only [integral_const_mul] using key
  have hslice := lps_ae_slice_test_eq_zero_fintype A hA lpsTestData lpsTestData_memLp hzero
  -- almost every slice is regular
  have hfam := LPS.lps_spatial_sobolev_slices_ae_of_weak_derivs hderiv hv hDv hD2v
  have hAt : ∀ᵐ t ∂(volume.restrict (Ioo c d)), ∀ k, MemLp (fun x => A k (x, t)) 2 volume := by
    rw [ae_all_iff]
    exact fun k => lps_prod_slice_memLp_ae (hAν k)
  have hvt := lps_slice_memLp_two_ae_slab hv
  have hDvt := lps_slice_memLp_two_ae_slab hDv
  have hDtvt := lps_slice_memLp_two_ae_slab hDtv
  have hHt : ∀ᵐ t ∂(volume.restrict (Ioo c d)), ∀ i j,
      MemLp (fun x : Vec3 => H (x, t) i j) 2 volume := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    exact fun j => lps_slice_memLp_two_ae_slab (hH i j)
  have hdivt : ∀ᵐ t ∂(volume.restrict (Ioo c d)), ∀ᵐ x ∂(volume : Measure Vec3),
      ∑ i, Dv (x, t) i i = 0 := by
    have hSmeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d)) :=
      MeasurableSet.univ.prod measurableSet_Ioo
    have hpre : parabolicHomeomorph.symm ⁻¹' spaceTimeSet (Set.univ : Set Vec3) (Ioo c d) =
        (Set.univ : Set Vec3) ×ˢ Ioo c d := by
      ext z
      rfl
    have hmp := CKN.parabolicHomeomorphSymm_measurePreserving.restrict_preimage hSmeas
    rw [hpre, hνslab] at hmp
    have h1 : ∀ᵐ y ∂ν, ∑ i, Dv (parabolicHomeomorph.symm y) i i = 0 :=
      hmp.quasiMeasurePreserving.ae hdiv
    have h2 := (Measure.measurePreserving_swap (μ := volume.restrict (Ioo c d))
      (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae h1
    exact Measure.ae_ae_of_ae_prod h2
  filter_upwards [hslice, hfam, hAt, hvt, hDvt, hDtvt, hHt, hdivt] with t hΛ hF hA_t hv_t hDv_t
    hDtv_t hH_t hdiv_t
  -- smooth compactly supported approximations of the slice
  obtain ⟨g, hgs, hgc, hgconv, -⟩ := sobolevFamily_smooth_approx (ι := Fin 3) (m := 2)
    (f := fun i x => v (x, t) i)
    (D := fun α i x => LPS.lps_h1_spatial_family v Dv D2v i α (x, t)) hF
  have hcs (n : ℕ) : HasCompactSupport (fun x : Vec3 => (fun i => g n i x : Vec3)) := by
    refine IsCompact.of_isClosed_subset (isCompact_iUnion fun i => hgc n i)
      (isClosed_tsupport _) ?_
    refine closure_minimal ?_ (isClosed_iUnion_of_finite fun i => isClosed_tsupport _)
    intro x hx
    by_contra hno
    simp only [mem_iUnion, not_exists] at hno
    apply hx
    funext i
    exact image_eq_zero_of_notMem_tsupport (hno i)
  let ψ : ℕ → lpsSmoothCompactFields := fun n =>
    ⟨fun x i => g n i x, contDiff_pi.2 fun i => hgs n i, hcs n⟩
  let fk : Fin 3 ⊕ (Fin 3 × Fin 3) → Vec3 → ℝ :=
    Sum.elim (fun i x => v (x, t) i) (fun ij x => Dv (x, t) ij.1 ij.2)
  have hfk : ∀ k, MemLp (fk k) 2 volume := by
    intro k
    cases k with
    | inl i => exact (memLp_pi_iff.1 hv_t) i
    | inr ij => exact (memLp_pi_iff.1 ((memLp_pi_iff.1 hDv_t) ij.1)) ij.2
  have hconv : ∀ k, Tendsto (fun n => eLpNorm (lpsTestData (ψ n) k - fk k) 2 volume)
      atTop (𝓝 0) := by
    intro k
    cases k with
    | inl i => exact hgconv i [] (by simp)
    | inr ij => exact hgconv ij.1 [ij.2] (by simp)
  have hΛn : ∀ n, ∑ k, ∫ x, A k (x, t) * lpsTestData (ψ n) k x = 0 := by
    intro n
    have hint : ∀ k ∈ Finset.univ, Integrable (fun x => A k (x, t) * lpsTestData (ψ n) k x)
        volume := fun k _ => (hA_t k).integrable_mul (lpsTestData_memLp (ψ n) k)
    rw [← integral_finsetSum _ hint]
    exact hΛ (ψ n)
  have hlim : Tendsto (fun n => ∑ k, ∫ x, A k (x, t) * lpsTestData (ψ n) k x) atTop
      (𝓝 (∑ k, ∫ x, A k (x, t) * fk k x)) := by
    refine tendsto_finsetSum _ fun k _ => ?_
    have h := lps_scalar_lp_pairing_tendsto_of_strong
      (fun n => lpsTestData_memLp (ψ n) k) (hfk k) (hA_t k) (hconv k)
    simpa only [mul_comm] using h
  have hzero_t : ∑ k, ∫ x, A k (x, t) * fk k x = 0 := by
    refine tendsto_nhds_unique hlim ?_
    simp only [hΛn]
    exact tendsto_const_nhds
  have hintf : ∀ k ∈ Finset.univ, Integrable (fun x => A k (x, t) * fk k x) volume :=
    fun k _ => (hA_t k).integrable_mul (hfk k)
  rw [← integral_finsetSum _ hintf] at hzero_t
  -- the pressure drops out and the slice balance follows
  have hvi (i : Fin 3) : MemLp (fun x : Vec3 => v (x, t) i) 2 volume := (memLp_pi_iff.1 hv_t) i
  have hDti (i : Fin 3) : MemLp (fun x : Vec3 => Dtv (x, t) i) 2 volume :=
    (memLp_pi_iff.1 hDtv_t) i
  have hDij (i j : Fin 3) : MemLp (fun x : Vec3 => Dv (x, t) i j) 2 volume :=
    (memLp_pi_iff.1 ((memLp_pi_iff.1 hDv_t) i)) j
  have hX : Integrable (fun x : Vec3 => ∑ i, v (x, t) i * Dtv (x, t) i) volume :=
    integrable_finsetSum _ fun i _ => (hvi i).integrable_mul (hDti i)
  have hY : Integrable (fun x : Vec3 => ∑ i, ∑ j, (Dv (x, t) i j) ^ 2) volume :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hDij i j).integrable_sq
  have hZ : Integrable (fun x : Vec3 => ∑ i, ∑ j, H (x, t) i j * Dv (x, t) i j) volume :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hH_t i j).integrable_mul (hDij i j)
  have hsum : ∫ x : Vec3, (∑ i, v (x, t) i * Dtv (x, t) i + ∑ i, ∑ j, (Dv (x, t) i j) ^ 2
      - ∑ i, ∑ j, H (x, t) i j * Dv (x, t) i j) = 0 := by
    rw [← hzero_t]
    refine integral_congr_ae ?_
    filter_upwards [hdiv_t] with x hx
    simp only [A, fk, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
      parabolicHomeomorph_symm_apply]
    exact (lps_self_integrand_eq (q (x, t)) (fun i => Dtv (x, t) i) (fun i => v (x, t) i)
      (fun i j => Dv (x, t) i j) (fun i j => H (x, t) i j) hx).symm
  have hXY : Integrable (fun x : Vec3 => ∑ i, v (x, t) i * Dtv (x, t) i
      + ∑ i, ∑ j, (Dv (x, t) i j) ^ 2) volume := hX.add hY
  rw [integral_sub hXY hZ, integral_add hX hY] at hsum
  linarith only [hsum]

end ESS
