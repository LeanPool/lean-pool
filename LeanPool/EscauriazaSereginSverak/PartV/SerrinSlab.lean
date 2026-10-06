/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakSolution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.WeakContL3Support
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.UniformCutoffFamilySeparated

/-!
# Time-slab identities for a fixed spatial test

For a Leray–Hopf solution whose momentum identity holds with a pressure, the
pairing of the specified time slices with a fixed smooth compactly supported
spatial field evolves by the integrated flux. This is the pairing formula used
for the cross-testing identity in `lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The momentum flux density of `(u, Du, p)` against a fixed spatial field
`ψ`: convection, diffusion and pressure terms. -/
@[expose] def serrinFlux (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (ψ : Vec3 → Vec3) (z : ParabolicPoint) : ℝ :=
  (∑ i : Fin 3, ∑ j : Fin 3,
      u z i * u z j * spatialDeriv (fun y => ψ y i) j z.1)
    - (∑ i : Fin 3, ∑ j : Fin 3,
      Du z i j * spatialDeriv (fun y => ψ y i) j z.1)
    + p z * ∑ i : Fin 3, spatialDeriv (fun y => ψ y i) i z.1

/-- The pairing density of a velocity with a fixed spatial field. -/
@[expose] def serrinPairing (u : ParabolicPoint → Vec3) (ψ : Vec3 → Vec3)
    (z : ParabolicPoint) : ℝ :=
  ∑ i : Fin 3, u z i * ψ z.1 i

/-- A spatial derivative vanishes outside the topological support. -/
theorem serrin_spatialDeriv_eq_zero_of_not_mem_tsupport {f : Vec3 → ℝ}
    {x : Vec3} (hx : x ∉ tsupport f) (j : Fin 3) :
    spatialDeriv f j x = 0 := by
  have hderiv : fderiv ℝ f x = 0 := by
    by_contra hne
    exact hx (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
  simp [spatialDeriv, hderiv]

private theorem tsupport_component_subset {ψ : Vec3 → Vec3} (i : Fin 3) :
    tsupport (fun y => ψ y i) ⊆ tsupport ψ := by
  apply closure_mono
  intro x hx hzero
  apply hx
  simp [hzero]

/-- Outside the support of the spatial field, the flux density vanishes. -/
theorem serrinFlux_eq_zero_of_not_mem
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {ψ : Vec3 → Vec3} {z : ParabolicPoint}
    (hz : z.1 ∉ tsupport ψ) :
    serrinFlux u Du p ψ z = 0 := by
  have hzero (i j : Fin 3) : spatialDeriv (fun y => ψ y i) j z.1 = 0 :=
    serrin_spatialDeriv_eq_zero_of_not_mem_tsupport
      (fun h => hz (tsupport_component_subset i h)) j
  simp [serrinFlux, hzero]

private theorem serrinPairing_eq_zero_of_not_mem
    {u : ParabolicPoint → Vec3} {ψ : Vec3 → Vec3} {z : ParabolicPoint}
    (hz : z.1 ∉ tsupport ψ) :
    serrinPairing u ψ z = 0 := by
  have hψ : ψ z.1 = 0 := image_eq_zero_of_notMem_tsupport hz
  simp [serrinPairing, hψ]

private theorem continuous_spatialDeriv_of_smooth {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 3) :
    Continuous (spatialDeriv f j) := by
  have hcont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by simp)
  exact hcont.clm_apply continuous_const

private theorem bounded_spatialDeriv_of_smooth {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (j : Fin 3) :
    ∃ C : ℝ, ∀ x, ‖spatialDeriv f j x‖ ≤ C := by
  have hcompact : HasCompactSupport (spatialDeriv f j) := by
    apply HasCompactSupport.of_support_subset_isCompact hfc.isCompact
    intro x hx
    by_contra hnot
    exact hx (serrin_spatialDeriv_eq_zero_of_not_mem_tsupport hnot j)
  exact hcompact.exists_bound_of_continuous
    (continuous_spatialDeriv_of_smooth hf j)

/-- The separated test `ψ(x) η(t)` in the momentum identity with pressure. -/
theorem serrin_momentum_pressure_separated
    {T : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hmom : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0)
    {ψ : Vec3 → Vec3} (hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcompact : HasCompactSupport ψ)
    {η : ℝ → ℝ} (hη : IsIntervalTest (Ioo 0 T) η) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      -(serrinPairing u ψ z * deriv η z.2) - serrinFlux u Du p ψ z * η z.2 = 0 := by
  rcases hη with ⟨hηsmooth, hηcompact, hηsupport⟩
  let φ : Vec3 × ℝ → Vec3 := fun z i => ψ z.1 i * η z.2
  let K : Set (Vec3 × ℝ) := tsupport ψ ×ˢ tsupport η
  have hKcompact : IsCompact K := hψcompact.isCompact.prod hηcompact.isCompact
  have hKclosed : IsClosed K := (isClosed_tsupport ψ).prod (isClosed_tsupport η)
  have hsupport : Function.support φ ⊆ K := by
    intro z hz
    simp only [K, Set.mem_prod]
    constructor
    · by_contra hx
      have hψzero : ψ z.1 = 0 := image_eq_zero_of_notMem_tsupport hx
      apply hz
      funext i
      simp [φ, hψzero]
    · by_contra ht
      have hηzero : η z.2 = 0 := image_eq_zero_of_notMem_tsupport ht
      apply hz
      funext i
      simp [φ, hηzero]
  have hφcompact : HasCompactSupport φ :=
    IsCompact.of_isClosed_subset hKcompact (isClosed_tsupport φ)
      (closure_minimal hsupport hKclosed)
  have hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ := by
    apply contDiff_pi.mpr
    intro i
    exact ((contDiff_pi.mp hψsmooth i).comp contDiff_fst).mul
      (hηsmooth.comp contDiff_snd)
  have hφsupport : tsupport φ ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
    intro z hz
    rcases closure_minimal hsupport hKclosed hz with ⟨_, hzt⟩
    exact ⟨Set.mem_univ _, hηsupport hzt⟩
  have hφtest : φ ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Ioo 0 T) := ⟨hφsmooth, hφcompact, hφsupport⟩
  have hψi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => ψ x i) :=
    contDiff_pi.mp hψsmooth i
  have hspace (z : ParabolicPoint) (i j : Fin 3) :
      spatialPartial (fun y => φ y i) j z =
        spatialDeriv (fun x => ψ x i) j z.1 * η z.2 := by
    exact CKN.Core.Endgame.spatialPartial_separatedProduct η (hψi i) j
      (parabolicHomeomorph z)
  have htime (z : ParabolicPoint) (i : Fin 3) :
      timePartial (fun y => φ y i) z = ψ z.1 i * deriv η z.2 := by
    exact CKN.Core.Endgame.timePartial_separatedProduct
      (fun x => ψ x i) hηsmooth (parabolicHomeomorph z)
  have hidentity := hmom φ hφtest
  have hpoint (z : ParabolicPoint) :
      ((-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) =
        -(serrinPairing u ψ z * deriv η z.2) - serrinFlux u Du p ψ z * η z.2 := by
    simp only [htime, hspace, serrinPairing, serrinFlux, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, sub_zero, Fin.sum_univ_three]
    ring
  simpa only [hpoint] using hidentity

/-- The velocity of a finite-energy weak solution is square integrable on the
space-time slab. -/
theorem serrinWeak_velocity_memLp_two
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du p) :
    MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  have hLT : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun z => le_self_add) hU.energy
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hU.meas_u]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hLT.ne

/-- The weak gradient of a finite-energy weak solution is square integrable on
the slab. -/
theorem serrinWeak_gradient_memLp_two
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du p) :
    MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  have hLT : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun z => le_add_self) hU.energy
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hU.meas_Du]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hLT.ne

/-- The velocity tensor of a finite-energy weak solution is integrable on the slab. -/
theorem serrinWeak_tensor_memLp_one
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du p) (i j : Fin 3) :
    MemLp (fun z => u z i * u z j) 1
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  have hu2 := serrinWeak_velocity_memLp_two hU
  have h : MemLp ((fun z : ParabolicPoint => u z i) * fun z => u z j) 1
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    MemLp.mul (p := 2) (q := 2) (hu2.eval i) (hu2.eval j)
  exact h

/-- A slab field in `L^q` with `q ≥ 1` is integrable on a compact spatial set times the time interval. -/
theorem serrin_integrable_restrict_of_memLp
    {T : ℝ} {K : Set Vec3} (hK : IsCompact K) {f : ParabolicPoint → ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q)
    (hf : MemLp f q (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    Integrable (fun z : Vec3 × ℝ => f z)
      ((volume.restrict K).prod (volume.restrict (Ioo 0 T))) := by
  have hmeas : (volume.restrict K).prod (volume.restrict (Ioo 0 T)) =
      (volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ Ioo 0 T) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
  rw [hmeas]
  have : IsFiniteMeasure ((volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ Ioo 0 T)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top hK.measure_lt_top (by simp)
  have hsub : K ×ˢ Ioo 0 T ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
    intro z hz
    exact ⟨Set.mem_univ _, hz.2⟩
  have hf' : MemLp (fun z : Vec3 × ℝ => f z) q
      ((volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ Ioo 0 T)) :=
    hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  exact hf'.integrable hq

/-- The pairing of the specified time slices of a finite-energy weak solution with a
fixed smooth compactly supported spatial field is the initial pairing plus the
time integral of the momentum flux, at every time of the closed interval. -/
theorem serrin_slab_identity
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hU : IsSerrinWeakSolution T a u Du p)
    {ψ : Vec3 → Vec3} (hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcompact : HasCompactSupport ψ) :
    IntegrableOn (fun τ => ∫ x : Vec3, serrinFlux u Du p ψ (x, τ)) (Ioo 0 T) ∧
    ∀ t ∈ Icc 0 T,
      (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * ψ x i) =
        (∫ x : Vec3, ∑ i : Fin 3, u (x, 0) i * ψ x i) +
          ∫ τ in (0 : ℝ)..t, ∫ x : Vec3, serrinFlux u Du p ψ (x, τ) := by
  have hT : 0 < T := hU.pos
  have hp := hU.pressure
  have hmom := hU.momentum
  let K : Set Vec3 := tsupport ψ
  have hKc : IsCompact K := hψcompact.isCompact
  have hKm : MeasurableSet K := (isClosed_tsupport ψ).measurableSet
  let μx : Measure Vec3 := volume.restrict K
  let μt : Measure ℝ := volume.restrict (Ioo 0 T)
  have hu2 := serrinWeak_velocity_memLp_two hU
  have hDu2 := serrinWeak_gradient_memLp_two hU
  have huu := serrinWeak_tensor_memLp_one hU
  have hq53 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (5 / 3 : ℝ) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hψi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => ψ x i) :=
    contDiff_pi.mp hψsmooth i
  have hψic (i : Fin 3) : HasCompactSupport (fun x : Vec3 => ψ x i) :=
    HasCompactSupport.of_support_subset_isCompact hKc
      ((subset_tsupport _).trans (tsupport_component_subset i))
  -- bounds on the spatial field and its derivatives
  have hψbd (i : Fin 3) : ∃ C : ℝ, ∀ x, ‖ψ x i‖ ≤ C :=
    (hψic i).exists_bound_of_continuous (hψi i).continuous
  have hdbd (i j : Fin 3) : ∃ C : ℝ, ∀ x, ‖spatialDeriv (fun y => ψ y i) j x‖ ≤ C :=
    bounded_spatialDeriv_of_smooth (hψi i) (hψic i) j
  -- integrability of the pairing and flux densities on `K × (0,T)`
  have hFint : Integrable (fun z : Vec3 × ℝ => serrinPairing u ψ z) (μx.prod μt) := by
    unfold serrinPairing
    refine integrable_finsetSum _ fun i _ => ?_
    obtain ⟨C, hC⟩ := hψbd i
    have hui : MemLp (fun z : ParabolicPoint => u z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := hu2.eval i
    exact (serrin_integrable_restrict_of_memLp hKc (by norm_num) hui).mul_bdd
      (((hψi i).continuous.comp continuous_fst).aestronglyMeasurable)
      (Eventually.of_forall fun z => hC z.1)
  have hGint : Integrable (fun z : Vec3 × ℝ => serrinFlux u Du p ψ z) (μx.prod μt) := by
    unfold serrinFlux
    refine ((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_).sub
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_)).add ?_
    · obtain ⟨C, hC⟩ := hdbd i j
      exact (serrin_integrable_restrict_of_memLp hKc le_rfl (huu i j)).mul_bdd
        (((continuous_spatialDeriv_of_smooth (hψi i) j).comp
          continuous_fst).aestronglyMeasurable)
        (Eventually.of_forall fun z => hC z.1)
    · obtain ⟨C, hC⟩ := hdbd i j
      have hDij : MemLp (fun z : ParabolicPoint => Du z i j) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
        (hDu2.eval i).eval j
      exact (serrin_integrable_restrict_of_memLp hKc (by norm_num) hDij).mul_bdd
        (((continuous_spatialDeriv_of_smooth (hψi i) j).comp
          continuous_fst).aestronglyMeasurable)
        (Eventually.of_forall fun z => hC z.1)
    · have hdiv : ∃ C : ℝ, ∀ x,
          ‖∑ i : Fin 3, spatialDeriv (fun y => ψ y i) i x‖ ≤ C := by
        choose C hC using fun i : Fin 3 => hdbd i i
        refine ⟨∑ i : Fin 3, C i, fun x => ?_⟩
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hC i x)
      obtain ⟨C, hC⟩ := hdiv
      exact (serrin_integrable_restrict_of_memLp hKc hq53 hp).mul_bdd
        ((continuous_finsetSum _ fun i _ =>
          continuous_spatialDeriv_of_smooth (hψi i) i).comp
            continuous_fst).aestronglyMeasurable
        (Eventually.of_forall fun z => hC z.1)
  -- the separated weak identity on the product measure
  have hweak : ∀ η : ℝ → ℝ, IsIntervalTest (Ioo 0 T) η →
      (∫ z, -(serrinPairing u ψ z * deriv η z.2) - serrinFlux u Du p ψ z * η z.2
        ∂(μx.prod μt)) = 0 := by
    intro η hη
    have h := serrin_momentum_pressure_separated hmom hψsmooth hψcompact hη
    rw [setIntegral_parabolic_to_product] at h
    have hmeas : μx.prod μt =
        (volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ Ioo 0 T) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
    rw [hmeas]
    have hsub : K ×ˢ Ioo 0 T ⊆ (Set.univ : Set Vec3) ×ˢ Ioo 0 T := by
      intro z hz
      exact ⟨Set.mem_univ _, hz.2⟩
    have hzero : ∀ q ∈ ((Set.univ : Set Vec3) ×ˢ Ioo 0 T) \ (K ×ˢ Ioo 0 T),
        (-(serrinPairing u ψ (parabolicHomeomorph.symm q) *
            deriv η (parabolicHomeomorph.symm q).2) -
          serrinFlux u Du p ψ (parabolicHomeomorph.symm q) *
            η (parabolicHomeomorph.symm q).2) = 0 := by
      intro q hq
      have hq1 : (parabolicHomeomorph.symm q).1 ∉ tsupport ψ :=
        fun hmem => hq.2 ⟨hmem, hq.1.2⟩
      rw [serrinPairing_eq_zero_of_not_mem hq1, serrinFlux_eq_zero_of_not_mem hq1]
      ring
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (MeasurableSet.univ.prod measurableSet_Ioo) hsub hzero] at h
    exact h
  obtain ⟨hfLoc, hgInt, hderiv⟩ :=
    weakContL3_productWeakDeriv (a := 0) (b := T) μx hFint hGint hweak
  -- rewrite the restricted spatial integrals as whole-space integrals
  have hFfull (t : ℝ) : (∫ x, serrinPairing u ψ (x, t) ∂μx) =
      ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * ψ x i := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rfl
    · intro x hx
      exact serrinPairing_eq_zero_of_not_mem (z := (x, t)) hx
  have hGfull (t : ℝ) : (∫ x, serrinFlux u Du p ψ (x, t) ∂μx) =
      ∫ x : Vec3, serrinFlux u Du p ψ (x, t) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    exact serrinFlux_eq_zero_of_not_mem (z := (x, t)) hx
  let g : ℝ → ℝ := fun τ => ∫ x : Vec3, serrinFlux u Du p ψ (x, τ)
  have hgOn : IntegrableOn g (Ioo 0 T) := by
    simpa only [hGfull] using hgInt
  refine ⟨hgOn, ?_⟩
  let P : ℝ → ℝ := fun t => ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * ψ x i
  have hderiv' : HasWeakDerivOn (Ioo 0 T) P g := by
    simpa only [hFfull, hGfull] using hderiv
  have hPloc : LocallyIntegrableOn P (Ioo 0 T) volume := by
    simpa only [hFfull] using hfLoc
  let gFull : ℝ → ℝ := (Ioo 0 T).indicator g
  have hgFullInt : Integrable gFull volume :=
    hgOn.integrable_indicator measurableSet_Ioo
  have hderivFull : HasWeakDerivOn (Ioo 0 T) P gFull := by
    intro θ hθ
    have hIntEq : (∫ t in Ioo 0 T, gFull t * θ t) = ∫ t in Ioo 0 T, g t * θ t := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      simp [gFull, ht]
    rw [hIntEq]
    exact hderiv' θ hθ
  have hmid : T / 2 ∈ Ioo 0 T := ⟨by linarith only [hT], by linarith only [hT]⟩
  obtain ⟨C, hC⟩ := exists_ae_eq_const_add_intervalIntegral_of_weakDeriv hT hmid hPloc
    (hgFullInt.locallyIntegrable.locallyIntegrableOn (Ioo 0 T)) hderivFull
  let Φ : ℝ → ℝ := fun t => C + ∫ r in (T / 2)..t, gFull r
  have hΦcont : Continuous Φ :=
    continuous_const.add (hgFullInt.continuous_primitive (T / 2))
  have hPcont : ContinuousOn P (Icc 0 T) := hU.weak_cont ψ hψsmooth hψcompact
  have hAE : P =ᵐ[volume.restrict (Ioo 0 T)] Φ := by
    filter_upwards [ae_restrict_of_ae hC, ae_restrict_mem measurableSet_Ioo]
      with t ht htI
    exact ht htI
  have hEqOpen := Measure.eqOn_open_of_ae_eq hAE isOpen_Ioo
    (hPcont.mono Ioo_subset_Icc_self) hΦcont.continuousOn
  have hEq : EqOn P Φ (Icc 0 T) := by
    apply Set.EqOn.of_subset_closure hEqOpen hPcont hΦcont.continuousOn
      Ioo_subset_Icc_self
    rw [closure_Ioo hT.ne]
  intro t ht
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hPt := hEq ht
  have hP0 := hEq h0
  have hint (s : ℝ) : IntervalIntegrable gFull volume (T / 2) s :=
    hgFullInt.intervalIntegrable
  have hsplit : (∫ r in (T / 2)..t, gFull r) - ∫ r in (T / 2)..(0 : ℝ), gFull r =
      ∫ r in (0 : ℝ)..t, gFull r :=
    intervalIntegral.integral_interval_sub_left (hint t) (hint 0)
  have hcongr : (∫ r in (0 : ℝ)..t, gFull r) = ∫ r in (0 : ℝ)..t, g r := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume T] with r hrT hr
    rw [uIoc_of_le ht.1] at hr
    have hrI : r ∈ Ioo 0 T := ⟨hr.1, lt_of_le_of_ne (hr.2.trans ht.2) hrT⟩
    simp [gFull, hrI]
  change P t = P 0 + ∫ τ in (0 : ℝ)..t, g τ
  rw [hPt, hP0, ← hcongr, ← hsplit]
  simp only [Φ]
  ring

end ESS
