/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateStrongFormAE
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingShiftEquation
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSliceTest

/-!
# The pressure equation on almost every time slice

`prop:lps-smoothing`: let `u` be a strong solution with square-integrable space-time weak
derivatives `∇u`, `∇²u`, `∂ₜu` and pressure `p`. Testing the equation against separated fields `χ(t) ψ(x)`
shows that for almost every time, and for every smooth compactly supported spatial field `ψ`,
`∫ (∂ₜu - Δu + (u·∇)u)(t) · ψ = ∫ p(t) div ψ`.
The nonlinear term is moved onto `(u·∇)u` slice by slice, where `u(t) ∈ H²` is solenoidal.
Hence at almost every time the pressure slice `p(t)` has the square-integrable weak gradient
`-(∂ₜu - Δu + (u·∇)u)(t)`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Smooth compactly supported scalar functions on `ℝ³`, as a real vector space
(`prop:lps-smoothing`). -/
@[expose] def lpsScalarTests : Submodule ℝ (Vec3 → ℝ) where
  carrier := {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun a _ hx =>
    ⟨contDiff_const.smul hx.1, hx.2.mono (Function.support_const_smul_subset a _)⟩

/-- The data of a scalar test in slice identities: the test itself (index `none`) and its
first partial derivatives (index `some k`) (`prop:lps-smoothing`). -/
@[expose] def lpsScalarTestData : lpsScalarTests →ₗ[ℝ] (Option (Fin 3) → Vec3 → ℝ) where
  toFun φ := fun o => match o with
    | none => (φ : Vec3 → ℝ)
    | some k => spatialDeriv (φ : Vec3 → ℝ) k
  map_add' φ φ' := by
    funext o
    cases o with
    | none => rfl
    | some k => exact spatialDeriv_add_smooth φ.2.1 φ'.2.1 k
  map_smul' a φ := by
    funext o
    cases o with
    | none => rfl
    | some k =>
      funext x
      have hd : DifferentiableAt ℝ (φ : Vec3 → ℝ) x := (φ.2.1.differentiable (by simp)) x
      change (fderiv ℝ (fun x => a * (φ : Vec3 → ℝ) x) x) (basisVec k) =
        a * (fderiv ℝ (φ : Vec3 → ℝ) x) (basisVec k)
      rw [fderiv_const_mul hd]
      rfl

/-- The data of a scalar test are square integrable (`prop:lps-smoothing`). -/
theorem lpsScalarTestData_memLp (φ : lpsScalarTests) (o : Option (Fin 3)) :
    MemLp (lpsScalarTestData φ o) 2 volume := by
  cases o with
  | none => exact φ.2.1.continuous.memLp_of_hasCompactSupport φ.2.2
  | some k =>
    exact (contDiff_spatialDeriv_smooth φ.2.1 k).continuous.memLp_of_hasCompactSupport
      (φ.2.2.fderiv_apply (𝕜 := ℝ) (basisVec k))

/-- Slice identities for a linear family of tests: if each identity holds for almost every
time and the slice data are square integrable for almost every time, then almost every time
satisfies all the identities simultaneously (`prop:lps-smoothing`). -/
theorem lps_ae_forall_test_of_forall_ae {ν : Measure ℝ} {κ : Type*} [Fintype κ]
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    (A : ℝ → κ → Vec3 → ℝ) (hA : ∀ᵐ t ∂ν, ∀ k, MemLp (A t k) 2 volume)
    (ι : T →ₗ[ℝ] (κ → Vec3 → ℝ)) (hι : ∀ ψ k, MemLp (ι ψ k) 2 volume)
    (h : ∀ ψ : T, ∀ᵐ t ∂ν, ∫ x, ∑ k, A t k x * ι ψ k x = 0) :
    ∀ᵐ t ∂ν, ∀ ψ : T, ∫ x, ∑ k, A t k x * ι ψ k x = 0 := by
  classical
  let ιL : T → (κ → Lp ℝ 2 (volume : Measure Vec3)) := fun ψ k => (hι ψ k).toLp (ι ψ k)
  have h2top : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  have : SecondCountableTopology (κ → Lp ℝ 2 (volume : Measure Vec3)) := inferInstance
  have hR : TopologicalSpace.IsSeparable (Set.range ιL) :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  obtain ⟨C, hCR, hCcount, hCdense⟩ := hR.exists_countable_dense_subset
  choose ψc hψc using fun c : C => hCR c.2
  have hae_count : ∀ᵐ t ∂ν, ∀ c : C, ∫ x, ∑ k, A t k x * ι (ψc c) k x = 0 := by
    have : Countable C := hCcount.to_subtype
    rw [ae_all_iff]
    intro c
    exact h (ψc c)
  filter_upwards [hae_count, hA] with t ht hAt ψ
  let Λ : T → ℝ := fun ψ => ∫ x, ∑ k, A t k x * ι ψ k x
  have hΛlin : ∀ ψ ψ', Λ ψ - Λ ψ' = Λ (ψ - ψ') := by
    intro ψ ψ'
    have h1 : ∀ k, Integrable (fun x => A t k x * ι ψ k x) volume := fun k =>
      (hAt k).integrable_mul (hι ψ k)
    have h2 : ∀ k, Integrable (fun x => A t k x * ι ψ' k x) volume := fun k =>
      (hAt k).integrable_mul (hι ψ' k)
    simp only [Λ, map_sub, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [integral_sub (integrable_finsetSum _ fun k _ => h1 k)
      (integrable_finsetSum _ fun k _ => h2 k)]
  have hΛbound : ∀ ψ, |Λ ψ| ≤ ∑ k, Real.sqrt (∫ x, A t k x ^ 2) *
      Real.sqrt (∫ x, ι ψ k x ^ 2) := by
    intro ψ
    have h1 : ∀ k, Integrable (fun x => A t k x * ι ψ k x) volume := fun k =>
      (hAt k).integrable_mul (hι ψ k)
    calc |Λ ψ| = |∑ k, ∫ x, A t k x * ι ψ k x| := by
          simp only [Λ]
          rw [integral_finsetSum _ fun k _ => h1 k]
      _ ≤ ∑ k, |∫ x, A t k x * ι ψ k x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, Real.sqrt (∫ x, A t k x ^ 2) * Real.sqrt (∫ x, ι ψ k x ^ 2) :=
          Finset.sum_le_sum fun k _ => lps_abs_integral_pairing_le _ _ (hAt k) (hι ψ k)
  by_contra hne
  have hpos : 0 < |Λ ψ| := abs_pos.mpr hne
  set M : ℝ := ∑ k, Real.sqrt (∫ x, A t k x ^ 2) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _
  have hε : 0 < |Λ ψ| / (M + 1) := by positivity
  have hcl : ιL ψ ∈ closure C := hCdense ⟨ψ, rfl⟩
  obtain ⟨c, hcC, hdist⟩ := Metric.mem_closure_iff.mp hcl (|Λ ψ| / (M + 1)) hε
  have hcψ : ιL (ψc ⟨c, hcC⟩) = c := hψc ⟨c, hcC⟩
  have hdk : ∀ k, ‖ιL ψ k - ιL (ψc ⟨c, hcC⟩) k‖ < |Λ ψ| / (M + 1) := by
    intro k
    rw [hcψ]
    have := (dist_pi_lt_iff hε).mp hdist k
    rwa [dist_eq_norm] at this
  have hsqrt : ∀ k, Real.sqrt (∫ x, ι (ψ - ψc ⟨c, hcC⟩) k x ^ 2) < |Λ ψ| / (M + 1) := by
    intro k
    have hm : MemLp (ι (ψ - ψc ⟨c, hcC⟩) k) 2 volume := hι _ k
    rw [vl_integral_sq_eq hm, Real.sqrt_sq ENNReal.toReal_nonneg]
    have h1 : ‖ιL ψ k - ιL (ψc ⟨c, hcC⟩) k‖ =
        (eLpNorm (ι (ψ - ψc ⟨c, hcC⟩) k) 2 volume).toReal := by
      have : ιL ψ k - ιL (ψc ⟨c, hcC⟩) k = hm.toLp (ι (ψ - ψc ⟨c, hcC⟩) k) := by
        simp only [ιL, ← MemLp.toLp_sub]
        refine MemLp.toLp_congr _ _ ?_
        exact Eventually.of_forall fun x => by simp
      rw [this, Lp.norm_toLp]
    rw [← h1]
    exact hdk k
  have hΛ0 : Λ (ψc ⟨c, hcC⟩) = 0 := ht ⟨c, hcC⟩
  have hbd := hΛbound (ψ - ψc ⟨c, hcC⟩)
  rw [← hΛlin, hΛ0, sub_zero] at hbd
  have hbd2 : |Λ ψ| ≤ ∑ k, Real.sqrt (∫ x, A t k x ^ 2) * (|Λ ψ| / (M + 1)) := by
    refine hbd.trans (Finset.sum_le_sum fun k _ => ?_)
    exact mul_le_mul_of_nonneg_left (hsqrt k).le (Real.sqrt_nonneg _)
  rw [← Finset.sum_mul, ← hM] at hbd2
  have : M * (|Λ ψ| / (M + 1)) < |Λ ψ| := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith only [hpos, hM0]
  linarith only [hbd2, this]

/-- Testing the equation against `χ(t) ψ(x)` for a fixed spatial field `ψ`: the slice pairing
of the equation with `ψ` vanishes for almost every time. -/
private theorem lps_source_slice_test_ae {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hsol : IsLpsStrongSolution t₀ T u Du p)
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    {ψ : Vec3 → Vec3} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)),
      ∫ x : Vec3, ((∑ i, Dtu (x, t) i * ψ x i)
        - (∑ i, ∑ j, u (x, t) i * u (x, t) j * spatialDeriv (fun y => ψ y i) j x)
        + (∑ i, ∑ j, Du (x, t) i j * spatialDeriv (fun y => ψ y i) j x)
        - p (x, t) * ∑ i, spatialDeriv (fun y => ψ y i) i x) = 0 := by
  have hp : MemLp p 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) :=
    hsol.2.2.2.2.1
  have hψi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x i) := contDiff_pi.mp hψ i
  have hψci (i : Fin 3) : HasCompactSupport (fun x => ψ x i) :=
    hψc.comp_left (g := fun v : Vec3 => v i) rfl
  have hψ2 (i : Fin 3) : MemLp (fun x => ψ x i) 2 (volume : Measure Vec3) :=
    (hψi i).continuous.memLp_of_hasCompactSupport (hψci i)
  have hdψ2 (i j : Fin 3) : MemLp (fun x => spatialDeriv (fun y => ψ y i) j x) 2
      (volume : Measure Vec3) :=
    (contDiff_spatialDeriv_smooth (hψi i) j).continuous.memLp_of_hasCompactSupport
      ((hψci i).fderiv_apply (𝕜 := ℝ) (basisVec j))
  have hdψb (i j : Fin 3) : ∃ C, ∀ x, ‖spatialDeriv (fun y => ψ y i) j x‖ ≤ C :=
    (contDiff_spatialDeriv_smooth (hψi i) j).continuous.bounded_above_of_compact_support
      ((hψci i).fderiv_apply (𝕜 := ℝ) (basisVec j))
  have hdiv2 : MemLp (fun x => ∑ i, spatialDeriv (fun y => ψ y i) i x) 2
      (volume : Measure Vec3) :=
    memLp_finsetSum Finset.univ fun i _ => hdψ2 i i
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo t₀ T))
    with hν
  have hslab : (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo t₀ T) : Measure (Vec3 × ℝ)) = ν :=
    lps_measure_slab_eq_prod t₀ T
  have hu' : MemLp (fun q : Vec3 × ℝ => u q) 2 ν := by rw [← hslab]; exact hu
  let H : Vec3 × ℝ → ℝ := fun q =>
    (∑ i, Dtu q i * ψ q.1 i)
      - (∑ i, ∑ j, u q i * u q j * spatialDeriv (fun y => ψ y i) j q.1)
      + (∑ i, ∑ j, Du q i j * spatialDeriv (fun y => ψ y i) j q.1)
      - p q * ∑ i, spatialDeriv (fun y => ψ y i) i q.1
  have hH : Integrable H ν := by
    have h1 : Integrable (fun q : Vec3 × ℝ => ∑ i, Dtu q i * ψ q.1 i) ν :=
      integrable_finsetSum _ fun i _ =>
        lps_integrable_slice_pairing (A := fun q => Dtu q i) (hDtu.eval i) (hψ2 i)
    have h2 : Integrable (fun q : Vec3 × ℝ =>
        ∑ i, ∑ j, u q i * u q j * spatialDeriv (fun y => ψ y i) j q.1) ν := by
      refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
      obtain ⟨C, hC⟩ := hdψb i j
      have hprod : Integrable (fun q : Vec3 × ℝ => u q i * u q j) ν :=
        memLp_one_iff_integrable.mp ((hu'.eval i).mul (hu'.eval j) (hpqr := inferInstance))
      have := hprod.bdd_mul (f := fun q : Vec3 × ℝ => spatialDeriv (fun y => ψ y i) j q.1)
        (c := C)
        (((contDiff_spatialDeriv_smooth (hψi i) j).continuous.comp
          continuous_fst).aestronglyMeasurable)
        (Eventually.of_forall fun q => hC q.1)
      simpa [mul_comm] using this
    have h3 : Integrable (fun q : Vec3 × ℝ =>
        ∑ i, ∑ j, Du q i j * spatialDeriv (fun y => ψ y i) j q.1) ν :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        lps_integrable_slice_pairing (A := fun q => Du q i j) ((hDu.eval i).eval j) (hdψ2 i j)
    have h4 : Integrable (fun q : Vec3 × ℝ =>
        p q * ∑ i, spatialDeriv (fun y => ψ y i) i q.1) ν :=
      lps_integrable_slice_pairing (A := fun q => p q) hp hdiv2
    exact ((h1.sub h2).add h3).sub h4
  set f : ℝ → ℝ := fun t => ∫ x : Vec3, H (x, t) with hf
  have hfint : Integrable f (volume.restrict (Ioo t₀ T)) := hH.integral_prod_right
  have hzero : ∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      tsupport χ ⊆ Ioo t₀ T → ∫ t in Ioo t₀ T, χ t * f t = 0 := by
    intro χ hχ hχc hχs
    have hsub : tsupport (fun q : Vec3 × ℝ => (fun i => χ q.2 * ψ q.1 i : Vec3)) ⊆
        tsupport ψ ×ˢ tsupport χ := by
      refine closure_minimal ?_ ((isClosed_tsupport ψ).prod (isClosed_tsupport χ))
      intro z hz
      have hz' : (fun i => χ z.2 * ψ z.1 i : Vec3) ≠ 0 := hz
      have hχz : χ z.2 ≠ 0 := by
        intro h0
        exact hz' (funext fun i => by simp [h0])
      have hψz : ψ z.1 ≠ 0 := by
        intro h0
        exact hz' (funext fun i => by simp [h0])
      exact ⟨subset_tsupport _ hψz, subset_tsupport _ hχz⟩
    have hφmem : (fun q : Vec3 × ℝ => (fun i => χ q.2 * ψ q.1 i : Vec3)) ∈
        spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo t₀ T) := by
      refine ⟨contDiff_pi.mpr fun i => (hχ.comp contDiff_snd).mul ((hψi i).comp contDiff_fst),
        IsCompact.of_isClosed_subset (hψc.prod hχc) (isClosed_tsupport _) hsub, ?_⟩
      intro z hz
      exact ⟨mem_univ _, hχs (hsub hz).2⟩
    have hEq := ESS.LPS.lps_strong_solution_equation_Dtu hsol hderiv hDtu _ hφmem
    have hsp (i j : Fin 3) (z : ParabolicPoint) :
        spatialPartial (fun y : ParabolicPoint => χ y.2 * ψ y.1 i) j z =
          χ z.2 * spatialDeriv (fun y => ψ y i) j z.1 :=
      lps_separated_spatialPartial (χ := χ) (f := fun x => ψ x i) (hψi i) j z
    simp only [hsp] at hEq
    have hpt (q : Vec3 × ℝ) :
        ((∑ i, Dtu q i * (χ q.2 * ψ q.1 i))
          - (∑ i, ∑ j, (u q i * u q j) * (χ q.2 * spatialDeriv (fun y => ψ y i) j q.1))
          + (∑ i, ∑ j, Du q i j * (χ q.2 * spatialDeriv (fun y => ψ y i) j q.1))
          - p q * ∑ i, χ q.2 * spatialDeriv (fun y => ψ y i) i q.1) = χ q.2 * H q := by
      simp only [H, Fin.sum_univ_three]
      ring
    have hEq' : ∫ q, χ q.2 * H q ∂ν = 0 := by
      rw [← hslab]
      refine Eq.trans ?_ hEq
      exact integral_congr_ae (Eventually.of_forall fun q => (hpt q).symm)
    obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hχc
    have hmul : Integrable (fun q : Vec3 × ℝ => χ q.2 * H q) ν :=
      hH.bdd_mul (f := fun q : Vec3 × ℝ => χ q.2) (c := C)
        ((hχ.continuous.comp continuous_snd).aestronglyMeasurable)
        (Eventually.of_forall fun q => hC q.2)
    rw [integral_prod_symm _ hmul] at hEq'
    simpa [hf, integral_const_mul] using hEq'
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), t ∈ Ioo t₀ T → f t = 0 :=
    isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hfint.locallyIntegrable.locallyIntegrableOn _)
      (fun g hg hgc hgs => by simpa using hzero g hg hgc hgs)
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t ht htI
  exact ht htI

/-- For almost every time the slice pairing of the equation with a fixed spatial field `ψ`,
with the nonlinear term moved onto `(u·∇)u` and the viscous term onto `Δu`, vanishes. -/
private theorem lps_source_slice_vector_ae {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hsol : IsLpsStrongSolution t₀ T u Du p)
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    {ψ : Vec3 → Vec3} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)),
      ∫ x : Vec3, ((∑ i, (Dtu (x, t) i - ∑ j, D2u (x, t) i j j +
          ∑ j, u (x, t) j * Du (x, t) i j) * ψ x i)
        - p (x, t) * ∑ i, spatialDeriv (fun y => ψ y i) i x) = 0 := by
  have hp : MemLp p 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) :=
    hsol.2.2.2.2.1
  have hψi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x i) := contDiff_pi.mp hψ i
  have hψci (i : Fin 3) : HasCompactSupport (fun x => ψ x i) :=
    hψc.comp_left (g := fun v : Vec3 => v i) rfl
  have hψ2 (i : Fin 3) : MemLp (fun x => ψ x i) 2 (volume : Measure Vec3) :=
    (hψi i).continuous.memLp_of_hasCompactSupport (hψci i)
  have hdψ2 (i j : Fin 3) : MemLp (fun x => spatialDeriv (fun y => ψ y i) j x) 2
      (volume : Measure Vec3) :=
    (contDiff_spatialDeriv_smooth (hψi i) j).continuous.memLp_of_hasCompactSupport
      ((hψci i).fderiv_apply (𝕜 := ℝ) (basisVec j))
  have hdψb (i j : Fin 3) : ∃ C, ∀ x, ‖spatialDeriv (fun y => ψ y i) j x‖ ≤ C :=
    (contDiff_spatialDeriv_smooth (hψi i) j).continuous.bounded_above_of_compact_support
      ((hψci i).fderiv_apply (𝕜 := ℝ) (basisVec j))
  have hdiv2 : MemLp (fun x => ∑ i, spatialDeriv (fun y => ψ y i) i x) 2
      (volume : Measure Vec3) :=
    memLp_finsetSum Finset.univ fun i _ => hdψ2 i i
  filter_upwards [lps_source_slice_test_ae hsol hderiv hu hDu hDtu hψ hψc,
    lps_strong_good_slices hsol hderiv hu hDu hD2u hDtu, lps_slice_memLp_two_ae_slab hp,
    ae_restrict_mem measurableSet_Ioo] with t ht hgood hpt htI
  obtain ⟨hDt, hD2, hgrad, htr⟩ := hgood
  have htIcc : t ∈ Icc t₀ T := ⟨htI.1.le, htI.2.le⟩
  obtain ⟨hu2t, hDu2t⟩ := lps_strong_solution_slice_memLp_two hsol htIcc
  have hH1t := (lps_strong_solution_slice_h1 hsol htIcc).2.2
  have hgu := lps_strong_solution_slice_weak_gradient hsol htIcc
  have K : (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        u (x, t) i * u (x, t) j * spatialDeriv (fun y => ψ y i) j x) =
      -∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, u (x, t) j * Du (x, t) i j) * ψ x i :=
    lps_h1_convection_test_identity (u := fun x => u (x, t))
      (Du := fun x => Du (x, t)) (D2u := fun x => D2u (x, t)) (ψ := ψ)
      hu2t hDu2t hD2 hH1t hgu hgrad htr hψi hψci
  have L : (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        Du (x, t) i j * spatialDeriv (fun y => ψ y i) j x) =
      -∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u (x, t) i j j) * ψ x i :=
    lps_h1_laplacian_test_identity (Du := fun x => Du (x, t))
      (D2u := fun x => D2u (x, t)) (ψ := ψ) hgrad hψi hψci hDu2t hD2
  have hN (i : Fin 3) := lps_h1_convection_memLp_two (u := fun x => u (x, t))
    (Du := fun x => Du (x, t)) (D2u := fun x => D2u (x, t)) hu2t hDu2t hD2 hH1t hgrad i
  have ia : Integrable (fun x : Vec3 => ∑ i, Dtu (x, t) i * ψ x i) volume :=
    integrable_finsetSum _ fun i _ => (hDt.eval i).integrable_mul (hψ2 i)
  have ib : Integrable (fun x : Vec3 => ∑ i, ∑ j,
      u (x, t) i * u (x, t) j * spatialDeriv (fun y => ψ y i) j x) volume := by
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    obtain ⟨C, hC⟩ := hdψb i j
    have hprod : Integrable (fun x : Vec3 => u (x, t) i * u (x, t) j) volume :=
      memLp_one_iff_integrable.mp ((hu2t.eval i).mul (hu2t.eval j) (hpqr := inferInstance))
    have := hprod.bdd_mul (f := fun x : Vec3 => spatialDeriv (fun y => ψ y i) j x) (c := C)
      (contDiff_spatialDeriv_smooth (hψi i) j).continuous.aestronglyMeasurable
      (Eventually.of_forall hC)
    simpa [mul_comm] using this
  have ic : Integrable (fun x : Vec3 => ∑ i, ∑ j,
      Du (x, t) i j * spatialDeriv (fun y => ψ y i) j x) volume :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      ((hDu2t.eval i).eval j).integrable_mul (hdψ2 i j)
  have id : Integrable (fun x : Vec3 =>
      p (x, t) * ∑ i, spatialDeriv (fun y => ψ y i) i x) volume :=
    hpt.integrable_mul hdiv2
  have iL : Integrable (fun x : Vec3 => ∑ i, (∑ j, D2u (x, t) i j j) * ψ x i) volume :=
    integrable_finsetSum _ fun i _ =>
      (memLp_finsetSum Finset.univ fun j _ => ((hD2.eval i).eval j).eval j).integrable_mul
        (hψ2 i)
  have iB : Integrable (fun x : Vec3 =>
      ∑ i, (∑ j, u (x, t) j * Du (x, t) i j) * ψ x i) volume :=
    integrable_finsetSum _ fun i _ => (hN i).integrable_mul (hψ2 i)
  have h1 : (∫ x : Vec3, ((∑ i, Dtu (x, t) i * ψ x i)
        - (∑ i, ∑ j, u (x, t) i * u (x, t) j * spatialDeriv (fun y => ψ y i) j x)
        + (∑ i, ∑ j, Du (x, t) i j * spatialDeriv (fun y => ψ y i) j x)
        - p (x, t) * ∑ i, spatialDeriv (fun y => ψ y i) i x)) =
      (∫ x : Vec3, ∑ i, Dtu (x, t) i * ψ x i)
        - (∫ x : Vec3, ∑ i, ∑ j, u (x, t) i * u (x, t) j * spatialDeriv (fun y => ψ y i) j x)
        + (∫ x : Vec3, ∑ i, ∑ j, Du (x, t) i j * spatialDeriv (fun y => ψ y i) j x)
        - ∫ x : Vec3, p (x, t) * ∑ i, spatialDeriv (fun y => ψ y i) i x := by
    have iabc : Integrable (fun x : Vec3 => (∑ i, Dtu (x, t) i * ψ x i)
        - (∑ i, ∑ j, u (x, t) i * u (x, t) j * spatialDeriv (fun y => ψ y i) j x)
        + (∑ i, ∑ j, Du (x, t) i j * spatialDeriv (fun y => ψ y i) j x)) volume :=
      (ia.sub ib).add ic
    rw [integral_sub iabc id, lps_integral_sub_add ia ib ic]
  have hpt' (x : Vec3) : ((∑ i, (Dtu (x, t) i - ∑ j, D2u (x, t) i j j +
          ∑ j, u (x, t) j * Du (x, t) i j) * ψ x i)
        - p (x, t) * ∑ i, spatialDeriv (fun y => ψ y i) i x) =
      ((∑ i, Dtu (x, t) i * ψ x i) - (∑ i, (∑ j, D2u (x, t) i j j) * ψ x i)
        + (∑ i, (∑ j, u (x, t) j * Du (x, t) i j) * ψ x i))
        - p (x, t) * ∑ i, spatialDeriv (fun y => ψ y i) i x := by
    simp only [Fin.sum_univ_three]
    ring
  have h2 : (∫ x : Vec3, ((∑ i, (Dtu (x, t) i - ∑ j, D2u (x, t) i j j +
          ∑ j, u (x, t) j * Du (x, t) i j) * ψ x i)
        - p (x, t) * ∑ i, spatialDeriv (fun y => ψ y i) i x)) =
      (∫ x : Vec3, ∑ i, Dtu (x, t) i * ψ x i)
        - (∫ x : Vec3, ∑ i, (∑ j, D2u (x, t) i j j) * ψ x i)
        + (∫ x : Vec3, ∑ i, (∑ j, u (x, t) j * Du (x, t) i j) * ψ x i)
        - ∫ x : Vec3, p (x, t) * ∑ i, spatialDeriv (fun y => ψ y i) i x := by
    have iaLB : Integrable (fun x : Vec3 => (∑ i, Dtu (x, t) i * ψ x i)
        - (∑ i, (∑ j, D2u (x, t) i j j) * ψ x i)
        + (∑ i, (∑ j, u (x, t) j * Du (x, t) i j) * ψ x i)) volume :=
      (ia.sub iL).add iB
    rw [integral_congr_ae (Eventually.of_forall hpt'), integral_sub iaLB id,
      lps_integral_sub_add ia iL iB]
  rw [h2]
  rw [h1] at ht
  linarith only [ht, K, L]

/-- `prop:lps-smoothing`: the pressure equation on almost every time slice. For almost every
time `t`, the pressure slice `p(t)` is square integrable and has the square-integrable weak
gradient `Gq = -(∂ₜu - Δu + (u·∇)u)(t)`, where `Δu = Σⱼ ∂ⱼ∂ⱼu` and
`((u·∇)u)ᵢ = Σⱼ uⱼ ∂ⱼuᵢ`. -/
theorem lps_strong_slice_pressure_equation {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hsol : IsLpsStrongSolution t₀ T u Du p)
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)))) :
    ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∃ Gq : Fin 3 → Vec3 → ℝ,
      (∀ i, MemLp (Gq i) 2 volume) ∧ MemLp (fun x : Vec3 => p (x, t)) 2 volume ∧
      (∀ i, HasWeakPartialDerivOn (Set.univ : Set Vec3) i (fun x => p (x, t)) (Gq i)) ∧
      ∀ᵐ x ∂(volume : Measure Vec3), ∀ i,
        Dtu (x, t) i - ∑ j, D2u (x, t) i j j + ∑ j, u (x, t) j * Du (x, t) i j + Gq i x = 0 := by
  have hp : MemLp p 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) :=
    hsol.2.2.2.2.1
  let F : ℝ → Fin 3 → Vec3 → ℝ := fun t i x =>
    Dtu (x, t) i - ∑ j, D2u (x, t) i j j + ∑ j, u (x, t) j * Du (x, t) i j
  have hgood : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)),
      (∀ i, MemLp (F t i) 2 volume) ∧ MemLp (fun x : Vec3 => p (x, t)) 2 volume := by
    filter_upwards [lps_strong_good_slices hsol hderiv hu hDu hD2u hDtu,
      lps_slice_memLp_two_ae_slab hp, ae_restrict_mem measurableSet_Ioo] with t hg hpt htI
    obtain ⟨hDt, hD2, hgrad, -⟩ := hg
    have htIcc : t ∈ Icc t₀ T := ⟨htI.1.le, htI.2.le⟩
    obtain ⟨hu2t, hDu2t⟩ := lps_strong_solution_slice_memLp_two hsol htIcc
    have hH1t := (lps_strong_solution_slice_h1 hsol htIcc).2.2
    refine ⟨fun i => ?_, hpt⟩
    exact ((hDt.eval i).sub (memLp_finsetSum Finset.univ fun j _ =>
      ((hD2.eval i).eval j).eval j)).add
      (lps_h1_convection_memLp_two (u := fun x => u (x, t)) (Du := fun x => Du (x, t))
        (D2u := fun x => D2u (x, t)) hu2t hDu2t hD2 hH1t hgrad i)
  let A : Fin 3 → ℝ → Option (Fin 3) → Vec3 → ℝ := fun i t o => match o with
    | none => F t i
    | some k => fun x => if k = i then -p (x, t) else 0
  have hptw : ∀ (φ : lpsScalarTests) (i : Fin 3) (t : ℝ) (x : Vec3),
      ∑ o, A i t o x * lpsScalarTestData φ o x =
        F t i x * (φ : Vec3 → ℝ) x - p (x, t) * spatialDeriv (φ : Vec3 → ℝ) i x := by
    intro φ i t x
    rw [Fintype.sum_option]
    simp only [A, lpsScalarTestData, LinearMap.coe_mk, AddHom.coe_mk, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  have hdir : ∀ i, ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ φ : lpsScalarTests,
      ∫ x, ∑ o, A i t o x * lpsScalarTestData φ o x = 0 := by
    intro i
    refine lps_ae_forall_test_of_forall_ae (A i) ?_ lpsScalarTestData lpsScalarTestData_memLp ?_
    · filter_upwards [hgood] with t ht o
      cases o with
      | none => exact ht.1 i
      | some k =>
        by_cases hk : k = i
        · simp only [A, hk, ↓reduceIte]
          exact ht.2.neg
        · simp only [A, hk, ↓reduceIte]
          exact MemLp.zero
    · intro φ
      have hφ : ContDiff ℝ (⊤ : ℕ∞) (φ : Vec3 → ℝ) := φ.2.1
      have hφc : HasCompactSupport (φ : Vec3 → ℝ) := φ.2.2
      let ψ : Vec3 → Vec3 := fun x i' => if i' = i then (φ : Vec3 → ℝ) x else 0
      have hψi : ∀ i', (fun x => ψ x i') = if i' = i then (φ : Vec3 → ℝ) else fun _ => 0 := by
        intro i'
        by_cases h : i' = i
        · simp only [ψ, h, ↓reduceIte]
        · simp only [ψ, h, ↓reduceIte]
      have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
        refine contDiff_pi.mpr fun i' => ?_
        rw [hψi i']
        split_ifs
        · exact hφ
        · exact contDiff_const
      have hψc : HasCompactSupport ψ := by
        refine hφc.mono ?_
        intro x hx
        by_contra h0
        apply hx
        have h0' : (φ : Vec3 → ℝ) x = 0 := Function.notMem_support.mp h0
        funext i'
        simp [ψ, h0']
      have hsd : ∀ i' x, spatialDeriv (fun y => ψ y i') i' x =
          if i' = i then spatialDeriv (φ : Vec3 → ℝ) i x else 0 := by
        intro i' x
        rw [hψi i']
        by_cases h : i' = i
        · subst h
          simp only [↓reduceIte]
        · simp [h, spatialDeriv]
      filter_upwards [lps_source_slice_vector_ae hsol hderiv hu hDu hD2u hDtu hψ hψc] with t ht
      rw [← ht]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      change ∑ o, A i t o x * lpsScalarTestData φ o x = _
      rw [hptw φ i t x]
      simp only [hsd, ψ, F, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hall : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ i, ∀ φ : lpsScalarTests,
      ∫ x, ∑ o, A i t o x * lpsScalarTestData φ o x = 0 := ae_all_iff.mpr hdir
  filter_upwards [hall, hgood] with t ht hg
  refine ⟨fun i x => -F t i x, fun i => (hg.1 i).neg, hg.2, fun i => ?_,
    Eventually.of_forall fun x i => by simp only [F]; ring⟩
  intro φ hφ hφc _
  have h0 := ht i ⟨φ, hφ, hφc⟩
  simp only [hptw] at h0
  have iF : Integrable (fun x => F t i x * φ x) volume :=
    (hg.1 i).integrable_mul (q := 2) (hφ.continuous.memLp_of_hasCompactSupport hφc)
  have ip : Integrable (fun x => p (x, t) * spatialDeriv φ i x) volume :=
    hg.2.integrable_mul (q := 2)
      ((contDiff_spatialDeriv_smooth hφ i).continuous.memLp_of_hasCompactSupport
        (hφc.fderiv_apply (𝕜 := ℝ) (basisVec i)))
  rw [integral_sub iF ip] at h0
  simp only [Measure.restrict_univ, neg_mul, integral_neg, neg_neg]
  change ∫ x, p (x, t) * spatialDeriv φ i x = ∫ x, F t i x * φ x
  linarith only [h0]

end ESS
