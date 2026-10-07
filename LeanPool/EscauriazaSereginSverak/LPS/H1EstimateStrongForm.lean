/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateEquation
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSliceConvection
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSobolevBridge
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateTestField
public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs

/-!
# The strong form of the equation against separated test fields

Testing the pressure-free weak equation of a strong solution against the
separated solenoidal field `χ(t) ψ(x)`, and using the weak time and spatial
derivatives, gives the integrated strong form
`∫ χ(t) ⟨∂ₜu - Δu + (u·∇)u, ψ⟩ dt = 0` (`lem:lps-H1-estimate`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_prod_integrable_mul_test
    {a b : ℝ} {f : Vec3 × ℝ → ℝ} {g : Vec3 × ℝ → ℝ}
    (hf : MemLp f 2 ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))))
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun q => f q * g q)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
  hf.integrable_mul (q := 2) (hg.memLp_of_hasCompactSupport hgc)

private theorem lps_prod_integrable_L1_mul_test
    {a b : ℝ} {f : Vec3 × ℝ → ℝ} {g : Vec3 × ℝ → ℝ}
    (hf : Integrable f ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))))
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun q => f q * g q)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  have := hf.bdd_mul (f := g) (c := C) hg.aestronglyMeasurable
    (Eventually.of_forall hC)
  simpa [mul_comm] using this

private theorem lps_sep_cont_compact {χ : ℝ → ℝ} {f : Vec3 → ℝ}
    (hχ : Continuous χ) (hχk : HasCompactSupport χ)
    (hf : Continuous f) (hfk : HasCompactSupport f) :
    Continuous (fun q : Vec3 × ℝ => χ q.2 * f q.1) ∧
      HasCompactSupport (fun q : Vec3 × ℝ => χ q.2 * f q.1) := by
  refine ⟨(hχ.comp continuous_snd).mul (hf.comp continuous_fst), ?_⟩
  exact IsCompact.of_isClosed_subset (hfk.prod hχk) (isClosed_tsupport _)
    lps_separated_tsupport_subset

private theorem lps_sep_vec_mem {a b : ℝ} {χ : ℝ → ℝ} {ψ : Vec3 → Vec3}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo a b)
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x i)) (hψc : HasCompactSupport ψ) :
    (fun q : Vec3 × ℝ => (fun i => χ q.2 * ψ q.1 i : Vec3)) ∈
      spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo a b) := by
  refine ⟨contDiff_pi.mpr fun i => (hχ.comp contDiff_snd).mul ((hψ i).comp contDiff_fst), ?_, ?_⟩
  · refine IsCompact.of_isClosed_subset (hψc.prod hχc) (isClosed_tsupport _) ?_
    refine closure_minimal ?_ ((isClosed_tsupport ψ).prod (isClosed_tsupport χ))
    intro z hz
    have hz' : (fun i => χ z.2 * ψ z.1 i : Vec3) ≠ 0 := hz
    have h1 : χ z.2 ≠ 0 := by
      intro h
      apply hz'
      funext i
      simp [h]
    have h2 : ψ z.1 ≠ 0 := by
      intro h
      apply hz'
      funext i
      simp [h]
    exact ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩
  · intro z hz
    have : z ∈ tsupport ψ ×ˢ tsupport χ := by
      refine closure_minimal ?_ ((isClosed_tsupport ψ).prod (isClosed_tsupport χ)) hz
      intro w hw
      have hw' : (fun i => χ w.2 * ψ w.1 i : Vec3) ≠ 0 := hw
      have h1 : χ w.2 ≠ 0 := by
        intro h
        apply hw'
        funext i
        simp [h]
      have h2 : ψ w.1 ≠ 0 := by
        intro h
        apply hw'
        funext i
        simp [h]
      exact ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩
    exact ⟨mem_univ _, hχs this.2⟩

/-- Integral of `-f - g + h`. -/
theorem lps_integral_neg_sub_add {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f g h : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    ∫ q, (-f q - g q + h q) ∂μ = -∫ q, f q ∂μ - ∫ q, g q ∂μ + ∫ q, h q ∂μ := by
  have h1 : Integrable (fun q => -f q - g q) μ := hf.neg.sub hg
  have h2 : Integrable (fun q => -f q) μ := hf.neg
  rw [integral_add h1 hh, integral_sub h2 hg, integral_neg]

/-- Integral of `f - g + h`. -/
theorem lps_integral_sub_add {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f g h : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    ∫ q, (f q - g q + h q) ∂μ = ∫ q, f q ∂μ - ∫ q, g q ∂μ + ∫ q, h q ∂μ := by
  have h1 : Integrable (fun q => f q - g q) μ := hf.sub hg
  rw [integral_add h1 hh, integral_sub hf hg]

/-- Integral of `f - g - h`. -/
theorem lps_integral_sub_sub {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f g h : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    ∫ q, (f q - g q - h q) ∂μ = ∫ q, f q ∂μ - ∫ q, g q ∂μ - ∫ q, h q ∂μ := by
  have h1 : Integrable (fun q => f q - g q) μ := hf.sub hg
  rw [integral_sub h1 hh, integral_sub hf hg]

/-- Testing the strong equation with a separated solenoidal field: the weak
time and spatial derivatives convert the weak form into the integrated strong
form, up to the transported product `u ⊗ u` (`lem:lps-H1-estimate`). -/
theorem lps_strong_separated_identity
    {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (hU : IsLpsStrongSolution t₀ t₁ u Du p)
    (hD : HasSpaceTimeWeakDerivs Set.univ (Ioo t₀ t₁) u Du D2u Dtu)
    (hMu : MemLp u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    (hMDu : MemLp Du 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    (hMD2 : MemLp D2u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    (hMDt : MemLp Dtu 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    {χ : ℝ → ℝ} {ψ : Vec3 → Vec3}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo t₀ t₁)
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x i)) (hψc : HasCompactSupport ψ)
    (hdiv : ∀ x, ∑ i : Fin 3, spatialDeriv (fun y => ψ y i) i x = 0) :
    ∫ q : Vec3 × ℝ,
      ((∑ i : Fin 3, Dtu (parabolicHomeomorph.symm q) i * (χ q.2 * ψ q.1 i)) -
        (∑ i : Fin 3, ∑ j : Fin 3, u (parabolicHomeomorph.symm q) i *
          u (parabolicHomeomorph.symm q) j *
            (χ q.2 * spatialDeriv (fun y => ψ y i) j q.1)) -
        (∑ i : Fin 3, (∑ j : Fin 3, D2u (parabolicHomeomorph.symm q) i j j) *
          (χ q.2 * ψ q.1 i)))
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo t₀ t₁))) = 0 := by
  set ν : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo t₀ t₁)) with hν
  have hψi (i : Fin 3) : HasCompactSupport (fun x => ψ x i) :=
    hψc.comp_left (g := fun v : Vec3 => v i) rfl
  have hMU : MemLp (fun q : Vec3 × ℝ => u (parabolicHomeomorph.symm q)) 2 ν :=
    lps_memLp_slab_to_prod hMu
  have hMDU : MemLp (fun q : Vec3 × ℝ => Du (parabolicHomeomorph.symm q)) 2 ν :=
    lps_memLp_slab_to_prod hMDu
  have hMD2U : MemLp (fun q : Vec3 × ℝ => D2u (parabolicHomeomorph.symm q)) 2 ν :=
    lps_memLp_slab_to_prod hMD2
  have hMDtU : MemLp (fun q : Vec3 × ℝ => Dtu (parabolicHomeomorph.symm q)) 2 ν :=
    lps_memLp_slab_to_prod hMDt
  -- the separated test functions
  have hΦmem (i : Fin 3) := lps_separated_test_mem hχ hχc hχs (hψ i) (hψi i)
  have hφ := lps_sep_vec_mem hχ hχc hχs hψ hψc
  -- pressure-free weak equation
  have hEq := ESS.LPS.lps_strong_solenoidal_weak_equation hU hφ (fun z => by
    have : ∀ i : Fin 3, spatialPartial (fun y : ParabolicPoint =>
        (fun q : Vec3 × ℝ => (fun i => χ q.2 * ψ q.1 i : Vec3)) y i) i z =
        χ z.2 * spatialDeriv (fun y => ψ y i) i z.1 := fun i =>
      lps_separated_spatialPartial (χ := χ) (hψ i) i z
    simp only [this, ← Finset.mul_sum, hdiv, mul_zero])
  -- continuity and compact support of the test integrands
  have hχ0 : Continuous χ := hχ.continuous
  have hχ1 : Continuous (deriv χ) := hχ.continuous_deriv (by simp)
  have hχ1c : HasCompactSupport (deriv χ) := hχc.deriv
  have hψ0 (i : Fin 3) : Continuous (fun x => ψ x i) := (hψ i).continuous
  have hψ1 (i j : Fin 3) : Continuous (fun x => spatialDeriv (fun y => ψ y i) j x) :=
    (contDiff_spatialDeriv_smooth (hψ i) j).continuous
  have hψ1c (i j : Fin 3) : HasCompactSupport (fun x => spatialDeriv (fun y => ψ y i) j x) :=
    (hψi i).fderiv_apply (𝕜 := ℝ) (basisVec j)
  have tA (i : Fin 3) := lps_sep_cont_compact hχ1 hχ1c (hψ0 i) (hψi i)
  have tF (i : Fin 3) := lps_sep_cont_compact hχ0 hχc (hψ0 i) (hψi i)
  have tG (i j : Fin 3) := lps_sep_cont_compact hχ0 hχc (hψ1 i j) (hψ1c i j)
  -- integrability of every term
  have iA (i : Fin 3) : Integrable (fun q : Vec3 × ℝ =>
      u (parabolicHomeomorph.symm q) i * (deriv χ q.2 * ψ q.1 i)) ν :=
    lps_prod_integrable_mul_test (hMU.eval i) (tA i).1 (tA i).2
  have iT (i : Fin 3) : Integrable (fun q : Vec3 × ℝ =>
      Dtu (parabolicHomeomorph.symm q) i * (χ q.2 * ψ q.1 i)) ν :=
    lps_prod_integrable_mul_test (hMDtU.eval i) (tF i).1 (tF i).2
  have iB (i j : Fin 3) : Integrable (fun q : Vec3 × ℝ =>
      u (parabolicHomeomorph.symm q) i * u (parabolicHomeomorph.symm q) j *
        (χ q.2 * spatialDeriv (fun y => ψ y i) j q.1)) ν := by
    have hprod : Integrable (fun q : Vec3 × ℝ =>
        u (parabolicHomeomorph.symm q) i * u (parabolicHomeomorph.symm q) j) ν :=
      memLp_one_iff_integrable.mp ((hMU.eval i).mul (hMU.eval j) (hpqr := inferInstance))
    exact lps_prod_integrable_L1_mul_test hprod (tG i j).1 (tG i j).2
  have iC (i j : Fin 3) : Integrable (fun q : Vec3 × ℝ =>
      Du (parabolicHomeomorph.symm q) i j *
        (χ q.2 * spatialDeriv (fun y => ψ y i) j q.1)) ν :=
    lps_prod_integrable_mul_test ((hMDU.eval i).eval j) (tG i j).1 (tG i j).2
  have iL (i j : Fin 3) : Integrable (fun q : Vec3 × ℝ =>
      D2u (parabolicHomeomorph.symm q) i j j * (χ q.2 * ψ q.1 i)) ν :=
    lps_prod_integrable_mul_test (((hMD2U.eval i).eval j).eval j) (tF i).1 (tF i).2
  -- weak time derivative
  have hT (i : Fin 3) : (∫ q : Vec3 × ℝ,
      u (parabolicHomeomorph.symm q) i * (deriv χ q.2 * ψ q.1 i) ∂ν) =
      -∫ q : Vec3 × ℝ, Dtu (parabolicHomeomorph.symm q) i * (χ q.2 * ψ q.1 i) ∂ν := by
    have h := (hD.2.2.2.2 _ (hΦmem i)).2.2 i
    rw [lps_setIntegral_slab_to_prod, lps_setIntegral_slab_to_prod] at h
    calc (∫ q : Vec3 × ℝ, u (parabolicHomeomorph.symm q) i * (deriv χ q.2 * ψ q.1 i) ∂ν)
        = ∫ q : Vec3 × ℝ, u (parabolicHomeomorph.symm q) i *
            timePartial (fun z : ParabolicPoint => χ z.2 * ψ z.1 i)
              (parabolicHomeomorph.symm q) ∂ν := by
          congr 1
          funext q
          rw [lps_separated_timePartial (f := fun x => ψ x i) hχ]
          rfl
      _ = _ := h
  -- weak spatial derivative of `Du`
  have hS (i j : Fin 3) : (∫ q : Vec3 × ℝ,
      Du (parabolicHomeomorph.symm q) i j *
        (χ q.2 * spatialDeriv (fun y => ψ y i) j q.1) ∂ν) =
      -∫ q : Vec3 × ℝ, D2u (parabolicHomeomorph.symm q) i j j * (χ q.2 * ψ q.1 i) ∂ν := by
    have h := (hD.2.2.2.2 _ (hΦmem i)).2.1 i j j
    rw [lps_setIntegral_slab_to_prod, lps_setIntegral_slab_to_prod] at h
    calc (∫ q : Vec3 × ℝ, Du (parabolicHomeomorph.symm q) i j *
          (χ q.2 * spatialDeriv (fun y => ψ y i) j q.1) ∂ν)
        = ∫ q : Vec3 × ℝ, Du (parabolicHomeomorph.symm q) i j *
            spatialPartial (fun z : ParabolicPoint => χ z.2 * ψ z.1 i) j
              (parabolicHomeomorph.symm q) ∂ν := by
          congr 1
          funext q
          rw [lps_separated_spatialPartial (χ := χ) (f := fun x => ψ x i) (hψ i) j]
          rfl
      _ = _ := h
  -- expand the weak equation
  rw [lps_setIntegral_slab_to_prod] at hEq
  have hEq2 : ∫ q : Vec3 × ℝ,
      (-(∑ i : Fin 3, u (parabolicHomeomorph.symm q) i * (deriv χ q.2 * ψ q.1 i)) -
        (∑ i : Fin 3, ∑ j : Fin 3, u (parabolicHomeomorph.symm q) i *
          u (parabolicHomeomorph.symm q) j *
            (χ q.2 * spatialDeriv (fun y => ψ y i) j q.1)) +
        (∑ i : Fin 3, ∑ j : Fin 3, Du (parabolicHomeomorph.symm q) i j *
          (χ q.2 * spatialDeriv (fun y => ψ y i) j q.1))) ∂ν = 0 := by
    refine (integral_congr_ae (Eventually.of_forall fun q => ?_)).trans hEq
    have hp1 (i : Fin 3) : timePartial (fun y : ParabolicPoint => χ y.2 * ψ y.1 i)
        (parabolicHomeomorph.symm q) = deriv χ q.2 * ψ q.1 i :=
      lps_separated_timePartial (f := fun x => ψ x i) hχ _
    have hp2 (i j : Fin 3) : spatialPartial (fun y : ParabolicPoint => χ y.2 * ψ y.1 i) j
        (parabolicHomeomorph.symm q) = χ q.2 * spatialDeriv (fun y => ψ y i) j q.1 :=
      lps_separated_spatialPartial (χ := χ) (f := fun x => ψ x i) (hψ i) j _
    simp only [hp1, hp2]
  have hEq' : (-∑ i : Fin 3, ∫ q : Vec3 × ℝ,
        u (parabolicHomeomorph.symm q) i * (deriv χ q.2 * ψ q.1 i) ∂ν) -
      (∑ i : Fin 3, ∑ j : Fin 3, ∫ q : Vec3 × ℝ,
        u (parabolicHomeomorph.symm q) i * u (parabolicHomeomorph.symm q) j *
          (χ q.2 * spatialDeriv (fun y => ψ y i) j q.1) ∂ν) +
      (∑ i : Fin 3, ∑ j : Fin 3, ∫ q : Vec3 × ℝ,
        Du (parabolicHomeomorph.symm q) i j *
          (χ q.2 * spatialDeriv (fun y => ψ y i) j q.1) ∂ν) = 0 := by
    have hAs : Integrable (fun q : Vec3 × ℝ =>
        ∑ i : Fin 3, u (parabolicHomeomorph.symm q) i * (deriv χ q.2 * ψ q.1 i)) ν :=
      integrable_finsetSum _ fun i _ => iA i
    have hBs : Integrable (fun q : Vec3 × ℝ =>
        ∑ i : Fin 3, ∑ j : Fin 3, u (parabolicHomeomorph.symm q) i *
          u (parabolicHomeomorph.symm q) j *
            (χ q.2 * spatialDeriv (fun y => ψ y i) j q.1)) ν :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iB i j
    have hCs : Integrable (fun q : Vec3 × ℝ =>
        ∑ i : Fin 3, ∑ j : Fin 3, Du (parabolicHomeomorph.symm q) i j *
          (χ q.2 * spatialDeriv (fun y => ψ y i) j q.1)) ν :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iC i j
    rw [lps_integral_neg_sub_add hAs hBs hCs,
      integral_finsetSum _ fun i _ => iA i,
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iB i j,
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iC i j] at hEq2
    simp only [integral_finsetSum _ fun j _ => iB _ j,
      integral_finsetSum _ fun j _ => iC _ j] at hEq2
    exact hEq2
  simp only [hT, hS, Finset.sum_neg_distrib, neg_neg] at hEq'
  have hTs : Integrable (fun q : Vec3 × ℝ =>
      ∑ i : Fin 3, Dtu (parabolicHomeomorph.symm q) i * (χ q.2 * ψ q.1 i)) ν :=
    integrable_finsetSum _ fun i _ => iT i
  have hBs : Integrable (fun q : Vec3 × ℝ =>
      ∑ i : Fin 3, ∑ j : Fin 3, u (parabolicHomeomorph.symm q) i *
        u (parabolicHomeomorph.symm q) j *
          (χ q.2 * spatialDeriv (fun y => ψ y i) j q.1)) ν :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iB i j
  have hLs : Integrable (fun q : Vec3 × ℝ =>
      ∑ i : Fin 3, (∑ j : Fin 3, D2u (parabolicHomeomorph.symm q) i j j) *
        (χ q.2 * ψ q.1 i)) ν := by
    have h1 : Integrable (fun q : Vec3 × ℝ => ∑ i : Fin 3, ∑ j : Fin 3,
        D2u (parabolicHomeomorph.symm q) i j j * (χ q.2 * ψ q.1 i)) ν :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iL i j
    refine h1.congr (Eventually.of_forall fun q => ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
  rw [lps_integral_sub_sub hTs hBs hLs,
    integral_finsetSum _ fun i _ => iT i,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iB i j]
  have hLsum : (∫ q : Vec3 × ℝ, ∑ i : Fin 3, (∑ j : Fin 3, D2u (parabolicHomeomorph.symm q) i j j) *
        (χ q.2 * ψ q.1 i) ∂ν) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ q : Vec3 × ℝ,
        D2u (parabolicHomeomorph.symm q) i j j * (χ q.2 * ψ q.1 i) ∂ν := by
    have : (fun q : Vec3 × ℝ => ∑ i : Fin 3, (∑ j : Fin 3, D2u (parabolicHomeomorph.symm q) i j j) *
        (χ q.2 * ψ q.1 i)) = fun q => ∑ i : Fin 3, ∑ j : Fin 3,
          D2u (parabolicHomeomorph.symm q) i j j * (χ q.2 * ψ q.1 i) := by
      funext q
      exact Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
    rw [this, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iL i j]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => iL i j
  rw [hLsum]
  simp only [integral_finsetSum _ fun j _ => iB _ j]
  linarith only [hEq']

end ESS

end
