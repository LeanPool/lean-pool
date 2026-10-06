/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSourceSlice
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLerayApply
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpace

/-!
# The projected equation on almost every time slice

`prop:lps-smoothing`: for a strong solution, at almost every time `t` the field
`G(t) = (∂ₜu - Δu)(t)` is weakly divergence free, and `G(t) + ((u·∇)u)(t)` is the gradient
of the pressure slice up to sign. Applying the Leray projection `P` gives
`G(t) = -P((u·∇)u)(t)`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The Leray projection of a sum of fields is the sum of the projections
(`prop:lps-smoothing`). -/
theorem lpsLerayApply_add {g h : Fin 3 → Vec3 → ℝ} (hg : ∀ j, MemLp (g j) 2 volume)
    (hh : ∀ j, MemLp (h j) 2 volume) (i : Fin 3) :
    lpsLerayApply (fun j x => g j x + h j x) (fun j => (hg j).add (hh j)) i =ᵐ[volume]
      fun x => lpsLerayApply g hg i x + lpsLerayApply h hh i x := by
  have hgh : ∀ j, MemLp (fun x => g j x + h j x) 2 volume := fun j => (hg j).add (hh j)
  rw [lpsLerayApply_eq hgh, lpsLerayApply_eq hg, lpsLerayApply_eq hh]
  have hsum : lpsFieldOf (fun j x => g j x + h j x) hgh = lpsFieldOf g hg + lpsFieldOf h hh := by
    refine PiLp.ext fun j => ?_
    simp only [lpsFieldOf, PiLp.add_apply]
    exact MemLp.toLp_add (hg j) (hh j)
  rw [hsum, map_add, PiLp.add_apply]
  exact Lp.coeFn_add _ _

/-- The time derivative of a strong solution is weakly divergence free on almost every
time slice. -/
private theorem lps_source_Dtu_div_ae {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hsol : IsLpsStrongSolution t₀ T u Du p)
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)))) :
    ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → ∑ i, ∫ x, Dtu (x, t) i * spatialDeriv φ i x = 0 := by
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo t₀ T))
    with hν
  have hslab : (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo t₀ T) : Measure (Vec3 × ℝ)) = ν :=
    lps_measure_slab_eq_prod t₀ T
  have hS : ∀ F : ParabolicPoint → ℝ,
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), F z = ∫ q, F q ∂ν := by
    intro F
    rw [← hslab]
    rfl
  have hdivfree := ESS.LPS.lps_strong_solution_div_free hsol
  -- the slice data: `none` carries nothing, `some k` carries the `k`-th component
  let A : ℝ → Option (Fin 3) → Vec3 → ℝ := fun t o => match o with
    | none => fun _ => 0
    | some k => fun x => Dtu (x, t) k
  have hptw : ∀ (φ : lpsScalarTests) (t : ℝ) (x : Vec3),
      ∑ o, A t o x * lpsScalarTestData φ o x =
        ∑ k, Dtu (x, t) k * spatialDeriv (φ : Vec3 → ℝ) k x := by
    intro φ t x
    rw [Fintype.sum_option]
    simp only [A, lpsScalarTestData, LinearMap.coe_mk, AddHom.coe_mk, zero_mul, zero_add]
  have hsingle : ∀ φ : lpsScalarTests, ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)),
      ∫ x, ∑ o, A t o x * lpsScalarTestData φ o x = 0 := by
    intro φ
    have hφ : ContDiff ℝ (⊤ : ℕ∞) (φ : Vec3 → ℝ) := φ.2.1
    have hφc : HasCompactSupport (φ : Vec3 → ℝ) := φ.2.2
    have hdφ (k : Fin 3) : MemLp (spatialDeriv (φ : Vec3 → ℝ) k) 2 volume :=
      (contDiff_spatialDeriv_smooth hφ k).continuous.memLp_of_hasCompactSupport
        (hφc.fderiv_apply (𝕜 := ℝ) (basisVec k))
    have hzero : ∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
        tsupport χ ⊆ Ioo t₀ T →
        ∫ t in Ioo t₀ T, χ t * ∫ x, ∑ k, Dtu (x, t) k * spatialDeriv (φ : Vec3 → ℝ) k x = 0 := by
      intro χ hχ hχc hχs
      have hχ' : ContDiff ℝ (⊤ : ℕ∞) (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
      have hχ'c : HasCompactSupport (deriv χ) := hχc.deriv
      have hχ's : tsupport (deriv χ) ⊆ Ioo t₀ T := tsupport_deriv_subset.trans hχs
      obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hχc
      obtain ⟨C', hC'⟩ := hχ'.continuous.bounded_above_of_compact_support hχ'c
      -- the space-time identity for each component
      have hcomp (k : Fin 3) :
          ∫ q, Dtu q k * (χ q.2 * spatialDeriv (φ : Vec3 → ℝ) k q.1) ∂ν =
            ∫ q, Du q k k * (deriv χ q.2 * (φ : Vec3 → ℝ) q.1) ∂ν := by
        have hT := (hderiv.2.2.2.2 _ (lps_separated_test_mem hχ hχc hχs
          (contDiff_spatialDeriv_smooth hφ k) (hφc.fderiv_apply (𝕜 := ℝ) (basisVec k)))).2.2 k
        have hX := (hderiv.2.2.2.2 _ (lps_separated_test_mem hχ' hχ'c hχ's hφ hφc)).1 k k
        rw [hS, hS] at hT hX
        have hT' : ∫ q, u q k * (deriv χ q.2 * spatialDeriv (φ : Vec3 → ℝ) k q.1) ∂ν =
            -∫ q, Dtu q k * (χ q.2 * spatialDeriv (φ : Vec3 → ℝ) k q.1) ∂ν := by
          rw [← hT]
          refine integral_congr_ae (Eventually.of_forall fun q => ?_)
          exact congrArg (fun a => u q k * a)
            (lps_separated_timePartial (f := spatialDeriv (φ : Vec3 → ℝ) k) hχ q).symm
        have hX' : ∫ q, u q k * (deriv χ q.2 * spatialDeriv (φ : Vec3 → ℝ) k q.1) ∂ν =
            -∫ q, Du q k k * (deriv χ q.2 * (φ : Vec3 → ℝ) q.1) ∂ν := by
          rw [← hX]
          refine integral_congr_ae (Eventually.of_forall fun q => ?_)
          exact congrArg (fun a => u q k * a)
            (lps_separated_spatialPartial (χ := deriv χ) hφ k q).symm
        linarith only [hT', hX']
      have hφ2 : MemLp (φ : Vec3 → ℝ) 2 volume := hφ.continuous.memLp_of_hasCompactSupport hφc
      have iDt (k : Fin 3) : Integrable
          (fun q : Vec3 × ℝ => Dtu q k * spatialDeriv (φ : Vec3 → ℝ) k q.1) ν := by
        rw [← hslab]; exact (hDtu.eval k).integrable_mul (lps_memLp_slab_of_space (hdφ k))
      have iDu (k : Fin 3) : Integrable (fun q : Vec3 × ℝ => Du q k k * (φ : Vec3 → ℝ) q.1) ν := by
        rw [← hslab]
        exact ((hDu.eval k).eval k).integrable_mul (lps_memLp_slab_of_space hφ2)
      have iDt' (k : Fin 3) : Integrable
          (fun q : Vec3 × ℝ => Dtu q k * (χ q.2 * spatialDeriv (φ : Vec3 → ℝ) k q.1)) ν := by
        have := (iDt k).bdd_mul (f := fun q : Vec3 × ℝ => χ q.2) (c := C)
          ((hχ.continuous.comp continuous_snd).aestronglyMeasurable)
          (Eventually.of_forall fun q => hC q.2)
        refine this.congr (Eventually.of_forall fun q => ?_)
        simp only
        ring
      have iDu' (k : Fin 3) : Integrable
          (fun q : Vec3 × ℝ => Du q k k * (deriv χ q.2 * (φ : Vec3 → ℝ) q.1)) ν := by
        have := (iDu k).bdd_mul (f := fun q : Vec3 × ℝ => deriv χ q.2) (c := C')
          ((hχ'.continuous.comp continuous_snd).aestronglyMeasurable)
          (Eventually.of_forall fun q => hC' q.2)
        refine this.congr (Eventually.of_forall fun q => ?_)
        simp only
        ring
      -- the divergence of `u` vanishes almost everywhere on the slab
      have hdiv0 : ∫ q, ∑ k, Du q k k * (deriv χ q.2 * (φ : Vec3 → ℝ) q.1) ∂ν = 0 := by
        have hdiv' : ∀ᵐ q ∂ν, ∑ k, Du q k k = 0 := by
          rw [← hslab]
          exact hdivfree
        rw [integral_eq_zero_of_ae]
        filter_upwards [hdiv'] with q hq
        rw [← Finset.sum_mul, hq, zero_mul]
        rfl
      rw [integral_finsetSum _ fun k _ => iDu' k] at hdiv0
      have hsum : ∫ q, χ q.2 * ∑ k, Dtu q k * spatialDeriv (φ : Vec3 → ℝ) k q.1 ∂ν = 0 := by
        have heq : (fun q : Vec3 × ℝ => χ q.2 * ∑ k, Dtu q k * spatialDeriv (φ : Vec3 → ℝ) k q.1) =
            fun q : Vec3 × ℝ => ∑ k, Dtu q k * (χ q.2 * spatialDeriv (φ : Vec3 → ℝ) k q.1) := by
          funext q
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [heq, integral_finsetSum _ fun k _ => iDt' k]
        simp only [hcomp]
        exact hdiv0
      have hmul : Integrable
          (fun q : Vec3 × ℝ => χ q.2 * ∑ k, Dtu q k * spatialDeriv (φ : Vec3 → ℝ) k q.1) ν :=
        (integrable_finsetSum _ fun k _ => iDt k).bdd_mul (f := fun q : Vec3 × ℝ => χ q.2)
          (c := C) ((hχ.continuous.comp continuous_snd).aestronglyMeasurable)
          (Eventually.of_forall fun q => hC q.2)
      rw [integral_prod_symm _ hmul] at hsum
      simpa [integral_const_mul] using hsum
    have h := lps_ae_slice_test_single (fun k (z : Vec3 × ℝ) => Dtu z k)
      (fun k => hDtu.eval k) (fun k => spatialDeriv (φ : Vec3 → ℝ) k) hdφ hzero
    filter_upwards [h] with t ht
    rw [← ht]
    exact integral_congr_ae (Eventually.of_forall fun x => hptw φ t x)
  have hslices : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ o, MemLp (A t o) 2 volume := by
    filter_upwards [lps_slice_memLp_two_ae_slab hDtu] with t ht o
    cases o with
    | none => exact MemLp.zero
    | some k => exact ht.eval k
  filter_upwards [lps_ae_forall_test_of_forall_ae A hslices lpsScalarTestData
    lpsScalarTestData_memLp hsingle, lps_slice_memLp_two_ae_slab hDtu] with t ht hDt φ hφ hφc
  have h0 := ht ⟨φ, hφ, hφc⟩
  simp only [hptw] at h0
  have hdφ (k : Fin 3) : MemLp (spatialDeriv φ k) 2 volume :=
    (contDiff_spatialDeriv_smooth hφ k).continuous.memLp_of_hasCompactSupport
      (hφc.fderiv_apply (𝕜 := ℝ) (basisVec k))
  have iDk : ∀ k : Fin 3, Integrable (fun x : Vec3 => Dtu (x, t) k * spatialDeriv φ k x)
      volume := fun k => (hDt.eval k).integrable_mul (hdφ k)
  rw [← integral_finsetSum _ fun k _ => iDk k]
  exact h0

/-- `prop:lps-smoothing`: the projected equation on almost every time slice. For almost every
time `t`, `(∂ₜu - Δu)(t) = -P((u·∇)u)(t)` almost everywhere on `ℝ³`, where `Δu = Σⱼ ∂ⱼ∂ⱼu`,
`((u·∇)u)ᵢ = Σⱼ uⱼ ∂ⱼuᵢ` and `P` is the Leray projection `lpsLerayP` acting through
`lpsLerayApply`. -/
theorem lps_strong_slice_projected_equation {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hsol : IsLpsStrongSolution t₀ T u Du p)
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)))) :
    ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ i
      (hconv : ∀ i', MemLp (fun y => ∑ j, u (y, t) j * Du (y, t) i' j) 2 volume),
      (fun x => Dtu (x, t) i - ∑ j, D2u (x, t) i j j) =ᵐ[volume]
        fun x => -lpsLerayApply (fun i' y => ∑ j, u (y, t) j * Du (y, t) i' j) hconv i x := by
  filter_upwards [lps_strong_slice_pressure_equation hsol hderiv hu hDu hD2u hDtu,
    lps_source_Dtu_div_ae hsol hderiv hDu hDtu,
    lps_strong_good_slices hsol hderiv hu hDu hD2u hDtu,
    ae_restrict_mem measurableSet_Ioo] with t hpres hdiv hgood htI
  obtain ⟨Gq, hGq2, hp2, hpw, hsum⟩ := hpres
  obtain ⟨hDt, hD2, hgrad, -⟩ := hgood
  have htIcc : t ∈ Icc t₀ T := ⟨htI.1.le, htI.2.le⟩
  obtain ⟨hu2t, hDu2t⟩ := lps_strong_solution_slice_memLp_two hsol htIcc
  have hH1t := (lps_strong_solution_slice_h1 hsol htIcc).2.2
  have hgu := lps_strong_solution_slice_weak_gradient hsol htIcc
  have hJ : IsInJ (fun x : Vec3 => u (x, t)) := (hsol.2.1 t htIcc).1
  let G : Fin 3 → Vec3 → ℝ := fun i x => Dtu (x, t) i - ∑ j, D2u (x, t) i j j
  let B : Fin 3 → Vec3 → ℝ := fun i x => ∑ j, u (x, t) j * Du (x, t) i j
  have hL2 : ∀ i, MemLp (fun x => ∑ j, D2u (x, t) i j j) 2 volume := fun i =>
    memLp_finsetSum Finset.univ fun j _ => ((hD2.eval i).eval j).eval j
  have hG2 : ∀ i, MemLp (G i) 2 volume := fun i => (hDt.eval i).sub (hL2 i)
  have hB2 : ∀ i, MemLp (B i) 2 volume := fun i =>
    lps_h1_convection_memLp_two (u := fun x => u (x, t)) (Du := fun x => Du (x, t))
      (D2u := fun x => D2u (x, t)) hu2t hDu2t hD2 hH1t hgrad i
  -- `G(t)` is weakly divergence free
  have hLap := lps_h1_laplacian_weak_div_free (u := fun x => u (x, t))
    (Du := fun x => Du (x, t)) (D2u := fun x => D2u (x, t)) hu2t hDu2t hD2 hgu hgrad
    (isInJ_weakDivFree hJ).2
  have hGdiv : ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∑ i, ∫ x, G i x * spatialDeriv φ i x = 0 := by
    intro φ hφ hφc
    have hdφ (k : Fin 3) : MemLp (spatialDeriv φ k) 2 volume :=
      (contDiff_spatialDeriv_smooth hφ k).continuous.memLp_of_hasCompactSupport
        (hφc.fderiv_apply (𝕜 := ℝ) (basisVec k))
    have h1 := hdiv φ hφ hφc
    have h2 := hLap.2 ⟨φ, hφ, hφc, subset_univ _⟩
    have iL : ∀ i : Fin 3, Integrable
        (fun x : Vec3 => (∑ j, D2u (x, t) i j j) * spatialDeriv φ i x) volume :=
      fun i => (hL2 i).integrable_mul (hdφ i)
    have iD : ∀ i : Fin 3, Integrable (fun x : Vec3 => Dtu (x, t) i * spatialDeriv φ i x)
        volume := fun i => (hDt.eval i).integrable_mul (hdφ i)
    have h2' : ∑ i, ∫ x, (∑ j, D2u (x, t) i j j) * spatialDeriv φ i x = 0 := by
      rw [← integral_finsetSum _ fun i _ => iL i]
      exact h2
    calc ∑ i, ∫ x, G i x * spatialDeriv φ i x
        = ∑ i, ((∫ x, Dtu (x, t) i * spatialDeriv φ i x) -
            ∫ x, (∑ j, D2u (x, t) i j j) * spatialDeriv φ i x) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← integral_sub (iD i) (iL i)]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [G]
          ring
      _ = 0 := by rw [Finset.sum_sub_distrib, h1, h2', sub_zero]
  have hPG : ∀ i, lpsLerayApply G hG2 i =ᵐ[volume] G i := lpsLerayApply_eq_self hG2 hGdiv
  -- `G(t) + B(t)` is the weak gradient of `-p(t)`
  have hnegp : ∀ i, HasWeakPartialDerivOn (Set.univ : Set Vec3) i (fun x => -p (x, t))
      (fun x => G i x + B i x) := by
    intro i φ hφ hφc hφs
    have h := hpw i φ hφ hφc hφs
    have hae : (fun x => (G i x + B i x) * φ x) =ᵐ[volume] fun x => -Gq i x * φ x := by
      filter_upwards [hsum] with x hx
      have hxi := hx i
      have : G i x + B i x = -Gq i x := by
        simp only [G, B]
        linarith only [hxi]
      rw [this]
    simp only [Measure.restrict_univ] at h ⊢
    rw [integral_congr_ae hae]
    simp only [neg_mul, integral_neg, neg_neg]
    rw [h, neg_neg]
  have hPGB : ∀ i, lpsLerayApply (fun j x => G j x + B j x) (fun j => (hG2 j).add (hB2 j)) i
      =ᵐ[volume] 0 :=
    lpsLerayApply_gradient (fun j => (hG2 j).add (hB2 j)) hp2.neg hnegp
  intro i hconv
  filter_upwards [hPG i, hPGB i, lpsLerayApply_add hG2 hB2 i] with x h1 h2 h3
  have h3' := h3.symm.trans h2
  simp only [Pi.zero_apply] at h3'
  change G i x = -lpsLerayApply B hB2 i x
  linarith only [h1, h3']

end ESS
