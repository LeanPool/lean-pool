/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitAux
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitPackage
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitRep
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongEquation
public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution

/-!
# The compactness limit is a strong solution

The compactness limit of the regularized solutions, with the continuous representative of its
gradient and the pressure of the Leray--Hopf limit, is a strong solution on the closed time interval
(`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The limit of the regularized solutions with uniform `H¹` and `L²_tH²` bounds is a strong
solution on `[0, T]` with the good initial datum as trace (`prop:lps-local-strong`). -/
theorem lps_strong_limit_solution
    (ρ : CKN.Leray.RegMollifierProfile)
    (b : Vec3 → Vec3) (Db : Vec3 → Fin 3 → Vec3)
    (hb : ESS.IsLpsGoodTime (fun z : ParabolicPoint => b z.1) (fun z i => Db z.1 i) 0)
    (T M : ℝ) (hT : 0 < T)
    (hclause : ∀ (ε : ℝ) (hε : 0 < ε),
        let Uε : ParabolicPoint → Vec3 :=
          CKN.Leray.regR12Velocity ρ ε hε b (by simpa using hb.2)
        let Dε : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
          spatialPartial (fun y => Uε y i) j z
        let D2ε : ParabolicPoint → Fin 3 → Fin 3 → Vec3 :=
          fun z i j k =>
            spatialPartial
              (fun y => spatialPartial (fun x => Uε x i) j y) k z
        (∀ t : ℝ, t ∈ Icc 0 T →
          ∫ x : Vec3,
            vec3EuclideanNorm (Uε (x, t)) ^ (2 : ℕ) +
              spatialGradientSq Uε Dε (x, t) ≤ M) ∧
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          ∑ i : Fin 3, ∑ j : Fin 3,
            vec3EuclideanNorm (D2ε z i j) ^ (2 : ℕ) ≤ M) :
    ∃ (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ),
      ESS.IsLpsStrongSolution 0 T u Du p ∧ (fun x : Vec3 => u (x, 0)) =ᵐ[volume] b := by
  classical
  have hb' : (∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
        h.toFun = (fun x : Vec3 => b x i) ∧ h.grad = (fun x : Vec3 => Db x i)) ∧ CKN.IsInJ b :=
    ⟨hb.1, by simpa using hb.2⟩
  have hM : 0 ≤ M := by
    have h0 := (hclause 1 one_pos).1 0 ⟨le_rfl, hT.le⟩
    refine le_trans (integral_nonneg fun x => ?_) h0
    exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      sq_nonneg _)
  obtain ⟨σ₀, hσ₀, u, Du, D2u, Dtu, htrace, hLH, hDerivs, huMem, hDuMem, hD2mem, hDtmem,
    hweakSlice, hrep⟩ := lps_strong_limit_weak_derivatives ρ b Db hb' T M hT hM hclause
  -- every slice is in `H¹ ∩ J`
  obtain ⟨Dpositive, hpos⟩ := lps_strong_limit_all_time_h1_slices ρ b Db hb' T M hT hM hclause
    σ₀ hσ₀ hweakSlice hrep
  obtain ⟨Dslice, hgood, -⟩ := lps_strong_limit_h1_slices_closed hb' htrace
    (9 * ENNReal.ofReal (Real.sqrt M)) Dpositive hpos
  -- continuous curves for the velocity and its gradient
  obtain ⟨Lu, LD, hLuc, hLDc, hLuq, hLDq, -, -⟩ := lps_strong_time_regularity (t₀ := 0) (T := T)
    hT hDerivs huMem hDuMem hD2mem hDtmem
  have hweakc : ∀ (i : Fin 3) (w : Vec3 → ℝ), MemLp w 2 volume →
      ContinuousOn (fun t : ℝ => ∫ x, u (x, t) i * w x) (Icc 0 T) := fun i w hw =>
    lps_weak_continuity_scalar hLH.2.2.2.2.2.2.2.2.1 i w hw
  have hLu_all : ∀ i : Fin 3, ∀ (t : ℝ) (ht : t ∈ Icc 0 T),
      ((Lu i ⟨t, ht⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
        fun x => u (x, t) i := fun i =>
    lps_curve_eq_of_weak_continuous hT (F := fun z : Vec3 × ℝ => u z i) (hLuc i) (hLuq i)
      (fun t ht => lps_goodTime_memLp (hgood t ht) i) (hweakc i)
  -- a jointly measurable representative of the gradient curve
  choose f hfm hfrep using fun i j : Fin 3 => lps_curve_measurable_rep hT.le (hLDc i j)
  let Du' : ParabolicPoint → Fin 3 → Vec3 := fun z i j => f i j z
  have hslicesLD : ∀ i j : Fin 3, ∀ᵐ s ∂(volume.restrict (Ioo 0 T)),
      (fun x => f i j (x, s)) =ᵐ[volume] fun x => Du (x, s) i j := by
    intro i j
    filter_upwards [hLDq i j, ae_restrict_mem measurableSet_Ioo] with s hs hsI
    have hsI' := Ioo_subset_Icc_self hsI
    exact (hfrep i j s hsI').trans (hs hsI')
  have hDuComp : ∀ i j : Fin 3, AEStronglyMeasurable (fun z : Vec3 × ℝ => Du z i j)
      (volume.restrict (vlSlab 0 T)) := fun i j =>
    ((memLp_pi_iff.1 ((memLp_pi_iff.1 hDuMem) i)) j).aestronglyMeasurable
  have hae_comp : ∀ i j : Fin 3, (fun z : Vec3 × ℝ => f i j z) =ᵐ[volume.restrict (vlSlab 0 T)]
      fun z => Du z i j := fun i j =>
    lps_slab_ae_eq_of_slices (hfm i j).aestronglyMeasurable (hDuComp i j) (hslicesLD i j)
  have hae : Du' =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] Du := by
    have h := ae_all_iff.2 fun i : Fin 3 => ae_all_iff.2 fun j : Fin 3 => hae_comp i j
    filter_upwards [h] with z hz
    funext i j
    exact hz i j
  have hDu'mem : MemLp Du' 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    (memLp_congr_ae hae).2 hDuMem
  -- weak gradient of every slice
  have hslice_u := hLH.2.2.2.2.2.2.1
  have hweakAll : ∀ i j : Fin 3, ∀ t ∈ Icc 0 T,
      HasWeakPartialDerivOn (Set.univ : Set Vec3) j (fun x => u (x, t) i)
        (fun x => f i j (x, t)) := by
    intro i j
    refine lps_weak_partial_all_times hT j (F := fun z : Vec3 × ℝ => u z i)
      (G := fun z : Vec3 × ℝ => f i j z) (hLDc i j) (fun t ht => (hfrep i j t ht).symm)
      (hweakc i) ?_
    filter_upwards [hslice_u, hslicesLD i j] with t h1 h2
    intro φ hφ hφc hsub
    have h1' := h1 i j φ hφ hφc hsub
    simp only [Measure.restrict_univ] at h1' ⊢
    rw [h1']
    congr 1
    exact integral_congr_ae (h2.mono fun x hx => by
      change Du (x, t) i j * φ x = f i j (x, t) * φ x
      rw [show f i j (x, t) = Du (x, t) i j from hx])
  have hH1 : ∀ t ∈ Icc 0 T, ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x : Vec3 => u (x, t) i) ∧ h.grad = (fun x : Vec3 => Du' (x, t) i) := by
    intro t ht i
    obtain ⟨h0, hfun0, -⟩ := (hgood t ht).1 i
    refine ⟨{ toFun := fun x => u (x, t) i
              grad := fun x => Du' (x, t) i
              memL2 := ?_
              gradMemL2 := ?_
              hasWeakGradient := fun j => hweakAll i j t ht }, rfl, rfl⟩
    · have := h0.memL2
      rw [hfun0] at this
      exact this
    · intro j
      have hm : MemLp (fun x : Vec3 => f i j (x, t)) 2 volume :=
        (Lp.memLp (LD i j ⟨t, ht⟩)).ae_eq (hfrep i j t ht).symm
      simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using hm
  -- continuity of the slices
  have hcont : ∀ t ∈ Icc 0 T,
      Tendsto (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
        (nhdsWithin t (Icc 0 T)) (𝓝 0) ∧
      Tendsto (fun s : ℝ => eLpNorm (fun x : Vec3 => Du' (x, s) - Du' (x, t)) 2 volume)
        (nhdsWithin t (Icc 0 T)) (𝓝 0) := by
    intro t ht
    constructor
    · refine lps_vec3_norm_tendsto (v := fun s x => u (x, s) - u (x, t)) ?_ ?_
      · intro s hs
        exact memLp_pi_iff.2 fun i =>
          (lps_goodTime_memLp (hgood s hs) i).sub (lps_goodTime_memLp (hgood t ht) i)
      · intro i
        exact lps_curve_slices_tendsto hT (F := fun z : Vec3 × ℝ => u z i) (hLuc i)
          (hLu_all i) ht
    · refine lps_matrix_norm_tendsto (v := fun s x => Du' (x, s) - Du' (x, t)) ?_ ?_
      · intro s hs
        refine memLp_pi_iff.2 fun i => memLp_pi_iff.2 fun j => ?_
        have h1 : MemLp (fun x : Vec3 => f i j (x, s)) 2 volume :=
          (Lp.memLp (LD i j ⟨s, hs⟩)).ae_eq (hfrep i j s hs).symm
        have h2 : MemLp (fun x : Vec3 => f i j (x, t)) 2 volume :=
          (Lp.memLp (LD i j ⟨t, ht⟩)).ae_eq (hfrep i j t ht).symm
        exact h1.sub h2
      · intro i j
        exact lps_curve_slices_tendsto hT (F := fun z : Vec3 × ℝ => f i j z) (hLDc i j)
          (fun t' ht' => (hfrep i j t' ht').symm) ht
  -- the pressure and the equation
  obtain ⟨hpmem, heq⟩ := lps_strong_limit_pressure_equation ρ b Db hb' T M hT hM hclause σ₀ hσ₀
    hweakSlice hrep hLH
  refine ⟨u, Du', CKN.Leray.associatedPressureForSolution hLH,
    ⟨hT, fun t ht => ⟨(hgood t ht).2, hH1 t ht⟩, hcont,
      ⟨D2u, Dtu, lps_hasSpaceTimeWeakDerivs_congr_grad hDerivs hae.symm hDu'mem, huMem, hDu'mem,
        hD2mem, hDtmem⟩, hpmem, fun φ hφ => ?_⟩, Eventually.of_forall fun x => htrace x⟩
  refine Eq.trans (integral_congr_ae ?_) (heq φ hφ)
  filter_upwards [hae] with z hz
  simp only [hz]

end ESS.LPS

end
