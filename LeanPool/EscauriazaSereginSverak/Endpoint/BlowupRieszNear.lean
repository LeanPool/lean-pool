/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureAssembly
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSpaceTimeLp

public section

open CKN

open MeasureTheory Filter CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS


/-- Strong `L^(3/2)` convergence of all nine tensor components gives strong
convergence of their whole-space pressures. This is the near-field step of
`prop:blowup-limit` after restricting the tensors to a fixed ball. -/
theorem blowup_rieszPressureSpaceTime_tendsto_of_tensor
    (F : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ k i j, MemLp (F k i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (hconv : ∀ i j, Tendsto
      (fun k => eLpNorm (fun z => F k i j z - G i j z)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume : Measure (Vec3 × ℝ))) atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm
      (fun z => CKN.Leray.rieszPressureSpaceTime (3 / 2) (by norm_num)
          (F k) (hF k) z -
        CKN.Leray.rieszPressureSpaceTime (3 / 2) (by norm_num)
          G hG z)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
  let : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
  let P : ℕ → Vec3 × ℝ → ℝ := fun k =>
    CKN.Leray.rieszPressureSpaceTime (3 / 2) (by norm_num) (F k) (hF k)
  let Q : Vec3 × ℝ → ℝ :=
    CKN.Leray.rieszPressureSpaceTime (3 / 2) (by norm_num) G hG
  have hP (k : ℕ) : MemLp (P k) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) :=
    CKN.Leray.rieszPressureSpaceTime_memLp (3 / 2) (by norm_num) (F k) (hF k)
  have hQ : MemLp Q (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) :=
    CKN.Leray.rieszPressureSpaceTime_memLp (3 / 2) (by norm_num) G hG
  have hinput (i j : Fin 3) : Tendsto
      (fun k => (hF k i j).toLp (F k i j)) atTop
      (nhds ((hG i j).toLp (G i j))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hfinite (k : ℕ) :
        eLpNorm (fun z => F k i j z - G i j z)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume : Measure (Vec3 × ℝ)) ≠ ⊤ :=
      ((hF k i j).sub (hG i j)).eLpNorm_ne_top
    have hreal := (ENNReal.tendsto_toReal_zero_iff hfinite).2 (hconv i j)
    convert hreal using 1
    ext k
    rw [← MemLp.toLp_sub (hF k i j) (hG i j), Lp.norm_toLp]
    congr 2
  have hclass : Tendsto (fun k =>
      CKN.Leray.rieszPressureSpaceTimeClass (3 / 2) (by norm_num)
        (CKN.Leray.rieszPressureSpaceTimeTensorToLp (3 / 2) (by norm_num)
          (F k) (hF k))) atTop
      (nhds (CKN.Leray.rieszPressureSpaceTimeClass (3 / 2) (by norm_num)
        (CKN.Leray.rieszPressureSpaceTimeTensorToLp (3 / 2) (by norm_num)
          G hG))) := by
    unfold CKN.Leray.rieszPressureSpaceTimeClass
    apply tendsto_finsetSum Finset.univ
    intro i hi
    apply tendsto_finsetSum Finset.univ
    intro j hj
    exact (CKN.Leray.rieszPressureSpaceTimeComponent
      (3 / 2) (by norm_num) i j).continuous.continuousAt.tendsto.comp (hinput i j)
  have hclassEqP (k : ℕ) :
      (hP k).toLp (P k) =
        CKN.Leray.rieszPressureSpaceTimeClass (3 / 2) (by norm_num)
          (CKN.Leray.rieszPressureSpaceTimeTensorToLp (3 / 2) (by norm_num)
            (F k) (hF k)) := by
    apply Lp.ext
    filter_upwards [(hP k).coeFn_toLp,
      (Lp.aestronglyMeasurable (CKN.Leray.rieszPressureSpaceTimeClass
        (3 / 2) (by norm_num)
        (CKN.Leray.rieszPressureSpaceTimeTensorToLp (3 / 2) (by norm_num)
          (F k) (hF k)))).aemeasurable.ae_eq_mk] with z hz hmk
    exact hz.trans hmk.symm
  have hclassEqQ :
      hQ.toLp Q =
        CKN.Leray.rieszPressureSpaceTimeClass (3 / 2) (by norm_num)
          (CKN.Leray.rieszPressureSpaceTimeTensorToLp (3 / 2) (by norm_num)
            G hG) := by
    apply Lp.ext
    filter_upwards [hQ.coeFn_toLp,
      (Lp.aestronglyMeasurable (CKN.Leray.rieszPressureSpaceTimeClass
        (3 / 2) (by norm_num)
        (CKN.Leray.rieszPressureSpaceTimeTensorToLp (3 / 2) (by norm_num)
          G hG))).aemeasurable.ae_eq_mk] with z hz hmk
    exact hz.trans hmk.symm
  have hout : Tendsto (fun k => (hP k).toLp (P k)) atTop
      (nhds (hQ.toLp Q)) := by
    simpa only [hclassEqP, hclassEqQ] using hclass
  have hnorm : Tendsto (fun k =>
      ‖(hP k).toLp (P k) - hQ.toLp Q‖) atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hout
  have hfinite (k : ℕ) : eLpNorm (fun z => P k z - Q z)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) ≠ ⊤ :=
    ((hP k).sub hQ).eLpNorm_ne_top
  have hnorm' : Tendsto (fun k =>
      (eLpNorm (fun z => P k z - Q z)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume : Measure (Vec3 × ℝ))).toReal) atTop (nhds 0) := by
    convert hnorm using 1
    ext k
    rw [← MemLp.toLp_sub (hP k) hQ, Lp.norm_toLp]
    congr 2
  have hfinal := (ENNReal.tendsto_toReal_zero_iff hfinite).1 hnorm'
  simpa only [P, Q] using hfinal

/-- Strong local `L³` velocity convergence controls the pressure of the
tensor truncated to a fixed measurable space-time region. -/
theorem blowup_rieszPressureSpaceTime_near_tendsto
    (C : Set (Vec3 × ℝ)) (hC : MeasurableSet C)
    (v : ℕ → Vec3 × ℝ → Vec3) (u : Vec3 × ℝ → Vec3)
    (hu : MemLp u 3 (volume.restrict C))
    (hv : ∀ k, MemLp (v k) 3 (volume.restrict C))
    (hconv : Tendsto (fun k => eLpNorm (fun z => v k z - u z)
      3 (volume.restrict C)) atTop (nhds 0))
    (hbound : ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ k, eLpNorm (v k) 3 (volume.restrict C) ≤ B) :
    let F : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
      fun k i j => C.indicator (fun z => v k z i * v k z j)
    let G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
      fun i j => C.indicator (fun z => u z i * u z j)
    ∃ (hF : ∀ k i j, MemLp (F k i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
      (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume),
      Tendsto (fun k => eLpNorm
        (fun z => CKN.Leray.rieszPressureSpaceTime (3 / 2) (by norm_num)
            (F k) (hF k) z -
          CKN.Leray.rieszPressureSpaceTime (3 / 2) (by norm_num)
            G hG z)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume) atTop (nhds 0) := by
  let F : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
    fun k i j => C.indicator (fun z => v k z i * v k z j)
  let G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
    fun i j => C.indicator (fun z => u z i * u z j)
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hthree : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by norm_num
  have : (3 : ℝ≥0∞).HolderTriple 3 (3 / 2 : ℝ≥0∞) := by
    have h : (3 : ℝ).HolderTriple 3 (3 / 2 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    simpa only [hcoeff, hthree] using h.ennrealOfReal
  have hcomp (w : Vec3 × ℝ → Vec3)
      (hw : MemLp w 3 (volume.restrict C)) (i : Fin 3) :
      MemLp (fun z => w z i) 3 (volume.restrict C) :=
    hw.of_le ((continuous_apply i).comp_aestronglyMeasurable
      hw.aestronglyMeasurable)
      (Eventually.of_forall fun z => norm_le_pi_norm (w z) i)
  have hF : ∀ k i j, MemLp (F k i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    intro k i j
    rw [hcoeff]
    change MemLp (C.indicator (fun z => v k z i * v k z j))
      (3 / 2 : ℝ≥0∞) volume
    rw [memLp_indicator_iff_restrict hC]
    convert (hcomp (v k) (hv k) i).mul (hcomp (v k) (hv k) j) using 1
    exact this
  have hG : ∀ i j, MemLp (G i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    intro i j
    rw [hcoeff]
    change MemLp (C.indicator (fun z => u z i * u z j))
      (3 / 2 : ℝ≥0∞) volume
    rw [memLp_indicator_iff_restrict hC]
    convert (hcomp u hu i).mul (hcomp u hu j) using 1
    exact this
  have htensor (i j : Fin 3) : Tendsto
      (fun k => eLpNorm (fun z => F k i j z - G i j z)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume) atTop (nhds 0) := by
    have h := blowup_tensor_component_tendsto_LthreeHalves
      (volume.restrict C) v u hu hv hconv hbound i j
    have heq (k : ℕ) :
        (fun z => F k i j z - G i j z) =
          C.indicator (fun z => v k z i * v k z j - u z i * u z j) := by
      funext z
      by_cases hz : z ∈ C
      · simp only [F, G, Set.indicator_of_mem hz]
      · simp only [F, G, Set.indicator_of_notMem hz, sub_self]
    convert h using 1
    ext k
    rw [heq k, hcoeff, eLpNorm_indicator_eq_eLpNorm_restrict hC]
  exact ⟨hF, hG,
    blowup_rieszPressureSpaceTime_tendsto_of_tensor F G hF hG htensor⟩

end ESS
