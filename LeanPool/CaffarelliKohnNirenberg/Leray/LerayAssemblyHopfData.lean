/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.Data
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.LocalBox
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Leray.PressureLimitLeray
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureSolenoidalCore
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureSolenoidalTimeLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureSolenoidalPairings
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityDivergenceSupport

/-!
# Leray Assembly Hopf Data

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Pull back finite-slab pressure integrability from product coordinates to
CKN's parabolic-point coordinates. -/
theorem lerayAssembly_productSlab_memLp_to_parabolic
    {T : ℝ} {f : ParabolicPoint → ℝ} {r : ℝ≥0∞}
    (hf : MemLp (fun z : Vec3 × ℝ => f (parabolicHomeomorph.symm z)) r
      ((volume : Measure (Vec3 × ℝ)).restrict
        (lerayPressureLimitSlab T))) :
    MemLp f r
      (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  have hQ : MeasurableSet (lerayPressureLimitSlab T) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hpre : parabolicHomeomorph ⁻¹' lerayPressureLimitSlab T =
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
    ext z
    rfl
  have hmap := CKN.parabolicHomeomorph_measurePreserving.restrict_preimage hQ
  rw [hpre] at hmap
  have h := hf.comp_measurePreserving hmap
  change MemLp
    (fun z : ParabolicPoint =>
      f (parabolicHomeomorph.symm (parabolicHomeomorph z))) r
    (volume.restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) at h
  have heq :
      (fun z : ParabolicPoint =>
        f (parabolicHomeomorph.symm (parabolicHomeomorph z))) = f := by
    funext z
    exact congrArg f (parabolicHomeomorph.symm_apply_apply z)
  rw [heq] at h
  exact h

/-- Strong pressure convergence on the product slab restricts to, and agrees
with, convergence on a compact parabolic test box. -/
theorem lerayAssembly_pressureConv_localBox
    {Ω' : Set Vec3} {J : Set ℝ} {T : ℝ}
    (hbox : CKN.localBox (Set.univ : Set Vec3) (Ioi 0) Ω' J)
    (hJT : J ⊆ Ioo 0 T)
    (pseq : ℕ → ParabolicPoint → ℝ) (p : ParabolicPoint → ℝ)
    (hpseq : ∀ n, MemLp (pseq n) 2
      (volume.restrict (spaceTimeSet Ω' J)))
    (hp : MemLp (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z))
      (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict
        (lerayPressureLimitSlab T)))
    (hconv : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        pseq n (parabolicHomeomorph.symm z) - p (parabolicHomeomorph.symm z))
      (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict
        (lerayPressureLimitSlab T))) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (pseq n - p) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0) := by
  let Q : Set ParabolicPoint := spaceTimeSet Ω' J
  let Qprod : Set (Vec3 × ℝ) := Ω' ×ˢ J
  let μ : Measure ParabolicPoint := volume.restrict Q
  let ν : Measure (Vec3 × ℝ) := (volume : Measure (Vec3 × ℝ)).restrict Qprod
  let νT : Measure (Vec3 × ℝ) := (volume : Measure (Vec3 × ℝ)).restrict
    (lerayPressureLimitSlab T)
  have hQmeas : MeasurableSet Q := hbox.1.measurableSet.prod
    hbox.2.2.2.1.measurableSet
  have hQprodMeas : MeasurableSet Qprod := hbox.1.measurableSet.prod
    hbox.2.2.2.1.measurableSet
  have hQpre : parabolicHomeomorph ⁻¹' Qprod = Q := by
    ext z
    rfl
  have hQpreSymm : parabolicHomeomorph.symm ⁻¹' Q = Qprod := by
    ext z
    rfl
  have hmp := parabolicHomeomorph_measurePreserving.restrict_preimage hQprodMeas
  rw [hQpre] at hmp
  have hmpSymm :=
    CKN.parabolicHomeomorphSymm_measurePreserving.restrict_preimage hQmeas
  rw [hQpreSymm] at hmpSymm
  have hsubset : Qprod ⊆ lerayPressureLimitSlab T := by
    exact Set.prod_mono (Set.subset_univ _) hJT
  have hmeasureLE : ν ≤ νT := Measure.restrict_mono hsubset le_rfl
  have hseqProd (n : ℕ) : MemLp
      (fun z : Vec3 × ℝ => pseq n (parabolicHomeomorph.symm z)) 2 ν := by
    have h := (hpseq n).comp_measurePreserving hmpSymm
    change MemLp (fun z : Vec3 × ℝ =>
      pseq n (parabolicHomeomorph.symm z)) 2 ν
    exact h
  have hpProd : MemLp (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z))
      (ENNReal.ofReal (3 / 2 : ℝ)) ν := hp.mono_measure hmeasureLE
  have hbound (n : ℕ) : eLpNorm
      (fun z : Vec3 × ℝ =>
        pseq n (parabolicHomeomorph.symm z) - p (parabolicHomeomorph.symm z))
      (ENNReal.ofReal (3 / 2 : ℝ)) ν ≤ eLpNorm
        (fun z : Vec3 × ℝ =>
          pseq n (parabolicHomeomorph.symm z) - p (parabolicHomeomorph.symm z))
        (ENNReal.ofReal (3 / 2 : ℝ)) νT := by
    exact eLpNorm_mono_measure _ hmeasureLE
  have hconvProd : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        pseq n (parabolicHomeomorph.symm z) - p (parabolicHomeomorph.symm z))
      (ENNReal.ofReal (3 / 2 : ℝ)) ν) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hconv
      (Eventually.of_forall fun _ => bot_le)
      (Eventually.of_forall hbound)
  have hEq (n : ℕ) : eLpNorm (pseq n - p)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ = eLpNorm
        (fun z : Vec3 × ℝ =>
          pseq n (parabolicHomeomorph.symm z) - p (parabolicHomeomorph.symm z))
          (ENNReal.ofReal (3 / 2 : ℝ)) ν := by
    let g : Vec3 × ℝ → ℝ := fun z =>
      pseq n (parabolicHomeomorph.symm z) - p (parabolicHomeomorph.symm z)
    have hmeas : AEStronglyMeasurable g ν := (hseqProd n).aestronglyMeasurable.sub
      hpProd.aestronglyMeasurable
    have h := eLpNorm_comp_measurePreserving
      (p := ENNReal.ofReal (3 / 2 : ℝ)) hmeas hmp
    have hfun : g ∘ parabolicHomeomorph = pseq n - p := by
      funext z
      cases z
      rfl
    rw [hfun] at h
    exact h.symm
  have hconvPar : Tendsto (fun n => eLpNorm (pseq n - p)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ) atTop (nhds 0) := by
    have hseqEq : (fun n => eLpNorm (pseq n - p)
        (ENNReal.ofReal (3 / 2 : ℝ)) μ) =
        (fun n => eLpNorm
          (fun z : Vec3 × ℝ =>
            pseq n (parabolicHomeomorph.symm z) - p (parabolicHomeomorph.symm z))
          (ENNReal.ofReal (3 / 2 : ℝ)) ν) := by
      funext n
      exact hEq n
    rw [hseqEq]
    exact hconvProd
  simpa [μ, Q] using hconvPar

/-- A local box compactly contained in positive time is contained in a
strictly positive finite open time slab. -/
theorem lerayAssembly_localBox_time_bounds
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : CKN.localBox (Set.univ : Set Vec3) (Ioi 0) Ω' J) :
    ∃ δ T : ℝ, 0 < δ ∧ δ < T ∧ J ⊆ Ioo δ T := by
  obtain ⟨_, _, _, _, hJcompact, hJpositive⟩ := hbox
  by_cases hJne : (closure J).Nonempty
  · obtain ⟨a, ha⟩ := hJcompact.exists_isLeast hJne
    obtain ⟨b, hb⟩ := hJcompact.exists_isGreatest hJne
    have haPos : 0 < a := hJpositive ha.1
    have hab : a ≤ b := ha.2 hb.1
    let δ : ℝ := a / 2
    let T : ℝ := b + 1
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδT : δ < T := by
      dsimp [δ, T]
      linarith only [haPos, hab]
    refine ⟨δ, T, hδ, hδT, ?_⟩
    intro t ht
    have htc : t ∈ closure J := subset_closure ht
    constructor
    · dsimp [δ]
      linarith only [ha.2 htc, haPos]
    · dsimp [T]
      linarith only [hb.2 htc]
  · have hJempty : J = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hJne ⟨t, subset_closure ht⟩
    refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
    simp [hJempty]

/-- Strong convergence on a finite positive-time slab restricts to each
local box inside that slab. -/
theorem lerayAssembly_strongConv_localBox
    {E : Type*} [NormedAddCommGroup E]
    {Ω' : Set Vec3} {J : Set ℝ} {T : ℝ} {r : ℝ≥0∞}
    (hJ : J ⊆ Ioo 0 T)
    (F : ℕ → ParabolicPoint → E) (f : ParabolicPoint → E)
    (hconv : Tendsto (fun n => eLpNorm (F n - f) r
      (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (F n - f) r
      (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0) := by
  have hsub : spaceTimeSet Ω' J ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) :=
    Set.prod_mono (Set.subset_univ _) hJ
  have hmeas : volume.restrict (spaceTimeSet Ω' J) ≤
      volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    Measure.restrict_mono hsub le_rfl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hconv
    (Eventually.of_forall fun _ => bot_le)
    (Eventually.of_forall fun n => eLpNorm_mono_measure _ hmeas)

/-- Weak gradient pairings on a slab restrict to a test supported in a
local box. -/
theorem lerayAssembly_weakConv_localBox
    {Ω' : Set Vec3} {J : Set ℝ} {T : ℝ}
    (hJ : J ⊆ Ioo 0 T)
    (F : ℕ → ParabolicPoint → ℝ) (f w : ParabolicPoint → ℝ)
    (hwzero : ∀ z ∉ spaceTimeSet Ω' J, w z = 0)
    (hweak : Tendsto (fun n => ∫ z in spaceTimeSet
        (Set.univ : Set Vec3) (Ioo 0 T), F n z * w z) atTop
      (nhds (∫ z in spaceTimeSet
        (Set.univ : Set Vec3) (Ioo 0 T), f z * w z))) :
    Tendsto (fun n => ∫ z in spaceTimeSet Ω' J, F n z * w z) atTop
      (nhds (∫ z in spaceTimeSet Ω' J, f z * w z)) := by
  have hsub : spaceTimeSet Ω' J ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) :=
    Set.prod_mono (Set.subset_univ _) hJ
  have hloc (g : ParabolicPoint → ℝ) :
      (∫ z in spaceTimeSet Ω' J, g z * w z) =
        ∫ z, g z * w z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    simp [hwzero z hz]
  have hslab (g : ParabolicPoint → ℝ) :
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        g z * w z) = ∫ z, g z * w z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    simp [hwzero z (fun hmem => hz (hsub hmem))]
  simpa only [hslab, hloc] using hweak

/-- Weak slab convergence gives every local-box weak pairing by extending
the local test by zero. -/
theorem lerayAssembly_weakConv_localBox_all
    {Ω' : Set Vec3} {J : Set ℝ} {T : ℝ}
    (hbox : CKN.localBox (Set.univ : Set Vec3) (Ioi 0) Ω' J)
    (hJ : J ⊆ Ioo 0 T)
    (F : ℕ → ParabolicPoint → ℝ) (f : ParabolicPoint → ℝ)
    (hweak : ∀ w : ParabolicPoint → ℝ,
      MemLp w 2 (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
      Tendsto (fun n => ∫ z in spaceTimeSet
          (Set.univ : Set Vec3) (Ioo 0 T), F n z * w z) atTop
        (nhds (∫ z in spaceTimeSet
          (Set.univ : Set Vec3) (Ioo 0 T), f z * w z)))
    (w : ParabolicPoint → ℝ)
    (hw : MemLp w 2 (volume.restrict (spaceTimeSet Ω' J))) :
    Tendsto (fun n => ∫ z in spaceTimeSet Ω' J, F n z * w z) atTop
      (nhds (∫ z in spaceTimeSet Ω' J, f z * w z)) := by
  let Q : Set ParabolicPoint := spaceTimeSet Ω' J
  let QT : Set ParabolicPoint :=
    spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  have hQ : MeasurableSet Q := hbox.1.measurableSet.prod
    hbox.2.2.2.1.measurableSet
  have hsub : Q ⊆ QT := Set.prod_mono (Set.subset_univ _) hJ
  let W : ParabolicPoint → ℝ := Q.indicator w
  have hW : MemLp W 2 (volume.restrict QT) := by
    change MemLp (Q.indicator w) 2 (volume.restrict QT)
    rw [memLp_indicator_iff_restrict hQ,
      Measure.restrict_restrict_of_subset hsub]
    exact hw
  have hpair (g : ParabolicPoint → ℝ) :
      (∫ z in QT, g z * W z) = ∫ z in Q, g z * w z := by
    have hpoint : (fun z => g z * W z) =
        Q.indicator (fun z => g z * w z) := by
      funext z
      by_cases hz : z ∈ Q
      · simp [W, Set.indicator_of_mem hz]
      · simp [W, Set.indicator_of_notMem hz]
    change (∫ z, g z * W z ∂(volume.restrict QT)) = _
    rw [hpoint, integral_indicator hQ,
      Measure.restrict_restrict_of_subset hsub]
  have h := hweak W hW
  change Tendsto (fun n => ∫ z in QT, F n z * W z) atTop
    (nhds (∫ z in QT, f z * W z)) at h
  simpa only [hpair] using h

/-- The regularized momentum pairing is supported in the test field's
compact support. -/
theorem lerayAssembly_regMomentum_localBox
    {Ω' : Set Vec3} {J : Set ℝ}
    (φ : Vec3 × ℝ → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Ioi 0))
    (hKbox : tsupport (show ParabolicPoint → Vec3 from φ) ⊆
      spaceTimeSet Ω' J)
    (U Jv : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      (-(∑ i : Fin 3, U z i * timePartial (fun w => φ w i) z))
        - ∑ i : Fin 3, ∑ j : Fin 3,
          Jv z j * U z i * spatialPartial (fun w => φ w i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
          D z i j * spatialPartial (fun w => φ w i) j z
        - p z * ∑ i : Fin 3,
          spatialPartial (fun w => φ w i) i z) =
    ∫ z in spaceTimeSet Ω' J,
      (-(∑ i : Fin 3, U z i * timePartial (fun w => φ w i) z))
        - ∑ i : Fin 3, ∑ j : Fin 3,
          Jv z j * U z i * spatialPartial (fun w => φ w i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
          D z i j * spatialPartial (fun w => φ w i) j z
        - p z * ∑ i : Fin 3,
          spatialPartial (fun w => φ w i) i z := by
  let F : ParabolicPoint → ℝ := fun z =>
    (-(∑ i : Fin 3, U z i * timePartial (fun w => φ w i) z))
      - ∑ i : Fin 3, ∑ j : Fin 3,
        Jv z j * U z i * spatialPartial (fun w => φ w i) j z
      + ∑ i : Fin 3, ∑ j : Fin 3,
        D z i j * spatialPartial (fun w => φ w i) j z
      - p z * ∑ i : Fin 3,
        spatialPartial (fun w => φ w i) i z
  have hzero {z : ParabolicPoint}
      (hz : z ∉ tsupport (show ParabolicPoint → Vec3 from φ)) : F z = 0 := by
    have hzprod : (z : Vec3 × ℝ) ∉ tsupport φ := by
      intro hmem
      apply hz
      rw [tsupport_parabolic_eq]
      exact hmem
    have hzcomp (i : Fin 3) :
        (z : Vec3 × ℝ) ∉ tsupport (fun w => φ w i) := by
      intro hmem
      exact hzprod ((tsupport_component_subset (V := ℝ) φ i
        (fun _ h => by rw [h]; rfl)) hmem)
    have htime (i : Fin 3) : timePartial (fun w => φ w i) z = 0 :=
      timePartial_eq_zero_off_tsupport (hzcomp i)
    have hspace (i j : Fin 3) :
        spatialPartial (fun w => φ w i) j z = 0 :=
      spatialPartial_eq_zero_off_tsupport (hzcomp i) j
    simp [F, htime, hspace]
  have hglob : ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), F z =
      ∫ z, F z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    exact hzero (fun hmem => hz
      (tsupport_parabolic_subset_spaceTimeSet hφ hmem))
  have hloc : ∫ z in spaceTimeSet Ω' J, F z = ∫ z, F z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    exact hzero (fun hmem => hz (hKbox hmem))
  exact hglob.trans hloc.symm

private theorem assembly_localBox_time_bound
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : CKN.localBox (Set.univ : Set Vec3) (Ioi 0) Ω' J) :
    ∃ T : ℝ, 0 < T ∧ J ⊆ Ioo 0 T := by
  obtain ⟨δ, T, hδ, hδT, hJ⟩ := lerayAssembly_localBox_time_bounds hbox
  refine ⟨T, lt_trans hδ hδT, ?_⟩
  intro t ht
  have h := hJ ht
  exact ⟨lt_trans hδ h.1, h.2⟩

/-- A global Leray--Hopf pair and its finite-slab pressure integrability give
the data clauses of `def:sws` on the positive-time half space. -/
theorem lerayAssembly_hopfData
    {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hglobal : ∀ T : ℝ, 0 < T → IsLerayHopfSolution T a u Du)
    (hp : ∀ T : ℝ, 0 < T →
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    {q : ℝ} (hq : 5 / 2 < q) :
    CKN.IsSuitableWeakSolutionData (Set.univ : Set Vec3) (Ioi 0) q u Du p
      (0 : ParabolicPoint → Vec3) := by
  unfold CKN.IsSuitableWeakSolutionData
  refine ⟨isOpen_univ, isOpen_Ioi, ordConnected_Ioi, hq, ?_, ?_⟩
  · intro Ω' J hbox i
    change MemLp (fun z : ParabolicPoint => (0 : Vec3) i)
      (ENNReal.ofReal q) (volume.restrict (spaceTimeSet Ω' J))
    exact MemLp.zero
  · intro Ω' J hbox
    obtain ⟨T, hT, hJ⟩ := assembly_localBox_time_bound hbox
    let Q : Set ParabolicPoint := spaceTimeSet Ω' J
    let Q₀ : Set ParabolicPoint :=
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
    have hΩ : Ω' ⊆ (Set.univ : Set Vec3) := Set.subset_univ _
    have hQ : Q ⊆ Q₀ := Set.prod_mono hΩ hJ
    rcases hglobal T hT with
      ⟨_, _, hU, hDu, hSliceTop, hEnergyTop, hWeakGradient, _, _, _, _, _⟩
    have hUloc : AEStronglyMeasurable u (volume.restrict Q) :=
      hU.mono_measure (Measure.restrict_mono hQ le_rfl)
    have hDuloc : AEStronglyMeasurable Du (volume.restrict Q) :=
      hDu.mono_measure (Measure.restrict_mono hQ le_rfl)
    have hploc : AEStronglyMeasurable p (volume.restrict Q) :=
      (hp T hT).aestronglyMeasurable.mono_measure
        (Measure.restrict_mono hQ le_rfl)
    have hL2slice : essSup
        (fun s : ℝ => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ))
        (volume.restrict J) < ⊤ := by
      let G : ℝ → ℝ≥0∞ := fun s =>
        ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ)
      have hglobalAE := ae_le_essSup
        (μ := volume.restrict (Ioo 0 T)) (f := G)
      have hJAE := ae_restrict_of_ae_restrict_of_subset hJ hglobalAE
      have hbound : ∀ᵐ s ∂volume.restrict J,
          (∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ)) ≤
            essSup G (volume.restrict (Ioo 0 T)) := by
        filter_upwards [hJAE] with s hs
        exact (lintegral_mono_set hΩ).trans (by simpa [G] using hs)
      exact lt_of_le_of_lt (essSup_le_of_ae_le _ hbound) hSliceTop
    have hEnergy :
        (∫⁻ z in Q, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      exact lt_of_le_of_lt (lintegral_mono_set hQ) hEnergyTop
    have hpLoc : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict Q) :=
      (hp T hT).mono_measure (Measure.restrict_mono hQ le_rfl)
    have hWeakGradientLoc :
        ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
          HasWeakGradientOn Ω' (fun x => u (x, s) i)
            (fun x => Du (x, s) i) := by
      intro i
      have hJAE := ae_restrict_of_ae_restrict_of_subset hJ hWeakGradient
      filter_upwards [hJAE] with s hs
      exact HasWeakGradientOn.restrict hbox.1 hΩ (hs i)
    refine ⟨hUloc, hDuloc, hploc, ?_, hL2slice, hEnergy, hpLoc,
      MemLp.zero, hWeakGradientLoc⟩
    exact (MemLp.zero : MemLp (0 : ParabolicPoint → Vec3)
      (1 : ℝ≥0∞) (volume.restrict Q)).aestronglyMeasurable

/-- The divergence identity on positive time follows from the every-slab
Leray--Hopf weak-divergence clause. -/
theorem lerayAssembly_hopfDivergence
    {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hglobal : ∀ T : ℝ, 0 < T → IsLerayHopfSolution T a u Du)
    (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (Set.univ : Set Vec3) (Ioi 0)) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0 := by
  let K : Set ParabolicPoint := tsupport ψ
  have hK : IsCompact K := by
    simpa [K, CKN.tsupport_parabolic_eq] using
      CKN.isCompact_tsupport_parabolic hψ.2.1
  have hKsub : K ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) := by
    simpa [K] using CKN.tsupport_parabolic_subset_spaceTimeSet hψ
  obtain ⟨Ω', J, hbox, hKboxRaw⟩ := CKN.caccioppoli_localBox_of_compact_subset
    isOpen_univ isOpen_Ioi ordConnected_Ioi hK hKsub
  have hKbox : K ⊆ spaceTimeSet Ω' J := by
    simpa [K] using hKboxRaw
  obtain ⟨T, hT, hJ⟩ := assembly_localBox_time_bound hbox
  have hlocalToSlab : spaceTimeSet Ω' J ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) :=
    Set.prod_mono (Set.subset_univ _) hJ
  have hKslab : K ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) :=
    hKbox.trans hlocalToSlab
  have hKslabProduct : tsupport (show Vec3 × ℝ → ℝ from ψ) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
    rw [← CKN.tsupport_parabolic_eq]
    exact hKslab
  have hψslab : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (Set.univ : Set Vec3) (Ioo 0 T) :=
    ⟨hψ.1, hψ.2.1, hKslabProduct⟩
  have hfullLocal := CKN.stability_divergence_integral_eq_localBox
    ψ hψ hKbox u
  have hslabLocal := CKN.stability_divergence_integral_eq_localBox
    ψ hψslab hKbox u
  let F : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
      CKN.spatialPartialProd ψ i z
  have hmeasure :
      ((volume : Measure Vec3).prod
        (volume.restrict (Ioo 0 T))) =
        (volume : Measure (Vec3 × ℝ)).restrict
          (CKN.Leray.lerayPressureLimitSlab T) := by
    calc
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) =
          ((volume.restrict (Set.univ : Set Vec3)).prod
            (volume.restrict (Ioo 0 T))) := by simp
      _ = ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
          (Set.univ ×ˢ Ioo 0 T) := by rw [Measure.prod_restrict]
      _ = (volume : Measure (Vec3 × ℝ)).restrict
          (CKN.Leray.lerayPressureLimitSlab T) := by
        rw [← Measure.volume_eq_prod Vec3 ℝ]
        rfl
  have hAssoc := CKN.Leray.associatedPressureWeakDivergence_pairing_zero
    (hglobal T hT) hψ.1 hψ.2.1
  have hAssocZero : (∫ z : Vec3 × ℝ, F z
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)))) = 0 := by
    simpa [F, CKN.spatialPartialProd] using hAssoc
  have hfiniteProduct : (∫ z in CKN.Leray.lerayPressureLimitSlab T,
      F z ∂(volume : Measure (Vec3 × ℝ))) = 0 := by
    rw [← hmeasure]
    exact hAssocZero
  have hfinite := CKN.setIntegral_parabolic_to_product
    (Ω := (Set.univ : Set Vec3)) (I := Ioo 0 T)
    (F := fun z : ParabolicPoint =>
      ∑ i : Fin 3, u z i * spatialPartial ψ i z)
  have hslabZero :
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z) = 0 := by
    rw [hfinite]
    simpa [F, CKN.spatialPartialProd, CKN.Leray.lerayPressureLimitSlab]
      using hfiniteProduct
  calc
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z) =
      ∫ z in spaceTimeSet Ω' J,
        ∑ i : Fin 3, u z i * spatialPartial ψ i z := hfullLocal
    _ = ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z := hslabLocal.symm
    _ = 0 := hslabZero

end CKN.Leray

end
