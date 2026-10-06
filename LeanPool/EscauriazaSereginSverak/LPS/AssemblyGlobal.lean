/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.Assembly
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Assembly Global

Patch compatible smooth representatives from later-than-zero intervals into
one representative on the whole positive-time slab (`thm:lps`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

abbrev lpsAssemblySlab (a b : ℝ) :=
  spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)

abbrev lpsAssemblyTopSlab (a b : ℝ) :=
  spaceTimeSet (Set.univ : Set Vec3) (Ioc a b)

private instance : Measure.IsOpenPosMeasure (volume : Measure ParabolicPoint) where
  open_pos U hU hne := by
    have ho : IsOpen (parabolicHomeomorph.symm ⁻¹' U) :=
      hU.preimage parabolicHomeomorph.symm.continuous
    have hn : (parabolicHomeomorph.symm ⁻¹' U).Nonempty := by
      obtain ⟨z, hz⟩ := hne
      exact ⟨parabolicHomeomorph z, hz⟩
    exact ho.measure_ne_zero (volume : Measure (Vec3 × ℝ)) hn

private theorem lps_smooth_representatives_agree_on_overlap
    {a b T A B : ℝ} {u v w : ParabolicPoint → Vec3}
    (hTA : T < A) (hTB : T < B)
    (hu : u =ᵐ[volume.restrict (lpsAssemblySlab a T)] w)
    (hv : v =ᵐ[volume.restrict (lpsAssemblySlab b T)] w)
    (huSmooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z))
      ((Set.univ : Set Vec3) ×ˢ Ioc a A))
    (hvSmooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => v (parabolicHomeomorph.symm z))
      ((Set.univ : Set Vec3) ×ˢ Ioc b B)) :
    ∀ z, z ∈ lpsAssemblySlab (max a b) T → u z = v z := by
  let s : Set ParabolicPoint := lpsAssemblySlab (max a b) T
  have hsa : s ⊆ lpsAssemblySlab a T := by
    intro z hz
    rcases hz with ⟨hx, ht⟩
    exact ⟨hx, ⟨lt_of_le_of_lt (le_max_left a b) ht.1, ht.2⟩⟩
  have hsb : s ⊆ lpsAssemblySlab b T := by
    intro z hz
    rcases hz with ⟨hx, ht⟩
    exact ⟨hx, ⟨lt_of_le_of_lt (le_max_right a b) ht.1, ht.2⟩⟩
  have hu' : u =ᵐ[volume.restrict s] w :=
    ae_restrict_of_ae_restrict_of_subset hsa hu
  have hv' : v =ᵐ[volume.restrict s] w :=
    ae_restrict_of_ae_restrict_of_subset hsb hv
  have huv : u =ᵐ[volume.restrict s] v := hu'.trans hv'.symm
  have hsOpen : IsOpen s :=
    isOpen_spaceTimeSet Set.univ (Ioo (max a b) T) isOpen_univ isOpen_Ioo
  have huSub : (Set.univ : Set Vec3) ×ˢ Ioo (max a b) T ⊆
      (Set.univ : Set Vec3) ×ˢ Ioc a A := by
    intro z hz
    rcases hz with ⟨hx, ht⟩
    have hlow : a < z.2 := lt_of_le_of_lt (le_max_left a b) ht.1
    have hupp : z.2 < A := lt_trans ht.2 hTA
    exact ⟨hx, ⟨hlow, le_of_lt hupp⟩⟩
  have hvSub : (Set.univ : Set Vec3) ×ˢ Ioo (max a b) T ⊆
      (Set.univ : Set Vec3) ×ˢ Ioc b B := by
    intro z hz
    rcases hz with ⟨hx, ht⟩
    have hlow : b < z.2 := lt_of_le_of_lt (le_max_right a b) ht.1
    have hupp : z.2 < B := lt_trans ht.2 hTB
    exact ⟨hx, ⟨hlow, le_of_lt hupp⟩⟩
  have huContProd : ContinuousOn
      (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z))
      ((Set.univ : Set Vec3) ×ˢ Ioo (max a b) T) :=
    huSmooth.continuousOn.mono huSub
  have hvContProd : ContinuousOn
      (fun z : Vec3 × ℝ => v (parabolicHomeomorph.symm z))
      ((Set.univ : Set Vec3) ×ˢ Ioo (max a b) T) :=
    hvSmooth.continuousOn.mono hvSub
  have hmaps : MapsTo parabolicHomeomorph s
      ((Set.univ : Set Vec3) ×ˢ Ioo (max a b) T) := by
    intro z hz
    rcases hz with ⟨hx, ht⟩
    exact ⟨hx, ht⟩
  have huCont : ContinuousOn u s := by
    have h := huContProd.comp parabolicHomeomorph.continuous.continuousOn hmaps
    have heq : (fun z : ParabolicPoint => u (z.1, z.2)) = u := by
      funext z
      rfl
    simpa [Function.comp_def, parabolicHomeomorph_symm_apply, heq] using h
  have hvCont : ContinuousOn v s := by
    have h := hvContProd.comp parabolicHomeomorph.continuous.continuousOn hmaps
    have heq : (fun z : ParabolicPoint => v (z.1, z.2)) = v := by
      funext z
      rfl
    simpa [Function.comp_def, parabolicHomeomorph_symm_apply, heq] using h
  have hEqOn : EqOn u v s := Measure.eqOn_open_of_ae_eq huv hsOpen huCont hvCont
  intro z hz
  exact hEqOn hz

private theorem lps_eventuallyEq_of_eqOn_open_intersection
    {α : Type*} [TopologicalSpace α] {β : Type*} {x : α}
    {s o : Set α} {f g : α → β}
    (ho : IsOpen o) (hxo : x ∈ o)
    (hfg : ∀ y, y ∈ o ∩ s → f y = g y) :
    f =ᶠ[nhdsWithin x s] g := by
  have ho' : o ∈ 𝓝 x := ho.mem_nhds hxo
  have hoWithin : ∀ᶠ y in 𝓝[s] x, y ∈ o :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds ho'
  filter_upwards [hoWithin, self_mem_nhdsWithin] with y hyo hys
  exact hfg y ⟨hyo, hys⟩

private theorem lps_slab_covered_by_later_intervals
    {T : ℝ} (t : ℕ → ℝ) (htBase : t 0 < T / 2)
    (hCover : ∀ s, 0 < s → s < T / 2 → ∃ n, t n < s) :
    ∀ z, z ∈ lpsAssemblySlab 0 T → ∃ n, z ∈ lpsAssemblySlab (t n) T := by
  intro z hz
  rcases hz with ⟨-, hzt⟩
  have hpos : 0 < z.2 := hzt.1
  have hlt : z.2 < T := hzt.2
  by_cases hhalf : T / 2 ≤ z.2
  · refine ⟨0, ?_⟩
    refine ⟨by simp, ?_⟩
    exact ⟨lt_of_lt_of_le htBase hhalf, hlt⟩
  · obtain ⟨n, hn⟩ := hCover z.2 hpos (lt_of_not_ge hhalf)
    exact ⟨n, ⟨by simp, hn, hlt⟩⟩

/-- Patch compatible smooth representatives from later-than-zero intervals into
one representative on the whole positive-time slab (`thm:lps`). -/
theorem lps_patch_smooth_representatives
    {T : ℝ} {u : ParabolicPoint → Vec3}
    (t : ℕ → ℝ) (htPos : ∀ n, 0 < t n)
    (htBase : t 0 < T / 2)
    (hCover : ∀ s, 0 < s → s < T / 2 → ∃ n, t n < s)
    (v : ℕ → ParabolicPoint → Vec3)
    (hvEq : ∀ n, v n =ᵐ[volume.restrict (lpsAssemblySlab (t n) T)] u)
    (top : ℕ → ℝ) (hTop : ∀ n, T < top n)
    (hvSmooth : ∀ n, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => v n (parabolicHomeomorph.symm z))
      ((Set.univ : Set Vec3) ×ˢ Ioc (t n) (top n))) :
    ∃ uSmooth : ParabolicPoint → Vec3,
      uSmooth =ᵐ[volume.restrict (lpsAssemblySlab 0 T)] u ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : Vec3 × ℝ => uSmooth (parabolicHomeomorph.symm z))
        ((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T) := by
  let hsel : ∀ s, 0 < s → s < T / 2 → ℕ := fun s hs hsT =>
    Classical.choose (hCover s hs hsT)
  have hsel_lt : ∀ s (hs : 0 < s) (hsT : s < T / 2),
      t (hsel s hs hsT) < s :=
    fun s hs hsT => Classical.choose_spec (hCover s hs hsT)
  let uSmooth : ParabolicPoint → Vec3 := fun z =>
    if hz : z.2 ∈ Ioc (0 : ℝ) T then
      if hhalf : T / 2 ≤ z.2 then v 0 z
      else v (hsel z.2 hz.1 (lt_of_not_ge hhalf)) z
    else u z
  have hpatch : ∀ n z, z ∈ lpsAssemblySlab (t n) T →
      uSmooth z = v n z := by
    intro n z hz
    rcases hz with ⟨-, hzt⟩
    have hztPos : 0 < z.2 := lt_trans (htPos n) hzt.1
    have hztT : z.2 < T := hzt.2
    have hzmem : z.2 ∈ Ioc (0 : ℝ) T := ⟨hztPos, le_of_lt hztT⟩
    by_cases hhalf : T / 2 ≤ z.2
    · have h0 : t 0 < z.2 := lt_of_lt_of_le htBase hhalf
      have hagree := lps_smooth_representatives_agree_on_overlap
        (hTop 0) (hTop n) (hvEq 0) (hvEq n) (hvSmooth 0) (hvSmooth n)
      have hmax : max (t 0) (t n) < z.2 := max_lt_iff.mpr ⟨h0, hzt.1⟩
      have hzOverlap : z ∈ lpsAssemblySlab (max (t 0) (t n)) T :=
        ⟨by simp, ⟨hmax, hzt.2⟩⟩
      dsimp [uSmooth]
      rw [dite_eq_left hzmem, dite_eq_left hhalf]
      exact hagree z hzOverlap
    · have hsmall : z.2 < T / 2 := lt_of_not_ge hhalf
      let m := hsel z.2 hztPos hsmall
      have hmlt : t m < z.2 := hsel_lt z.2 hztPos hsmall
      have hagree := lps_smooth_representatives_agree_on_overlap
        (hTop m) (hTop n) (hvEq m) (hvEq n) (hvSmooth m) (hvSmooth n)
      have hmax : max (t m) (t n) < z.2 := max_lt_iff.mpr ⟨hmlt, hzt.1⟩
      have hzOverlap : z ∈ lpsAssemblySlab (max (t m) (t n)) T :=
        ⟨by simp, ⟨hmax, hzt.2⟩⟩
      dsimp [uSmooth]
      rw [dite_eq_left hzmem, dite_eq_right hhalf]
      simpa [m] using hagree z hzOverlap
  have hpatchAe : ∀ n,
      uSmooth =ᵐ[volume.restrict (lpsAssemblySlab (t n) T)] u := by
    intro n
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioo), hvEq n]
      with z hz heq
    exact (hpatch n z hz).trans heq
  have hAll : ∀ᵐ z ∂volume,
      ∀ n, z ∈ lpsAssemblySlab (t n) T → uSmooth z = u z :=
    ae_all_iff.2 (fun n => ae_imp_of_ae_restrict (hpatchAe n))
  have hCoverSlab := lps_slab_covered_by_later_intervals t htBase hCover
  have hGlobal : uSmooth =ᵐ[volume.restrict (lpsAssemblySlab 0 T)] u := by
    have hAllRestrict : ∀ᵐ z ∂(volume.restrict (lpsAssemblySlab 0 T)),
        ∀ n, z ∈ lpsAssemblySlab (t n) T → uSmooth z = u z :=
      hAll.filter_mono ae_restrict_le
    filter_upwards [hAllRestrict, ae_restrict_mem (by
      change MeasurableSet ((Set.univ : Set Vec3) ×ˢ Ioo (0 : ℝ) T)
      exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo)]
      with z hzAll hz
    obtain ⟨n, hzn⟩ := hCoverSlab z hz
    exact hzAll n hzn
  have hSmoothGlobal : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => uSmooth (parabolicHomeomorph.symm z))
      ((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T) := by
    intro x hx
    let z : ParabolicPoint := parabolicHomeomorph.symm x
    have hxTime : z.2 ∈ Ioc (0 : ℝ) T := by
      simpa [z, parabolicHomeomorph_symm_apply] using hx.2
    by_cases hhalf : T / 2 ≤ z.2
    · have hz0 : t 0 < z.2 := lt_of_lt_of_le htBase hhalf
      have hOpen : IsOpen {y : ParabolicPoint | t 0 < y.2} :=
        isOpen_Ioi.preimage continuous_snd_parabolicPoint
      have hzOpen : z ∈ {y : ParabolicPoint | t 0 < y.2} := hz0
      have hEqOn : ∀ y, y ∈ {y : ParabolicPoint | t 0 < y.2} ∩
          lpsAssemblyTopSlab 0 T → uSmooth y = v 0 y := by
        intro y hy
        have hy0 : t 0 < y.2 := hy.1
        rcases hy.2 with ⟨-, hyTime⟩
        by_cases hyhalf : T / 2 ≤ y.2
        · dsimp [uSmooth]
          rw [dite_eq_left hyTime, dite_eq_left hyhalf]
        · have hsmall : y.2 < T / 2 := lt_of_not_ge hyhalf
          let m := hsel y.2 hyTime.1 hsmall
          have hmt : t m < y.2 := hsel_lt y.2 hyTime.1 hsmall
          have hTpos : 0 < T := by linarith only [htPos 0, htBase]
          have hhalfT : T / 2 < T := by linarith only [hTpos]
          have hylt : y.2 < T := lt_trans hsmall hhalfT
          have hagree := lps_smooth_representatives_agree_on_overlap
            (hTop m) (hTop 0) (hvEq m) (hvEq 0) (hvSmooth m) (hvSmooth 0)
          have hmax : max (t m) (t 0) < y.2 := max_lt_iff.mpr ⟨hmt, hy0⟩
          have hyOverlap : y ∈ lpsAssemblySlab (max (t m) (t 0)) T :=
            ⟨by simp, ⟨hmax, hylt⟩⟩
          dsimp [uSmooth]
          rw [dite_eq_left hyTime, dite_eq_right hyhalf]
          simpa [m] using hagree y hyOverlap
      have hOpenProd : IsOpen
          (parabolicHomeomorph.symm ⁻¹' {y : ParabolicPoint | t 0 < y.2}) :=
        hOpen.preimage parabolicHomeomorph.symm.continuous
      have hxOpen : x ∈ parabolicHomeomorph.symm ⁻¹'
          {y : ParabolicPoint | t 0 < y.2} := hzOpen
      have hEqOpen := lps_eventuallyEq_of_eqOn_open_intersection hOpenProd hxOpen
        (by
          intro y hy
          have hyPar : parabolicHomeomorph.symm y ∈ lpsAssemblyTopSlab 0 T := by
            have hyProd : y ∈ (Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T := hy.2
            rcases hyProd with ⟨hx', ht'⟩
            exact ⟨by simp, by simpa [parabolicHomeomorph_symm_apply] using ht'⟩
          exact hEqOn (parabolicHomeomorph.symm y) ⟨hy.1, hyPar⟩)
      have hxBase : x ∈ (Set.univ : Set Vec3) ×ˢ Ioc (t 0) (top 0) := by
        exact ⟨by simp, ⟨hz0, le_trans hx.2.2 (le_of_lt (hTop 0))⟩⟩
      have hOpenEvent : ∀ᶠ y in 𝓝[((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T)] x,
          y ∈ parabolicHomeomorph.symm ⁻¹' {y : ParabolicPoint | t 0 < y.2} :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (hOpenProd.mem_nhds hxOpen)
      have hOpenAndDomain : ∀ᶠ y in 𝓝[((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T)] x,
          y ∈ parabolicHomeomorph.symm ⁻¹' {y : ParabolicPoint | t 0 < y.2} ∧
            y ∈ (Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T :=
        hOpenEvent.and self_mem_nhdsWithin
      have hBaseSet : ((Set.univ : Set Vec3) ×ˢ Ioc (t 0) (top 0)) ∈
          𝓝[((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T)] x :=
        Filter.mem_of_superset hOpenAndDomain (by
          intro y hy
          rcases hy.2 with ⟨-, hyt⟩
          have ht0 : t 0 < (parabolicHomeomorph.symm y).2 := hy.1
          exact ⟨by simp, ⟨by simpa [parabolicHomeomorph_symm_apply] using ht0,
            le_trans hyt.2 (le_of_lt (hTop 0))⟩⟩)
      have hbase : ContDiffWithinAt ℝ (⊤ : ℕ∞)
          (fun y : Vec3 × ℝ => v 0 (parabolicHomeomorph.symm y))
          ((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T) x :=
        (hvSmooth 0 x hxBase).mono_of_mem_nhdsWithin hBaseSet
      have hzTop : z ∈ lpsAssemblyTopSlab 0 T := ⟨by simp, hxTime⟩
      have hxEq : uSmooth z = v 0 z := hEqOn z ⟨hzOpen, hzTop⟩
      have hxEq' : uSmooth (parabolicHomeomorph.symm x) =
          v 0 (parabolicHomeomorph.symm x) := by simpa [z] using hxEq
      exact hbase.congr_of_eventuallyEq hEqOpen hxEq'
    · have hsmall : z.2 < T / 2 := lt_of_not_ge hhalf
      let n := hsel z.2 hxTime.1 hsmall
      have hnt : t n < z.2 := hsel_lt z.2 hxTime.1 hsmall
      have hOpen : IsOpen {y : ParabolicPoint | t n < y.2 ∧ y.2 < T / 2} :=
        (isOpen_Ioo).preimage continuous_snd_parabolicPoint
      have hzOpen : z ∈ {y : ParabolicPoint | t n < y.2 ∧ y.2 < T / 2} :=
        ⟨hnt, hsmall⟩
      have hEqOn : ∀ y, y ∈ {y : ParabolicPoint | t n < y.2 ∧ y.2 < T / 2} ∩
          lpsAssemblyTopSlab 0 T → uSmooth y = v n y := by
        intro y hy
        rcases hy with ⟨hyO, hyS⟩
        rcases hyS with ⟨-, hyTime⟩
        let m := hsel y.2 hyTime.1 hyO.2
        have hmt : t m < y.2 := hsel_lt y.2 hyTime.1 hyO.2
        have hagree := lps_smooth_representatives_agree_on_overlap
          (hTop m) (hTop n) (hvEq m) (hvEq n) (hvSmooth m) (hvSmooth n)
        have hmax : max (t m) (t n) < y.2 :=
          max_lt_iff.mpr ⟨hmt, hyO.1⟩
        have hyOverlap : y ∈ lpsAssemblySlab (max (t m) (t n)) T := by
          have hTpos : 0 < T := by linarith only [htPos 0, htBase]
          have hhalfT : T / 2 < T := by linarith only [hTpos]
          exact ⟨by simp, ⟨hmax, lt_trans hyO.2 hhalfT⟩⟩
        dsimp [uSmooth]
        rw [dite_eq_left hyTime, dite_eq_right (not_le_of_gt hyO.2)]
        simpa [m] using hagree y hyOverlap
      have hOpenProd : IsOpen
          (parabolicHomeomorph.symm ⁻¹'
            {y : ParabolicPoint | t n < y.2 ∧ y.2 < T / 2}) :=
        hOpen.preimage parabolicHomeomorph.symm.continuous
      have hxOpen : x ∈ parabolicHomeomorph.symm ⁻¹'
          {y : ParabolicPoint | t n < y.2 ∧ y.2 < T / 2} := hzOpen
      have hEqOpen := lps_eventuallyEq_of_eqOn_open_intersection hOpenProd hxOpen
        (by
          intro y hy
          have hyPar : parabolicHomeomorph.symm y ∈ lpsAssemblyTopSlab 0 T := by
            have hyProd : y ∈ (Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T := hy.2
            rcases hyProd with ⟨hx', ht'⟩
            exact ⟨by simp, by simpa [parabolicHomeomorph_symm_apply] using ht'⟩
          exact hEqOn (parabolicHomeomorph.symm y) ⟨hy.1, hyPar⟩)
      have hxBase : x ∈ (Set.univ : Set Vec3) ×ˢ Ioc (t n) (top n) := by
        exact ⟨by simp, ⟨hnt, le_trans hx.2.2 (le_of_lt (hTop n))⟩⟩
      have hOpenEvent : ∀ᶠ y in 𝓝[((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T)] x,
          y ∈ parabolicHomeomorph.symm ⁻¹'
            {y : ParabolicPoint | t n < y.2 ∧ y.2 < T / 2} :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (hOpenProd.mem_nhds hxOpen)
      have hOpenAndDomain : ∀ᶠ y in 𝓝[((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T)] x,
          y ∈ parabolicHomeomorph.symm ⁻¹'
              {y : ParabolicPoint | t n < y.2 ∧ y.2 < T / 2} ∧
            y ∈ (Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T :=
        hOpenEvent.and self_mem_nhdsWithin
      have hBaseSet : ((Set.univ : Set Vec3) ×ˢ Ioc (t n) (top n)) ∈
          𝓝[((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T)] x :=
        Filter.mem_of_superset hOpenAndDomain (by
          intro y hy
          rcases hy.2 with ⟨-, hyt⟩
          have htn : t n < (parabolicHomeomorph.symm y).2 := hy.1.1
          exact ⟨by simp, ⟨by simpa [parabolicHomeomorph_symm_apply] using htn,
            le_trans hyt.2 (le_of_lt (hTop n))⟩⟩)
      have hsmooth : ContDiffWithinAt ℝ (⊤ : ℕ∞)
          (fun y : Vec3 × ℝ => v n (parabolicHomeomorph.symm y))
          ((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T) x :=
        (hvSmooth n x hxBase).mono_of_mem_nhdsWithin hBaseSet
      have hzTop : z ∈ lpsAssemblyTopSlab 0 T := ⟨by simp, hxTime⟩
      have hxEq : uSmooth z = v n z := hEqOn z ⟨hzOpen, hzTop⟩
      have hxEq' : uSmooth (parabolicHomeomorph.symm x) =
          v n (parabolicHomeomorph.symm x) := by simpa [z] using hxEq
      exact hsmooth.congr_of_eventuallyEq hEqOpen hxEq'
  exact ⟨uSmooth, hGlobal, hSmoothGlobal⟩

/-- Assemble the exact `thm:lps` conclusion from the continuation, uniqueness,
and smoothing conclusions for its source-facing nodes. The continuation
input is the conclusion of `lem:lps-continuation`; it receives the a.e.
energy identity from `lem:lps-energy-equality` and a time in the joint good
and equality set. -/
theorem lps_ladyzhenskaya_prodi_serrin_of_node_conclusions
    (hD5 : ∀ {T : ℝ} {a : Vec3 → Vec3}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3},
      (hLH : IsLerayHopfSolution T a u Du) →
      ((∃ s : ℝ, 3 < s ∧
          (∫⁻ t in Ioo (0 : ℝ) T,
            (∫⁻ x : Vec3,
              ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
                ((2 * s / (s - 3)) / s)) < ⊤) ∨
        (∫⁻ t in Ioo (0 : ℝ) T,
          (essSup (fun x : Vec3 =>
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
            (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤) →
      (∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
        (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k) -
            (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
          -2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j) →
      ∀ t₀, t₀ ∈ Ioo (0 : ℝ) T → IsLpsGoodTime u Du t₀ →
        (∫ x : Vec3, ∑ k : Fin 3, u (x, t₀) k * u (x, t₀) k) -
            (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
          -2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
            ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j →
        ∃ t₁, T < t₁ ∧
          ∃ (U : ParabolicPoint → Vec3)
            (DU : ParabolicPoint → Fin 3 → Vec3)
            (p : ParabolicPoint → ℝ),
            IsLpsStrongSolution t₀ t₁ U DU p ∧
            (fun x : Vec3 => U (x, t₀)) =ᵐ[volume]
              (fun x : Vec3 => u (x, t₀)) ∧
            U =ᵐ[volume.restrict
              (spaceTimeSet Set.univ (Ioo t₀ T))] u)
    (hD6 : ∀ {T : ℝ} {a : Vec3 → Vec3}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3},
      IsLerayHopfSolution T a u Du →
      ((∃ s : ℝ, 3 < s ∧
          (∫⁻ t in Ioo (0 : ℝ) T,
            (∫⁻ x : Vec3,
              ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
                ((2 * s / (s - 3)) / s)) < ⊤) ∨
        (∫⁻ t in Ioo (0 : ℝ) T,
          (essSup (fun x : Vec3 =>
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
            (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤) →
      ∀ v : ParabolicPoint → Vec3,
        ∀ Dv : ParabolicPoint → Fin 3 → Vec3,
          IsLerayHopfSolution T a v Dv →
            v =ᵐ[volume.restrict
              (spaceTimeSet Set.univ (Ioo (0 : ℝ) T))] u)
    (hD7 : ∀ {t₀ t₁ : ℝ} {U : ParabolicPoint → Vec3}
      {DU : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ},
      IsLpsStrongSolution t₀ t₁ U DU p →
      ∃ R : ParabolicPoint → Vec3,
        R =ᵐ[volume.restrict
          (spaceTimeSet Set.univ (Ioo t₀ t₁))] U ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => R z)
          ((Set.univ : Set Vec3) ×ˢ Ioc t₀ t₁))
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hSerrin :
      (∃ s : ℝ, 3 < s ∧
        (∫⁻ t in Ioo (0 : ℝ) T,
          (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
              ((2 * s / (s - 3)) / s)) < ⊤) ∨
      (∫⁻ t in Ioo (0 : ℝ) T,
        (essSup (fun x : Vec3 =>
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤) :
    (∀ v : ParabolicPoint → Vec3,
      ∀ Dv : ParabolicPoint → Fin 3 → Vec3,
        IsLerayHopfSolution T a v Dv →
          v =ᵐ[volume.restrict
            (spaceTimeSet Set.univ (Ioo (0 : ℝ) T))] u) ∧
    (∃ uSmooth : ParabolicPoint → Vec3,
      uSmooth =ᵐ[volume.restrict
        (spaceTimeSet Set.univ (Ioo (0 : ℝ) T))] u ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => uSmooth z)
        ((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T)) := by
  have hEnergy := lps_serrin_energy_equality hLH hSerrin
  have hUnique := hD6 hLH hSerrin
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 4)
  have hδpos : ∀ n, 0 < δ n := by
    intro n
    dsimp [δ]
    exact div_pos hLH.1 (by positivity)
  have hδle : ∀ n, δ n ≤ T := by
    intro n
    dsimp [δ]
    have hden : 0 < (n : ℝ) + 4 := by positivity
    have hdenle : (1 : ℝ) ≤ (n : ℝ) + 4 := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith only [hn]
    apply (div_le_iff₀ hden).2
    calc
      T = T * 1 := by ring
      _ ≤ T * ((n : ℝ) + 4) :=
        mul_le_mul_of_nonneg_left hdenle (le_of_lt hLH.1)
  let t : ℕ → ℝ := fun n => Classical.choose
    (lps_good_energy_time_in_interval hLH hSerrin (hδpos n) (hδle n))
  have htData : ∀ n,
      t n ∈ Ioo (0 : ℝ) (δ n) ∧ IsLpsGoodTime u Du (t n) ∧
        (∫ x : Vec3, ∑ k : Fin 3, u (x, t n) k * u (x, t n) k) -
            (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
          -2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 (t n)),
            ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j := by
    intro n
    exact Classical.choose_spec
      (lps_good_energy_time_in_interval hLH hSerrin (hδpos n) (hδle n))
  have htPos : ∀ n, 0 < t n := fun n => (htData n).1.1
  have htLtT : ∀ n, t n < T := fun n =>
    lt_of_lt_of_le (htData n).1.2 (hδle n)
  have hCover : ∀ s, 0 < s → s < T / 2 → ∃ n, t n < s := by
    intro s hs hsT
    obtain ⟨n, hn⟩ := exists_nat_gt (T / s)
    have hn4 : (n : ℝ) < (n : ℝ) + 4 :=
      lt_add_of_pos_right _ (by norm_num)
    have hTmul : T < s * ((n : ℝ) + 4) := by
      calc
      T < (n : ℝ) * s := (div_lt_iff₀ hs).mp hn
      _ = s * (n : ℝ) := by ring
      _ ≤ s * ((n : ℝ) + 4) :=
          mul_le_mul_of_nonneg_left (le_of_lt hn4) (le_of_lt hs)
    have hδs : δ n < s := (div_lt_iff₀ (by positivity)).2 hTmul
    exact ⟨n, lt_trans (htData n |>.1.2) hδs⟩
  let top : ℕ → ℝ := fun n => Classical.choose
    (hD5 hLH hSerrin hEnergy (t n) (by
      exact ⟨htPos n, htLtT n⟩) (htData n).2.1 (htData n).2.2)
  have hContinueSpec : ∀ n,
      T < top n ∧
        ∃ (U : ParabolicPoint → Vec3)
          (DU : ParabolicPoint → Fin 3 → Vec3)
          (p : ParabolicPoint → ℝ),
          IsLpsStrongSolution (t n) (top n) U DU p ∧
          (fun x : Vec3 => U (x, t n)) =ᵐ[volume]
            (fun x : Vec3 => u (x, t n)) ∧
          U =ᵐ[volume.restrict
            (spaceTimeSet Set.univ (Ioo (t n) T))] u := by
    intro n
    exact Classical.choose_spec
      (hD5 hLH hSerrin hEnergy (t n) (by
        exact ⟨htPos n, htLtT n⟩) (htData n).2.1 (htData n).2.2)
  choose v Dv p hStrong hTrace hMatch using
    (fun n => (hContinueSpec n).2)
  let smooth : ℕ → ParabolicPoint → Vec3 := fun n => Classical.choose
    (hD7 (hStrong n))
  have hSmoothSpec : ∀ n,
      smooth n =ᵐ[volume.restrict
        (spaceTimeSet Set.univ (Ioo (t n) (top n)))] v n ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : Vec3 × ℝ => smooth n z)
        ((Set.univ : Set Vec3) ×ˢ Ioc (t n) (top n)) := by
    intro n
    exact Classical.choose_spec (hD7 (hStrong n))
  have hSmoothEq : ∀ n,
      smooth n =ᵐ[volume.restrict (lpsAssemblySlab (t n) T)] u := by
    intro n
    have hsub : lpsAssemblySlab (t n) T ⊆
        spaceTimeSet Set.univ (Ioo (t n) (top n)) := by
      intro z hz
      rcases hz with ⟨hx, ht⟩
      exact ⟨hx, ⟨ht.1, lt_trans ht.2 (hContinueSpec n).1⟩⟩
    have hSmoothU : smooth n =ᵐ[volume.restrict (lpsAssemblySlab (t n) T)]
        v n := by
      exact ae_restrict_of_ae_restrict_of_subset hsub (hSmoothSpec n).1
    exact hSmoothU.trans (hMatch n)
  have hTop : ∀ n, T < top n := fun n => (hContinueSpec n).1
  have hSmoothTop : ∀ n, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => smooth n (parabolicHomeomorph.symm z))
      ((Set.univ : Set Vec3) ×ˢ Ioc (t n) (top n)) := by
    intro n
    simpa [parabolicHomeomorph_symm_apply] using (hSmoothSpec n).2
  have hPatch := lps_patch_smooth_representatives (T := T) (u := u)
    t htPos
    (by
      have h0 : t 0 < T / 4 := by simpa [δ] using (htData 0).1.2
      have hquarter : T / 4 < T / 2 := by linarith only [hLH.1]
      exact lt_trans h0 hquarter)
    hCover smooth hSmoothEq top hTop hSmoothTop
  obtain ⟨uSmooth, hSmoothAe, hSmooth⟩ := hPatch
  refine ⟨hUnique, ?_⟩
  refine ⟨uSmooth, ?_, ?_⟩
  · simpa [lpsAssemblySlab] using hSmoothAe
  · simpa [parabolicHomeomorph_symm_apply] using hSmooth
end ESS

end
