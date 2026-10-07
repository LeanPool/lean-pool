/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingJointField
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGain
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# Patching the jointly smooth representatives over positive-time slabs

`lem:lps-Bochner-joint-smooth`: representatives built on the slabs
`ℝ³ × [t₀ + δ, t₁]` that agree almost everywhere with the same field agree
everywhere on the common slab.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Two vector fields continuous on a slab whose slices agree almost everywhere for
almost every time agree everywhere on the slab. -/
theorem lps_eqOn_slab_of_slices_ae {a b : ℝ} (hab : a < b) {R R' : Vec3 × ℝ → Vec3}
    (hR : ContinuousOn R ((univ : Set Vec3) ×ˢ Icc a b))
    (hR' : ContinuousOn R' ((univ : Set Vec3) ×ˢ Icc a b))
    (h : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      (fun x => R (x, t)) =ᵐ[volume] fun x => R' (x, t)) :
    EqOn R R' ((univ : Set Vec3) ×ˢ Icc a b) := by
  rintro ⟨x, t⟩ ⟨-, ht⟩
  -- the slices agree everywhere in space for almost every time
  have hslice : ∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ y : Vec3, R (y, s) = R' (y, s) := by
    filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with s hs hsI
    have hsI' : s ∈ Icc a b := Ioo_subset_Icc_self hsI
    have hc : Continuous fun y : Vec3 => R (y, s) :=
      hR.comp_continuous (continuous_id.prodMk continuous_const)
        (fun y => ⟨mem_univ _, hsI'⟩)
    have hc' : Continuous fun y : Vec3 => R' (y, s) :=
      hR'.comp_continuous (continuous_id.prodMk continuous_const)
        (fun y => ⟨mem_univ _, hsI'⟩)
    exact fun y => congrFun ((Continuous.ae_eq_iff_eq volume hc hc').mp hs) y
  -- continuity in time gives equality at every time
  have hfun : ∀ y : Vec3, EqOn (fun s => R (y, s)) (fun s => R' (y, s)) (Icc a b) := by
    intro y
    have hy : ∀ᵐ s ∂(volume.restrict (Icc a b)), R (y, s) = R' (y, s) := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      filter_upwards [hslice] with s hs using hs y
    refine Measure.eqOn_of_ae_eq hy ?_ ?_ ?_
    · exact hR.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun s hs => ⟨mem_univ _, hs⟩)
    · exact hR'.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun s hs => ⟨mem_univ _, hs⟩)
    · rw [interior_Icc]
      exact (closure_Ioo hab.ne).ge
  exact hfun x ht

/-- The slab representatives of the strong solution, one for each positive-time slab
(`lem:lps-Bochner-joint-smooth`). -/
theorem lps_slab_rep_of_data {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3} {δ : ℝ}
    (hδ1 : t₀ + δ < t₁)
    (Z : ℕ → Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ)
    (hfam : ∀ (i : Fin 3) (j : ℕ), ∀ t ∈ Icc (t₀ + δ) t₁, ∀ m : ℕ,
      IsSobolevFamilyOn m univ (Z j i t []) (Z j i t))
    (hcont : ∀ (i : Fin 3) (j : ℕ) (α : List (Fin 3)), ∀ t ∈ Icc (t₀ + δ) t₁,
      Tendsto (fun s => eLpNorm (Z j i s α - Z j i t α) 2 volume)
        (𝓝[Icc (t₀ + δ) t₁] t) (𝓝 0))
    (hderiv : ∀ (i : Fin 3) (j : ℕ) (α : List (Fin 3)) (ψ : Vec3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → ∀ t ∈ Icc (t₀ + δ) t₁,
        HasDerivWithinAt (fun s => ∫ x, Z j i s α x * ψ x)
          (∫ x, Z (j + 1) i t α x * ψ x) (Icc (t₀ + δ) t₁) t)
    (hae : ∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) t₁)), ∀ i : Fin 3,
      Z 0 i t [] =ᵐ[volume] fun x => u (x, t) i) :
    ∃ R : Vec3 × ℝ → Vec3,
      ContDiffOn ℝ (⊤ : ℕ∞) R ((univ : Set Vec3) ×ˢ Icc (t₀ + δ) t₁) ∧
      ∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) t₁)),
        (fun x => R (x, t)) =ᵐ[volume] fun x => u (x, t) := by
  have hab : t₀ + δ < t₁ := hδ1
  have hi := fun i : Fin 3 => lps_smooth_rep_of_curves (a := t₀ + δ) (b := t₁) hab
    (Z := fun j => Z j i) (fun j => hfam i j) (hcont i) (hderiv i)
  choose Ri hRi using hi
  refine ⟨fun z i => Ri i z, contDiffOn_pi.mpr fun i => (hRi i).1, ?_⟩
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t ht htI
  have hall : ∀ᵐ x ∂(volume : Measure Vec3), ∀ i : Fin 3, Ri i (x, t) = u (x, t) i :=
    ae_all_iff.mpr fun i => ((hRi i).2 t (Ioo_subset_Icc_self htI)).trans (ht i)
  filter_upwards [hall] with x hx
  funext i
  exact hx i

/-- Joint smoothness of the strong solution from all-order slice curves on each positive-time
slab (`prop:lps-smoothing`, `lem:lps-Bochner-joint-smooth`). -/
theorem lps_smoothing_of_curves {t₀ t₁ : ℝ} (hab : t₀ < t₁) {u : ParabolicPoint → Vec3}
    (hu : ∀ i : Fin 3, AEStronglyMeasurable (fun z : ParabolicPoint => u z i)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hData : ∀ δ : ℝ, 0 < δ → t₀ + δ < t₁ →
      ∃ Z : ℕ → Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ,
        (∀ (i : Fin 3) (j : ℕ), ∀ t ∈ Icc (t₀ + δ) t₁, ∀ m : ℕ,
          IsSobolevFamilyOn m univ (Z j i t []) (Z j i t)) ∧
        (∀ (i : Fin 3) (j : ℕ) (α : List (Fin 3)), ∀ t ∈ Icc (t₀ + δ) t₁,
          Tendsto (fun s => eLpNorm (Z j i s α - Z j i t α) 2 volume)
            (𝓝[Icc (t₀ + δ) t₁] t) (𝓝 0)) ∧
        (∀ (i : Fin 3) (j : ℕ) (α : List (Fin 3)) (ψ : Vec3 → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → ∀ t ∈ Icc (t₀ + δ) t₁,
            HasDerivWithinAt (fun s => ∫ x, Z j i s α x * ψ x)
              (∫ x, Z (j + 1) i t α x * ψ x) (Icc (t₀ + δ) t₁) t) ∧
        (∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) t₁)), ∀ i : Fin 3,
          Z 0 i t [] =ᵐ[volume] fun x => u (x, t) i)) :
    ∃ R : ParabolicPoint → Vec3,
      R =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))] u ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => R z)
        ((univ : Set Vec3) ×ˢ Ioc t₀ t₁) := by
  -- slab representatives
  have hslab : ∀ δ : ℝ, 0 < δ → t₀ + δ < t₁ → ∃ Rδ : Vec3 × ℝ → Vec3,
      ContDiffOn ℝ (⊤ : ℕ∞) Rδ ((univ : Set Vec3) ×ˢ Icc (t₀ + δ) t₁) ∧
      ∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) t₁)),
        (fun x => Rδ (x, t)) =ᵐ[volume] fun x => u (x, t) := by
    intro δ hδ hδ1
    obtain ⟨Z, hfam, hcont, hderiv, hae⟩ := hData δ hδ hδ1
    exact lps_slab_rep_of_data hδ1 Z hfam hcont hderiv hae
  choose! R hR using hslab
  -- agreement of two slab representatives on the common slab
  have hE : ∀ δ δ' : ℝ, 0 < δ → t₀ + δ < t₁ → 0 < δ' → t₀ + δ' < t₁ →
      EqOn (R δ) (R δ') ((univ : Set Vec3) ×ˢ Icc (t₀ + max δ δ') t₁) := by
    intro δ δ' hδ hδ1 hδ' hδ1'
    have hm : t₀ + max δ δ' < t₁ := by
      rcases le_total δ δ' with h | h
      · rw [max_eq_right h]; exact hδ1'
      · rw [max_eq_left h]; exact hδ1
    have hsub : (univ : Set Vec3) ×ˢ Icc (t₀ + max δ δ') t₁ ⊆
        (univ : Set Vec3) ×ˢ Icc (t₀ + δ) t₁ :=
      prod_mono subset_rfl (Icc_subset_Icc (by linarith only [le_max_left δ δ']) le_rfl)
    have hsub' : (univ : Set Vec3) ×ˢ Icc (t₀ + max δ δ') t₁ ⊆
        (univ : Set Vec3) ×ˢ Icc (t₀ + δ') t₁ :=
      prod_mono subset_rfl (Icc_subset_Icc (by linarith only [le_max_right δ δ']) le_rfl)
    refine lps_eqOn_slab_of_slices_ae hm
      ((hR δ hδ hδ1).1.continuousOn.mono hsub) ((hR δ' hδ' hδ1').1.continuousOn.mono hsub') ?_
    have h1 : ∀ᵐ t ∂(volume.restrict (Ioo (t₀ + max δ δ') t₁)),
        (fun x => R δ (x, t)) =ᵐ[volume] fun x => u (x, t) :=
      ae_restrict_of_ae_restrict_of_subset
        (Ioo_subset_Ioo (by linarith only [le_max_left δ δ']) le_rfl) (hR δ hδ hδ1).2
    have h2 : ∀ᵐ t ∂(volume.restrict (Ioo (t₀ + max δ δ') t₁)),
        (fun x => R δ' (x, t)) =ᵐ[volume] fun x => u (x, t) :=
      ae_restrict_of_ae_restrict_of_subset
        (Ioo_subset_Ioo (by linarith only [le_max_right δ δ']) le_rfl) (hR δ' hδ' hδ1').2
    filter_upwards [h1, h2] with t ht1 ht2
    exact ht1.trans ht2.symm
  -- the patched representative
  classical
  let S : Set (Vec3 × ℝ) := (univ : Set Vec3) ×ˢ Ioc t₀ t₁
  let F : Vec3 × ℝ → Vec3 := fun z => R ((z.2 - t₀) / 2) z
  let Rf : Vec3 × ℝ → Vec3 := S.piecewise F 0
  have hδpos : ∀ z ∈ S, 0 < (z.2 - t₀) / 2 := fun z hz => by
    have := hz.2.1
    positivity
  have hδlt : ∀ z ∈ S, t₀ + (z.2 - t₀) / 2 < t₁ := fun z hz => by
    have h1 := hz.2.1
    have h2 := hz.2.2
    linarith only [h1, h2]
  -- local agreement with a fixed slab representative
  have hclaim : ∀ δ₀ : ℝ, 0 < δ₀ → t₀ + δ₀ < t₁ → ∀ z ∈ S, t₀ + δ₀ ≤ z.2 → Rf z = R δ₀ z := by
    intro δ₀ hδ₀ hδ₀1 z hz hzt
    simp only [Rf, Set.piecewise_eq_of_mem _ _ _ hz, F]
    refine hE _ δ₀ (hδpos z hz) (hδlt z hz) hδ₀ hδ₀1 ?_
    refine ⟨mem_univ _, ?_, hz.2.2⟩
    have := hz.2.1
    rcases le_total ((z.2 - t₀) / 2) δ₀ with h | h
    · rw [max_eq_right h]; exact hzt
    · rw [max_eq_left h]; linarith only [this]
  have hcd : ContDiffOn ℝ (⊤ : ℕ∞) Rf S := by
    intro z₀ hz₀
    set δ₀ : ℝ := (z₀.2 - t₀) / 2 with hδ₀def
    have hδ₀ : 0 < δ₀ := hδpos z₀ hz₀
    have hδ₀1 : t₀ + δ₀ < t₁ := hδlt z₀ hz₀
    have hz₀t : t₀ + δ₀ < z₀.2 := by
      have := hz₀.2.1
      rw [hδ₀def]
      linarith only [this]
    have h1 : ContDiffWithinAt ℝ (⊤ : ℕ∞) (R δ₀) ((univ : Set Vec3) ×ˢ Icc (t₀ + δ₀) t₁) z₀ :=
      (hR δ₀ hδ₀ hδ₀1).1 z₀ ⟨mem_univ _, hz₀t.le, hz₀.2.2⟩
    have hmem : (univ : Set Vec3) ×ˢ Icc (t₀ + δ₀) t₁ ∈ 𝓝[S] z₀ := by
      refine mem_nhdsWithin.mpr ⟨{z | t₀ + δ₀ < z.2}, isOpen_lt continuous_const continuous_snd,
        hz₀t, fun z hz => ⟨mem_univ _, hz.1.le, hz.2.2.2⟩⟩
    have h2 := h1.mono_of_mem_nhdsWithin hmem
    have heq : Rf =ᶠ[𝓝[S] z₀] R δ₀ := by
      have : {z : Vec3 × ℝ | t₀ + δ₀ < z.2} ∩ S ∈ 𝓝[S] z₀ :=
        mem_nhdsWithin.mpr ⟨{z | t₀ + δ₀ < z.2}, isOpen_lt continuous_const continuous_snd,
          hz₀t, subset_rfl⟩
      filter_upwards [this] with z hz using hclaim δ₀ hδ₀ hδ₀1 z hz.2 hz.1.le
    exact h2.congr_of_eventuallyEq heq (hclaim δ₀ hδ₀ hδ₀1 z₀ hz₀ hz₀t.le)
  -- slices of the patched representative
  have hslices : ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)),
      (fun x => Rf (x, t)) =ᵐ[volume] fun x => u (x, t) := by
    let δn : ℕ → ℝ := fun n => (t₁ - t₀) / ((n : ℝ) + 2)
    have hδn : ∀ n : ℕ, 0 < δn n ∧ t₀ + δn n < t₁ := by
      intro n
      have h0 : 0 < t₁ - t₀ := sub_pos.mpr hab
      have hn2 : (1 : ℝ) < (n : ℝ) + 2 := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith only [this]
      refine ⟨by positivity, ?_⟩
      have : δn n < t₁ - t₀ := by
        simp only [δn]
        rw [div_lt_iff₀ (by positivity)]
        nlinarith only [h0, hn2]
      linarith only [this]
    have hIoo : Ioo t₀ t₁ = ⋃ n : ℕ, Ioo (t₀ + δn n) t₁ := by
      ext t
      simp only [mem_Ioo, mem_iUnion]
      constructor
      · rintro ⟨ht0, ht1⟩
        obtain ⟨n, hn⟩ := exists_nat_gt ((t₁ - t₀) / (t - t₀))
        refine ⟨n, ?_, ht1⟩
        have hpos : 0 < t - t₀ := sub_pos.mpr ht0
        have h1 : t₁ - t₀ < n * (t - t₀) := by
          rwa [div_lt_iff₀ hpos] at hn
        have h2 : δn n < t - t₀ := by
          simp only [δn]
          rw [div_lt_iff₀ (by positivity)]
          nlinarith only [h1, hpos, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        linarith only [h2]
      · rintro ⟨n, h1, h2⟩
        exact ⟨by linarith only [h1, (hδn n).1], h2⟩
    rw [hIoo, ae_restrict_iUnion_iff]
    intro n
    filter_upwards [(hR (δn n) (hδn n).1 (hδn n).2).2, ae_restrict_mem measurableSet_Ioo]
      with t ht htI
    refine (Filter.EventuallyEq.of_eq ?_).trans ht
    funext x
    exact hclaim (δn n) (hδn n).1 (hδn n).2 (x, t)
      ⟨mem_univ _, by linarith only [htI.1, (hδn n).1], htI.2.le⟩ htI.1.le
  -- measurability and the product statement
  have hSm : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Ioc
  have hRfm : Measurable Rf :=
    ContinuousOn.measurable_piecewise
      (hcd.continuousOn.congr fun z hz => (Set.piecewise_eq_of_mem S F 0 hz).symm)
      continuous_zero.continuousOn hSm
  have hu' : ∀ i : Fin 3, AEStronglyMeasurable (fun z : Vec3 × ℝ => u z i)
      (volume.restrict ((univ : Set Vec3) ×ˢ Ioo t₀ t₁)) := hu
  let ut : Vec3 × ℝ → Vec3 := fun z i => (hu' i).mk _ z
  have hutm : Measurable ut :=
    measurable_pi_iff.mpr fun i => (hu' i).stronglyMeasurable_mk.measurable
  have hut : u =ᵐ[volume.restrict ((univ : Set Vec3) ×ˢ Ioo t₀ t₁)] ut := by
    have := ae_all_iff.mpr fun i => (hu' i).ae_eq_mk
    filter_upwards [this] with z hz
    funext i
    exact hz i
  refine ⟨Rf, ?_, hcd⟩
  have hslicesut : ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)),
      (fun x => Rf (x, t)) =ᵐ[volume] fun x => ut (x, t) := by
    have h1 : ∀ i : Fin 3, ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)),
        (fun x => u (x, t) i) =ᵐ[volume.restrict (univ : Set Vec3)] fun x => ut (x, t) i :=
      fun i => ae_slices_of_ae_prod (B := (univ : Set Vec3)) (I := Ioo t₀ t₁)
        (f := fun z => u z i) (g := fun z => ut z i) (hut.mono fun z hz => congrFun hz i)
    have h2 := ae_all_iff.mpr h1
    filter_upwards [hslices, h2] with t ht1 ht2
    simp only [Measure.restrict_univ] at ht2
    have h3 : ∀ᵐ x ∂(volume : Measure Vec3), ∀ i : Fin 3, u (x, t) i = ut (x, t) i :=
      ae_all_iff.mpr ht2
    filter_upwards [ht1, h3] with x hx1 hx2
    rw [hx1]
    funext i
    exact hx2 i
  have hset : MeasurableSet {z : Vec3 × ℝ | Rf z = ut z} := measurableSet_eq_fun hRfm hutm
  have hprod : volume.restrict ((univ : Set Vec3) ×ˢ Ioo t₀ t₁) =
      (volume.restrict (univ : Set Vec3)).prod (volume.restrict (Ioo t₀ t₁)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hRut : Rf =ᵐ[volume.restrict ((univ : Set Vec3) ×ˢ Ioo t₀ t₁)] ut := by
    rw [hprod, Filter.EventuallyEq, Measure.ae_prod_iff_ae_ae hset,
      Measure.ae_ae_comm (p := fun x t => Rf (x, t) = ut (x, t)) hset]
    simp only [Measure.restrict_univ]
    exact hslicesut
  exact hRut.trans hut.symm

end ESS
