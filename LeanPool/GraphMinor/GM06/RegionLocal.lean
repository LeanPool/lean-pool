/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.Defs
import LeanPool.GraphMinor.Surface.JordanDomain
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.GM11.Fan
import LeanPool.GraphMinor.GM11.PlaneFacts
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.Convex.PathConnected

/-!
# Local Accessibility of Regions in the Plane

This file proves the local plane-topological lemmas used to construct curves in regions of a proper
drawing on a closed disc:
- `locallyPathConnectedSpace_of_isClosedDiscSpace`, `isOpen_region`, `isPathConnected_region`,
  and `closure_sdiff_bd_eq`: regions of a drawing on a closed disc space are open and
  path-connected, and removing the disc boundary preserves their closure.
- `exists_curve_of_half_nbhd`: any half-disc neighborhood at a boundary point of a closed disc
  contains a radial entry curve starting at that boundary point.
- `exists_entry_path_of_spokes`: if at least two injective spokes meet at a point `c` in the plane,
  then any open set `R_open` off the drawing with `c ∈ closure R_open` is entered by a continuous
  curve starting at `c`.
- `exists_entry_path_of_one_spoke` and `exists_entry_path_of_zero_spokes`: the corresponding entry
  curve existence results when `1` or `0` spokes meet at `c`.
-/

public section

namespace GraphMinor.GM06

open Set Function Topology Metric GraphMinor.Surface unitInterval

universe u

/-! ## 1. Local Path-Connectivity of Closed Disc Spaces and Their Regions -/

instance locallyPathConnectedSpace_closedUnitDisc :
    LocallyPathConnectedSpace ClosedUnitDisc :=
  (convex_closedBall (0 : EuclideanPlane) 1).locallyPathConnectedSpace

theorem locallyPathConnectedSpace_of_isClosedDiscSpace {S : Type u} [TopologicalSpace S]
    (hDisc : IsClosedDiscSpace S) : LocallyPathConnectedSpace S := by
  obtain ⟨e⟩ := hDisc
  exact Homeomorph.locallyPathConnectedSpace e

theorem t2Space_of_isClosedDiscSpace {S : Type u} [TopologicalSpace S]
    (hDisc : IsClosedDiscSpace S) : T2Space S := by
  obtain ⟨e⟩ := hDisc
  exact e.symm.isEmbedding.t2Space

theorem isOpen_region {S : Type u} [TopologicalSpace S]
    (hDisc : IsClosedDiscSpace S) (G : Drawing S) {r : Set S} (hr : r ∈ G.R) :
    IsOpen r := by
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hDisc
  rcases hr with ⟨x, _, rfl⟩
  exact (isOpen_univ.sdiff G.isClosed_U).connectedComponentIn

theorem isPathConnected_region {S : Type u} [TopologicalSpace S]
    (hDisc : IsClosedDiscSpace S) (G : Drawing S) {r : Set S} (hr : r ∈ G.R) :
    IsPathConnected r := by
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hDisc
  have hopen : IsOpen r := isOpen_region hDisc G hr
  rcases hr with ⟨x, hx, rfl⟩
  exact hopen.isConnected_iff_isPathConnected.mp (isConnected_connectedComponentIn_iff.mpr hx)

theorem region_subset_of_isPreconnected {S : Type u} [TopologicalSpace S]
    (G : Drawing S) {r A : Set S} (hr : r ∈ G.R) (hA : IsPreconnected A)
    (hdisj : Disjoint A G.U) (hinter : (A ∩ r).Nonempty) :
    A ⊆ r := by
  rcases hr with ⟨x, _, rfl⟩
  rcases hinter with ⟨z, hzA, hzr⟩
  rw [connectedComponentIn_eq hzr]
  refine hA.subset_connectedComponentIn hzA ?_
  intro w hw
  exact ⟨mem_univ w, disjoint_left.mp hdisj hw⟩

theorem closure_sdiff_bd_eq {S : Type u} [TopologicalSpace S]
    (hDisc : IsClosedDiscSpace S) {r : Set S} (hr : IsOpen r) :
    closure (r \ bd S) = closure r := by
  apply Subset.antisymm (closure_mono sdiff_subset)
  obtain ⟨e⟩ := hDisc
  have hbd_img := image_bd_homeomorph e
  rw [bd_closedUnitDisc] at hbd_img
  intro p hp
  rw [_root_.mem_closure_iff] at hp ⊢
  intro V hV hpV
  obtain ⟨q, hqV, hqr⟩ := hp V hV hpV
  have hopen_sub : IsOpen (e ⁻¹' (V ∩ r)) := (hV.inter hr).preimage e.continuous
  rw [isOpen_induced_iff] at hopen_sub
  rcases hopen_sub with ⟨W, hW, hWeq⟩
  have hqW : (e.symm q).1 ∈ W := by
    have hmem : e.symm q ∈ Subtype.val ⁻¹' W := by
      rw [hWeq]
      simp [hqV, hqr]
    exact hmem
  have hcl : (e.symm q).1 ∈ closure (OpenUnitDisc : Set EuclideanPlane) := by
    rw [show closure (OpenUnitDisc : Set EuclideanPlane) = ClosedUnitDisc from
      closure_ball (0 : EuclideanPlane) one_ne_zero]
    exact (e.symm q).2
  obtain ⟨y, hyW, hyO⟩ := _root_.mem_closure_iff.mp hcl W hW hqW
  let y_disc : ClosedUnitDisc := ⟨y, Metric.ball_subset_closedBall hyO⟩
  have hy_pre : y_disc ∈ e ⁻¹' (V ∩ r) := by
    rw [← hWeq]
    exact hyW
  refine ⟨e y_disc, hy_pre.1, hy_pre.2, ?_⟩
  intro hbd
  rw [← hbd_img] at hbd
  rcases hbd with ⟨z, hz, hze⟩
  have hzy : z = y_disc := e.injective hze
  subst hzy
  have h1 : ‖y‖ < 1 := by simpa [OpenUnitDisc] using hyO
  have h2 : ‖y‖ = 1 := by simpa [UnitCircle, y_disc] using hz
  linarith

/-! ## 2. Radial Entry Curve in a Half-Disc Neighborhood -/

/-- Any half-disc neighborhood `(W ∩ Δ) \ discBd Δ ⊆ A` around a boundary point `p ∈ discBd Δ`
of a closed disc `Δ` contains a continuous curve starting at `p` that stays in `A` for all `t > 0`.
-/
theorem exists_curve_of_half_nbhd {S : Type u} [TopologicalSpace S]
    {Δ W A : Set S} (hΔ : IsClosedDisc Δ) (hW : IsOpen W)
    {p : S} (hp : p ∈ discBd Δ) (hpW : p ∈ W)
    (hsub : (W ∩ Δ) \ discBd Δ ⊆ A) :
    ∃ α : C(I, S), α 0 = p ∧ ∀ t : I, 0 < (t : ℝ) → α t ∈ A := by
  obtain ⟨φ⟩ := hΔ
  have hbd := disc_boundary Δ φ
  rw [hbd] at hp
  rcases hp with ⟨c, hc, rfl⟩
  let f : ClosedUnitDisc → S := fun x => (φ x).1
  have hf : Continuous f := continuous_subtype_val.comp φ.continuous
  have hfinj : Function.Injective f := fun x y h => φ.injective (Subtype.ext h)
  have hopen : IsOpen {x : ClosedUnitDisc | f x ∈ W} := hW.preimage hf
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen c hpW
  let ε : ℝ := min (δ / 2) (1 / 2)
  have hε_pos : 0 < ε := lt_min (half_pos hδ) (by norm_num)
  have hε_δ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  have hε_half : ε ≤ 1 / 2 := min_le_right _ _
  have hc_norm : ‖(c : EuclideanPlane)‖ = 1 := by simpa [UnitCircle] using hc
  have hg_mem : ∀ t : I, (1 - ε * (t : ℝ)) • (c : EuclideanPlane) ∈ ClosedUnitDisc := by
    intro t
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have h1 : 0 ≤ 1 - ε * (t : ℝ) := by nlinarith
    have h2 : 1 - ε * (t : ℝ) ≤ 1 := by nlinarith
    simp only [ClosedUnitDisc, Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg h1, hc_norm, mul_one]
    exact h2
  let g : I → ClosedUnitDisc := fun t => ⟨(1 - ε * (t : ℝ)) • (c : EuclideanPlane), hg_mem t⟩
  have hg_cont : Continuous g := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  refine ⟨⟨f ∘ g, hf.comp hg_cont⟩, ?_, ?_⟩
  · change f (g 0) = f c
    congr 1
    ext
    simp [g]
  · intro t ht
    refine hsub ⟨⟨?_, (φ (g t)).2⟩, ?_⟩
    · apply hball
      change dist ((1 - ε * (t : ℝ)) • (c : EuclideanPlane)) (c : EuclideanPlane) < δ
      have hdiff : (1 - ε * (t : ℝ)) • (c : EuclideanPlane) - (c : EuclideanPlane) =
          (- (ε * (t : ℝ))) • (c : EuclideanPlane) := by
        rw [sub_smul, one_smul, sub_sub_cancel_left, neg_smul]
      rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, hc_norm, mul_one]
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      have hnonneg : 0 ≤ ε * (t : ℝ) := mul_nonneg hε_pos.le ht0
      rw [abs_neg, abs_of_nonneg hnonneg]
      nlinarith
    · rw [hbd]
      rintro ⟨y, hy, hy_eq⟩
      have heq : y = g t := hfinj hy_eq
      have hy_norm : ‖(y : EuclideanPlane)‖ = 1 := by simpa [UnitCircle] using hy
      rw [heq] at hy_norm
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      have hpos : 0 ≤ 1 - ε * (t : ℝ) := by nlinarith
      have h_gt_norm : ‖(g t : EuclideanPlane)‖ = 1 - ε * (t : ℝ) := by
        simp [g, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos, hc_norm]
      linarith [mul_pos hε_pos ht]

/-! ## 3. Round Closed Discs in the Plane -/

private theorem exists_round_closedDisc {c : EuclideanPlane} {O : Set EuclideanPlane}
    (hO : IsOpen O) (hc : c ∈ O) :
    ∃ (D D' : Set EuclideanPlane) (ρ : ℝ),
      0 < ρ ∧ D = Metric.closedBall c ρ ∧ D' = Metric.ball c ρ ∧
      IsClosedDisc D ∧ IsOpen D' ∧ c ∈ D' ∧ D' ⊆ D ∧ D ⊆ O ∧ D \ D' = discBd D := by
  obtain ⟨ρ', hρ', hball⟩ := Metric.isOpen_iff.mp hO c hc
  let ρ : ℝ := ρ' / 2
  have hρ : 0 < ρ := half_pos hρ'
  let D : Set EuclideanPlane := Metric.closedBall c ρ
  let D' : Set EuclideanPlane := Metric.ball c ρ
  have hDO : D ⊆ O := (Metric.closedBall_subset_ball (half_lt_self hρ')).trans hball
  let g : EuclideanPlane → EuclideanPlane := fun x => c + ρ • x
  have hg : Continuous g := by fun_prop
  have hgin : ∀ x : EuclideanPlane, g x ∈ D ↔ x ∈ ClosedUnitDisc := by
    intro x
    simp only [g, D, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, ClosedUnitDisc,
      sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    exact ⟨fun h' => le_of_mul_le_mul_left (by simpa using h') hρ, fun h' => by nlinarith⟩
  have hgball : ∀ x : EuclideanPlane, g x ∈ D' ↔ x ∈ OpenUnitDisc := by
    intro x
    simp only [g, D', Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, OpenUnitDisc,
      sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    exact ⟨fun h' => lt_of_mul_lt_mul_left (by simpa using h') hρ.le, fun h' => by nlinarith⟩
  have hginj : Function.Injective g := by
    intro x y hxy
    exact smul_right_injective _ hρ.ne' (add_left_cancel hxy)
  let k : ClosedUnitDisc → D := fun x => ⟨g x.1, (hgin x.1).mpr x.2⟩
  have hk : Continuous k := Continuous.subtype_mk (hg.comp continuous_subtype_val) _
  have hkinj : Function.Injective k := fun x y hxy =>
    Subtype.ext (hginj (congrArg Subtype.val hxy))
  have hksurj : Function.Surjective k := by
    rintro ⟨y, hy⟩
    let x : EuclideanPlane := ρ⁻¹ • (y - c)
    have hgx : g x = y := by
      simp [g, x, smul_smul, mul_inv_cancel₀ hρ.ne']
    have hx : x ∈ ClosedUnitDisc := (hgin x).mp (hgx.symm ▸ hy)
    exact ⟨⟨x, hx⟩, Subtype.ext hgx⟩
  have : CompactSpace ClosedUnitDisc :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : EuclideanPlane) 1)
  let E : ClosedUnitDisc ≃ₜ D :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective k ⟨hkinj, hksurj⟩) hk
  have hbd := disc_boundary D E
  refine ⟨D, D', ρ, hρ, rfl, rfl, ⟨E⟩, Metric.isOpen_ball, Metric.mem_ball_self hρ,
    Metric.ball_subset_closedBall, hDO, ?_⟩
  rw [hbd]
  ext q
  constructor
  · rintro ⟨hqD, hqD'⟩
    obtain ⟨x, hx⟩ := E.surjective ⟨q, hqD⟩
    have hkx : g x.1 = q := congrArg Subtype.val hx
    refine ⟨x, ?_, hkx⟩
    have hle : ‖x.1‖ ≤ 1 := by simpa [ClosedUnitDisc] using x.2
    have hne : ¬ ‖x.1‖ < 1 := fun hlt =>
      hqD' (hkx ▸ (hgball x.1).mpr (by simpa [OpenUnitDisc] using hlt))
    have : ‖x.1‖ = 1 := le_antisymm hle (not_lt.mp hne)
    simpa [UnitCircle] using this
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(E x).2, fun hin => ?_⟩
    have h1 : ‖x.1‖ < 1 := by simpa [OpenUnitDisc] using (hgball x.1).mp hin
    have h2 : ‖x.1‖ = 1 := by simpa [UnitCircle] using hx
    linarith

/-! ## 4. Truncation of Spokes in the Plane -/

private theorem exists_spoke_truncation {sp : I → EuclideanPlane}
    (hc : Continuous sp) {D D' : Set EuclideanPlane}
    (hD : IsClosed D) (hD' : IsOpen D') (hsub : D' ⊆ D) (hbd : D \ D' = discBd D)
    (hv : sp 0 ∈ D') (hout : sp 1 ∉ D) :
    ∃ τ : I, 0 < τ ∧ τ < 1 ∧ (∀ t, t < τ → sp t ∈ D') ∧ sp τ ∈ discBd D := by
  have hC : IsCompact {t : I | sp t ∉ D'} := (hD'.isClosed_compl.preimage hc).isCompact
  obtain ⟨τ, hτ, hmin⟩ := hC.exists_isLeast ⟨1, fun h => hout (hsub h)⟩
  have hτ0 : 0 < τ := by
    refine unitInterval.pos_iff_ne_zero.mpr ?_
    rintro rfl
    exact hτ hv
  have hbefore : ∀ t, t < τ → sp t ∈ D' := fun t ht => by
    by_contra hcon
    exact absurd (hmin hcon) (not_le.mpr ht)
  have hτD : sp τ ∈ D := by
    have h1 : τ ∈ closure (Iio τ) := by
      rw [closure_Iio' (a := τ) ⟨0, hτ0⟩]
      exact mem_Iic.mpr le_rfl
    have h2 := map_mem_closure hc h1 (t := D) fun t ht => hsub (hbefore t ht)
    rwa [hD.closure_eq] at h2
  have hτ1 : τ < 1 := by
    refine lt_of_le_of_ne le_top ?_
    rintro rfl
    exact hout hτD
  exact ⟨τ, hτ0, hτ1, hbefore, hbd ▸ ⟨hτD, hτ⟩⟩

private theorem isLineWithEnds_spoke_piece {sp : I → EuclideanPlane}
    (hc : Continuous sp) (hinj : Function.Injective sp) {τ : I} (hτ : 0 < τ) :
    IsLineWithEnds (sp '' Icc 0 τ) (sp 0) (sp τ) := by
  let f : C(I, EuclideanPlane) := ⟨fun t => sp (t * τ), hc.comp (by fun_prop)⟩
  have hfinj : Function.Injective f := by
    intro s t h
    have h1 := hinj h
    have h2 : s.1 * τ.1 = t.1 * τ.1 := congrArg Subtype.val h1
    have hτ' : (τ : ℝ) ≠ 0 := ne_of_gt hτ
    exact Subtype.ext (mul_right_cancel₀ hτ' h2)
  have hr : range f = sp '' Icc 0 τ := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t * τ, ⟨bot_le, unitInterval.mul_le_right⟩, rfl⟩
    · rintro ⟨t, ⟨-, ht⟩, rfl⟩
      have hτ' : (0 : ℝ) < τ := hτ
      have ht' : t.1 ≤ τ.1 := ht
      refine ⟨⟨t.1 / τ.1, div_nonneg t.2.1 hτ'.le, (div_le_one hτ').mpr ht'⟩, ?_⟩
      change sp _ = _
      congr 1
      apply Subtype.ext
      change t.1 / τ.1 * τ.1 = t.1
      field_simp
  have hline := GM11.isLineWithEnds_range f hfinj
  rw [hr] at hline
  have h0 : f 0 = sp 0 := by simp [f]
  have h1 : f 1 = sp τ := by simp [f]
  rwa [h0, h1] at hline

/-! ## 5. Entry Curve for `≥ 2` Spokes (`exists_entry_path_of_spokes`) -/

/-- If `2 ≤ Fintype.card ι` injective spokes meet at `c` and cover `U_full` outside a closed set
`Bad` missing `c`, then any open set `R_open ⊆ U_fullᶜ` with `c ∈ closure R_open` has a preconnected
subset `P ⊆ U_fullᶜ` meeting `R_open` and a curve `α` starting at `c` with `α t ∈ P` for `t > 0`. -/
theorem exists_entry_path_of_spokes
    {ι : Type*} [Fintype ι] (h2 : 2 ≤ Fintype.card ι)
    {c : EuclideanPlane} {U_full R_open : Set EuclideanPlane}
    (_hR_open : IsOpen R_open) (hR_sub : R_open ⊆ U_fullᶜ) (hc_cl : c ∈ closure R_open)
    (Bad : Set EuclideanPlane) (hBad : IsClosed Bad) (hcBad : c ∉ Bad)
    (sp : ι → I → EuclideanPlane)
    (hsp_cont : ∀ i, Continuous (sp i))
    (hsp_zero : ∀ i, sp i 0 = c)
    (hsp_inj : ∀ i, Function.Injective (sp i))
    (hsp_disj : ∀ i j, i ≠ j → ∀ s t : I, 0 < s → 0 < t → sp i s = sp j t → s = 1 ∧ t = 1)
    (hsp_sub : ∀ i, range (sp i) ⊆ U_full)
    (hU_cover : U_full ⊆ Bad ∪ ⋃ i, range (sp i)) :
    ∃ (P : Set EuclideanPlane) (α : C(I, EuclideanPlane)),
      IsPreconnected P ∧ Disjoint P U_full ∧ (P ∩ R_open).Nonempty ∧
      α 0 = c ∧ ∀ t : I, 0 < (t : ℝ) → α t ∈ P := by
  classical
  have hmid_fin : (range fun i : ι => sp i 1).Finite := finite_range _
  have hcmid : c ∉ range fun i : ι => sp i 1 := by
    rintro ⟨i, hi⟩
    have h01 : (1 : I) = 0 := hsp_inj i (hi.trans (hsp_zero i).symm)
    exact one_ne_zero (congrArg Subtype.val h01)
  have hO : IsOpen (Bad ∪ range fun i : ι => sp i 1)ᶜ :=
    (hBad.union hmid_fin.isClosed).isOpen_compl
  have hcO : c ∈ (Bad ∪ range fun i : ι => sp i 1)ᶜ := by
    rintro (h | h)
    · exact hcBad h
    · exact hcmid h
  obtain ⟨D, D', _, _, _, _, hD, hD', hcD', hD'D, hDO, hbdD⟩ :=
    exists_round_closedDisc hO hcO
  have hDc : IsClosed D := hD.isClosed
  have htrunc : ∀ i : ι, ∃ τ : I, 0 < τ ∧ τ < 1 ∧ (∀ t, t < τ → sp i t ∈ D') ∧
      sp i τ ∈ discBd D := fun i =>
    exists_spoke_truncation (hsp_cont i) hDc hD' hD'D hbdD (by rw [hsp_zero]; exact hcD')
      fun h => hDO h (Or.inr ⟨i, rfl⟩)
  choose τ hτ0 hτ1 hτb hτp using htrunc
  let J : ι → Set EuclideanPlane := fun i => sp i '' Icc 0 (τ i)
  let q : ι → EuclideanPlane := fun i => sp i (τ i)
  have hbdD' : Disjoint D' (discBd D) := by
    rw [← hbdD]
    exact Set.disjoint_left.mpr fun x hx hx' => hx'.2 hx
  have hcJ : ∀ i, c ∈ J i := fun i => ⟨0, ⟨le_rfl, bot_le⟩, hsp_zero i⟩
  have hline : ∀ i, IsLineWithEnds (J i) c (q i) := fun i => by
    have := isLineWithEnds_spoke_piece (hsp_cont i) (hsp_inj i) (hτ0 i)
    rwa [hsp_zero] at this
  have hsub : ∀ i, J i ⊆ D := by
    rintro i _ ⟨t, ht, rfl⟩
    rcases ht.2.eq_or_lt with rfl | hlt
    · exact discBd_subset _ (hτp i)
    · exact hD'D (hτb i t hlt)
  have hbd : ∀ i, J i ∩ discBd D = {q i} := by
    intro i
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hx⟩
      rcases ht.2.eq_or_lt with rfl | hlt
      · rfl
      · exact absurd hx (Set.disjoint_left.mp hbdD' (hτb i t hlt))
    · rintro rfl
      exact ⟨⟨τ i, ⟨bot_le, le_rfl⟩, rfl⟩, hτp i⟩
  have hJJ : ∀ i j, i ≠ j → J i ∩ J j = {c} := by
    intro i j hij
    ext x
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, ⟨t, ht, hst⟩⟩
      by_cases hs0 : 0 < s
      · by_cases ht0 : 0 < t
        · have := (hsp_disj i j hij s t hs0 ht0 hst.symm).1
          have hs1 : s < 1 := lt_of_le_of_lt hs.2 (hτ1 i)
          exact absurd this hs1.ne
        · have ht' : t = 0 := le_antisymm (not_lt.mp ht0) bot_le
          rw [← hst, ht', hsp_zero]
          rfl
      · have hs' : s = 0 := le_antisymm (not_lt.mp hs0) bot_le
        rw [hs', hsp_zero]
        rfl
    · rintro rfl
      exact ⟨hcJ i, hcJ j⟩
  have hne : ∀ i, c ≠ q i := by
    intro i h
    have h0 : τ i = 0 := hsp_inj i (h.symm.trans (hsp_zero i).symm)
    exact (hτ0 i).ne' h0
  have hcD : c ∉ discBd D := fun h => Set.disjoint_left.mp hbdD' hcD' h
  obtain ⟨next, Q, hF⟩ := GM11.exists_fanInv hD hline hsub hbd hJJ hne hcD
    (Finset.univ : Finset ι) (by rwa [Finset.card_univ])
  let K : Set EuclideanPlane := Bad ∪ ⋃ i : ι, sp i '' Ici (τ i)
  have hKclosed : IsClosed K :=
    hBad.union (isClosed_iUnion_of_finite fun i =>
      (isClosed_Ici.isCompact.image (hsp_cont i)).isClosed)
  have hcK : c ∉ K := by
    rintro (h | h)
    · exact hcBad h
    · obtain ⟨i, ⟨t, ht, htc⟩⟩ := mem_iUnion.mp h
      have ht0 : t = 0 := hsp_inj i (htc.trans (hsp_zero i).symm)
      subst ht0
      exact not_le.mpr (hτ0 i) ht
  have hUsub : U_full ⊆ K ∪ ⋃ i, J i := by
    intro x hx
    rcases hU_cover hx with hxBad | hxsp
    · exact Or.inl (Or.inl hxBad)
    · obtain ⟨i, ⟨t, rfl⟩⟩ := mem_iUnion.mp hxsp
      rcases le_total t (τ i) with ht | ht
      · exact Or.inr (mem_iUnion.mpr ⟨i, ⟨t, ⟨bot_le, ht⟩, rfl⟩⟩)
      · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨i, ⟨t, ht, rfl⟩⟩))
  have hJU : ∀ i, J i ⊆ U_full := by
    rintro i _ ⟨t, _, rfl⟩
    exact hsp_sub i ⟨t, rfl⟩
  obtain ⟨P, W, hW, hcW, hWD', hP⟩ :=
    GM11.exists_sector_sets hF hD' hcD' hcJ hKclosed hcK
  have hWbd : Disjoint W (discBd D) := hbdD'.mono_left hWD'
  have hWD : W ⊆ D := hWD'.trans hD'D
  obtain ⟨c₁, -⟩ := GM11.sector_sets_props hF hW hWD hWbd
    (fun k hk => (hF.disc k hk).isClosed)
    (fun k hk => ⟨(hP k hk).2.2.2.2.1, (hP k hk).2.2.2.2.2⟩)
  have mem : ∀ k : ι, k ∈ (Finset.univ : Finset ι) := Finset.mem_univ
  have hiU : (⋃ i ∈ (Finset.univ : Finset ι), J i) ⊆ U_full :=
    iUnion₂_subset fun i _ => hJU i
  have hcbd : ∀ k, c ∈ discBd (Q k) := by
    intro k
    obtain ⟨B, -, hb⟩ := hF.bd k (mem k)
    exact hb ▸ Or.inl (Or.inl (hcJ k))
  have hdisjU : ∀ k, Disjoint (P k) U_full := by
    intro k
    obtain ⟨-, hPQ, hPbd, hPK, -, -⟩ := hP k (mem k)
    refine Set.disjoint_left.mpr fun x hx hxU => ?_
    obtain ⟨B, -, hb⟩ := hF.bd k (mem k)
    have hxbd : x ∉ discBd (Q k) := Set.disjoint_left.mp hPbd hx
    rw [hb] at hxbd
    rcases hUsub hxU with hxK | hxJ
    · exact Set.disjoint_left.mp hPK hx hxK
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hxJ
      by_cases hik : i = k
      · exact hxbd (Or.inl (Or.inl (hik ▸ hi)))
      · by_cases hin : i = next k
        · exact hxbd (Or.inl (Or.inr (hin ▸ hi)))
        · rcases hF.off k (mem k) i (mem i) hik hin ⟨hi, hPQ hx⟩ with h | h
          · exact hxbd (Or.inl (Or.inl (h ▸ hcJ k)))
          · have := hF.edge k (mem k) ⟨hPQ hx, h⟩
            rw [hb] at this
            exact hxbd this
  obtain ⟨z, hzW, hzR⟩ := mem_closure_iff.mp hc_cl W hW hcW
  have hzU : z ∉ U_full := hR_sub hzR
  obtain ⟨k, -, hzk⟩ := mem_iUnion₂.mp (c₁ ⟨hzW, fun h => hzU (hiU h)⟩)
  obtain ⟨α, hα0, hαP⟩ := exists_curve_of_half_nbhd (hF.disc k (mem k)) hW (hcbd k) hcW
    (hP k (mem k)).2.2.2.2.1
  exact ⟨P k, α, (hP k (mem k)).1, hdisjU k, ⟨z, hzk, hzR⟩, hα0, hαP⟩

/-! ## 6. Entry Curve for `1` Spoke (`exists_entry_path_of_one_spoke`) -/

private theorem exists_one_spoke_connector
    {c : EuclideanPlane} {U_full : Set EuclideanPlane}
    (Bad : Set EuclideanPlane) (hBad : IsClosed Bad) (hcBad : c ∉ Bad)
    (sp₀ : I → EuclideanPlane) (hsp_cont : Continuous sp₀) (hsp_zero : sp₀ 0 = c)
    (hsp_inj : Function.Injective sp₀) (hsp_sub : range sp₀ ⊆ U_full)
    (hU_cover : U_full ⊆ Bad ∪ range sp₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : EuclideanPlane,
      x ∈ Metric.ball c δ → x ∉ U_full → y ∈ Metric.ball c δ → y ∉ U_full →
      ∃ C : Set EuclideanPlane, IsPathConnected C ∧ Disjoint C U_full ∧
        x ∈ C ∧ y ∈ C ∧ C ⊆ Metric.ball c ε := by
  have hcmid : c ≠ sp₀ 1 := fun h =>
    one_ne_zero (congrArg Subtype.val (hsp_inj (h.symm.trans hsp_zero.symm)))
  have hO : IsOpen (Bad ∪ {sp₀ 1})ᶜ := (hBad.union isClosed_singleton).isOpen_compl
  have hcO : c ∈ (Bad ∪ {sp₀ 1})ᶜ := by
    rintro (h | h)
    · exact hcBad h
    · exact hcmid (mem_singleton_iff.mp h)
  obtain ⟨ρ', hρ', hball⟩ := Metric.isOpen_iff.mp hO c hcO
  let ρ₀ : ℝ := min (ρ' / 2) ε
  have hρ₀ : 0 < ρ₀ := lt_min (half_pos hρ') hε
  have hCB : Metric.closedBall c ρ₀ ⊆ (Bad ∪ {sp₀ 1})ᶜ :=
    (Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ'))).trans
      hball
  let D : Set EuclideanPlane := Metric.closedBall c ρ₀
  let D' : Set EuclideanPlane := Metric.ball c ρ₀
  have hC₁ : IsCompact {t : I | sp₀ t ∉ D'} :=
    (Metric.isOpen_ball.isClosed_compl.preimage hsp_cont).isCompact
  have h1_out : sp₀ 1 ∉ D' := fun h => hCB (Metric.ball_subset_closedBall h) (Or.inr rfl)
  obtain ⟨a, ha, hamin⟩ := hC₁.exists_isLeast ⟨1, h1_out⟩
  have ha0 : 0 < a := by
    refine unitInterval.pos_iff_ne_zero.mpr ?_
    rintro rfl
    exact ha (by rw [hsp_zero]; exact Metric.mem_ball_self hρ₀)
  have hbefore : ∀ t, t < a → sp₀ t ∈ D' := fun t ht => by
    by_contra hcon
    exact absurd (hamin hcon) (not_le.mpr ht)
  have haD : sp₀ a ∈ D := by
    have h1 : a ∈ closure (Iio a) := by
      rw [closure_Iio' (a := a) ⟨0, ha0⟩]
      exact mem_Iic.mpr le_rfl
    have h2 := map_mem_closure hsp_cont h1 (t := D) fun t ht =>
      Metric.ball_subset_closedBall (hbefore t ht)
    rwa [Metric.isClosed_closedBall.closure_eq] at h2
  have ha_sph : sp₀ a ∈ Metric.sphere c ρ₀ := by
    rw [← Metric.closedBall_sdiff_ball]
    exact ⟨haD, ha⟩
  let f : C(I, EuclideanPlane) := ⟨fun s => sp₀ (s * a), hsp_cont.comp (by fun_prop)⟩
  have hfinj : Function.Injective f := by
    intro s t h
    have h1 := hsp_inj h
    have h2 : s.1 * a.1 = t.1 * a.1 := congrArg Subtype.val h1
    have ha' : (a : ℝ) ≠ 0 := ne_of_gt ha0
    exact Subtype.ext (mul_right_cancel₀ ha' h2)
  have hJline : IsLine (range f) :=
    ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective f hfinj)
      f.continuous.rangeFactorization⟩
  have hJ_eq : range f = sp₀ '' Icc 0 a := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s * a, ⟨bot_le, unitInterval.mul_le_right⟩, rfl⟩
    · rintro ⟨t, ⟨-, ht⟩, rfl⟩
      have ha' : (0 : ℝ) < a := ha0
      have ht' : t.1 ≤ a.1 := ht
      refine ⟨⟨t.1 / a.1, div_nonneg t.2.1 ha'.le, (div_le_one ha').mpr ht'⟩, ?_⟩
      change sp₀ _ = _
      congr 1
      apply Subtype.ext
      change t.1 / a.1 * a.1 = t.1
      field_simp
  let M : Set EuclideanPlane := D ∩ (sp₀ '' Ici a)
  have hMcpt : IsCompact M :=
    ( isCompact_closedBall c ρ₀ ).inter_right (isClosed_Ici.isCompact.image hsp_cont).isClosed
  let K : Set EuclideanPlane := Metric.sphere c ρ₀ ∪ M
  have hKcpt : IsCompact K := (isCompact_sphere c ρ₀).union hMcpt
  have hKJ : K ∩ range f = {sp₀ a} := by
    rw [hJ_eq]
    ext z
    constructor
    · rintro ⟨hzK, t, ht, rfl⟩
      rcases eq_or_lt_of_le ht.2 with rfl | hlt
      · rfl
      · rcases hzK with hz_sph | ⟨_, s, hs, hst⟩
        · exact absurd hz_sph (ne_of_lt (Metric.mem_ball.mp (hbefore t hlt)))
        · have hts : s = t := hsp_inj hst
          exact absurd (hts ▸ hs) (not_le.mpr hlt)
    · rintro rfl
      exact ⟨Or.inl ha_sph, ⟨a, ⟨bot_le, le_rfl⟩, rfl⟩⟩
  have hKJconn : IsPreconnected (K ∩ range f) := by
    rw [hKJ]
    exact isPreconnected_singleton
  have hcK : c ∉ K := by
    rintro (h_sph | ⟨_, t, ht, htc⟩)
    · have : dist c c = ρ₀ := h_sph
      rw [dist_self] at this
      exact hρ₀.ne this
    · have ht0 : t = 0 := hsp_inj (htc.trans hsp_zero.symm)
      subst ht0
      exact not_le.mpr ha0 ht
  obtain ⟨ρ₂, hρ₂, hballK⟩ := Metric.isOpen_iff.mp hKcpt.isClosed.isOpen_compl c hcK
  let δ : ℝ := min ρ₂ ρ₀
  have hδ : 0 < δ := lt_min hρ₂ hρ₀
  have hsmallK : Metric.ball c δ ⊆ Kᶜ :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hballK
  have hsmall₀ : Metric.ball c δ ⊆ D' :=
    Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨δ, hδ, fun x y hx hxU hy hyU => ?_⟩
  have hoff : ∀ z : EuclideanPlane, z ∉ U_full → z ∉ range f := by
    rintro z hz ⟨s, rfl⟩
    exact hz (hsp_sub ⟨s * a, rfl⟩)
  have hxnot : x ∉ K ∪ range f := fun h => h.elim (hsmallK hx) (hoff x hxU)
  have hynot : y ∉ K ∪ range f := fun h => h.elim (hsmallK hy) (hoff y hyU)
  have hsameK : y ∈ connectedComponentIn Kᶜ x :=
    (convex_ball c δ).isPreconnected.subset_connectedComponentIn hx hsmallK hy
  have hsameJ : y ∈ connectedComponentIn (range f)ᶜ x :=
    (isPreconnected_compl_of_isLine hJline).subset_connectedComponentIn
      (fun h => hxnot (Or.inr h)) subset_rfl (fun h => hynot (Or.inr h))
  have hsame := janiszewski_plane hKcpt (isCompact_range f.continuous) hKJconn
    hxnot hynot hsameK hsameJ
  let Cc : Set EuclideanPlane := connectedComponentIn (K ∪ range f)ᶜ x
  have hCc_open : IsOpen Cc :=
    (hKcpt.union (isCompact_range f.continuous)).isClosed.isOpen_compl.connectedComponentIn
  have hCc_conn : IsConnected Cc := isConnected_connectedComponentIn_iff.mpr hxnot
  have hCc_pc : IsPathConnected Cc := hCc_open.isConnected_iff_isPathConnected.mp hCc_conn
  have hCc_sub : Cc ⊆ (K ∪ range f)ᶜ := connectedComponentIn_subset _ _
  have hxCc : x ∈ Cc := mem_connectedComponentIn hxnot
  have hCc_ball : Cc ⊆ D' := by
    refine hCc_conn.isPreconnected.subset_left_of_subset_union Metric.isOpen_ball
      (show IsOpen Dᶜ from Metric.isClosed_closedBall.isOpen_compl) ?_ ?_ ⟨x, hxCc, hsmall₀ hx⟩
    · exact disjoint_left.mpr fun z hz h' => h' (Metric.ball_subset_closedBall hz)
    · intro z hz
      by_cases hzb : z ∈ D'
      · exact Or.inl hzb
      · refine Or.inr fun hzc => ?_
        have h1 : dist z c = ρ₀ := le_antisymm hzc (not_lt.mp hzb)
        exact hCc_sub hz (Or.inl (Or.inl h1))
  refine ⟨Cc, hCc_pc, ?_, hxCc, hsame, hCc_ball.trans (Metric.ball_subset_ball (min_le_right _ _))⟩
  refine disjoint_left.mpr fun z hz hzU => ?_
  have hzD : z ∈ D := Metric.ball_subset_closedBall (hCc_ball hz)
  rcases hU_cover hzU with hzBad | ⟨t, rfl⟩
  · exact hCB hzD (Or.inl hzBad)
  · rcases le_or_gt t a with hta | hta
    · refine hCc_sub hz (Or.inr ?_)
      rw [hJ_eq]
      exact ⟨t, ⟨bot_le, hta⟩, rfl⟩
    · exact hCc_sub hz (Or.inl (Or.inr ⟨hzD, t, hta.le, rfl⟩))

/-- Entry curve when `1` injective spoke meets at `c`. -/
theorem exists_entry_path_of_one_spoke
    {c : EuclideanPlane} {U_full R_open : Set EuclideanPlane}
    (hR_sub : R_open ⊆ U_fullᶜ) (hc_cl : c ∈ closure R_open)
    (Bad : Set EuclideanPlane) (hBad : IsClosed Bad) (hcBad : c ∉ Bad)
    (sp₀ : I → EuclideanPlane) (hsp_cont : Continuous sp₀) (hsp_zero : sp₀ 0 = c)
    (hsp_inj : Function.Injective sp₀) (hsp_sub : range sp₀ ⊆ U_full)
    (hU_cover : U_full ⊆ Bad ∪ range sp₀) :
    ∃ (P : Set EuclideanPlane) (α : C(I, EuclideanPlane)),
      IsPreconnected P ∧ Disjoint P U_full ∧ (P ∩ R_open).Nonempty ∧
      α 0 = c ∧ ∀ t : I, 0 < (t : ℝ) → α t ∈ P := by
  classical
  have hε : ∀ n : ℕ, (0 : ℝ) < (1 / 2) ^ n := fun _ => by positivity
  choose δ hδ hconn using fun n =>
    exists_one_spoke_connector Bad hBad hcBad sp₀ hsp_cont hsp_zero hsp_inj hsp_sub hU_cover (hε n)
  let η : ℕ → ℝ := fun n => min (δ n / 2) ((1 / 2) ^ n)
  have hη : ∀ n, 0 < η n := fun n => lt_min (half_pos (hδ n)) (hε n)
  let e : ℕ → ℝ := fun n => Nat.casesOn n (η 0) fun k => min (η k) (η (k + 1))
  have he : ∀ n, 0 < e n := by
    intro n; cases n with
    | zero => exact hη 0
    | succ k => exact lt_min (hη k) (hη (k + 1))
  have heη : ∀ n, e n ≤ η n := by
    intro n; cases n with
    | zero => exact le_rfl
    | succ k => exact min_le_right _ _
  have heη' : ∀ n, e (n + 1) ≤ η n := fun n => min_le_left _ _
  choose y hyR hyd using fun n => Metric.mem_closure_iff.mp hc_cl (e n) (he n)
  have hyU : ∀ n, y n ∉ U_full := fun n => hR_sub (hyR n)
  have hy_ball : ∀ n, y n ∈ Metric.ball c (δ n) := by
    intro n
    rw [Metric.mem_ball, dist_comm]
    have h1 := hyd n
    have h2 := heη n
    have h3 : η n ≤ δ n / 2 := min_le_left _ _
    have h4 := hδ n
    linarith
  have hy_ball' : ∀ n, y (n + 1) ∈ Metric.ball c (δ n) := by
    intro n
    rw [Metric.mem_ball, dist_comm]
    have h1 := hyd (n + 1)
    have h2 := heη' n
    have h3 : η n ≤ δ n / 2 := min_le_left _ _
    have h4 := hδ n
    linarith
  have hstep : ∀ n, ∃ q : Path (y n) (y (n + 1)),
      (∀ t, q t ∉ U_full) ∧ ∀ t, dist (q t) c ≤ (1 / 2) ^ n := by
    intro n
    obtain ⟨C, hC_pc, hC_disj, hxC, hyC, hC_ball⟩ :=
      hconn n (y n) (y (n + 1)) (hy_ball n) (hyU n) (hy_ball' n) (hyU (n + 1))
    obtain ⟨q, hq⟩ := hC_pc.joinedIn _ hxC _ hyC
    refine ⟨q, fun t => disjoint_left.mp hC_disj (hq t), fun t => ?_⟩
    exact le_of_lt (Metric.mem_ball.mp (hC_ball (hq t)))
  choose q hqU hqd using hstep
  let f := complexPlane.toHomeomorph.symm
  have hf_isom : ∀ x z : EuclideanPlane, dist (f x) (f z) = dist x z :=
    fun x z => complexPlane.symm.dist_map x z
  let P_seq : ℕ → I → ℂ := fun n t => f (q n t)
  let r_bd : ℕ → ℝ := fun n => (1 / 2) ^ n
  have hr : Filter.Tendsto r_bd Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hPc : ∀ n, Continuous (P_seq n) := fun n => f.continuous.comp (q n).continuous
  have hlink : ∀ n, P_seq n 1 = P_seq (n + 1) 0 := fun n => by
    simp only [P_seq]
    rw [(q n).target, (q (n + 1)).source]
  have hclose : ∀ n t, dist (P_seq n t) (f c) ≤ r_bd n := fun n t => by
    rw [hf_isom]
    exact hqd n t
  obtain ⟨γ₀, hγ₀c, hγ₀0, hγ₀1, hγ₀U⟩ := exists_path_of_tendsto hPc hlink hr hclose
  let β : C(I, EuclideanPlane) :=
    ⟨fun t => complexPlane.toHomeomorph (γ₀ t), complexPlane.toHomeomorph.continuous.comp hγ₀c⟩
  have hβ0 : β 0 = y 0 := by
    change complexPlane.toHomeomorph (γ₀ 0) = y 0
    rw [hγ₀0]
    simp [P_seq, f]
  have hβ1 : β 1 = c := by
    change complexPlane.toHomeomorph (γ₀ 1) = c
    rw [hγ₀1]
    simp [f]
  have hβ_notU : ∀ t : I, t ≠ 1 → β t ∉ U_full := by
    intro t ht
    obtain ⟨n, s, hs⟩ := hγ₀U t ht
    have hbt : β t = q n s := by
      change complexPlane.toHomeomorph (γ₀ t) = q n s
      rw [hs]
      simp [P_seq, f]
    rw [hbt]
    exact hqU n s
  have h_ioo_conn : IsPreconnected {s : I | s ≠ 1} := by
    have h_eq : {s : I | s ≠ 1} = Ico (0 : I) 1 := by
      ext s
      simp only [mem_ofPred_eq, mem_Ico]
      exact ⟨fun h => ⟨bot_le, lt_of_le_of_ne le_top h⟩, fun h => h.2.ne⟩
    rw [h_eq]
    exact isPreconnected_Ico
  let P : Set EuclideanPlane := β '' {s : I | s ≠ 1}
  have hP_conn : IsPreconnected P := h_ioo_conn.image β β.continuous.continuousOn
  have hP_disj : Disjoint P U_full := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨s, hs, rfl⟩
    exact hβ_notU s hs
  have hy0_mem : y 0 ∈ P := ⟨0, zero_ne_one, hβ0⟩
  refine ⟨P, ⟨fun t => β (σ t), β.continuous.comp unitInterval.continuous_symm⟩,
    hP_conn, hP_disj, ⟨y 0, hy0_mem, hyR 0⟩, ?_, ?_⟩
  · change β (σ 0) = c
    simpa using hβ1
  · intro t ht
    refine ⟨σ t, ?_, rfl⟩
    intro h
    have h1 : 1 - (t : ℝ) = 1 := congrArg Subtype.val h
    linarith

/-! ## 7. Entry Curve for `0` Spokes (`exists_entry_path_of_zero_spokes`) -/

/-- Entry curve when `0` spokes meet at `c` (so `U_full \ {c} ⊆ Bad`). -/
theorem exists_entry_path_of_zero_spokes
    {c : EuclideanPlane} {U_full R_open : Set EuclideanPlane}
    (hR_sub : R_open ⊆ U_fullᶜ) (hc_cl : c ∈ closure R_open) (hcU : c ∈ U_full)
    (Bad : Set EuclideanPlane) (hBad : IsClosed Bad) (hcBad : c ∉ Bad)
    (hU_cover : U_full \ {c} ⊆ Bad) :
    ∃ (P : Set EuclideanPlane) (α : C(I, EuclideanPlane)),
      IsPreconnected P ∧ Disjoint P U_full ∧ (P ∩ R_open).Nonempty ∧
      α 0 = c ∧ ∀ t : I, 0 < (t : ℝ) → α t ∈ P := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hBad.isOpen_compl c hcBad
  obtain ⟨z, hz_ball, hzR⟩ :=
    mem_closure_iff.mp hc_cl (Metric.ball c δ) Metric.isOpen_ball (Metric.mem_ball_self hδ)
  have hzc : z ≠ c := fun h => hR_sub hzR (h ▸ hcU)
  let α : C(I, EuclideanPlane) := ⟨fun t => (1 - (t : ℝ)) • c + (t : ℝ) • z, by fun_prop⟩
  let P : Set EuclideanPlane := α '' Ioc (0 : I) 1
  have hP_conn : IsPreconnected P := isPreconnected_Ioc.image α α.continuous.continuousOn
  have hα0 : α 0 = c := by simp [α]
  have hα1 : α 1 = z := by simp [α]
  refine ⟨P, α, hP_conn, ?_, ⟨z, ⟨1, ⟨zero_lt_one, le_rfl⟩, hα1⟩, hzR⟩, hα0, ?_⟩
  · refine disjoint_left.mpr ?_
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩ hxU
    have ht_pos : 0 < (t : ℝ) := ht0
    have h_ne_c : α t ≠ c := by
      intro heq
      have hdiff : (t : ℝ) • (z - c) = 0 := by
        calc (t : ℝ) • (z - c)
          _ = ((1 - (t : ℝ)) • c + (t : ℝ) • z) - c := by
            rw [smul_sub, sub_smul, one_smul]
            abel
          _ = α t - c := rfl
          _ = 0 := sub_eq_zero.mpr heq
      rcases smul_eq_zero.mp hdiff with h0 | h0
      · exact ht_pos.ne' h0
      · exact hzc (sub_eq_zero.mp h0)
    have h_in_ball : α t ∈ Metric.ball c δ := by
      have hconv := convex_ball c δ (Metric.mem_ball_self hδ) hz_ball
        (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel 1 (t : ℝ))
      exact hconv
    exact hball h_in_ball (hU_cover ⟨hxU, h_ne_c⟩)
  · intro t ht
    exact ⟨t, ⟨ht, le_top⟩, rfl⟩

end GraphMinor.GM06
