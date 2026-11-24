/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Forest
import LeanPool.GraphMinor.GM11.PlaneFacts

/-!
# The neighbourhood of a leaf

Let `v` be a vertex of a drawing in a closed surface that is an end of just one edge `e`, and let
`e` not be a loop. Then `v` has an open neighbourhood `Z` such that any two points of `Z - U(Γ)` lie
in one connected subset of `Σ - U(Γ)` (`exists_leaf_nbhd`). So only one region reaches `v`.

The proof works in a chart. Let `D` be a small round disc around `v`. Let `J` be the end piece of
`e` from its last entry into `D` to `v`, and let `K` be the union of the circle `bd(D)` with the
rest of `e` in `D`. Then `J` is an arc, so it does not separate the plane, and points near `v` lie
in one component of the complement of `K`, as `K` misses a small ball around `v`. Moreover `J ∩ K`
is one point. Janiszewski's theorem now says that `J ∪ K` does not separate points near `v`, and the
component of its complement stays inside `D`.
-/

public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The affine map of the unit interval onto a closed subinterval. -/
theorem exists_reparam {a b : unitInterval} (hab : a < b) :
    ∃ ρ : unitInterval → unitInterval, Continuous ρ ∧ Function.Injective ρ ∧
      range ρ = Icc a b ∧ ρ 0 = a ∧ ρ 1 = b := by
  have habR : (a : ℝ) < b := hab
  have hρmem : ∀ u : unitInterval, (a : ℝ) + u.1 * (b - a) ∈ Set.Icc (0 : ℝ) 1 := by
    intro u
    have hu₀ := u.2.1
    have hu₁ := u.2.2
    have ha' := a.2.1
    have hb' := b.2.2
    constructor
    · have : 0 ≤ u.1 * ((b : ℝ) - a) := mul_nonneg hu₀ (by linarith)
      linarith
    · have : u.1 * ((b : ℝ) - a) ≤ 1 * ((b : ℝ) - a) :=
        mul_le_mul_of_nonneg_right hu₁ (by linarith)
      linarith
  let ρ : unitInterval → unitInterval := fun u => ⟨(a : ℝ) + u.1 * (b - a), hρmem u⟩
  refine ⟨ρ, ?_, ?_, ?_, Subtype.ext (by simp [ρ]), Subtype.ext (by simp [ρ])⟩
  · refine Continuous.subtype_mk ?_ _
    fun_prop
  · intro u v h
    have h₁ : (a : ℝ) + u.1 * (b - a) = a + v.1 * (b - a) := congrArg Subtype.val h
    have hd : ((b : ℝ) - a) ≠ 0 := by linarith
    exact Subtype.ext (mul_right_cancel₀ hd (add_left_cancel h₁))
  · ext t
    constructor
    · rintro ⟨u, rfl⟩
      have hu₀ := u.2.1
      have hu₁ := u.2.2
      constructor
      · have : 0 ≤ u.1 * ((b : ℝ) - a) := mul_nonneg hu₀ (by linarith)
        exact Subtype.mk_le_mk.mpr (by linarith)
      · have : u.1 * ((b : ℝ) - a) ≤ 1 * ((b : ℝ) - a) :=
          mul_le_mul_of_nonneg_right hu₁ (by linarith)
        exact Subtype.mk_le_mk.mpr (by linarith)
    · intro ht
      have ht₁ : (a : ℝ) ≤ t := ht.1
      have ht₂ : (t : ℝ) ≤ b := ht.2
      have hd : (0 : ℝ) < b - a := by linarith
      have hu : ((t : ℝ) - a) / (b - a) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).mpr (by linarith)⟩
      refine ⟨⟨_, hu⟩, Subtype.ext ?_⟩
      change (a : ℝ) + ((t : ℝ) - a) / (b - a) * (b - a) = t
      field_simp
      ring

variable [T2Space S]

private theorem drawing_off_leaf_closed (Γ : Drawing S) {e : Set S} {v : S}
    (hv : v ∈ closure e) (hleaf : ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f) :
    let Bad : Set S := (Γ.V \ {v}) ∪ ⋃ g ∈ Γ.E \ {e}, closure g
    IsClosed Bad ∧ v ∉ Bad ∧ (∀ x ∈ Γ.U, x ∈ Bad ∨ x ∈ closure e) := by
  intro Bad
  have hBad : IsClosed Bad :=
    (Γ.finite_V.subset sdiff_subset).isClosed.union
      ((Γ.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)
  have hvBad : v ∉ Bad := by
    rintro (h | h)
    · exact h.2 rfl
    · obtain ⟨g, ⟨hg, hge⟩, hvg⟩ := mem_iUnion₂.mp h
      exact hleaf g hg hge hvg
  have hUsub : ∀ x ∈ Γ.U, x ∈ Bad ∨ x ∈ closure e := by
    intro x hx
    rw [Γ.U_eq] at hx
    rcases hx with hx | hx
    · by_cases hxv : x = v
      · exact Or.inr (hxv ▸ hv)
      · exact Or.inl (Or.inl ⟨hx, hxv⟩)
    · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp hx
      by_cases hge : g = e
      · exact Or.inr (hge ▸ hxg)
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨g, ⟨hg, hge⟩, hxg⟩))
  exact ⟨hBad, hvBad, hUsub⟩

omit [T2Space S] in
private theorem exists_last_exit {φ : unitInterval → S} (hφ : Continuous φ)
    {U C : Set S} (hU : IsOpen U) (hC : IsClosed C) (hUC : U ⊆ C)
    (h0 : φ 0 ∉ U) (h1 : φ 1 ∈ U) :
    ∃ a : unitInterval, φ a ∉ U ∧ a < 1 ∧ (∀ t, a < t → φ t ∈ U) ∧ φ a ∈ C := by
  have hC₁ : IsCompact {t : unitInterval | φ t ∉ U} :=
    (hU.isClosed_compl.preimage hφ).isCompact
  obtain ⟨a, ha, hamax⟩ := hC₁.exists_isGreatest
    ⟨0, h0⟩
  have ha1 : a < 1 := lt_of_le_of_ne (unitInterval.le_one _) fun h' => ha (h' ▸ h1)
  have hlate : ∀ t, a < t → φ t ∈ U := by
    intro t ht
    by_contra hcon
    exact absurd (hamax hcon) (not_le.mpr ht)
  have hφaBC : φ a ∈ C := by
    have h₁ : a ∈ closure (Ioi a) := by
      rw [closure_Ioi' (⟨1, ha1⟩ : (Ioi a).Nonempty)]
      exact self_mem_Ici
    have h₂ : φ a ∈ closure (φ '' Ioi a) := image_closure_subset_closure_image hφ ⟨a, h₁, rfl⟩
    refine hC.closure_subset_iff.mpr ?_ h₂
    rintro _ ⟨t, ht, rfl⟩
    exact hUC (hlate t ht)
  exact ⟨a, ha, ha1, hlate, hφaBC⟩

private theorem preconnected_subset_ball_of_disjoint_sphere {C : Set EuclideanPlane}
    {c x : EuclideanPlane} {r : ℝ} (hconn : IsPreconnected C)
    (havoid : Disjoint C (Metric.sphere c r)) (hx : x ∈ C) (hxb : x ∈ Metric.ball c r) :
    C ⊆ Metric.ball c r := by
  refine hconn.subset_left_of_subset_union Metric.isOpen_ball
    (show IsOpen (Metric.closedBall (c : EuclideanPlane) r)ᶜ from
      Metric.isClosed_closedBall.isOpen_compl) ?_ ?_ ⟨x, hx, hxb⟩
  · exact disjoint_left.mpr fun z hz h' => h' (Metric.ball_subset_closedBall hz)
  · intro z hz
    by_cases hzb : z ∈ Metric.ball (c : EuclideanPlane) r
    · exact Or.inl hzb
    · refine Or.inr fun hzc => ?_
      have h₁ : dist z c = r :=
        le_antisymm hzc (not_lt.mp hzb)
      exact Set.disjoint_left.1 havoid hz h₁

private theorem isCompact_preimage_closedBall {c : EuclideanPlane} {r : ℝ}
    (hin : Metric.closedBall c r ⊆ OpenUnitDisc) :
    IsCompact (Subtype.val ⁻¹' Metric.closedBall c r : Set OpenUnitDisc) := by
  refine IsInducing.subtypeVal.isCompact_iff.mpr ?_
  rw [Subtype.image_preimage_coe, inter_eq_right.mpr hin]
  exact isCompact_closedBall _ _

private theorem mem_connectedComponentIn_compl_union_of_ball
    {K J : Set EuclideanPlane} {c x y : EuclideanPlane} {r : ℝ}
    (hK : IsCompact K) (hJ : IsCompact J) (hKJ : IsPreconnected (K ∩ J))
    (hline : IsLine J) (hsmall : Metric.ball c r ⊆ Kᶜ)
    (hx : x ∈ Metric.ball c r) (hy : y ∈ Metric.ball c r)
    (hxnot : x ∉ K ∪ J) (hynot : y ∉ K ∪ J) :
    y ∈ connectedComponentIn (K ∪ J)ᶜ x := by
  have hsameK : y ∈ connectedComponentIn Kᶜ x :=
    (convex_ball _ _).isPreconnected.subset_connectedComponentIn hx hsmall hy
  have hsameJ : y ∈ connectedComponentIn Jᶜ x :=
    (isPreconnected_compl_of_isLine hline).subset_connectedComponentIn
      (fun h => hxnot (Or.inr h)) subset_rfl (fun h => hynot (Or.inr h))
  exact janiszewski_plane hK hJ hKJ hxnot hynot hsameK hsameJ

/-- Near a leaf only one region is present. See the module docstring for the proof. -/
theorem exists_leaf_nbhd (hS : IsClosedSurface S) (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E)
    {u v : S} (huv : u ≠ v) (hcap : closure e ∩ Γ.V = {u, v}) (hL : IsLineWithEnds (closure e) u v)
    (hleaf : ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f) {N : Set S} (hN : IsOpen N) (hvN : v ∈ N) :
    ∃ Z : Set S, IsOpen Z ∧ v ∈ Z ∧ ∀ x ∈ Z, x ∉ Γ.U → ∀ y ∈ Z, y ∉ Γ.U →
      ∃ A : Set S, IsPreconnected A ∧ Disjoint A Γ.U ∧ x ∈ A ∧ y ∈ A ∧ A ⊆ N := by
  obtain ⟨f, hf0, hf1⟩ := hL
  let φ : unitInterval → S := fun t => (f t).1
  have hφ : Continuous φ := continuous_subtype_val.comp f.continuous
  have hφinj : Function.Injective φ := fun s t h => f.injective (Subtype.ext h)
  have hφr : ∀ x ∈ closure e, ∃ t, φ t = x := fun x hx => ⟨f.symm ⟨x, hx⟩, by simp [φ]⟩
  have huV : u ∈ Γ.V := by
    have : u ∈ closure e ∩ Γ.V := by rw [hcap]; simp
    exact this.2
  -- The closed set `Bad`: what `U(Γ)` has besides the closure of `e`.
  let Bad : Set S := (Γ.V \ {v}) ∪ ⋃ g ∈ Γ.E \ {e}, closure g
  have hvClosure : v ∈ closure e := hf1 ▸ (f 1).2
  obtain ⟨hBad, hvBad, hUsub⟩ := drawing_off_leaf_closed Γ (e := e) hvClosure hleaf
  change IsClosed Bad at hBad
  change v ∉ Bad at hvBad
  have huBad : u ∈ Bad := Or.inl ⟨huV, huv⟩
  -- A chart around `v`.
  obtain ⟨V₀, hV₀, hvV₀, ⟨h⟩⟩ := hS.2.2 v
  let T : OpenUnitDisc → S := fun y => (h.symm y).1
  have hT : Continuous T := continuous_subtype_val.comp h.symm.continuous
  have hTinj : Function.Injective T := fun x y hxy => h.symm.injective (Subtype.ext hxy)
  have hTopen : IsOpenMap T :=
    hV₀.isOpenEmbedding_subtypeVal.isOpenMap.comp h.symm.isOpenMap
  have hTV : ∀ y, T y ∈ V₀ := fun y => (h.symm y).2
  have hTh : ∀ (x : S) (hx : x ∈ V₀), T (h ⟨x, hx⟩) = x := by intro x hx; simp [T]
  have hhT : ∀ y, h ⟨T y, hTV y⟩ = y := by intro y; simp [T]
  let c : OpenUnitDisc := h ⟨v, hvV₀⟩
  have hTc : T c = v := hTh v hvV₀
  let Pb : Set OpenUnitDisc := {y | T y ∉ Bad ∧ T y ∈ N}
  have hPb : IsOpen Pb := (hBad.isOpen_compl.inter hN).preimage hT
  have hPb' : IsOpen (Subtype.val '' Pb : Set EuclideanPlane) :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal.isOpenMap _ hPb
  have hcPb : (c : EuclideanPlane) ∈ (Subtype.val '' Pb : Set EuclideanPlane) :=
    ⟨c, by simpa [Pb, hTc] using ⟨hvBad, hvN⟩, rfl⟩
  obtain ⟨ρ', hρ', hball⟩ := Metric.isOpen_iff.mp hPb' _ hcPb
  let ρ₀ : ℝ := ρ' / 2
  have hρ₀ : 0 < ρ₀ := half_pos hρ'
  have hCB : Metric.closedBall (c : EuclideanPlane) ρ₀ ⊆ Subtype.val '' Pb :=
    (Metric.closedBall_subset_ball (half_lt_self hρ')).trans hball
  have hCBo : ∀ z ∈ Metric.closedBall (c : EuclideanPlane) ρ₀, z ∈ OpenUnitDisc := by
    intro z hz
    obtain ⟨y, -, rfl⟩ := hCB hz
    exact y.2
  have hCBgood : ∀ z (hz : z ∈ Metric.closedBall (c : EuclideanPlane) ρ₀),
      T ⟨z, hCBo z hz⟩ ∉ Bad := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hCB hz
    exact hy.1
  -- The images of the open and the closed round disc.
  let BO : Set OpenUnitDisc := Subtype.val ⁻¹' Metric.ball (c : EuclideanPlane) ρ₀
  have hBO : IsOpen BO := Metric.isOpen_ball.preimage continuous_subtype_val
  have hYO : IsOpen (T '' BO) := hTopen _ hBO
  let BC : Set OpenUnitDisc := Subtype.val ⁻¹' Metric.closedBall (c : EuclideanPlane) ρ₀
  have hBCcpt : IsCompact BC := isCompact_preimage_closedBall hCBo
  have hYC : IsClosed (T '' BC) := (hBCcpt.image hT).isClosed
  have hBOC : BO ⊆ BC := fun y hy => Metric.ball_subset_closedBall hy
  -- The last time `a` when `φ` is outside the small open disc.
  have hφ0 : φ 0 = u := hf0
  have hφ1 : φ 1 = v := hf1
  have huBC : u ∉ T '' BC := by
    rintro ⟨y, hy, hyu⟩
    exact hCBgood y.1 hy (by simpa [hyu] using huBad)
  have hcBO : c ∈ BO := by simp [BO, hρ₀]
  have hvYO : v ∈ T '' BO := ⟨c, hcBO, hTc⟩
  obtain ⟨a, ha, ha1, hlate, hφaBC⟩ :=
    exists_last_exit hφ hYO hYC (image_mono hBOC) (fun h' => huBC (hφ0 ▸ image_mono hBOC h'))
      (hφ1.symm ▸ hvYO)
  -- The end piece `J`, as a curve `ψ` in the plane.
  obtain ⟨σ, hσ, hσinj, hσr, hσ0, hσ1⟩ := exists_reparam ha1
  have hσa : ∀ s, a ≤ σ s := fun s => (show σ s ∈ Icc a 1 from hσr ▸ mem_range_self s).1
  have hkBC : ∀ s, φ (σ s) ∈ T '' BC := by
    intro s
    rcases eq_or_lt_of_le (hσa s) with h' | h'
    · rw [← h']
      exact hφaBC
    · exact image_mono hBOC (hlate _ h')
  have hkV : ∀ s, φ (σ s) ∈ V₀ := by
    intro s
    obtain ⟨y, -, hy⟩ := hkBC s
    exact hy ▸ hTV y
  let ψ : unitInterval → EuclideanPlane := fun s => (h ⟨φ (σ s), hkV s⟩).1
  have hψ : Continuous ψ := by
    refine continuous_subtype_val.comp (h.continuous.comp ?_)
    exact Continuous.subtype_mk (hφ.comp hσ) _
  have hψinj : Function.Injective ψ := by
    intro s s' hss
    have h₁ := h.injective (Subtype.ext hss)
    have h₂ : φ (σ s) = φ (σ s') := congrArg (fun z : V₀ => z.1) h₁
    exact hσinj (hφinj h₂)
  have hTψ : ∀ s, T (h ⟨φ (σ s), hkV s⟩) = φ (σ s) := fun s => hTh _ _
  have hψBC : ∀ s, ψ s ∈ Metric.closedBall (c : EuclideanPlane) ρ₀ := by
    intro s
    obtain ⟨y, hy, hyeq⟩ := hkBC s
    have : h ⟨φ (σ s), hkV s⟩ = y := hTinj ((hTψ s).trans hyeq.symm)
    change (h ⟨φ (σ s), hkV s⟩ : EuclideanPlane) ∈ _
    rw [this]
    exact hy
  have hψBO : ∀ s, a < σ s → ψ s ∈ Metric.ball (c : EuclideanPlane) ρ₀ := by
    intro s hs
    obtain ⟨y, hy, hyeq⟩ := hlate _ hs
    have : h ⟨φ (σ s), hkV s⟩ = y := hTinj ((hTψ s).trans hyeq.symm)
    change (h ⟨φ (σ s), hkV s⟩ : EuclideanPlane) ∈ _
    rw [this]
    exact hy
  have hJline : IsLine (range ψ) := by
    refine ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective ψ hψinj)
      hψ.rangeFactorization⟩
  -- The set `M`: the rest of `e` in the closed round disc, and `K`.
  let M : Set EuclideanPlane := Subtype.val '' (BC ∩ T ⁻¹' (φ '' Iic a))
  have hMcpt : IsCompact M := by
    have hcl : IsClosed (φ '' Iic a) := (isClosed_Iic.isCompact.image hφ).isClosed
    have : IsCompact (BC ∩ T ⁻¹' (φ '' Iic a)) := hBCcpt.inter_right (hcl.preimage hT)
    exact this.image continuous_subtype_val
  let K : Set EuclideanPlane := Metric.sphere (c : EuclideanPlane) ρ₀ ∪ M
  have hKcpt : IsCompact K := (isCompact_sphere _ _).union hMcpt
  have hKJ : K ∩ range ψ = {ψ 0} := by
    ext x
    constructor
    · rintro ⟨hxK, s, rfl⟩
      have hs : σ s = a := by
        by_contra hne
        have hlt : a < σ s := lt_of_le_of_ne (hσa s) (Ne.symm hne)
        rcases hxK with hxK | ⟨z, ⟨-, t, ht, htz⟩, hzs⟩
        · have h₁ := hψBO s hlt
          exact absurd hxK (ne_of_lt (Metric.mem_ball.mp h₁))
        · have hzeq : z = h ⟨φ (σ s), hkV s⟩ := Subtype.ext hzs
          have h₁ : φ t = φ (σ s) := by rw [htz, hzeq, hTψ]
          have h₂ : t = σ s := hφinj h₁
          exact absurd (h₂ ▸ ht) (not_le.mpr hlt)
      have : s = 0 := hσinj (hs.trans hσ0.symm)
      rw [this]
      exact rfl
    · intro hx
      rw [mem_singleton_iff.mp hx]
      refine ⟨Or.inr ⟨h ⟨φ (σ 0), hkV 0⟩, ⟨hψBC 0, a, le_refl a, ?_⟩, rfl⟩, mem_range_self 0⟩
      rw [hTψ, hσ0]
  have hKJconn : IsPreconnected (K ∩ range ψ) := hKJ ▸ isPreconnected_singleton
  have hcK : (c : EuclideanPlane) ∉ K := by
    rintro (h' | ⟨z, ⟨-, t, ht, htz⟩, hzc⟩)
    · have : dist (c : EuclideanPlane) c = ρ₀ := h'
      rw [dist_self] at this
      exact hρ₀.ne this
    · have hzeq : z = c := Subtype.ext hzc
      have h₁ : φ t = φ 1 := by rw [htz, hzeq, hTc, hφ1]
      have h₂ : t = 1 := hφinj h₁
      exact absurd (h₂ ▸ ht) (not_le.mpr ha1)
  obtain ⟨ρ₂, hρ₂, hballK⟩ := Metric.isOpen_iff.mp hKcpt.isClosed.isOpen_compl _ hcK
  let ρ₃ : ℝ := min ρ₂ ρ₀
  have hρ₃ : 0 < ρ₃ := lt_min hρ₂ hρ₀
  have hsmall : Metric.ball (c : EuclideanPlane) ρ₃ ⊆ Kᶜ :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hballK
  have hsmall₀ : Metric.ball (c : EuclideanPlane) ρ₃ ⊆ Metric.ball (c : EuclideanPlane) ρ₀ :=
    Metric.ball_subset_ball (min_le_right _ _)
  let B₃ : Set OpenUnitDisc := Subtype.val ⁻¹' Metric.ball (c : EuclideanPlane) ρ₃
  refine ⟨T '' B₃, hTopen _ (Metric.isOpen_ball.preimage continuous_subtype_val),
    ⟨c, by simp [B₃, hρ₃], hTc⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ hxU _ ⟨y, hy, rfl⟩ hyU
  -- Points of the small ball are outside `J`, since they are off `U(Γ)`.
  have hoff : ∀ z : OpenUnitDisc, T z ∉ Γ.U → (z : EuclideanPlane) ∉ range ψ := by
    rintro z hz ⟨s, hs⟩
    have hzeq : h ⟨φ (σ s), hkV s⟩ = z := Subtype.ext hs
    have h₁ : T z = φ (σ s) := by rw [← hzeq, hTψ]
    exact hz (h₁ ▸ Γ.closure_subset_U he (f (σ s)).2)
  have hxnot : (x : EuclideanPlane) ∉ K ∪ range ψ :=
    fun h => h.elim (hsmall hx) (hoff x hxU)
  have hynot : (y : EuclideanPlane) ∉ K ∪ range ψ :=
    fun h => h.elim (hsmall hy) (hoff y hyU)
  have hsame := mem_connectedComponentIn_compl_union_of_ball hKcpt (isCompact_range hψ)
    hKJconn hJline hsmall hx hy hxnot hynot
  let Cc : Set EuclideanPlane := connectedComponentIn (K ∪ range ψ)ᶜ (x : EuclideanPlane)
  have hCcconn : IsPreconnected Cc := isPreconnected_connectedComponentIn
  have hCcsub : Cc ⊆ (K ∪ range ψ)ᶜ := connectedComponentIn_subset _ _
  have hxCc : (x : EuclideanPlane) ∈ Cc := mem_connectedComponentIn hxnot
  have hCcball : Cc ⊆ Metric.ball (c : EuclideanPlane) ρ₀ :=
    preconnected_subset_ball_of_disjoint_sphere hCcconn
      (Set.disjoint_left.2 fun _ hz hs => hCcsub hz (Or.inl (Or.inl hs))) hxCc (hsmall₀ hx)
  have hCcO : Cc ⊆ OpenUnitDisc := fun z hz => hCBo z (Metric.ball_subset_closedBall (hCcball hz))
  have hconn' : IsPreconnected (Subtype.val ⁻¹' Cc : Set OpenUnitDisc) := by
    refine (IsInducing.subtypeVal :
      IsInducing (Subtype.val : OpenUnitDisc → EuclideanPlane)).isPreconnected_image.mp ?_
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hCcO]
    exact hCcconn
  refine ⟨T '' (Subtype.val ⁻¹' Cc), hconn'.image _ hT.continuousOn, ?_, ⟨x, hxCc, rfl⟩,
    ⟨y, hsame, rfl⟩, ?_⟩
  swap
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hCB (Metric.ball_subset_closedBall (hCcball hz))
    have : w = z := Subtype.ext hwz
    exact this ▸ hw.2
  refine disjoint_left.mpr ?_
  rintro _ ⟨z, hz, rfl⟩ hzU
  have hzB : (z : EuclideanPlane) ∈ Metric.closedBall (c : EuclideanPlane) ρ₀ :=
    Metric.ball_subset_closedBall (hCcball hz)
  rcases hUsub _ hzU with h' | h'
  · exact hCBgood z.1 hzB h'
  obtain ⟨t, ht⟩ := hφr _ h'
  rcases le_or_gt t a with hta | hta
  · exact hCcsub hz (Or.inl (Or.inr ⟨z, ⟨hzB, t, hta, ht⟩, rfl⟩))
  · have htm : t ∈ Icc a 1 := ⟨hta.le, unitInterval.le_one _⟩
    rw [← hσr] at htm
    obtain ⟨s, rfl⟩ := htm
    refine hCcsub hz (Or.inr ⟨s, ?_⟩)
    have : h ⟨φ (σ s), hkV s⟩ = z := hTinj ((hTψ s).trans ht)
    exact congrArg Subtype.val this

end GraphMinor.GM11
