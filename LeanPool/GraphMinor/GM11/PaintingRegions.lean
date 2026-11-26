/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PaintingCells
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The regions of the boundary drawing of a painting

`boundary_R`: the regions of the drawing of the boundaries of the cells of a painting are the
regions
of the painting and the interiors of the cells.

`isPreconnected_frontier`: the frontier of an open disc in a surface is connected. Hence the point
set
of a drawing with all regions open discs is connected (`eq_empty_of_split`). The consequence used
later: if a 2-cell painting has a cell with no vertex, that cell is all of it.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A decreasing sequence of compact connected sets has a connected intersection. -/
theorem isPreconnected_iInter_of_antitone [CompactSpace S] [T2Space S] {K : ℕ → Set S}
    (hanti : ∀ n, K (n + 1) ⊆ K n) (hc : ∀ n, IsClosed (K n)) (hp : ∀ n, IsPreconnected (K n)) :
    IsPreconnected (⋂ n, K n) := by
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hsub hne hne'
  by_contra hemp
  let s := ⋂ n, K n
  have hs : IsClosed s := isClosed_iInter hc
  have hdis : Disjoint (s ∩ t) (s ∩ t') := by
    refine disjoint_left.mpr fun x hx hx' => hemp ⟨x, hx.1, hx.2, hx'.2⟩
  obtain ⟨O₁, O₂, h₁, h₂, hs₁, hs₂, hO⟩ := SeparatedNhds.of_isCompact_isCompact
    (hs.inter ht).isCompact (hs.inter ht').isCompact hdis
  -- Some `K n` lies in `O₁ ∪ O₂`.
  have hex : ∃ n, K n ⊆ O₁ ∪ O₂ := by
    by_contra hno
    push Not at hno
    let L : ℕ → Set S := fun n => K n \ (O₁ ∪ O₂)
    have hLc : ∀ n, IsClosed (L n) := fun n => (hc n).sdiff (h₁.union h₂)
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed L
      (fun n x hx => ⟨hanti n hx.1, hx.2⟩)
      (fun n => by
        obtain ⟨x, hx, hn⟩ := not_subset.mp (hno n)
        exact ⟨x, hx, hn⟩) (hLc 0).isCompact hLc
    have hxs : x ∈ s := mem_iInter.mpr fun n => (mem_iInter.mp hx n).1
    have hn := (mem_iInter.mp hx 0).2
    rcases hsub hxs with h | h
    · exact hn (Or.inl (hs₁ ⟨hxs, h⟩))
    · exact hn (Or.inr (hs₂ ⟨hxs, h⟩))
  obtain ⟨n, hn⟩ := hex
  obtain ⟨x, hxs, hxt⟩ := hne
  obtain ⟨y, hys, hyt⟩ := hne'
  obtain ⟨z, -, hz₁, hz₂⟩ := hp n O₁ O₂ h₁ h₂ hn ⟨x, mem_iInter.mp hxs n, hs₁ ⟨hxs, hxt⟩⟩
    ⟨y, mem_iInter.mp hys n, hs₂ ⟨hys, hyt⟩⟩
  exact disjoint_left.mp hO hz₁ hz₂

/-- An open annulus around the origin of the plane is connected. -/
theorem isPreconnected_annulus {a : ℝ} (ha : 0 ≤ a) :
    IsPreconnected {x : EuclideanPlane | a < ‖x‖ ∧ ‖x‖ < 1} := by
  have hrank : 1 < Module.rank ℝ EuclideanPlane := by
    apply Module.lt_rank_of_lt_finrank
    simp
  have hsph : IsPreconnected (Metric.sphere (0 : EuclideanPlane) 1) :=
    isPreconnected_sphere hrank 0 1
  have hI : IsPreconnected (Ioo a 1) := isPreconnected_Ioo
  have himg : {x : EuclideanPlane | a < ‖x‖ ∧ ‖x‖ < 1} =
      (fun p : ℝ × EuclideanPlane => p.1 • p.2) '' (Ioo a 1 ×ˢ Metric.sphere 0 1) := by
    ext x
    constructor
    · rintro ⟨h₁, h₂⟩
      have hx : ‖x‖ ≠ 0 := by linarith
      refine ⟨(‖x‖, ‖x‖⁻¹ • x), ⟨⟨h₁, h₂⟩, ?_⟩, ?_⟩
      · simp [norm_smul, hx]
      · simp [smul_smul, hx]
    · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      have hu' : ‖u‖ = 1 := by simpa using hu
      have ht0 : 0 ≤ t := by linarith [ht.1]
      simp only [mem_ofPred_eq, norm_smul, hu', mul_one, Real.norm_of_nonneg ht0]
      exact ht
  rw [himg]
  exact (hI.prod hsph).image _ (by fun_prop)

/-- **The frontier of an open disc in a compact surface is connected.** -/
theorem isPreconnected_frontier [CompactSpace S] [T2Space S] {r : Set S} (hr : IsOpenDisc r) :
    IsPreconnected (frontier r) := by
  obtain ⟨hopen, ⟨φ⟩⟩ := hr
  let f : OpenUnitDisc → S := fun z => (φ z).1
  have hf : IsOpenEmbedding f := hopen.isOpenEmbedding_subtypeVal.comp φ.isOpenEmbedding
  have hfr : range f = r := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact (φ z).2
    · intro hy
      obtain ⟨z, hz⟩ := φ.surjective ⟨y, hy⟩
      exact ⟨z, by simp [f, hz]⟩
  let a : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
  have ha0 : ∀ n, 0 ≤ a n := fun n => by
    have : 1 / ((n : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    simp only [a]
    linarith
  have ha1 : ∀ n, a n < 1 := fun n => by
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    simp only [a]
    linarith
  have hamono : ∀ n, a n ≤ a (n + 1) := fun n => by
    have : 1 / (((n + 1 : ℕ) : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith
    simp only [a]
    linarith
  let A : ℕ → Set OpenUnitDisc := fun n => {z | a n < ‖z.1‖}
  let K : ℕ → Set S := fun n => closure (f '' A n)
  have hAconn : ∀ n, IsPreconnected (A n) := fun n => by
    rw [← IsEmbedding.subtypeVal.isInducing.isPreconnected_image]
    have : Subtype.val '' A n = {x : EuclideanPlane | a n < ‖x‖ ∧ ‖x‖ < 1} := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, by simpa [OpenUnitDisc] using z.2⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨⟨x, by simpa [OpenUnitDisc] using h₂⟩, h₁, rfl⟩
    rw [this]
    exact isPreconnected_annulus (ha0 n)
  have hK : frontier r = ⋂ n, K n := by
    have hsplit : ∀ n, r = f '' {z | ‖z.1‖ ≤ a n} ∪ f '' A n := fun n => by
      rw [← image_union, ← hfr, ← image_univ]
      congr 1
      ext z
      simp only [mem_univ, mem_union, mem_ofPred_eq, A, true_iff]
      exact le_or_gt _ _
    have hCc : ∀ n, IsClosed (f '' {z | ‖z.1‖ ≤ a n}) := fun n => by
      have hcomp : IsCompact {z : OpenUnitDisc | ‖z.1‖ ≤ a n} := by
        rw [IsEmbedding.subtypeVal.isCompact_iff]
        have : Subtype.val '' {z : OpenUnitDisc | ‖z.1‖ ≤ a n} = Metric.closedBall 0 (a n) := by
          ext x
          constructor
          · rintro ⟨z, hz, rfl⟩
            simpa using hz
          · intro hx
            have hx' : ‖x‖ ≤ a n := by simpa using hx
            exact ⟨⟨x, by simpa [OpenUnitDisc] using lt_of_le_of_lt hx' (ha1 n)⟩, hx', rfl⟩
        rw [this]
        exact isCompact_closedBall _ _
      exact (hcomp.image hf.continuous).isClosed
    apply subset_antisymm
    · intro y hy
      refine mem_iInter.mpr fun n => ?_
      have hcl : y ∈ closure r := hy.1
      have hyn : y ∉ r := fun h => hy.2 (by rwa [hopen.interior_eq])
      rw [hsplit n, closure_union, (hCc n).closure_eq] at hcl
      rcases hcl with h | h
      · exact (hyn ((hsplit n).symm ▸ Or.inl h)).elim
      · exact h
    · intro y hy
      have hcl : y ∈ closure r := by
        have h0 := mem_iInter.mp hy 0
        exact closure_mono (fun w hw => (hsplit 0).symm ▸ Or.inr hw) h0
      refine ⟨hcl, ?_⟩
      rw [hopen.interior_eq]
      intro hyr
      obtain ⟨z, rfl⟩ : y ∈ range f := hfr ▸ hyr
      have hz : ‖z.1‖ < 1 := by simpa [OpenUnitDisc] using z.2
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - ‖z.1‖))
      have hd : 0 < 1 - ‖z.1‖ := by linarith
      have hlt : ‖z.1‖ < a n := by
        have hn0 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
        have h₁ : 1 / ((n : ℝ) + 2) < 1 - ‖z.1‖ := by
          rw [div_lt_iff₀ hn0]
          rw [div_lt_iff₀ hd] at hn
          nlinarith [mul_comm (n : ℝ) (1 - ‖z.1‖)]
        simp only [a]
        linarith
      have hO : IsOpen (f '' {w | ‖w.1‖ < a n}) :=
        hf.isOpenMap _ (isOpen_lt (by fun_prop) continuous_const)
      obtain ⟨_, ⟨w, hw, rfl⟩, ⟨w', hw', he⟩⟩ := mem_closure_iff.mp (mem_iInter.mp hy n) _ hO
        ⟨z, hlt, rfl⟩
      obtain rfl := hf.injective he
      exact lt_asymm (show ‖w'.1‖ < a n from hw) hw'
  rw [hK]
  refine isPreconnected_iInter_of_antitone (fun n => closure_mono ?_) (fun n => isClosed_closure)
    fun n => ((hAconn n).image f hf.continuous.continuousOn).closure
  exact image_mono fun z hz => lt_of_le_of_lt (hamono n) hz

variable [T2Space S]

/-- If the regions of a drawing are open discs, its point set is connected: it does not split into
two non-empty disjoint closed sets. -/
theorem eq_empty_of_split (hS : IsClosedSurface S) [ConnectedSpace S] {D : Drawing S}
    (hD : ∀ r ∈ D.R, IsOpenDisc r) {C₁ C₂ : Set S} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (hdis : Disjoint C₁ C₂) (hU : C₁ ∪ C₂ = D.U) (hne : C₁.Nonempty) : C₂ = ∅ := by
  classical
  have : CompactSpace S := hS.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hfin := finite_R hS D
  have hfr : ∀ r ∈ D.R, frontier r ⊆ D.U := by
    intro r hr x hx
    by_contra hxU
    obtain ⟨r', hr', hxr'⟩ := exists_region_of_notMem hxU
    obtain ⟨z, hz', hz⟩ := mem_closure_iff.mp hx.1 r' (region_isOpen hr') hxr'
    obtain rfl := region_eq_of_mem hr' hr hz' hz
    exact hx.2 (by rwa [(region_isOpen hr').interior_eq])
  have isClosed_of_frontier_subset' : ∀ {r : Set S}, r ∈ D.R → frontier r = ∅ → IsClosed r := by
    intro r _ h
    exact isClosed_of_closure_subset fun x hx => by
      by_contra hn
      have : x ∈ frontier r := ⟨hx, fun hi => hn (interior_subset hi)⟩
      rw [h] at this
      exact this
  have hfrne : ∀ r ∈ D.R, (frontier r).Nonempty := by
    intro r hr
    by_contra hemp
    have hemp' : frontier r = ∅ := not_nonempty_iff_eq_empty.mp hemp
    have hcl : IsClopen r := ⟨isClosed_of_frontier_subset' hr hemp', region_isOpen hr⟩
    rcases isClopen_iff.mp hcl with h | h
    · exact (region_nonempty hr).ne_empty h
    · obtain ⟨x, hx⟩ := hne
      exact region_subset hr (h ▸ mem_univ x) (hU ▸ Or.inl hx)
  let Reg : Set S → Set S := fun C => C ∪ ⋃ r ∈ {r ∈ D.R | frontier r ⊆ C}, r
  have hclosed : ∀ C, IsClosed C → IsClosed (Reg C) := by
    intro C hC
    have heq : Reg C = C ∪ ⋃ r ∈ {r ∈ D.R | frontier r ⊆ C}, closure r := by
      apply subset_antisymm
      · refine union_subset_union_right _ (iUnion₂_mono fun r _ => subset_closure)
      · refine union_subset subset_union_left (iUnion₂_subset fun r hr x hx => ?_)
        by_cases hxr : x ∈ r
        · exact Or.inr (mem_iUnion₂.mpr ⟨r, hr, hxr⟩)
        · exact Or.inl (hr.2 ⟨hx, by rwa [(region_isOpen hr.1).interior_eq]⟩)
    rw [heq]
    have hCfin : {r ∈ D.R | frontier r ⊆ C}.Finite := hfin.subset fun _ h => h.1
    exact hC.union (hCfin.isClosed_biUnion fun _ _ => isClosed_closure)
  have hcover : Reg C₁ ∪ Reg C₂ = univ := by
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ D.U
    · rw [← hU] at hx
      exact hx.elim (fun h => Or.inl (Or.inl h)) fun h => Or.inr (Or.inl h)
    · obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hx
      have hsub : frontier r ⊆ C₁ ∪ C₂ := hU ▸ hfr r hr
      rcases subset_or_subset_of_closed (isPreconnected_frontier (hD r hr)) h₁ h₂ hsub
        (fun _ _ h h' => disjoint_left.mp hdis h h') with h | h
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨r, ⟨hr, h⟩, hxr⟩))
      · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨r, ⟨hr, h⟩, hxr⟩))
  have hdisj : Disjoint (Reg C₁) (Reg C₂) := by
    refine disjoint_left.mpr ?_
    have hoff : ∀ {C r x}, C ⊆ D.U → r ∈ D.R → x ∈ r → x ∉ C := fun hC hr hx hxC =>
      region_subset hr hx (hC hxC)
    have hC₁ : C₁ ⊆ D.U := hU ▸ subset_union_left
    have hC₂ : C₂ ⊆ D.U := hU ▸ subset_union_right
    rintro x (hx | hx) (hy | hy)
    · exact disjoint_left.mp hdis hx hy
    · obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hy
      exact hoff hC₁ hr.1 hxr hx
    · obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hx
      exact hoff hC₂ hr.1 hxr hy
    · obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hx
      obtain ⟨r', hr', hxr'⟩ := mem_iUnion₂.mp hy
      obtain rfl := region_eq_of_mem hr.1 hr'.1 hxr hxr'
      obtain ⟨z, hz⟩ := hfrne r hr.1
      exact disjoint_left.mp hdis (hr.2 hz) (hr'.2 hz)
  have hclopen : IsClopen (Reg C₁) := by
    refine ⟨hclosed C₁ h₁, ?_⟩
    have : Reg C₁ = (Reg C₂)ᶜ := by
      ext x
      constructor
      · exact fun h h' => disjoint_left.mp hdisj h h'
      · intro h
        exact (mem_union _ _ _).mp (hcover ▸ mem_univ x) |>.resolve_right h
    rw [this]
    exact (hclosed C₂ h₂).isOpen_compl
  rcases isClopen_iff.mp hclopen with h | h
  · obtain ⟨x, hx⟩ := hne
    have : x ∈ Reg C₁ := Or.inl hx
    rw [h] at this
    exact this.elim
  · refine eq_empty_of_forall_notMem fun x hx => ?_
    exact disjoint_left.mp hdisj (h ▸ mem_univ x) (Or.inl hx)

omit [T2Space S] in
/-- An `O`-arc is compact. -/
theorem isCompact_of_isOArc {F : Set S} (hF : IsOArc F) : IsCompact F := by
  obtain ⟨f⟩ := hF
  have : F = range fun x : Circle => (f x).1 := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := f.surjective ⟨y, hy⟩
      exact ⟨x, by simp [hx]⟩
    · rintro ⟨x, rfl⟩
      exact (f x).2
  rw [this]
  exact isCompact_range (by fun_prop)

omit [T2Space S] in
/-- **The regions of the boundary drawing of a painting** are the regions of the painting and the
interiors of its cells. -/
theorem boundary_R (hS : IsClosedSurface S) {Γ : Painting S} (hP : ∀ r ∈ Γ.R, IsOpenDisc r)
    {D : Drawing S} {V₀ : Set S} (hsub : Γ.V ⊆ V₀) (hV₀ : V₀ ⊆ Γ.U)
    (hbd : ∀ e ∈ Γ.E, V₀ ∩ closure e ⊆ discBd (closure e))
    (hDU : D.U = V₀ ∪ ⋃ e ∈ Γ.E, discBd (closure e)) :
    D.R = Γ.R ∪ (fun e => closure e \ discBd (closure e)) '' Γ.E := by
  have hU : IsClosed Γ.U := Cell.isClosed_U Γ fun r hr => (hP r hr).1
  have hclU : ∀ e ∈ Γ.E, closure e ⊆ Γ.U := fun e he =>
    closure_minimal (he.2.1.trans sdiff_subset) hU
  have hintne : ∀ e ∈ Γ.E, (closure e \ discBd (closure e)).Nonempty := fun e he => by
    obtain ⟨-, ⟨φ⟩⟩ := isOpenDisc_interior hS (Cell.isClosedDisc_closure he)
    exact ⟨(φ ⟨0, by simp [OpenUnitDisc]⟩).1, (φ _).2⟩
  have hintV : ∀ e ∈ Γ.E, Disjoint (closure e \ discBd (closure e)) V₀ := fun e he => by
    refine disjoint_left.mpr fun x hx hxV => hx.2 (hbd e he ⟨hxV, hx.1⟩)
  have hintint : ∀ e ∈ Γ.E, ∀ f ∈ Γ.E, e ≠ f →
      Disjoint (closure e \ discBd (closure e)) (closure f) := fun e he f hf hef => by
    refine disjoint_left.mpr fun x hx hxf => ?_
    exact disjoint_left.mp (hintV e he) hx (hsub (Cell.closure_inter_subset_V hS hU he hf hef
      ⟨hx.1, hxf⟩))
  refine componentsIn_of_partition ?_ ?_ ?_
  · rintro a (ha | ⟨e, he, rfl⟩)
    · obtain ⟨x, hx, rfl⟩ := id ha
      exact ⟨(hP _ ha).1, isPreconnected_connectedComponentIn, ⟨x, mem_connectedComponentIn hx⟩⟩
    · have hd := Cell.isClosedDisc_closure he
      refine ⟨(isOpenDisc_interior hS hd).1, ?_, hintne e he⟩
      have := IsClosedDisc.isPreconnected_diff_frontier hS hd
      rwa [IsClosedDisc.frontier_eq_discBd hS hd] at this
  · have hreg : ∀ a ∈ Γ.R, ∀ e ∈ Γ.E, ¬ (a ∩ (closure e \ discBd (closure e))).Nonempty := by
      rintro a ⟨y, -, rfl⟩ e he ⟨x, hxa, hxe⟩
      exact (connectedComponentIn_subset _ _ hxa).2 (hclU e he hxe.1)
    rintro a (ha | ⟨e, he, rfl⟩) b (hb | ⟨f, hf, rfl⟩) hne
    · obtain ⟨x, hxa, hxb⟩ := hne
      obtain ⟨y, -, rfl⟩ := id ha
      obtain ⟨z, -, rfl⟩ := id hb
      rw [connectedComponentIn_eq hxa, connectedComponentIn_eq hxb]
    · exact (hreg a ha f hf hne).elim
    · exact (hreg b hb e he (by rwa [inter_comm] at hne)).elim
    · by_cases hef : e = f
      · rw [hef]
      · obtain ⟨x, hxa, hxb⟩ := hne
        exact (disjoint_left.mp (hintint e he f hf hef) hxa hxb.1).elim
  · ext x
    rw [hDU]
    constructor
    · rintro ⟨a, ha | ⟨e, he, rfl⟩, hx⟩
      · refine ⟨trivial, ?_⟩
        obtain ⟨y, -, rfl⟩ := id ha
        have hxU := (connectedComponentIn_subset _ _ hx).2
        rintro (h | h)
        · exact hxU (hV₀ h)
        · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp h
          exact hxU (hclU f hf (discBd_subset _ hxf))
      · refine ⟨trivial, ?_⟩
        rintro (h | h)
        · exact disjoint_left.mp (hintV e he) hx h
        · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp h
          by_cases hef : e = f
          · subst hef
            exact hx.2 hxf
          · exact disjoint_left.mp (hintint e he f hf hef) hx (discBd_subset _ hxf)
    · rintro ⟨-, hx⟩
      by_cases hxU : x ∈ Γ.U
      · rcases Cell.mem_V_or_cell Γ hxU with h | ⟨e, he, hxe⟩
        · exact (hx (Or.inl (hsub h))).elim
        · refine ⟨_, Or.inr ⟨e, he, rfl⟩, subset_closure hxe, fun h => hx (Or.inr ?_)⟩
          exact mem_iUnion₂.mpr ⟨e, he, h⟩
      · have hx' : x ∈ univ \ Γ.U := ⟨trivial, hxU⟩
        exact ⟨_, Or.inl ⟨x, hx', rfl⟩, mem_connectedComponentIn hx'⟩

/-- **A cell with no vertex is all of a 2-cell painting.** -/
theorem free_cell (hS : IsClosedSurface S) [ConnectedSpace S] {Γ : Painting S}
    (hP : ∀ r ∈ Γ.R, IsOpenDisc r) {e : Set S} (he : e ∈ Γ.E) (hfree : closure e ∩ Γ.V = ∅) :
    Γ.V = ∅ ∧ Γ.E = {e} := by
  classical
  have hU : IsClosed Γ.U := Cell.isClosed_U Γ fun r hr => (hP r hr).1
  have hclU : ∀ e ∈ Γ.E, closure e ⊆ Γ.U := fun e he =>
    closure_minimal (he.2.1.trans sdiff_subset) hU
  have hbdne : ∀ f ∈ Γ.E, (discBd (closure f)).Nonempty := fun f hf => by
    obtain ⟨g⟩ := (Cell.isClosedDisc_closure hf).isOArc_discBd
    exact ⟨_, (g 1).2⟩
  -- Choose one boundary point for each cell, and add these points to the vertices.
  choose! w hw using hbdne
  let V₀ : Set S := Γ.V ∪ w '' {f ∈ Γ.E | closure f ∩ Γ.V = ∅}
  have hfe : Γ.E.Finite := Γ.finite_edges
  have hf₀ : {f ∈ Γ.E | closure f ∩ Γ.V = ∅}.Finite := hfe.subset fun _ h => h.1
  have hfin : V₀.Finite := Γ.finite_V.union (hf₀.image w)
  have hV₀U : V₀ ⊆ Γ.U := by
    refine union_subset Γ.V_subset_U ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hclU f hf.1 (discBd_subset _ (hw f hf.1))
  -- A vertex of `V₀` in the closure of a cell `f` is on its boundary.
  have hbd : ∀ f ∈ Γ.E, V₀ ∩ closure f ⊆ discBd (closure f) := by
    rintro f hf x ⟨h | ⟨g, hg, rfl⟩, hxf⟩
    · exact Cell.closure_inter_V_subset hS hf ⟨hxf, h⟩
    · by_cases hfg : f = g
      · subst hfg
        exact hw f hf
      · have := Cell.closure_inter_subset_V hS hU hf hg.1 hfg
          ⟨hxf, discBd_subset _ (hw g hg.1)⟩
        have h' : w g ∈ closure g ∩ Γ.V := ⟨discBd_subset _ (hw g hg.1), this⟩
        rw [hg.2] at h'
        exact h'.elim
  have hne : ∀ f ∈ Γ.E, (V₀ ∩ discBd (closure f)).Nonempty := by
    intro f hf
    by_cases hc : closure f ∩ Γ.V = ∅
    · exact ⟨w f, Or.inr ⟨f, ⟨hf, hc⟩, rfl⟩, hw f hf⟩
    · obtain ⟨x, hx, hxV⟩ := nonempty_iff_ne_empty.mpr hc
      exact ⟨x, Or.inl hxV, Cell.closure_inter_V_subset hS hf ⟨hx, hxV⟩⟩
  obtain ⟨D, hDU, hDV⟩ := exists_boundary_drawing hS hU hfin subset_union_left hne
  have hR := boundary_R hS hP subset_union_left hV₀U hbd hDU
  have hDisc : ∀ r ∈ D.R, IsOpenDisc r := by
    rw [hR]
    rintro r (hr | ⟨f, hf, rfl⟩)
    · exact hP r hr
    · exact isOpenDisc_interior hS (Cell.isClosedDisc_closure hf)
  -- Split `U(D)` into the boundary of `e` and the rest.
  let C₁ : Set S := discBd (closure e)
  let C₂ : Set S := (V₀ \ {w e}) ∪ ⋃ f ∈ Γ.E \ {e}, discBd (closure f)
  have hcl₁ : IsClosed C₁ := (isCompact_of_isOArc (Cell.isClosedDisc_closure
    he).isOArc_discBd).isClosed
  have hcl₂ : IsClosed C₂ := by
    refine (hfin.subset sdiff_subset).isClosed.union ((hfe.subset sdiff_subset).isClosed_biUnion
      fun f hf => ?_)
    exact (isCompact_of_isOArc (Cell.isClosedDisc_closure hf.1).isOArc_discBd).isClosed
  have hcapV : V₀ ∩ closure e ⊆ {w e} := by
    rintro x ⟨h | ⟨g, hg, rfl⟩, hxe⟩
    · have : x ∈ closure e ∩ Γ.V := ⟨hxe, h⟩
      rw [hfree] at this
      exact this.elim
    · by_cases hfg : e = g
      · rw [hfg]
        rfl
      · have := Cell.closure_inter_subset_V hS hU he hg.1 hfg ⟨hxe, discBd_subset _ (hw g hg.1)⟩
        have h' : w g ∈ closure e ∩ Γ.V := ⟨hxe, this⟩
        rw [hfree] at h'
        exact h'.elim
  have hsep : ∀ f ∈ Γ.E, f ≠ e → Disjoint (closure e) (closure f) := by
    intro f hf hfe'
    refine disjoint_left.mpr fun x hx hxf => ?_
    have := Cell.closure_inter_subset_V hS hU he hf hfe'.symm ⟨hx, hxf⟩
    have h' : x ∈ closure e ∩ Γ.V := ⟨hx, this⟩
    rw [hfree] at h'
    exact h'
  have hdis : Disjoint C₁ C₂ := by
    refine disjoint_left.mpr ?_
    rintro x hx (⟨hxV, hn⟩ | hxU)
    · exact hn (hcapV ⟨hxV, discBd_subset _ hx⟩)
    · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hxU
      exact disjoint_left.mp (hsep f hf.1 hf.2) (discBd_subset _ hx) (discBd_subset _ hxf)
  have hcover : C₁ ∪ C₂ = D.U := by
    rw [hDU]
    apply subset_antisymm
    · rintro x (hx | ⟨hx, -⟩ | hx)
      · exact Or.inr (mem_iUnion₂.mpr ⟨e, he, hx⟩)
      · exact Or.inl hx
      · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
        exact Or.inr (mem_iUnion₂.mpr ⟨f, hf.1, hxf⟩)
    · rintro x (hx | hx)
      · by_cases hxw : x = w e
        · exact Or.inl (hxw ▸ hw e he)
        · exact Or.inr (Or.inl ⟨hx, hxw⟩)
      · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
        by_cases hfe' : f = e
        · subst hfe'
          exact Or.inl hxf
        · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfe'⟩, hxf⟩))
  have hemp : C₂ = ∅ := eq_empty_of_split hS hDisc hcl₁ hcl₂ hdis hcover ⟨w e, hw e he⟩
  constructor
  · refine eq_empty_of_forall_notMem fun x hx => ?_
    have hxw : x ≠ w e := by
      intro h
      have h' : x ∈ closure e ∩ Γ.V := ⟨h ▸ discBd_subset _ (hw e he), hx⟩
      rw [hfree] at h'
      exact h'
    have : x ∈ C₂ := Or.inl ⟨Or.inl hx, hxw⟩
    rw [hemp] at this
    exact this
  · refine eq_singleton_iff_unique_mem.mpr ⟨he, fun f hf => ?_⟩
    by_contra hfe'
    have : w f ∈ C₂ := Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfe'⟩, hw f hf⟩)
    rw [hemp] at this
    exact this

/-- `RegionFacts` for a 2-cell painting with a cell with no vertex. -/
theorem regionFacts_of_free_cell (hS : IsClosedSurface S) [ConnectedSpace S] {Γ : Painting S}
    {Γ' : Drawing S} (hrad : PreRad (PaintingOrDrawing.painting Γ) Γ')
    {e : Set S} (he : e ∈ Γ.E) (hfree : closure e ∩ Γ.V = ∅) :
    RegionFacts (PaintingOrDrawing.painting Γ) Γ' := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hP : ∀ r ∈ Γ.R, IsOpenDisc r := hrad.1.2
  obtain ⟨hV, hE⟩ := free_cell hS hP he hfree
  have hEΓ' : Γ'.E = ∅ := by
    refine eq_empty_of_forall_notMem fun f hf => ?_
    obtain ⟨v, hv, -⟩ := hrad.2.2.2.2.2.1 f hf
    have hv' : v ∈ Γ.V := hv
    rw [hV] at hv'
    exact hv'
  have hno : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → False := by
    intro C hC hsub
    obtain ⟨u, W, -, hpos, -, hE'⟩ := hC
    have hne : ∃ f, f ∈ W.edges := by
      cases W with
      | nil => simp at hpos
      | cons h rest => exact ⟨_, List.mem_cons_self⟩
    obtain ⟨f, hf⟩ := hne
    have hfC : f ∈ C.E := hE' ▸ hf
    have := hsub.2 hfC
    rw [hEΓ'] at this
    exact this
  have heU : Disjoint e Γ'.U := by
    refine disjoint_left.mpr fun x hx hx' => ?_
    have h₁ : x ∈ Γ.U ∩ Γ'.U := ⟨(he.2.1 hx).1, hx'⟩
    have h₂ : Γ.U ∩ Γ'.U = Γ.V := hrad.2.1
    exact (he.2.1 hx).2 (h₂ ▸ h₁)
  have hcontain : ∀ s ∈ Γ'.R, e ⊆ s := by
    intro s hs
    obtain ⟨x, hx⟩ := he.1
    obtain ⟨s', hs', hxs'⟩ := exists_region_of_notMem (disjoint_left.mp heU hx)
    obtain rfl := region_eq_of_noCircuit hS hno hs hs'
    exact subset_region hs (he.2.2.1.isConnected.isPreconnected) heU hx hxs'
  refine ⟨fun s hs => ⟨e, he, hcontain s hs⟩, ?_, ?_⟩
  · intro s _ f hf g hg _ _
    have hf' : f ∈ Γ.E := hf
    have hg' : g ∈ Γ.E := hg
    rw [hE] at hf' hg'
    exact hf'.trans hg'.symm
  · intro s _ f _ _ v hv
    have hv' : v ∈ Γ.V := hv
    rw [hV] at hv'
    exact hv'.elim

end GraphMinor.GM11
