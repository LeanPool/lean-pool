/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14r

/-!
# Graph Minors XIX, Section 14: the code of a sector

In the paper the hub and the spokes of the singular vertices are drawn in the flaw, so they are the
same for all the paintings. We do not
draw them. We record instead, for each sector, how its march `π` reads along the two spokes and
along the hub. There are finitely many
codes, since all the numbers are bounded in terms of the radius. Two sectors with the same code have
marches that correspond term by term.
-/

@[expose] public section

namespace GraphMinor.GM19

universe w

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α} {D : TangleDatum cap χ} {W : Set Shat}

namespace TangleDatum.WheelFrame

variable (fr : WheelFrame D W)

theorem finite_hubPts : (fr.H.U ∩ D.P.Γ.hatV cap).Finite := (D.P.Γ.finite_V.image _).subset
  inter_subset_right

open Classical in
/-- The vertices of `Γ` on the hub, in a fixed order: the order of the march of the hub sector, if
there is one. -/
noncomputable def hubList : List Shat :=
  if hc : fr.H.V.ncard ≠ 1 then (fr.hubArm hc).π.map cap.emb else fr.finite_hubPts.toFinset.toList

theorem hubList_of (hc : fr.H.V.ncard ≠ 1) : fr.hubList = (fr.hubArm hc).π.map cap.emb := by
  rw [hubList, dite_eq_left hc]

theorem mem_hubArm_π (hc : fr.H.V.ncard ≠ 1) {v : S} : v ∈ (fr.hubArm hc).π ↔ cap.emb v ∈ fr.H.U
  ∧ v ∈ D.P.Γ.V := by
  have : ConnectedSpace Shat := cap.connected
  have hset : v ∈ (fr.hubArm hc).π ↔ v ∈ {v | v ∈ (fr.hubArm hc).π} := Iff.rfl
  have hT : IsClosedSurface Shat := cap.isClosedSurface
  obtain ⟨-, -, hi⟩ := fr.hub_data hc
  have hdisc := fr.hubArm_disc hc
  rw [hset, (fr.hubArm hc).π_set]
  change v ∈ (fr.hubArm hc).minus.vertexSet ∩ (fr.hubArm hc).compl.vertexSet ↔ _
  rw [hdisc.minus, hdisc.compl]
  constructor
  · rintro ⟨⟨hv, h₁⟩, -, h₂⟩
    refine ⟨?_, hv⟩
    rw [closure_compl_disc hT hi.2.2.1] at h₂
    have h₃ : cap.emb v ∈ D.ins fr.H := by simpa using h₁
    rw [← hi.2.2.2.1]
    by_contra hn
    exact h₂ ⟨h₃, hn⟩
  · rintro ⟨h₁, hv⟩
    have h₂ : cap.emb v ∈ discBd (D.ins fr.H) := hi.2.2.2.1 ▸ h₁
    refine ⟨⟨hv, .inl (Surface.discBd_subset _ h₂)⟩, hv, ?_⟩
    rw [closure_compl_disc hT hi.2.2.1]
    exact fun h₃ ↦ h₃.2 h₂

theorem mem_hubList {x : Shat} : x ∈ fr.hubList ↔ x ∈ fr.H.U ∧ x ∈ D.P.Γ.hatV cap := by
  by_cases hc : fr.H.V.ncard ≠ 1
  · rw [fr.hubList_of hc]
    simp only [List.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have := (fr.mem_hubArm_π hc).mp hv
      exact ⟨this.1, v, this.2, rfl⟩
    · rintro ⟨h₁, v, hv, rfl⟩
      exact ⟨v, (fr.mem_hubArm_π hc).mpr ⟨h₁, hv⟩, rfl⟩
  · rw [hubList, dite_eq_right hc]
    simp

theorem hubList_nodup : fr.hubList.Nodup := by
  by_cases hc : fr.H.V.ncard ≠ 1
  · rw [fr.hubList_of hc]
    exact (fr.hubArm hc).π_nodup.map cap.isEmbedding.injective
  · rw [hubList, dite_eq_right hc]
    exact Finset.nodup_toList _

/-- The place in the hub list of the end of a spoke, or the length of the list if this end is not a
vertex of `Γ`. -/
noncomputable def hIdx (i : ℕ) : ℕ := by
  classical exact fr.hubList.idxOf (fr.levV i (fr.top i))

/-- A vertex of the hub lies on a spoke only at the end of the spoke. -/
theorem hub_lev {x : Shat} (hx : x ∈ fr.hubList) {i t : ℕ} (ht : t ≤ fr.top i) :
    x = fr.levV i t ↔ t = fr.top i ∧
      (haveI := Classical.decEq Shat; fr.hubList.idxOf x) = fr.hIdx i := by
  classical
  obtain ⟨hxH, hxV⟩ := fr.mem_hubList.mp hx
  have hK := fr.spoke_spoke i
  have hmemV : fr.R.inner fr.sp i ∈ D.rad.G.V := GraphWalk.support_mem_V _
    (GraphWalk.end_mem_support (fr.R.spoke fr.sp i))
  have hlen : GraphWalk.vertexAt (fr.R.spoke fr.sp i) (fr.R.spoke fr.sp i).length
    = fr.R.inner fr.sp i := GraphWalk.vertexAt_length _ hmemV
  have htl : 2 * t ≤ (fr.R.spoke fr.sp i).length := by
    rw [top] at ht
    omega
  constructor
  · rintro rfl
    have hin : fr.levV i t ∈ hubSet D fr.H ∩ (walkDrawing D.rad.G (fr.R.spoke fr.sp i)).U :=
      ⟨(fr.hW.hubSet_facts).2.2.2 hxH, (mem_walkDrawing_U _ _).mpr (.inl (fr.levV_support ht))⟩
    rw [fr.hW.hubSet_inter_spoke hK] at hin
    have e : 2 * t = (fr.R.spoke fr.sp i).length := GraphWalk.vertexAt_inj _ hK.1 htl le_rfl
      (hin.trans hlen.symm)
    have et : t = fr.top i := by
      rw [top]
      omega
    refine ⟨et, ?_⟩
    rw [hIdx, ← et]
  · rintro ⟨rfl, hi⟩
    have hlt : fr.hubList.idxOf (fr.levV i (fr.top i)) < fr.hubList.length := by
      have : fr.hIdx i = fr.hubList.idxOf (fr.levV i (fr.top i)) := by
        simp only [hIdx]
      rw [← this, ← hi]
      exact List.idxOf_lt_length_iff.mpr hx
    have hmem := List.idxOf_lt_length_iff.mp hlt
    have h' : fr.hubList.idxOf x = fr.hubList.idxOf (fr.levV i (fr.top i)) := hi
    exact (List.idxOf_inj hx).mp h'

/-- Addresses of the vertices of a sector: a place on one of the two spokes, or a place in the hub
list. -/
abbrev Addr := (Bool × ℕ) ⊕ ℕ

open Classical in
/-- The address of a vertex in the sector `i`. -/
noncomputable def addr (i : ℕ) (v : S) : Addr :=
  if h : ∃ t ≤ fr.top i, cap.emb v = fr.levV i t then .inl (false, h.choose)
  else if h : ∃ t ≤ fr.top (i + 1), cap.emb v = fr.levV (i + 1) t then .inl (true, h.choose)
  else .inr (fr.hubList.idxOf (cap.emb v))

/-- The three kinds of address. -/
theorem addr_spec {i : ℕ} {v : S} (hv : v ∈ (fr.secArm i).π) :
    (∃ t ≤ fr.top i, fr.addr i v = .inl (false, t) ∧ cap.emb v = fr.levV i t) ∨ (∃ t ≤ fr.top
      (i + 1), fr.addr i v = .inl (true, t) ∧ cap.emb v = fr.levV (i + 1) t) ∨
      ∃ j, fr.addr i v = .inr j ∧ fr.hubList[j]? = some (cap.emb v) := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hT : IsClosedSurface Shat := cap.isClosedSurface
  have hset : v ∈ {v | v ∈ (fr.secArm i).π} := hv
  rw [(fr.secArm i).π_set] at hset
  have hdisc := fr.secArm_disc i
  change v ∈ (fr.secArm i).minus.vertexSet ∩ (fr.secArm i).compl.vertexSet at hset
  rw [hdisc.minus, hdisc.compl] at hset
  obtain ⟨⟨hvV, h₁⟩, -, h₂⟩ := hset
  have hV : cap.emb v ∈ D.P.Γ.hatV cap := ⟨v, hvV, rfl⟩
  rw [closure_compl_disc hT hdisc.disc] at h₂
  have hcases : cap.emb v ∈ (fr.R.spoke fr.sp i).support ∨ cap.emb v ∈ (fr.R.spoke fr.sp
    (i + 1)).support ∨ cap.emb v ∈ fr.H.U := by
    rcases h₁ with h₁ | h₁
    · exact fr.bd_sector hV (by
        by_contra hn
        exact h₂ ⟨h₁, hn⟩)
    · exact .inl (support_of_mem_U _ h₁.1.2 (D.rad.isPreRadial.2.1 hV))
  by_cases h₃ : ∃ t ≤ fr.top i, cap.emb v = fr.levV i t
  · have hr : fr.addr i v = .inl (false, h₃.choose) := by rw [addr, dite_eq_left h₃]
    exact .inl ⟨h₃.choose, h₃.choose_spec.1, hr, h₃.choose_spec.2⟩
  by_cases h₄ : ∃ t ≤ fr.top (i + 1), cap.emb v = fr.levV (i + 1) t
  · have hr : fr.addr i v = .inl (true, h₄.choose) := by
      rw [addr, dite_eq_right h₃, dite_eq_left h₄]
    exact .inr (.inl ⟨h₄.choose, h₄.choose_spec.1, hr, h₄.choose_spec.2⟩)
  have hH : cap.emb v ∈ fr.H.U := by
    rcases hcases with h | h | h
    · exact absurd (fr.exists_levV h hV) h₃
    · exact absurd (fr.exists_levV h hV) h₄
    · exact h
  have hl := fr.mem_hubList.mpr ⟨hH, hV⟩
  refine .inr (.inr ⟨_, by rw [addr, dite_eq_right h₃, dite_eq_right h₄], ?_⟩)
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr hl)]
  simp [List.getElem_idxOf]

open Classical in
/-- The places where the two spokes of a sector meet. -/
noncomputable def same (i : ℕ) : Finset ℕ := (Finset.range (fr.top i + 1)).filter fun t ↦ fr.levV i
  t = fr.levV (i + 1) t

/-- The type of codes. -/
abbrev CodeT := ℕ × ℕ × ℕ × ℕ × Finset ℕ × List Addr

/-- **The code of a sector.** -/
noncomputable def code (i : ℕ) : CodeT :=
  (fr.top i, fr.top (i + 1), fr.hIdx i, fr.hIdx (i + 1), fr.same i, (fr.secArm i).π.map (fr.addr i))

end TangleDatum.WheelFrame

theorem finite_lists {β : Type} {A : Set β} (hA : A.Finite) (b : ℕ) : {l : List β | l.length ≤ b
  ∧ ∀ x ∈ l, x ∈ A}.Finite := by
  induction b with
  | zero =>
    refine (finite_singleton ([] : List β)).subset ?_
    rintro l ⟨h, -⟩
    exact List.length_eq_zero_iff.mp (by omega)
  | succ b ih =>
    refine (((hA.image2 List.cons ih)).insert []).subset ?_
    rintro l ⟨h₁, h₂⟩
    cases l with
    | nil => exact .inl rfl
    | cons x l =>
      refine .inr ⟨x, h₂ x (by simp), l, ⟨by simpa using h₁, fun y hy ↦ h₂ y (by simp [hy])⟩, rfl⟩

/-- The codes with all numbers at most `b`. -/
def codeSet (b : ℕ) : Set TangleDatum.WheelFrame.CodeT :=
  {c | c.1 ≤ b ∧ c.2.1 ≤ b ∧ c.2.2.1 ≤ b ∧ c.2.2.2.1 ≤ b ∧ c.2.2.2.2.1 ⊆ Finset.range (b + 1)
    ∧ c.2.2.2.2.2.length ≤ b ∧
    ∀ x ∈ c.2.2.2.2.2, (Sum.elim (fun p : Bool × ℕ ↦ p.2 ≤ b) (fun j ↦ j
      ≤ b) : TangleDatum.WheelFrame.Addr → Prop) x}

theorem finite_codeSet (b : ℕ) : (codeSet b).Finite := by
  have hN : (Iic b).Finite := finite_Iic b
  have hA : {x : TangleDatum.WheelFrame.Addr | Sum.elim (fun p : Bool × ℕ ↦ p.2 ≤ b) (fun j ↦ j
    ≤ b) x}.Finite := by
    refine ((((finite_univ (α := Bool)).prod hN).image Sum.inl).union (hN.image Sum.inr)).subset ?_
    rintro (⟨c, t⟩ | j) h
    · exact .inl ⟨(c, t), ⟨mem_univ _, h⟩, rfl⟩
    · exact .inr ⟨j, h, rfl⟩
  have hF : {f : Finset ℕ | f ⊆ Finset.range (b + 1)}.Finite := (Finset.finite_toSet (Finset.range
    (b + 1)).powerset).subset fun f hf ↦ Finset.mem_coe.mpr (Finset.mem_powerset.mpr hf)
  refine (hN.prod (hN.prod (hN.prod (hN.prod (hF.prod (finite_lists hA b)))))).subset ?_
  rintro ⟨a, b', c, d, f, l⟩ ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩

namespace TangleDatum.WheelFrame

variable (fr : WheelFrame D W)

theorem π_length_le (i : ℕ) : (fr.secArm i).π.length ≤ 2 * fr.ρ + 2 := by
  have h := fr.sec_order_le i
  have h₁ : (fr.secArm i).π.length = {v | v ∈ (fr.secArm i).π}.ncard := by
    classical
    have : {v | v ∈ (fr.secArm i).π} = ↑(fr.secArm i).π.toFinset := by
      ext v
      simp
    rw [this, ncard_coe_finset, List.toFinset_card_of_nodup (fr.secArm i).π_nodup]
  rw [h₁, (fr.secArm i).π_set]
  exact h

theorem hubList_length_le : fr.hubList.length ≤ 2 * fr.ρ + 2 := by
  classical
  by_cases hc : fr.H.V.ncard ≠ 1
  · rw [fr.hubList_of hc, List.length_map]
    have h := fr.hub_order_le hc
    have h₁ : (fr.hubArm hc).π.length = {v | v ∈ (fr.hubArm hc).π}.ncard := by
      have : {v | v ∈ (fr.hubArm hc).π} = ↑(fr.hubArm hc).π.toFinset := by
        ext v
        simp
      rw [this, ncard_coe_finset, List.toFinset_card_of_nodup (fr.hubArm hc).π_nodup]
    rw [h₁, (fr.hubArm hc).π_set]
    exact h
  · rcases fr.hW.hub_cases with ⟨z, -, hU, -⟩ | ⟨-, -, h, -⟩
    · have h₁ := List.toFinset_card_of_nodup fr.hubList_nodup
      have h₂ : fr.hubList.toFinset ⊆ {z} := fun x hx ↦ by
        have := (fr.mem_hubList.mp (List.mem_toFinset.mp hx)).1
        rw [hU] at this
        simpa using this
      have h₃ := Finset.card_le_card h₂
      simp only [Finset.card_singleton] at h₃
      omega
    · exact absurd h hc

theorem top_le (i : ℕ) : fr.top i ≤ fr.ρ := by
  have h := (fr.hW.spoke_length (fr.spoke_spoke i)).1
  rw [top]
  omega

theorem code_mem (i : ℕ) : fr.code i ∈ codeSet (2 * fr.ρ + 3) := by
  classical
  have h₁ := fr.top_le i
  have h₂ := fr.top_le (i + 1)
  have hL := fr.hubList_length_le
  have hI : ∀ j, fr.hIdx j ≤ 2 * fr.ρ + 3 := fun j ↦ by
    have := List.idxOf_le_length (a := fr.levV j (fr.top j)) (l := fr.hubList)
    simp only [hIdx]
    omega
  refine ⟨by simp only [code]; omega, by simp only [code]; omega, hI _, hI _, ?_, ?_, ?_⟩
  · intro t ht
    have := (Finset.mem_filter.mp ht).1
    simp only [Finset.mem_range] at this ⊢
    omega
  · have := fr.π_length_le i
    simp only [code, List.length_map]
    omega
  · simp only [code, List.mem_map]
    rintro _ ⟨v, hv, rfl⟩
    rcases fr.addr_spec hv with ⟨t, ht, e, -⟩ | ⟨t, ht, e, -⟩ | ⟨j, e, hj⟩
    · rw [e]
      simp only [Sum.elim_inl]
      omega
    · rw [e]
      simp only [Sum.elim_inl]
      omega
    · rw [e]
      have := (List.getElem?_eq_some_iff.mp hj).1
      simp only [Sum.elim_inr]
      omega

end TangleDatum.WheelFrame

end GraphMinor.GM19
