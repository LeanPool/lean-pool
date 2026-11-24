/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14n

/-!
# Graph Minors XIX, Section 14: the vertices of `M(Γ, ℒ)` in a wheel

Inside a wheel, `M(Γ, ℒ)` keeps only the vertices on the spokes and the hub. The arms of the wheel
are distinct.
-/

@[expose] public section

namespace GraphMinor.GM19

universe w

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α} {D : TangleDatum cap χ} {W : Set Shat}

namespace TangleDatum.WheelFrame

variable (fr : WheelFrame D W)

theorem spoke_support_congr {i : ℕ} {v : bdVerts D W} (h : fr.R.vert i = v.1) {x : Shat} (hx : x ∈
  (fr.sp.K v).support) : x ∈ (fr.R.spoke fr.sp i).support := by
  have key : ∀ (y z : bdVerts D W), y.1 = z.1 → x ∈ (fr.sp.K z).support → x ∈ (fr.sp.K y).support
    := by
    rintro ⟨y, hy⟩ ⟨z, hz⟩ e h'
    obtain rfl : y = z := e
    exact h'
  exact key _ _ h hx

theorem k_three : 3 ≤ fr.R.k := by
  have h₁ := three_le_ncard_bd fr.hW fr.hbdS fr.hin
  have hsub : discBd W ∩ D.P.Γ.hatV cap ⊆ fr.R.vert '' Iio fr.R.k := by
    rintro x ⟨hb, hV⟩
    obtain ⟨i, hi, rfl⟩ := fr.R.exists_vert x ⟨hV, hb⟩
    exact ⟨i, hi, rfl⟩
  have h₂ := ncard_le_ncard hsub ((finite_Iio _).image _)
  have h₃ := ncard_image_le (f := fr.R.vert) (finite_Iio fr.R.k)
  have h₄ : (Iio fr.R.k).ncard = fr.R.k := by
    rw [← Nat.card_coe_set_eq]
    simp
  omega

/-- A vertex of `Γ` on a spoke, seen at a rim position below `k`. -/
theorem exists_levV_lt {i : ℕ} {y : Shat} (hy : y ∈ (fr.R.spoke fr.sp i).support)
  (hV : y ∈ D.P.Γ.hatV cap) : ∃ j < fr.R.k, ∃ t ≤ fr.top j, y = fr.levV j t := by
  obtain ⟨t, ht, rfl⟩ := fr.exists_levV hy hV
  refine ⟨i % fr.R.k, fr.R.mod_lt i, t, ?_, ?_⟩
  · rw [fr.top_congr (fr.vert_mod i)]
    exact ht
  · exact fr.levV_congr (fr.vert_mod i).symm t

/-- The sectors with rim position below `k` cover `W` off the hub and the spokes. -/
theorem cover_lt {x : Shat} (hx : x ∈ W) (hxA : x ∉ fr.sp.A) : ∃ i < fr.R.k, x ∈ (fr.sec i).Δ := by
  obtain ⟨r, hr⟩ := SpokeSystem.cover fr.hW fr.sp fr.hbdS fr.hin (ι := {i : ℕ // i < fr.R.k})
    (fun i ↦ fr.R.reg i.1) (fun i ↦ (fr.sec i.1).toSectorAt)
    (fun r hr ↦ by
      obtain ⟨i, hi, rfl⟩ := fr.R.exists_reg r hr
      exact ⟨⟨i, hi⟩, rfl⟩) hx hxA
  exact ⟨r.1, r.2, hr⟩

theorem emb_notMem_discInt {A : Arm D.Γ} {Δ X : Set Shat} (h : IsDiscArm fr A Δ X) {v : S}
  (hv : v ∈ A.compl.vertexSet) : cap.emb v ∉ discInt Δ := by
  have hT := cap.isClosedSurface
  rw [h.compl] at hv
  have : cap.emb v ∈ closure Δᶜ := hv.2
  rw [closure_compl_disc hT h.disc] at this
  exact this

/-- **Inside a wheel, `M(Γ, ℒ)` lives on the spokes and on the hub.** -/
theorem mem_cases {x : Shat} (hV : x ∈ D.P.Γ.hatV cap) (hxW : x ∈ W) (hoff : ∀ A ∈ fr.arms, ∀ Δ X,
  IsDiscArm fr A Δ X → x ∉ discInt Δ) :
    (∃ i < fr.R.k, ∃ t ≤ fr.top i, x = fr.levV i t) ∨ x ∈ fr.H.U := by
  have hspoke : ∀ {i : ℕ}, x ∈ (fr.R.spoke fr.sp i).support → (∃ i < fr.R.k, ∃ t ≤ fr.top i, x
    = fr.levV i t) ∨ x ∈ fr.H.U := fun h ↦ .inl (fr.exists_levV_lt h hV)
  have hG : x ∈ D.rad.G.V := D.rad.isPreRadial.2.1 hV
  by_cases hxA : x ∈ fr.sp.A
  · rcases hxA with hh | hu
    · rcases fr.hW.hub_cases with ⟨z, -, hU, hz⟩ | ⟨hH, hle, hc, hz⟩
      · right
        rw [hU]
        rw [hz] at hh
        exact hh
      · right
        rw [hz] at hh
        obtain ⟨-, -, hi⟩ := fr.hub_data hc
        by_contra hn
        have hb : x ∉ discBd (D.ins fr.H) := fun h' ↦ hn (hi.2.2.2.1 ▸ h')
        exact hoff _ (.inr ⟨hc, rfl⟩) _ _ (fr.hubArm_disc hc) ⟨hh, hb⟩
    · obtain ⟨v, hv⟩ := mem_iUnion.mp hu
      obtain ⟨i, -, hi⟩ := fr.R.exists_vert v.1 v.2
      exact hspoke (fr.spoke_support_congr hi.symm (support_of_mem_U _ hv hG))
  · obtain ⟨i, hi, hx⟩ := fr.cover_lt hxW hxA
    have hb : x ∈ discBd (fr.sec i).Δ := by
      by_contra hn
      exact hoff _ (.inl ⟨i, hi, rfl⟩) _ _ (fr.secArm_disc i) ⟨hx, hn⟩
    rcases fr.bd_sector hV hb with h' | h' | h'
    · exact hspoke h'
    · exact hspoke h'
    · exact .inr h'

theorem discInt_sec_off_bd (i : ℕ) {y : Shat} (hy : y ∈ discInt (fr.sec i).Δ) : y ∈ discInt W :=
  ⟨fr.sec_Δ_sub i ((discInt_subset _) hy), discInt_off_bd cap.isClosedSurface fr.hW.is_disc
    (fr.sec i).full.disc (fr.sec_Δ_sub i) hy⟩

theorem spoke_mem_W (i : ℕ) {y : Shat} (hy : y ∈ (fr.R.spoke fr.sp i).support) : y ∈ W :=
  fr.spoke_subset i ((mem_walkDrawing_U _ _).mpr (.inl hy))

theorem spoke_bd (i : ℕ) {y : Shat} (hy : y ∈ (fr.R.spoke fr.sp i).support) (hb : y ∈ discBd W) : y
  = fr.R.vert i :=
  (fr.spoke_spoke i).meet_bd fr.hW fr.hbdS fr.hin ((mem_walkDrawing_U _ _).mpr (.inl hy)) hb

theorem hub_int {y : Shat} (hy : y ∈ fr.H.U) : y ∈ discInt W := by
  obtain ⟨-, h₁, h₂, h₃⟩ := fr.hW.hubSet_facts
  exact ⟨h₁ (h₃ hy), fun hb ↦ disjoint_left.mp h₂ (h₃ hy) hb⟩

/-- The vertices of `Γ` on the rim in a sector are the two rim vertices of the sector. -/
theorem sec_rim {i : ℕ} {y : Shat} (hV : y ∈ D.P.Γ.hatV cap) (hy : y ∈ (fr.sec i).Δ ∪ fr.secX i)
  (hb : y ∈ discBd W) : y = fr.R.vert i ∨ y = fr.R.vert (i + 1) := by
  have hG : y ∈ D.rad.G.V := D.rad.isPreRadial.2.1 hV
  rcases hy with hy | hy
  · have hbd : y ∈ discBd (fr.sec i).Δ := by
      by_contra hn
      exact (fr.discInt_sec_off_bd i ⟨hy, hn⟩).2 hb
    rcases fr.bd_sector hV hbd with h' | h' | h'
    · exact .inl (fr.spoke_bd i h' hb)
    · exact .inr (fr.spoke_bd (i + 1) h' hb)
    · exact absurd hb (fr.hub_int h').2
  · exact .inl (fr.spoke_bd i (support_of_mem_U _ hy.1.2 hG) hb)

theorem vert_mem_sec (i : ℕ) : fr.R.vert i ∈ (fr.sec i).Δ ∧ fr.R.vert (i + 1) ∈ (fr.sec i).Δ := by
  have hfull := (fr.sec i).full
  have h₁ : fr.R.vert i ∈ discBd (fr.sec i).Δ := by
    rw [hfull.bd_eq]
    exact .inr ((mem_walkDrawing_U _ _).mpr (.inl (fr.sec i).Z.start_mem_support))
  have h₂ : fr.R.vert (i + 1) ∈ discBd (fr.sec i).Δ := by
    rw [hfull.bd_eq]
    exact .inr ((mem_walkDrawing_U _ _).mpr (.inl (fr.sec i).Z.end_mem_support))
  exact ⟨Surface.discBd_subset _ h₁, Surface.discBd_subset _ h₂⟩

theorem vert_V (i : ℕ) : D.pre (fr.R.vert i) ∈ D.Γ.V ∧ cap.emb (D.pre (fr.R.vert i)) = fr.R.vert i
  := by
  obtain ⟨u, hu, e⟩ := fr.vert_hatV i
  rw [← e, D.pre_emb]
  exact ⟨hu, rfl⟩

theorem vert_mem_arm (i : ℕ) : D.pre (fr.R.vert i) ∈ (fr.secArm i).minus.vertexSet ∧ D.pre
  (fr.R.vert (i + 1)) ∈ (fr.secArm i).minus.vertexSet := by
  have h := fr.secArm_disc i
  rw [h.minus]
  refine ⟨⟨(fr.vert_V i).1, ?_⟩, ⟨(fr.vert_V (i + 1)).1, ?_⟩⟩
  · change cap.emb (D.pre (fr.R.vert i)) ∈ (fr.sec i).Δ ∪ fr.secX i
    rw [(fr.vert_V i).2]
    exact .inl (fr.vert_mem_sec i).1
  · change cap.emb (D.pre (fr.R.vert (i + 1))) ∈ (fr.sec i).Δ ∪ fr.secX i
    rw [(fr.vert_V (i + 1)).2]
    exact .inl (fr.vert_mem_sec i).2

theorem arm_rim {i : ℕ} {v : S} (hv : v ∈ (fr.secArm i).minus.vertexSet)
  (hb : cap.emb v ∈ discBd W) : cap.emb v = fr.R.vert i ∨ cap.emb v = fr.R.vert (i + 1) := by
  rw [(fr.secArm_disc i).minus] at hv
  exact fr.sec_rim ⟨v, hv.1, rfl⟩ hv.2 hb

/-- **Distinct rim positions give distinct sectors.** -/
theorem secArm_inj {i j : ℕ} (hi : i < fr.R.k) (hj : j < fr.R.k) (h : fr.secArm i
  = fr.secArm j) : i = j := by
  have h3 := fr.k_three
  have hmod : ∀ {a b : ℕ}, fr.R.vert a = fr.R.vert b → a % fr.R.k = b % fr.R.k := fun {a b} e ↦
    fr.R.vert_inj (fr.R.mod_lt a) (fr.R.mod_lt b) (by rw [fr.vert_mod, fr.vert_mod, e])
  have hsucc : ∀ a, a < fr.R.k → (a + 1) % fr.R.k = if a + 1 < fr.R.k then a + 1 else 0
    := fun a ha ↦ by
    split_ifs with h'
    · exact Nat.mod_eq_of_lt h'
    · rw [show a + 1 = fr.R.k by omega, Nat.mod_self]
  have hbd : ∀ a, fr.R.vert a ∈ discBd W := fun a ↦ (fr.R.vert_mem a).2
  have he : ∀ a, cap.emb (D.pre (fr.R.vert a)) = fr.R.vert a := fun a ↦ (fr.vert_V a).2
  have h₁ := fr.arm_rim (i := j) (by rw [← h]; exact (fr.vert_mem_arm i).1)
    (by rw [he]; exact hbd _)
  have h₂ := fr.arm_rim (i := j) (by rw [← h]; exact (fr.vert_mem_arm i).2)
    (by rw [he]; exact hbd _)
  rw [he] at h₁ h₂
  by_contra hne
  have hi' := Nat.mod_eq_of_lt hi
  have hj' := Nat.mod_eq_of_lt hj
  have s₁ := hsucc i hi
  have s₂ := hsucc j hj
  rcases h₁ with e | e
  · exact hne (fr.R.vert_inj hi hj e)
  · have m₁ := hmod e
    rcases h₂ with e' | e'
    · have m₂ := hmod e'
      rw [hi', s₂] at m₁
      rw [s₁, hj'] at m₂
      split_ifs at m₁ m₂ <;> omega
    · exact fr.R.vert_ne_succ hi (e.trans e'.symm)

/-- A hub of more than one vertex has a vertex of `Γ`. -/
theorem hub_has_vertex (hc : fr.H.V.ncard ≠ 1) : ∃ x ∈ fr.H.U, x ∈ D.P.Γ.hatV cap := by
  obtain ⟨-, -, hi⟩ := fr.hub_data hc
  have hC := hi.1
  obtain ⟨e, he⟩ := GraphMinor.GM11.IsCircuit.E_nonempty hC.2
  have heG := hC.1.2 he
  have hcl : closure e ⊆ fr.H.U := fun z hz ↦ by
    rw [fr.H.U_eq]
    exact .inr (mem_biUnion he hz)
  have key : ∀ {x y : Shat}, D.rad.G.toGraph.IsLink e x y → ∃ x ∈ fr.H.U, x ∈ D.P.Γ.hatV cap := by
    intro x y hl
    have h₁ := D.even_length_walk (.cons hl (.nil hl.2.2.1))
    have h₂ : ¬ Even (GraphWalk.cons hl (.nil hl.2.2.1)).length := by
      simp [GraphWalk.length, GraphWalk.edges]
    have hm : ∀ z, z ∈ ({x, y} : Set Shat) → z ∈ fr.H.U := fun z hz ↦ by
      have : z ∈ closure e ∩ D.rad.G.V := by
        rw [hl.2.2.2]
        exact hz
      exact hcl this.1
    have hx : x ∈ fr.H.U := hm x (mem_insert x {y})
    have hy : y ∈ fr.H.U := hm y (mem_insert_of_mem x rfl)
    by_cases hxV : x ∈ D.P.Γ.hatV cap
    · exact ⟨x, hx, hxV⟩
    · by_cases hyV : y ∈ D.P.Γ.hatV cap
      · exact ⟨y, hy, hyV⟩
      · exact absurd (h₁.mpr ⟨fun h' ↦ absurd h' hxV, fun h' ↦ absurd h' hyV⟩) h₂
  rcases D.rad.G.edge_cond e heG with ⟨u, v, -, hc₁, -⟩ | ⟨u, hc₁, -⟩
  · have hu : u ∈ closure e ∩ D.rad.G.V := by
      rw [hc₁]
      exact mem_insert u {v}
    have hv : v ∈ closure e ∩ D.rad.G.V := by
      rw [hc₁]
      exact mem_insert_of_mem u rfl
    exact key (x := u) (y := v) ⟨heG, hu.2, hv.2, hc₁⟩
  · have hu : u ∈ closure e ∩ D.rad.G.V := by
      rw [hc₁]
      exact rfl
    exact key (x := u) (y := u) ⟨heG, hu.2, hu.2, by rw [hc₁]; simp⟩

theorem hub_minus_mem (hc : fr.H.V.ncard ≠ 1) : ∃ v ∈ (fr.hubArm hc).minus.vertexSet, cap.emb v ∈ W
  := by
  obtain ⟨x, hx, u, hu, rfl⟩ := fr.hub_has_vertex hc
  have h := fr.hubArm_disc hc
  obtain ⟨-, -, hi⟩ := fr.hub_data hc
  have hxI : cap.emb u ∈ D.ins fr.H := Surface.discBd_subset _ (hi.2.2.2.1 ▸ hx)
  refine ⟨u, ?_, (fr.hub_int hx).1⟩
  rw [h.minus]
  exact ⟨hu, .inl hxI⟩

end TangleDatum.WheelFrame

end GraphMinor.GM19
