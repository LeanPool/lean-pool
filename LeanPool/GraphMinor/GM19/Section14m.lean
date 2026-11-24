/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14l

/-!
# Graph Minors XIX, Section 14: the vertices of `Γ` on the spokes of a wheel

We read the vertices of `Γ` on a spoke as levels `0, 1, ...`, and we record how the paths of (13.7)
sit on the levels.
-/

@[expose] public section

namespace GraphMinor.GM19

universe w

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α} {D : TangleDatum cap χ} {W : Set Shat} {H :
    Drawing Shat} {ρ : ℕ}

namespace TangleDatum

/-- Two spokes with the same inner end from vertices of `Γ` have the same length. -/
theorem spoke_length_eq (hW : D.IsWheelHubOfRadius W H ρ) {v₁ v₂ h : Shat} {K₁ : GraphWalk
  D.rad.G.toGraph v₁ h} {K₂ : GraphWalk D.rad.G.toGraph v₂ h}
    (hv₁ : v₁ ∈ D.P.Γ.hatV cap) (hv₂ : v₂ ∈ D.P.Γ.hatV cap) (h1 : D.IsSpokeWalk W H K₁)
      (h2 : D.IsSpokeWalk W H K₂) : K₁.length = K₂.length := by
  have e₁ := D.even_length_walk K₁
  have e₂ := D.even_length_walk K₂
  have l₁ := hW.spoke_length h1
  have l₂ := hW.spoke_length h2
  have hpar : Even K₁.length ↔ Even K₂.length := by
    rw [e₁, e₂]
    exact ⟨fun h' ↦ ⟨fun _ ↦ h'.mp hv₁, fun _ ↦ hv₂⟩, fun h' ↦ ⟨fun _ ↦ h'.mp hv₂, fun _ ↦ hv₁⟩⟩
  rw [Nat.even_iff, Nat.even_iff] at hpar
  omega

/-- A vertex that is on two spokes has the same position on both. -/
theorem spoke_pos_eq (hW : D.IsWheelHubOfRadius W H ρ) {v₁ v₂ h₁ h₂ : Shat} {K₁ : GraphWalk
  D.rad.G.toGraph v₁ h₁} {K₂ : GraphWalk D.rad.G.toGraph v₂ h₂}
    (hv₁ : v₁ ∈ D.P.Γ.hatV cap) (hv₂ : v₂ ∈ D.P.Γ.hatV cap) (h1 : D.IsSpokeWalk W H K₁)
      (h2 : D.IsSpokeWalk W H K₂) {p q : ℕ} (hp : p ≤ K₁.length) (hq : q ≤ K₂.length)
    (e : GraphWalk.vertexAt K₁ p = GraphWalk.vertexAt K₂ q) : p = q := by
  have hx₁ := GraphWalk.vertexAt_mem K₁ hp
  have hx₂ := GraphWalk.vertexAt_mem K₂ hq
  rw [← e] at hx₂
  obtain rfl := h1.same_end h2 hx₁ hx₂
  have hlen := spoke_length_eq hW hv₁ hv₂ h1 h2
  obtain ⟨u, A₁, A₂, T, hK₁, hK₂, hxT, -⟩ := h1.merge h2 hx₁ hx₂
  subst hK₁ hK₂
  obtain ⟨s, hs, hsx⟩ := GraphWalk.exists_vertexAt T hxT
  simp only [GraphWalk.length_append] at hlen hp hq
  have hp' := GraphWalk.vertexAt_append_right A₁ T hs
  have hq' := GraphWalk.vertexAt_append_right A₂ T hs
  have i₁ := GraphWalk.vertexAt_inj _ h1.1 (p := p) (q := A₁.length + s)
    (by simp only [GraphWalk.length_append]; omega) (by simp only [GraphWalk.length_append]; omega)
    (by rw [hp', hsx])
  have i₂ := GraphWalk.vertexAt_inj _ h2.1 (p := q) (q := A₂.length + s)
    (by simp only [GraphWalk.length_append]; omega) (by simp only [GraphWalk.length_append]; omega)
    (by rw [hq']; exact e.symm.trans hsx)
  omega

namespace WheelFrame

variable (fr : WheelFrame D W)

/-- The vertex at level `t` of the spoke at the `i`th vertex of the rim. -/
noncomputable def levV (i t : ℕ) : Shat := GraphWalk.vertexAt (fr.R.spoke fr.sp i) (2 * t)

/-- The top level of the spoke at the `i`th vertex of the rim. -/
noncomputable def top (i : ℕ) : ℕ := (fr.R.spoke fr.sp i).length / 2

theorem vert_hatV (i : ℕ) : fr.R.vert i ∈ D.P.Γ.hatV cap := (fr.R.vert_mem i).1

theorem levV_support {i t : ℕ} (ht : t ≤ fr.top i) : fr.levV i t ∈ (fr.R.spoke fr.sp i).support :=
  GraphWalk.vertexAt_mem _ (by rw [top] at ht; omega)

theorem levV_hatV {i t : ℕ} (ht : t ≤ fr.top i) : fr.levV i t ∈ D.P.Γ.hatV cap :=
  (IsSpokeWalk.even_hatV (fr.vert_hatV i) (by rw [top] at ht; omega)).mpr (even_two_mul _)

theorem levV_zero (i : ℕ) : fr.levV i 0 = fr.R.vert i := GraphWalk.vertexAt_zero _

theorem exists_levV {i : ℕ} {y : Shat} (hy : y ∈ (fr.R.spoke fr.sp i).support)
  (hV : y ∈ D.P.Γ.hatV cap) : ∃ t ≤ fr.top i, y = fr.levV i t := by
  obtain ⟨p, hp, rfl⟩ := GraphWalk.exists_vertexAt _ hy
  obtain ⟨t, rfl⟩ := (IsSpokeWalk.even_hatV (fr.vert_hatV i) hp).mp hV
  exact ⟨t, by rw [top]; omega, by rw [levV, two_mul]⟩

/-- A vertex on two spokes is at the same level on both. -/
theorem level_eq {i j t t' : ℕ} (ht : t ≤ fr.top i) (ht' : t' ≤ fr.top j) (e : fr.levV i t
  = fr.levV j t') : t = t' := by
  have := spoke_pos_eq fr.hW (fr.vert_hatV i) (fr.vert_hatV j) (fr.spoke_spoke i)
    (fr.spoke_spoke j) (p := 2 * t) (q := 2 * t')
    (by rw [top] at ht; omega) (by rw [top] at ht'; omega) e
  omega

/-- The levels of one spoke are distinct. -/
theorem levV_inj {i t t' : ℕ} (ht : t ≤ fr.top i) (ht' : t' ≤ fr.top i) (e : fr.levV i t
  = fr.levV i t') : t = t' := fr.level_eq ht ht' e

/-- The two spokes of a sector end at the same vertex. -/
def Reg (i : ℕ) : Prop := fr.R.inner fr.sp i = fr.R.inner fr.sp (i + 1)

theorem top_eq_of_inner {i j : ℕ} (h : fr.R.inner fr.sp i = fr.R.inner fr.sp j) : fr.top i
  = fr.top j := by
  have key : ∀ {v₁ v₂ h₁ h₂ : Shat} (K₁ : GraphWalk D.rad.G.toGraph v₁ h₁)
    (K₂ : GraphWalk D.rad.G.toGraph v₂ h₂), h₁ = h₂ → v₁ ∈ D.P.Γ.hatV cap → v₂ ∈ D.P.Γ.hatV cap →
      D.IsSpokeWalk W fr.H K₁ → D.IsSpokeWalk W fr.H K₂ → K₁.length = K₂.length := by
    rintro v₁ v₂ h₁ h₂ K₁ K₂ rfl h₃ h₄ h₅ h₆
    exact spoke_length_eq fr.hW h₃ h₄ h₅ h₆
  exact congrArg (· / 2) (key _ _ h (fr.vert_hatV i) (fr.vert_hatV j) (fr.spoke_spoke i)
    (fr.spoke_spoke j))

/-- The paths of (13.7) in the sector `i`, one for each level. -/
structure IsPaths (i : ℕ) (P : ℕ → Set Shat) : Prop where
  disj : ∀ j k, j ≤ fr.top i → k ≤ fr.top i → j ≠ k → Disjoint (P j) (P k)
  left : ∀ j ≤ fr.top i, fr.levV i j ∈ P j
  right : ∀ j ≤ fr.top i, fr.levV (i + 1) j ∈ P j
  hat : ∀ j ≤ fr.top i, P j ⊆ D.P.Γ.hatV cap
  joined : ∀ j ≤ fr.top i, ∀ y ∈ P j, D.SkJoined (P j) (fr.levV i j) y
  cases : ∀ j ≤ fr.top i, (fr.levV i j = fr.levV (i + 1) j ∧ P j = {fr.levV i j}) ∨
    (fr.levV i j ∉ (fr.R.spoke fr.sp (i + 1)).support ∧ fr.levV (i + 1) j ∉
      (fr.R.spoke fr.sp i).support ∧ P j ⊆ (fr.sec i).Δ)

theorem exists_paths {i : ℕ} (hr : fr.Reg i) : ∃ P, fr.IsPaths i P := by
  have hmeet : ∃ x ∈ (fr.R.spoke fr.sp i).support, x ∈ (fr.R.spoke fr.sp (i + 1)).support :=
    ⟨fr.R.inner fr.sp i, GraphWalk.end_mem_support _, by
      have h := (fr.R.spoke fr.sp (i + 1)).end_mem_support
      rw [show fr.R.inner fr.sp i = fr.R.inner fr.sp (i + 1) from hr]
      exact h⟩
  obtain ⟨hl, P, hd, hP⟩ := (fr.sec i).full.levels fr.hopt fr.hbdS fr.hin (fr.spoke_spoke i)
    (fr.spoke_spoke (i + 1)) (fr.vert_hatV i) hmeet
  have hle : ∀ j, j ≤ fr.top i → 2 * j ≤ (fr.R.spoke fr.sp i).length := fun j hj ↦ by
    rw [top] at hj
    omega
  exact ⟨P, fun j k hj hk ↦ hd j k (hle j hj) (hle k hk), fun j hj ↦ (hP j (hle j hj)).1,
    fun j hj ↦ (hP j (hle j hj)).2.1, fun j hj ↦ (hP j (hle j hj)).2.2.1,
    fun j hj ↦ (hP j (hle j hj)).2.2.2.1, fun j hj ↦ (hP j (hle j hj)).2.2.2.2⟩

open Classical in
/-- The vertex sets of the paths of (13.7) in the sector `i`. -/
noncomputable def path (i : ℕ) : ℕ → Set Shat := if h : fr.Reg i then
  (fr.exists_paths h).choose else fun _ ↦ ∅

theorem path_spec {i : ℕ} (hr : fr.Reg i) : fr.IsPaths i (fr.path i) := by
  rw [path, dite_eq_left hr]
  exact (fr.exists_paths hr).choose_spec

/-- A vertex of `Γ` on the boundary of a sector is on one of its two spokes or on the hub. -/
theorem bd_sector {i : ℕ} {y : Shat} (hV : y ∈ D.P.Γ.hatV cap) (hy : y ∈ discBd (fr.sec i).Δ) :
    y ∈ (fr.R.spoke fr.sp i).support ∨ y ∈ (fr.R.spoke fr.sp (i + 1)).support ∨ y ∈ fr.H.U := by
  have hG : y ∈ D.rad.G.V := D.rad.isPreRadial.2.1 hV
  have hfull := (fr.sec i).full
  rw [hfull.bd_eq] at hy
  rcases hy with (hy | hy) | hy
  · exact .inl ((hat_on_edge hfull.r_mem.1 hfull.link₁ hy hV) ▸ (fr.R.spoke fr.sp
      i).start_mem_support)
  · exact .inr (.inl ((hat_on_edge hfull.r_mem.1 hfull.link₂ hy hV) ▸ (fr.R.spoke fr.sp
      (i + 1)).start_mem_support))
  · rcases hfull.Z_sub hy with (h' | h') | h'
    · exact .inl (support_of_mem_U _ h' hG)
    · exact .inr (.inl (support_of_mem_U _ h' hG))
    · exact .inr (.inr h')

/-- For a sector with spokes that meet, the hub is not needed. -/
theorem bd_sector_reg {i : ℕ} (hr : fr.Reg i) {y : Shat} (hV : y ∈ D.P.Γ.hatV cap) (hy : y ∈ discBd
  (fr.sec i).Δ) :
    y ∈ (fr.R.spoke fr.sp i).support ∨ y ∈ (fr.R.spoke fr.sp (i + 1)).support := by
  have hG : y ∈ D.rad.G.V := D.rad.isPreRadial.2.1 hV
  have hfull := (fr.sec i).full
  rw [hfull.bd_eq] at hy
  rcases hy with (hy | hy) | hy
  · exact .inl ((hat_on_edge hfull.r_mem.1 hfull.link₁ hy hV) ▸ (fr.R.spoke fr.sp
      i).start_mem_support)
  · exact .inr ((hat_on_edge hfull.r_mem.1 hfull.link₂ hy hV) ▸ (fr.R.spoke fr.sp
      (i + 1)).start_mem_support)
  · rcases hfull.Z_same hr hy with h' | h'
    · exact .inl (support_of_mem_U _ h' hG)
    · exact .inr (support_of_mem_U _ h' hG)

/-- A vertex of a path of (13.7) is an end of the path, or it is off all the spokes, inside the
sector. -/
theorem path_cases {i j : ℕ} (hr : fr.Reg i) (hj : j ≤ fr.top i) {y : Shat}
  (hy : y ∈ fr.path i j) : y = fr.levV i j ∨ y = fr.levV (i + 1) j ∨ y ∈ discInt (fr.sec i).Δ := by
  have hP := fr.path_spec hr
  have hV := hP.hat j hj hy
  have ht : fr.top (i + 1) = fr.top i := (fr.top_eq_of_inner hr).symm
  rcases hP.cases j hj with ⟨-, hs⟩ | ⟨-, -, hsub⟩
  · rw [hs] at hy
    exact .inl hy
  · by_cases hb : y ∈ discBd (fr.sec i).Δ
    · have hlev : ∃ t ≤ fr.top i, y ∈ fr.path i t ∧ (y = fr.levV i t ∨ y = fr.levV (i + 1) t) := by
        rcases fr.bd_sector_reg hr hV hb with h' | h'
        · obtain ⟨t, ht', rfl⟩ := fr.exists_levV h' hV
          exact ⟨t, ht', hP.left t ht', .inl rfl⟩
        · obtain ⟨t, ht', rfl⟩ := fr.exists_levV h' hV
          exact ⟨t, ht ▸ ht', hP.right t (ht ▸ ht'), .inr rfl⟩
      obtain ⟨t, ht', hyt, ho⟩ := hlev
      obtain rfl : t = j := by
        by_contra hne
        exact disjoint_left.mp (hP.disj t j ht' hj hne) hyt hy
      exact ho.imp id .inl
    · exact .inr (.inr ⟨hsub hy, hb⟩)

theorem discInt_off_spoke (i l : ℕ) {y : Shat} (hy : y ∈ discInt (fr.sec i).Δ) : y ∉
  (fr.R.spoke fr.sp l).support := fun h' ↦
  disjoint_left.mp ((fr.sec i).full.spoke_off _ _ _ (fr.spoke_spoke l))
    ((mem_walkDrawing_U _ _).mpr (.inl h')) hy

theorem discInt_off_hub (i : ℕ) {y : Shat} (hy : y ∈ discInt (fr.sec i).Δ) : y ∉ fr.H.U
  := fun h' ↦ disjoint_left.mp (fr.sec i).full.hub_off h' hy

end WheelFrame

end TangleDatum

end GraphMinor.GM19
