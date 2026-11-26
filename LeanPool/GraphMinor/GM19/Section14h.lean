/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14g

/-!
# Graph Minors XIX, Section 14: the frame of a wheel and its arms

For one wheel we fix an optimal hub, a spoke at each vertex, the rim, and the sector at each vertex
of `R*` on the rim. From these come the hub
sector and the `r*`-sectors of the proof of (14.1).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ}

omit [T2Space S] in
omit [T2Space Shat] in
/-- A wheel has an optimal hub. -/
theorem exists_optimal_hub (h : D.IsWheel W) : ∃ H, D.IsOptimalWheelHub W H (D.wheelRadius W) := by
  have hne : {ρ : ℕ | ∃ H : Drawing Shat, D.IsWheelHubOfRadius W H ρ}.Nonempty := by
    obtain ⟨H, ρ, hH⟩ := h
    exact ⟨ρ, H, hH⟩
  obtain ⟨H, hH⟩ := Nat.sInf_mem hne
  by_cases hone : ∃ H' : Drawing Shat, D.IsWheelHubOfRadius W H' (D.wheelRadius W) ∧ H'.V.ncard = 1
  · obtain ⟨H', h₁, h₂⟩ := hone
    exact ⟨H', { h₁ with ρ_eq_radius := rfl, one_vertex_priority := .inl h₂ }⟩
  · exact ⟨H, { hH with ρ_eq_radius := rfl, one_vertex_priority := .inr hone }⟩

/-- The sector at the `i`th vertex of `R*` of a rim. -/
structure RimSector (R : Rim D W) (sp : SpokeSystem D W H) (i : ℕ) where
  /-- The first rim edge at the sector pole. -/
  f : Set Shat
  /-- The second rim edge at the sector pole. -/
  g : Set Shat
  /-- The radial walk joining the successive rim vertices. -/
  Z : GraphWalk D.rad.G.toGraph (R.vert i) (R.vert (i + 1))
  /-- The closed disc of the sector. -/
  Δ : Set Shat
  /-- The other closed disc in the sector decomposition. -/
  Δ' : Set Shat
  /-- The circuit bounding the sector disc. -/
  C : Drawing Shat
  full : D.IsFullSector W H (R.reg i) f g (R.spoke sp i) (R.spoke sp (i + 1)) Z Δ Δ' C
  only : ∀ e ∈ D.rad.G.E, e ⊆ discBd W → R.reg i ∈ closure e → e = f ∨ e = g

/-- A sector of a rim is a sector at `r`. -/
noncomputable def RimSector.toSectorAt {R : Rim D W} {sp : SpokeSystem D W H} {i : ℕ}
  (s : RimSector R sp i) : SectorAt sp (R.reg i) :=
  ⟨⟨R.vert i, R.vert_mem i⟩, ⟨R.vert (i + 1), R.vert_mem (i + 1)⟩, s.f, s.g, s.Z, s.Δ, s.Δ', s.C,
    s.full, s.only⟩

theorem exists_rimSector (hopt : D.IsOptimalWheelHub W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S)) (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    (R : Rim D W) (sp : SpokeSystem D W H) (i : ℕ) : Nonempty (RimSector R sp i) := by
  have hW := hopt.toIsWheelHubOfRadius
  have hi := R.mod_lt i
  have hvert : R.vert (i % R.k) = R.vert i := by rw [Rim.vert, Rim.vert, Nat.mod_mod]
  have hne : R.vert i ≠ R.vert (i + 1) := by
    have h := R.vert_ne_succ hi
    rw [hvert] at h
    have h₂ : R.vert (i % R.k + 1) = R.vert (i + 1) := by
      rw [Rim.vert, Rim.vert]
      congr 2
      exact Nat.mod_add_mod i R.k 1
    rwa [h₂] at h
  obtain ⟨f, g, hl₁, hl₂, hf, hg⟩ := R.exists_links i
  obtain ⟨Z, Δ, Δ', C, hs⟩ := exists_fullSector hopt hbdS hin (R.spoke_spoke sp i)
    (R.spoke_spoke sp (i + 1)) (R.reg_mem i) hl₁ hl₂ hne hf hg
  obtain ⟨f₁, f₂, v₁, v₂, -, -, -, -, -, honly⟩ := hW.exists_two_bd_edges hbdS hin (R.reg_mem i).1
    (R.reg_mem i).2
  have hrf : ∀ {e v}, D.rad.G.toGraph.IsLink e (R.reg i) v → R.reg i ∈ closure e
    := fun {e v} hl ↦ by
    have hm : R.reg i ∈ closure e ∩ D.rad.G.V := by
      rw [hl.2.2.2]
      exact .inl rfl
    exact hm.1
  have hfg : f ≠ g := by
    rintro rfl
    have hm : R.vert i ∈ closure f ∩ D.rad.G.V := by
      rw [hl₁.2.2.2]
      exact .inr rfl
    rw [hl₂.2.2.2] at hm
    rcases hm with hm | hm
    · exact (R.reg_mem i).1.2 (hm ▸ (R.vert_mem i).1)
    · exact hne hm
  refine ⟨⟨f, g, Z, Δ, Δ', C, hs, fun e he heb hre ↦ ?_⟩⟩
  have h₁ := honly f hl₁.1 hf (hrf hl₁)
  have h₂ := honly g hl₂.1 hg (hrf hl₂)
  rcases honly e he heb hre with he' | he' <;> rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
    first
    | exact .inl (he'.trans h₁.symm)
    | exact .inr (he'.trans h₂.symm)
    | exact absurd (h₁.trans h₂.symm) hfg

/-- All that we fix for one wheel. -/
structure WheelFrame (D : TangleDatum cap χ) (W : Set Shat) where
  /-- The hub drawing. -/
  H : Drawing Shat
  /-- The radius of the chosen hub. -/
  ρ : ℕ
  hopt : D.IsOptimalWheelHub W H ρ
  hbdS : discBd W ⊆ cap.emb '' (univ \ bd S)
  hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty
  hrep : 6 * ρ + 14 ≤ D.rep
  /-- The spokes joining rim vertices to the hub. -/
  sp : SpokeSystem D W H
  /-- The rim walk and its base vertex. -/
  R : Rim D W
  /-- The sector between each two successive spokes. -/
  sec : ∀ i, RimSector R sp i

theorem exists_wheelFrame (h : D.IsWheel W) (hbdS : discBd W ⊆ cap.emb '' (univ \ bd S)) (hin :
  ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) (hrep : 6 * D.wheelRadius W + 14 ≤ D.rep) :
    ∃ fr : WheelFrame D W, fr.ρ = D.wheelRadius W := by
  obtain ⟨H, hopt⟩ := exists_optimal_hub h
  have hW := hopt.toIsWheelHubOfRadius
  obtain ⟨sp⟩ := exists_spokeSystem hW
  obtain ⟨R⟩ := exists_rim hW hbdS hin
  have hsec := fun i ↦ exists_rimSector hopt hbdS hin R sp i
  exact ⟨⟨H, _, hopt, hbdS, hin, hrep, sp, R, fun i ↦ (hsec i).some⟩, rfl⟩

/-- The left inverse of `Σ → Σ̂`. -/
noncomputable def pre (_ : TangleDatum cap χ) : Shat → S :=
  haveI : Nonempty S := χ.connected.toNonempty
  Function.invFun cap.emb

omit [T2Space S] [T2Space Shat] in
theorem pre_emb (D : TangleDatum cap χ) (x : S) : D.pre (cap.emb x) = x := by
  have : Nonempty S := χ.connected.toNonempty
  exact Function.leftInverse_invFun cap.isEmbedding.injective x

open Classical in
/-- The march with `front` first, and then the rest of `T` in any order. -/
noncomputable def orderedList (front : List S) (T : Set S) (hT : T.Finite) : List S :=
  (front.filter (· ∈ T)).dedup ++ (hT.toFinset \ front.toFinset).toList

omit [TopologicalSpace S] [T2Space S] in
theorem orderedList_nodup (front : List S) {T : Set S} (hT : T.Finite) :
  (orderedList front T hT).Nodup := by
  classical
  refine List.nodup_append.mpr ⟨List.nodup_dedup _, Finset.nodup_toList _, ?_⟩
  intro a ha b hb e
  subst e
  simp only [Finset.mem_toList, Finset.mem_sdiff, List.mem_toFinset] at hb
  exact hb.2 (List.mem_of_mem_filter (List.mem_dedup.mp ha))

omit [TopologicalSpace S] [T2Space S] in
theorem orderedList_set (front : List S) {T : Set S} (hT : T.Finite) : {v | v ∈ orderedList front T
  hT} = T := by
  classical
  ext v
  simp only [orderedList, mem_ofPred_eq, List.mem_append, List.mem_dedup, List.mem_filter,
    Finset.mem_toList, Finset.mem_sdiff, hT.mem_toFinset, List.mem_toFinset, decide_eq_true_eq]
  tauto

omit [TopologicalSpace S] [T2Space S] in
theorem orderedList_length (front : List S) {T : Set S} (hT : T.Finite) :
  (orderedList front T hT).length = T.ncard := by
  classical
  have hnd := orderedList_nodup front hT
  have h : T = ↑(orderedList front T hT).toFinset := by
    ext v
    rw [Finset.mem_coe, List.mem_toFinset]
    exact (Set.ext_iff.mp (orderedList_set front hT) v).symm
  conv_rhs => rw [h]
  rw [ncard_coe_finset, List.toFinset_card_of_nodup hnd]

/-- The arm of the disc `Δ` with the vertices `X`. -/
noncomputable def discArm (D : TangleDatum cap χ) (Δ X : Set Shat) (h :
  D.Γ.toHypergraph.IsSeparation (D.partPlus Δ X) (partIn cap D.Γ (closure Δᶜ)))
    (front : List S) : Arm D.Γ where
  minus := D.partPlus Δ X
  compl := partIn cap D.Γ (closure Δᶜ)
  isSeparation := h
  π := orderedList front (D.partPlus Δ X ∩ partIn cap D.Γ (closure Δᶜ)).vertexSet
    (D.partPlus Δ X ∩ partIn cap D.Γ (closure Δᶜ)).vertexSet_finite
  π_nodup := orderedList_nodup _ _
  π_set := orderedList_set _ _

/-- The enumeration of the vertices of `Γ` on a walk of `Γ*`. -/
noncomputable def walkMarch (D : TangleDatum cap χ) {a b : Shat} (K : GraphWalk D.rad.G.toGraph a
  b) : List S := by
  classical exact (K.support.filter (· ∈ cap.emb '' D.Γ.V)).map D.pre

namespace WheelFrame

variable (fr : WheelFrame D W)

theorem hW : D.IsWheelHubOfRadius W fr.H fr.ρ := fr.hopt.toIsWheelHubOfRadius

theorem spoke_spoke (i : ℕ) : D.IsSpokeWalk W fr.H (fr.R.spoke fr.sp i) := fr.R.spoke_spoke fr.sp i

/-- The sectors and the hub with its spokes cover `W`. -/
theorem cover {x : Shat} (hx : x ∈ W) (hxA : x ∉ fr.sp.A) : ∃ i, x ∈ (fr.sec i).Δ := by
  obtain ⟨r, hr⟩ := SpokeSystem.cover fr.hW fr.sp fr.hbdS fr.hin (ι := ℕ) fr.R.reg (fun i ↦
    (fr.sec i).toSectorAt)
    (fun r hr ↦ by
      obtain ⟨i, -, rfl⟩ := fr.R.exists_reg r hr
      exact ⟨i, rfl⟩) hx hxA
  exact ⟨r, hr⟩

theorem disjoint_int {i j : ℕ} (hne : fr.R.reg i ≠ fr.R.reg j) : Disjoint (discInt (fr.sec i).Δ)
  (discInt (fr.sec j).Δ) :=
  SectorAt.disjoint_int fr.hW fr.hbdS fr.hin (fr.sec i).toSectorAt (fr.sec j).toSectorAt hne

/-- The vertices of `Γ` in `Σ̂` that are on both spokes of the sector `i`. -/
noncomputable def secX (i : ℕ) : Set Shat := (cap.emb '' D.Γ.V) ∩ (walkDrawing D.rad.G
  (fr.R.spoke fr.sp i)).U ∩ (walkDrawing D.rad.G (fr.R.spoke fr.sp (i + 1))).U

theorem secX_sub (i : ℕ) : fr.secX i ⊆ cap.emb '' D.Γ.V := fun _ h ↦ h.1.1

theorem secX_off (i : ℕ) : Disjoint (fr.secX i) (discInt (fr.sec i).Δ) :=
  disjoint_left.mpr fun _ h h' ↦ disjoint_left.mp ((fr.sec i).full.spoke_off _ _ _
    (fr.spoke_spoke i)) h.1.2 h'

theorem sec_sep (i : ℕ) : D.Γ.toHypergraph.IsSeparation (D.partPlus (fr.sec i).Δ (fr.secX i))
  (partIn cap D.Γ (closure (fr.sec i).Δᶜ)) :=
  sep_plus (fr.sec i).full.boundary.Dv_circuit (fr.sec i).full.boundary.is_disc
    (fr.sec i).full.boundary.Dv_U.symm (fr.secX_sub i)

/-- The enumeration `μ(v)` of the vertices of `Γ` on the spoke `i`. -/
noncomputable def lev (i : ℕ) : List S := D.walkMarch (fr.R.spoke fr.sp i)

/-- The `r*`-sector at the `i`th vertex of `R*`. -/
noncomputable def secArm (i : ℕ) : Arm D.Γ := D.discArm (fr.sec i).Δ (fr.secX i) (fr.sec_sep i)
  (fr.lev i ++ fr.lev (i + 1))

theorem hub_data (hc : fr.H.V.ncard ≠ 1) : IsEnclave D.tb D.ord D.𝒯 fr.H ∧ fr.H.E.ncard
  ≤ 4 * fr.ρ + 4 ∧ IsInsOf D.rad D.ord D.𝒯 fr.H (D.ins fr.H) := by
  rcases fr.hW.hub_cases with ⟨z, hV, -, -⟩ | ⟨hH, hle, -, -⟩
  · rw [hV, ncard_singleton] at hc
    exact absurd rfl hc
  · obtain ⟨-, -, -, hcirc, -⟩ := id hH
    have hrep := fr.hW.rep_ge
    exact ⟨hH, hle, D.ins_spec hcirc (by omega)⟩

theorem hub_sep (hc : fr.H.V.ncard ≠ 1) : D.Γ.toHypergraph.IsSeparation (D.partPlus (D.ins fr.H) ∅)
  (partIn cap D.Γ (closure (D.ins fr.H)ᶜ)) := by
  obtain ⟨-, -, hi⟩ := fr.hub_data hc
  exact sep_plus hi.1 hi.2.2.1 hi.2.2.2.1 (empty_subset _)

/-- The hub sector. -/
noncomputable def hubArm (hc : fr.H.V.ncard ≠ 1) : Arm D.Γ := D.discArm (D.ins fr.H) ∅
  (fr.hub_sep hc) []

/-- The arms at `W`. -/
def arms : Set (Arm D.Γ) := {A | (∃ i < fr.R.k, A = fr.secArm i) ∨ ∃ hc : fr.H.V.ncard ≠ 1, A
  = fr.hubArm hc}

theorem arms_finite : fr.arms.Finite := by
  refine ((finite_lt_nat fr.R.k).image fr.secArm |>.union (Set.Subsingleton.finite (s
    := {A | ∃ hc : fr.H.V.ncard ≠ 1, A = fr.hubArm hc}) ?_)).subset ?_
  · rintro _ ⟨h, rfl⟩ _ ⟨h', rfl⟩
    rfl
  · rintro A (⟨i, hi, rfl⟩ | h)
    · exact .inl ⟨i, hi, rfl⟩
    · exact .inr h

end WheelFrame

end TangleDatum

end GraphMinor.GM19
