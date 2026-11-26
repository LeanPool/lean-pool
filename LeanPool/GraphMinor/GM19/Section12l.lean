/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section12k

import LeanPool.GraphMinor.GM07.Bridge

/-!
# Graph Minors XIX, Section 12: (12.4)

`exists_circuit_patch` chooses `C_x`, and `exists_hub_patch` chooses `H_x`. Then `theorem_12_4`
gives the cover.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

variable {D : TangleDatum cap χ} {t : ℕ} {x y : Shat}

omit [T2Space S] in
/-- The drawing with a single vertex is a patch. -/
theorem isPatch_point (D : TangleDatum cap χ) {v : Shat} (hv : v ∈ D.rad.G.V) (m : ℕ) :
    IsPatch D (walkDrawing D.rad.G (GraphWalk.nil hv)) ∅ m ∧ (walkDrawing D.rad.G
      (GraphWalk.nil hv)).V = {v} ∧
      (walkDrawing D.rad.G (GraphWalk.nil hv)).E = ∅ := by
  have hV : (walkDrawing D.rad.G (GraphWalk.nil hv)).V = {v} := by
    rw [walkDrawing_V]
    ext x
    simp [GraphWalk.support]
  have hE : (walkDrawing D.rad.G (GraphWalk.nil hv)).E = ∅ := by
    rw [walkDrawing_E]
    ext x
    simp [GraphWalk.edges]
  refine ⟨⟨walkDrawing_isSubdrawing _ _, isPreconnected_walkDrawing_U _, ⟨v, by rw [hV]; rfl⟩, .inr
    ⟨rfl, hE, ?_⟩⟩, hV, hE⟩
  rw [hV]
  exact subsingleton_singleton

omit [T2Space S] in
/-- The choice of `C_x`: a circuit of at most `2t` edges with `x` strictly inside and its inside
maximal, if there is one. -/
theorem exists_circuit_patch (D : TangleDatum cap χ) (ht : t < D.rep)
  (hx : x ∈ D.rad.G.V) :
    ∃ y C A, IsPatch D C A (2 * t) ∧ y ∈ C.V ∧ (x ∈ A \ C.U ∨ (A = ∅ ∧ y = x)) ∧
      ∀ F : Drawing Shat, Drawing.IsCircuitOf F D.rad.G → F.E.ncard ≤ 2 * t → x ∈ D.ins F \ F.U
        → ¬ A ⊆ D.ins F \ F.U := by
  classical
  have : ConnectedSpace Shat := cap.connected
  let 𝓢 : Set (Drawing Shat) := {F | Drawing.IsCircuitOf F D.rad.G ∧ F.E.ncard ≤ 2 * t
    ∧ x ∈ D.ins F \ F.U}
  have hfin : 𝓢.Finite := (finite_circuits D.rad.G).subset fun F hF ↦ ⟨hF.1.2, hF.1.1⟩
  by_cases hne : 𝓢.Nonempty
  · obtain ⟨_, ⟨F, hF, rfl⟩, hmax⟩ := (hfin.image D.ins).exists_maximal (hne.image _)
    have hP := IsPatch.of_circuit hF.1 hF.2.1
    obtain ⟨y, hy⟩ := hP.2.2.1
    refine ⟨y, F, D.ins F, hP, hy, .inl hF.2.2, fun F' h₁ h₂ h₃ hsub ↦ ?_⟩
    have hle : D.ins F' ⊆ D.ins F := hmax ⟨F', ⟨h₁, h₂, h₃⟩, rfl⟩ fun z hz ↦ (hsub hz).1
    have hP' := IsPatch.of_circuit h₁ h₂
    obtain ⟨v, hv⟩ := hP'.2.2.1
    have hU := hP'.U_subset (by omega) ⟨x, h₃.1⟩ (F'.V_subset_U hv)
    exact (hsub (hle hU)).2 (F'.V_subset_U hv)
  · obtain ⟨hP, hV, -⟩ := D.isPatch_point hx (2 * t)
    refine ⟨x, _, ∅, hP, by rw [hV]; rfl, .inr ⟨rfl, rfl⟩, fun F h₁ h₂ h₃ _ ↦ hne ⟨F, h₁, h₂, h₃⟩⟩

omit [T2Space S] in
omit [T2Space Shat] in
/-- Two circuits of `Γ*` with the same set are equal. -/
theorem eq_of_U_eq {F F' : Drawing Shat} (hF : F.IsSubdrawing D.rad.G)
  (hF' : F'.IsSubdrawing D.rad.G) (he : F.U = F'.U) :
    F = F' := by
  have : ConnectedSpace Shat := cap.connected
  have key : ∀ {A B : Drawing Shat}, A.IsSubdrawing D.rad.G → B.IsSubdrawing D.rad.G → A.U = B.U
    → A.E ⊆ B.E := by
    intro A B hA hB hU f hf
    obtain ⟨z, hz⟩ := (hA.2 hf).2.2.1.nonempty
    have hzV : z ∉ D.rad.G.V := ((hA.2 hf).2.1 hz).2
    have hzB : z ∈ B.U := hU ▸ (A.U_eq ▸ .inr (mem_iUnion₂.mpr ⟨f, hf, subset_closure hz⟩))
    obtain ⟨f', hf', hzf'⟩ := B.exists_edge_of_mem hzB fun h' ↦ hzV (hB.1 h')
    exact D.rad.G.edge_eq_of_mem (hA.2 hf) (hB.2 hf') hz hzf' ▸ hf'
  have keyV : ∀ {A B : Drawing Shat}, A.IsSubdrawing D.rad.G → B.IsSubdrawing D.rad.G → A.U = B.U
    → A.V ⊆ B.V :=
    fun {A B} hA hB hU v hv ↦ mem_V_of_mem_U hB (hU ▸ A.V_subset_U hv) (hA.1 hv)
  exact Drawing.ext_of_V_E ((keyV hF hF' he).antisymm (keyV hF' hF he.symm))
    ((key hF hF' he).antisymm (key hF' hF he.symm))

omit [T2Space S] in
/-- The choice of `H_x`: an enclave of at most `8t + 4` edges with `y` strictly inside and its
inside maximal, if there is
one. -/
theorem exists_hub_patch (D : TangleDatum cap χ) (hre : 8 * t + 4 < 2 * D.rep) (ht : 1 ≤ D.rep)
  (hy : y ∈ D.rad.G.V) :
    ∃ H B, IsPatch D H B (8 * t + 4) ∧ (y ∈ B \ H.U ∨ (B = ∅ ∧ y ∈ H.V)) ∧
      ((H.V.ncard = 1 ∧ H.E = ∅ ∧
        ∀ H' : Drawing Shat, IsEnclave D.tb D.ord D.𝒯 H' → H'.E.ncard ≤ 4 * (2 * t) + 4 →
          ¬ (H.V ⊆ D.ins H' \ H'.U)) ∨
      (IsEnclave D.tb D.ord D.𝒯 H ∧ H.E.ncard ≤ 4 * (2 * t) + 4 ∧
      ∀ H' : Drawing Shat, IsEnclave D.tb D.ord D.𝒯 H' → H' ≠ H → H'.E.ncard ≤ 4 * (2 * t) + 4 →
        ¬ (H.U ⊆ D.ins H'))) := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hcirc : ∀ {F : Drawing Shat}, IsEnclave D.tb D.ord D.𝒯 F → Drawing.IsCircuitOf F D.rad.G
    := by
    rintro F ⟨_, _, h⟩
    exact h.2.1
  let 𝓢 : Set (Drawing Shat) := {F | IsEnclave D.tb D.ord D.𝒯 F ∧ F.E.ncard ≤ 4 * (2 * t) + 4
    ∧ y ∈ D.ins F \ F.U}
  have hfin : 𝓢.Finite := (finite_circuits D.rad.G).subset fun F hF ↦ ⟨(hcirc hF.1).2,
    (hcirc hF.1).1⟩
  by_cases hne : 𝓢.Nonempty
  · obtain ⟨_, ⟨F, hF, rfl⟩, hmax⟩ := (hfin.image D.ins).exists_maximal (hne.image _)
    have hFc := hcirc hF.1
    have hP : IsPatch D F (D.ins F) (8 * t + 4) := IsPatch.of_circuit hFc (by have := hF.2.1; omega)
    refine ⟨F, D.ins F, hP, .inl hF.2.2, .inr ⟨hF.1, hF.2.1, fun H' h₁ hne' h₂ hsub ↦ hne' ?_⟩⟩
    have hH'c := hcirc h₁
    have hl : F.length < 2 * D.rep := lt_of_le_of_lt hF.2.1 (by omega)
    have hl' : H'.length < 2 * D.rep := lt_of_le_of_lt h₂ (by omega)
    have hsl := D.isSlope ht
    have hsubI := hsl.monotone F H' hFc.2 hFc.1 hl hH'c.2 hH'c.1 hl' hsub
    have hyi : y ∈ interior (D.ins H') :=
      interior_mono hsubI (hP.mem_interior (by omega) hF.2.2)
    have hyU : y ∉ H'.U := fun h' ↦ by
      have hfr := (ins_facts_of_length hsl hH'c.2 hH'c.1 hl').2.1
      rw [← hfr] at h'
      exact h'.2 hyi
    have hsup : D.ins H' ⊆ D.ins F := hmax ⟨H', ⟨h₁, h₂, interior_subset hyi, hyU⟩, rfl⟩ hsubI
    have heq : D.ins F = D.ins H' := hsubI.antisymm hsup
    have hUU : F.U = H'.U := by
      rw [← hsl.subBd_eq F hFc.2 hFc.1 hl, ← hsl.subBd_eq H' hH'c.2 hH'c.1 hl', heq]
    exact (eq_of_U_eq hFc.1 hH'c.1 hUU).symm
  · obtain ⟨hP, hV, hE⟩ := D.isPatch_point hy (8 * t + 4)
    refine ⟨_, ∅, hP, .inr ⟨rfl, by rw [hV]; rfl⟩, .inl ⟨by rw [hV, ncard_singleton], hE, fun H' h₁
      h₂ hsub ↦ hne ?_⟩⟩
    refine ⟨H', h₁, h₂, hsub ?_⟩
    rw [hV]
    rfl

/-- Every centre has a wheel. -/
theorem exists_centredWheel (D : TangleDatum cap χ) (ht : 4 ≤ t) (hre : 25 * t ≤ D.rep)
    (hx : x ∈ D.rad.G.V) (hsep : ∀ p ∈ D.rad.poles, p ≠ x → 24 * t < D.vDist x p) :
    ∃ y C H A B W k, IsCentredWheel D t x y C H A B W k ∧
      ∀ F : Drawing Shat, Drawing.IsCircuitOf F D.rad.G → F.E.ncard ≤ 2 * t → x ∈ D.ins F \ F.U
        → ¬ A ⊆ D.ins F \ F.U := by
  obtain ⟨y, C, A, hC, hy, hxc, hmax⟩ := D.exists_circuit_patch (t := t) (by omega) hx
  have hyG : y ∈ D.rad.G.V := hC.1.1 hy
  obtain ⟨H, B, hH, hyc, hhub⟩ := D.exists_hub_patch (t := t) (by omega) (by omega) hyG
  have hc : IsCentre D t x y C H A B := ⟨ht, hx, hre, hC, hH, hy, hxc, hyc⟩
  obtain ⟨W, k, hk, hW, hzone, hfar⟩ := hc.exists_wheel hsep hhub
  exact ⟨y, C, H, A, B, W, k, ⟨hc, hk, hW, hzone, hfar⟩, hmax⟩

omit [T2Space S] [T2Space Shat] in
/-- An edge with a label above `ω₀` is internal of size `k`, in a disjoint colour scheme. The paper:
"Since $\chi$ is disjoint, every member of $Z$ is internal". -/
theorem mem_largeEdges (D : TangleDatum cap χ) (hd : χ.IsDisjoint) {k : ℕ} {ω₀ : α}
    (hk : (k = 2 ∧ ω₀ ∈ χ.Ω2.E) ∨ (k = 3 ∧ ω₀ ∈ χ.Ω3.E)) {e : Set S} (he : e ∈ D.P.Γ.E)
    (hle : χ.unionLE ω₀ (D.P.φ e)) : e ∈ D.largeEdges k ω₀ := by
  classical
  have hS := χ.isSurface
  have hnot : ∀ s ∈ χ.Φ.sides, D.P.φ e ∉ (χ.ΩS s).E ∧ ((ω₀ ∈ (χ.ΩS s).E) → False) := by
    intro s hs
    rcases hk with ⟨-, h⟩ | ⟨-, h⟩
    · refine ⟨fun h' ↦ ?_, fun h' ↦ disjoint_left.mp (hd.disj_2_S s hs) h h'⟩
      rcases hle with ⟨-, h₂, -⟩ | ⟨h₃, -⟩ | ⟨s', hs', h₁, -⟩
      · exact disjoint_left.mp (hd.disj_2_S s hs) h₂ h'
      · exact disjoint_left.mp hd.disj_2_3 h h₃
      · exact disjoint_left.mp (hd.disj_2_S s' hs') h h₁
    · refine ⟨fun h' ↦ ?_, fun h' ↦ disjoint_left.mp (hd.disj_3_S s hs) h h'⟩
      rcases hle with ⟨h₂, -⟩ | ⟨-, h₃, -⟩ | ⟨s', hs', h₁, -⟩
      · exact disjoint_left.mp hd.disj_2_3 h₂ h
      · exact disjoint_left.mp (hd.disj_3_S s hs) h₃ h'
      · exact disjoint_left.mp (hd.disj_3_S s' hs') h h₁
  have hint : Painting.IsInternal e := by
    rw [Painting.IsInternal, disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
    intro hm
    obtain ⟨-, hsub⟩ := D.P.Γ.border_edge e he hm
    obtain ⟨s, hs, hes⟩ := exists_arcComp_superset (F := bd S \ χ.Φ.V) he.2.2.1
      (fun x hx ↦ ⟨hsub hx, fun hV ↦ D.P.Γ.disjoint_V he hx (D.P.fits.V_subset hV)⟩)
    exact (hnot s hs).1 (D.P.border_mem e he s hs ⟨hm, hes⟩)
  rcases D.P.Γ.size_cases he with h2 | h3
  · rcases hk with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · refine ⟨he, hint, h2, .inl ⟨rfl, ?_⟩⟩
      rcases hle with ⟨-, -, h'⟩ | ⟨h₃, -⟩ | ⟨s', hs', h₁, -⟩
      · exact h'
      · exact absurd h₃ (disjoint_left.mp hd.disj_2_3 h)
      · exact absurd h₁ (disjoint_left.mp (hd.disj_2_S s' hs') h)
    · exfalso
      have hm := D.P.internal_2_mem e he hint h2
      rcases hle with ⟨h₂, -⟩ | ⟨-, h₃, -⟩ | ⟨s', hs', h₁, -⟩
      · exact disjoint_left.mp hd.disj_2_3 h₂ h
      · exact disjoint_left.mp hd.disj_2_3 hm h₃
      · exact disjoint_left.mp (hd.disj_3_S s' hs') h h₁
  · rcases hk with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exfalso
      have hm := D.P.internal_3_mem e he hint h3
      rcases hle with ⟨-, h₂, -⟩ | ⟨h₃, -⟩ | ⟨s', hs', h₁, -⟩
      · exact disjoint_left.mp hd.disj_2_3 h₂ hm
      · exact disjoint_left.mp hd.disj_2_3 h h₃
      · exact disjoint_left.mp (hd.disj_2_S s' hs') h h₁
    · refine ⟨he, hint, h3, .inr ⟨rfl, ?_⟩⟩
      rcases hle with ⟨h₂, -⟩ | ⟨-, -, h'⟩ | ⟨s', hs', h₁, -⟩
      · exact absurd h (disjoint_left.mp hd.disj_2_3 h₂)
      · exact h'
      · exact absurd h₁ (disjoint_left.mp (hd.disj_3_S s' hs') h)

/-- **Graph Minors XIX, (12.4)** (page 364): "There is a cover $\mathcal{W}$ with $|\mathcal{W}| \le
m + c(\Sigma_\chi)$, each member of
which has radius $\le 2n \cdot 5^{2m}$." Uses the proved VII (11.10) through (7.1). -/
theorem theorem_12_4_proof (D : TangleDatum cap χ) (hd : χ.IsDisjoint) {m n k : ℕ} {ω₀ : α}
    (hk : (k = 2 ∧ ω₀ ∈ χ.Ω2.E) ∨ (k = 3 ∧ ω₀ ∈ χ.Ω3.E)) (hn : 4 ≤ n)
      (hfl : D.IsFlawedInternally m n k ω₀) :
    ∃ 𝒲, D.IsWheelCover ω₀ 𝒲 ∧ 𝒲.ncard ≤ m + numCuffs S ∧ ∀ W ∈ 𝒲, D.wheelRadius W ≤ 2 * n * 5 ^
      (2 * m) := by
  classical
  obtain ⟨X₂, hX₂G, hX₂c, hpoles, t, hnt, htle, hsep, hedge⟩ := theorem_12_3_proof D hn hfl
  have ht : 4 ≤ t := by omega
  have hre : 25 * t ≤ D.rep := by
    have h25 : 5 ^ (2 * m + 2) * n = 25 * (5 ^ (2 * m) * n) := by rw [pow_add]; ring
    have := hfl.1
    omega
  have hmain : ∀ x ∈ X₂, ∃ y C H A B W k, IsCentredWheel D t x y C H A B W k ∧
      ∀ F : Drawing Shat, Drawing.IsCircuitOf F D.rad.G → F.E.ncard ≤ 2 * t → x ∈ D.ins F \ F.U
        → ¬ A ⊆ D.ins F \ F.U :=
    fun x hx ↦ D.exists_centredWheel ht hre (hX₂G hx) fun p hp hne ↦ hsep x hx p
      (hpoles hp) hne.symm
  have : ConnectedSpace Shat := cap.connected
  have : Nonempty (Drawing Shat) := ⟨D.rad.G⟩
  choose! Y C H A B W K hW hmax using hmain
  have hX₂fin : X₂.Finite := D.rad.G.finite_V.subset hX₂G
  refine ⟨W '' X₂, ⟨hX₂fin.image _, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨H x, 2 * t, (hW x hx).hub⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ hne
    exact (hW x hx).disjoint (hW x' hx') (hsep x hx x' hx' fun e ↦ hne (e ▸ rfl))
  · rintro _ ⟨x, hx, rfl⟩
    exact (hW x hx).bd_in_interior fun p hp hne ↦ hsep x hx p (hpoles hp) hne.symm
  · intro r hr
    exact ⟨W r, mem_image_of_mem _ (hpoles hr), (hW r (hpoles hr)).x_mem.1⟩
  · intro e he hle
    obtain ⟨x, hx, hdx⟩ := hedge e (D.mem_largeEdges hd hk he hle)
    exact ⟨W x, mem_image_of_mem _ hx, (hW x hx).edge_subset (hmax x hx) he hdx⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hW x hx).interior_vertex
  · exact (ncard_image_le hX₂fin).trans hX₂c
  · rintro _ ⟨x, hx, rfl⟩
    have h₁ : D.wheelRadius (W x) ≤ 2 * t := Nat.sInf_le ⟨H x, (hW x hx).hub⟩
    have h₂ : 2 * n * 5 ^ (2 * m) = 2 * (5 ^ (2 * m) * n) := by ring
    omega

end TangleDatum

end GraphMinor.GM19
