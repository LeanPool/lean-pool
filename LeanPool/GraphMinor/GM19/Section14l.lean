/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14j

/-!
# Graph Minors XIX, Section 14: levels of a sector

Two spokes that meet have the same length, and (13.7) gives disjoint paths in the sector between the
vertices of `Γ` at the same
position on them. This is the "paths given by 13.6" of the proof of (14.1): the paper's
cross-reference is to (13.7).
-/

@[expose] public section

namespace GraphMinor.GM19

universe w

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α} {D : TangleDatum cap χ} {W Δ Δ' : Set Shat}
    {H C : Drawing Shat} {ρ : ℕ}
  {r v₁ v₂ h₁ h₂ : Shat} {f₁ f₂ : Set Shat}

theorem GraphWalk.support_mem_V {T : Type} [TopologicalSpace T] {G : Drawing T} {a b : T}
  (K : GraphWalk G.toGraph a b) {z : T} (hz : z ∈ K.support) : z ∈ G.V := by
  induction K with
  | nil h =>
    obtain rfl : z = _ := by simpa [GraphWalk.support] using hz
    exact h
  | cons hl t ih =>
    rw [GraphWalk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hl.2.1
    · exact ih hz

namespace TangleDatum

/-- Two points of `Σ̂` are joined by a walk of `sk(Γ)` in `X`. -/
def SkJoined (D : TangleDatum cap χ) (X : Set Shat) : Shat → Shat → Prop :=
  Relation.ReflTransGen fun x y ↦ x ∈ X ∧ y ∈ X ∧ ∃ a b, cap.emb a = x ∧ cap.emb b = y
    ∧ D.P.Γ.skAdj.Adj a b

omit [T2Space S] [T2Space Shat] in
theorem SkJoined.mono {X Y : Set Shat} (h : X ⊆ Y) {x y : Shat} (hj : D.SkJoined X x y) :
  D.SkJoined Y x y :=
  Relation.ReflTransGen.mono (r := fun x y ↦ x ∈ X ∧ y ∈ X ∧ ∃ a b, cap.emb a = x ∧ cap.emb b = y
    ∧ D.P.Γ.skAdj.Adj a b) (fun _ _ h' ↦ ⟨h h'.1, h h'.2.1, h'.2.2⟩) _ _ hj

omit [T2Space S] [T2Space Shat] in
theorem skJoined_of_walk {Sk : Drawing Shat} {G : Drawing Δ} (hG : D.IsSkPart Δ Sk G) {a b : Δ}
  (K : GraphWalk G.toGraph a b) {X : Set Shat}
    (hX : ∀ z ∈ K.support, z.1 ∈ X) : ∀ z ∈ K.support, D.SkJoined X a.1 z.1 := by
  induction K with
  | nil h =>
    intro z hz
    obtain rfl : z = _ := by simpa [GraphWalk.support] using hz
    exact Relation.ReflTransGen.refl
  | @cons u v w e hl t ih =>
    intro z hz
    rw [GraphWalk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact Relation.ReflTransGen.refl
    · have hs : v.1 ∈ X := hX _ (by
        rw [GraphWalk.support_cons]
        exact List.mem_cons_of_mem _ t.start_mem_support)
      have hrest := ih (fun z hz ↦ hX z (by
        rw [GraphWalk.support_cons]
        exact List.mem_cons_of_mem _ hz)) z hz
      rcases hG.link _ _ _ hl with e' | ⟨p, q, hp, hq, hadj⟩
      · rw [e']
        exact hrest
      · exact Relation.ReflTransGen.head
          ⟨hX _ (by rw [GraphWalk.support_cons]; exact List.mem_cons_self), hs, p, q, hp, hq, hadj⟩
          hrest

omit [T2Space Shat] in
/-- The vertices of `Γ` on a spoke are those at even position. -/
theorem IsSpokeWalk.even_hatV {K : GraphWalk D.rad.G.toGraph v₁ h₁} (hv : v₁ ∈ D.P.Γ.hatV cap) {p :
  ℕ} (hp : p ≤ K.length) :
    GraphWalk.vertexAt K p ∈ D.P.Γ.hatV cap ↔ Even p := by
  obtain ⟨P, Q, -, hl⟩ := GraphWalk.exists_split_at K hp
  have h := D.even_length_walk P
  rw [hl] at h
  rw [h]
  exact ⟨fun h' ↦ ⟨fun _ ↦ h', fun _ ↦ hv⟩, fun h' ↦ h'.mp hv⟩

/-- **The paths of (13.7), for a sector.** -/
theorem IsFullSector.levels {K₁ : GraphWalk D.rad.G.toGraph v₁ h₁} {K₂ : GraphWalk D.rad.G.toGraph
  v₂ h₂} {Z : GraphWalk D.rad.G.toGraph v₁ v₂}
    (hs : D.IsFullSector W H r f₁ f₂ K₁ K₂ Z Δ Δ' C) (hopt : D.IsOptimalWheelHub W H ρ)
      (hbdS : discBd W ⊆ cap.emb '' (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) (h1 : D.IsSpokeWalk W H K₁)
      (h2 : D.IsSpokeWalk W H K₂) (hv₁ : v₁ ∈ D.P.Γ.hatV cap)
    (hx : ∃ x ∈ K₁.support, x ∈ K₂.support) :
    K₁.length = K₂.length ∧ ∃ P : ℕ → Set Shat, (∀ j k, 2 * j ≤ K₁.length → 2 * k ≤ K₁.length
      → j ≠ k → Disjoint (P j) (P k)) ∧
      ∀ j, 2 * j ≤ K₁.length → GraphWalk.vertexAt K₁ (2 * j) ∈ P j ∧ GraphWalk.vertexAt K₂
        (2 * j) ∈ P j ∧ P j ⊆ D.P.Γ.hatV cap ∧ (∀ y ∈ P j, D.SkJoined (P j) (GraphWalk.vertexAt K₁
          (2 * j)) y) ∧
        ((GraphWalk.vertexAt K₁ (2 * j) = GraphWalk.vertexAt K₂ (2 * j) ∧ P j
          = {GraphWalk.vertexAt K₁ (2 * j)}) ∨
          (GraphWalk.vertexAt K₁ (2 * j) ∉ K₂.support ∧ GraphWalk.vertexAt K₂ (2 * j) ∉ K₁.support
            ∧ P j ⊆ Δ)) := by
  classical
  obtain ⟨u, A₁, A₂, T₁, T₂, hK₁, hK₂, hT, hmeet, hZU⟩ := hs.Z_fan hx
  obtain rfl : h₁ = h₂ := h1.same_end h2 hx.choose_spec.1 hx.choose_spec.2
  obtain rfl : T₁ = T₂ := eq_of_heq hT
  subst hK₁ hK₂
  have hW := hopt.toIsWheelHubOfRadius
  have hfan : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T₁ := ⟨hW, hbdS, hin, hs.r_mem.1, hs.r_mem.2, hs.ne,
    hs.link₁, hs.link₂, h1, h2, hmeet⟩
  obtain ⟨C', hC'⟩ := hfan.exists_circuit
  have hbd' : C'.U = discBd Δ := by
    rw [hs.bd_eq, hfan.U_eq hC', hZU]
    ext x
    simp only [mem_union]
    tauto
  have hb : D.IsBoundarySector W H r Δ C' := { hs.boundary with Dv_circuit := hC'.circuit, Dv_U
    := hbd' }
  have hlen := hfan.length_eq
  have hlen' : (A₁.append T₁).length = (A₂.append T₁).length := by
    rw [GraphWalk.length_append, GraphWalk.length_append, hlen]
  obtain ⟨Sk, G, hG, P, hdis, hP⟩ := hfan.theorem_13_7_proof hopt hbdS hin hC' hb
  set x₁ := fun j ↦ GraphWalk.vertexAt (A₁.append T₁) (2 * j) with hx₁def
  set x₂ := fun j ↦ GraphWalk.vertexAt (A₂.append T₁) (2 * j) with hx₂def
  have hone : ∀ j, ∃ Q : Set Shat, 2 * j ≤ (A₁.append T₁).length → Q ⊆ P j ∧ x₁ j ∈ Q ∧ x₂ j ∈ Q
    ∧ Q ⊆ D.P.Γ.hatV cap ∧ (∀ y ∈ Q, D.SkJoined Q (x₁ j) y) ∧
      ((x₁ j = x₂ j ∧ Q = {x₁ j}) ∨ (x₁ j ∉ (A₂.append T₁).support ∧ x₂ j ∉ (A₁.append T₁).support
        ∧ Q ⊆ Δ)) := fun j ↦ by
    by_cases hj : 2 * j ≤ (A₁.append T₁).length
    · have hh₁ : x₁ j ∈ D.P.Γ.hatV cap := (IsSpokeWalk.even_hatV (K := A₁.append T₁) hv₁ hj).mpr
        (even_two_mul _)
      rcases hP j hj with ⟨e, -, -, hPj⟩ | ⟨n₁, n₂, hsub, a, b, ha, hb', K, -, hK⟩
      · refine ⟨{x₁ j}, fun _ ↦ ⟨singleton_subset_iff.mpr (by rw [hPj]; exact rfl),
          rfl, e.symm, singleton_subset_iff.mpr hh₁, ?_, .inl ⟨e, rfl⟩⟩⟩
        rintro y rfl
        exact Relation.ReflTransGen.refl
      · have hG' : ∀ z : Δ, z ∈ G.V ↔ z.1 ∈ D.P.Γ.hatV cap := hG.mem_V
        refine ⟨{y | ∃ z ∈ K.support, z.1 = y}, fun _ ↦ ⟨?_, ⟨a, K.start_mem_support, ha⟩, ⟨b,
          K.end_mem_support, hb'⟩, ?_, ?_, .inr ⟨n₁, n₂, ?_⟩⟩⟩
        · rintro _ ⟨z, hz, rfl⟩
          exact hK z hz
        · rintro _ ⟨z, hz, rfl⟩
          exact (hG' z).mp (GraphWalk.support_mem_V K hz)
        · rintro _ ⟨z, hz, rfl⟩
          have := skJoined_of_walk hG K (X := {y | ∃ z ∈ K.support, z.1 = y})
            (fun z hz ↦ ⟨z, hz, rfl⟩) z hz
          rw [ha] at this
          exact this
        · rintro _ ⟨z, hz, rfl⟩
          exact hsub (hK z hz)
    · exact ⟨∅, fun h' ↦ absurd h' hj⟩
  choose Q hQ using hone
  refine ⟨hlen', Q, fun j k hj hk hne ↦ (hdis j k hj hk hne).mono (hQ j hj).1 (hQ k hk).1,
    fun j hj ↦ ?_⟩
  obtain ⟨-, h₁, h₂, h₃, h₄, h₅⟩ := hQ j hj
  exact ⟨h₁, h₂, h₃, h₄, h₅⟩

end TangleDatum

end GraphMinor.GM19
