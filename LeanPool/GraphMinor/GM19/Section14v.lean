/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14u
public import LeanPool.GraphMinor.GM19.BiteArc

/-!
# Graph Minors XIX, Section 14: the arcs of the rim

Between two consecutive vertices of `Γ` on the rim there is one vertex of `R*`. Here we show that
the arc of the rim between them has no other vertex of `Γ`, and that
each arc of the rim between two vertices of `Γ` contains a vertex of `R*`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

universe w

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α} {D : TangleDatum cap χ} {W : Set Shat}

theorem IsLineWithEnds.isPathConnected_diff {T : Type} [TopologicalSpace T] {L : Set T} {u v : T}
  (h : IsLineWithEnds L u v) : IsPathConnected (L \ {u}) := by
  obtain ⟨f, hf₀, hf₁⟩ := h
  have hs : L \ {u} = (fun x ↦ (f x).1) '' {x | x ≠ 0} := by
    ext y
    constructor
    · rintro ⟨hy, hne⟩
      refine ⟨f.symm ⟨y, hy⟩, ?_, by simp⟩
      intro h0
      apply hne
      have : f (f.symm ⟨y, hy⟩) = f 0 := by rw [h0]
      rw [f.apply_symm_apply] at this
      exact (congrArg Subtype.val this).trans hf₀
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(f x).2, fun h' ↦ hx (f.injective (Subtype.ext (h'.trans hf₀.symm)))⟩
  rw [hs]
  refine IsPathConnected.image ?_ (by fun_prop)
  have hconv : {x : unitInterval | x ≠ 0} = (fun t : Ioc (0 : ℝ) 1 ↦ (⟨t.1, t.2.1.le, t.2.2⟩ :
    unitInterval)) '' univ := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x.1, lt_of_le_of_ne x.2.1 (fun h' ↦ hx (Subtype.ext h'.symm)), x.2.2⟩, mem_univ _,
        rfl⟩
    · rintro ⟨t, -, rfl⟩ h'
      have := congrArg Subtype.val h'
      exact t.2.1.ne' this
  rw [hconv]
  have : PathConnectedSpace (Ioc (0 : ℝ) 1) := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Ioc 0 1).isPathConnected ⟨1, by norm_num, le_rfl⟩)
  exact isPathConnected_univ.image (by fun_prop)

namespace TangleDatum.Rim

/-- The rim arc through `R.reg i`. -/
theorem exists_arc (R : Rim D W) (i : ℕ) : ∃ A : Set Shat, IsPathConnected A ∧ A ⊆ discBd W
  ∧ Disjoint A (D.P.Γ.hatV cap) ∧ R.reg i ∈ A ∧ R.vert i ∈ closure A ∧ R.vert (i + 1) ∈ closure A
    := by
  have hT2 := cap.isSurface
  obtain ⟨f, g, hf, hg, hfW, hgW⟩ := R.exists_links i
  have hreg := R.reg_mem i
  have hvh : ∀ j, R.vert j ∈ D.P.Γ.hatV cap := fun j ↦ (R.vert_mem j).1
  have hcW : IsClosed (discBd W) := R.U_eq ▸ (walkDrawing D.rad.G R.B).isClosed_U
  have key : ∀ {f : Set Shat} {v : Shat}, D.rad.G.toGraph.IsLink f (R.reg i) v → f ⊆ discBd W
    → v ∈ D.P.Γ.hatV cap →
      ∃ A : Set Shat, IsPathConnected A ∧ A ⊆ discBd W ∧ Disjoint A (D.P.Γ.hatV cap) ∧ R.reg i ∈ A
        ∧ v ∈ closure A := by
    intro f v hf hfW hv
    obtain ⟨hfE, hrV, hvV, hcl⟩ := hf
    have hne : v ≠ R.reg i := fun e ↦ hreg.1.2 (e ▸ hv)
    have hL : IsLineWithEnds (closure f) v (R.reg i) := by
      rcases D.rad.G.edge_cond f hfE with ⟨u, w, huw, h₁, h₂⟩ | ⟨u, h₁, -⟩
      · have h₃ : ({u, w} : Set Shat) = {R.reg i, v} := h₁.symm.trans hcl
        have hu : u = R.reg i ∨ u = v := by simpa using h₃.subset (mem_insert u {w})
        have hw : w = R.reg i ∨ w = v := by simpa using h₃.subset (mem_insert_of_mem u rfl)
        rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
        · exact absurd rfl huw
        · exact GM11.IsLineWithEnds.symm h₂
        · exact h₂
        · exact absurd rfl huw
      · have h₃ : (R.reg i ∈ ({u} : Set Shat)) ∧ v ∈ ({u} : Set Shat) := by
          rw [← h₁, hcl]
          simp
        exact absurd (h₃.2.trans h₃.1.symm) hne
    refine ⟨closure f \ {v}, IsLineWithEnds.isPathConnected_diff hL,
      fun y hy ↦ closure_minimal hfW hcW hy.1, ?_, ?_, ?_⟩
    · refine disjoint_left.mpr fun y hy hyV ↦ ?_
      have hyG : y ∈ closure f ∩ D.rad.G.V := ⟨hy.1, D.rad.isPreRadial.2.1 hyV⟩
      rw [hcl] at hyG
      rcases hyG with rfl | h'
      · exact hreg.1.2 hyV
      · exact hy.2 h'
    · refine ⟨?_, fun h' ↦ hne h'.symm⟩
      have : R.reg i ∈ closure f ∩ D.rad.G.V := by rw [hcl]; simp
      exact this.1
    · have := line_subset_closure_diff hL (finite_singleton v)
      refine this ?_
      have : v ∈ closure f ∩ D.rad.G.V := by rw [hcl]; simp
      exact this.1
  obtain ⟨A₁, h₁, h₂, h₃, h₄, h₅⟩ := key hf hfW (hvh _)
  obtain ⟨A₂, h₆, h₇, h₈, h₉, h₁₀⟩ := key hg hgW (hvh _)
  exact ⟨A₁ ∪ A₂, h₁.union h₆ ⟨_, h₄, h₉⟩, union_subset h₂ h₇, disjoint_union_left.mpr ⟨h₃, h₈⟩,
    .inl h₄, closure_mono subset_union_left h₅, closure_mono subset_union_right h₁₀⟩

omit [T2Space S] in
/-- A connected part of the rim with no vertex of `Γ*` has at most one vertex of `Γ` in its closure.
-/
theorem no_two_ends (R : Rim D W) {E : Set Shat} (hE : IsPathConnected E) (hEW : E ⊆ discBd W)
  (hEV : Disjoint E D.rad.G.V) {u v : Shat} (hu : u ∈ closure E) (hv : v ∈ closure E)
    (hne : u ≠ v) (huV : u ∈ D.P.Γ.hatV cap) (hvV : v ∈ D.P.Γ.hatV cap) : False := by
  obtain ⟨x, hx⟩ := hE.nonempty
  obtain ⟨f, hf, hxf⟩ := exists_mem_arcComponent (F := D.rad.G.U \ D.rad.G.V) ⟨R.G_sub
    (hEW hx), disjoint_left.mp hEV hx⟩
  obtain ⟨f', hf', hEf⟩ := exists_arcComp_superset hE (F := D.rad.G.U \ D.rad.G.V)
    (fun y hy ↦ ⟨R.G_sub (hEW hy), disjoint_left.mp hEV hy⟩)
  have hff : f' = f := arcComp_eq_of_mem hf' hf (hEf hx) hxf
  subst hff
  obtain ⟨a, b, hb, ha', hab⟩ := D.rad.isPreRadial.2.2.2.2.1 f' hf
  have h₁ : u ∈ closure f' ∩ D.rad.G.V := ⟨closure_mono hEf hu, D.rad.isPreRadial.2.1 huV⟩
  have h₂ : v ∈ closure f' ∩ D.rad.G.V := ⟨closure_mono hEf hv, D.rad.isPreRadial.2.1 hvV⟩
  rw [hab] at h₁ h₂
  rcases h₁ with rfl | h₁
  · rcases h₂ with rfl | h₂
    · exact hne rfl
    · exact ha'.2 (mem_singleton_iff.mp h₂ ▸ hvV)
  · exact ha'.2 (mem_singleton_iff.mp h₁ ▸ huV)

end TangleDatum.Rim

end GraphMinor.GM19
