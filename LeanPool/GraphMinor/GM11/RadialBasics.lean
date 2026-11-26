/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section6
public import LeanPool.GraphMinor.GM11.Corners
public import LeanPool.GraphMinor.GM11.Section3

/-!
# Tools for radial drawings

Graph Minors XI omits the proof that "every region of $\Gamma'$ includes a unique edge of $\Gamma$",
for a radial
drawing `Γ'` of `Γ` (Section 3, page 75). This file has three general tools for that proof.

* `Drawing.glue`: the union of two drawings that meet only in common vertices, with its edges.
* `isOArc_union`: two lines with the same ends and nothing else in common form an `O`-arc.
* `exists_disc_in_openDisc`: an `O`-arc in an open disc bounds a closed disc in that open disc.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface Metric

universe u

variable {S : Type u} [TopologicalSpace S]

section Glue

variable {A B : Set S} {X Y : Set S}

/-- A connected subset of two closed sets, which misses their intersection, lies in one of them. -/
theorem subset_or_subset_of_closed {C : Set S} (hC : IsPreconnected C) (hX : IsClosed X)
    (hY : IsClosed Y) (hsub : C ⊆ X ∪ Y) (hdis : ∀ x ∈ C, x ∈ X → x ∉ Y) : C ⊆ X ∨ C ⊆ Y := by
  by_contra hno
  push Not at hno
  obtain ⟨hnX, hnY⟩ := hno
  obtain ⟨y, hyC, hyX⟩ := not_subset.mp hnX
  obtain ⟨x, hxC, hxY⟩ := not_subset.mp hnY
  have hxX : x ∈ X := (hsub hxC).resolve_right hxY
  have hyY : y ∈ Y := (hsub hyC).resolve_left hyX
  obtain ⟨z, hzC, hzX, hzY⟩ := isPreconnected_closed_iff.mp hC X Y hX hY hsub ⟨x, hxC, hxX⟩
    ⟨y, hyC, hyY⟩
  exact hdis z hzC hzX hzY

end Glue

/-- The arc-wise connected components of the union of two sets `A`, `B` that lie in closed sets
meeting only outside `A` and `B`. -/
theorem arcComponentsIn_union {U₁ U₂ A B : Set S} (h₁ : IsClosed U₁) (h₂ : IsClosed U₂)
    (hA : A ⊆ U₁) (hB : B ⊆ U₂) (hAB : ∀ x ∈ A ∪ B, x ∈ U₁ → x ∉ U₂) :
    arcComponentsIn (A ∪ B) = arcComponentsIn A ∪ arcComponentsIn B := by
  have hdisj : ∀ x, x ∈ A → x ∈ B → False := fun x h h' =>
    hAB x (Or.inl h) (hA h) (hB h')
  have hsplit : ∀ {C : Set S}, IsPathConnected C → C ⊆ A ∪ B → C ⊆ A ∨ C ⊆ B := by
    intro C hC hsub
    have hc : C ⊆ U₁ ∪ U₂ := hsub.trans (union_subset_union hA hB)
    rcases subset_or_subset_of_closed hC.isConnected.isPreconnected h₁ h₂ hc
      (fun x hx => hAB x (hsub hx)) with h | h
    · refine Or.inl fun x hx => (hsub hx).resolve_right fun hxB => ?_
      exact hAB x (hsub hx) (h hx) (hB hxB)
    · refine Or.inr fun x hx => (hsub hx).resolve_left fun hxA => ?_
      exact hAB x (hsub hx) (hA hxA) (h hx)
  ext C
  constructor
  · rintro ⟨hne, hsub, hp, hmax⟩
    rcases hsplit hp hsub with h | h
    · exact Or.inl ⟨hne, h, hp, fun D hD hpD hCD => hmax D (hD.trans subset_union_left) hpD hCD⟩
    · exact Or.inr ⟨hne, h, hp, fun D hD hpD hCD => hmax D (hD.trans subset_union_right) hpD hCD⟩
  · rintro (⟨hne, hsub, hp, hmax⟩ | ⟨hne, hsub, hp, hmax⟩)
    · refine ⟨hne, hsub.trans subset_union_left, hp, fun D hD hpD hCD => ?_⟩
      obtain ⟨x, hx⟩ := hne
      rcases hsplit hpD hD with h | h
      · exact hmax D h hpD hCD
      · exact (hdisj x (hsub hx) (h (hCD hx))).elim
    · refine ⟨hne, hsub.trans subset_union_right, hp, fun D hD hpD hCD => ?_⟩
      obtain ⟨x, hx⟩ := hne
      rcases hsplit hpD hD with h | h
      · exact (hdisj x (h (hCD hx)) (hsub hx)).elim
      · exact hmax D h hpD hCD

theorem glue_sdiff {Γ₁ Γ₂ : Drawing S} (h : Γ₁.U ∩ Γ₂.U ⊆ Γ₁.V ∩ Γ₂.V) :
    (Γ₁.U ∪ Γ₂.U) \ (Γ₁.V ∪ Γ₂.V) = (Γ₁.U \ Γ₁.V) ∪ (Γ₂.U \ Γ₂.V) := by
  ext x
  constructor
  · rintro ⟨hx | hx, hn⟩
    · exact Or.inl ⟨hx, fun h' => hn (Or.inl h')⟩
    · exact Or.inr ⟨hx, fun h' => hn (Or.inr h')⟩
  · rintro (⟨hx, hn⟩ | ⟨hx, hn⟩)
    · refine ⟨Or.inl hx, ?_⟩
      rintro (h' | h')
      · exact hn h'
      · exact hn (h ⟨hx, Γ₂.V_subset_U h'⟩).1
    · refine ⟨Or.inr hx, ?_⟩
      rintro (h' | h')
      · exact hn (h ⟨Γ₁.V_subset_U h', hx⟩).2
      · exact hn h'

theorem glue_arc {Γ₁ Γ₂ : Drawing S} (h : Γ₁.U ∩ Γ₂.U ⊆ Γ₁.V ∩ Γ₂.V) :
    arcComponentsIn ((Γ₁.U ∪ Γ₂.U) \ (Γ₁.V ∪ Γ₂.V)) =
      arcComponentsIn (Γ₁.U \ Γ₁.V) ∪ arcComponentsIn (Γ₂.U \ Γ₂.V) := by
  rw [glue_sdiff h]
  refine arcComponentsIn_union Γ₁.isClosed_U Γ₂.isClosed_U sdiff_subset sdiff_subset ?_
  rintro x (⟨-, hn⟩ | ⟨-, hn⟩) hx₁ hx₂
  · exact hn (h ⟨hx₁, hx₂⟩).1
  · exact hn (h ⟨hx₁, hx₂⟩).2

/-- The union of two drawings that meet only in common vertices. -/
def _root_.GraphMinor.Surface.Drawing.glue (Γ₁ Γ₂ : Drawing S) (h : Γ₁.U ∩ Γ₂.U ⊆ Γ₁.V ∩ Γ₂.V) :
  Drawing S where
  U := Γ₁.U ∪ Γ₂.U
  V := Γ₁.V ∪ Γ₂.V
  V_subset_U := union_subset_union Γ₁.V_subset_U Γ₂.V_subset_U
  isClosed_U := Γ₁.isClosed_U.union Γ₂.isClosed_U
  finite_V := Γ₁.finite_V.union Γ₂.finite_V
  finite_edges := by
    rw [glue_arc h]
    exact Γ₁.finite_edges.union Γ₂.finite_edges
  edge_cond := by
    intro e he
    rw [glue_arc h] at he
    rcases he with he | he
    · have hcap : closure e ∩ (Γ₁.V ∪ Γ₂.V) = closure e ∩ Γ₁.V := by
        ext x
        constructor
        · rintro ⟨hx, hv | hv⟩
          · exact ⟨hx, hv⟩
          · exact ⟨hx, (h ⟨Γ₁.closure_subset_U he hx, Γ₂.V_subset_U hv⟩).1⟩
        · exact fun hx => ⟨hx.1, Or.inl hx.2⟩
      rw [hcap]
      exact Γ₁.edge_cond e he
    · have hcap : closure e ∩ (Γ₁.V ∪ Γ₂.V) = closure e ∩ Γ₂.V := by
        ext x
        constructor
        · rintro ⟨hx, hv | hv⟩
          · exact ⟨hx, (h ⟨Γ₁.V_subset_U hv, Γ₂.closure_subset_U he hx⟩).2⟩
          · exact ⟨hx, hv⟩
        · exact fun hx => ⟨hx.1, Or.inr hx.2⟩
      rw [hcap]
      exact Γ₂.edge_cond e he

theorem _root_.GraphMinor.Surface.Drawing.glue_E {Γ₁ Γ₂ : Drawing S} (h : Γ₁.U ∩ Γ₂.U ⊆ Γ₁.V ∩
  Γ₂.V) :
    (Γ₁.glue Γ₂ h).E = Γ₁.E ∪ Γ₂.E :=
  glue_arc h

/-- An `O`-arc in an open disc bounds a closed disc in that open disc. -/
theorem exists_disc_in_openDisc [T2Space S] {r J : Set S} (hr : IsOpenDisc r) (hJ : IsOArc J)
    (hsub : J ⊆ r) : ∃ Δ : Set S, Δ ⊆ r ∧ IsClosedDisc Δ ∧ discBd Δ = J := by
  obtain ⟨-, ⟨φ⟩⟩ := hr
  have hJc : IsCompact J := by
    obtain ⟨f⟩ := hJ
    have : J = range fun x : Circle => (f x).1 := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx⟩ := f.surjective ⟨y, hy⟩
        exact ⟨x, by simp [hx]⟩
      · rintro ⟨x, rfl⟩
        exact (f x).2
    rw [this]
    exact isCompact_range (by fun_prop)
  -- The points of the plane that correspond to `J` lie in a smaller closed disc.
  let T : Set r := Subtype.val ⁻¹' J
  have hT : IsCompact T := Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr (by
    rw [Subtype.image_preimage_coe]
    rwa [inter_eq_right.mpr hsub])
  have hT' : IsCompact (φ.symm '' T) := hT.image φ.symm.continuous
  have hbd : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ x ∈ φ.symm '' T, ‖(x : EuclideanPlane)‖ ≤ ρ := by
    by_cases hne : (φ.symm '' T).Nonempty
    · obtain ⟨x₀, hx₀, hmax⟩ := hT'.exists_isMaxOn hne
        (f := fun x : OpenUnitDisc => ‖(x : EuclideanPlane)‖) (by fun_prop)
      have hn : ‖(x₀ : EuclideanPlane)‖ < 1 := by
        have := x₀.2
        simpa [OpenUnitDisc] using this
      refine ⟨(‖(x₀ : EuclideanPlane)‖ + 1) / 2, by positivity, by linarith, fun x hx => ?_⟩
      have := hmax hx
      have this' : ‖(x : EuclideanPlane)‖ ≤ ‖(x₀ : EuclideanPlane)‖ := this
      linarith
    · refine ⟨1 / 2, by norm_num, by norm_num, fun x hx => ?_⟩
      exact absurd ⟨x, hx⟩ hne
  obtain ⟨ρ, h0, h1, hρ⟩ := hbd
  have hin : ∀ x : ClosedUnitDisc, ρ • (x : EuclideanPlane) ∈ OpenUnitDisc := by
    intro x
    have hx : ‖(x : EuclideanPlane)‖ ≤ 1 := by
      have := x.2
      simpa [ClosedUnitDisc] using this
    have : ‖ρ • (x : EuclideanPlane)‖ < 1 := by
      rw [norm_smul, Real.norm_of_nonneg h0.le]
      nlinarith
    simpa [OpenUnitDisc] using this
  let m : ClosedUnitDisc → S := fun x => (φ ⟨ρ • x.1, hin x⟩).1
  have hmc : Continuous m := by
    refine continuous_subtype_val.comp (φ.continuous.comp ?_)
    exact Continuous.subtype_mk (by fun_prop) _
  have hmi : Function.Injective m := by
    intro x y hxy
    have h₁ := φ.injective (Subtype.ext hxy)
    have h₂ : ρ • x.1 = ρ • y.1 := congrArg Subtype.val h₁
    exact Subtype.ext (smul_right_injective _ h0.ne' h₂)
  have : CompactSpace ClosedUnitDisc := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have hemb := hmc.isClosedEmbedding hmi
  have hD : IsClosedDisc (range m) := ⟨hemb.isEmbedding.toHomeomorph⟩
  have hJD : J ⊆ range m := by
    intro y hy
    have hyr := hsub hy
    set z := φ.symm ⟨y, hyr⟩ with hz
    have hzn : ‖(z : EuclideanPlane)‖ ≤ ρ := hρ z ⟨⟨y, hyr⟩, hy, rfl⟩
    have hmem : ρ⁻¹ • (z : EuclideanPlane) ∈ ClosedUnitDisc := by
      have : ‖ρ⁻¹ • (z : EuclideanPlane)‖ ≤ 1 := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg h0.le]
        exact (inv_mul_le_iff₀ h0).mpr (by simpa using hzn)
      simpa [ClosedUnitDisc] using this
    refine ⟨⟨_, hmem⟩, ?_⟩
    have heq : (⟨ρ • (ρ⁻¹ • (z : EuclideanPlane)), hin ⟨_, hmem⟩⟩ : OpenUnitDisc) = z :=
      Subtype.ext (smul_inv_smul₀ h0.ne' _)
    change (φ _).1 = y
    rw [heq, hz, φ.apply_symm_apply]
  obtain ⟨Δ, ⟨hsubΔ, hd, hb, -⟩, -⟩ := disc_oArc (range m) J hD hJD hJ
  refine ⟨Δ, hsubΔ.trans ?_, hd, hb⟩
  rintro _ ⟨x, rfl⟩
  exact (φ _).2

end GraphMinor.GM11
