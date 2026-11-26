/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ModelPresent

/-!
# Spaces presented by the model word

A Hausdorff space presented by the word of the model `Σ(a, b, c)` is homeomorphic to it
(`model_homeo`). The map from
the discs onto a Hausdorff space identifies its target with a quotient of a compact set, and this
gives continuity
in both directions.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u v

/-- A map out of a compact quotient is continuous when its composition with the quotient map is. -/
theorem continuous_of_compact_quotient {A : Type*} {X : Type u} {Y : Type v} [TopologicalSpace A]
  [T2Space A]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] {D : Set A} (hD : IsCompact D) {f : A → X}
    (hf : ContinuousOn f D) (hs : f '' D = univ) {e : X → Y} (he : ContinuousOn
      (e ∘ f) D) : Continuous e := by
  rw [continuous_iff_isClosed]
  intro C hC
  have h1 : IsCompact (D ∩ (e ∘ f) ⁻¹' C) :=
    hD.of_isClosed_subset (he.preimage_isClosed_of_isClosed hD.isClosed hC) inter_subset_left
  have h2 : e ⁻¹' C = f '' (D ∩ (e ∘ f) ⁻¹' C) := by
    ext x
    constructor
    · intro hx
      have h3 : x ∈ f '' D := hs ▸ mem_univ x
      obtain ⟨a, ha, rfl⟩ := h3
      exact ⟨a, ⟨ha, hx⟩, rfl⟩
    · rintro ⟨a, ⟨-, ha⟩, rfl⟩
      exact ha
  rw [h2]
  exact (h1.image_of_continuousOn (hf.mono inter_subset_left)).isClosed

theorem model_homeo {X : Type u} [TopologicalSpace X] [T2Space X] (a b c : ℕ) {f : ℕ × ℂ → X}
    (hf : Presents (modelW a b (2 * a + b + c)) f) : Nonempty (X ≃ₜ SurfaceModel a b c) := by
  classical
  obtain ⟨Φ, Φ', hΦ⟩ := exists_modelPoly (2 * a + b + c)
  set n := 2 * a + b + c with hn
  have hg := presents_of_isPoly (a := a) (b := b) (Φ' := Φ') hΦ (by omega)
  have hW : {i | modelW a b n i ≠ []}.Finite := by
    refine (finite_le_nat 1).subset fun i hi => modelW_slot hi
  have hD : IsCompact (Dsk (modelW a b n)) := isCompact_Dsk hW
  obtain ⟨hc, hs, hrel⟩ := hf
  obtain ⟨hgc, hgs, hgrel⟩ := hg
  have hbase : ∀ x ∈ Dsk (modelW a b n), Fv n Φ x ∈ modelBase n := fun x hx => Fv_base hΦ.1 hx.2
  have ex1 : ∀ x : X, ∃ y ∈ Dsk (modelW a b n), f y = x := fun x => by
    have h1 : x ∈ f '' Dsk (modelW a b n) := hs ▸ mem_univ x
    exact h1
  have ex2 : ∀ p : modelBase n, ∃ y ∈ Dsk (modelW a b n), Fv n Φ y = p.1 := fun p =>
    Fv_surj (a := a) (b := b) hΦ p.2
  choose s1 hs1 hs1' using ex1
  choose s2 hs2 hs2' using ex2
  have hret : ∀ p : modelBase n, retB n p.1 = p := fun p => Subtype.ext (retB_val p.2)
  have hgs2 : ∀ p : modelBase n, toModel a b n Φ (s2 p) = Quot.mk _ p := fun p => by
    simp only [toModel, hs2', hret]
  let lift : Quot (ModelGlue a b n) → X := Quot.lift (fun p => f (s2 p)) (by
    intro p q hpq
    have h1 : toModel a b n Φ (s2 p) = toModel a b n Φ (s2 q) := by
      rw [hgs2, hgs2]
      exact Quot.sound hpq
    exact (hrel _ (hs2 p) _ (hs2 q)).mpr ((hgrel _ (hs2 p) _ (hs2 q)).mp h1))
  let e : X → Quot (ModelGlue a b n) := fun x => toModel a b n Φ (s1 x)
  have he1 : ∀ y ∈ Dsk (modelW a b n), e (f y) = toModel a b n Φ y := fun y hy =>
    (hgrel _ (hs1 _) _ hy).mpr ((hrel _ (hs1 _) _ hy).mp (hs1' _))
  have hl1 : ∀ y ∈ Dsk (modelW a b n), lift (toModel a b n Φ y) = f y := fun y hy => by
    have h1 : toModel a b n Φ y = Quot.mk _ (retB n (Fv n Φ y)) := rfl
    rw [h1]
    change f (s2 _) = f y
    have h2 : toModel a b n Φ (s2 (retB n (Fv n Φ y))) = toModel a b n Φ y := hgs2 _
    exact (hrel _ (hs2 _) _ hy).mpr ((hgrel _ (hs2 _) _ hy).mp h2)
  have hec : Continuous e := continuous_of_compact_quotient hD hc hs
    (hgc.congr fun y hy => he1 y hy)
  have hrc : ContinuousOn (fun x => retB n (Fv n Φ x)) (Dsk (modelW a b n)) :=
    (continuousOn_retB n).comp (continuousOn_Fv hΦ.1) hbase
  have hrs : (fun x => retB n (Fv n Φ x)) '' Dsk (modelW a b n) = univ :=
    eq_univ_of_forall fun p => ⟨s2 p, hs2 p, by simp only [hs2', hret]⟩
  have hlc : Continuous lift := by
    refine continuous_quot_lift _ ?_
    exact continuous_of_compact_quotient hD hrc hrs (hc.congr fun y hy => by
      exact (hrel _ (hs2 _) _ hy).mpr ((hgrel _ (hs2 _) _ hy).mp (hgs2 _)))
  refine ⟨{ toFun := e, invFun := lift, left_inv := fun x => ?_, right_inv := fun q => ?_,
            continuous_toFun := hec, continuous_invFun := hlc }⟩
  · show lift (e x) = x
    simp only [e]
    rw [hl1 _ (hs1 x), hs1']
  · obtain ⟨p, rfl⟩ := Quot.exists_rep q
    change e (f (s2 p)) = _
    rw [he1 _ (hs2 p), hgs2]

end GraphMinor.Surface
