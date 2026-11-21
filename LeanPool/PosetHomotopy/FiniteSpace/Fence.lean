/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Topology.AlexandrovDiscrete
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Specialization
public import Mathlib.Topology.UnitInterval

/-!
# Homotopies between maps of finite spaces are fences (roadmap 1.1, 1.2)

For Alexandrov-discrete spaces, continuity is monotonicity for the specialization preorder
(`continuous_of_specializes`). Two pointwise comparable maps `f₁ x ⤳ f₂ x` are homotopic
relative to the set where they agree (`homotopicRel_of_specializes`), by the homotopy equal to
`f₁` on `[0, 1) × X` and to `f₂` on `{1} × X`. Conversely, for a finite source and an
Alexandrov-discrete target, the maps along a homotopy form a fence of pointwise comparable maps
(`eqvGen_of_homotopic`): the set of times joined to `0` by a fence is open and closed in the unit
interval. Together they give `homotopic_iff_eqvGen` (J. A. Barmak, *Algebraic Topology of Finite
Topological Spaces and Applications*, Lecture Notes in Math. 2032, Springer, 2011,
Corollary 1.2.6).
-/

@[expose] public section

open Topology unitInterval

namespace LeanPool.PosetHomotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Roadmap 1.1.** A map out of an Alexandrov-discrete space that preserves specialization is
continuous. -/
theorem continuous_of_specializes [AlexandrovDiscrete X] {f : X → Y}
    (hf : ∀ x y, x ⤳ y → f x ⤳ f y) : Continuous f := by
  refine continuous_def.2 fun V hV => isOpen_iff_forall_specializes.2 fun x y hxy hy => ?_
  exact (specializes_iff_forall_open.1 (hf x y hxy)) V hV hy

/-- The homotopy equal to `f₁` before time `1` and to `f₂` at time `1`, for `f₁ x ⤳ f₂ x`. -/
noncomputable def specializesHomotopy (f₁ f₂ : C(X, Y)) (h : ∀ x, f₁ x ⤳ f₂ x) :
    ContinuousMap.HomotopyRel f₁ f₂ {x | f₁ x = f₂ x} where
  toFun p := if (p.1 : ℝ) < 1 then f₁ p.2 else f₂ p.2
  continuous_toFun := by
    refine continuous_def.2 fun V hV => ?_
    have : (fun p : I × X => if (p.1 : ℝ) < 1 then f₁ p.2 else f₂ p.2) ⁻¹' V =
        ({t : I | (t : ℝ) < 1} ×ˢ (f₁ ⁻¹' V)) ∪ (Set.univ ×ˢ (f₂ ⁻¹' V)) := by
      ext ⟨t, x⟩
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_prod, Set.mem_ofPred_eq,
        Set.mem_univ, true_and]
      split_ifs with ht
      · exact ⟨fun hx => Or.inl ⟨ht, hx⟩, fun hx => hx.elim And.right
          fun hx => specializes_iff_forall_open.1 (h x) V hV hx⟩
      · exact ⟨Or.inr, fun hx => hx.elim (fun hx => absurd hx.1 ht) id⟩
    rw [this]
    exact ((isOpen_lt continuous_subtype_val continuous_const).prod
      (hV.preimage f₁.continuous)).union (isOpen_univ.prod (hV.preimage f₂.continuous))
  map_zero_left x := by simp
  map_one_left x := by simp
  prop' t x hx := by
    simp only [ContinuousMap.coe_mk]
    split_ifs
    · rfl
    · exact hx.symm

/-- **Roadmap 1.2.** Two pointwise comparable maps are homotopic relative to the set where they
agree. -/
theorem homotopicRel_of_specializes (f₁ f₂ : C(X, Y)) (h : ∀ x, f₁ x ⤳ f₂ x) :
    f₁.HomotopicRel f₂ {x | f₁ x = f₂ x} :=
  ⟨specializesHomotopy f₁ f₂ h⟩

/-- **Roadmap 1.2.** Comparable maps that agree on `S` are homotopic relative to `S`. -/
theorem homotopicRel_of_specializes_of_eqOn (f₁ f₂ : C(X, Y)) (h : ∀ x, f₁ x ⤳ f₂ x)
    {S : Set X} (hS : Set.EqOn f₁ f₂ S) : f₁.HomotopicRel f₂ S := by
  obtain ⟨F⟩ := homotopicRel_of_specializes f₁ f₂ h
  exact ⟨{ toHomotopy := F.toHomotopy, prop' := fun t x hx => F.prop t x (hS hx) }⟩

/-- **Roadmap 1.2.** Pointwise comparable maps are homotopic. -/
theorem homotopic_of_specializes (f₁ f₂ : C(X, Y)) (h : ∀ x, f₁ x ⤳ f₂ x) :
    f₁.Homotopic f₂ :=
  (homotopicRel_of_specializes f₁ f₂ h).homotopic

/-- Maps joined by a fence of pointwise comparable maps are homotopic. -/
theorem homotopic_of_eqvGen {f g : C(X, Y)}
    (h : Relation.EqvGen (fun f₁ f₂ : C(X, Y) => ∀ x, f₁ x ⤳ f₂ x) f g) : f.Homotopic g := by
  induction h with
  | rel f₁ f₂ h => exact homotopic_of_specializes f₁ f₂ h
  | refl => exact ContinuousMap.Homotopic.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Near every time, the maps of a homotopy with finite source and Alexandrov-discrete target
specialize to the map at that time. -/
theorem eventually_specializes_homotopy [Finite X] [AlexandrovDiscrete Y] {f g : C(X, Y)}
    (F : f.Homotopy g) (t : I) : ∀ᶠ s in 𝓝 t, ∀ x, F (s, x) ⤳ F (t, x) := by
  refine Filter.eventually_all.2 fun x => ?_
  have hU : nhdsKer {F (t, x)} ∈ 𝓝 (F (t, x)) :=
    isOpen_nhdsKer.mem_nhds (subset_nhdsKer (Set.mem_singleton _))
  have hc : Continuous fun s : I => F (s, x) := F.continuous.comp (Continuous.prodMk_left x)
  filter_upwards [hc.continuousAt.preimage_mem_nhds hU] with s hs
  exact specializes_iff_forall_open.2 fun V hV hy =>
    (nhdsKer_subset_iff_isOpen.2 hV).trans' (nhdsKer_mono (Set.singleton_subset_iff.2 hy)) hs

/-- **Roadmap 1.2.** Homotopic maps from a finite space to an Alexandrov-discrete space are
joined by a fence of pointwise comparable maps. -/
theorem eqvGen_of_homotopic [Finite X] [AlexandrovDiscrete Y] {f g : C(X, Y)}
    (h : f.Homotopic g) :
    Relation.EqvGen (fun f₁ f₂ : C(X, Y) => ∀ x, f₁ x ⤳ f₂ x) f g := by
  obtain ⟨F⟩ := h
  set R := Relation.EqvGen (fun f₁ f₂ : C(X, Y) => ∀ x, f₁ x ⤳ f₂ x)
  have hR : Equivalence R := Relation.EqvGen.is_equivalence _
  let S : Set I := {t | R f (F.curry t)}
  have step : ∀ t, ∀ᶠ s in 𝓝 t, R (F.curry s) (F.curry t) := fun t =>
    (eventually_specializes_homotopy F t).mono fun s hs => Relation.EqvGen.rel _ _ hs
  have hS : IsClopen S := by
    refine ⟨isOpen_compl_iff.1 ?_, ?_⟩ <;> refine isOpen_iff_mem_nhds.2 fun t ht => ?_
    · exact (step t).mono fun s hs hs' => ht (hR.trans hs' hs)
    · exact (step t).mono fun s hs => hR.trans ht (hR.symm hs)
  have h0 : (0 : I) ∈ S := by
    change R f (F.curry 0)
    convert hR.refl f using 1
    ext x
    simp
  have h1 := (isClopen_iff.1 hS).resolve_left (Set.nonempty_of_mem h0).ne_empty
  have : (1 : I) ∈ S := h1 ▸ Set.mem_univ _
  change R f (F.curry 1) at this
  convert this using 1
  ext x
  simp

/-- **Roadmap 1.2.** Two maps between finite spaces are homotopic exactly when they are joined by
a fence of maps, consecutive ones pointwise comparable in the specialization order. -/
theorem homotopic_iff_eqvGen [Finite X] [Finite Y] (f g : C(X, Y)) :
    f.Homotopic g ↔ Relation.EqvGen (fun f₁ f₂ : C(X, Y) => ∀ x, f₁ x ⤳ f₂ x) f g :=
  ⟨eqvGen_of_homotopic, homotopic_of_eqvGen⟩

end LeanPool.PosetHomotopy
