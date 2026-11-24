/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.JordanPlane
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The Jordan curve theorem in the plane and in the sphere

This file proves `jordan_curve_theorem : JordanCurveStatement`.

The plane case carries `jordan_complex` over the isometry between `ℂ` and `EuclideanPlane`. For the
sphere, we first find a point off the `O`-arc (the sphere is not a circle, `exists_notMem_oArc`).
The sphere is homogeneous (`exists_homeomorph_onePoint`, by a reflection of $\mathbb{R}^3$), so we
may take that point to be the point at infinity of the one-point compactification. Then the arc lies
in the plane, and the sphere components are the bounded component and the unbounded component with
the point at infinity added.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Complex

universe u v

/-- A homeomorphism carries a Jordan split to a Jordan split. -/
theorem IsJordanSplit.image {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {F A B : Set X} (h : IsJordanSplit F A B) (e : X ≃ₜ Y) :
    IsJordanSplit (e '' F) (e '' A) (e '' B) := by
  obtain ⟨hne, hcomp, hA, hB⟩ := h
  refine ⟨fun heq => hne (e.injective.image_injective heq), ?_, ?_, ?_⟩
  · have hset : e '' (univ \ F) = univ \ (e '' F) := by
      rw [image_sdiff e.injective, image_univ, e.surjective.range_eq]
    have hcomps : componentsIn (univ \ (e '' F)) = (fun C => e '' C) '' componentsIn (univ \ F)
      := by
      ext C
      simp only [componentsIn, mem_image, exists_exists_and_eq_and]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [← hset] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨x, hx, by rw [e.image_connectedComponentIn hx, hset]⟩
      · rintro ⟨x, hx, rfl⟩
        refine ⟨e x, hset ▸ mem_image_of_mem _ hx, ?_⟩
        rw [e.image_connectedComponentIn hx, hset]
    rw [hcomps, hcomp, image_pair]
  · rw [← e.image_frontier, hA]
  · rw [← e.image_frontier, hB]

/-- A criterion for a Jordan split: two disjoint open connected sets that fill the complement of
`F`, with closures `A ∪ F` and `B ∪ F`. -/
theorem isJordanSplit_of_parts {X : Type u} [TopologicalSpace X] {F A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hAc : IsPreconnected A) (hBc : IsPreconnected B)
    (hAn : A.Nonempty) (hBn : B.Nonempty) (hdisj : Disjoint A B) (hun : A ∪ B = Fᶜ)
    (hclA : closure A = A ∪ F) (hclB : closure B = B ∪ F) : IsJordanSplit F A B := by
  have hdF : ∀ {C : Set X}, C ⊆ A ∪ B → Disjoint C F := fun hC =>
    Set.disjoint_left.mpr fun x hx hxF => (hun ▸ hC hx) hxF
  refine ⟨fun h => ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hAn
    exact Set.disjoint_left.mp hdisj hx (h ▸ hx)
  · rw [← compl_eq_univ_sdiff]
    exact componentsIn_eq_pair hA hB hAc hBc hAn hBn hdisj hun.symm
  · rw [hA.frontier_eq, hclA,
      union_sdiff_cancel_left (disjoint_iff_inter_eq_empty.mp (hdF subset_union_left)).subset]
  · rw [hB.frontier_eq, hclB,
      union_sdiff_cancel_left (disjoint_iff_inter_eq_empty.mp (hdF subset_union_right)).subset]

/-- The isometry between `ℂ` and the plane. -/
noncomputable def complexPlane : ℂ ≃ₗᵢ[ℝ] EuclideanPlane :=
  Complex.orthonormalBasisOneI.repr

/-- The Jordan curve theorem in the plane. -/
theorem jordan_plane {F : Set EuclideanPlane} (hF : IsOArc F) :
    ∃ A B, IsJordanSplit F A B ∧ Bornology.IsBounded A ∧ ¬ Bornology.IsBounded B := by
  obtain ⟨φ⟩ := hF
  let e : ℂ ≃ₜ EuclideanPlane := complexPlane.toHomeomorph
  obtain ⟨A, B, hsplit, hA, hB⟩ := jordan_complex (φ.trans (e.symm.image F))
  have himg : e '' (e.symm '' F) = F := by
    rw [← image_comp]
    simp
  refine ⟨e '' A, e '' B, himg ▸ hsplit.image e, ?_, ?_⟩
  · exact complexPlane.lipschitzWith.isBounded_image hA
  · intro h
    apply hB
    have := complexPlane.symm.lipschitzWith.isBounded_image h
    have heq : complexPlane.symm '' (e '' B) = B := by
      have hid : (complexPlane.symm ∘ e) = id := funext fun x => complexPlane.symm_apply_apply x
      rw [← image_comp, hid, image_id]
    rwa [heq] at this

/-- The sphere is homogeneous: every point can be moved to the point at infinity, by a reflection of
$\mathbb{R}^3$. -/
theorem exists_homeomorph_onePoint (x : OnePoint EuclideanPlane) :
    ∃ h : OnePoint EuclideanPlane ≃ₜ OnePoint EuclideanPlane, h x = OnePoint.infty := by
  let T := onePointEquivSphereOfFinrankEq (ι := Fin 3) (V := EuclideanPlane) (by simp)
  let v : EuclideanSpace ℝ (Fin 3) := (T x).1
  let w : EuclideanSpace ℝ (Fin 3) := (T OnePoint.infty).1
  have hv : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp (T x).2
  have hw : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp (T OnePoint.infty).2
  let R := Submodule.reflection (ℝ ∙ (v - w))ᗮ
  let r : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    R.toHomeomorph.subtype (fun y => by simp [R])
  refine ⟨T.trans (r.trans T.symm), ?_⟩
  have hr : r (T x) = T OnePoint.infty := by
    apply Subtype.ext
    exact Submodule.reflection_sub (by rw [hv, hw])
  simp [hr]

/-- A continuous real function on the plane is not injective: it takes the same value at two
antipodal points. -/
theorem not_injective_real {f : ℂ → ℝ} (hf : Continuous f) : ¬ Function.Injective f := by
  intro hinj
  let g : ℝ → ℝ := fun t => f (exp (t * I)) - f (-exp (t * I))
  have hg : Continuous g := by fun_prop
  have hanti : g Real.pi = - g 0 := by
    simp only [g]
    simp [exp_pi_mul_I]
  obtain ⟨t, ht⟩ : ∃ t, g t = 0 := by
    have h1 : ∃ a, g a ≤ 0 := by
      rcases le_total (g 0) 0 with h | h
      · exact ⟨0, h⟩
      · exact ⟨Real.pi, by linarith⟩
    have h2 : ∃ b, 0 ≤ g b := by
      rcases le_total (g 0) 0 with h | h
      · exact ⟨Real.pi, by linarith⟩
      · exact ⟨0, h⟩
    exact mem_range_of_exists_le_of_exists_ge hg h1 h2
  have h3 := hinj (sub_eq_zero.mp ht)
  have h4 : exp (t * I) ≠ 0 := exp_ne_zero _
  have h5 : (2 : ℂ) * exp (t * I) = 0 := by linear_combination h3
  simp [h4] at h5

/-- An `O`-arc is not the whole sphere. Otherwise the plane would embed in a circle, and a logarithm
of the embedding would be an injective continuous real function on the plane. -/
theorem exists_notMem_oArc {F : Set (OnePoint EuclideanPlane)} (hF : IsOArc F) : ∃ x, x ∉ F := by
  by_contra hcon
  push Not at hcon
  obtain ⟨φ⟩ := hF
  let j : ℂ → Circle := fun z => φ.symm ⟨((complexPlane z : EuclideanPlane) : OnePoint _), hcon _⟩
  have hj : Continuous j := by
    apply φ.symm.continuous.comp
    apply Continuous.subtype_mk
    exact OnePoint.continuous_coe.comp complexPlane.continuous
  obtain ⟨g, hg, hfg⟩ := hasLogOn_univ_of_ne_zero (f := fun z => ((j z : Circle) : ℂ))
    (by fun_prop) (fun z => Circle.coe_ne_zero _)
  have hgc : Continuous g := continuousOn_univ.mp hg
  refine not_injective_real (f := fun z => (g z).im) (by fun_prop) fun x y hxy => ?_
  have hre : ∀ z, (g z).re = 0 := by
    intro z
    have h1 : ‖((j z : Circle) : ℂ)‖ = 1 := Circle.norm_coe _
    have h2 : ((j z : Circle) : ℂ) = exp (g z) := hfg z (mem_univ _)
    rw [h2, norm_exp] at h1
    simpa using h1
  have hgg : g x = g y := Complex.ext (by rw [hre, hre]) hxy
  have hjj : j x = j y := by
    apply Circle.ext
    have h2 : ((j x : Circle) : ℂ) = exp (g x) := hfg x (mem_univ _)
    have h3 : ((j y : Circle) : ℂ) = exp (g y) := hfg y (mem_univ _)
    rw [h2, h3, hgg]
  have h1 := φ.symm.injective hjj
  have h2 := OnePoint.coe_injective (congr_arg Subtype.val h1)
  exact complexPlane.injective h2

/-- An `O`-arc in the plane gives a Jordan split in the sphere: the point at infinity joins the
unbounded component. -/
theorem jordan_onePoint_of_plane {F : Set EuclideanPlane} (hF : IsOArc F) :
    ∃ A B, IsJordanSplit (((↑) : EuclideanPlane → OnePoint EuclideanPlane) '' F) A B := by
  obtain ⟨A, B, ⟨hne, hcomp, hA, hB⟩, hAb, hBb⟩ := jordan_plane hF
  obtain ⟨φ⟩ := id hF
  have hFc : IsCompact F := by
    have : CompactSpace F := φ.compactSpace
    exact isCompact_iff_compactSpace.mpr this
  have hFcl : IsClosed F := hFc.isClosed
  have hU : IsOpen (univ \ F) := by
    rw [← compl_eq_univ_sdiff]
    exact hFcl.isOpen_compl
  have hmem : A ∈ componentsIn (univ \ F) ∧ B ∈ componentsIn (univ \ F) := by
    rw [hcomp]; simp
  have hparts : ∀ C ∈ componentsIn (univ \ F), IsOpen C ∧ IsPreconnected C ∧ C.Nonempty ∧ Cᶜ ⊇ F
    := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hU.connectedComponentIn, isPreconnected_connectedComponentIn,
      ⟨x, mem_connectedComponentIn hx⟩, fun y hy h => ?_⟩
    exact (connectedComponentIn_subset _ _ h).2 hy
  obtain ⟨hAo, hAp, hAn, hAF⟩ := hparts A hmem.1
  obtain ⟨hBo, hBp, hBn, hBF⟩ := hparts B hmem.2
  have hdisj : Disjoint A B := by
    refine Set.disjoint_left.mpr fun y hyA hyB => hne ?_
    obtain ⟨x, _, rfl⟩ := hmem.1
    obtain ⟨z, _, rfl⟩ := hmem.2
    rw [connectedComponentIn_eq hyA, connectedComponentIn_eq hyB]
  have hcover : ∀ x, x ∉ F → x ∈ A ∨ x ∈ B := by
    intro x hx
    have hx' : x ∈ univ \ F := ⟨mem_univ _, hx⟩
    have h1 : connectedComponentIn (univ \ F) x ∈ ({A, B} : Set (Set EuclideanPlane)) :=
      hcomp ▸ mem_image_of_mem _ hx'
    rcases h1 with h1 | h1
    · exact Or.inl (h1 ▸ mem_connectedComponentIn hx')
    · exact Or.inr (h1 ▸ mem_connectedComponentIn hx')
  have hclA : closure A = A ∪ F := by rw [closure_eq_self_union_frontier, hA]
  have hclB : closure B = B ∪ F := by rw [closure_eq_self_union_frontier, hB]
  have hcompl : (A ∪ F)ᶜ = B := by
    ext x
    constructor
    · intro hx
      have hx1 : x ∉ A := fun h => hx (Or.inl h)
      have hx2 : x ∉ F := fun h => hx (Or.inr h)
      exact (hcover x hx2).resolve_left hx1
    · rintro hx (h | h)
      · exact Set.disjoint_left.mp hdisj h hx
      · exact hBF h hx
  have hAFc : IsCompact (A ∪ F) := Metric.isCompact_of_isClosed_isBounded
    (hclA ▸ isClosed_closure) (hAb.union hFc.isBounded)
  let c : EuclideanPlane → OnePoint EuclideanPlane := (↑)
  have hcc : Continuous c := OnePoint.continuous_coe
  have hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∈ closure (c '' B) := by
    refine mem_closure_iff.mpr fun U hUo hUi => ?_
    obtain ⟨h1, h2⟩ := (OnePoint.isOpen_iff_of_mem hUi).mp hUo
    have : ∃ b ∈ B, b ∉ (c ⁻¹' U)ᶜ := by
      by_contra hcon
      push Not at hcon
      exact hBb (h2.isBounded.subset hcon)
    obtain ⟨b, hb, hbU⟩ := this
    exact ⟨c b, not_not.mp hbU, mem_image_of_mem _ hb⟩
  have hBopen : (c '' B ∪ {OnePoint.infty}) = (c '' (A ∪ F))ᶜ := by
    rw [OnePoint.compl_image_coe, hcompl]
  refine ⟨c '' A, c '' B ∪ {OnePoint.infty}, isJordanSplit_of_parts (OnePoint.isOpen_image_coe.mpr
    hAo)
    ?_ (hAp.image _ hcc.continuousOn) ?_ (hAn.image _) ⟨OnePoint.infty, Or.inr rfl⟩ ?_ ?_ ?_ ?_⟩
  · rw [hBopen]
    exact OnePoint.isOpen_compl_image_coe.mpr ⟨hAFc.isClosed, hAFc⟩
  · refine (hBp.image _ hcc.continuousOn).subset_closure subset_union_left
      (union_subset subset_closure ?_)
    rintro _ rfl
    exact hinf
  · rw [hBopen]
    exact Set.disjoint_left.mpr fun x hx hx' => hx' (image_mono subset_union_left hx)
  · have h1 : Fᶜ = A ∪ B := by
      ext x
      constructor
      · exact hcover x
      · rintro (h | h) hx
        · exact hAF hx h
        · exact hBF hx h
    have h2 : (c '' F)ᶜ = c '' Fᶜ ∪ {OnePoint.infty} := OnePoint.compl_image_coe F
    rw [h2, h1, image_union, union_assoc]
  · refine Subset.antisymm ?_ ?_
    · rw [← image_union]
      exact closure_minimal (image_mono subset_union_left)
        (OnePoint.isClosed_image_coe.mpr ⟨hAFc.isClosed, hAFc⟩)
    · rw [← image_union, ← hclA]
      exact image_closure_subset_closure_image hcc
  · have h1 : Aᶜ = B ∪ F := by
      ext x
      constructor
      · intro hx
        by_cases hxF : x ∈ F
        · exact Or.inr hxF
        · exact Or.inl ((hcover x hxF).resolve_left hx)
      · rintro (h | h) hx
        · exact Set.disjoint_left.mp hdisj hx h
        · exact hAF h hx
    have h2 : c '' B ∪ {OnePoint.infty} ∪ c '' F = (c '' A)ᶜ := by
      have h3 : (c '' A)ᶜ = c '' Aᶜ ∪ {OnePoint.infty} := OnePoint.compl_image_coe A
      rw [h3, h1, image_union, union_right_comm]
    refine Subset.antisymm ?_ ?_
    · refine closure_minimal subset_union_left ?_
      rw [h2]
      exact (OnePoint.isOpen_image_coe.mpr hAo).isClosed_compl
    · refine union_subset subset_closure ?_
      have h4 : c '' F ⊆ closure (c '' B) := by
        refine (image_mono ?_).trans (image_closure_subset_closure_image hcc)
        rw [hclB]
        exact subset_union_right
      exact h4.trans (closure_mono subset_union_left)

/-- The Jordan curve theorem in the sphere. -/
theorem jordan_sphere {S : Type u} [TopologicalSpace S] (hS : IsSphere S) {F : Set S}
    (hF : IsOArc F) : ∃ A B, IsJordanSplit F A B := by
  obtain ⟨e⟩ := hS
  obtain ⟨φ⟩ := id hF
  obtain ⟨x, hx⟩ := exists_notMem_oArc (F := e '' F) ⟨φ.trans (e.image F)⟩
  obtain ⟨h, hh⟩ := exists_homeomorph_onePoint x
  let E : S ≃ₜ OnePoint EuclideanPlane := e.trans h
  let c : EuclideanPlane → OnePoint EuclideanPlane := (↑)
  have hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ E '' F := by
    rintro ⟨y, hy, hyE⟩
    have : e y = x := h.injective (hyE.trans hh.symm)
    exact hx ⟨y, hy, this⟩
  have hrange : E '' F ⊆ range c := by
    intro y hy
    induction y using OnePoint.rec with
    | infty => exact absurd hy hinf
    | coe y => exact ⟨y, rfl⟩
  have himg : c '' (c ⁻¹' (E '' F)) = E '' F := image_preimage_eq_of_subset hrange
  have hG : IsOArc (c ⁻¹' (E '' F)) := by
    have h1 := OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage (c ⁻¹' (E '' F))
    have h2 : (E '' F : Set _) ≃ₜ (c '' (c ⁻¹' (E '' F)) : Set _) := Homeomorph.setCongr himg.symm
    exact ⟨(φ.trans (E.image F)).trans (h2.trans h1.symm)⟩
  obtain ⟨A, B, hsplit⟩ := jordan_onePoint_of_plane hG
  have h3 : E.symm '' (c '' (c ⁻¹' (E '' F))) = F := by
    rw [himg, ← image_comp]
    simp
  exact ⟨_, _, h3 ▸ hsplit.image E.symm⟩

/-- **The Jordan curve theorem**, in the plane and in the sphere. Route: Eilenberg's criterion for
separation by continuous logarithms (`component_eq_of_hasLogOn`) and a Mayer–Vietoris argument
(`not_isPreconnected_compl_union`), see `GraphMinor/Surface/JordanPlane.lean`. -/
theorem jordan_curve_theorem : JordanCurveStatement.{u} :=
  ⟨fun _ hF => jordan_plane hF, fun _ _ hS _ hF => jordan_sphere hS hF⟩

end GraphMinor.Surface
