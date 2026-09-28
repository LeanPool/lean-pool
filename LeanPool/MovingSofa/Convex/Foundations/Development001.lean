/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.Isoperimetric.BrunnMinkowski
public import LeanPool.MovingSofa.Analysis.Foundations.Development002
public import LeanPool.MovingSofa.Classical.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.Analysis.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.BoundedVariation.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.Convex.Foundations.Development001



public import LeanPool.MovingSofa.ForMathlib.MeasureTheory.Foundations.Development001

public import LeanPool.MovingSofa.Geometry.Foundations.Development001


public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Thickening
/-!
# Moving sofa: related mathematical developments

* `Convex.BoundaryVariation`.
* `Convex.BoundaryApproximation`.
* `Convex.Combination`.
* `Convex.AreaSuperlevel`.
* `Convex.CombinationPullback`.
* `Convex.ContactFanArea`.
* `Convex.ExposedFaces`.
* `Convex.Limits`.
* `Convex.SupportEmbedding`.
* `Convex.CombinationProperties`.
* `Convex.EnvelopeFace`.
* `Convex.Space`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Boundary Variation
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private theorem tangent_cone_decomposition (p : Point) (s t : ℝ)
    (h : Real.sin (t - s) ≠ 0) :
    p = (inner ℝ p (normalVector (t : Real.Angle)) / Real.sin (t - s)) •
        tangentVector (s : Real.Angle) +
      (-inner ℝ p (normalVector (s : Real.Angle)) / Real.sin (t - s)) •
        tangentVector (t : Real.Angle) := by
  ext i
  fin_cases i <;>
    simp only [normalVector, tangentVector, frame, PiLp.inner_apply,
      Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Real.Angle.cos_coe,
      Real.Angle.sin_coe, Real.inner_apply] <;>
    norm_num <;> field_simp [h] <;> rw [Real.sin_sub] <;> ring

private theorem exists_nonneg_tangent_coefficients (p q : Point) (s t : ℝ)
    (hst : s < t) (hts : t < s + Real.pi)
    (hs : inner ℝ q (normalVector (s : Real.Angle)) ≤
      inner ℝ p (normalVector (s : Real.Angle)))
    (ht : inner ℝ p (normalVector (t : Real.Angle)) ≤
      inner ℝ q (normalVector (t : Real.Angle))) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
      q - p = α • tangentVector (s : Real.Angle) +
        β • tangentVector (t : Real.Angle) := by
  have hsin : 0 < Real.sin (t - s) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hst) (by linarith)
  refine ⟨inner ℝ (q - p) (normalVector (t : Real.Angle)) / Real.sin (t - s),
    -inner ℝ (q - p) (normalVector (s : Real.Angle)) / Real.sin (t - s),
    ?_, ?_, tangent_cone_decomposition (q - p) s t hsin.ne'⟩
  · apply div_nonneg _ hsin.le
    rw [inner_sub_left]
    exact sub_nonneg.mpr ht
  · apply div_nonneg _ hsin.le
    rw [inner_sub_left]
    linarith

private theorem inner_tangent_normal (r a : ℝ) :
    inner ℝ (tangentVector (r : Real.Angle)) (normalVector (a : Real.Angle)) =
      -Real.sin (r - a) := by
  simp [tangentVector, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
    Real.sin_sub]
  ring

private theorem inner_tangent_tangent (r a : ℝ) :
    inner ℝ (tangentVector (r : Real.Angle)) (tangentVector (a : Real.Angle)) =
      Real.cos (r - a) := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub]
  ring

private theorem tangent_projection_signs {a r : ℝ}
    (hr : r ∈ Set.Icc a (a + Real.pi / 2)) :
    inner ℝ (tangentVector (r : Real.Angle)) (normalVector (a : Real.Angle)) ≤ 0 ∧
    0 ≤ inner ℝ (tangentVector (r : Real.Angle)) (tangentVector (a : Real.Angle)) := by
  rw [inner_tangent_normal, inner_tangent_tangent]
  constructor
  · exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hr.1])
      (by linarith [hr.2, Real.pi_pos]))
  · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hr.1, Real.pi_pos],
      by linarith [hr.2]⟩

private theorem support_selection_projection_order (K : ConvexBody Point)
    {a s t : ℝ} (hs : s ∈ Set.Icc a (a + Real.pi / 2))
    (ht : t ∈ Set.Icc a (a + Real.pi / 2)) (hst : s < t)
    {p q : Point} (hp : p ∈ exposedEdge K (s : Real.Angle))
    (hq : q ∈ exposedEdge K (t : Real.Angle)) :
    inner ℝ q (normalVector (a : Real.Angle)) ≤
        inner ℝ p (normalVector (a : Real.Angle)) ∧
      inner ℝ p (tangentVector (a : Real.Angle)) ≤
        inner ℝ q (tangentVector (a : Real.Angle)) := by
  have hsp := inner_le_supportValue K hq.1 (s : Real.Angle)
  have htp := inner_le_supportValue K hp.1 (t : Real.Angle)
  rw [← hp.2] at hsp
  rw [← hq.2] at htp
  obtain ⟨α, β, hα, hβ, hrepr⟩ := exists_nonneg_tangent_coefficients p q s t hst
    (by linarith [hs.1, ht.2, Real.pi_pos]) hsp htp
  have hsigns := tangent_projection_signs hs
  have hsignt := tangent_projection_signs ht
  constructor
  · have h := congrArg (fun p ↦ inner ℝ p (normalVector (a : Real.Angle))) hrepr
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at h
    linarith [mul_nonpos_of_nonneg_of_nonpos hα hsigns.1,
      mul_nonpos_of_nonneg_of_nonpos hβ hsignt.1]
  · have h := congrArg (fun p ↦ inner ℝ p (tangentVector (a : Real.Angle))) hrepr
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at h
    linarith [mul_nonneg hα hsigns.2, mul_nonneg hβ hsignt.2]

private theorem support_selection_boundedVariationOn_quarter (K : ConvexBody Point)
    (f : ℝ → Point) (a : ℝ)
    (hf : ∀ t ∈ Set.Icc a (a + Real.pi / 2), f t ∈ exposedEdge K (t : Real.Angle)) :
    BoundedVariationOn f (Set.Icc a (a + Real.pi / 2)) := by
  let x : ℝ → ℝ := fun t ↦ -inner ℝ (f t) (normalVector (a : Real.Angle))
  let y : ℝ → ℝ := fun t ↦ inner ℝ (f t) (tangentVector (a : Real.Angle))
  have hx : MonotoneOn x (Set.Icc a (a + Real.pi / 2)) := by
    intro s hs t ht hst
    rcases hst.eq_or_lt with rfl | hst
    · rfl
    · exact neg_le_neg (support_selection_projection_order K hs ht hst (hf s hs) (hf t ht)).1
  have hy : MonotoneOn y (Set.Icc a (a + Real.pi / 2)) := by
    intro s hs t ht hst
    rcases hst.eq_or_lt with rfl | hst
    · rfl
    · exact (support_selection_projection_order K hs ht hst (hf s hs) (hf t ht)).2
  have ha : a ≤ a + Real.pi / 2 := by linarith [Real.pi_pos]
  have hxv : BoundedVariationOn x (Set.Icc a (a + Real.pi / 2)) := by
    simpa only [Set.inter_self] using
      hx.locallyBoundedVariationOn a (a + Real.pi / 2) ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩
  have hyv : BoundedVariationOn y (Set.Icc a (a + Real.pi / 2)) := by
    simpa only [Set.inter_self] using
      hy.locallyBoundedVariationOn a (a + Real.pi / 2) ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩
  let U := ContinuousLinearMap.toSpanSingleton ℝ (-normalVector (a : Real.Angle))
  let V := ContinuousLinearMap.toSpanSingleton ℝ (tangentVector (a : Real.Angle))
  have hsum := (U.lipschitzWith.comp_boundedVariationOn hxv).add
    (V.lipschitzWith.comp_boundedVariationOn hyv)
  have heq : (U ∘ x) + (V ∘ y) = f := by
    funext t
    simpa [U, V, x, y, Function.comp_def] using
      inner_normalVector_smul_add_inner_tangentVector_smul (f t) (a : Real.Angle)
  rwa [heq] at hsum

private theorem boundedVariationOn_Icc_trans {f : ℝ → Point} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hf : BoundedVariationOn f (Set.Icc a b))
    (hg : BoundedVariationOn f (Set.Icc b c)) :
    BoundedVariationOn f (Set.Icc a c) := by
  have h := eVariationOn.Icc_add_Icc f (s := Set.univ) hab hbc (Set.mem_univ b)
  simp only [Set.univ_inter] at h
  change eVariationOn f (Set.Icc a c) ≠ ⊤
  rw [← h]
  exact ENNReal.add_ne_top.mpr ⟨hf, hg⟩

/-- Every selection of points from the exposed edges has bounded variation on bounded intervals. -/
theorem boundedVariationOn_of_mem_exposedEdge (K : ConvexBody Point)
    (f : ℝ → Point) (hf : ∀ t : ℝ, f t ∈ exposedEdge K (t : Real.Angle)) (a b : ℝ) :
    BoundedVariationOn f (Set.Icc a b) := by
  have hN : ∀ n : ℕ, BoundedVariationOn f (Set.Icc a (a + n * (Real.pi / 2))) := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact BoundedVariationOn.of_subsingleton (Set.subsingleton_Icc_of_ge (le_refl a))
    | succ n ih =>
      have hn : a ≤ a + n * (Real.pi / 2) :=
        le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) (by positivity))
      have hn' : a + n * (Real.pi / 2) ≤ a + (n + 1) * (Real.pi / 2) := by
        linarith [Real.pi_pos]
      have hpiece := support_selection_boundedVariationOn_quarter K f
        (a + n * (Real.pi / 2)) (fun t _ ↦ hf t)
      have hstep := boundedVariationOn_Icc_trans hn hn' ih
        (by convert hpiece using 1; congr 1; ring)
      simpa only [Nat.cast_add, Nat.cast_one] using hstep
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / (Real.pi / 2))
  have hb : b ≤ a + n * (Real.pi / 2) := by
    have h := (div_lt_iff₀ (by positivity : 0 < Real.pi / 2)).mp hn
    linarith
  exact (hN n).mono (Set.Icc_subset_Icc_right hb)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Boundary Approximation
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem positiveVertex_boundedVariation (K : ConvexBody Point) (a b : ℝ) (hab : a ≤ b) :
    BoundedVariationOn (fun t : ℝ ↦ (edgeVertices K (t : Real.Angle)).1) (Set.Icc a b) := by
  rcases hab.eq_or_lt with rfl | hab
  · exact BoundedVariationOn.of_subsingleton (Set.subsingleton_Icc_of_ge le_rfl)
  · exact boundedVariationOn_of_mem_exposedEdge K _ (fun t ↦ edgeVertices_fst_mem K _) a b

private theorem exists_facePreserving_polygon (K : ConvexBody Point)
    (F : Finset Real.Angle) {ε : ℝ} (hε : 0 < ε) :
    ∃ (V : Finset Point) (P : ConvexBody Point),
      V.Nonempty ∧
      (P : Set Point) = convexHull ℝ (V : Set Point) ∧
      (P : Set Point) ⊆ (K : Set Point) ∧
      (∀ t ∈ F, exposedEdge P t = exposedEdge K t) ∧
      Metric.hausdorffDist (P : Set Point) (K : Set Point) ≤ ε := by
  obtain ⟨S, hSK, hSfinite, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded K.isCompact.totallyBounded ε hε
  let N : Finset Point := hSfinite.toFinset
  let E : Finset Point :=
    F.image (fun t ↦ (edgeVertices K t).1) ∪
      F.image (fun t ↦ (edgeVertices K t).2)
  let p₀ : Point := Classical.choose K.nonempty
  let V : Finset Point := insert p₀ (N ∪ E)
  have hp₀ : p₀ ∈ K := Classical.choose_spec K.nonempty
  have hVnonempty : V.Nonempty := by
    exact ⟨p₀, Finset.mem_insert_self p₀ _⟩
  have hVsubset : (V : Set Point) ⊆ (K : Set Point) := by
    intro p hp
    simp only [V, E, Finset.mem_coe, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image] at hp
    rcases hp with rfl | hpN | hpE
    · exact hp₀
    · exact hSK (hSfinite.mem_toFinset.mp hpN)
    · rcases hpE with hpE | hpE
      · obtain ⟨t, ht, rfl⟩ := hpE
        exact (edgeVertices_fst_mem K t).1
      · obtain ⟨t, ht, rfl⟩ := hpE
        exact (edgeVertices_snd_mem K t).1
  let P : ConvexBody Point :=
    { carrier := convexHull ℝ (V : Set Point)
      convex' := convex_convexHull ℝ _
      isCompact' := V.finite_toSet.isCompact_convexHull ℝ
      nonempty' := ⟨p₀, subset_convexHull ℝ _ (Finset.mem_coe.mpr
        (Finset.mem_insert_self p₀ _))⟩ }
  have hPcarrier : (P : Set Point) = convexHull ℝ (V : Set Point) := rfl
  have hPK : (P : Set Point) ⊆ (K : Set Point) := by
    change convexHull ℝ (V : Set Point) ⊆ (K : Set Point)
    exact convexHull_min hVsubset K.convex
  have hfaces : ∀ t ∈ F, exposedEdge P t = exposedEdge K t := by
    intro t ht
    have hfstV : (edgeVertices K t).1 ∈ V := by
      simp only [V, E, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      exact Or.inr (Or.inr (Or.inl ⟨t, ht, rfl⟩))
    have hsndV : (edgeVertices K t).2 ∈ V := by
      simp only [V, E, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      exact Or.inr (Or.inr (Or.inr ⟨t, ht, rfl⟩))
    have hfstP : (edgeVertices K t).1 ∈ P := by
      exact subset_convexHull ℝ (V : Set Point) hfstV
    have hsndP : (edgeVertices K t).2 ∈ P := by
      exact subset_convexHull ℝ (V : Set Point) hsndV
    have hsupport : supportValue P t = supportValue K t := by
      apply le_antisymm
      · apply csSup_le (P.nonempty.image _)
        rintro _ ⟨p, hp, rfl⟩
        exact inner_le_supportValue K (hPK hp) t
      · have h := inner_le_supportValue P hfstP t
        rw [(edgeVertices_fst_mem K t).2] at h
        exact h
    ext p
    constructor
    · intro hp
      exact ⟨hPK hp.1, hp.2.trans hsupport⟩
    · intro hp
      have hpseg : p ∈ segment ℝ (edgeVertices K t).2 (edgeVertices K t).1 := by
        rw [← exposedEdge_eq_segment_edgeVertices]
        exact hp
      have hpP : p ∈ P := P.convex.segment_subset hsndP hfstP hpseg
      exact ⟨hpP, hp.2.trans hsupport.symm⟩
  have hdist : Metric.hausdorffDist (P : Set Point) (K : Set Point) ≤ ε := by
    apply Metric.hausdorffDist_le_of_mem_dist hε.le
    · intro p hp
      exact ⟨p, hPK hp, dist_self p ▸ hε.le⟩
    · intro p hp
      have hpcover := hcover hp
      simp only [Set.mem_iUnion, Metric.mem_ball] at hpcover
      obtain ⟨q, hqS, hpq⟩ := hpcover
      have hqN : q ∈ N := hSfinite.mem_toFinset.mpr hqS
      have hqV : q ∈ V := by
        simp only [V, Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inl hqN)
      have hqP : q ∈ P := subset_convexHull ℝ (V : Set Point) hqV
      exact ⟨q, hqP, hpq.le⟩
  exact ⟨V, P, hVnonempty, hPcarrier, hPK, hfaces, hdist⟩

theorem exists_facePreserving_polygonApproximation (K : ConvexBody Point)
    (F : Finset Real.Angle) :
    ∃ (V : ℕ → Finset Point) (P : ℕ → ConvexBody Point),
      (∀ n, (V n).Nonempty ∧
        (P n : Set Point) = convexHull ℝ (V n : Set Point) ∧
        (P n : Set Point) ⊆ (K : Set Point) ∧
        ∀ t ∈ F, exposedEdge (P n) t = exposedEdge K t) ∧
      ∀ n : ℕ, 1 ≤ n → Metric.hausdorffDist (P n : Set Point) (K : Set Point) ≤ 1 / (n : ℝ) := by
  let m : ℕ → ℕ := fun n ↦ max n 1
  let V : ℕ → Finset Point := fun n ↦
    Classical.choose (exists_facePreserving_polygon K F
      (show 0 < 1 / (m n : ℝ) by positivity))
  let P : ℕ → ConvexBody Point := fun n ↦
    Classical.choose (Classical.choose_spec (exists_facePreserving_polygon K F
      (show 0 < 1 / (m n : ℝ) by positivity)))
  have hdata (n : ℕ) := Classical.choose_spec (Classical.choose_spec
    (exists_facePreserving_polygon K F (show 0 < 1 / (m n : ℝ) by positivity)))
  refine ⟨V, P, ?_, ?_⟩
  · intro n
    exact ⟨(hdata n).1, (hdata n).2.1, (hdata n).2.2.1, (hdata n).2.2.2.1⟩
  · intro n hn
    have hmn : m n = n := max_eq_left hn
    simpa only [P, m, hmn] using (hdata n).2.2.2.2

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Combination
-/

@[expose] public section

noncomputable section

open scoped unitInterval

universe u v w

namespace MovingSofa

/-- A barycentric operation has an injective realization as convex combinations in a real space. -/
def IsConvexDomain {α : Type u} (c : I → α → α → α) : Prop :=
  ∃ (V : ModuleCat.{v} ℝ) (e : α → V), Function.Injective e ∧
    Convex ℝ (Set.range e) ∧
    ∀ (t : I) x y, e (c t x y) = (1 - (t : ℝ)) • e x + (t : ℝ) • e y

/-- Preservation of the specified barycentric operations. -/
def IsConvexLinear {α : Type u} {β : Type v}
    (cα : I → α → α → α) (cβ : I → β → β → β) (f : α → β) : Prop :=
  ∀ t x y, f (cα t x y) = cβ t (f x) (f y)

/-- Separate preservation of barycentric combinations in both variables. -/
def IsConvexBilinear {α : Type u} {β : Type v} {γ : Type w}
    (cα : I → α → α → α) (cβ : I → β → β → β) (cγ : I → γ → γ → γ)
    (g : α → β → γ) : Prop :=
  (∀ x, IsConvexLinear cβ cγ (g x)) ∧
    ∀ y, IsConvexLinear cα cγ (fun x ↦ g x y)

/-- The usual barycentric combination of real numbers. -/
def realCombination (t : I) (x y : ℝ) : ℝ := (1 - (t : ℝ)) * x + (t : ℝ) * y

/-- A quadratic functional is the diagonal of a separately convex-linear real map. -/
def IsQuadraticFunctional {α : Type u} (c : I → α → α → α) (f : α → ℝ) : Prop :=
  ∃ g : α → α → ℝ, IsConvexBilinear c c realCombination g ∧ ∀ x, f x = g x x

/-- Concavity or convexity according to the direction of the barycentric inequality. -/
def IsConvexFunctional {α : Type u} (c : I → α → α → α) (f : α → ℝ)
    (concave : Bool) : Prop :=
  ∀ t x y, if concave then realCombination t (f x) (f y) ≤ f (c t x y)
    else f (c t x y) ≤ realCombination t (f x) (f y)

/-- The segment function, extended by zero outside its parameter interval. -/
def segmentFunctional {α : Type u} (c : I → α → α → α) (f : α → ℝ)
    (x y : α) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Icc (0 : ℝ) 1 then f (c ⟨t, ht⟩ x y) else 0

/-- The right derivative along the barycentric segment; used for quadratic functionals. -/
def convexDirectionalDerivative {α : Type u} (c : I → α → α → α)
    (f : α → ℝ) (x y : α) : ℝ :=
  derivWithin (segmentFunctional c f x y) (Set.Icc 0 1) 0

/-- Minkowski interpolation of nonempty compact convex bodies, including both endpoints. -/
def convexBodyCombination (t : I) (K L : ConvexBody Point) : ConvexBody Point :=
  (1 - (t : ℝ)) • K + (t : ℝ) • L

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Area Superlevel
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Pointwise unitInterval

namespace MovingSofa

theorem convexBody_area_superlevel (K L : ConvexBody Point)
    (hK : (11 : ℝ) / 5 ≤ ClassicalResults.area (K : Set Point))
    (hL : (11 : ℝ) / 5 ≤ ClassicalResults.area (L : Set Point)) (t : I) :
    (11 : ℝ) / 5 ≤ ClassicalResults.area (convexBodyCombination t K L : Set Point) := by
  let a : ℝ := 1 - (t : ℝ)
  let b : ℝ := t
  let A : Set Point := a • (K : Set Point)
  let B : Set Point := b • (L : Set Point)
  have ha : 0 ≤ a := by dsimp [a]; exact sub_nonneg.mpr t.2.2
  have hb : 0 ≤ b := t.2.1
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hAcomp : IsCompact A := K.isCompact.smul a
  have hBcomp : IsCompact B := L.isCompact.smul b
  have hABcomp : IsCompact (A + B) := hAcomp.add hBcomp
  have hbm :
      volume A ^ (2 : ℝ)⁻¹ + volume B ^ (2 : ℝ)⁻¹ ≤
        volume (A + B) ^ (2 : ℝ)⁻¹ := by
    convert brunn_minkowski_euclideanSpace (d := 1) (A := A) (B := B)
      (K.nonempty.smul_set (a := a)) hAcomp.measurableSet
      (L.nonempty.smul_set (a := b)) hBcomp.measurableSet hABcomp.measurableSet using 1 <;>
      norm_num
  have hKfin : volume (K : Set Point) ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hLfin : volume (L : Set Point) ≠ ⊤ := L.isCompact.measure_lt_top.ne
  have hABfin : volume (A + B) ≠ ⊤ := hABcomp.measure_lt_top.ne
  have hKvol : ENNReal.ofReal ((11 : ℝ) / 5) ≤ volume (K : Set Point) :=
    (ENNReal.ofReal_le_iff_le_toReal hKfin).2 hK
  have hLvol : ENNReal.ofReal ((11 : ℝ) / 5) ≤ volume (L : Set Point) :=
    (ENNReal.ofReal_le_iff_le_toReal hLfin).2 hL
  have hKroot := ENNReal.monotone_rpow_of_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹) hKvol
  have hLroot := ENNReal.monotone_rpow_of_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹) hLvol
  have hroot :
      ENNReal.ofReal ((11 : ℝ) / 5) ^ (2 : ℝ)⁻¹ ≤
        volume (A + B) ^ (2 : ℝ)⁻¹ := by
    rw [volume_smul_rpow_half (K : Set Point) a ha,
      volume_smul_rpow_half (L : Set Point) b hb] at hbm
    calc
      _ = (ENNReal.ofReal a + ENNReal.ofReal b) *
          ENNReal.ofReal ((11 : ℝ) / 5) ^ (2 : ℝ)⁻¹ := by
        rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal a * volume (K : Set Point) ^ (2 : ℝ)⁻¹ +
          ENNReal.ofReal b * volume (L : Set Point) ^ (2 : ℝ)⁻¹ := by
        rw [add_mul]
        exact add_le_add
          (by simpa [mul_comm] using mul_le_mul_left hKroot (ENNReal.ofReal a))
          (by simpa [mul_comm] using mul_le_mul_left hLroot (ENNReal.ofReal b))
      _ ≤ _ := hbm
  have hvol : ENNReal.ofReal ((11 : ℝ) / 5) ≤ volume (A + B) := by
    calc
      _ = (ENNReal.ofReal ((11 : ℝ) / 5) ^ (2 : ℝ)⁻¹) ^ (2 : ℕ) :=
        (ENNReal.rpow_inv_natCast_pow (by norm_num) _).symm
      _ ≤ (volume (A + B) ^ (2 : ℝ)⁻¹) ^ (2 : ℕ) := pow_le_pow_left' hroot 2
      _ = _ := ENNReal.rpow_inv_natCast_pow (by norm_num) _
  have hcomb : (convexBodyCombination t K L : Set Point) = A + B := by
    rfl
  rw [hcomb]
  exact (ENNReal.ofReal_le_iff_le_toReal hABfin).1 hvol

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Pulling barycentric functionals back along convex-linear maps

A convex-linear map transports one barycentric operation to another, so every notion defined
from that operation pulls back along it: a quadratic functional stays quadratic, and its
directional derivative along a segment is the directional derivative between the images of the
two endpoints. Neither statement needs any topology or differentiability: the two segment
functions are literally equal.
-/

@[expose] public section

noncomputable section

open scoped unitInterval

universe u v

namespace MovingSofa

/-- A quadratic functional pulled back along a convex-linear map is quadratic. -/
theorem IsQuadraticFunctional.comp_isConvexLinear {α : Type u} {β : Type v}
    {cα : I → α → α → α} {cβ : I → β → β → β} {F : α → β}
    (hF : IsConvexLinear cα cβ F) {f : β → ℝ} (hf : IsQuadraticFunctional cβ f) :
    IsQuadraticFunctional cα fun x ↦ f (F x) := by
  obtain ⟨g, hg, hfg⟩ := hf
  refine ⟨fun x y ↦ g (F x) (F y), ⟨fun x s y z ↦ ?_, fun y s x z ↦ ?_⟩, fun x ↦ hfg (F x)⟩
  · change g (F x) (F (cα s y z)) = _
    rw [hF]
    exact hg.1 (F x) s (F y) (F z)
  · change g (F (cα s x z)) (F y) = _
    rw [hF]
    exact hg.2 (F y) s (F x) (F z)

/-- The directional derivative of a functional pulled back along a convex-linear map is the
directional derivative of the functional between the images. -/
theorem convexDirectionalDerivative_comp_isConvexLinear {α : Type u} {β : Type v}
    {cα : I → α → α → α} {cβ : I → β → β → β} {F : α → β}
    (hF : IsConvexLinear cα cβ F) (f : β → ℝ) (x y : α) :
    convexDirectionalDerivative cα (fun z ↦ f (F z)) x y =
      convexDirectionalDerivative cβ f (F x) (F y) := by
  unfold convexDirectionalDerivative
  congr 1
  funext s
  simp only [segmentFunctional]
  split_ifs with hs
  · exact congrArg f (hF _ x y)
  · rfl

/-- A convex or concave functional pulled back along a convex-linear map keeps its direction of
convexity. -/
theorem IsConvexFunctional.comp_isConvexLinear {α : Type u} {β : Type v}
    {cα : I → α → α → α} {cβ : I → β → β → β} {F : α → β}
    (hF : IsConvexLinear cα cβ F) {f : β → ℝ} {concave : Bool}
    (hf : IsConvexFunctional cβ f concave) :
    IsConvexFunctional cα (fun x ↦ f (F x)) concave := by
  intro s x y
  have h := hf s (F x) (F y)
  rw [← hF s x y] at h
  exact h

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Area lower bound from ordered support contacts

A compact convex set `K` of the plane that contains a base point `L = (ℓ, 0)` and lies in the
closed quadrant `{(a, b) | ℓ ≤ a, 0 ≤ b}` has area at least the shoelace expression of any
finite fan `L, P₀, …, P_n` of support contacts taken at strictly increasing normal angles in
`[0, π)`.

Two ordered contacts span a nonnegatively oriented determinant over `L`: expanding the
support inequalities in coordinates turns `sin (β - α) · (P - L) × (Q - L)` into a sum of two
products of nonnegative factors. The fan triangles `convexHull ℝ {L, Pᵢ, Pᵢ₊₁}` therefore lie
in `K` with area one half of their determinant, and two of them can meet only along the line
through `L` and the contact they share, which is planar null. Finite additivity of the volume
off that null set and monotonicity give the bound. Repeated contacts, zero contact vectors and
collinear consecutive rays are allowed: a degenerate triangle simply has vanishing area.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- Two ordered support contacts of a set lying in the closed quadrant above a base point
have nonnegative oriented determinant over that base point. -/
theorem planeCrossProduct_sub_nonneg_of_support {K : Set Point} {L P Q : Point}
    (hL : L ∈ K) (hquadrant : ∀ p ∈ K, L 0 ≤ p 0 ∧ 0 ≤ p 1)
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α < β) (hβ : β < Real.pi)
    (hP : P ∈ K) (hQ : Q ∈ K)
    (hPs : ∀ x ∈ K, inner ℝ x (normalVector (α : Real.Angle)) ≤
      inner ℝ P (normalVector (α : Real.Angle)))
    (hQs : ∀ x ∈ K, inner ℝ x (normalVector (β : Real.Angle)) ≤
      inner ℝ Q (normalVector (β : Real.Angle))) :
    0 ≤ planeCrossProduct (P - L) (Q - L) := by
  have hsβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi (hα.trans_lt hαβ) hβ
  have hsα : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi hα (by linarith)
  have hsδ : 0 < Real.sin β * Real.cos α - Real.cos β * Real.sin α := by
    have h := Real.sin_pos_of_pos_of_lt_pi (x := β - α) (by linarith) (by linarith)
    rwa [Real.sin_sub] at h
  have hz : 0 ≤ (P 0 - Q 0) * Real.cos α + (P 1 - Q 1) * Real.sin α := by
    have h := hPs Q hQ
    rw [inner_normalVector_real, inner_normalVector_real] at h
    linarith
  have hk : 0 ≤ (Q 0 - P 0) * Real.cos β + (Q 1 - P 1) * Real.sin β := by
    have h := hQs P hP
    rw [inner_normalVector_real, inner_normalVector_real] at h
    linarith
  have hB : 0 ≤ (Q 0 - L 0) * Real.cos β + (Q 1 - L 1) * Real.sin β := by
    have h := hQs L hL
    rw [inner_normalVector_real, inner_normalVector_real] at h
    linarith
  have hq0 : 0 ≤ Q 0 - L 0 := sub_nonneg.mpr (hquadrant Q hQ).1
  have hc : 0 ≤ (Q 0 - L 0) * Real.cos α + (Q 1 - L 1) * Real.sin α := by
    have hid : Real.sin β * ((Q 0 - L 0) * Real.cos α + (Q 1 - L 1) * Real.sin α)
        = Real.sin α * ((Q 0 - L 0) * Real.cos β + (Q 1 - L 1) * Real.sin β)
          + (Real.sin β * Real.cos α - Real.cos β * Real.sin α) * (Q 0 - L 0) := by
      ring
    nlinarith [mul_nonneg hsα hB, mul_nonneg hsδ.le hq0]
  have hcross : planeCrossProduct (P - L) (Q - L)
      = (P 0 - L 0) * (Q 1 - L 1) - (P 1 - L 1) * (Q 0 - L 0) := by
    simp [planeCrossProduct]
  have hid2 : (Real.sin β * Real.cos α - Real.cos β * Real.sin α) *
      ((P 0 - L 0) * (Q 1 - L 1) - (P 1 - L 1) * (Q 0 - L 0))
      = ((Q 0 - L 0) * Real.cos α + (Q 1 - L 1) * Real.sin α) *
          ((Q 0 - P 0) * Real.cos β + (Q 1 - P 1) * Real.sin β)
        + ((P 0 - Q 0) * Real.cos α + (P 1 - Q 1) * Real.sin α) *
          ((Q 0 - L 0) * Real.cos β + (Q 1 - L 1) * Real.sin β) := by
    ring
  rw [hcross]
  nlinarith [mul_nonneg hc hk, mul_nonneg hz hB]

theorem supportContact_fan_area (K : Set Point)
    (hcK : IsCompact K) (hvK : Convex ℝ K) (L : Point) (hL : L ∈ K)
    (hLy : L 1 = 0) (hquadrant : ∀ p ∈ K, L 0 ≤ p 0 ∧ 0 ≤ p 1)
    (n : ℕ) (θ : Fin (n + 1) → ℝ)
    (hθ : StrictMono θ) (hθrange : ∀ i, 0 ≤ θ i ∧ θ i < Real.pi)
    (P : Fin (n + 1) → Point) (hP : ∀ i, P i ∈ K)
    (hsupport : ∀ i q, q ∈ K →
      inner ℝ q (normalVector (θ i : Real.Angle)) ≤
        inner ℝ (P i) (normalVector (θ i : Real.Angle))) :
    0 ≤ (1 / 2 : ℝ) * ∑ i : Fin n,
      planeCrossProduct (P i.castSucc - L) (P i.succ - L) ∧
    (1 / 2 : ℝ) * (∑ i : Fin n,
      planeCrossProduct (P i.castSucc - L) (P i.succ - L)) ≤ ClassicalResults.area K := by
  have hquad : ∀ x ∈ K, 0 ≤ (x - L) 0 ∧ 0 ≤ (x - L) 1 := by
    intro x hx
    obtain ⟨h1, h2⟩ := hquadrant x hx
    exact ⟨by simpa using sub_nonneg.mpr h1, by simpa [hLy] using h2⟩
  have hmono : ∀ i j : Fin (n + 1), i ≤ j → 0 ≤ planeCrossProduct (P i - L) (P j - L) := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hlt
    · simp
    · exact planeCrossProduct_sub_nonneg_of_support hL hquadrant (hθrange i).1 (hθ hlt)
        (hθrange j).2 (hP i) (hP j) (fun x hx ↦ hsupport i x hx) (fun x hx ↦ hsupport j x hx)
  have hcnn : ∀ i : Fin n, 0 ≤ planeCrossProduct (P i.castSucc - L) (P i.succ - L) :=
    fun i ↦ hmono _ _ Fin.castSucc_lt_succ.le
  have hsumnn : 0 ≤ ∑ i : Fin n, planeCrossProduct (P i.castSucc - L) (P i.succ - L) :=
    Finset.sum_nonneg fun i _ ↦ hcnn i
  refine ⟨by linarith, ?_⟩
  set T : Fin n → Set Point := fun i ↦ convexHull ℝ {L, P i.castSucc, P i.succ} with hTdef
  have hTsub : ∀ i, T i ⊆ K := by
    intro i
    refine convexHull_min ?_ hvK
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [hL, hP _, hP _]
  have hTvol : ∀ i, volume (T i) = ENNReal.ofReal
      ((1 / 2 : ℝ) * planeCrossProduct (P i.castSucc - L) (P i.succ - L)) := by
    intro i
    have hpos := hcnn i
    simp only [planeCrossProduct] at hpos
    simp only [hTdef, EuclideanSpace.volume_convexHull_triple]
    congr 1
    rw [abs_of_nonneg (by linarith)]
    simp only [planeCrossProduct]
    ring
  have hTmeas : ∀ i, NullMeasurableSet (T i) volume := by
    intro i
    refine (IsCompact.measurableSet ?_).nullMeasurableSet
    exact (((Set.finite_singleton _).insert _).insert _).isCompact_convexHull ℝ
  have hsector : ∀ i : Fin n, T i ⊆ {x : Point |
      0 ≤ planeCrossProduct (P i.castSucc - L) (x - L) ∧
      0 ≤ planeCrossProduct (x - L) (P i.succ - L)} := by
    intro i
    refine convexHull_min ?_ (convex_setOf_planeCrossProduct_fan _ _ _)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, hcnn i⟩
    · exact ⟨hcnn i, by simp⟩
  have hdisj : Pairwise (Function.onFun (AEDisjoint volume) T) := by
    have hkey : ∀ i j : Fin n, i < j → volume (T i ∩ T j) = 0 := by
      intro i j hij
      rcases eq_or_lt_of_le (hcnn i) with h0 | h0
      · exact measure_mono_null Set.inter_subset_left (by rw [hTvol i, ← h0]; simp)
      rcases eq_or_lt_of_le (hcnn j) with h1 | h1
      · exact measure_mono_null Set.inter_subset_right (by rw [hTvol j, ← h1]; simp)
      have hne2 : P j.castSucc - L ≠ 0 := by
        intro h
        rw [h] at h1
        simp [planeCrossProduct] at h1
      have hne1 : P i.succ - L ≠ 0 := by
        intro h
        rw [h] at h0
        simp [planeCrossProduct] at h0
      refine measure_mono_null ?_ (volume_setOf_planeCrossProduct_sub_eq_zero hne1 L)
      rintro x ⟨hxi, hxj⟩
      have hxK : x ∈ K := hTsub i hxi
      have h2 := (hsector i hxi).2
      have h3 := (hsector j hxj).1
      have hle : i.succ ≤ j.castSucc := by
        have hij' : (i : ℕ) < (j : ℕ) := hij
        rw [Fin.le_def]
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      have h5 : 0 ≤ planeCrossProduct (P i.succ - L) (x - L) :=
        planeCrossProduct_nonneg_trans hne2
          (hquad _ (hP _)).1 (hquad _ (hP _)).2 (hquad _ (hP _)).1 (hquad _ (hP _)).2
          (hquad x hxK).1 (hquad x hxK).2 (hmono _ _ hle) h3
      change planeCrossProduct (P i.succ - L) (x - L) = 0
      rw [planeCrossProduct_swap (x - L)] at h2
      linarith
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hkey i j h
    · change volume (T i ∩ T j) = 0
      rw [Set.inter_comm]
      exact hkey j i h
  have hunion : ∑ i : Fin n, volume (T i) ≤ volume K := by
    have h := measure_iUnion₀ (μ := volume) hdisj hTmeas
    rw [tsum_fintype] at h
    rw [← h]
    exact measure_mono (Set.iUnion_subset hTsub)
  have hgoal : ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i : Fin n,
      planeCrossProduct (P i.castSucc - L) (P i.succ - L)) ≤ volume K := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by linarith [hcnn i])]
    simpa only [hTvol] using hunion
  exact (ENNReal.ofReal_le_iff_le_toReal hcK.measure_lt_top.ne).mp hgoal

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Exposed Faces
-/

@[expose] public section

noncomputable section

open scoped Pointwise unitInterval

namespace MovingSofa

private theorem support_bound (K : ConvexBody Point) (a : Real.Angle)
    {x : Point} (hx : x ∈ K) : inner ℝ x (normalVector a) ≤ supportValue K a := by
  apply le_csSup
  · exact (K.isCompact.image (continuous_id.inner continuous_const)).bddAbove
  · exact ⟨x, hx, rfl⟩

private theorem edge_nonempty (K : ConvexBody Point) (a : Real.Angle) :
    (exposedEdge K a).Nonempty := by
  obtain ⟨x, hx, he⟩ := (K.isCompact.image (continuous_id.inner continuous_const)).sSup_mem
    (K.nonempty.image (fun x ↦ inner ℝ x (normalVector a)))
  exact ⟨x, hx, he⟩

private theorem mem_edge_iff (K : ConvexBody Point) (a : Real.Angle) (x : Point) :
    x ∈ exposedEdge K a ↔ x ∈ K ∧ ∀ y ∈ K,
      inner ℝ y (normalVector a) ≤ inner ℝ x (normalVector a) := by
  change (x ∈ K ∧ inner ℝ x (normalVector a) = supportValue K a) ↔ _
  constructor
  · rintro ⟨hx, he⟩
    exact ⟨hx, fun y hy ↦ he ▸ support_bound K a hy⟩
  · rintro ⟨hx, hm⟩
    refine ⟨hx, le_antisymm (support_bound K a hx) ?_⟩
    exact csSup_le (K.nonempty.image _) (by rintro _ ⟨y, hy, rfl⟩; exact hm y hy)

private theorem combination_zero (K L : ConvexBody Point) :
    convexBodyCombination 0 K L = K := by
  apply SetLike.coe_injective
  simp [convexBodyCombination, Set.zero_smul_set L.nonempty]

private theorem combination_one (K L : ConvexBody Point) :
    convexBodyCombination 1 K L = L := by
  apply SetLike.coe_injective
  simp [convexBodyCombination, Set.zero_smul_set K.nonempty]

/-- Exposed faces commute with convex interpolation, including zero and unit weights. -/
theorem exposedEdge_convexBodyCombination (K L : ConvexBody Point) (a : Real.Angle)
    (t : unitInterval) :
    exposedEdge (convexBodyCombination t K L) a =
      (1 - (t : ℝ)) • exposedEdge K a + (t : ℝ) • exposedEdge L a := by
  by_cases h0 : t = 0
  · subst t
    simp [combination_zero, Set.zero_smul_set (edge_nonempty L a)]
  by_cases h1 : t = 1
  · subst t
    simp [combination_one, Set.zero_smul_set (edge_nonempty K a)]
  have ht : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (by
    intro h; exact h0 (Subtype.ext h.symm))
  have hu : 0 < 1 - (t : ℝ) := sub_pos.mpr (lt_of_le_of_ne t.property.2 (by
    intro h; exact h1 (Subtype.ext h)))
  have mem_combo (x y : Point) (hx : x ∈ K) (hy : y ∈ L) :
      (1 - (t : ℝ)) • x + (t : ℝ) • y ∈ convexBodyCombination t K L := by
    exact Set.add_mem_add (Set.smul_mem_smul_set hx) (Set.smul_mem_smul_set hy)
  ext p
  constructor
  · intro hp
    obtain ⟨hp, hm⟩ := (mem_edge_iff _ a p).mp hp
    obtain ⟨u, huK, v, hvL, rfl⟩ := hp
    obtain ⟨x, hx, rfl⟩ := huK
    obtain ⟨y, hy, rfl⟩ := hvL
    have hxedge : x ∈ exposedEdge K a := (mem_edge_iff K a x).mpr ⟨hx, by
      intro z hz
      have h := hm _ (mem_combo z y hz hy)
      simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real] at h
      nlinarith⟩
    have hyedge : y ∈ exposedEdge L a := (mem_edge_iff L a y).mpr ⟨hy, by
      intro z hz
      have h := hm _ (mem_combo x z hx hz)
      simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real] at h
      nlinarith⟩
    exact Set.add_mem_add (Set.smul_mem_smul_set hxedge) (Set.smul_mem_smul_set hyedge)
  · rintro ⟨u, huK, v, hvL, rfl⟩
    obtain ⟨x, hx, rfl⟩ := huK
    obtain ⟨y, hy, rfl⟩ := hvL
    obtain ⟨hx, hmx⟩ := (mem_edge_iff K a x).mp hx
    obtain ⟨hy, hmy⟩ := (mem_edge_iff L a y).mp hy
    apply (mem_edge_iff _ a _).mpr
    refine ⟨mem_combo x y hx hy, ?_⟩
    rintro p ⟨u, huK, v, hvL, rfl⟩
    obtain ⟨z, hz, rfl⟩ := huK
    obtain ⟨w, hw, rfl⟩ := hvL
    have hxz := hmx z hz
    have hyw := hmy w hw
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
    nlinarith

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Limits
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

/-- The supremum of scalar products with a specified direction vector. -/
def vectorSupport (S : Set Point) (u : Point) : ℝ := sSup ((fun x ↦ inner ℝ x u) '' S)

/-- Support values in a unit direction vary by at most the Hausdorff distance. -/
theorem abs_vectorSupport_sub_le_hausdorffDist {S T : Set Point}
    (hS : S.Nonempty) (hcS : IsCompact S) (hT : T.Nonempty) (hcT : IsCompact T)
    {u : Point} (hu : ‖u‖ = 1) :
    |vectorSupport S u - vectorSupport T u| ≤ Metric.hausdorffDist S T := by
  simpa only [vectorSupport, hu, mul_one] using
    hcS.abs_csSup_inner_sub_le_hausdorffDist hS hcT hT u

theorem convexBody_selection (A : Set Point) (hA : IsCompact A)
    (K : ℕ → ConvexBody Point) (hK : ∀ n, (K n : Set Point) ⊆ A) :
    ∃ (φ : ℕ → ℕ) (L : ConvexBody Point), StrictMono φ ∧
      Tendsto (fun n ↦ Metric.hausdorffDist (K (φ n) : Set Point) (L : Set Point))
        atTop (𝓝 0) := by
  let C : ℕ → TopologicalSpace.NonemptyCompacts Point := fun n ↦
    ⟨⟨(K n : Set Point), (K n).isCompact⟩, (K n).nonempty⟩
  obtain ⟨L, hLA, φ, hφ, hlim⟩ :=
    (TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact hA).tendsto_subseq
      (show ∀ n, C n ∈ {L : TopologicalSpace.NonemptyCompacts Point | (L : Set Point) ⊆ A}
        from hK)
  have hconv : Convex ℝ (L : Set Point) :=
    TopologicalSpace.NonemptyCompacts.convex_of_tendsto (fun n ↦ (K (φ n)).convex) hlim
  refine ⟨φ, ⟨(L : Set Point), hconv, L.isCompact, L.nonempty⟩, hφ, ?_⟩
  simpa only [C, Function.comp_apply, TopologicalSpace.NonemptyCompacts.dist_eq,
    TopologicalSpace.NonemptyCompacts.coe_mk, TopologicalSpace.Compacts.coe_mk, ConvexBody.coe_mk]
      using
    (tendsto_iff_dist_tendsto_zero.mp hlim)

theorem compactSet_support_continuity (S T : Set Point)
    (hS : S.Nonempty) (hcS : IsCompact S) (hT : T.Nonempty) (hcT : IsCompact T) :
    (∀ u v : Point, ‖u‖ = 1 → ‖v‖ = 1 →
      |vectorSupport S u - vectorSupport S v| ≤ sSup (norm '' S) * ‖u - v‖) ∧
    (∀ u : Point, ‖u‖ = 1 →
      |vectorSupport S u - vectorSupport T u| ≤ Metric.hausdorffDist S T) ∧
    Continuous (fun t : Real.Angle ↦ supportValue S t) ∧
    (∀ (K : ℕ → Set Point), (∀ n, (K n).Nonempty ∧ IsCompact (K n)) →
      Tendsto (fun n ↦ Metric.hausdorffDist (K n) S) atTop (𝓝 0) →
      TendstoUniformlyOn (fun n u ↦ vectorSupport (K n) u) (vectorSupport S)
        atTop {u | ‖u‖ = 1}) := by
  constructor
  · intro u v _ _
    exact hcS.abs_csSup_inner_sub_le hS u v
  constructor
  · intro u hu
    exact abs_vectorSupport_sub_le_hausdorffDist hS hcS hT hcT hu
  constructor
  · unfold supportValue
    apply hcS.continuous_sSup
    change Continuous (fun q : Real.Angle × Point ↦ inner ℝ q.2 (normalVector q.1))
    have hn : Continuous (fun q : Real.Angle × Point ↦ normalVector q.1) := by
      let c : Real.Angle × Point → (i : Fin 2) → ℝ :=
        fun q i ↦ Fin.cases q.1.cos (fun _ ↦ q.1.sin) i
      have hc : Continuous c := by
        apply continuous_pi
        intro i
        fin_cases i
        · exact Real.Angle.continuous_cos.comp continuous_fst
        · exact Real.Angle.continuous_sin.comp continuous_fst
      have heq : (fun q : Real.Angle × Point ↦ normalVector q.1) =
          (fun q ↦ WithLp.toLp 2 (c q)) := by
        funext q
        ext i
        fin_cases i <;> rfl
      rw [heq]
      exact (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ)).comp hc
    simpa [Function.comp_def] using
      (continuous_inner (𝕜 := ℝ) (E := Point)).comp (continuous_snd.prodMk hn)
  · intro K hK hlim
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
    intro u hu
    rw [Real.dist_eq]
    exact (abs_vectorSupport_sub_le_hausdorffDist hS hcS
      (hK n).1 (hK n).2 hu).trans_lt (by simpa [Metric.hausdorffDist_comm] using hn)

private theorem exists_inner_pos_of_eq_iInter
    (U : Set Point) (K : Set Point) (hne : K.Nonempty) (hbounded : Bornology.IsBounded K)
    (hK : K = ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport K u}) :
    ∀ d : Point, d ≠ 0 → ∃ u ∈ U, 0 < inner ℝ d u := by
  intro d hd
  by_contra hno
  push Not at hno
  obtain ⟨z, hz⟩ := hne
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall (0 : Point) |>.1 hbounded
  have hzI : z ∈ ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport K u} := by
    rw [← hK]
    exact hz
  have hmem : ∀ t : ℝ, 0 ≤ t → z + t • d ∈ K := by
    intro t ht
    rw [hK]
    simp only [Set.mem_iInter]
    intro u hu
    have hz' := (Set.mem_iInter.mp (Set.mem_iInter.mp hzI u) hu)
    dsimp at hz' ⊢
    rw [inner_add_left, inner_smul_left]
    change inner ℝ z u + t * inner ℝ d u ≤ vectorSupport K u
    have hdu : inner ℝ d u ≤ 0 := hno u hu
    have htd : t * inner ℝ d u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hdu
    nlinarith [hz', htd]
  have hnorm : ∀ t : ℝ, 0 ≤ t → ‖z + t • d‖ ≤ R := by
    intro t ht
    simpa [dist_eq_norm] using (Metric.mem_closedBall.mp (hR (hmem t ht)))
  have hd' : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hR0 : 0 ≤ R := dist_nonneg.trans (Metric.mem_closedBall.mp (hR hz))
  let t : ℝ := (R + ‖z‖ + 1) / ‖d‖
  have ht : 0 ≤ t := by dsimp [t]; exact div_nonneg (by positivity) (le_of_lt hd')
  have hn := hnorm t ht
  have hts : ‖t • d‖ = R + ‖z‖ + 1 := by
    dsimp [t]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    exact div_mul_cancel₀ _ (ne_of_gt hd')
  have htriangle' : ‖t • d‖ ≤ ‖z + t • d‖ + ‖z‖ := by
    have h := norm_sub_le (z + t • d) z
    simpa [sub_eq_add_neg, add_assoc] using h
  rw [hts] at htriangle'
  nlinarith

private theorem ball_support_margin
    (U : Set Point) (L : Set Point) (q u : Point) (r : ℝ) (hr : 0 ≤ r)
    (hu : u ∈ U) (hunit : ‖u‖ = 1)
    (hball : Metric.closedBall q r ⊆ ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport L u}) :
    inner ℝ q u + r ≤ vectorSupport L u := by
  have hp : q + r • u ∈ Metric.closedBall q r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [add_sub_cancel_left]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hunit]
    simp
  have hp' := hball hp
  have hpu := (Set.mem_iInter.mp (Set.mem_iInter.mp hp' u) hu)
  dsimp at hpu
  rw [inner_add_left, inner_smul_left] at hpu
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hunit]
    norm_num
  simp only [huu] at hpu
  simpa using hpu

private theorem eventually_ball_center_mem
    (U : Set Point) (q : Point) (r : ℝ) (hr : 0 < r)
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hK : ∀ n, (K n : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport (K n) u})
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0))
    (hq : ∀ u ∈ U, inner ℝ q u + r ≤ vectorSupport (L : Set Point) u)
    (hU : ∀ u ∈ U, ‖u‖ = 1) :
    ∀ᶠ n in atTop, q ∈ (K n : Set Point) := by
  filter_upwards [hlim.eventually (gt_mem_nhds hr)] with n hn
  rw [hK n]
  simp only [Set.mem_iInter]
  intro u hu
  have habs := (compactSet_support_continuity (K n : Set Point) (L : Set Point)
    (K n).nonempty (K n).isCompact L.nonempty L.isCompact).2.1 u (hU u hu)
  have hlower : vectorSupport (L : Set Point) u -
      Metric.hausdorffDist (K n : Set Point) (L : Set Point) ≤
      vectorSupport (K n : Set Point) u := by
    linarith [neg_le_of_abs_le habs]
  have hqr := hq u hu
  change inner ℝ q u ≤ vectorSupport (K n : Set Point) u
  calc
    inner ℝ q u ≤ vectorSupport (L : Set Point) u - r := by linarith
    _ ≤ vectorSupport (L : Set Point) u - Metric.hausdorffDist (K n : Set Point) L := by
      exact le_of_lt (by linarith)
    _ ≤ vectorSupport (K n : Set Point) u := hlower

private theorem ball_center_mem_limit
    (U : Set Point) (hU : ∀ u ∈ U, ‖u‖ = 1) (q : Point) (r : ℝ) (hr : 0 < r)
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hK : ∀ n, (K n : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport (K n) u})
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0))
    (hball : Metric.closedBall q r ⊆ ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport L u}) :
    q ∈ (L : Set Point) := by
  exact ConvexBody.mem_of_tendsto_hausdorffDist q K L
    (eventually_ball_center_mem U q r hr K L hK hlim
      (fun u hu ↦ ball_support_margin U L q u r hr.le hu (hU u hu) hball) hU) hlim

theorem fixedNormalBody_closed (U : Set Point) (hU : ∀ u ∈ U, ‖u‖ = 1)
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hK : ∀ n, (K n : Set Point) = ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport (K n) u})
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) :
    (L : Set Point) = ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport L u} := by
  let H : Set Point := ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport L u}
  have hLH : (L : Set Point) ⊆ H := by
    intro x hx
    simp only [H, Set.mem_iInter, Set.mem_ofPred_eq]
    intro u hu
    exact le_csSup (L.isCompact.bddAbove_image
      (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn)
      ⟨x, hx, rfl⟩
  have hH : Convex ℝ H := by
    intro x hx y hy a b ha hb hab
    simp only [H, Set.mem_iInter, Set.mem_ofPred_eq] at hx hy ⊢
    intro u hu
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    calc
      a * inner ℝ x u + b * inner ℝ y u ≤
          a * vectorSupport L u + b * vectorSupport L u :=
        add_le_add (mul_le_mul_of_nonneg_left (hx u hu) ha)
          (mul_le_mul_of_nonneg_left (hy u hu) hb)
      _ = vectorSupport L u := by rw [← add_mul, hab, one_mul]
  have hint : interior H ⊆ (L : Set Point) := by
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (mem_interior_iff_mem_nhds.mp hx)
    exact ball_center_mem_limit U hU x r hr K L hK hlim hball
  apply Set.Subset.antisymm hLH
  rcases (interior H).eq_empty_or_nonempty with hempty | hnonempty
  · have hcol : Collinear ℝ H := hH.collinear_of_interior_eq_empty (by
      simp [Point, finrank_euclideanSpace]) hempty
    intro p hp
    obtain ⟨a, ha⟩ := L.nonempty
    by_cases hpa : p = a
    · simpa only [hpa] using ha
    obtain ⟨u, hu, hpos⟩ := exists_inner_pos_of_eq_iInter U (K 0) (K 0).nonempty
      (K 0).isCompact.isBounded (hK 0)
      (p - a) (sub_ne_zero.mpr hpa)
    have hmax : ∃ x ∈ (L : Set Point), vectorSupport L u = inner ℝ x u ∧
        ∀ y ∈ (L : Set Point), inner ℝ y u ≤ inner ℝ x u := by
      simpa only [vectorSupport, Function.comp_apply, id_eq] using
        L.isCompact.exists_sSup_image_eq_and_ge (α := ℝ) (β := Point)
          (f := fun x : Point ↦ inner ℝ x u) L.nonempty
          (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
    obtain ⟨x, hx, hxu, _⟩ := hmax
    have hle : inner ℝ p u ≤ inner ℝ x u := by
      rw [← hxu]
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hp u) hu
    have hsegment := hcol.mem_segment_of_apply_le (hLH ha) hp (hLH hx)
      (innerSL ℝ u).toLinearMap (by change 0 < inner ℝ u (p - a); rwa [real_inner_comm])
      (by change inner ℝ u p ≤ inner ℝ u x; simpa only [real_inner_comm u] using hle)
    exact L.convex.segment_subset ha hx hsegment
  · have hclosure : closure (interior H) = closure H :=
      hH.closure_interior_eq_closure_of_nonempty_interior hnonempty
    exact subset_closure.trans (hclosure ▸ L.isClosed.closure_subset_iff.mpr hint)

theorem convexArea_hausdorff_continuity (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ ClassicalResults.area (K n)) atTop (𝓝 (ClassicalResults.area L)) := by
  let U : Set Point := {u | ‖u‖ = 1}
  have hrepK : ∀ n, (K n : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport (K n) u} := by
    intro n
    simpa only [U, vectorSupport] using ConvexBody.eq_iInter_halfSpaces (K n)
  have hrepL : (L : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport L u} := by
    simpa only [U, vectorSupport] using ConvexBody.eq_iInter_halfSpaces L
  obtain ⟨R, hR, hcompact⟩ := L.isCompact.exists_isCompact_cthickening
  let C : Set Point := Metric.cthickening R (L : Set Point)
  have hsubset : ∀ᶠ n in atTop, (K n : Set Point) ⊆ C := by
    filter_upwards [hlim.eventually (gt_mem_nhds hR)] with n hn p hp
    obtain ⟨q, hq, hpq⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hp hn
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
    exact Metric.mem_cthickening_of_dist_le p q R L hq hpq.le
  have hpointwise : ∀ p ∉ frontier (L : Set Point),
      Tendsto (fun n ↦ (K n : Set Point).indicator (fun _ ↦ (1 : ℝ)) p) atTop
        (𝓝 ((L : Set Point).indicator (fun _ ↦ (1 : ℝ)) p)) := by
    intro p hpfrontier
    by_cases hpL : p ∈ (L : Set Point)
    · have hpint : p ∈ interior (L : Set Point) := by
        by_contra hp
        exact hpfrontier ((mem_frontier_iff_notMem_interior hpL).mpr hp)
      obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
        (mem_interior_iff_mem_nhds.mp hpint)
      have hmargin : ∀ u ∈ U, inner ℝ p u + r ≤ vectorSupport L u := by
        intro u hu
        rw [hrepL] at hball
        exact ball_support_margin U L p u r hr.le hu hu hball
      have hev := eventually_ball_center_mem U p r hr K L hrepK hlim hmargin
        (fun _ hu ↦ hu)
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [hev] with n hn
      simp [hn, hpL]
    · have hdist : 0 < Metric.infDist p (L : Set Point) := by
        exact (Metric.infDist_pos_iff_notMem_closure L.nonempty).mp (by
          rwa [L.isClosed.closure_eq])
      have hev : ∀ᶠ n in atTop, p ∉ (K n : Set Point) := by
        filter_upwards [hlim.eventually (gt_mem_nhds hdist)] with n hn hpn
        have hle := Metric.infDist_le_hausdorffDist_of_mem hpn
          (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
            (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
        linarith
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [hev] with n hn
      simp [hn, hpL]
  have hfrontier : MeasureTheory.volume (frontier (L : Set Point)) = 0 :=
    L.convex.addHaar_frontier MeasureTheory.volume
  have hmeas : ∀ n, MeasurableSet (K n : Set Point) := fun n ↦ (K n).isCompact.measurableSet
  have hCmeas : MeasurableSet C := hcompact.measurableSet
  have hCint : MeasureTheory.Integrable (C.indicator fun _ ↦ (1 : ℝ)) := by
    exact (MeasureTheory.integrableOn_const hcompact.measure_lt_top.ne).integrable_indicator hCmeas
  have htendsto := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume)
    (F := fun n ↦ (K n : Set Point).indicator fun _ ↦ (1 : ℝ))
    (f := (L : Set Point).indicator fun _ ↦ (1 : ℝ))
    (C.indicator fun _ ↦ (1 : ℝ))
    (Filter.Eventually.of_forall fun n ↦
      (measurable_const.indicator (hmeas n)).aestronglyMeasurable)
    (by
      filter_upwards [hsubset] with n hn
      filter_upwards [] with p
      by_cases hp : p ∈ (K n : Set Point)
      · have hpC := hn hp
        simp [hp, hpC]
      · by_cases hpC : p ∈ C <;> simp [hp, hpC])
    hCint
    (by
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hfrontier] with p hp
      exact hpointwise p hp)
  have heqK : ∀ n, (∫ p, (K n : Set Point).indicator (fun _ ↦ (1 : ℝ)) p) =
      MeasureTheory.volume.real (K n : Set Point) := by
    intro n
    change (∫ p, (K n : Set Point).indicator 1 p) = _
    exact MeasureTheory.integral_indicator_one (μ := MeasureTheory.volume) (hmeas n)
  have heqL : (∫ p, (L : Set Point).indicator (fun _ ↦ (1 : ℝ)) p) =
      MeasureTheory.volume.real (L : Set Point) := by
    change (∫ p, (L : Set Point).indicator 1 p) = _
    exact MeasureTheory.integral_indicator_one (μ := MeasureTheory.volume)
      L.isCompact.measurableSet
  simp_rw [heqK] at htendsto
  rw [heqL] at htendsto
  simpa [ClassicalResults.area, MeasureTheory.Measure.real] using htendsto

/-- The support function of a convex body is continuous in the normal direction. -/
theorem continuous_supportValue (K : ConvexBody Point) :
    Continuous fun t : Real.Angle ↦ supportValue (K : Set Point) t :=
  (compactSet_support_continuity K K K.nonempty K.isCompact K.nonempty K.isCompact).2.2.1

theorem continuous_supportValue_real (K : ConvexBody Point) :
    Continuous (fun t : ℝ ↦ supportValue K (t : Real.Angle)) :=
  (continuous_supportValue K).comp Real.Angle.continuous_coe

/-- Support values of a nonempty compact set are Lipschitz in the real angle, with the largest
norm of a point of the set as Lipschitz constant. -/
theorem abs_supportValue_sub_le_of_isCompact {s : Set Point} (hne : s.Nonempty)
    (hc : IsCompact s) (x y : ℝ) :
    |supportValue s (x : Real.Angle) - supportValue s (y : Real.Angle)| ≤
      sSup (norm '' s) * |x - y| := by
  have hdir := (compactSet_support_continuity s s hne hc hne hc).1
    (normalVector (x : Real.Angle)) (normalVector (y : Real.Angle))
    (norm_normalVector_real x) (norm_normalVector_real y)
  have hframe : ‖normalVector (x : Real.Angle) - normalVector (y : Real.Angle)‖ ≤ |x - y| := by
    simpa [dist_eq_norm, Real.dist_eq] using lipschitzWith_normalVector_real.dist_le_mul x y
  have h0 : 0 ≤ sSup (norm '' s) :=
    Real.sSup_nonneg (by rintro _ ⟨p, -, rfl⟩; exact norm_nonneg p)
  exact hdir.trans (mul_le_mul_of_nonneg_left hframe h0)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Support Embedding
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem supportFunction_minkowski_embedding (K L : ConvexBody Point) :
    (∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → ∀ t : Real.Angle,
      supportValue {z : Point | ∃ x ∈ (K : Set Point), ∃ y ∈ (L : Set Point),
        z = a • x + b • y} t =
        a * supportValue K t + b * supportValue L t) ∧
    ((∀ t : Real.Angle, supportValue K t = supportValue L t) → K = L) ∧
    Continuous (fun t : Real.Angle ↦ supportValue K t) ∧
    (K : Set Point) = ⋂ u ∈ {u : Point | ‖u‖ = 1},
      {p : Point | inner ℝ p u ≤ vectorSupport K u} := by
  refine ⟨?_, ?_, (compactSet_support_continuity K K K.nonempty K.isCompact
    K.nonempty K.isCompact).2.2.1, K.eq_iInter_halfSpaces⟩
  · intro a b ha hb t
    obtain ⟨x, hx, hxmax, hxle⟩ := K.isCompact.exists_sSup_image_eq_and_ge
      (f := fun x : Point ↦ inner ℝ x (normalVector t)) K.nonempty
      (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
    obtain ⟨y, hy, hymax, hyle⟩ := L.isCompact.exists_sSup_image_eq_and_ge
      (f := fun x : Point ↦ inner ℝ x (normalVector t)) L.nonempty
      (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
    change sSup ((fun p ↦ inner ℝ p (normalVector t)) '' K) = _ at hxmax
    change sSup ((fun p ↦ inner ℝ p (normalVector t)) '' L) = _ at hymax
    unfold supportValue
    apply IsGreatest.csSup_eq
    constructor
    · refine ⟨a • x + b • y, ?_, ?_⟩
      · exact ⟨x, hx, y, hy, rfl⟩
      · change inner ℝ (a • x + b • y) (normalVector t) = _
        rw [inner_add_left, inner_smul_left, inner_smul_left, ← hxmax, ← hymax]
        simp
    · intro r hr
      obtain ⟨z, ⟨x', hx', y', hy', rfl⟩, rfl⟩ := hr
      change inner ℝ (a • x' + b • y') (normalVector t) ≤ _
      rw [inner_add_left, inner_smul_left, inner_smul_left]
      rw [hxmax, hymax]
      exact add_le_add (mul_le_mul_of_nonneg_left (hxle x' hx') ha)
        (mul_le_mul_of_nonneg_left (hyle y' hy') hb)
  · intro hKL
    have hvector (u : Point) (hu : ‖u‖ = 1) : vectorSupport K u = vectorSupport L u := by
      obtain ⟨t, rfl⟩ := exists_angle_normalVector_eq hu
      exact hKL t
    simp only [vectorSupport] at hvector
    apply ConvexBody.ext
    rw [K.eq_iInter_halfSpaces,
      L.eq_iInter_halfSpaces]
    ext p
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor <;> intro hp u hu
    · simpa [hvector u hu] using hp u hu
    · simpa [hvector u hu] using hp u hu

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Combination Properties
-/

@[expose] public section

noncomputable section

open scoped Pointwise unitInterval

namespace MovingSofa

/-- Pointwise description of the Minkowski interpolation of two convex bodies. -/
theorem mem_convexBodyCombination_iff (t : I) (K L : ConvexBody Point) (z : Point) :
    z ∈ (convexBodyCombination t K L : Set Point) ↔
      ∃ x ∈ (K : Set Point), ∃ y ∈ (L : Set Point),
        z = (1 - (t : ℝ)) • x + (t : ℝ) • y := by
  change z ∈ (1 - (t : ℝ)) • (K : Set Point) + (t : ℝ) • (L : Set Point) ↔ _
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩

/-- The first edge vertex maximizes tangent coordinate on its exposed edge. -/
theorem inner_le_edgeVertices_fst_tangent (K : ConvexBody Point)
    (a : Real.Angle) {p : Point} (hp : p ∈ exposedEdge K a) :
    inner ℝ p (tangentVector a) ≤ inner ℝ (edgeVertices K a).1 (tangentVector a) := by
  rw [inner_edgeVertices_fst_tangent]
  exact le_csSup ((isCompact_exposedEdge K a).image
    (continuous_id.inner continuous_const) |>.bddAbove) ⟨p, hp, rfl⟩

/-- A tangent-coordinate maximizer on an exposed edge is its first vertex. -/
theorem edgeVertices_fst_eq_of_tangent_isGreatest (K : ConvexBody Point)
    (a : Real.Angle) {p : Point} (hp : p ∈ exposedEdge K a)
    (hmax : ∀ q ∈ exposedEdge K a,
      inner ℝ q (tangentVector a) ≤ inner ℝ p (tangentVector a)) :
    (edgeVertices K a).1 = p := by
  have ht := le_antisymm (hmax _ (edgeVertices_fst_mem K a))
    (inner_le_edgeVertices_fst_tangent K a hp)
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K a).1 a,
    ← inner_normalVector_smul_add_inner_tangentVector_smul p a,
    (edgeVertices_fst_mem K a).2, hp.2, ht]

/-- A tangent-coordinate minimizer on an exposed edge is its second vertex. -/
theorem edgeVertices_snd_eq_of_tangent_isLeast (K : ConvexBody Point)
    (a : Real.Angle) {p : Point} (hp : p ∈ exposedEdge K a)
    (hmin : ∀ q ∈ exposedEdge K a,
      inner ℝ p (tangentVector a) ≤ inner ℝ q (tangentVector a)) :
    (edgeVertices K a).2 = p := by
  have hbdd : BddBelow
      ((fun q : Point ↦ inner ℝ q (tangentVector a)) '' exposedEdge K a) :=
    ((isCompact_exposedEdge K a).image
      (continuous_id.inner continuous_const)).bddBelow
  have ht : inner ℝ (edgeVertices K a).2 (tangentVector a) =
      inner ℝ p (tangentVector a) := by
    rw [inner_edgeVertices_snd_tangent]
    apply le_antisymm (csInf_le hbdd ⟨p, hp, rfl⟩)
    rw [← inner_edgeVertices_snd_tangent]
    exact hmin _ (edgeVertices_snd_mem K a)
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K a).2 a,
    ← inner_normalVector_smul_add_inner_tangentVector_smul p a,
    (edgeVertices_snd_mem K a).2, hp.2, ht]

private theorem inner_edgeVertices_snd_tangent_le_point (K : ConvexBody Point)
    (a : Real.Angle) {p : Point} (hp : p ∈ exposedEdge K a) :
    inner ℝ (edgeVertices K a).2 (tangentVector a) ≤ inner ℝ p (tangentVector a) := by
  rw [inner_edgeVertices_snd_tangent]
  exact csInf_le ((isCompact_exposedEdge K a).image
    (continuous_id.inner continuous_const) |>.bddBelow) ⟨p, hp, rfl⟩

/-- The extreme points of exposed edges commute with convex combinations. -/
theorem edgeVertices_convexBodyCombination (t : I) (K L : ConvexBody Point)
    (a : Real.Angle) :
    (edgeVertices (convexBodyCombination t K L) a).1 =
        (1 - (t : ℝ)) • (edgeVertices K a).1 + (t : ℝ) • (edgeVertices L a).1 ∧
      (edgeVertices (convexBodyCombination t K L) a).2 =
        (1 - (t : ℝ)) • (edgeVertices K a).2 + (t : ℝ) • (edgeVertices L a).2 := by
  let M := convexBodyCombination t K L
  have hedge := exposedEdge_convexBodyCombination K L a t
  have hnonneg : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  have htnonneg : 0 ≤ (t : ℝ) := t.property.1
  constructor
  · apply edgeVertices_fst_eq_of_tangent_isGreatest M a
    · rw [hedge]
      exact Set.add_mem_add (Set.smul_mem_smul_set (edgeVertices_fst_mem K a))
        (Set.smul_mem_smul_set (edgeVertices_fst_mem L a))
    · intro q hq
      rw [hedge] at hq
      obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩ := hq
      simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (inner_le_edgeVertices_fst_tangent K a hx) hnonneg)
        (mul_le_mul_of_nonneg_left (inner_le_edgeVertices_fst_tangent L a hy) htnonneg)
  · apply edgeVertices_snd_eq_of_tangent_isLeast M a
    · rw [hedge]
      exact Set.add_mem_add (Set.smul_mem_smul_set (edgeVertices_snd_mem K a))
        (Set.smul_mem_smul_set (edgeVertices_snd_mem L a))
    · intro q hq
      rw [hedge] at hq
      obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩ := hq
      simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (inner_edgeVertices_snd_tangent_le_point K a hx) hnonneg)
        (mul_le_mul_of_nonneg_left (inner_edgeVertices_snd_tangent_le_point L a hy) htnonneg)

/-- Support values commute with convex combinations. -/
theorem supportValue_convexBodyCombination (t : I) (K L : ConvexBody Point)
    (a : Real.Angle) :
    supportValue (convexBodyCombination t K L) a =
      (1 - (t : ℝ)) * supportValue K a + (t : ℝ) * supportValue L a := by
  rw [show (convexBodyCombination t K L : Set Point) =
      {z : Point | ∃ x ∈ (K : Set Point), ∃ y ∈ (L : Set Point),
        z = (1 - (t : ℝ)) • x + (t : ℝ) • y} from
    Set.ext (mem_convexBodyCombination_iff t K L)]
  exact (supportFunction_minkowski_embedding K L).1
    (1 - (t : ℝ)) t (sub_nonneg.mpr t.property.2) t.property.1 a

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Faces of a body cut out by a differentiable family of half-planes

Let `L` be a convex body lying in every half-plane `{q | m s ≤ ⟪q, u_s⟫}` of a family indexed
by a real angle parameter `s`, and let `p ∈ L` attain the bound at `s = t`.  If `m` is
differentiable at `t` with `m' t = ⟪p, v_t⟫` — that is, if `p` is the first-order contact point
of the family — then the reversed face of `L` at `t + π` is pinned down by the sign of the
one-sided derivatives of `s ↦ ⟪z, u_s⟫ - m s` at `t`:
`exposedEdge_add_pi_eq_singleton_of_mem_Ioo` at an interior parameter gives the singleton
`{p}`, while `edgeVertices_add_pi_fst_eq_of_lt` and `edgeVertices_add_pi_snd_eq_of_lt` identify
`p` with one endpoint vertex of the face at the two boundary parameters.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The tangent coordinate of a point whose normal coordinate dominates a differentiable family
to the left of the touching parameter is at most that of the contact point. -/
theorem inner_tangentVector_le_of_forall_le_Ioo {m : ℝ → ℝ} {p z : Point} {a t : ℝ}
    (hat : a < t) (hle : ∀ s ∈ Set.Ioo a t, m s ≤ inner ℝ z (normalVector (s : Real.Angle)))
    (hzm : inner ℝ z (normalVector (t : Real.Angle)) = m t)
    (hd : HasDerivAt m (inner ℝ p (tangentVector (t : Real.Angle))) t) :
    inner ℝ z (tangentVector (t : Real.Angle)) ≤
      inner ℝ p (tangentVector (t : Real.Angle)) := by
  have hmin : IsLocalMinOn (fun s : ℝ ↦ inner ℝ z (normalVector (s : Real.Angle)) - m s)
      (Set.Iic t) t := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hat), self_mem_nhdsWithin] with s hs hst
    rcases (Set.mem_Iic.1 hst).lt_or_eq with h | rfl
    · simpa only [hzm, sub_self] using sub_nonneg.2 (hle s ⟨hs, h⟩)
    · exact le_rfl
  have hF := (hasDerivAt_inner_normalVector z t).sub hd
  linarith only [hmin.hasDerivWithinAt_Iic_nonpos hF.hasDerivWithinAt]

/-- The tangent coordinate of a point whose normal coordinate dominates a differentiable family
to the right of the touching parameter is at least that of the contact point. -/
theorem le_inner_tangentVector_of_forall_le_Ioo {m : ℝ → ℝ} {p z : Point} {t b : ℝ}
    (htb : t < b) (hle : ∀ s ∈ Set.Ioo t b, m s ≤ inner ℝ z (normalVector (s : Real.Angle)))
    (hzm : inner ℝ z (normalVector (t : Real.Angle)) = m t)
    (hd : HasDerivAt m (inner ℝ p (tangentVector (t : Real.Angle))) t) :
    inner ℝ p (tangentVector (t : Real.Angle)) ≤
      inner ℝ z (tangentVector (t : Real.Angle)) := by
  have hmin : IsLocalMinOn (fun s : ℝ ↦ inner ℝ z (normalVector (s : Real.Angle)) - m s)
      (Set.Ici t) t := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds htb), self_mem_nhdsWithin] with s hs hst
    rcases (Set.mem_Ici.1 hst).lt_or_eq with h | rfl
    · simpa only [hzm, sub_self] using sub_nonneg.2 (hle s ⟨h, hs⟩)
    · exact le_rfl
  have hF := (hasDerivAt_inner_normalVector z t).sub hd
  linarith only [hmin.hasDerivWithinAt_Ici_nonneg hF.hasDerivWithinAt]

/-- At an interior touching parameter of a differentiable family of supporting half-planes the
reversed face is the singleton contact point. -/
theorem exposedEdge_add_pi_eq_singleton_of_mem_Ioo {L : ConvexBody Point} {m : ℝ → ℝ}
    {p : Point} {a b t : ℝ} (ht : t ∈ Set.Ioo a b)
    (hle : ∀ q ∈ (L : Set Point), ∀ s ∈ Set.Ioo a b,
      m s ≤ inner ℝ q (normalVector (s : Real.Angle)))
    (hp : p ∈ (L : Set Point))
    (hpm : inner ℝ p (normalVector (t : Real.Angle)) = m t)
    (hd : HasDerivAt m (inner ℝ p (tangentVector (t : Real.Angle))) t) :
    exposedEdge L ((t + Real.pi : ℝ) : Real.Angle) = {p} := by
  have hlet : ∀ q ∈ (L : Set Point), m t ≤ inner ℝ q (normalVector (t : Real.Angle)) :=
    fun q hq ↦ hle q hq t ht
  rw [exposedEdge_add_pi_eq_of_forall_le hlet hp hpm]
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  refine ⟨fun hq ↦ ?_, fun hq ↦ ⟨hq ▸ hp, hq ▸ hpm⟩⟩
  have h1 : inner ℝ q (tangentVector (t : Real.Angle)) ≤
      inner ℝ p (tangentVector (t : Real.Angle)) :=
    inner_tangentVector_le_of_forall_le_Ioo ht.1
      (fun s hs ↦ hle q hq.1 s ⟨hs.1, hs.2.trans ht.2⟩) hq.2 hd
  have h2 : inner ℝ p (tangentVector (t : Real.Angle)) ≤
      inner ℝ q (tangentVector (t : Real.Angle)) :=
    le_inner_tangentVector_of_forall_le_Ioo ht.2
      (fun s hs ↦ hle q hq.1 s ⟨ht.1.trans hs.1, hs.2⟩) hq.2 hd
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul q (t : Real.Angle),
    ← inner_normalVector_smul_add_inner_tangentVector_smul p (t : Real.Angle),
    hq.2, hpm, le_antisymm h1 h2]

/-- At the left endpoint parameter of a differentiable family of supporting half-planes the
contact point is the positive vertex of the reversed face. -/
theorem edgeVertices_add_pi_fst_eq_of_lt {L : ConvexBody Point} {m : ℝ → ℝ} {p : Point}
    {a b : ℝ} (hab : a < b)
    (hle : ∀ q ∈ (L : Set Point), ∀ s ∈ Set.Ioo a b,
      m s ≤ inner ℝ q (normalVector (s : Real.Angle)))
    (hlea : ∀ q ∈ (L : Set Point), m a ≤ inner ℝ q (normalVector (a : Real.Angle)))
    (hp : p ∈ (L : Set Point))
    (hpm : inner ℝ p (normalVector (a : Real.Angle)) = m a)
    (hd : HasDerivAt m (inner ℝ p (tangentVector (a : Real.Angle))) a) :
    (edgeVertices L ((a + Real.pi : ℝ) : Real.Angle)).1 = p := by
  have hface := exposedEdge_add_pi_eq_of_forall_le hlea hp hpm
  refine edgeVertices_fst_eq_of_tangent_isGreatest L _ (hface ▸ ⟨hp, hpm⟩) ?_
  intro q hq
  rw [hface] at hq
  have h1 : inner ℝ p (tangentVector (a : Real.Angle)) ≤
      inner ℝ q (tangentVector (a : Real.Angle)) :=
    le_inner_tangentVector_of_forall_le_Ioo hab (fun s hs ↦ hle q hq.1 s hs) hq.2 hd
  rw [tangentVector_add_pi, inner_neg_right, inner_neg_right]
  linarith only [h1]

/-- At the right endpoint parameter of a differentiable family of supporting half-planes the
contact point is the negative vertex of the reversed face. -/
theorem edgeVertices_add_pi_snd_eq_of_lt {L : ConvexBody Point} {m : ℝ → ℝ} {p : Point}
    {a b : ℝ} (hab : a < b)
    (hle : ∀ q ∈ (L : Set Point), ∀ s ∈ Set.Ioo a b,
      m s ≤ inner ℝ q (normalVector (s : Real.Angle)))
    (hleb : ∀ q ∈ (L : Set Point), m b ≤ inner ℝ q (normalVector (b : Real.Angle)))
    (hp : p ∈ (L : Set Point))
    (hpm : inner ℝ p (normalVector (b : Real.Angle)) = m b)
    (hd : HasDerivAt m (inner ℝ p (tangentVector (b : Real.Angle))) b) :
    (edgeVertices L ((b + Real.pi : ℝ) : Real.Angle)).2 = p := by
  have hface := exposedEdge_add_pi_eq_of_forall_le hleb hp hpm
  refine edgeVertices_snd_eq_of_tangent_isLeast L _ (hface ▸ ⟨hp, hpm⟩) ?_
  intro q hq
  rw [hface] at hq
  have h1 : inner ℝ q (tangentVector (b : Real.Angle)) ≤
      inner ℝ p (tangentVector (b : Real.Angle)) :=
    inner_tangentVector_le_of_forall_le_Ioo hab (fun s hs ↦ hle q hq.1 s hs) hq.2 hd
  rw [tangentVector_add_pi, inner_neg_right, inner_neg_right]
  linarith only [h1]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Space
-/

@[expose] public section

open scoped unitInterval Pointwise

namespace MovingSofa

/-- Convex bodies form a convex domain under Minkowski interpolation. -/
theorem convexBody_isConvexDomain : IsConvexDomain.{0, 0} convexBodyCombination := by
  let e : ConvexBody Point → C(Real.Angle, ℝ) := fun K ↦
    ⟨fun t ↦ supportValue K t, (supportFunction_minkowski_embedding K K).2.2.1⟩
  have he (t : I) (K L : ConvexBody Point) :
      e (convexBodyCombination t K L) = (1 - (t : ℝ)) • e K + (t : ℝ) • e L := by
    ext u
    change supportValue (convexBodyCombination t K L) u = _
    exact supportValue_convexBodyCombination t K L u
  refine ⟨ModuleCat.of ℝ C(Real.Angle, ℝ), e, ?_, ?_, he⟩
  · intro K L h
    apply (supportFunction_minkowski_embedding K L).2.1
    intro t
    exact congrArg (fun f : C(Real.Angle, ℝ) ↦ f t) h
  · rintro _ ⟨K, rfl⟩ _ ⟨L, rfl⟩ a b ha hb hab
    refine ⟨convexBodyCombination ⟨b, hb, by linarith⟩ K L, ?_⟩
    have h : 1 - b = a := by linarith
    simpa only [h] using he ⟨b, hb, by linarith⟩ K L

end MovingSofa

end

end
