/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Convex.Foundations.Development001
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
/-!
# Moving sofa: related mathematical developments

* `Area.ModuloLinear`.
* `Area.Quadratic`.
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
# Area / Modulo Linear
-/

@[expose] public section

noncomputable section

open scoped unitInterval

universe u

namespace MovingSofa

/-- The difference of two functionals preserves the specified convex combinations. -/
def EquivalentModuloConvexLinear {α : Type u} (c : I → α → α → α)
    (f g : α → ℝ) : Prop :=
  IsConvexLinear c realCombination (fun x ↦ f x - g x)

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
# Area / Quadratic
-/

@[expose] public section

noncomputable section

open scoped unitInterval

universe u v

namespace MovingSofa

/-- The directional derivative along a barycentric segment is computed by any derivative of the
segment function at the base point. -/
theorem convexDirectionalDerivative_eq_of_hasDerivWithinAt {α : Type u} (c : I → α → α → α)
    (f : α → ℝ) (x y : α) {d : ℝ}
    (h : HasDerivWithinAt (segmentFunctional c f x y) d (Set.Icc 0 1) 0) :
    convexDirectionalDerivative c f x y = d :=
  h.derivWithin (uniqueDiffOn_Icc_zero_one.uniqueDiffWithinAt (by norm_num))

/-- A quadratic diagonal has the stated segment derivative, affine in its destination. -/
theorem quadratic_directional_derivative {α : Type u} (c : I → α → α → α) (f : α → ℝ) (h : α → α →
  ℝ)
    (hh : IsConvexBilinear c c realCombination h) (hf : ∀ x, f x = h x x) :
    (∀ x y, HasDerivWithinAt (segmentFunctional c f x y)
      (h x y + h y x - 2 * h x x) (Set.Icc 0 1) 0) ∧
    (∀ x y, convexDirectionalDerivative c f x y = h x y + h y x - 2 * h x x) ∧
    ∀ x, IsConvexLinear c realCombination (fun y ↦ convexDirectionalDerivative c f x y) := by
  have hquad (t : I) (x y : α) :
      f (c t x y) =
        (1 - (t : ℝ)) ^ 2 * h x x +
          (t : ℝ) * (1 - (t : ℝ)) * (h x y + h y x) + (t : ℝ) ^ 2 * h y y := by
    rw [hf]
    have hleft := hh.2 (c t x y) t x y
    change h (c t x y) (c t x y) =
      realCombination t (h x (c t x y)) (h y (c t x y)) at hleft
    rw [hleft, hh.1 x t x y, hh.1 y t x y]
    simp only [realCombination]
    ring
  have hderiv (x y : α) : HasDerivAt
      (fun t : ℝ ↦ (1 - t) ^ 2 * h x x +
        t * (1 - t) * (h x y + h y x) + t ^ 2 * h y y)
      (h x y + h y x - 2 * h x x) 0 := by
    have hid : HasDerivAt (fun t : ℝ ↦ t) 1 0 := hasDerivAt_id 0
    have hsub : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) 0 := hid.const_sub 1
    convert (((hsub.pow 2).mul_const (h x x)).add
      ((hid.mul hsub).mul_const (h x y + h y x))).add
      ((hid.pow 2).mul_const (h y y)) using 1
    all_goals ring
  have hfirst : ∀ x y, HasDerivWithinAt (segmentFunctional c f x y)
      (h x y + h y x - 2 * h x x) (Set.Icc 0 1) 0 := by
    intro x y
    apply (hderiv x y).hasDerivWithinAt.congr
    · intro t ht
      simp only [segmentFunctional, ht, ↓reduceDIte]
      exact hquad ⟨t, ht⟩ x y
    · simp [segmentFunctional, hquad]
  refine ⟨hfirst, ?_, ?_⟩
  · exact fun x y ↦ convexDirectionalDerivative_eq_of_hasDerivWithinAt c f x y (hfirst x y)
  · intro x t y z
    unfold convexDirectionalDerivative
    have huniq : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) 1) 0 :=
      uniqueDiffOn_Icc_zero_one.uniqueDiffWithinAt (by norm_num)
    change derivWithin (segmentFunctional c f x (c t y z)) (Set.Icc 0 1) 0 =
      realCombination t
        (derivWithin (segmentFunctional c f x y) (Set.Icc 0 1) 0)
        (derivWithin (segmentFunctional c f x z) (Set.Icc 0 1) 0)
    rw [(hfirst x (c t y z)).derivWithin huniq,
      (hfirst x y).derivWithin huniq, (hfirst x z).derivWithin huniq]
    simp only [realCombination]
    have hright := hh.2 x t y z
    change h (c t y z) x = realCombination t (h y x) (h z x) at hright
    rw [hh.1 x t y z, hright]
    simp only [realCombination]
    ring

/-- The segment function of a quadratic functional is differentiable at the base point, with the
directional derivative as its derivative. -/
theorem IsQuadraticFunctional.hasDerivWithinAt_segmentFunctional {α : Type u}
    {c : I → α → α → α} {f : α → ℝ} (hf : IsQuadraticFunctional c f)
    (x y : α) :
    HasDerivWithinAt (segmentFunctional c f x y)
      (convexDirectionalDerivative c f x y) (Set.Icc 0 1) 0 := by
  obtain ⟨g, hg, hfg⟩ := hf
  obtain ⟨hderiv, hderiv_eq, -⟩ := quadratic_directional_derivative c f g hg hfg
  rw [hderiv_eq x y]
  exact hderiv x y

/-- A concave quadratic functional is maximized exactly where all directional derivatives are
nonpositive. -/
theorem quadratic_maximum_iff {α : Type u} (c : I → α → α → α)
    (hc : IsConvexDomain.{u, v} c) (f : α → ℝ)
    (hq : IsQuadraticFunctional c f) (hconcave : IsConvexFunctional c f true) (x : α) :
    (∀ y, f y ≤ f x) ↔ ∀ y, convexDirectionalDerivative c f x y ≤ 0 := by
  obtain ⟨g, hg, hfg⟩ := hq
  obtain ⟨hderiv, hderiv_eq, -⟩ :=
    quadratic_directional_derivative c f g hg hfg
  obtain ⟨V, e, he, -, hcmap⟩ := hc
  have hc0 (z : α) : c 0 x z = x := by
    apply he
    rw [hcmap]
    simp
  have hquad (t : I) (y : α) :
      f (c t x y) =
        (1 - (t : ℝ)) ^ 2 * g x x +
          (t : ℝ) * (1 - (t : ℝ)) * (g x y + g y x) +
            (t : ℝ) ^ 2 * g y y := by
    rw [hfg]
    have hleft := hg.2 (c t x y) t x y
    change g (c t x y) (c t x y) =
      realCombination t (g x (c t x y)) (g y (c t x y)) at hleft
    rw [hleft, hg.1 x t x y, hg.1 y t x y]
    simp only [realCombination]
    ring
  constructor
  · intro hmax y
    have hlocal : IsLocalMaxOn (segmentFunctional c f x y) (Set.Icc 0 1) 0 :=
      by
        filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [segmentFunctional, ht, ↓reduceDIte, Set.mem_Icc, Std.le_refl, zero_le_one,
          and_self,
          Set.Icc.mk_zero, hc0]
        exact hmax _
    have htangent : (1 : ℝ) ∈ posTangentConeAt (Set.Icc 0 1) 0 := by
      simpa using sub_mem_posTangentConeAt_of_segment_subset
        (show segment ℝ (0 : ℝ) 1 ⊆ Set.Icc 0 1 by rw [segment_eq_Icc (by norm_num)])
    have := hlocal.hasFDerivWithinAt_nonpos (hderiv x y).hasFDerivWithinAt htangent
    simpa [hderiv_eq] using this
  · intro hd y
    have hmid := hconcave (⟨1 / 2, by constructor <;> norm_num⟩ : I) x y
    simp only [↓reduceIte, realCombination] at hmid
    rw [hquad, hfg x, hfg y] at hmid
    have hcoef : g x x - g x y - g y x + g y y ≤ 0 := by
      norm_num at hmid ⊢
      linarith
    have := hd y
    rw [hderiv_eq x y] at this
    rw [hfg y, hfg x]
    linarith

/-- A sum of quadratic functionals is quadratic. -/
theorem IsQuadraticFunctional.add {α : Type u} {c : I → α → α → α} {f g : α → ℝ}
    (hf : IsQuadraticFunctional c f) (hg : IsQuadraticFunctional c g) :
    IsQuadraticFunctional c (fun x ↦ f x + g x) := by
  obtain ⟨F, ⟨hFright, hFleft⟩, hFf⟩ := hf
  obtain ⟨G, ⟨hGright, hGleft⟩, hGg⟩ := hg
  refine ⟨fun x y ↦ F x y + G x y, ⟨fun x t y z ↦ ?_, fun z t x y ↦ ?_⟩, fun x ↦ ?_⟩
  · change F x (c t y z) + G x (c t y z) = realCombination t (F x y + G x y) (F x z + G x z)
    rw [hFright x t y z, hGright x t y z]
    simp only [realCombination]
    ring
  · have hF : F (c t x y) z = realCombination t (F x z) (F y z) := hFleft z t x y
    have hG : G (c t x y) z = realCombination t (G x z) (G y z) := hGleft z t x y
    change F (c t x y) z + G (c t x y) z = realCombination t (F x z + G x z) (F y z + G y z)
    rw [hF, hG]
    simp only [realCombination]
    ring
  · change f x + g x = F x x + G x x
    rw [hFf x, hGg x]

/-- A sum of convex functionals is convex, and a sum of concave functionals is concave. -/
theorem IsConvexFunctional.add {α : Type u} {c : I → α → α → α} {f g : α → ℝ} {concave : Bool}
    (hf : IsConvexFunctional c f concave) (hg : IsConvexFunctional c g concave) :
    IsConvexFunctional c (fun x ↦ f x + g x) concave := by
  intro t x y
  have hsum : ∀ u v w z : ℝ, realCombination t u v + realCombination t w z =
      realCombination t (u + w) (v + z) := by
    intro u v w z
    simp only [realCombination]
    ring
  cases concave
  · have hfxy : f (c t x y) ≤ realCombination t (f x) (f y) := hf t x y
    have hgxy : g (c t x y) ≤ realCombination t (g x) (g y) := hg t x y
    change f (c t x y) + g (c t x y) ≤ realCombination t (f x + g x) (f y + g y)
    rw [← hsum]
    exact add_le_add hfxy hgxy
  · have hfxy : realCombination t (f x) (f y) ≤ f (c t x y) := hf t x y
    have hgxy : realCombination t (g x) (g y) ≤ g (c t x y) := hg t x y
    change realCombination t (f x + g x) (f y + g y) ≤ f (c t x y) + g (c t x y)
    rw [← hsum]
    exact add_le_add hfxy hgxy

/-- A convex-linear real functional satisfies both barycentric inequalities, with equality. -/
theorem IsConvexLinear.isConvexFunctional {α : Type u} {c : I → α → α → α} {f : α → ℝ}
    (hf : IsConvexLinear c realCombination f) (concave : Bool) :
    IsConvexFunctional c f concave := by
  intro t x y
  cases concave
  · change f (c t x y) ≤ realCombination t (f x) (f y)
    exact (hf t x y).le
  · change realCombination t (f x) (f y) ≤ f (c t x y)
    exact (hf t x y).ge

/-- A convex-linear real functional is quadratic: it is the diagonal of the mean of its values. -/
theorem IsConvexLinear.isQuadraticFunctional {α : Type u} {c : I → α → α → α} {f : α → ℝ}
    (hf : IsConvexLinear c realCombination f) : IsQuadraticFunctional c f := by
  refine ⟨fun x y ↦ (f x + f y) / 2, ⟨fun x t y z ↦ ?_, fun z t x y ↦ ?_⟩, fun x ↦ ?_⟩
  · change (f x + f (c t y z)) / 2 = realCombination t ((f x + f y) / 2) ((f x + f z) / 2)
    rw [hf t y z]
    simp only [realCombination]
    ring
  · change (f (c t x y) + f z) / 2 = realCombination t ((f x + f z) / 2) ((f y + f z) / 2)
    rw [hf t x y]
    simp only [realCombination]
    ring
  · change f x = (f x + f x) / 2
    ring

/-- Negation exchanges convexity and concavity. -/
theorem IsConvexFunctional.neg {α : Type u} {c : I → α → α → α} {f : α → ℝ} {concave : Bool}
    (hf : IsConvexFunctional c f concave) : IsConvexFunctional c (fun x ↦ -f x) (!concave) := by
  intro t x y
  have hneg : realCombination t (-f x) (-f y) = -realCombination t (f x) (f y) := by
    simp only [realCombination]
    ring
  cases concave
  · have h : f (c t x y) ≤ realCombination t (f x) (f y) := hf t x y
    change realCombination t (-f x) (-f y) ≤ -f (c t x y)
    rw [hneg]
    exact neg_le_neg h
  · have h : realCombination t (f x) (f y) ≤ f (c t x y) := hf t x y
    change -f (c t x y) ≤ realCombination t (-f x) (-f y)
    rw [hneg]
    exact neg_le_neg h

/-- The negative of a quadratic functional is quadratic. -/
theorem IsQuadraticFunctional.neg {α : Type u} {c : I → α → α → α} {f : α → ℝ}
    (hf : IsQuadraticFunctional c f) : IsQuadraticFunctional c (fun x ↦ -f x) := by
  obtain ⟨F, ⟨hFright, hFleft⟩, hFf⟩ := hf
  have hneg : ∀ (t : I) (u v : ℝ), -realCombination t u v = realCombination t (-u) (-v) := by
    intro t u v
    simp only [realCombination]
    ring
  refine ⟨fun x y ↦ -F x y, ⟨fun x t y z ↦ ?_, fun z t x y ↦ ?_⟩, fun x ↦ ?_⟩
  · change -F x (c t y z) = realCombination t (-F x y) (-F x z)
    rw [hFright x t y z, hneg]
  · have hF : F (c t x y) z = realCombination t (F x z) (F y z) := hFleft z t x y
    change -F (c t x y) z = realCombination t (-F x z) (-F y z)
    rw [hF, hneg]
  · change -f x = -F x x
    rw [hFf x]

end MovingSofa

end

end

end
