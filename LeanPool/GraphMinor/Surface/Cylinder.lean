/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting

/-!
# The Cylinder Surface and Winding Numbers of Curves

This file develops the topological foundations for the cylinder
$\Sigma = [1, 2] \times S^1$ (`ClosedCylinder`) and the winding number $\theta(f) \in \mathbb{R}$
of continuous curves $f \colon [0, 1] \to \Sigma$, as used in Graph Minors VI, Sections 4–5
(pages 122–135):
- The two boundary cuffs `cylinderCuff1` ($\{1\} \times S^1$) and `cylinderCuff2`
  ($\{2\} \times S^1$), and polar-coordinate point constructor `cylinderPoint`.
- The unique path lift `cylinderAngleLift` of the angular component of a curve $f$ through the
  universal covering map `Circle.exp : ℝ → Circle` (`Circle.isCoveringMap_exp.liftPath` from
  `Mathlib.Topology.Homotopy.Lifting` and `Mathlib.Analysis.SpecialFunctions.Complex.Circle`).
- The winding number `windingNumber f` ($\theta(f)$ in Graph Minors VI, Section 5, page 127).
- Homotopy invariance of the winding number, integrality of $\theta(f_0) - \theta(f_1)$ for curves
  with the same endpoints, and the converse theorem that two curves on the cylinder with the same
  endpoints are homotopic if and only if their winding numbers are equal.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Function Complex Real Topology unitInterval

/-! ## 1. Cuffs and Polar Coordinates on `ClosedCylinder` -/

/-- The radial coordinate $r \in [1, 2]$ of a point on `ClosedCylinder`. -/
def cylinderRadius (p : ClosedCylinder) : ℝ :=
  p.1.1

/-- The angular coordinate on `Circle` of a point on `ClosedCylinder`. -/
def cylinderAngle (p : ClosedCylinder) : Circle :=
  p.1.2

theorem cylinderRadius_mem_Icc (p : ClosedCylinder) :
    cylinderRadius p ∈ Icc (1 : ℝ) 2 :=
  p.2.1

/-- The inner cuff $C_1 = \{1\} \times S^1$ of `ClosedCylinder`.
Graph Minors VI, Section 5 (page 127): "$$C_i = \{(i, \theta): 0 \le \theta < 2\pi\} \qquad (i = 1,
2).$$" -/
def cylinderCuff1 : Set ClosedCylinder :=
  {p : ClosedCylinder | p.1.1 = 1}

/-- The outer cuff $C_2 = \{2\} \times S^1$ of `ClosedCylinder`.
Graph Minors VI, Section 5 (page 127). -/
def cylinderCuff2 : Set ClosedCylinder :=
  {p : ClosedCylinder | p.1.1 = 2}

theorem disjoint_cylinderCuffs : Disjoint cylinderCuff1 cylinderCuff2 := by
  rw [Set.disjoint_left]
  intro p hp1 hp2
  change p.1.1 = 1 at hp1
  change p.1.1 = 2 at hp2
  linarith

/-- Construct a point $(r, \theta)$ on `ClosedCylinder` from $r \in [1, 2]$ and angle $\theta \in
\mathbb{R}$.
Graph Minors VI, Section 5 (page 127). -/
noncomputable def cylinderPoint (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) (θ : ℝ) : ClosedCylinder :=
  ⟨(r, Circle.exp θ), hr, trivial⟩

@[simp]
theorem cylinderRadius_cylinderPoint (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) (θ : ℝ) :
    cylinderRadius (cylinderPoint r hr θ) = r :=
  rfl

@[simp]
theorem cylinderAngle_cylinderPoint (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) (θ : ℝ) :
    cylinderAngle (cylinderPoint r hr θ) = Circle.exp θ :=
  rfl

/-! ## 2. Covering Lift and Winding Number $\theta(f)$ -/

/-- The angular projection $\gamma \colon [0, 1] \to S^1$ of a curve $f$ on `ClosedCylinder`. -/
def curveCircleProj (f : Curve ClosedCylinder) : C(unitInterval, Circle) :=
  ⟨fun x => (f x).1.2, continuous_snd.comp (continuous_subtype_val.comp f.continuous)⟩

@[simp]
theorem curveCircleProj_apply (f : Curve ClosedCylinder) (x : unitInterval) :
    curveCircleProj f x = (f x).1.2 :=
  rfl

/-- The unique continuous angular lift $\Gamma \colon [0, 1] \to \mathbb{R}$ of a curve $f$ on
`ClosedCylinder` starting at $\operatorname{arg}(f(0)) \in (-\pi, \pi]$.
Route: `IsCoveringMap.liftPath` applied to `Circle.isCoveringMap_exp`. -/
noncomputable def cylinderAngleLift (f : Curve ClosedCylinder) : C(unitInterval, ℝ) :=
  Circle.isCoveringMap_exp.liftPath (curveCircleProj f) (arg ((f 0).1.2 : ℂ))
    (Circle.exp_arg (f 0).1.2).symm

@[simp]
theorem cylinderAngleLift_zero (f : Curve ClosedCylinder) :
    cylinderAngleLift f 0 = arg ((f 0).1.2 : ℂ) :=
  Circle.isCoveringMap_exp.liftPath_zero _ _ _

theorem exp_comp_cylinderAngleLift (f : Curve ClosedCylinder) :
    Circle.exp ∘ cylinderAngleLift f = curveCircleProj f :=
  Circle.isCoveringMap_exp.liftPath_lifts _ _ _

@[simp]
theorem exp_cylinderAngleLift (f : Curve ClosedCylinder) (x : unitInterval) :
    Circle.exp (cylinderAngleLift f x) = (f x).1.2 :=
  congr_fun (exp_comp_cylinderAngleLift f) x

/-- The *winding number* $\theta(f) \in \mathbb{R}$ of a continuous curve $f \colon [0, 1] \to
\Sigma$
on the cylinder $\Sigma = [1, 2] \times S^1$, defined as $1/(2\pi)$ times the net angle turned
through by the lifted path `cylinderAngleLift f`.
Graph Minors VI, Section 5 (page 127): "Let $f: [0, 1] \to \Sigma$ be continuous. Then it has
a finite *winding number* $\theta(f)$, defined intuitively as $1/2\pi$ times the the total angle
turned
through (measured counterclockwise) by the line $OX$, where $O$ is the origin, $X = f(x)$, and $x$
ranges from 0 to 1." -/
noncomputable def windingNumber (f : Curve ClosedCylinder) : ℝ :=
  (cylinderAngleLift f 1 - cylinderAngleLift f 0) / (2 * π)

/-- A constant curve on the cylinder has winding number $0$. -/
theorem windingNumber_const {f : Curve ClosedCylinder} (hf : f.IsConstant) :
    windingNumber f = 0 := by
  rcases hf with ⟨c, hc⟩
  have hlift : cylinderAngleLift f = ContinuousMap.const unitInterval (arg ((f 0).1.2 : ℂ)) := by
    symm
    refine (Circle.isCoveringMap_exp.eq_liftPath_iff' _).mpr ⟨?_, rfl⟩
    ext x
    simp [hc x, hc 0, Circle.exp_arg]
  simp [windingNumber, hlift]

/-- Homotopic curves on the cylinder have the same winding number.
Graph Minors VI, Section 5 (page 127).
Route: monodromy invariance `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` applied to
`Circle.isCoveringMap_exp`. -/
theorem windingNumber_eq_of_homotopic {f₀ f₁ : Curve ClosedCylinder}
    (h : CurvesHomotopic f₀ f₁) :
    windingNumber f₀ = windingNumber f₁ := by
  rcases h with ⟨ψ, _, hψ0, hψ1, hψy0, hψy0', hψy1, hψy1'⟩
  have h0_eq : f₀ 0 = f₁ 0 := by
    rw [← hψy0 0, ← hψy0' 0]
  have h1_eq : f₀ 1 = f₁ 1 := by
    rw [← hψy1 0, ← hψy1' 0]
  let H_map : C(unitInterval × unitInterval, Circle) :=
    ⟨fun tx => (ψ (tx.2, tx.1)).1.2,
      continuous_snd.comp (continuous_subtype_val.comp
        (ψ.continuous.comp (continuous_snd.prodMk continuous_fst)))⟩
  let H_rel : (curveCircleProj f₀).HomotopyRel (curveCircleProj f₁) {0, 1} :=
    { toContinuousMap := H_map
      map_zero_left := fun x => congrArg (fun p : ClosedCylinder => p.1.2) (hψ0 x)
      map_one_left := fun x => congrArg (fun p : ClosedCylinder => p.1.2) (hψ1 x)
      prop' := by
        intro t x hx
        rcases hx with rfl | rfl
        · exact congrArg (fun p : ClosedCylinder => p.1.2) (hψy0 t)
        · exact congrArg (fun p : ClosedCylinder => p.1.2) (hψy1 t) }
  have hhom : (curveCircleProj f₀).HomotopicRel (curveCircleProj f₁) {0, 1} := ⟨H_rel⟩
  have hstart : arg ((f₀ 0).1.2 : ℂ) = arg ((f₁ 0).1.2 : ℂ) := by rw [h0_eq]
  have hend : cylinderAngleLift f₀ 1 = cylinderAngleLift f₁ 1 := by
    have h := Circle.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel hhom
      (arg ((f₀ 0).1.2 : ℂ)) (Circle.exp_arg (f₀ 0).1.2).symm
      (by rw [curveCircleProj_apply, ← h0_eq, Circle.exp_arg])
    have heq_lift : Circle.isCoveringMap_exp.liftPath (curveCircleProj f₁) (arg ((f₀ 0).1.2 : ℂ))
        (by rw [curveCircleProj_apply, ← h0_eq, Circle.exp_arg]) = cylinderAngleLift f₁ := by
      symm
      refine (Circle.isCoveringMap_exp.eq_liftPath_iff' _).mpr ⟨?_, ?_⟩
      · exact exp_comp_cylinderAngleLift f₁
      · simp [h0_eq]
    rw [heq_lift] at h
    exact h
  simp only [windingNumber, cylinderAngleLift_zero, hend, hstart]

/-- If two curves on the cylinder have the same initial point and the same terminal point, then
the difference of their winding numbers is an integer.
Graph Minors VI, Section 5 (page 127): "If $P_1$, $P_2$ are both paths drawn on $\Sigma$ from some
$s \in C_1$ to some $t \in C_2$, then $\theta(P_1) - \theta(P_2)$ is an integer, and is zero if and
only if $P_1$ is homotopic to $P_2$."
Route: fiber periodicity `Circle.exp_eq_exp`. -/
theorem windingNumber_sub_int_of_same_ends {f₀ f₁ : Curve ClosedCylinder}
    (h0 : f₀ 0 = f₁ 0) (h1 : f₀ 1 = f₁ 1) :
    ∃ m : ℤ, windingNumber f₀ - windingNumber f₁ = m := by
  have hexp : Circle.exp (cylinderAngleLift f₀ 1) = Circle.exp (cylinderAngleLift f₁ 1) := by
    rw [exp_cylinderAngleLift, exp_cylinderAngleLift, h1]
  rcases Circle.exp_eq_exp.mp hexp with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  have hstart : cylinderAngleLift f₀ 0 = cylinderAngleLift f₁ 0 := by
    simp [h0]
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  unfold windingNumber
  rw [hm, hstart]
  field_simp [h2pi]
  ring

/-- If two curves on the cylinder have the same endpoints and the same winding number, then they
are homotopic on the cylinder.
Graph Minors VI, Section 5 (page 127).
Route: straight-line homotopy of the radial coordinates in $[1, 2]$ and of the lifted angular
paths `cylinderAngleLift` in $\mathbb{R}$, projected back to `ClosedCylinder` via `Circle.exp`. -/
theorem curvesHomotopic_of_windingNumber_eq {f₀ f₁ : Curve ClosedCylinder}
    (h0 : f₀ 0 = f₁ 0) (h1 : f₀ 1 = f₁ 1)
    (hw : windingNumber f₀ = windingNumber f₁) :
    CurvesHomotopic f₀ f₁ := by
  have hstart : cylinderAngleLift f₀ 0 = cylinderAngleLift f₁ 0 := by simp [h0]
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have hend : cylinderAngleLift f₀ 1 = cylinderAngleLift f₁ 1 := by
    unfold windingNumber at hw
    have hw' := (div_left_inj₀ h2pi).mp hw
    linarith
  have hr_mem : ∀ p : unitInterval × unitInterval,
      (1 - (p.2 : ℝ)) * (f₀ p.1).1.1 + (p.2 : ℝ) * (f₁ p.1).1.1 ∈ Icc (1 : ℝ) 2 := by
    intro p
    exact convex_Icc (1 : ℝ) 2 (f₀ p.1).2.1 (f₁ p.1).2.1
      (sub_nonneg.mpr p.2.2.2) p.2.2.1 (sub_add_cancel 1 (p.2 : ℝ))
  let rMap : C(unitInterval × unitInterval, ℝ) :=
    ⟨fun p => (1 - (p.2 : ℝ)) * (f₀ p.1).1.1 + (p.2 : ℝ) * (f₁ p.1).1.1,
      Continuous.add
        (Continuous.mul (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
          (continuous_fst.comp (continuous_subtype_val.comp (f₀.continuous.comp continuous_fst))))
        (Continuous.mul (continuous_subtype_val.comp continuous_snd)
          (continuous_fst.comp (continuous_subtype_val.comp (f₁.continuous.comp continuous_fst))))⟩
  let θMap : C(unitInterval × unitInterval, ℝ) :=
    ⟨fun p => (1 - (p.2 : ℝ)) * cylinderAngleLift f₀ p.1 + (p.2 : ℝ) * cylinderAngleLift f₁ p.1,
      Continuous.add
        (Continuous.mul (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
          ((cylinderAngleLift f₀).continuous.comp continuous_fst))
        (Continuous.mul (continuous_subtype_val.comp continuous_snd)
          ((cylinderAngleLift f₁).continuous.comp continuous_fst))⟩
  let Ψ : C(unitInterval × unitInterval, ClosedCylinder) :=
    ⟨fun p => ⟨(rMap p, Circle.exp (θMap p)), hr_mem p, trivial⟩,
      (rMap.continuous.prodMk (Circle.exp.continuous.comp θMap.continuous)).subtype_mk
        (fun p => ⟨hr_mem p, trivial⟩)⟩
  refine ⟨Ψ, fun _ => trivial, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    ext1; ext1
    · change (1 - (0 : ℝ)) * (f₀ x).1.1 + (0 : ℝ) * (f₁ x).1.1 = (f₀ x).1.1
      ring
    · change Circle.exp ((1 - (0 : ℝ)) * cylinderAngleLift f₀ x + (0 : ℝ) * cylinderAngleLift f₁ x)
      = (f₀ x).1.2
      have : (1 - (0 : ℝ)) * cylinderAngleLift f₀ x + (0 : ℝ) * cylinderAngleLift f₁ x
        = cylinderAngleLift f₀ x := by ring
      rw [this, exp_cylinderAngleLift]
  · intro x
    ext1; ext1
    · change (1 - (1 : ℝ)) * (f₀ x).1.1 + (1 : ℝ) * (f₁ x).1.1 = (f₁ x).1.1
      ring
    · change Circle.exp ((1 - (1 : ℝ)) * cylinderAngleLift f₀ x + (1 : ℝ) * cylinderAngleLift f₁ x)
      = (f₁ x).1.2
      have : (1 - (1 : ℝ)) * cylinderAngleLift f₀ x + (1 : ℝ) * cylinderAngleLift f₁ x
        = cylinderAngleLift f₁ x := by ring
      rw [this, exp_cylinderAngleLift]
  · intro y
    ext1; ext1
    · change (1 - (y : ℝ)) * (f₀ 0).1.1 + (y : ℝ) * (f₁ 0).1.1 = (f₀ 0).1.1
      rw [h0]; ring
    · change Circle.exp ((1 - (y : ℝ)) * cylinderAngleLift f₀ 0 + (y : ℝ) * cylinderAngleLift f₁ 0)
      = (f₀ 0).1.2
      have : (1 - (y : ℝ)) * cylinderAngleLift f₀ 0 + (y : ℝ) * cylinderAngleLift f₁ 0
        = cylinderAngleLift f₀ 0 := by
        rw [hstart]; ring
      rw [this, exp_cylinderAngleLift]
  · intro y
    ext1; ext1
    · change (1 - (y : ℝ)) * (f₀ 0).1.1 + (y : ℝ) * (f₁ 0).1.1 = (f₁ 0).1.1
      rw [h0]; ring
    · change Circle.exp ((1 - (y : ℝ)) * cylinderAngleLift f₀ 0 + (y : ℝ) * cylinderAngleLift f₁ 0)
      = (f₁ 0).1.2
      have : (1 - (y : ℝ)) * cylinderAngleLift f₀ 0 + (y : ℝ) * cylinderAngleLift f₁ 0
        = cylinderAngleLift f₁ 0 := by
        rw [hstart]; ring
      rw [this, exp_cylinderAngleLift]
  · intro y
    ext1; ext1
    · change (1 - (y : ℝ)) * (f₀ 1).1.1 + (y : ℝ) * (f₁ 1).1.1 = (f₀ 1).1.1
      rw [h1]; ring
    · change Circle.exp ((1 - (y : ℝ)) * cylinderAngleLift f₀ 1 + (y : ℝ) * cylinderAngleLift f₁ 1)
      = (f₀ 1).1.2
      have : (1 - (y : ℝ)) * cylinderAngleLift f₀ 1 + (y : ℝ) * cylinderAngleLift f₁ 1
        = cylinderAngleLift f₀ 1 := by
        rw [hend]; ring
      rw [this, exp_cylinderAngleLift]
  · intro y
    ext1; ext1
    · change (1 - (y : ℝ)) * (f₀ 1).1.1 + (y : ℝ) * (f₁ 1).1.1 = (f₁ 1).1.1
      rw [h1]; ring
    · change Circle.exp ((1 - (y : ℝ)) * cylinderAngleLift f₀ 1 + (y : ℝ) * cylinderAngleLift f₁ 1)
      = (f₁ 1).1.2
      have : (1 - (y : ℝ)) * cylinderAngleLift f₀ 1 + (y : ℝ) * cylinderAngleLift f₁ 1
        = cylinderAngleLift f₁ 1 := by
        rw [hend]; ring
      rw [this, exp_cylinderAngleLift]

/-- Two curves on the cylinder with the same endpoints are homotopic if and only if they have the
same winding number.
Graph Minors VI, Section 5 (page 127): "and is zero if and only if $P_1$ is homotopic to $P_2$." -/
theorem curvesHomotopic_iff_windingNumber_eq {f₀ f₁ : Curve ClosedCylinder}
    (h0 : f₀ 0 = f₁ 0) (h1 : f₀ 1 = f₁ 1) :
    CurvesHomotopic f₀ f₁ ↔ windingNumber f₀ = windingNumber f₁ :=
  ⟨windingNumber_eq_of_homotopic, curvesHomotopic_of_windingNumber_eq h0 h1⟩

end GraphMinor.Surface
