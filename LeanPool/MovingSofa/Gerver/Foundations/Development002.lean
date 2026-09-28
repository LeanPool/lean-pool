/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Canonical.Foundations.Development001
public import LeanPool.MovingSofa.Infrastructure.Curves.Foundations.Development001
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Gerver.Foundations.Development001
/-!
# Moving sofa: related mathematical developments

* `Gerver.Motion`.
* `Gerver.PaperPath`.
* `Gerver.PaperSet`.
* `Gerver.Parameters`.
* `Gerver.ParameterDictionary`.
* `Gerver.Partition`.
* `Gerver.ReversePhysicalDomain`.
* `Gerver.DirectRegularity`.
* `Gerver.LiteralSets`.
* `Gerver.LiteralConnected`.
* `Gerver.ParameterIdentification`.
* `Gerver.Contacts`.
* `Gerver.Niche.Roof`.
* `Gerver.ODEs`.
* `Gerver.OuterContacts`.
* `Gerver.StageRegularity`.
* `Gerver.Area.Grid`.
* `Gerver.Niche.RoofProperties`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-
MIT License

Copyright (c) 2026 Dawid Trela

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/


/-! Adapted from GerverSofaLean v1.1.0, F07UpstreamMotion (MIT). -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped unitInterval ENNReal

namespace MovingSofa

open GerverSofa.PartF

/-- The certified continuous rigid motion carrying Gerver’s sofa through the hallway. -/
def gerversSofaMotion : I → Rigid := EuclideanMotion.motion

theorem isMovingSofa_gerversSofa_motion : IsMovingSofa gerversSofa gerversSofaMotion := by
  apply (ProjectAdapter.isMovingSofa_iff_model _ _).2
  rw [ProjectAdapter.gerversSofa_eq_certified]
  exact EuclideanMotion.concrete_movingSofa

theorem isMovingSofa_gerversSofa : ∃ m, IsMovingSofa gerversSofa m :=
  ⟨gerversSofaMotion, isMovingSofa_gerversSofa_motion⟩

theorem volume_gerversSofa_le_sofaConstant : volume gerversSofa ≤ sofaConstant := by
  unfold sofaConstant
  exact le_iSup_of_le gerversSofa (le_iSup_of_le isMovingSofa_gerversSofa le_rfl)

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
# The paper's Gerver path and the vendor coordinate transport

`paperGerverPath` is the certified direct five-phase Gerver path read through the vendor
coordinate identification `GerverSofa.PartF.Coordinates.toPlane`.  This file records the
transport lemmas for that identification (derivatives, smoothness, continuity) and the
frame readers that express the moving frame `normalVector`/`tangentVector` in the same
coordinates.

The frame readers live here rather than in `MovingSofa/Geometry/Basic.lean` because their
statements mention `toPlane`, which `Geometry/Basic.lean` does not import; this is the
lowest module that sees both the vendor coordinates and `MovingSofa.frame`.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace MovingSofa

/-- The certified direct five-phase Gerver path, taking the earlier branch at each switch. -/
def paperGerverPath (t : ℝ) : Point :=
  GerverSofa.PartF.Coordinates.toPlane (GerverSofa.Romik.path GerverSofa.PartB.params t)

theorem canonical_path_rotation_eq_paper (t : ℝ) (ht : t ∈ Set.Icc 0 (Real.pi / 2)) :
    rotationMap (t : Real.Angle) (GerversSofa.p t) = paperGerverPath t :=
  GerverSofa.PartF.ProjectAdapter.integral_rotation_to_full t ht

section Transport

open GerverSofa.Romik GerverSofa.PartF.Coordinates

/-! ### Transport along the coordinate identification -/

/-- The coordinate identification `toPlane` is a continuous linear map, so it transports
derivatives of plane-valued curves. -/
theorem hasDerivAt_toPlane {q : ℝ → GerverSofa.Point} {q' : GerverSofa.Point} {t : ℝ}
    (hq : HasDerivAt q q' t) : HasDerivAt (fun s => toPlane (q s)) (toPlane q') t := by
  obtain ⟨L, hL⟩ : ∃ L : GerverSofa.Point →L[ℝ] Point, ⇑L = toPlane :=
    ⟨{ toLinearMap := linearEquiv.toLinearMap, cont := continuous_toPlane }, rfl⟩
  rw [← hL]
  simpa [Function.comp_def] using L.hasFDerivAt.comp_hasDerivAt t hq

/-- The coordinate identification `toPlane` preserves smoothness of plane-valued curves. -/
theorem contDiff_toPlane {q : ℝ → GerverSofa.Point} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ fun t => toPlane (q t) := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · exact hq.fst
  · exact hq.snd

/-! ### Frame readers -/

/-- The angular frame normal is the coordinate image of the standard trigonometric pair. -/
theorem normalVector_coe_eq_toPlane (t : ℝ) :
    normalVector (t : Real.Angle) = toPlane (Real.cos t, Real.sin t) := rfl

/-- The angular frame tangent is the coordinate image of the rotated trigonometric pair. -/
theorem tangentVector_coe_eq_toPlane (t : ℝ) :
    tangentVector (t : Real.Angle) = toPlane (-Real.sin t, Real.cos t) := rfl

/-- The normal component of a body-frame vector rotated by `t` is its first coordinate. -/
theorem inner_toPlane_rot_normalVector (t : ℝ) (z : GerverSofa.Point) :
    inner ℝ (toPlane (rot t z)) (normalVector (t : Real.Angle)) = z.1 := by
  have h := Real.sin_sq_add_cos_sq t
  simp only [normalVector, MovingSofa.frame, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_two, rot, toPlane_zero_coord, toPlane_one_coord, conj_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one, Real.Angle.cos_coe, Real.Angle.sin_coe]
  linear_combination z.1 * h

/-- The tangential component of a body-frame vector rotated by `t` is its second
coordinate. -/
theorem inner_toPlane_rot_tangentVector (t : ℝ) (z : GerverSofa.Point) :
    inner ℝ (toPlane (rot t z)) (tangentVector (t : Real.Angle)) = z.2 := by
  have h := Real.sin_sq_add_cos_sq t
  simp only [tangentVector, MovingSofa.frame, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_two, rot, toPlane_zero_coord, toPlane_one_coord, conj_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one, Real.Angle.cos_coe, Real.Angle.sin_coe]
  linear_combination z.2 * h

/-- The normal frame component of a plane point is the vendor scalar product of its
coordinate pair with the vendor normal `u`. -/
theorem inner_normalVector_eq_dot (q : Point) (s : ℝ) :
    inner ℝ q (normalVector (s : Real.Angle)) =
      GerverSofa.dot (fromPlane q) (GerverSofa.u s) := by
  simp only [normalVector, MovingSofa.frame, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.Angle.cos_coe,
    Real.Angle.sin_coe, GerverSofa.dot, GerverSofa.u, fromPlane]
  ring

/-- The tangent frame component of a plane point is the vendor scalar product of its
coordinate pair with the vendor tangent `v`. -/
theorem inner_tangentVector_eq_dot (q : Point) (s : ℝ) :
    inner ℝ q (tangentVector (s : Real.Angle)) =
      GerverSofa.dot (fromPlane q) (GerverSofa.v s) := by
  simp only [tangentVector, MovingSofa.frame, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.Angle.cos_coe,
    Real.Angle.sin_coe, GerverSofa.dot, GerverSofa.v, fromPlane]
  ring

/-- The angular frame normal is a smooth function of the angle. -/
theorem contDiff_normalVector : ContDiff ℝ ∞ fun t : ℝ => normalVector (t : Real.Angle) := by
  simp only [normalVector_coe_eq_toPlane]
  exact contDiff_toPlane (Real.contDiff_cos.prodMk Real.contDiff_sin)

/-- The angular frame tangent is a smooth function of the angle. -/
theorem contDiff_tangentVector :
    ContDiff ℝ ∞ fun t : ℝ => tangentVector (t : Real.Angle) := by
  simp only [tangentVector_coe_eq_toPlane]
  exact contDiff_toPlane (Real.contDiff_sin.neg.prodMk Real.contDiff_cos)

/-! ### The paper path as a transported direct path

The hypothesis `ContDiff ℝ 1 (path GerverSofa.PartB.params)` in the lemmas below is the
first conjunct of `MovingSofa.gerver_direct_path_regularity`, which lives in a later
module; passing it as a hypothesis keeps this file free of that dependency. -/

/-- The paper path is the coordinate image of the certified direct path. -/
theorem paperGerverPath_eq_toPlane :
    paperGerverPath = fun t => toPlane (path GerverSofa.PartB.params t) := rfl

/-- The paper path differentiates by transporting the derivative of the direct path. -/
theorem hasDerivAt_paperGerverPath (hC1 : ContDiff ℝ 1 (path GerverSofa.PartB.params))
    (t : ℝ) :
    HasDerivAt paperGerverPath (toPlane (deriv (path GerverSofa.PartB.params) t)) t :=
  hasDerivAt_toPlane ((hC1.differentiable one_ne_zero t).hasDerivAt)

/-- The derivative of the paper path is the transported derivative of the direct path. -/
theorem deriv_paperGerverPath (hC1 : ContDiff ℝ 1 (path GerverSofa.PartB.params)) (t : ℝ) :
    deriv paperGerverPath t = toPlane (deriv (path GerverSofa.PartB.params) t) :=
  (hasDerivAt_paperGerverPath hC1 t).deriv

/-- The paper path is continuous. -/
theorem continuous_paperGerverPath (hC1 : ContDiff ℝ 1 (path GerverSofa.PartB.params)) :
    Continuous paperGerverPath := by
  rw [paperGerverPath_eq_toPlane]
  exact continuous_toPlane.comp hC1.continuous

/-- The paper path is continuously differentiable. -/
theorem continuous_deriv_paperGerverPath
    (hC1 : ContDiff ℝ 1 (path GerverSofa.PartB.params)) :
    Continuous (deriv paperGerverPath) := by
  rw [funext (deriv_paperGerverPath hC1)]
  exact continuous_toPlane.comp (hC1.continuous_deriv le_rfl)

end Transport

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
# Gerver / Paper Set
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Gerver's paper-frame set, cut out by the explicit path of rotated hallways. -/
def paperGerverSofa : Set Point :=
  (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 ∩
    ⋂ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      (fun p ↦ rotationMap (t : Real.Angle) p + paperGerverPath t) '' hallway

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
# Gerver / Parameters
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The two Gerver switching angles and the right/left distinguished angles. -/
def paperGerverConstants : (ℝ × ℝ) × (ℝ × ℝ) :=
  ((GerversSofa.φ, GerversSofa.θ), (GerversSofa.φ, Real.pi / 2 - GerversSofa.φ))

/-- The six endpoints of the five Gerver stages. -/
def gerverStageTimes : Fin 6 → ℝ :=
  ![0, GerversSofa.φ, GerversSofa.θ, Real.pi / 2 - GerversSofa.θ,
    Real.pi / 2 - GerversSofa.φ, Real.pi / 2]

/-- The five closed stage intervals in their source order. -/
def gerverStageIntervals (i : Fin 5) : Set ℝ :=
  Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ)

/-- The exact direct 22-equation Gerver system, with the certified phase-map convention. -/
def gerverDirectEquations (p : GerverSofa.Romik.Params) : Prop :=
  GerverSofa.Romik.Equations p

/-- The exact closed rational box for the direct Gerver parameters. -/
def gerverDirectBox : Set GerverSofa.Romik.Params := GerverSofa.Romik.box

/-- The exact box bounds the second-stage linear coefficient `b₁` from below by `-53/100`. -/
theorem gerverDirectBox_b1_lower_bound {p : GerverSofa.Romik.Params} (hp : p ∈ gerverDirectBox) :
    (-53 : ℝ) / 100 ≤ p.b1 := by
  dsimp only [gerverDirectBox, GerverSofa.Romik.box, GerverSofa.qR, Set.mem_ofPred_eq] at hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, hb1, -⟩ := hp
  exact le_trans (by norm_num) hb1

/-- The exact box bounds the fourth-stage linear coefficient `d₁` from above by `33/25`. -/
theorem gerverDirectBox_d1_upper_bound {p : GerverSofa.Romik.Params} (hp : p ∈ gerverDirectBox) :
    p.d1 ≤ (33 : ℝ) / 25 := by
  dsimp only [gerverDirectBox, GerverSofa.Romik.box, GerverSofa.qR, Set.mem_ofPred_eq] at hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, -, hd1, -⟩ := hp
  exact le_trans hd1 (by norm_num)

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
# Gerver / Parameter Dictionary
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Bundle the forward and reverse dictionaries between reduced and full Romik parameters. -/
def gerverParameterDictionary :
    (GerverSofa.Reduced.Params → GerverSofa.Romik.Params) ×
      (GerverSofa.Romik.Params → GerverSofa.Reduced.Params) :=
  (GerverSofa.PartF.Phases.dictionary, GerverSofa.PartF.Phases.undictionary)

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
# Gerver / Partition
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The ten half-open Gerver phase intervals, indexed from zero. -/
def gerverPhaseIntervals (j : Fin 10) : Set ℝ :=
  let lower (i : Fin 5) := Set.Ico (gerverStageTimes i.castSucc) (gerverStageTimes i.succ)
  Fin.addCases (motive := fun _ ↦ Set ℝ) lower
    (fun i ↦ (fun t ↦ Real.pi - t) '' lower i.rev) j

/-- The ten Gerver phase intervals, written out as explicit half-open real intervals. -/
theorem gerverPhaseIntervals_explicit (j : Fin 10) :
    gerverPhaseIntervals j =
      ![Set.Ico 0 GerversSofa.φ,
        Set.Ico GerversSofa.φ GerversSofa.θ,
        Set.Ico GerversSofa.θ (Real.pi / 2 - GerversSofa.θ),
        Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ),
        Set.Ico (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2),
        Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.φ),
        Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ),
        Set.Ioc (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.θ),
        Set.Ioc (Real.pi - GerversSofa.θ) (Real.pi - GerversSofa.φ),
        Set.Ioc (Real.pi - GerversSofa.φ) Real.pi] j := by
  fin_cases j
  all_goals simp [gerverPhaseIntervals, gerverStageTimes, Fin.addCases, Fin.rev]
  all_goals congr 1 <;> ring

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
# Gerver / Reverse Physical Domain
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem gerver_reverse_physical_domain (p : GerverSofa.Romik.Params)
    (hp : p ∈ gerverDirectBox) :
    0 < (gerverParameterDictionary.2 p).phi ∧
    (gerverParameterDictionary.2 p).phi < (gerverParameterDictionary.2 p).theta ∧
    (gerverParameterDictionary.2 p).theta < Real.pi / 4 ∧
    0 < (gerverParameterDictionary.2 p).a ∧ 0 < (gerverParameterDictionary.2 p).b ∧
    (39 : ℝ) / 1000 ≤ (gerverParameterDictionary.2 p).phi ∧
    (gerverParameterDictionary.2 p).phi ≤ (40 : ℝ) / 1000 := by
  dsimp [gerverDirectBox, GerverSofa.Romik.box, GerverSofa.qR] at hp
  rcases hp with ⟨_, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    hb1lo, hb1hi, hb2lo, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    hphilo, hphihi, hthetalo, hthetahi⟩
  norm_num at hb1lo hb1hi hb2lo hphilo hphihi hthetalo hthetahi
  have hphiLo : (39 : ℝ) / 1000 ≤ p.phi := by linarith only [hphilo]
  have hphiHi : p.phi ≤ (1 : ℝ) / 25 := by linarith only [hphihi]
  have hphiPos : (0 : ℝ) < p.phi := by linarith only [hphiLo]
  have hthetaLo : (3 : ℝ) / 5 ≤ p.theta := by linarith only [hthetalo]
  have hthetaHi : p.theta ≤ (7 : ℝ) / 10 := by linarith only [hthetahi]
  have hb1Lo : (-66 : ℝ) / 125 ≤ p.b1 := by linarith only [hb1lo]
  have hb1Hi : p.b1 ≤ (-527 : ℝ) / 1000 := by linarith only [hb1hi]
  have hb2Lo : (23 : ℝ) / 25 ≤ p.b2 := by linarith only [hb2lo]
  have hAPos : (0 : ℝ) < p.phi - 1 - 2 * p.b1 := by linarith only [hphiLo, hb1Hi]
  have hBPos :
      (0 : ℝ) <
        p.b2 + 1 / 2 - (1 + (p.phi - 1 - 2 * p.b1)) * p.phi / 2 + p.phi ^ 2 / 4 := by
    have hprod : (0 : ℝ) ≤ (p.b1 + 66 / 125) * p.phi :=
      mul_nonneg (by linarith only [hb1Lo]) hphiPos.le
    have hsq : (0 : ℝ) ≤ p.phi * (1 / 25 - p.phi) :=
      mul_nonneg hphiPos.le (by linarith only [hphiHi])
    nlinarith only [hb2Lo, hprod, hsq, hphiPos, hphiHi]
  refine ⟨hphiPos, show p.phi < p.theta from ?_,
    show p.theta < Real.pi / 4 from ?_, hAPos, hBPos, hphiLo,
    show p.phi ≤ (40 : ℝ) / 1000 from ?_⟩
  · linarith only [hphiHi, hthetaLo]
  · nlinarith only [hthetaHi, Real.pi_gt_three]
  · linarith only [hphiHi]

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
# Matching and `C¹` regularity of the direct Gerver path

The vendor library assembles the Gerver path `GerverSofa.Romik.path` from five smooth
branches `path1, …, path5` switched at `φ < θ < π/2 - θ < π/2 - φ`.  This file supplies the
differential interface for those branches — each `pathᵢ` has derivative
`rot t (alphaBetaᵢ p t)` — and deduces from the direct equations that values and derivatives
agree at all four switches, hence that `path p` is continuously differentiable with
`path p 0 = 0`.

It also records, for each stage, that the glued path agrees with its analytic branch on the
*closed* stage interval and that `deriv (path p)` is the corresponding `rot t (alphaBetaᵢ p t)`
there, endpoints included.
-/

/-! ### Differential interface for the five direct branches -/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace GerverSofa.Romik

/-- Rotating a differentiable body-frame curve and translating it differentiates by the
product rule, contributing the infinitesimal rotation `(z₁, z₂) ↦ (-z₂, z₁)`. -/
theorem hasDerivAt_addK_rot {z₁ z₂ : ℝ → ℝ} {z₁' z₂' k₁ k₂ t : ℝ}
    (hz₁ : HasDerivAt z₁ z₁' t) (hz₂ : HasDerivAt z₂ z₂' t) :
    HasDerivAt (fun s => addK (rot s (z₁ s, z₂ s)) k₁ k₂)
      (rot t (z₁' - z₂ t, z₂' + z₁ t)) t := by
  apply HasDerivAt.prodMk
  · change HasDerivAt (fun s => Real.cos s * z₁ s - Real.sin s * z₂ s + k₁)
      (Real.cos t * (z₁' - z₂ t) - Real.sin t * (z₂' + z₁ t)) t
    exact ((((Real.hasDerivAt_cos t).fun_mul hz₁).fun_sub
        ((Real.hasDerivAt_sin t).fun_mul hz₂)).fun_add
      (hasDerivAt_const t k₁)).congr_deriv (by ring)
  · change HasDerivAt (fun s => Real.sin s * z₁ s + Real.cos s * z₂ s + k₂)
      (Real.sin t * (z₁' - z₂ t) + Real.cos t * (z₂' + z₁ t)) t
    exact ((((Real.hasDerivAt_sin t).fun_mul hz₁).fun_add
        ((Real.hasDerivAt_cos t).fun_mul hz₂)).fun_add
      (hasDerivAt_const t k₂)).congr_deriv (by ring)

private theorem hasDerivAt_mul_self (t : ℝ) : HasDerivAt (fun s : ℝ => s * s) (t + t) t := by
  simpa only [id_eq, one_mul, mul_one] using (hasDerivAt_id t).fun_mul (hasDerivAt_id t)

/-- The first direct branch has body-frame velocity `alphaBeta1`. -/
theorem hasDerivAt_path1 (p : Params) (t : ℝ) :
    HasDerivAt (path1 p) (rot t (alphaBeta1 p t)) t := by
  have hz₁ : HasDerivAt (fun s => p.a1 * Real.cos s + p.a2 * Real.sin s - 1)
      (-p.a1 * Real.sin t + p.a2 * Real.cos t) t :=
    ((((Real.hasDerivAt_cos t).const_mul p.a1).fun_add
      ((Real.hasDerivAt_sin t).const_mul p.a2)).fun_sub
      (hasDerivAt_const t (1 : ℝ))).congr_deriv (by ring)
  have hz₂ : HasDerivAt (fun s => -p.a2 * Real.cos s + p.a1 * Real.sin s - 1 / 2)
      (p.a2 * Real.sin t + p.a1 * Real.cos t) t :=
    ((((Real.hasDerivAt_cos t).const_mul (-p.a2)).fun_add
      ((Real.hasDerivAt_sin t).const_mul p.a1)).fun_sub
      (hasDerivAt_const t (1 / 2 : ℝ))).congr_deriv (by ring)
  refine (hasDerivAt_addK_rot (k₁ := p.k11) (k₂ := p.k12) hz₁ hz₂).congr_deriv ?_
  apply congrArg (rot t)
  ext <;> simp [alphaBeta1] <;> ring

/-- The second direct branch has body-frame velocity `alphaBeta2`. -/
theorem hasDerivAt_path2 (p : Params) (t : ℝ) :
    HasDerivAt (path2 p) (rot t (alphaBeta2 p t)) t := by
  have hz₁ : HasDerivAt (fun s => -(1 / 4 : ℝ) * s * s + p.b1 * s + p.b2)
      (-(1 / 2 : ℝ) * t + p.b1) t := by
    have h := (((hasDerivAt_mul_self t).const_mul (-(1 / 4 : ℝ))).fun_add
      ((hasDerivAt_id t).const_mul p.b1)).fun_add (hasDerivAt_const t p.b2)
    simpa only [id_eq, mul_assoc] using h.congr_deriv (by ring)
  have hz₂ : HasDerivAt (fun s => (1 / 2 : ℝ) * s - p.b1 - 1) (1 / 2 : ℝ) t :=
    ((((hasDerivAt_id t).const_mul (1 / 2 : ℝ)).fun_sub (hasDerivAt_const t p.b1)).fun_sub
      (hasDerivAt_const t (1 : ℝ))).congr_deriv (by simp)
  refine (hasDerivAt_addK_rot (k₁ := p.k21) (k₂ := p.k22) hz₁ hz₂).congr_deriv ?_
  apply congrArg (rot t)
  ext <;> simp [alphaBeta2] <;> ring

/-- The third direct branch has body-frame velocity `alphaBeta3`. -/
theorem hasDerivAt_path3 (p : Params) (t : ℝ) :
    HasDerivAt (path3 p) (rot t (alphaBeta3 p t)) t := by
  have hz₁ : HasDerivAt (fun s => p.c1 - s) (-1) t :=
    ((hasDerivAt_const t p.c1).fun_sub (hasDerivAt_id t)).congr_deriv (by simp)
  have hz₂ : HasDerivAt (fun s => p.c2 + s) 1 t :=
    ((hasDerivAt_const t p.c2).fun_add (hasDerivAt_id t)).congr_deriv (by simp)
  refine (hasDerivAt_addK_rot (k₁ := p.k31) (k₂ := p.k32) hz₁ hz₂).congr_deriv ?_
  apply congrArg (rot t)
  ext <;> simp [alphaBeta3] <;> ring

/-- The fourth direct branch has body-frame velocity `alphaBeta4`. -/
theorem hasDerivAt_path4 (p : Params) (t : ℝ) :
    HasDerivAt (path4 p) (rot t (alphaBeta4 p t)) t := by
  have hz₁ : HasDerivAt (fun s => -(1 / 2 : ℝ) * s + p.d1 - 1) (-(1 / 2 : ℝ)) t :=
    ((((hasDerivAt_id t).const_mul (-(1 / 2 : ℝ))).fun_add (hasDerivAt_const t p.d1)).fun_sub
      (hasDerivAt_const t (1 : ℝ))).congr_deriv (by simp)
  have hz₂ : HasDerivAt (fun s => -(1 / 4 : ℝ) * s * s + p.d1 * s + p.d2)
      (-(1 / 2 : ℝ) * t + p.d1) t := by
    have h := (((hasDerivAt_mul_self t).const_mul (-(1 / 4 : ℝ))).fun_add
      ((hasDerivAt_id t).const_mul p.d1)).fun_add (hasDerivAt_const t p.d2)
    simpa only [id_eq, mul_assoc] using h.congr_deriv (by ring)
  refine (hasDerivAt_addK_rot (k₁ := p.k41) (k₂ := p.k42) hz₁ hz₂).congr_deriv ?_
  apply congrArg (rot t)
  ext <;> simp [alphaBeta4] <;> ring

/-- The fifth direct branch has body-frame velocity `alphaBeta5`. -/
theorem hasDerivAt_path5 (p : Params) (t : ℝ) :
    HasDerivAt (path5 p) (rot t (alphaBeta5 p t)) t := by
  have hz₁ : HasDerivAt (fun s => p.e1 * Real.cos s + p.e2 * Real.sin s - 1 / 2)
      (-p.e1 * Real.sin t + p.e2 * Real.cos t) t :=
    ((((Real.hasDerivAt_cos t).const_mul p.e1).fun_add
      ((Real.hasDerivAt_sin t).const_mul p.e2)).fun_sub
      (hasDerivAt_const t (1 / 2 : ℝ))).congr_deriv (by ring)
  have hz₂ : HasDerivAt (fun s => -p.e2 * Real.cos s + p.e1 * Real.sin s - 1)
      (p.e2 * Real.sin t + p.e1 * Real.cos t) t :=
    ((((Real.hasDerivAt_cos t).const_mul (-p.e2)).fun_add
      ((Real.hasDerivAt_sin t).const_mul p.e1)).fun_sub
      (hasDerivAt_const t (1 : ℝ))).congr_deriv (by ring)
  refine (hasDerivAt_addK_rot (k₁ := p.k51) (k₂ := p.k52) hz₁ hz₂).congr_deriv ?_
  apply congrArg (rot t)
  ext <;> simp [alphaBeta5] <;> ring

/-- Continuity of the body-frame velocity field on each branch, transported to the world
frame by the rotation. -/
theorem continuous_rot_alphaBeta1 (p : Params) :
    Continuous fun t : ℝ => rot t (alphaBeta1 p t) := by
  unfold rot alphaBeta1; fun_prop

@[inherit_doc continuous_rot_alphaBeta1]
theorem continuous_rot_alphaBeta2 (p : Params) :
    Continuous fun t : ℝ => rot t (alphaBeta2 p t) := by
  unfold rot alphaBeta2; fun_prop

@[inherit_doc continuous_rot_alphaBeta1]
theorem continuous_rot_alphaBeta3 (p : Params) :
    Continuous fun t : ℝ => rot t (alphaBeta3 p t) := by
  unfold rot alphaBeta3; fun_prop

@[inherit_doc continuous_rot_alphaBeta1]
theorem continuous_rot_alphaBeta4 (p : Params) :
    Continuous fun t : ℝ => rot t (alphaBeta4 p t) := by
  unfold rot alphaBeta4; fun_prop

@[inherit_doc continuous_rot_alphaBeta1]
theorem continuous_rot_alphaBeta5 (p : Params) :
    Continuous fun t : ℝ => rot t (alphaBeta5 p t) := by
  unfold rot alphaBeta5; fun_prop

/-- Equation 32 of the direct system.  The remaining scalar consequences used here are
already extracted by the vendor in `GerverSofa/KernelOnly/EndpointSymmetry.lean`. -/
theorem k11_eq_one_sub_a1_of_equations {p : Params} (heq : Equations p) :
    p.k11 = 1 - p.a1 := by
  have h5 := congrFun heq (5 : Fin 22)
  simp [system] at h5
  linarith

/-! ### Reflection identities for the body-frame velocities

With `S (r, s) = (-s, -r)` the direct equations give `w₃(π/2 - t) = S w₃(t)`,
`w₄(π/2 - t) = S w₂(t)` and `w₅(π/2 - t) = S w₁(t)`. -/

/-- The middle branch velocity is anti-symmetric about `π/4`. -/
theorem alphaBeta3_pi_div_two_sub {p : Params} (heq : Equations p) (t : ℝ) :
    alphaBeta3 p (Real.pi / 2 - t) = (-(alphaBeta3 p t).2, -(alphaBeta3 p t).1) := by
  have hc2 := c2_eq_c1_sub_halfPi_of_equations heq
  simp only [alphaBeta3, Prod.mk.injEq]
  constructor <;> rw [hc2] <;> ring

/-- The fourth branch velocity reflects onto the second. -/
theorem alphaBeta4_pi_div_two_sub {p : Params} (heq : Equations p) (t : ℝ) :
    alphaBeta4 p (Real.pi / 2 - t) = (-(alphaBeta2 p t).2, -(alphaBeta2 p t).1) := by
  have hd1 := d1_eq_quarterPi_sub_b1_of_equations heq
  have hd2 := d2_eq_b2_add_quarterPi_correction_of_equations heq
  simp only [alphaBeta4, alphaBeta2, Prod.mk.injEq]
  constructor <;> simp only [hd1, hd2] <;> ring

/-- The fifth branch velocity reflects onto the first. -/
theorem alphaBeta5_pi_div_two_sub {p : Params} (heq : Equations p) (t : ℝ) :
    alphaBeta5 p (Real.pi / 2 - t) = (-(alphaBeta1 p t).2, -(alphaBeta1 p t).1) := by
  have he1 := e1_eq_a1_of_equations heq
  have he2 := e2_eq_neg_a2_of_equations heq
  simp only [alphaBeta5, alphaBeta1, Prod.mk.injEq, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]
  constructor <;> simp only [he1, he2] <;> ring

/-- Velocity matching at the third switch `π/2 - θ`, by reflecting the match at `θ`. -/
theorem alphaBeta34_eq {p : Params} (heq : Equations p) :
    alphaBeta3 p (Real.pi / 2 - p.theta) = alphaBeta4 p (Real.pi / 2 - p.theta) := by
  rw [alphaBeta3_pi_div_two_sub heq, alphaBeta4_pi_div_two_sub heq,
    GerverSofa.PartF.Phases.alphaBeta23_eq heq]

/-- Velocity matching at the fourth switch `π/2 - φ`, by reflecting the match at `φ`. -/
theorem alphaBeta45_eq {p : Params} (heq : Equations p) :
    alphaBeta4 p (Real.pi / 2 - p.phi) = alphaBeta5 p (Real.pi / 2 - p.phi) := by
  rw [alphaBeta4_pi_div_two_sub heq, alphaBeta5_pi_div_two_sub heq,
    GerverSofa.PartF.Phases.alphaBeta12_eq heq]

/-! ### Branch selection on the closed stages

Each stage interval is closed, so the two stages adjacent to a switch both contain it.  The
glued `path` picks the *earlier* branch there, and the certified value-matching equations
say that this is also the later branch's value. -/

/-- The glued direct path unfolds to the nested selection of its five analytic branches. -/
theorem path_eq_ite (p : Params) (t : ℝ) :
    path p t =
      if t ≤ p.phi then path1 p t
      else if t ≤ p.theta then path2 p t
      else if t ≤ Real.pi / 2 - p.theta then path3 p t
      else if t ≤ Real.pi / 2 - p.phi then path4 p t else path5 p t := rfl

/-- On the closed first stage `[0, φ]` the glued path is the first branch. -/
theorem path_eq_path1_of_mem_Icc (p : Params) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) p.phi) :
    path p s = path1 p s := by
  rw [path_eq_ite, ite_eq_left hs.2]

/-- On the closed second stage `[φ, θ]` the glued path is the second branch; at the left
endpoint this is the certified value match `match_path12_of_equations`. -/
theorem path_eq_path2_of_mem_Icc {p : Params} (heq : Equations p) {s : ℝ}
    (hs : s ∈ Set.Icc p.phi p.theta) : path p s = path2 p s := by
  rw [path_eq_ite]
  by_cases hc : s ≤ p.phi
  · obtain rfl : s = p.phi := le_antisymm hc hs.1
    rw [ite_eq_left hc]
    exact match_path12_of_equations heq
  · rw [ite_eq_right hc, ite_eq_left hs.2]

/-- On the closed third stage `[θ, π/2 - θ]` the glued path is the third branch; at the left
endpoint this is the certified value match `match_path23_of_equations`. -/
theorem path_eq_path3_of_mem_Icc {p : Params} (heq : Equations p) (hpt : p.phi < p.theta)
    {s : ℝ} (hs : s ∈ Set.Icc p.theta (Real.pi / 2 - p.theta)) : path p s = path3 p s := by
  have hb := hs.1
  rw [path_eq_ite, ite_eq_right (by linarith : ¬ s ≤ p.phi)]
  by_cases hc : s ≤ p.theta
  · obtain rfl : s = p.theta := le_antisymm hc hs.1
    rw [ite_eq_left hc]
    exact match_path23_of_equations heq
  · rw [ite_eq_right hc, ite_eq_left hs.2]

/-- On the closed fourth stage `[π/2 - θ, π/2 - φ]` the glued path is the fourth branch; at
the left endpoint this is the certified value match `match_path34_of_equations`. -/
theorem path_eq_path4_of_mem_Icc {p : Params} (heq : Equations p) (hpt : p.phi < p.theta)
    (hq : p.theta < Real.pi / 4) {s : ℝ}
    (hs : s ∈ Set.Icc (Real.pi / 2 - p.theta) (Real.pi / 2 - p.phi)) :
    path p s = path4 p s := by
  have hb := hs.1
  rw [path_eq_ite, ite_eq_right (by linarith : ¬ s ≤ p.phi),
    ite_eq_right (by linarith : ¬ s ≤ p.theta)]
  by_cases hc : s ≤ Real.pi / 2 - p.theta
  · obtain rfl : s = Real.pi / 2 - p.theta := le_antisymm hc hs.1
    rw [ite_eq_left hc]
    exact match_path34_of_equations heq
  · rw [ite_eq_right hc, ite_eq_left hs.2]

/-- On the closed fifth stage `[π/2 - φ, π/2]` the glued path is the fifth branch; at the
left endpoint this is the certified value match `match_path45_of_equations`. -/
theorem path_eq_path5_of_mem_Icc {p : Params} (heq : Equations p) (hpt : p.phi < p.theta)
    (hq : p.theta < Real.pi / 4) {s : ℝ}
    (hs : s ∈ Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2)) : path p s = path5 p s := by
  have hb := hs.1
  rw [path_eq_ite, ite_eq_right (by linarith : ¬ s ≤ p.phi),
    ite_eq_right (by linarith : ¬ s ≤ p.theta),
    ite_eq_right (by linarith : ¬ s ≤ Real.pi / 2 - p.theta)]
  by_cases hc : s ≤ Real.pi / 2 - p.phi
  · obtain rfl : s = Real.pi / 2 - p.phi := le_antisymm hc hs.1
    rw [ite_eq_left hc]
    exact match_path45_of_equations heq
  · rw [ite_eq_right hc]

/-! ### Smoothness of the branches and of their body-frame velocities -/

/-- The first analytic branch is smooth on all of `ℝ`. -/
theorem contDiff_path1 (p : Params) : ContDiff ℝ ∞ (path1 p) := by
  unfold path1 addK rot; fun_prop

@[inherit_doc contDiff_path1]
theorem contDiff_path2 (p : Params) : ContDiff ℝ ∞ (path2 p) := by
  unfold path2 addK rot; fun_prop

@[inherit_doc contDiff_path1]
theorem contDiff_path3 (p : Params) : ContDiff ℝ ∞ (path3 p) := by
  unfold path3 addK rot; fun_prop

@[inherit_doc contDiff_path1]
theorem contDiff_path4 (p : Params) : ContDiff ℝ ∞ (path4 p) := by
  unfold path4 addK rot; fun_prop

@[inherit_doc contDiff_path1]
theorem contDiff_path5 (p : Params) : ContDiff ℝ ∞ (path5 p) := by
  unfold path5 addK rot; fun_prop

/-- The first body-frame velocity pair is smooth on all of `ℝ`. -/
theorem contDiff_alphaBeta1 (p : Params) : ContDiff ℝ ∞ (alphaBeta1 p) := by
  unfold alphaBeta1; fun_prop

@[inherit_doc contDiff_alphaBeta1]
theorem contDiff_alphaBeta2 (p : Params) : ContDiff ℝ ∞ (alphaBeta2 p) := by
  unfold alphaBeta2; fun_prop

@[inherit_doc contDiff_alphaBeta1]
theorem contDiff_alphaBeta3 (p : Params) : ContDiff ℝ ∞ (alphaBeta3 p) := by
  unfold alphaBeta3; fun_prop

@[inherit_doc contDiff_alphaBeta1]
theorem contDiff_alphaBeta4 (p : Params) : ContDiff ℝ ∞ (alphaBeta4 p) := by
  unfold alphaBeta4; fun_prop

@[inherit_doc contDiff_alphaBeta1]
theorem contDiff_alphaBeta5 (p : Params) : ContDiff ℝ ∞ (alphaBeta5 p) := by
  unfold alphaBeta5; fun_prop

/-! ### The stage derivatives, endpoints included

A nondegenerate closed interval has a unique tangent direction at each of its points,
including its endpoints, so a `C¹` function agreeing there with a differentiable curve
already has that curve's derivative at every point of the interval. -/

/-- If the `C¹` glued path agrees on a nondegenerate closed interval with a curve whose
derivative is `rot s (W s)`, then that is its derivative everywhere on the interval,
endpoints included. -/
theorem deriv_path_of_eqOn_Icc {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    {X W : ℝ → Point} {a b t : ℝ} (hab : a < b)
    (hX : ∀ s, HasDerivAt X (rot s (W s)) s) (hXe : ∀ s ∈ Set.Icc a b, path p s = X s)
    (ht : t ∈ Set.Icc a b) : deriv (path p) t = rot t (W t) := by
  have h1 : HasDerivWithinAt (path p) (deriv (path p) t) (Set.Icc a b) t :=
    ((hC1.differentiable one_ne_zero t).hasDerivAt).hasDerivWithinAt
  have h2 : HasDerivWithinAt (path p) (rot t (W t)) (Set.Icc a b) t :=
    ((hX t).hasDerivWithinAt).congr hXe (hXe t ht)
  exact (uniqueDiffOn_Icc hab t ht).eq_deriv _ h1 h2

/-- On the closed first stage the glued path has body-frame velocity `alphaBeta1`. -/
theorem deriv_path_eq_rot_alphaBeta1 {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    (hphi : 0 < p.phi) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) p.phi) :
    deriv (path p) t = rot t (alphaBeta1 p t) :=
  deriv_path_of_eqOn_Icc hC1 hphi (hasDerivAt_path1 p)
    (fun _ hs => path_eq_path1_of_mem_Icc p hs) ht

/-- On the closed second stage the glued path has body-frame velocity `alphaBeta2`. -/
theorem deriv_path_eq_rot_alphaBeta2 {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    (heq : Equations p) (hpt : p.phi < p.theta) {t : ℝ} (ht : t ∈ Set.Icc p.phi p.theta) :
    deriv (path p) t = rot t (alphaBeta2 p t) :=
  deriv_path_of_eqOn_Icc hC1 hpt (hasDerivAt_path2 p)
    (fun _ hs => path_eq_path2_of_mem_Icc heq hs) ht

/-- On the closed third stage the glued path has body-frame velocity `alphaBeta3`. -/
theorem deriv_path_eq_rot_alphaBeta3 {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    (heq : Equations p) (hpt : p.phi < p.theta) (hq : p.theta < Real.pi / 4) {t : ℝ}
    (ht : t ∈ Set.Icc p.theta (Real.pi / 2 - p.theta)) :
    deriv (path p) t = rot t (alphaBeta3 p t) :=
  deriv_path_of_eqOn_Icc hC1 (by linarith) (hasDerivAt_path3 p)
    (fun _ hs => path_eq_path3_of_mem_Icc heq hpt hs) ht

/-- On the closed fourth stage the glued path has body-frame velocity `alphaBeta4`. -/
theorem deriv_path_eq_rot_alphaBeta4 {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    (heq : Equations p) (hpt : p.phi < p.theta) (hq : p.theta < Real.pi / 4) {t : ℝ}
    (ht : t ∈ Set.Icc (Real.pi / 2 - p.theta) (Real.pi / 2 - p.phi)) :
    deriv (path p) t = rot t (alphaBeta4 p t) :=
  deriv_path_of_eqOn_Icc hC1 (by linarith) (hasDerivAt_path4 p)
    (fun _ hs => path_eq_path4_of_mem_Icc heq hpt hq hs) ht

/-- On the closed fifth stage the glued path has body-frame velocity `alphaBeta5`. -/
theorem deriv_path_eq_rot_alphaBeta5 {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    (heq : Equations p) (hphi : 0 < p.phi) (hpt : p.phi < p.theta)
    (hq : p.theta < Real.pi / 4) {t : ℝ}
    (ht : t ∈ Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2)) :
    deriv (path p) t = rot t (alphaBeta5 p t) :=
  deriv_path_of_eqOn_Icc hC1 (by linarith) (hasDerivAt_path5 p)
    (fun _ hs => path_eq_path5_of_mem_Icc heq hpt hq hs) ht

end GerverSofa.Romik

namespace MovingSofa

open GerverSofa.Romik

/-- The five explicit Romik path branches for a parameter tuple. -/
def gerverDirectBranches (p : GerverSofa.Romik.Params) : Fin 5 → ℝ → GerverSofa.Point :=
  ![GerverSofa.Romik.path1 p, GerverSofa.Romik.path2 p, GerverSofa.Romik.path3 p,
    GerverSofa.Romik.path4 p, GerverSofa.Romik.path5 p]

/-- The four switching times separating the explicit Romik path branches. -/
def gerverDirectSwitches (p : GerverSofa.Romik.Params) : Fin 4 → ℝ :=
  ![p.phi, p.theta, Real.pi / 2 - p.theta, Real.pi / 2 - p.phi]

theorem gerver_direct_path_regularity (p : GerverSofa.Romik.Params)
    (hp : p ∈ gerverDirectBox) (heq : gerverDirectEquations p) :
    ContDiff ℝ 1 (GerverSofa.Romik.path p) ∧ GerverSofa.Romik.path p 0 = 0 ∧
    ∀ i : Fin 4,
      gerverDirectBranches p i.castSucc (gerverDirectSwitches p i) =
        gerverDirectBranches p i.succ (gerverDirectSwitches p i) ∧
      deriv (gerverDirectBranches p i.castSucc) (gerverDirectSwitches p i) =
        deriv (gerverDirectBranches p i.succ) (gerverDirectSwitches p i) := by
  -- The switching angles are strictly ordered by the reverse-domain bounds.
  have hdom := gerver_reverse_physical_domain p hp
  have hphi_pos : 0 < p.phi := hdom.1
  have hphi_theta : p.phi < p.theta := hdom.2.1
  have htheta_quarter : p.theta < Real.pi / 4 := hdom.2.2.1
  have htheta_eta : p.theta < Real.pi / 2 - p.theta := by linarith
  have heta_tau : Real.pi / 2 - p.theta < Real.pi / 2 - p.phi := by linarith
  -- The body-frame velocity matches at the four switches.
  have hw12 := GerverSofa.PartF.Phases.alphaBeta12_eq (p := p) heq
  have hw23 := GerverSofa.PartF.Phases.alphaBeta23_eq (p := p) heq
  have hw34 := alphaBeta34_eq (p := p) heq
  have hw45 := alphaBeta45_eq (p := p) heq
  -- The four positional matches, from the certified vendor extraction.
  have hv12 := match_path12_of_equations (p := p) heq
  have hv23 := match_path23_of_equations (p := p) heq
  have hv34 := match_path34_of_equations (p := p) heq
  have hv45 := match_path45_of_equations (p := p) heq
  -- Glue the branches from the last switch backwards.
  have hD45 : ∀ t : ℝ, HasDerivAt
      (fun s => if s ≤ Real.pi / 2 - p.phi then path4 p s else path5 p s)
      (if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
        else rot t (alphaBeta5 p t)) t :=
    hasDerivAt_if_le (hasDerivAt_path4 p) (hasDerivAt_path5 p) hv45
      (congrArg (rot (Real.pi / 2 - p.phi)) hw45)
  have hC45 : Continuous fun t : ℝ =>
      if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t) else rot t (alphaBeta5 p t) :=
    (continuous_rot_alphaBeta4 p).if_le (continuous_rot_alphaBeta5 p)
      continuous_id continuous_const (by
        intro t ht
        subst ht
        exact congrArg (rot (Real.pi / 2 - p.phi)) hw45)
  have hD345 : ∀ t : ℝ, HasDerivAt
      (fun s => if s ≤ Real.pi / 2 - p.theta then path3 p s
        else if s ≤ Real.pi / 2 - p.phi then path4 p s else path5 p s)
      (if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
        else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
        else rot t (alphaBeta5 p t)) t :=
    hasDerivAt_if_le (hasDerivAt_path3 p) hD45
      (by rw [ite_eq_left heta_tau.le]; exact hv34)
      (by rw [ite_eq_left heta_tau.le]
          exact congrArg (rot (Real.pi / 2 - p.theta)) hw34)
  have hC345 : Continuous fun t : ℝ =>
      if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
      else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
      else rot t (alphaBeta5 p t) :=
    (continuous_rot_alphaBeta3 p).if_le hC45 continuous_id continuous_const (by
      intro t ht
      subst ht
      rw [ite_eq_left heta_tau.le]
      exact congrArg (rot (Real.pi / 2 - p.theta)) hw34)
  have hD2345 : ∀ t : ℝ, HasDerivAt
      (fun s => if s ≤ p.theta then path2 p s
        else if s ≤ Real.pi / 2 - p.theta then path3 p s
        else if s ≤ Real.pi / 2 - p.phi then path4 p s else path5 p s)
      (if t ≤ p.theta then rot t (alphaBeta2 p t)
        else if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
        else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
        else rot t (alphaBeta5 p t)) t :=
    hasDerivAt_if_le (hasDerivAt_path2 p) hD345
      (by rw [ite_eq_left htheta_eta.le]; exact hv23)
      (by rw [ite_eq_left htheta_eta.le]
          exact congrArg (rot p.theta) hw23)
  have hC2345 : Continuous fun t : ℝ =>
      if t ≤ p.theta then rot t (alphaBeta2 p t)
      else if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
      else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
      else rot t (alphaBeta5 p t) :=
    (continuous_rot_alphaBeta2 p).if_le hC345 continuous_id continuous_const (by
      intro t ht
      subst ht
      rw [ite_eq_left htheta_eta.le]
      exact congrArg (rot p.theta) hw23)
  have hDpath : ∀ t : ℝ, HasDerivAt (path p)
      (if t ≤ p.phi then rot t (alphaBeta1 p t)
        else if t ≤ p.theta then rot t (alphaBeta2 p t)
        else if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
        else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
        else rot t (alphaBeta5 p t)) t :=
    hasDerivAt_if_le (hasDerivAt_path1 p) hD2345
      (by rw [ite_eq_left hphi_theta.le]; exact hv12)
      (by rw [ite_eq_left hphi_theta.le]
          exact congrArg (rot p.phi) hw12)
  have hCpath : Continuous fun t : ℝ =>
      if t ≤ p.phi then rot t (alphaBeta1 p t)
      else if t ≤ p.theta then rot t (alphaBeta2 p t)
      else if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
      else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
      else rot t (alphaBeta5 p t) :=
    (continuous_rot_alphaBeta1 p).if_le hC2345 continuous_id continuous_const (by
      intro t ht
      subst ht
      rw [ite_eq_left hphi_theta.le]
      exact congrArg (rot p.phi) hw12)
  -- The four derivative matches.
  have hdv12 : deriv (path1 p) p.phi = deriv (path2 p) p.phi := by
    rw [(hasDerivAt_path1 p p.phi).deriv, (hasDerivAt_path2 p p.phi).deriv, hw12]
  have hdv23 : deriv (path2 p) p.theta = deriv (path3 p) p.theta := by
    rw [(hasDerivAt_path2 p p.theta).deriv, (hasDerivAt_path3 p p.theta).deriv, hw23]
  have hdv34 : deriv (path3 p) (Real.pi / 2 - p.theta) =
      deriv (path4 p) (Real.pi / 2 - p.theta) := by
    rw [(hasDerivAt_path3 p _).deriv, (hasDerivAt_path4 p _).deriv, hw34]
  have hdv45 : deriv (path4 p) (Real.pi / 2 - p.phi) =
      deriv (path5 p) (Real.pi / 2 - p.phi) := by
    rw [(hasDerivAt_path4 p _).deriv, (hasDerivAt_path5 p _).deriv, hw45]
  refine ⟨contDiff_one_of_hasDerivAt hDpath hCpath, ?_, ?_⟩
  · -- `0 < φ` selects the first branch, and the normalizations make it vanish at `0`.
    have hk11 := k11_eq_one_sub_a1_of_equations (p := p) heq
    have hk12 := k12_eq_quarter_of_equations (p := p) heq
    have ha2 := a2_eq_neg_quarter_of_equations (p := p) heq
    have h0 : path p 0 = path1 p 0 := by
      unfold GerverSofa.Romik.path
      exact ite_eq_left hphi_pos.le
    rw [h0]
    simp only [path1, addK, rot, Real.cos_zero, Real.sin_zero, Prod.ext_iff, Prod.fst_zero,
      Prod.snd_zero]
    constructor <;> linarith
  · intro i
    fin_cases i
    · exact ⟨hv12, hdv12⟩
    · exact ⟨hv23, hdv23⟩
    · exact ⟨hv34, hdv34⟩
    · exact ⟨hv45, hdv45⟩

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
# Gerver / Literal Sets
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The outer cap defined by all upper path support constraints and the horizontal base. -/
def gerverOuterCap : Set Point :=
  {q | 0 ≤ q 1 ∧ ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
    inner ℝ q (normalVector (t : Real.Angle)) ≤
      inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
    inner ℝ q (tangentVector (t : Real.Angle)) ≤
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1}

/-- The union of strict forbidden inner corners above the horizontal base along the Gerver
path. -/
def gerverLiteralNiche : Set Point :=
  {q | 0 ≤ q 1 ∧ ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) < 0 ∧
    inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) < 0}

/-- The literal Gerver sofa obtained by removing its niche from its outer cap. -/
def gerverLiteralSofa : Set Point := gerverOuterCap \ gerverLiteralNiche

/-- Bundle the literal niche and sofa sets for comparison with the canonical definitions. -/
def gerverLiteralSets : Set Point × Set Point := (gerverLiteralNiche, gerverLiteralSofa)

/-- The paper outer cap is the coordinate transport of the certified Romik cap `K₀`. -/
theorem mem_gerverOuterCap_iff (q : Point) :
    q ∈ gerverOuterCap ↔
      GerverSofa.PartF.Coordinates.fromPlane q ∈
        GerverSofa.Romik.K0 GerverSofa.PartB.params := by
  simp only [gerverOuterCap, Set.mem_ofPred_eq, GerverSofa.Romik.mem_K0, Set.mem_inter_iff,
    GerverSofa.Romik.mem_supportHalfU, GerverSofa.Romik.mem_supportHalfV,
    inner_normalVector_eq_dot, inner_tangentVector_eq_dot]
  exact Iff.rfl

/-- A point whose coordinate pair lies in the certified Romik cap `K₀` lies in the paper
outer cap. -/
theorem toPlane_mem_gerverOuterCap {x : GerverSofa.Point}
    (hx : x ∈ GerverSofa.Romik.K0 GerverSofa.PartB.params) :
    GerverSofa.PartF.Coordinates.toPlane x ∈ gerverOuterCap :=
  (mem_gerverOuterCap_iff _).2 (by rwa [GerverSofa.PartF.Coordinates.fromPlane_toPlane])

/-- The paper literal niche is the coordinate transport of the certified Romik niche. -/
theorem mem_gerverLiteralNiche_iff (q : Point) :
    q ∈ gerverLiteralNiche ↔
      GerverSofa.PartF.Coordinates.fromPlane q ∈
        GerverSofa.Romik.niche GerverSofa.PartB.params := by
  have hsub : ∀ (r : Point) (t : ℝ),
      GerverSofa.PartF.Coordinates.fromPlane (r - paperGerverPath t) =
        ((GerverSofa.PartF.Coordinates.fromPlane r).1 -
            (GerverSofa.Romik.path GerverSofa.PartB.params t).1,
          (GerverSofa.PartF.Coordinates.fromPlane r).2 -
            (GerverSofa.Romik.path GerverSofa.PartB.params t).2) := fun _ _ => rfl
  constructor
  · rintro ⟨hy, t, ht, h1, h2⟩
    rw [inner_normalVector_eq_dot, hsub] at h1
    rw [inner_tangentVector_eq_dot, hsub] at h2
    exact ⟨hy, t, ht, h1, h2⟩
  · rintro ⟨hy, t, ht, h1, h2⟩
    refine ⟨hy, t, ht, ?_, ?_⟩
    · rw [inner_normalVector_eq_dot, hsub]; exact h1
    · rw [inner_tangentVector_eq_dot, hsub]; exact h2

theorem paperGerverSofa_eq_literal : paperGerverSofa = gerverLiteralSofa := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hmemhall : ∀ (t : Real.Angle) (v q : Point),
      q ∈ (fun p ↦ rotationMap t p + v) '' hallway ↔
        (inner ℝ (q - v) (normalVector t) ≤ 1 ∧
          inner ℝ (q - v) (tangentVector t) ≤ 1) ∧
        (0 ≤ inner ℝ (q - v) (normalVector t) ∨
          0 ≤ inner ℝ (q - v) (tangentVector t)) := by
    intro t v q
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h0 : inner ℝ (rotationMap t p + v - v) (normalVector t) = p 0 := by
        rw [add_sub_cancel_right, inner_rotationMap_normalVector]
      have h1 : inner ℝ (rotationMap t p + v - v) (tangentVector t) = p 1 := by
        rw [add_sub_cancel_right, inner_rotationMap_tangentVector]
      simp only [h0, h1]
      exact (mem_hallway_iff p).1 hp
    · intro h
      obtain ⟨p, hp⟩ := (EuclideanGeometry.o.rotation t).surjective (q - v)
      have hpq : rotationMap t p = q - v := hp
      have h0 : p 0 = inner ℝ (q - v) (normalVector t) := by
        rw [← inner_rotationMap_normalVector p t, hpq]
      have h1 : p 1 = inner ℝ (q - v) (tangentVector t) := by
        rw [← inner_rotationMap_tangentVector p t, hpq]
      refine ⟨p, (mem_hallway_iff p).2 ?_, ?_⟩
      · rw [h0, h1]; exact h
      · show rotationMap t p + v = q
        rw [hpq]; abel
  have hconttan : Continuous (fun t : ℝ ↦ tangentVector (t : Real.Angle)) := by
    let c : ℝ → (i : Fin 2) → ℝ :=
      fun t i ↦ Fin.cases (-Real.sin t) (fun _ ↦ Real.cos t) i
    have hc : Continuous c := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact Real.continuous_sin.neg
      · exact Real.continuous_cos
    have heq : (fun t : ℝ ↦ tangentVector (t : Real.Angle)) =
        (fun t ↦ WithLp.toLp 2 (c t)) := by
      funext t
      ext i
      fin_cases i <;> rfl
    rw [heq]
    exact (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ)).comp hc
  have hreg := gerver_direct_path_regularity GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  have hpathcont : Continuous paperGerverPath :=
    GerverSofa.PartF.Coordinates.continuous_toPlane.comp hreg.1.continuous
  have hpath0 : paperGerverPath 0 = 0 := by
    show GerverSofa.PartF.Coordinates.toPlane
      (GerverSofa.Romik.path GerverSofa.PartB.params 0) = 0
    rw [hreg.2.1]
    ext i
    fin_cases i <;> rfl
  have hstrip : ∀ q : Point,
      q ∈ (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 ↔ 0 ≤ q 1 ∧ q 1 ≤ 1 := by
    intro q
    have h := mem_stripParallelogram_iff (Real.pi / 2) q
    rw [inner_normalVector_pi_div_two] at h
    have hset : (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 =
        (stripParallelogram (Real.pi / 2)).1 := rfl
    rw [hset, h]
    tauto
  have hshift : ∀ w z n : Point,
      (inner ℝ w n ≤ inner ℝ z n + 1 ↔ inner ℝ (w - z) n ≤ 1) := by
    intro w z n
    rw [inner_sub_left]
    constructor <;> intro h <;> linarith
  ext q
  constructor
  · rintro ⟨hs, hint⟩
    have hhall : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        (inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) ≤ 1 ∧
          inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) ≤ 1) ∧
        (0 ≤ inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) ∨
          0 ≤ inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle))) := fun t ht ↦
      (hmemhall _ _ _).1 (Set.mem_iInter₂.1 hint t ht)
    refine ⟨⟨((hstrip q).1 hs).1, fun t ht ↦
      ⟨(hshift _ _ _).2 (hhall t ht).1.1, (hshift _ _ _).2 (hhall t ht).1.2⟩⟩, ?_⟩
    rintro ⟨-, t, ht, hlt1, hlt2⟩
    rcases (hhall t (Set.Ioo_subset_Icc_self ht)).2 with h | h
    · linarith
    · linarith
  · rintro ⟨⟨hy, hcap⟩, hniche⟩
    have hcap' : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) ≤ 1 ∧
        inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) ≤ 1 := fun t ht ↦
      ⟨(hshift _ _ _).1 (hcap t ht).1, (hshift _ _ _).1 (hcap t ht).2⟩
    have hopen : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        0 ≤ inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) ∨
        0 ≤ inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) := by
      intro t ht
      by_contra hcon
      exact hniche ⟨hy, t, ht, not_le.mp fun h ↦ hcon (Or.inl h),
        not_le.mp fun h ↦ hcon (Or.inr h)⟩
    have hclosed : IsClosed {t : ℝ |
        0 ≤ max (inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)))
          (inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)))} :=
      isClosed_le continuous_const
        (((continuous_const.sub hpathcont).inner continuous_normalVector_real).max
          ((continuous_const.sub hpathcont).inner hconttan))
    have hIcc : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ {t : ℝ |
        0 ≤ max (inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)))
          (inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)))} := by
      rw [← closure_Ioo (ne_of_lt hTpos)]
      exact hclosed.closure_subset_iff.mpr fun t ht ↦ le_max_iff.mpr (hopen t ht)
    have hy1 : q 1 ≤ 1 := by
      have h := (hcap' 0 (Set.left_mem_Icc.mpr hTpos.le)).2
      rwa [hpath0, sub_zero, inner_tangentVector_zero] at h
    refine ⟨(hstrip q).2 ⟨hy, hy1⟩, Set.mem_iInter₂.2 fun t ht ↦ ?_⟩
    exact (hmemhall _ _ _).2
      ⟨hcap' t ht, le_max_iff.mp (hIcc ht)⟩

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
# Gerver / Literal Connected
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem gerver_literal_connected : IsConnected gerverLiteralSofa := by
  have hu : ∀ (q : Point) (t : ℝ),
      inner ℝ q (normalVector (t : Real.Angle)) =
        GerverSofa.dot (GerverSofa.PartF.Coordinates.fromPlane q) (GerverSofa.u t) := by
    intro q t
    simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, GerverSofa.dot,
      GerverSofa.u, GerverSofa.PartF.Coordinates.fromPlane, mul_comm]
  have hv : ∀ (q : Point) (t : ℝ),
      inner ℝ q (tangentVector (t : Real.Angle)) =
        GerverSofa.dot (GerverSofa.PartF.Coordinates.fromPlane q) (GerverSofa.v t) := by
    intro q t
    simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two, GerverSofa.dot,
      GerverSofa.v, GerverSofa.PartF.Coordinates.fromPlane, mul_comm]
  have hpath : ∀ t : ℝ,
      GerverSofa.PartF.Coordinates.fromPlane (paperGerverPath t) =
        GerverSofa.Romik.path GerverSofa.PartC.params t := fun _ => rfl
  have hcap : ∀ q : Point,
      q ∈ gerverOuterCap ↔
        GerverSofa.PartF.Coordinates.fromPlane q ∈
          GerverSofa.Romik.K0 GerverSofa.PartC.params := by
    intro q
    constructor
    · rintro ⟨hy, hs⟩
      refine ⟨hy, fun t ht => ?_⟩
      obtain ⟨h1, h2⟩ := hs t ht
      rw [hu, hu, hpath] at h1
      rw [hv, hv, hpath] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨hy, hs⟩
      refine ⟨hy, fun t ht => ?_⟩
      obtain ⟨h1, h2⟩ := hs t ht
      rw [hu, hu, hpath]
      rw [hv, hv, hpath]
      exact ⟨h1, h2⟩
  have hsub : ∀ (q : Point) (t : ℝ),
      GerverSofa.PartF.Coordinates.fromPlane (q - paperGerverPath t) =
        ((GerverSofa.PartF.Coordinates.fromPlane q).1 -
            (GerverSofa.Romik.path GerverSofa.PartC.params t).1,
          (GerverSofa.PartF.Coordinates.fromPlane q).2 -
            (GerverSofa.Romik.path GerverSofa.PartC.params t).2) := fun _ _ => rfl
  have hniche : ∀ q : Point,
      q ∈ gerverLiteralNiche ↔
        GerverSofa.PartF.Coordinates.fromPlane q ∈
          GerverSofa.Romik.niche GerverSofa.PartC.params := by
    intro q
    constructor
    · rintro ⟨hy, t, ht, h1, h2⟩
      rw [hu, hsub] at h1
      rw [hv, hsub] at h2
      exact ⟨hy, t, ht, h1, h2⟩
    · rintro ⟨hy, t, ht, h1, h2⟩
      refine ⟨hy, t, ht, ?_, ?_⟩
      · rw [hu, hsub]; exact h1
      · rw [hv, hsub]; exact h2
  have hset : gerverLiteralSofa =
      GerverSofa.PartF.Coordinates.toPlane '' GerverSofa.PartC.G := by
    rw [GerverSofa.PartF.Coordinates.image_eq_preimage]
    ext q
    exact and_congr (hcap q) (not_congr (hniche q))
  rw [hset]
  exact GerverSofa.PartF.Coordinates.isConnected_image
    GerverSofa.PartC.Stage4.G_connected_direct

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
# Gerver / Parameter Identification
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open GerverSofa.PartF.ProjectAdapter (selected)

/-- The adapter's selected reverse parameter vector carries the paper's angle `φ` in its
`phi` field.  This is true by definition — `selected` is built from the very quadruple that
defines `GerversSofa.φ` — but it is the only bridge from the vendor parameter vector to the
paper's stage times `gerverStageTimes`, so it is recorded as a named lemma rather than left
to an invisible unfolding at each use site. -/
theorem selected_phi : selected.phi = GerversSofa.φ := rfl

/-- The adapter's selected reverse parameter vector carries the paper's angle `θ` in its
`theta` field; see `selected_phi` for why this `rfl` is worth naming. -/
theorem selected_theta : selected.theta = GerversSofa.θ := rfl

theorem gerver_parameter_identification :
    (∀ p : GerverSofa.Romik.Params, p ∈ gerverDirectBox → gerverDirectEquations p →
      p = gerverParameterDictionary.1 selected ∧
      p.phi = selected.phi ∧ p.theta = selected.theta ∧
      0 < selected.phi ∧ selected.phi < selected.theta ∧ selected.theta < Real.pi / 4 ∧
      (39 : ℝ) / 1000 ≤ selected.phi ∧ selected.phi ≤ (40 : ℝ) / 1000 ∧
      GerversSofa.ABφθSpec selected.a selected.b selected.phi selected.theta) ∧
    (∃ p : GerverSofa.Romik.Params, p ∈ gerverDirectBox ∧ gerverDirectEquations p ∧
      p = gerverParameterDictionary.1 selected) := by
  -- The reverse parameters of any direct solution in the box satisfy the whole
  -- reduced specification, whose unique solution is the selected quadruple.
  have key : ∀ p : GerverSofa.Romik.Params, p ∈ gerverDirectBox → gerverDirectEquations p →
      gerverParameterDictionary.2 p = selected := by
    intro p hp heq
    rw [GerverSofa.PartF.ProjectAdapter.selected_eq_certified]
    exact GerverSofa.PartF.Parameters.undictionary_eq_reduced_certified hp heq
  -- Reconstruction then recovers the direct vector from its reverse parameters.
  have hdict : ∀ p : GerverSofa.Romik.Params, p ∈ gerverDirectBox → gerverDirectEquations p →
      p = gerverParameterDictionary.1 selected := by
    intro p hp heq
    calc p = GerverSofa.PartF.Phases.dictionary (gerverParameterDictionary.2 p) :=
          (GerverSofa.PartF.Phases.dictionary_undictionary_of_equations heq).symm
      _ = gerverParameterDictionary.1 selected :=
          congrArg GerverSofa.PartF.Phases.dictionary (key p hp heq)
  have hspec : GerversSofa.ABφθSpec selected.a selected.b selected.phi selected.theta :=
    GerversSofa.ABφθSpec.existsUnique.choose_spec.1
  refine ⟨fun p hp heq => ?_, GerverSofa.PartB.params, GerverSofa.PartB.params_mem,
    GerverSofa.PartB.params_equations,
    hdict _ GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations⟩
  obtain ⟨hphipos, hphitheta, htheta, -, -, hphilo, hphihi⟩ :=
    gerver_reverse_physical_domain p hp
  have hu := key p hp heq
  rw [hu] at hphipos hphitheta htheta hphilo hphihi
  exact ⟨hdict p hp heq, congrArg GerverSofa.Reduced.Params.phi hu,
    congrArg GerverSofa.Reduced.Params.theta hu, hphipos, hphitheta, htheta, hphilo, hphihi,
    hspec⟩

/-- The two distinguished Gerver angles are interior and complementary. -/
theorem paperGerverConstants_snd_mem_Ioo :
    paperGerverConstants.2.1 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) ∧
      paperGerverConstants.2.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) ∧
      paperGerverConstants.2.1 + paperGerverConstants.2.2 = Real.pi / 2 := by
  have hpos : 0 < GerversSofa.φ := by
    obtain ⟨hall, q, hqbox, hqeq, -⟩ := gerver_parameter_identification
    exact (hall q hqbox hqeq).2.2.2.1
  have hle : GerversSofa.φ ≤ Real.pi / 4 := by
    have h := GerversSofa.ABφθSpec.existsUnique.choose_spec.1
    exact le_trans h.2.1 h.2.2.1
  have hpi := Real.pi_pos
  have h1 : paperGerverConstants.2.1 = GerversSofa.φ := rfl
  have h2 : paperGerverConstants.2.2 = Real.pi / 2 - GerversSofa.φ := rfl
  rw [h1, h2]
  refine ⟨⟨hpos, by linarith only [hle, hpi]⟩,
    ⟨by linarith only [hle, hpi], by linarith only [hpos]⟩, by ring⟩

/-- The two distinguished angles are ordered: the certified bound `φ ≤ 1/25` puts `φ` well below
`π/4 = π/2 - π/4`. -/
theorem paperGerverConstants_snd_fst_lt_snd_snd :
    paperGerverConstants.2.1 < paperGerverConstants.2.2 := by
  obtain ⟨-, -, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  have hphi : paperGerverConstants.2.1 ≤ (40 : ℝ) / 1000 := by
    obtain ⟨hall, p, hpbox, hpeq, -⟩ := gerver_parameter_identification
    exact (hall p hpbox hpeq).2.2.2.2.2.2.2.1
  have := Real.pi_gt_three
  linarith

/-! ### The stage times as certified angles

`gerverStageTimes` is defined from the paper angles `GerversSofa.φ` and `GerversSofa.θ`,
while the certified Part C geometry is indexed by the vendor parameter fields
`params.phi`, `params.theta` and the derived angles `eta`, `tau`, `T`.  The six lemmas
below are the dictionary between the two indexings; they are the only place where
`gerver_parameter_identification` is needed to see a stage time. -/

/-- The zeroth stage time is the start of the rotation interval. -/
theorem gerverStageTimes_zero : gerverStageTimes 0 = 0 := rfl

/-- The first stage time is the certified first switching angle `params.phi`. -/
theorem gerverStageTimes_one : gerverStageTimes 1 = GerverSofa.PartC.params.phi := by
  obtain ⟨-, hphi, -⟩ := gerver_parameter_identification.1 GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  simp [gerverStageTimes, hphi.trans selected_phi]

/-- The second stage time is the certified second switching angle `params.theta`. -/
theorem gerverStageTimes_two : gerverStageTimes 2 = GerverSofa.PartC.params.theta := by
  obtain ⟨-, -, htheta, -⟩ := gerver_parameter_identification.1 GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  simp [gerverStageTimes, htheta.trans selected_theta]

/-- The third stage time is the certified reflected angle `eta = T - params.theta`. -/
theorem gerverStageTimes_three : gerverStageTimes 3 = GerverSofa.PartC.eta := by
  have h := gerverStageTimes_two
  simp only [gerverStageTimes, Matrix.cons_val] at h ⊢
  rw [GerverSofa.PartC.eta, GerverSofa.PartC.T, ← h]

/-- The fourth stage time is the certified reflected angle `tau = T - params.phi`. -/
theorem gerverStageTimes_four : gerverStageTimes 4 = GerverSofa.PartC.tau := by
  have h := gerverStageTimes_one
  simp only [gerverStageTimes, Matrix.cons_val] at h ⊢
  rw [GerverSofa.PartC.tau, GerverSofa.PartC.T, ← h]

/-- The fifth stage time is the certified end `T` of the rotation interval. -/
theorem gerverStageTimes_five : gerverStageTimes 5 = GerverSofa.PartC.T := rfl

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
# Gerver / Contacts
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace MovingSofa

/-- Resolve the Gerver path derivative into its normal and tangent frame components. -/
def paperGerverVelocityComponents (t : ℝ) : ℝ × ℝ :=
  (inner ℝ (deriv paperGerverPath t) (normalVector (t : Real.Angle)),
    inner ℝ (deriv paperGerverPath t) (tangentVector (t : Real.Angle)))

/-- The four standard support-contact points determined by the Gerver path and its derivative. -/
def paperGerverContacts (t : ℝ) : Fin 4 → Point :=
  ![paperGerverPath t + (paperGerverVelocityComponents t).1 • tangentVector (t : Real.Angle) +
      normalVector (t : Real.Angle),
    paperGerverPath t + (paperGerverVelocityComponents t).1 • tangentVector (t : Real.Angle),
    paperGerverPath t - (paperGerverVelocityComponents t).2 • normalVector (t : Real.Angle) +
      tangentVector (t : Real.Angle),
    paperGerverPath t - (paperGerverVelocityComponents t).2 • normalVector (t : Real.Angle)]

/-- Bundle the path velocity components and the four contact curves. -/
def paperGerverContactData : (ℝ → ℝ × ℝ) × (ℝ → Fin 4 → Point) :=
  (paperGerverVelocityComponents, paperGerverContacts)

/-- The explicit body-frame velocity coefficients on a selected Romik branch. -/
def gerverBranchVelocityComponents (i : Fin 5) (t : ℝ) : ℝ × ℝ :=
  ![GerverSofa.Romik.alphaBeta1 GerverSofa.PartB.params t,
    GerverSofa.Romik.alphaBeta2 GerverSofa.PartB.params t,
    GerverSofa.Romik.alphaBeta3 GerverSofa.PartB.params t,
    GerverSofa.Romik.alphaBeta4 GerverSofa.PartB.params t,
    GerverSofa.Romik.alphaBeta5 GerverSofa.PartB.params t] i

/-! ### The common shape of the four contact curves

`paperGerverContacts` is an instance of a generic four-slot shape built from a base curve
and two scalar coefficient functions.  Continuity and smoothness of the shape are proved
once here and reused for the ambient curve and for each analytic stage branch. -/

/-- The four contact curves are continuous as soon as the base curve and the two
coefficient functions are. -/
private theorem continuous_contactShape (X : ℝ → Point) (A B : ℝ → ℝ) (hX : Continuous X)
    (hA : Continuous A) (hB : Continuous B) :
    Continuous fun t : ℝ => (![
      X t + A t • tangentVector (t : Real.Angle) + normalVector (t : Real.Angle),
      X t + A t • tangentVector (t : Real.Angle),
      X t - B t • normalVector (t : Real.Angle) + tangentVector (t : Real.Angle),
      X t - B t • normalVector (t : Real.Angle)] : Fin 4 → Point) := by
  have hN : Continuous fun t : ℝ => normalVector (t : Real.Angle) :=
    contDiff_normalVector.continuous
  have hT : Continuous fun t : ℝ => tangentVector (t : Real.Angle) :=
    contDiff_tangentVector.continuous
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (hX.add (hA.smul hT)).add hN
  · exact hX.add (hA.smul hT)
  · exact (hX.sub (hB.smul hN)).add hT
  · exact hX.sub (hB.smul hN)

/-- The four contact curves are smooth as soon as the base curve and the two coefficient
functions are. -/
private theorem contDiff_contactShape (X : ℝ → Point) (A B : ℝ → ℝ)
    (hX : ContDiff ℝ ∞ X) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ fun t : ℝ => (![
      X t + A t • tangentVector (t : Real.Angle) + normalVector (t : Real.Angle),
      X t + A t • tangentVector (t : Real.Angle),
      X t - B t • normalVector (t : Real.Angle) + tangentVector (t : Real.Angle),
      X t - B t • normalVector (t : Real.Angle)] : Fin 4 → Point) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact (hX.add (hA.smul contDiff_tangentVector)).add contDiff_normalVector
  · exact hX.add (hA.smul contDiff_tangentVector)
  · exact (hX.sub (hB.smul contDiff_normalVector)).add contDiff_tangentVector
  · exact hX.sub (hB.smul contDiff_normalVector)

open GerverSofa.Romik GerverSofa.PartF.Coordinates in
theorem paperGerverContactData_properties :
    Continuous paperGerverVelocityComponents ∧ Continuous paperGerverContacts ∧
    (∀ i : Fin 5, ContDiffOn ℝ ∞ paperGerverContacts (gerverStageIntervals i)) ∧
    (∀ i : Fin 5, ∀ t ∈ gerverStageIntervals i,
      paperGerverVelocityComponents t = gerverBranchVelocityComponents i t) := by
  -- Abbreviate the certified direct parameter vector, and order its switching angles.
  obtain ⟨p, hp⟩ : ∃ p : Params, GerverSofa.PartB.params = p := ⟨_, rfl⟩
  have hmem : p ∈ gerverDirectBox := hp ▸ GerverSofa.PartB.params_mem
  have heqs : gerverDirectEquations p := hp ▸ GerverSofa.PartB.params_equations
  obtain ⟨hC1, -, -⟩ := gerver_direct_path_regularity p hmem heqs
  obtain ⟨-, hphi, htheta, hphipos, hphitheta, hthetalt, -⟩ :=
    gerver_parameter_identification.1 p hmem heqs
  have hphi' : p.phi = GerversSofa.φ := hphi.trans selected_phi
  have htheta' : p.theta = GerversSofa.θ := htheta.trans selected_theta
  have h0 : (0 : ℝ) < p.phi := by rw [hphi]; exact hphipos
  have h1 : p.phi < p.theta := by rw [hphi, htheta]; exact hphitheta
  have h2 : p.theta < Real.pi / 4 := by rw [htheta]; exact hthetalt
  have hC1' : ContDiff ℝ 1 (path GerverSofa.PartB.params) := by rw [hp]; exact hC1
  -- The velocity components read off the body-frame derivative of the direct path.
  have hvel : ∀ (w : GerverSofa.Point) (t : ℝ), deriv (path p) t = rot t w →
      paperGerverVelocityComponents t = w := by
    intro w t hw
    have hd : deriv paperGerverPath t = toPlane (rot t w) := by
      rw [deriv_paperGerverPath hC1' t, hp, hw]
    simp only [paperGerverVelocityComponents, hd, inner_toPlane_rot_normalVector,
      inner_toPlane_rot_tangentVector]
  have hvelC : Continuous paperGerverVelocityComponents :=
    ((continuous_deriv_paperGerverPath hC1').inner contDiff_normalVector.continuous).prodMk
      ((continuous_deriv_paperGerverPath hC1').inner contDiff_tangentVector.continuous)
  -- Stage smoothness: the contacts agree there with the smooth analytic branch data.
  have hstage : ∀ (X W : ℝ → GerverSofa.Point) (s : Set ℝ), ContDiff ℝ ∞ X →
      ContDiff ℝ ∞ W → (∀ t ∈ s, path p t = X t) →
      (∀ t ∈ s, deriv (path p) t = rot t (W t)) →
      ContDiffOn ℝ ∞ paperGerverContacts s := by
    intro X W s hX hW hXe hWe
    refine (contDiff_contactShape (fun t => toPlane (X t)) (fun t => (W t).1)
      (fun t => (W t).2) (contDiff_toPlane hX) hW.fst hW.snd).contDiffOn.congr ?_
    intro t ht
    have hx : paperGerverPath t = toPlane (X t) := by
      show toPlane (path GerverSofa.PartB.params t) = toPlane (X t)
      rw [hp]
      exact congrArg toPlane (hXe t ht)
    simp only [paperGerverContacts, hx, hvel (W t) t (hWe t ht)]
  -- The five stage intervals, in terms of the direct switching angles.
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 p.phi := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hI1 : gerverStageIntervals 1 = Set.Icc p.phi p.theta := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI2 : gerverStageIntervals 2 = Set.Icc p.theta (Real.pi / 2 - p.theta) := by
    simp [gerverStageIntervals, gerverStageTimes, htheta']
  have hI3 : gerverStageIntervals 3 =
      Set.Icc (Real.pi / 2 - p.theta) (Real.pi / 2 - p.phi) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI4 : gerverStageIntervals 4 = Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  -- The stage coefficient pairs, read off the vector of branch velocities.
  have hB0 : ∀ t, gerverBranchVelocityComponents 0 t = alphaBeta1 p t := fun t => by
    simp [gerverBranchVelocityComponents, hp]
  have hB1 : ∀ t, gerverBranchVelocityComponents 1 t = alphaBeta2 p t := fun t => by
    simp [gerverBranchVelocityComponents, hp]
  have hB2 : ∀ t, gerverBranchVelocityComponents 2 t = alphaBeta3 p t := fun t => by
    simp [gerverBranchVelocityComponents, hp]
  have hB3 : ∀ t, gerverBranchVelocityComponents 3 t = alphaBeta4 p t := fun t => by
    simp [gerverBranchVelocityComponents, hp]
  have hB4 : ∀ t, gerverBranchVelocityComponents 4 t = alphaBeta5 p t := fun t => by
    simp [gerverBranchVelocityComponents, hp]
  refine ⟨hvelC, ?_, ?_, ?_⟩
  · exact continuous_contactShape paperGerverPath
      (fun t => (paperGerverVelocityComponents t).1)
      (fun t => (paperGerverVelocityComponents t).2) (continuous_paperGerverPath hC1')
      hvelC.fst hvelC.snd
  · intro i
    fin_cases i
    · exact hstage (path1 p) (alphaBeta1 p) (gerverStageIntervals 0) (contDiff_path1 p)
        (contDiff_alphaBeta1 p) (fun t ht => path_eq_path1_of_mem_Icc p (hI0 ▸ ht))
        (fun t ht => deriv_path_eq_rot_alphaBeta1 hC1 h0 (hI0 ▸ ht))
    · exact hstage (path2 p) (alphaBeta2 p) (gerverStageIntervals 1) (contDiff_path2 p)
        (contDiff_alphaBeta2 p) (fun t ht => path_eq_path2_of_mem_Icc heqs (hI1 ▸ ht))
        (fun t ht => deriv_path_eq_rot_alphaBeta2 hC1 heqs h1 (hI1 ▸ ht))
    · exact hstage (path3 p) (alphaBeta3 p) (gerverStageIntervals 2) (contDiff_path3 p)
        (contDiff_alphaBeta3 p) (fun t ht => path_eq_path3_of_mem_Icc heqs h1 (hI2 ▸ ht))
        (fun t ht => deriv_path_eq_rot_alphaBeta3 hC1 heqs h1 h2 (hI2 ▸ ht))
    · exact hstage (path4 p) (alphaBeta4 p) (gerverStageIntervals 3) (contDiff_path4 p)
        (contDiff_alphaBeta4 p) (fun t ht => path_eq_path4_of_mem_Icc heqs h1 h2 (hI3 ▸ ht))
        (fun t ht => deriv_path_eq_rot_alphaBeta4 hC1 heqs h1 h2 (hI3 ▸ ht))
    · exact hstage (path5 p) (alphaBeta5 p) (gerverStageIntervals 4) (contDiff_path5 p)
        (contDiff_alphaBeta5 p) (fun t ht => path_eq_path5_of_mem_Icc heqs h1 h2 (hI4 ▸ ht))
        (fun t ht => deriv_path_eq_rot_alphaBeta5 hC1 heqs h0 h1 h2 (hI4 ▸ ht))
  · intro i
    fin_cases i
    · exact fun t ht => (hvel _ t (deriv_path_eq_rot_alphaBeta1 hC1 h0
        (hI0 ▸ (ht : t ∈ gerverStageIntervals 0)))).trans (hB0 t).symm
    · exact fun t ht => (hvel _ t (deriv_path_eq_rot_alphaBeta2 hC1 heqs h1
        (hI1 ▸ (ht : t ∈ gerverStageIntervals 1)))).trans (hB1 t).symm
    · exact fun t ht => (hvel _ t (deriv_path_eq_rot_alphaBeta3 hC1 heqs h1 h2
        (hI2 ▸ (ht : t ∈ gerverStageIntervals 2)))).trans (hB2 t).symm
    · exact fun t ht => (hvel _ t (deriv_path_eq_rot_alphaBeta4 hC1 heqs h1 h2
        (hI3 ▸ (ht : t ∈ gerverStageIntervals 3)))).trans (hB3 t).symm
    · exact fun t ht => (hvel _ t (deriv_path_eq_rot_alphaBeta5 hC1 heqs h0 h1 h2
        (hI4 ▸ (ht : t ∈ gerverStageIntervals 4)))).trans (hB4 t).symm

/-! ### Identification with the certified piecewise contact data -/

/-- On the physical rotation interval the paper velocity components agree with the vendor
piecewise body-frame coefficients. -/
theorem paperGerverVelocityComponents_eq_alphaBetaAt (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paperGerverVelocityComponents t = GerverSofa.PartC.alphaBetaAt t := by
  obtain ⟨-, hphi, htheta, -⟩ := gerver_parameter_identification.1 GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  have hphi' : GerverSofa.PartB.params.phi = GerversSofa.φ := hphi.trans selected_phi
  have htheta' : GerverSofa.PartB.params.theta = GerversSofa.θ := htheta.trans selected_theta
  have hvel := paperGerverContactData_properties.2.2.2
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 GerversSofa.φ := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI1 : gerverStageIntervals 1 = Set.Icc GerversSofa.φ GerversSofa.θ := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI2 : gerverStageIntervals 2 = Set.Icc GerversSofa.θ (Real.pi / 2 - GerversSofa.θ) := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI3 : gerverStageIntervals 3 =
      Set.Icc (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI4 : gerverStageIntervals 4 = Set.Icc (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes]
  obtain ⟨ht0, ht2⟩ := ht
  simp only [GerverSofa.PartC.alphaBetaAt, GerverSofa.PartC.eta, GerverSofa.PartC.tau,
    GerverSofa.PartC.T, hphi', htheta']
  split_ifs with h1 h2 h3 h4
  · have := hvel 0 t (by rw [hI0]; exact ⟨ht0, h1⟩)
    simpa [gerverBranchVelocityComponents] using this
  · have := hvel 1 t (by rw [hI1]; exact ⟨le_of_not_ge h1, h2⟩)
    simpa [gerverBranchVelocityComponents] using this
  · have := hvel 2 t (by rw [hI2]; exact ⟨le_of_not_ge h2, h3⟩)
    simpa [gerverBranchVelocityComponents] using this
  · have := hvel 3 t (by rw [hI3]; exact ⟨le_of_not_ge h3, h4⟩)
    simpa [gerverBranchVelocityComponents] using this
  · have := hvel 4 t (by rw [hI4]; exact ⟨le_of_not_ge h4, ht2⟩)
    simpa [gerverBranchVelocityComponents] using this

/-- On the physical rotation interval the four paper contact curves are the coordinate
transports of the four certified contact curves. -/
theorem fromPlane_paperGerverContacts (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (i : Fin 4) :
    GerverSofa.PartF.Coordinates.fromPlane (paperGerverContacts t i) =
      ![GerverSofa.PartC.A t, GerverSofa.PartC.B t, GerverSofa.PartC.C t,
        GerverSofa.PartC.D t] i := by
  have hab := paperGerverVelocityComponents_eq_alphaBetaAt t ht
  fin_cases i <;> simp only [paperGerverContacts, hab] <;> rfl

/-- On the physical rotation interval the second paper contact curve is the certified curve
`B`, read in plane coordinates. -/
theorem paperGerverContacts_one_eq_toPlane {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paperGerverContacts t 1 =
      GerverSofa.PartF.Coordinates.toPlane (GerverSofa.PartC.B t) :=
  (GerverSofa.PartF.Coordinates.toPlane_fromPlane _).symm.trans
    (congrArg GerverSofa.PartF.Coordinates.toPlane (fromPlane_paperGerverContacts t ht 1))

/-- On the physical rotation interval the fourth paper contact curve is the certified curve
`D`, read in plane coordinates. -/
theorem paperGerverContacts_three_eq_toPlane {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paperGerverContacts t 3 =
      GerverSofa.PartF.Coordinates.toPlane (GerverSofa.PartC.D t) :=
  (GerverSofa.PartF.Coordinates.toPlane_fromPlane _).symm.trans
    (congrArg GerverSofa.PartF.Coordinates.toPlane (fromPlane_paperGerverContacts t ht 3))

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
# The Gerver niche roof

The upper boundary of the paper's literal Gerver niche is a three-piece graph over the
rotation interval: the fourth contact curve up to the second stage time, the direct path run
*backwards* through the affine reversal `gerverRoofReverseTime` on the middle stage, and the
second contact curve from the third stage time on.  `gerverRoofCurve` is that graph as a
function of an unrestricted real parameter and `gerverNicheRoof` its restriction to the
rotation interval; `gerverRoofCurve_eq` relates the two.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The affine reversal of the middle roof stage: it maps `gerverStageTimes 2` to
`gerverStageTimes 4` and `gerverStageTimes 3` to `gerverStageTimes 1`, so it reparametrizes
the central part of the direct path backwards. -/
def gerverRoofReverseTime (s : ℝ) : ℝ :=
  gerverStageTimes 4 - (gerverStageTimes 4 - gerverStageTimes 1) /
    (gerverStageTimes 3 - gerverStageTimes 2) * (s - gerverStageTimes 2)

/-- The Gerver niche roof as a curve of an unrestricted real parameter.  On the rotation
interval it agrees with `gerverNicheRoof` (`gerverRoofCurve_eq`); the unrestricted form is
what the intermediate value theorem and `continuous_if_le` consume. -/
def gerverRoofCurve (s : ℝ) : Point :=
  if s ≤ gerverStageTimes 2 then paperGerverContacts s 3
  else if s ≤ gerverStageTimes 3 then paperGerverPath (gerverRoofReverseTime s)
  else paperGerverContacts s 1

/-- The three-branch roof of the Gerver niche, using two contact arcs and the reversed path. -/
def gerverNicheRoof (s : Set.Icc (0 : ℝ) (Real.pi / 2)) : Point :=
  if s.val ≤ gerverStageTimes 2 then paperGerverContacts s.val 3
  else if s.val ≤ gerverStageTimes 3 then paperGerverPath (gerverRoofReverseTime s.val)
  else paperGerverContacts s.val 1

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
# Gerver / ODEs
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Tangential components of the four contact-curve derivatives on a selected stage. -/
def gerverStageContactDerivatives (i : Fin 5) (t : ℝ) : Fin 4 → ℝ :=
  ![inner ℝ (derivWithin (fun s ↦ paperGerverContacts s 0) (gerverStageIntervals i) t)
      (tangentVector (t : Real.Angle)),
    inner ℝ (derivWithin (fun s ↦ paperGerverContacts s 1) (gerverStageIntervals i) t)
      (tangentVector (t : Real.Angle)),
    inner ℝ (-(derivWithin (fun s ↦ paperGerverContacts s 2) (gerverStageIntervals i) t))
      (normalVector (t : Real.Angle)),
    inner ℝ (derivWithin (fun s ↦ paperGerverContacts s 3) (gerverStageIntervals i) t)
      (normalVector (t : Real.Angle))]

private theorem gerver_contact_derivatives_from_frame (i : Fin 5) (t : ℝ)
    (ht : t ∈ gerverStageIntervals i)
    (huniq : UniqueDiffWithinAt ℝ (gerverStageIntervals i) t) :
    ∀ (X : ℝ → Point) (X' : Point) (A B : ℝ → ℝ) (a' b' : ℝ),
     HasDerivAt X X' t →
     inner ℝ X' (normalVector (t : Real.Angle)) = A t →
     inner ℝ X' (tangentVector (t : Real.Angle)) = B t →
     HasDerivAt A a' t → HasDerivAt B b' t →
     (∀ r ∈ gerverStageIntervals i, paperGerverPath r = X r) →
     (∀ r ∈ gerverStageIntervals i, paperGerverVelocityComponents r = (A r, B r)) →
     gerverStageContactDerivatives i t 0 = B t + a' + 1 ∧
     gerverStageContactDerivatives i t 1 = B t + a' ∧
     gerverStageContactDerivatives i t 2 = b' + 1 - A t ∧
     gerverStageContactDerivatives i t 3 = A t - b' := by
  -- Frame orthonormality at the fixed angle `t`.
  have huu :
      inner ℝ (normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = (1 : ℝ) :=
    inner_normalVector_self t
  have hvv :
      inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = (1 : ℝ) :=
    inner_tangentVector_self t
  have huv :
      inner ℝ (normalVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = (0 : ℝ) :=
    inner_normalVector_tangentVector t
  have hvu :
      inner ℝ (tangentVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = (0 : ℝ) := by
    rw [real_inner_comm]; exact huv
  intro X X' A B a' b' hX hXu hXv hA hB hpath hvel
  have hn : HasDerivAt (fun s : ℝ => normalVector (s : Real.Angle))
      (tangentVector (t : Real.Angle)) t := hasDerivAt_normalVector t
  have hg : HasDerivAt (fun s : ℝ => tangentVector (s : Real.Angle))
      (-normalVector (t : Real.Angle)) t := hasDerivAt_tangentVector t
  have hAv := hA.fun_smul hg
  have hBn := hB.fun_smul hn
  have hc0 : HasDerivWithinAt (fun s => paperGerverContacts s 0)
      (X' + (A t • (-normalVector (t : Real.Angle)) + a' • tangentVector (t : Real.Angle)) +
        tangentVector (t : Real.Angle)) (gerverStageIntervals i) t := by
    refine ((hX.fun_add hAv).fun_add hn).hasDerivWithinAt.congr (fun r hr => ?_) ?_
    · simp only [paperGerverContacts, Matrix.cons_val_zero, hpath r hr, hvel r hr]
    · simp only [paperGerverContacts, Matrix.cons_val_zero, hpath t ht, hvel t ht]
  have hc1 : HasDerivWithinAt (fun s => paperGerverContacts s 1)
      (X' + (A t • (-normalVector (t : Real.Angle)) + a' • tangentVector (t : Real.Angle)))
      (gerverStageIntervals i) t := by
    refine (hX.fun_add hAv).hasDerivWithinAt.congr (fun r hr => ?_) ?_
    · simp only [paperGerverContacts, hpath r hr, hvel r hr]
      rfl
    · simp only [paperGerverContacts, hpath t ht, hvel t ht]
      rfl
  have hc2 : HasDerivWithinAt (fun s => paperGerverContacts s 2)
      (X' - (B t • tangentVector (t : Real.Angle) + b' • normalVector (t : Real.Angle)) +
        -normalVector (t : Real.Angle)) (gerverStageIntervals i) t := by
    refine ((hX.fun_sub hBn).fun_add hg).hasDerivWithinAt.congr (fun r hr => ?_) ?_
    · simp only [paperGerverContacts, hpath r hr, hvel r hr]
      rfl
    · simp only [paperGerverContacts, hpath t ht, hvel t ht]
      rfl
  have hc3 : HasDerivWithinAt (fun s => paperGerverContacts s 3)
      (X' - (B t • tangentVector (t : Real.Angle) + b' • normalVector (t : Real.Angle)))
      (gerverStageIntervals i) t := by
    refine (hX.fun_sub hBn).hasDerivWithinAt.congr (fun r hr => ?_) ?_
    · simp only [paperGerverContacts, hpath r hr, hvel r hr]
      rfl
    · simp only [paperGerverContacts, hpath t ht, hvel t ht]
      rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show inner ℝ (derivWithin (fun s => paperGerverContacts s 0) (gerverStageIntervals i) t)
      (tangentVector (t : Real.Angle)) = B t + a' + 1
    rw [hc0.derivWithin huniq]
    simp only [inner_add_left, real_inner_smul_left, inner_neg_left, hXv, huv, hvv]
    ring
  · show inner ℝ (derivWithin (fun s => paperGerverContacts s 1) (gerverStageIntervals i) t)
      (tangentVector (t : Real.Angle)) = B t + a'
    rw [hc1.derivWithin huniq]
    simp only [inner_add_left, real_inner_smul_left, inner_neg_left, hXv, huv, hvv]
    ring
  · show inner ℝ (-derivWithin (fun s => paperGerverContacts s 2) (gerverStageIntervals i) t)
      (normalVector (t : Real.Angle)) = b' + 1 - A t
    rw [hc2.derivWithin huniq]
    simp only [inner_neg_left, inner_add_left, inner_sub_left, real_inner_smul_left, hXu, hvu,
      huu]
    ring
  · show inner ℝ (derivWithin (fun s => paperGerverContacts s 3) (gerverStageIntervals i) t)
      (normalVector (t : Real.Angle)) = A t - b'
    rw [hc3.derivWithin huniq]
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hXu, hvu, huu]
    ring

theorem gerver_stageODEs (i : Fin 5) (t : ℝ) (ht : t ∈ gerverStageIntervals i) :
    (gerverStageContactDerivatives i t 0, gerverStageContactDerivatives i t 2) =
      ![(0, gerverStageContactDerivatives i t 3),
        ((paperGerverVelocityComponents t).2,
          gerverStageContactDerivatives i t 3 - (paperGerverVelocityComponents t).1),
        ((paperGerverVelocityComponents t).2, -(paperGerverVelocityComponents t).1),
        (-gerverStageContactDerivatives i t 1 + (paperGerverVelocityComponents t).2,
          -(paperGerverVelocityComponents t).1),
        (-gerverStageContactDerivatives i t 1, 0)] i := by
  open GerverSofa.Romik GerverSofa.PartF.Coordinates in
  -- The certified direct parameter vector and the ordering of its switching angles.
  obtain ⟨p, hp⟩ : ∃ p : Params, GerverSofa.PartB.params = p := ⟨_, rfl⟩
  have hmem : p ∈ gerverDirectBox := hp ▸ GerverSofa.PartB.params_mem
  have heqs : gerverDirectEquations p := hp ▸ GerverSofa.PartB.params_equations
  obtain ⟨-, hphieq, hthetaeq, hphipos, hphitheta, hthetalt, -⟩ :=
    gerver_parameter_identification.1 p hmem heqs
  have hphi' : p.phi = GerversSofa.φ := hphieq.trans selected_phi
  have htheta' : p.theta = GerversSofa.θ := hthetaeq.trans selected_theta
  have h0 : (0 : ℝ) < p.phi := by rw [hphieq]; exact hphipos
  have h1 : p.phi < p.theta := by rw [hphieq, hthetaeq]; exact hphitheta
  have h2 : p.theta < Real.pi / 4 := by rw [hthetaeq]; exact hthetalt
  -- The five closed stage intervals in terms of the direct switching angles.
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 p.phi := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hI1 : gerverStageIntervals 1 = Set.Icc p.phi p.theta := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI2 : gerverStageIntervals 2 = Set.Icc p.theta (Real.pi / 2 - p.theta) := by
    simp [gerverStageIntervals, gerverStageTimes, htheta']
  have hI3 : gerverStageIntervals 3 =
      Set.Icc (Real.pi / 2 - p.theta) (Real.pi / 2 - p.phi) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI4 : gerverStageIntervals 4 = Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hval := paperGerverContactData_properties.2.2.2
  -- Derivatives of the ten branch coefficient functions, in one normal form.
  have hidt : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have hshape : ∀ (c₀ c₁ c₂ c₃ c₄ : ℝ) (f : ℝ → ℝ),
      (∀ s : ℝ,
        f s = c₀ + c₁ * s + c₂ * s * s + c₃ * Real.sin s + c₄ * Real.cos s) →
      HasDerivAt f (c₁ + 2 * c₂ * t + c₃ * Real.cos t - c₄ * Real.sin t) t := by
    intro c₀ c₁ c₂ c₃ c₄ f hf
    have h : HasDerivAt
        (fun s : ℝ => c₀ + c₁ * s + c₂ * s * s + c₃ * Real.sin s + c₄ * Real.cos s)
        (c₁ + 2 * c₂ * t + c₃ * Real.cos t - c₄ * Real.sin t) t := by
      refine ((((hasDerivAt_const t c₀).fun_add (hidt.const_mul c₁)).fun_add
        ((hidt.const_mul c₂).fun_mul hidt)).fun_add
        ((Real.hasDerivAt_sin t).const_mul c₃)).fun_add
        ((Real.hasDerivAt_cos t).const_mul c₄) |>.congr_deriv ?_
      ring
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hf s)
  -- Unique differentiability of the closed stage interval at `t`.
  have g0 : (0 : ℝ) < GerversSofa.φ := by rw [← hphi']; exact h0
  have g1 : GerversSofa.φ < GerversSofa.θ := by rw [← hphi', ← htheta']; exact h1
  have g2 : GerversSofa.θ < Real.pi / 4 := by rw [← htheta']; exact h2
  have huniq : UniqueDiffWithinAt ℝ (gerverStageIntervals i) t := by
    fin_cases i
    · exact uniqueDiffOn_Icc g0 t ht
    · exact uniqueDiffOn_Icc g1 t ht
    · exact uniqueDiffOn_Icc
        (show GerversSofa.θ < Real.pi / 2 - GerversSofa.θ by linarith) t ht
    · exact uniqueDiffOn_Icc
        (show Real.pi / 2 - GerversSofa.θ < Real.pi / 2 - GerversSofa.φ by linarith) t ht
    · exact uniqueDiffOn_Icc
        (show Real.pi / 2 - GerversSofa.φ < Real.pi / 2 by linarith) t ht
  -- The frame computation: the four contact derivatives in terms of `α, β, α', β'`.
  have hcore := gerver_contact_derivatives_from_frame i t ht huniq
  fin_cases i
  · -- Stage 1
    have hvel : ∀ r ∈ gerverStageIntervals 0,
        paperGerverVelocityComponents r = alphaBeta1 p r := by
      intro r hr
      rw [hval 0 r hr]
      simp [gerverBranchVelocityComponents, hp]
    obtain ⟨e0, e1, e2, e3⟩ := hcore (fun s => toPlane (path1 p s))
      (toPlane (rot t (alphaBeta1 p t))) (fun s => (alphaBeta1 p s).1)
      (fun s => (alphaBeta1 p s).2) _ _ (hasDerivAt_toPlane (hasDerivAt_path1 p t))
      (inner_toPlane_rot_normalVector t _) (inner_toPlane_rot_tangentVector t _)
      (hshape (1 / 2) 0 0 (-2 * p.a1) (2 * p.a2) _ fun s => by dsimp [alphaBeta1]; ring)
      (hshape (-1) 0 0 (2 * p.a2) (2 * p.a1) _ fun s => by dsimp [alphaBeta1]; ring)
      (fun r hr => by
        show toPlane (path GerverSofa.PartB.params r) = toPlane (path1 p r)
        rw [hp]
        exact congrArg toPlane (path_eq_path1_of_mem_Icc p (hI0 ▸ hr)))
      (fun r hr => hvel r hr)
    rw [Prod.mk.injEq, e0, e2, e3]
    refine ⟨?_, ?_⟩ <;> dsimp [alphaBeta1] <;> ring
  · -- Stage 2
    have hvel : ∀ r ∈ gerverStageIntervals 1,
        paperGerverVelocityComponents r = alphaBeta2 p r := by
      intro r hr
      rw [hval 1 r hr]
      simp [gerverBranchVelocityComponents, hp]
    obtain ⟨e0, e1, e2, e3⟩ := hcore (fun s => toPlane (path2 p s))
      (toPlane (rot t (alphaBeta2 p t))) (fun s => (alphaBeta2 p s).1)
      (fun s => (alphaBeta2 p s).2) _ _ (hasDerivAt_toPlane (hasDerivAt_path2 p t))
      (inner_toPlane_rot_normalVector t _) (inner_toPlane_rot_tangentVector t _)
      (hshape (1 + 2 * p.b1) (-1) 0 0 0 _ fun s => by dsimp [alphaBeta2]; ring)
      (hshape (p.b2 + 1 / 2) p.b1 (-(1 / 4)) 0 0 _ fun s => by dsimp [alphaBeta2]; ring)
      (fun r hr => by
        show toPlane (path GerverSofa.PartB.params r) = toPlane (path2 p r)
        rw [hp]
        exact congrArg toPlane (path_eq_path2_of_mem_Icc heqs (hI1 ▸ hr)))
      (fun r hr => hvel r hr)
    rw [Prod.mk.injEq, hvel t ht, e0, e2, e3]
    refine ⟨?_, ?_⟩ <;> dsimp [alphaBeta2] <;> ring
  · -- Stage 3
    have hvel : ∀ r ∈ gerverStageIntervals 2,
        paperGerverVelocityComponents r = alphaBeta3 p r := by
      intro r hr
      rw [hval 2 r hr]
      simp [gerverBranchVelocityComponents, hp]
    obtain ⟨e0, e1, e2, e3⟩ := hcore (fun s => toPlane (path3 p s))
      (toPlane (rot t (alphaBeta3 p t))) (fun s => (alphaBeta3 p s).1)
      (fun s => (alphaBeta3 p s).2) _ _ (hasDerivAt_toPlane (hasDerivAt_path3 p t))
      (inner_toPlane_rot_normalVector t _) (inner_toPlane_rot_tangentVector t _)
      (hshape (-1 - p.c2) (-1) 0 0 0 _ fun s => by dsimp [alphaBeta3]; ring)
      (hshape (1 + p.c1) (-1) 0 0 0 _ fun s => by dsimp [alphaBeta3]; ring)
      (fun r hr => by
        show toPlane (path GerverSofa.PartB.params r) = toPlane (path3 p r)
        rw [hp]
        exact congrArg toPlane (path_eq_path3_of_mem_Icc heqs h1 (hI2 ▸ hr)))
      (fun r hr => hvel r hr)
    rw [Prod.mk.injEq, hvel t ht, e0, e2]
    refine ⟨?_, ?_⟩ <;> dsimp [alphaBeta3] <;> ring
  · -- Stage 4
    have hvel : ∀ r ∈ gerverStageIntervals 3,
        paperGerverVelocityComponents r = alphaBeta4 p r := by
      intro r hr
      rw [hval 3 r hr]
      simp [gerverBranchVelocityComponents, hp]
    obtain ⟨e0, e1, e2, e3⟩ := hcore (fun s => toPlane (path4 p s))
      (toPlane (rot t (alphaBeta4 p t))) (fun s => (alphaBeta4 p s).1)
      (fun s => (alphaBeta4 p s).2) _ _ (hasDerivAt_toPlane (hasDerivAt_path4 p t))
      (inner_toPlane_rot_normalVector t _) (inner_toPlane_rot_tangentVector t _)
      (hshape (-p.d2 - 1 / 2) (-p.d1) (1 / 4) 0 0 _ fun s => by dsimp [alphaBeta4]; ring)
      (hshape (2 * p.d1 - 1) (-1) 0 0 0 _ fun s => by dsimp [alphaBeta4]; ring)
      (fun r hr => by
        show toPlane (path GerverSofa.PartB.params r) = toPlane (path4 p r)
        rw [hp]
        exact congrArg toPlane (path_eq_path4_of_mem_Icc heqs h1 h2 (hI3 ▸ hr)))
      (fun r hr => hvel r hr)
    rw [Prod.mk.injEq, hvel t ht, e0, e1, e2]
    refine ⟨?_, ?_⟩ <;> dsimp [alphaBeta4] <;> ring
  · -- Stage 5
    have hvel : ∀ r ∈ gerverStageIntervals 4,
        paperGerverVelocityComponents r = alphaBeta5 p r := by
      intro r hr
      rw [hval 4 r hr]
      simp [gerverBranchVelocityComponents, hp]
    obtain ⟨e0, e1, e2, e3⟩ := hcore (fun s => toPlane (path5 p s))
      (toPlane (rot t (alphaBeta5 p t))) (fun s => (alphaBeta5 p s).1)
      (fun s => (alphaBeta5 p s).2) _ _ (hasDerivAt_toPlane (hasDerivAt_path5 p t))
      (inner_toPlane_rot_normalVector t _) (inner_toPlane_rot_tangentVector t _)
      (hshape 1 0 0 (-2 * p.e1) (2 * p.e2) _ fun s => by dsimp [alphaBeta5]; ring)
      (hshape (-(1 / 2)) 0 0 (2 * p.e2) (2 * p.e1) _ fun s => by dsimp [alphaBeta5]; ring)
      (fun r hr => by
        show toPlane (path GerverSofa.PartB.params r) = toPlane (path5 p r)
        rw [hp]
        exact congrArg toPlane (path_eq_path5_of_mem_Icc heqs h1 h2 (hI4 ▸ hr)))
      (fun r hr => hvel r hr)
    rw [Prod.mk.injEq, e0, e1, e2]
    refine ⟨?_, ?_⟩ <;> dsimp [alphaBeta5] <;> ring

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
# Gerver / Outer Contacts
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem gerver_outer_contact_A (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paperGerverContacts t 0 ∈ gerverOuterCap := by
  rw [mem_gerverOuterCap_iff, fromPlane_paperGerverContacts t ht 0]
  exact GerverSofa.PartC.Stage3.supportA_direct t ht

theorem gerver_outer_contact_C (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paperGerverContacts t 2 ∈ gerverOuterCap := by
  rw [mem_gerverOuterCap_iff, fromPlane_paperGerverContacts t ht 2]
  exact GerverSofa.PartC.Stage3.supportC_direct t ht

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
# Regularity of the certified Gerver stage data

The five Gerver stages are nondegenerate: the six stage endpoints increase strictly from `0`
to `π / 2` (`gerverStageTimes_strictMono`), and `gerverStageIntervals_zero` through
`gerverStageIntervals_four` name the resulting closed stage intervals.  The certified direct
path is continuously differentiable on the whole rotation interval
(`contDiff_paperGerverPath`), while each contact curve is only continuous globally
(`continuous_paperGerverContact`) and continuously differentiable on a single stage
(`contDiffOn_paperGerverContact`).  Gluing two consecutive stages presents the two inner
contact curves on the parameter ranges where they touch the cap as continuous paths of bounded
variation (`gerverRightContactBV`, `gerverLeftContactBV`).

The second half of the file differentiates the two inner contact curves stagewise.  Writing
the velocity components of the direct path as `(α, β)`, the contact formulas are
`B = x + α v` and `D = x - β u`, so the product rule and the frame derivatives
`hasDerivAt_normalVector`, `hasDerivAt_tangentVector` give
`B' = (β + α') v` and `D' = (α - β') u`
(`hasDerivWithinAt_paperGerverContacts_one`, `hasDerivWithinAt_paperGerverContacts_three`).
Feeding the five analytic stage branches of `paperGerverContactData_properties` into these
two lemmas yields the signs of the two speeds on the stages where they are needed
(`hasDerivWithinAt_paperGerverContacts_one_neg_smul`,
`hasDerivWithinAt_paperGerverContacts_three_pos_smul`); the two nonconstant coefficients are
signed by the coarse box bounds `gerverDirectBox_b1_lower_bound`,
`gerverDirectBox_d1_upper_bound` and `gerverStageTimes_two_le_seven_div_ten`.

The last two sections record the consequences used downstream: the frame coordinates
`s ↦ x s ⋅ u_s` and `s ↦ x s ⋅ v_s` of the direct path are differentiable with derivatives
`B ⋅ v` and `-D ⋅ u` (`hasDerivAt_inner_paperGerverPath_normalVector`,
`hasDerivAt_inner_paperGerverPath_tangentVector`), and against a fixed frame direction outside
the stage the two inner contact curves are strictly monotone on each stage
(`strictAntiOn_inner_paperGerverContacts_three`, `strictMonoOn_inner_paperGerverContacts_one`).
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The six Gerver stage endpoints increase strictly along the rotation interval. -/
theorem gerverStageTimes_strictMono : StrictMono gerverStageTimes := by
  obtain ⟨-, -, -, hpos, hlt, hqt, -⟩ := gerver_parameter_identification.1
    GerverSofa.PartB.params GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  rw [selected_phi] at hpos
  rw [selected_phi, selected_theta] at hlt
  rw [selected_theta] at hqt
  refine Fin.strictMono_iff_lt_succ.mpr fun i ↦ ?_
  fin_cases i
  · show gerverStageTimes 0 < gerverStageTimes 1
    simp only [gerverStageTimes, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith
  · show gerverStageTimes 1 < gerverStageTimes 2
    simp only [gerverStageTimes, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linarith
  · show gerverStageTimes 2 < gerverStageTimes 3
    simp only [gerverStageTimes, Matrix.cons_val]
    linarith
  · show gerverStageTimes 3 < gerverStageTimes 4
    simp only [gerverStageTimes, Matrix.cons_val]
    linarith
  · show gerverStageTimes 4 < gerverStageTimes 5
    simp only [gerverStageTimes, Matrix.cons_val]
    linarith

/-- The second Gerver stage time is at most `7/10`.  This coarse bound on the certified
switching angle `θ` is what the stage speed estimates below consume. -/
theorem gerverStageTimes_two_le_seven_div_ten : gerverStageTimes 2 ≤ (7 : ℝ) / 10 := by
  have h := GerverSofa.PartB.theta_bounds.2
  rw [gerverStageTimes_two]
  norm_num at h ⊢
  linarith

/-- The first Gerver stage runs between the first two stage times. -/
theorem gerverStageIntervals_zero :
    gerverStageIntervals 0 = Set.Icc (gerverStageTimes 0) (gerverStageTimes 1) := rfl

/-- The second Gerver stage runs between the second and third stage times. -/
theorem gerverStageIntervals_one :
    gerverStageIntervals 1 = Set.Icc (gerverStageTimes 1) (gerverStageTimes 2) := rfl

/-- The fourth Gerver stage runs between the fourth and fifth stage times. -/
theorem gerverStageIntervals_three :
    gerverStageIntervals 3 = Set.Icc (gerverStageTimes 3) (gerverStageTimes 4) := rfl

/-- The fifth Gerver stage runs between the last two stage times. -/
theorem gerverStageIntervals_four :
    gerverStageIntervals 4 = Set.Icc (gerverStageTimes 4) (gerverStageTimes 5) := rfl

/-- The certified direct Gerver path is continuously differentiable. -/
theorem contDiff_paperGerverPath : ContDiff ℝ 1 paperGerverPath := by
  obtain ⟨hC1, -, -⟩ := gerver_direct_path_regularity GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  obtain ⟨L, hL⟩ : ∃ L : GerverSofa.Point →L[ℝ] Point,
      ⇑L = GerverSofa.PartF.Coordinates.toPlane :=
    ⟨{ toLinearMap := GerverSofa.PartF.Coordinates.linearEquiv.toLinearMap
       cont := GerverSofa.PartF.Coordinates.continuous_toPlane }, rfl⟩
  have hcomp : paperGerverPath = ⇑L ∘ GerverSofa.Romik.path GerverSofa.PartB.params := by
    rw [hL]
    rfl
  rw [hcomp]
  exact L.contDiff.comp hC1

/-- Each Gerver contact curve is continuous. -/
theorem continuous_paperGerverContact (i : Fin 4) :
    Continuous fun t : ℝ ↦ paperGerverContacts t i :=
  (continuous_apply i).comp paperGerverContactData_properties.2.1

/-- Each Gerver contact curve is continuously differentiable on each closed stage interval. -/
theorem contDiffOn_paperGerverContact (i : Fin 4) (j : Fin 5) :
    ContDiffOn ℝ 1 (fun t : ℝ ↦ paperGerverContacts t i) (gerverStageIntervals j) :=
  (contDiffOn_pi.mp (paperGerverContactData_properties.2.2.1 j) i).of_le (by norm_num)

/-! ### The two inner contact curves as bounded-variation paths -/

/-- The second Gerver contact curve, on the two stages `[t₃, t₅]` where it is an inner contact
of the cap, as a continuous path of bounded variation. -/
def gerverRightContactBV : ContinuousBVPaths (gerverStageTimes 3) (gerverStageTimes 5) :=
  continuousBVOfContDiffOnIccUnionIcc (fun t ↦ paperGerverContacts t 1)
    (gerverStageTimes_strictMono (show (3 : Fin 6) < 4 by decide)).le
    (gerverStageTimes_strictMono (show (4 : Fin 6) < 5 by decide)).le
    (contDiffOn_paperGerverContact 1 3) (contDiffOn_paperGerverContact 1 4)

/-- The fourth Gerver contact curve, on the two stages `[t₀, t₂]` where it is an inner contact
of the cap, as a continuous path of bounded variation. -/
def gerverLeftContactBV : ContinuousBVPaths (gerverStageTimes 0) (gerverStageTimes 2) :=
  continuousBVOfContDiffOnIccUnionIcc (fun t ↦ paperGerverContacts t 3)
    (gerverStageTimes_strictMono (show (0 : Fin 6) < 1 by decide)).le
    (gerverStageTimes_strictMono (show (1 : Fin 6) < 2 by decide)).le
    (contDiffOn_paperGerverContact 3 0) (contDiffOn_paperGerverContact 3 1)

/-- `gerverRightContactBV` is the second Gerver contact curve. -/
theorem gerverRightContactBV_apply (t : Set.Icc (gerverStageTimes 3) (gerverStageTimes 5)) :
    gerverRightContactBV.val t = paperGerverContacts t 1 := rfl

/-- `gerverLeftContactBV` is the fourth Gerver contact curve. -/
theorem gerverLeftContactBV_apply (t : Set.Icc (gerverStageTimes 0) (gerverStageTimes 2)) :
    gerverLeftContactBV.val t = paperGerverContacts t 3 := rfl

/-! ### Stage derivatives of the two inner contact curves -/

/-- The velocity components are the frame coordinates of the derivative of the direct path. -/
theorem deriv_paperGerverPath_eq_smul_add_smul {t a b : ℝ}
    (h : paperGerverVelocityComponents t = (a, b)) :
    deriv paperGerverPath t =
      a • normalVector (t : Real.Angle) + b • tangentVector (t : Real.Angle) := by
  have hframe := inner_normalVector_smul_add_inner_tangentVector_smul
    (deriv paperGerverPath t) (t : Real.Angle)
  rw [paperGerverVelocityComponents, Prod.mk.injEq] at h
  rw [h.1, h.2] at hframe
  exact hframe.symm

/-- On a stage where the direct path has velocity components `(α, β)`, the second contact
curve `B = x + α v` has derivative `(β + α') v`: the frame derivative `v' = -u` cancels the
normal component `α u` of `x'`, leaving the tangential component `β v` and the derivative of
the coefficient. -/
theorem hasDerivWithinAt_paperGerverContacts_one {i : Fin 5} {t c α' : ℝ} {α β : ℝ → ℝ}
    (ht : t ∈ gerverStageIntervals i) (hα : HasDerivAt α α' t)
    (hαβ : ∀ s ∈ gerverStageIntervals i, paperGerverVelocityComponents s = (α s, β s))
    (hc : β t + α' = c) :
    HasDerivWithinAt (fun s ↦ paperGerverContacts s 1)
      (c • tangentVector (t : Real.Angle)) (gerverStageIntervals i) t := by
  have hx : HasDerivAt paperGerverPath (deriv paperGerverPath t) t :=
    (contDiff_paperGerverPath.differentiable one_ne_zero t).hasDerivAt
  have hd := deriv_paperGerverPath_eq_smul_add_smul (hαβ t ht)
  have hmain : HasDerivAt (fun s ↦ paperGerverPath s + α s • tangentVector (s : Real.Angle))
      (c • tangentVector (t : Real.Angle)) t := by
    have h := hx.add (hα.smul (hasDerivAt_tangentVector t))
    rw [hd] at h
    rw [← hc]
    convert h using 1
    module
  refine hmain.hasDerivWithinAt.congr (fun y hy ↦ ?_) ?_
  · show paperGerverPath y + (paperGerverVelocityComponents y).1 •
      tangentVector (y : Real.Angle) = _
    rw [hαβ y hy]
  · show paperGerverPath t + (paperGerverVelocityComponents t).1 •
      tangentVector (t : Real.Angle) = _
    rw [hαβ t ht]

/-- On a stage where the direct path has velocity components `(α, β)`, the fourth contact
curve `D = x - β u` has derivative `(α - β') u`; see
`hasDerivWithinAt_paperGerverContacts_one` for the shape of the computation. -/
theorem hasDerivWithinAt_paperGerverContacts_three {i : Fin 5} {t c β' : ℝ} {α β : ℝ → ℝ}
    (ht : t ∈ gerverStageIntervals i) (hβ : HasDerivAt β β' t)
    (hαβ : ∀ s ∈ gerverStageIntervals i, paperGerverVelocityComponents s = (α s, β s))
    (hc : α t - β' = c) :
    HasDerivWithinAt (fun s ↦ paperGerverContacts s 3)
      (c • normalVector (t : Real.Angle)) (gerverStageIntervals i) t := by
  have hx : HasDerivAt paperGerverPath (deriv paperGerverPath t) t :=
    (contDiff_paperGerverPath.differentiable one_ne_zero t).hasDerivAt
  have hd := deriv_paperGerverPath_eq_smul_add_smul (hαβ t ht)
  have hmain : HasDerivAt (fun s ↦ paperGerverPath s - β s • normalVector (s : Real.Angle))
      (c • normalVector (t : Real.Angle)) t := by
    have h := hx.sub (hβ.smul (hasDerivAt_normalVector t))
    rw [hd] at h
    rw [← hc]
    convert h using 1
    module
  refine hmain.hasDerivWithinAt.congr (fun y hy ↦ ?_) ?_
  · show paperGerverPath y - (paperGerverVelocityComponents y).2 •
      normalVector (y : Real.Angle) = _
    rw [hαβ y hy]
  · show paperGerverPath t - (paperGerverVelocityComponents t).2 •
      normalVector (t : Real.Angle) = _
    rw [hαβ t ht]

/-- On each of the last two stages the second contact curve moves strictly backwards along
the tangent direction: its one-sided derivative is a negative multiple of `v_t`.  On the
fourth stage the tangential speed is `d₁ - 1 - t/2`, negative because `t ≥ π/2 - θ > 4/5` and
`d₁ ≤ 33/25`; on the fifth it is the exact constant `-1/2`. -/
theorem hasDerivWithinAt_paperGerverContacts_one_neg_smul {i : Fin 5} (hi : i = 3 ∨ i = 4)
    {t : ℝ} (ht : t ∈ gerverStageIntervals i) :
    ∃ c : ℝ, c < 0 ∧
      HasDerivWithinAt (fun s ↦ paperGerverContacts s 1)
        (c • tangentVector (t : Real.Angle)) (gerverStageIntervals i) t := by
  rcases hi with rfl | rfl
  · have hbranch : ∀ s ∈ gerverStageIntervals 3, paperGerverVelocityComponents s =
        ((1 / 4 : ℝ) * s * s - GerverSofa.PartB.params.d1 * s -
            GerverSofa.PartB.params.d2 - 1 / 2,
          2 * GerverSofa.PartB.params.d1 - 1 - s) := by
      intro s hs
      rw [paperGerverContactData_properties.2.2.2 3 s hs]
      rfl
    have hα : HasDerivAt (fun s : ℝ ↦ (1 / 4 : ℝ) * s * s -
        GerverSofa.PartB.params.d1 * s - GerverSofa.PartB.params.d2 - 1 / 2)
        (t / 2 - GerverSofa.PartB.params.d1) t := by
      have h := ((((hasDerivAt_id' t).const_mul (1 / 4 : ℝ)).mul (hasDerivAt_id' t)).sub
        ((hasDerivAt_id' t).const_mul GerverSofa.PartB.params.d1)).sub_const
          GerverSofa.PartB.params.d2 |>.sub_const (1 / 2 : ℝ)
      convert h using 1
      ring
    refine ⟨GerverSofa.PartB.params.d1 - 1 - t / 2, ?_,
      hasDerivWithinAt_paperGerverContacts_one ht hα hbranch (by ring)⟩
    rw [gerverStageIntervals_three] at ht
    have hrefl : gerverStageTimes 3 = Real.pi / 2 - gerverStageTimes 2 := rfl
    linarith [gerverDirectBox_d1_upper_bound GerverSofa.PartB.params_mem,
      gerverStageTimes_two_le_seven_div_ten, ht.1, Real.pi_gt_three]
  · have hbranch : ∀ s ∈ gerverStageIntervals 4, paperGerverVelocityComponents s =
        (1 - 2 * GerverSofa.PartB.params.e1 * Real.sin s +
            2 * GerverSofa.PartB.params.e2 * Real.cos s,
          2 * GerverSofa.PartB.params.e1 * Real.cos s +
            2 * GerverSofa.PartB.params.e2 * Real.sin s - 1 / 2) := by
      intro s hs
      rw [paperGerverContactData_properties.2.2.2 4 s hs]
      rfl
    have hα : HasDerivAt (fun s : ℝ ↦ 1 - 2 * GerverSofa.PartB.params.e1 * Real.sin s +
        2 * GerverSofa.PartB.params.e2 * Real.cos s)
        (-(2 * GerverSofa.PartB.params.e1 * Real.cos t) -
          2 * GerverSofa.PartB.params.e2 * Real.sin t) t := by
      have h := ((hasDerivAt_const t (1 : ℝ)).sub
        ((Real.hasDerivAt_sin t).const_mul (2 * GerverSofa.PartB.params.e1))).add
        ((Real.hasDerivAt_cos t).const_mul (2 * GerverSofa.PartB.params.e2))
      convert h using 1
      ring
    exact ⟨-(1 / 2), by norm_num,
      hasDerivWithinAt_paperGerverContacts_one ht hα hbranch (by ring)⟩

/-- On each of the first two stages the fourth contact curve moves strictly forwards along
the normal direction: its one-sided derivative is a positive multiple of `u_t`.  On the first
stage the normal speed is the exact constant `1/2`; on the second it is `1 + b₁ - t/2`,
positive because `t ≤ θ ≤ 7/10` and `b₁ ≥ -53/100`. -/
theorem hasDerivWithinAt_paperGerverContacts_three_pos_smul {i : Fin 5} (hi : i = 0 ∨ i = 1)
    {t : ℝ} (ht : t ∈ gerverStageIntervals i) :
    ∃ c : ℝ, 0 < c ∧
      HasDerivWithinAt (fun s ↦ paperGerverContacts s 3)
        (c • normalVector (t : Real.Angle)) (gerverStageIntervals i) t := by
  rcases hi with rfl | rfl
  · have hbranch : ∀ s ∈ gerverStageIntervals 0, paperGerverVelocityComponents s =
        (-2 * GerverSofa.PartB.params.a1 * Real.sin s +
            2 * GerverSofa.PartB.params.a2 * Real.cos s + 1 / 2,
          2 * GerverSofa.PartB.params.a1 * Real.cos s +
            2 * GerverSofa.PartB.params.a2 * Real.sin s - 1) := by
      intro s hs
      rw [paperGerverContactData_properties.2.2.2 0 s hs]
      rfl
    have hβ : HasDerivAt (fun s : ℝ ↦ 2 * GerverSofa.PartB.params.a1 * Real.cos s +
        2 * GerverSofa.PartB.params.a2 * Real.sin s - 1)
        (-(2 * GerverSofa.PartB.params.a1 * Real.sin t) +
          2 * GerverSofa.PartB.params.a2 * Real.cos t) t := by
      have h := (((Real.hasDerivAt_cos t).const_mul (2 * GerverSofa.PartB.params.a1)).add
        ((Real.hasDerivAt_sin t).const_mul (2 * GerverSofa.PartB.params.a2))).sub_const (1 : ℝ)
      convert h using 1
      ring
    exact ⟨1 / 2, by norm_num,
      hasDerivWithinAt_paperGerverContacts_three ht hβ hbranch (by ring)⟩
  · have hbranch : ∀ s ∈ gerverStageIntervals 1, paperGerverVelocityComponents s =
        (1 + 2 * GerverSofa.PartB.params.b1 - s,
          -(1 / 4 : ℝ) * s * s + GerverSofa.PartB.params.b1 * s +
            GerverSofa.PartB.params.b2 + 1 / 2) := by
      intro s hs
      rw [paperGerverContactData_properties.2.2.2 1 s hs]
      rfl
    have hβ : HasDerivAt (fun s : ℝ ↦ -(1 / 4 : ℝ) * s * s +
        GerverSofa.PartB.params.b1 * s + GerverSofa.PartB.params.b2 + 1 / 2)
        (-(t / 2) + GerverSofa.PartB.params.b1) t := by
      have h := ((((hasDerivAt_id' t).const_mul (-(1 / 4) : ℝ)).mul (hasDerivAt_id' t)).add
        ((hasDerivAt_id' t).const_mul GerverSofa.PartB.params.b1)).add_const
          GerverSofa.PartB.params.b2 |>.add_const (1 / 2 : ℝ)
      convert h using 1
      ring
    refine ⟨1 + GerverSofa.PartB.params.b1 - t / 2, ?_,
      hasDerivWithinAt_paperGerverContacts_three ht hβ hbranch (by ring)⟩
    rw [gerverStageIntervals_one] at ht
    linarith [gerverDirectBox_b1_lower_bound GerverSofa.PartB.params_mem,
      gerverStageTimes_two_le_seven_div_ten, ht.2]

/-! ### Frame coordinates of the direct path -/

/-- The derivative of the direct Gerver path in the moving frame. -/
theorem hasDerivAt_paperGerverPath_frame (t : ℝ) :
    HasDerivAt paperGerverPath
      ((paperGerverVelocityComponents t).1 • normalVector (t : Real.Angle) +
        (paperGerverVelocityComponents t).2 • tangentVector (t : Real.Angle)) t := by
  have h := (contDiff_paperGerverPath.differentiable one_ne_zero t).hasDerivAt
  rwa [deriv_paperGerverPath_eq_smul_add_smul rfl] at h

/-- The angular derivative of the normal frame coordinate of the Gerver path is the tangent
coordinate of the second contact curve: with `B = x + α v` the frame derivative `u' = v`
contributes `x ⋅ v` and the normal component of `x'` contributes `α`. -/
theorem hasDerivAt_inner_paperGerverPath_normalVector (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (paperGerverPath s) (normalVector (s : Real.Angle)))
      (inner ℝ (paperGerverContacts t 1) (tangentVector (t : Real.Angle))) t := by
  have h := (hasDerivAt_paperGerverPath_frame t).inner ℝ (hasDerivAt_normalVector t)
  convert h using 1
  show inner ℝ (paperGerverPath t + (paperGerverVelocityComponents t).1 •
    tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = _
  rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, inner_tangentVector_self, inner_normalVector_self,
    inner_tangentVector_normalVector_real, sub_self, Real.sin_zero]
  ring

/-- The angular derivative of the tangent frame coordinate of the Gerver path is minus the
normal coordinate of the fourth contact curve: with `D = x - β u` the frame derivative
`v' = -u` contributes `-x ⋅ u` and the tangent component of `x'` contributes `β`. -/
theorem hasDerivAt_inner_paperGerverPath_tangentVector (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (paperGerverPath s) (tangentVector (s : Real.Angle)))
      (-inner ℝ (paperGerverContacts t 3) (normalVector (t : Real.Angle))) t := by
  have h := (hasDerivAt_paperGerverPath_frame t).inner ℝ (hasDerivAt_tangentVector t)
  convert h using 1
  show -inner ℝ (paperGerverPath t - (paperGerverVelocityComponents t).2 •
    normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = _
  rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, inner_neg_right, inner_normalVector_self, inner_tangentVector_self,
    inner_normalVector_tangentVector]
  ring

/-! ### Stagewise monotonicity of the inner contact curves against a fixed direction -/

/-- Against the tangent direction at a later angle `c`, the fourth Gerver contact curve is
strictly antitone on each of its first two stages: its stage speed is a positive multiple of
`u_s`, whose `v_c` coordinate is `sin (s - c) < 0`. -/
theorem strictAntiOn_inner_paperGerverContacts_three {i : Fin 5} (hi : i = 0 ∨ i = 1) {c : ℝ}
    (hlt : ∀ s ∈ gerverStageIntervals i, s < c)
    (hwide : ∀ s ∈ gerverStageIntervals i, c - Real.pi < s) :
    StrictAntiOn (fun s ↦ inner ℝ (paperGerverContacts s 3) (tangentVector (c : Real.Angle)))
      (gerverStageIntervals i) := by
  rw [show gerverStageIntervals i =
    Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ) from rfl] at hlt hwide ⊢
  have hspeed : ∀ s ∈ interior (Set.Icc (gerverStageTimes i.castSucc)
      (gerverStageTimes i.succ)), ∃ cs : ℝ, 0 < cs ∧
      derivWithin (fun r ↦ paperGerverContacts r 3)
          (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s =
        cs • normalVector (s : Real.Angle) ∧
      HasDerivWithinAt (fun r ↦ paperGerverContacts r 3) (cs • normalVector (s : Real.Angle))
        (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s := by
    intro s hs
    obtain ⟨cs, hcs, hder⟩ :=
      hasDerivWithinAt_paperGerverContacts_three_pos_smul hi (interior_subset hs)
    exact ⟨cs, hcs, (hder.mono interior_subset).derivWithin
      (isOpen_interior.uniqueDiffWithinAt hs), hder.mono interior_subset⟩
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
    ((continuous_paperGerverContact 3).continuousOn.inner continuousOn_const)
    (f' := fun s ↦ inner ℝ (derivWithin (fun r ↦ paperGerverContacts r 3)
      (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s)
      (tangentVector (c : Real.Angle))) ?_ ?_
  · intro s hs
    obtain ⟨cs, -, hu, hder⟩ := hspeed s hs
    rw [hu]
    simpa using
      hder.inner ℝ (hasDerivWithinAt_const s _ (tangentVector (c : Real.Angle)))
  · intro s hs
    obtain ⟨cs, hcs, hu, -⟩ := hspeed s hs
    rw [hu, real_inner_smul_left,
      real_inner_comm (tangentVector (c : Real.Angle)) (normalVector (s : Real.Angle)),
      inner_tangentVector_normalVector_real]
    exact mul_neg_of_pos_of_neg hcs (Real.sin_neg_of_neg_of_neg_pi_lt
      (by linarith only [hlt s (interior_subset hs)])
      (by linarith only [hwide s (interior_subset hs)]))

/-- Against the normal direction at an earlier angle `c`, the second Gerver contact curve is
strictly monotone on each of its last two stages: its stage speed is a negative multiple of
`v_s`, whose `u_c` coordinate is `sin (c - s) < 0`. -/
theorem strictMonoOn_inner_paperGerverContacts_one {i : Fin 5} (hi : i = 3 ∨ i = 4) {c : ℝ}
    (hlt : ∀ s ∈ gerverStageIntervals i, c < s)
    (hwide : ∀ s ∈ gerverStageIntervals i, s < c + Real.pi) :
    StrictMonoOn (fun s ↦ inner ℝ (paperGerverContacts s 1) (normalVector (c : Real.Angle)))
      (gerverStageIntervals i) := by
  rw [show gerverStageIntervals i =
    Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ) from rfl] at hlt hwide ⊢
  have hspeed : ∀ s ∈ interior (Set.Icc (gerverStageTimes i.castSucc)
      (gerverStageTimes i.succ)), ∃ cs : ℝ, cs < 0 ∧
      derivWithin (fun r ↦ paperGerverContacts r 1)
          (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s =
        cs • tangentVector (s : Real.Angle) ∧
      HasDerivWithinAt (fun r ↦ paperGerverContacts r 1) (cs • tangentVector (s : Real.Angle))
        (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s := by
    intro s hs
    obtain ⟨cs, hcs, hder⟩ :=
      hasDerivWithinAt_paperGerverContacts_one_neg_smul hi (interior_subset hs)
    exact ⟨cs, hcs, (hder.mono interior_subset).derivWithin
      (isOpen_interior.uniqueDiffWithinAt hs), hder.mono interior_subset⟩
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    ((continuous_paperGerverContact 1).continuousOn.inner continuousOn_const)
    (f' := fun s ↦ inner ℝ (derivWithin (fun r ↦ paperGerverContacts r 1)
      (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s)
      (normalVector (c : Real.Angle))) ?_ ?_
  · intro s hs
    obtain ⟨cs, -, hu, hder⟩ := hspeed s hs
    rw [hu]
    simpa using
      hder.inner ℝ (hasDerivWithinAt_const s _ (normalVector (c : Real.Angle)))
  · intro s hs
    obtain ⟨cs, hcs, hu, -⟩ := hspeed s hs
    rw [hu, real_inner_smul_left, inner_tangentVector_normalVector_real]
    exact mul_pos_of_neg_of_neg hcs (Real.sin_neg_of_neg_of_neg_pi_lt
      (by linarith only [hlt s (interior_subset hs)])
      (by linarith only [hwide s (interior_subset hs)]))

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
# Stage endpoints, grid angles and branch selection

The certificate subdivides each of the five analytic stages of Gerver's sofa into
`NN = 64` equal parts.  This module carries the real-valued mirror of that grid:
`gerverStageTime` re-indexes the six stage endpoints by a natural number,
`gerverGridTime m` is the `m`-th grid angle, `gerverContactPoint` is the dictionary of the
four contact curves and the ambient path, and `GerverAreaCert.stageOf m` is the analytic
branch that the piecewise definitions select at the `m`-th angle.  The soundness statements
`endZ_sound` and `ttZ_sound` say that the integer data of the certificate encloses these
real quantities; the remaining lemmas are the order facts the evaluator needs.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open GerverAreaCert

/-- The six stage endpoints indexed by a natural number, constant past `5`. -/
def gerverStageTime (s : ℕ) : ℝ := gerverStageTimes ⟨min 5 s, by omega⟩

/-- The real grid angle at index `m`, mirroring `GerverAreaCert.ttZ`. -/
def gerverGridTime (m : ℕ) : ℝ :=
  (((NN - m % NN : ℕ) : ℝ) * gerverStageTime (m / NN) +
    ((m % NN : ℕ) : ℝ) * gerverStageTime (m / NN + 1)) / (NN : ℝ)

/-- The curve selected by a certificate `kind`: `0` the path, `1` `A`, `2` `B`, `3` `C`,
`4` `D`. -/
def gerverContactPoint : ℕ → ℝ → Point
  | 0 => paperGerverPath
  | 1 => fun t ↦ paperGerverContacts t 0
  | 2 => fun t ↦ paperGerverContacts t 1
  | 3 => fun t ↦ paperGerverContacts t 2
  | _ => fun t ↦ paperGerverContacts t 3

/-- The rotation interval starts at the first stage endpoint `0`. -/
theorem gerverStageTime_zero : gerverStageTime 0 = 0 := gerverStageTimes_zero

/-- The first stage ends at `φ`. -/
theorem gerverStageTime_one : gerverStageTime 1 = GerverSofa.PartB.params.phi :=
  gerverStageTimes_one

/-- The second stage ends at `θ`. -/
theorem gerverStageTime_two : gerverStageTime 2 = GerverSofa.PartB.params.theta :=
  gerverStageTimes_two

/-- The third stage ends at `η = π / 2 - θ`. -/
theorem gerverStageTime_three : gerverStageTime 3 = GerverSofa.PartC.eta :=
  gerverStageTimes_three

/-- The fourth stage ends at `τ = π / 2 - φ`. -/
theorem gerverStageTime_four : gerverStageTime 4 = GerverSofa.PartC.tau :=
  gerverStageTimes_four

/-- The fifth stage ends at `π / 2`. -/
theorem gerverStageTime_five : gerverStageTime 5 = Real.pi / 2 := gerverStageTimes_five

/-! ### Order properties of the stage endpoints and the grid -/

/-- The five stage endpoints are strictly increasing. -/
theorem gerverStageTime_lt_succ (s : ℕ) (hs : s < 5) :
    gerverStageTime s < gerverStageTime (s + 1) := by
  refine gerverStageTimes_strictMono ?_
  simp only [Fin.mk_lt_mk]
  omega

/-- Past index `5` the `ℕ`-indexed stage endpoint is constantly `π / 2`. -/
private theorem gerverStageTime_of_five_le {s : ℕ} (hs : 5 ≤ s) :
    gerverStageTime s = Real.pi / 2 := by
  simp only [gerverStageTime, min_eq_left hs]
  exact gerverStageTimes_five

/-- The stage-endpoint enclosure at every index, including those past `5`. -/
private theorem endZ_sound_all (s : ℕ) : SI.Contains (endZ s) (gerverStageTime s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hphi, htheta⟩ :=
    contains_params
  rcases s with _ | _ | _ | _ | _ | _ | n
  · rw [gerverStageTime_zero]
    exact SI.contains_zero
  · rw [gerverStageTime_one]
    exact hphi
  · rw [gerverStageTime_two]
    exact htheta
  · rw [show gerverStageTime 3 = Real.pi / 2 - GerverSofa.PartB.params.theta from
      gerverStageTime_three]
    exact SI.contains_sub contains_piHalfZ htheta
  · rw [show gerverStageTime 4 = Real.pi / 2 - GerverSofa.PartB.params.phi from
      gerverStageTime_four]
    exact SI.contains_sub contains_piHalfZ hphi
  · rw [gerverStageTime_five]
    exact contains_piHalfZ
  · rw [gerverStageTime_of_five_le (s := n + 6) (by omega)]
    exact contains_piHalfZ

/-- The integer stage endpoints enclose the real ones. -/
theorem endZ_sound (s : ℕ) (hs : s ≤ 5) : SI.Contains (endZ s) (gerverStageTime s) := by
  interval_cases s <;> exact endZ_sound_all _

/-- The integer grid angles enclose the real ones. -/
theorem ttZ_sound (m : ℕ) (hm : m ≤ 5 * NN) : SI.Contains (ttZ m) (gerverGridTime m) := by
  have hNN : (0 : ℤ) < (NN : ℤ) := by norm_num [NN]
  have hdiv : m / NN ≤ 5 := by
    rw [show NN = 64 from rfl] at hm ⊢
    omega
  have key : SI.Contains
      (SI.add (SI.imul ((NN - m % NN : ℕ) : ℤ) (endZ (m / NN)))
        (SI.imul ((m % NN : ℕ) : ℤ) (endZ (m / NN + 1))))
      (((NN - m % NN : ℕ) : ℝ) * gerverStageTime (m / NN) +
        ((m % NN : ℕ) : ℝ) * gerverStageTime (m / NN + 1)) := by
    refine SI.contains_add ?_ ?_
    · have h := SI.contains_imul ((NN - m % NN : ℕ) : ℤ) (endZ_sound (m / NN) hdiv)
      rwa [Int.cast_natCast] at h
    · have h := SI.contains_imul ((m % NN : ℕ) : ℤ) (endZ_sound_all (m / NN + 1))
      rwa [Int.cast_natCast] at h
  have hcast : (((NN : ℤ)) : ℝ) = (NN : ℝ) := by push_cast; ring
  rw [gerverGridTime, ← hcast]
  exact SI.contains_divn hNN key

/-- The grid step is uniform across stage joins. -/
theorem gerverGridTime_succ_sub (m : ℕ) :
    gerverGridTime (m + 1) - gerverGridTime m =
      (gerverStageTime (m / NN + 1) - gerverStageTime (m / NN)) / (NN : ℝ) := by
  have hNNR : (0 : ℝ) < (NN : ℝ) := by norm_num [NN]
  have hr : m % NN < NN := Nat.mod_lt _ (by norm_num [NN])
  have hsplit : ((m + 1) % NN = m % NN + 1 ∧ (m + 1) / NN = m / NN) ∨
      (m % NN + 1 = NN ∧ (m + 1) % NN = 0 ∧ (m + 1) / NN = m / NN + 1) := by
    rw [show NN = 64 from rfl]
    omega
  rcases hsplit with ⟨hmod, hdiv⟩ | ⟨hfull, hmod, hdiv⟩
  · rw [gerverGridTime, gerverGridTime, hmod, hdiv,
      Nat.cast_sub (by omega : m % NN + 1 ≤ NN), Nat.cast_sub hr.le]
    push_cast
    field_simp
    ring
  · rw [gerverGridTime, gerverGridTime, hmod, hdiv, Nat.cast_sub hr.le]
    have hrR : ((m % NN : ℕ) : ℝ) = (NN : ℝ) - 1 := by
      have : ((m % NN + 1 : ℕ) : ℝ) = ((NN : ℕ) : ℝ) := by rw [hfull]
      push_cast at this
      linarith
    rw [hrR]
    simp only [Nat.sub_zero]
    push_cast
    field_simp
    ring

/-- The grid angles are strictly increasing. -/
theorem gerverGridTime_lt_succ (m : ℕ) (hm : m < 5 * NN) :
    gerverGridTime m < gerverGridTime (m + 1) := by
  have hNNR : (0 : ℝ) < (NN : ℝ) := by norm_num [NN]
  have hlt : m / NN < 5 := (Nat.div_lt_iff_lt_mul (by norm_num [NN])).mpr hm
  have hstep := gerverGridTime_succ_sub m
  have hstage := gerverStageTime_lt_succ (m / NN) hlt
  have hpos : 0 < (gerverStageTime (m / NN + 1) - gerverStageTime (m / NN)) / (NN : ℝ) :=
    div_pos (by linarith) hNNR
  linarith

/-- Strict monotonicity of the grid angles below the top index, from `gerverGridTime_lt_succ`. -/
theorem gerverGridTime_lt_of_lt {m n : ℕ} (hmn : m < n) (hn : n ≤ 5 * NN) :
    gerverGridTime m < gerverGridTime n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hmn with h | h
    · exact (ih h (by omega)).trans (gerverGridTime_lt_succ n (by omega))
    · subst h
      exact gerverGridTime_lt_succ m (by omega)

/-- Weak monotonicity of the grid angles below the top index, from `gerverGridTime_lt_succ`. -/
theorem gerverGridTime_le_of_le {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ 5 * NN) :
    gerverGridTime m ≤ gerverGridTime n := by
  rcases eq_or_lt_of_le hmn with rfl | h
  · exact le_rfl
  · exact (gerverGridTime_lt_of_lt h hn).le

/-- The grid angle at a stage boundary is the stage endpoint itself. -/
theorem gerverGridTime_mul_NN (s : ℕ) : gerverGridTime (s * NN) = gerverStageTime s := by
  have hNN : 0 < NN := by norm_num [NN]
  have hne : (NN : ℝ) ≠ 0 := by norm_num [NN]
  rw [gerverGridTime, Nat.mul_mod_left, Nat.mul_div_cancel _ hNN]
  simp only [Nat.sub_zero, Nat.cast_zero, zero_mul, add_zero]
  exact mul_div_cancel_left₀ _ hne

/-- The grid starts at `0`. -/
theorem gerverGridTime_zero : gerverGridTime 0 = 0 := by
  have h := gerverGridTime_mul_NN 0
  rw [zero_mul] at h
  rw [h, gerverStageTime_zero]

/-- The grid ends at `π / 2`. -/
theorem gerverGridTime_top : gerverGridTime (5 * NN) = Real.pi / 2 := by
  rw [gerverGridTime_mul_NN 5, gerverStageTime_five]

/-- Every grid angle lies in the rotation interval. -/
theorem gerverGridTime_mem_Icc (m : ℕ) (hm : m ≤ 5 * NN) :
    gerverGridTime m ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
  refine ⟨?_, ?_⟩
  · rw [← gerverGridTime_zero]
    exact gerverGridTime_le_of_le (Nat.zero_le m) hm
  · rw [← gerverGridTime_top]
    exact gerverGridTime_le_of_le hm le_rfl

/-- The branch index is one of the five stages. -/
theorem stageOf_mem (m : ℕ) (hm : m ≤ 5 * NN) : 1 ≤ stageOf m ∧ stageOf m ≤ 5 := by
  have hNN : 0 < NN := by norm_num [NN]
  have hd : m / NN ≤ 5 := Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hm)
  rw [stageOf]
  split_ifs with h
  · exact ⟨le_max_left _ _, max_le (by omega) hd⟩
  · have hmlt : m < 5 * NN := by
      rcases lt_or_eq_of_le hm with h' | h'
      · exact h'
      · subst h'; exact absurd (Nat.mul_mod_left 5 NN) h
    have hd4 : m / NN < 5 := (Nat.div_lt_iff_lt_mul hNN).mpr hmlt
    exact ⟨Nat.le_add_left 1 _, hd4⟩

/-- The grid angle does not exceed the right endpoint of its branch. -/
theorem gerverGridTime_le_stageTime (m : ℕ) (hm : m ≤ 5 * NN) :
    gerverGridTime m ≤ gerverStageTime (stageOf m) := by
  have hNN : 0 < NN := by norm_num [NN]
  rw [stageOf]
  split_ifs with h
  · have hmm : m / NN * NN = m := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
    have key : gerverGridTime m = gerverStageTime (m / NN) := by
      have h' := gerverGridTime_mul_NN (m / NN)
      rwa [hmm] at h'
    rcases Nat.eq_zero_or_pos (m / NN) with h0 | h0
    · have hm0 : m = 0 := by rw [← hmm, h0, zero_mul]
      rw [h0, show max 1 0 = 1 from rfl, hm0, gerverGridTime_zero]
      have h01 := gerverStageTime_lt_succ 0 (by norm_num)
      rw [gerverStageTime_zero] at h01
      exact h01.le
    · rw [max_eq_right h0, key]
  · have hmlt : m < 5 * NN := by
      rcases lt_or_eq_of_le hm with h' | h'
      · exact h'
      · subst h'; exact absurd (Nat.mul_mod_left 5 NN) h
    have hd4 : m / NN < 5 := (Nat.div_lt_iff_lt_mul hNN).mpr hmlt
    have hlt : m < (m / NN + 1) * NN := (Nat.div_lt_iff_lt_mul hNN).mp (Nat.lt_succ_self _)
    have hub : (m / NN + 1) * NN ≤ 5 * NN := Nat.mul_le_mul_right NN hd4
    calc gerverGridTime m ≤ gerverGridTime ((m / NN + 1) * NN) :=
          gerverGridTime_le_of_le hlt.le hub
      _ = gerverStageTime (m / NN + 1) := gerverGridTime_mul_NN _

/-- The grid angle strictly exceeds the left endpoint of its branch, except on the
first branch. -/
theorem stageTime_lt_gerverGridTime (m : ℕ) (hm : m ≤ 5 * NN) (h2 : 2 ≤ stageOf m) :
    gerverStageTime (stageOf m - 1) < gerverGridTime m := by
  have hNN : 0 < NN := by norm_num [NN]
  have hd5 : m / NN ≤ 5 := Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hm)
  rw [stageOf] at h2 ⊢
  split_ifs at h2 ⊢ with h
  · have hd : 2 ≤ m / NN := by
      rcases le_max_iff.mp h2 with h' | h'
      · exact absurd h' (by norm_num)
      · exact h'
    have hpos : 0 < m / NN := lt_of_lt_of_le (by norm_num) hd
    have hmm : m / NN * NN = m := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
    have key : gerverGridTime m = gerverStageTime (m / NN) := by
      have h' := gerverGridTime_mul_NN (m / NN)
      rwa [hmm] at h'
    rw [max_eq_right (Nat.le_of_succ_le hd), key]
    have h4 : m / NN - 1 < 5 := lt_of_le_of_lt (Nat.sub_le_sub_right hd5 1) (by norm_num)
    have hlt := gerverStageTime_lt_succ (m / NN - 1) h4
    rwa [Nat.sub_add_cancel hpos] at hlt
  · rw [Nat.add_sub_cancel]
    have hle : m / NN * NN ≤ m := Nat.div_mul_le_self m NN
    have hne : m / NN * NN ≠ m := by
      intro he
      exact h (by rw [← he]; exact Nat.mul_mod_left _ _)
    have key : gerverGridTime (m / NN * NN) = gerverStageTime (m / NN) := gerverGridTime_mul_NN _
    rw [← key]
    exact gerverGridTime_lt_of_lt (lt_of_le_of_ne hle hne) hm

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
# Properties of the Gerver niche roof

The main results of this file describe the upper boundary of the paper's literal Gerver
niche: the three graph pieces join up (`gerver_niche_piece_endpoints`), each piece stays
inside the outer cap (`gerver_niche_roof_membership`), the roof is a strictly monotone
positive graph (`gerver_niche_roof_strictMono`, `gerver_niche_roof_positive`), and the
niche is exactly the strict vertical region under that roof (`gerver_niche_vertical_fills`).
The three pieces are identified branch by branch in `gerverNicheRoof_of_le_two`,
`gerverNicheRoof_mid` and `gerverNicheRoof_of_ge_three`, each valid on the closed stage.

Alongside them sits the elementary API of the reverse-time reparametrization
(`continuous_gerverRoofReverseTime`, `gerverRoofReverseTime_two`,
`gerverRoofReverseTime_three`, `gerverRoofReverseTime_mem_Icc`) and the continuity of the
roof, in both its real-parameter and its restricted form (`continuous_gerverRoofCurve`,
`continuous_gerverNicheRoof`).

Every one of them is the certified Part C niche geometry read through the coordinate
dictionary `GerverSofa.PartF.Coordinates.toPlane`.  The dictionary itself is supplied by
the public readers of the lower modules — `paperGerverContacts_one_eq_toPlane` and
`paperGerverContacts_three_eq_toPlane` for the contact curves, `gerverStageTimes_zero`
through `gerverStageTimes_five` for the stage times, and `mem_gerverLiteralNiche_iff`,
`toPlane_mem_gerverOuterCap` for the two literal sets.  What remains here, and is kept
private, is the roof-specific part of the dictionary: the reverse-time reparametrization
and the identification of `gerverNicheRoof` with the certified upper arc.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

section Roof

open GerverSofa.PartF.Coordinates
open GerverSofa.PartC (params eta tau)

/-- The roof reverse-time reparametrization is the certified affine reversal of the core
stage, which sends `params.theta` to `tau` and `eta` to `params.phi`. -/
private theorem gerverRoofReverseTime_eq (s : ℝ) :
    gerverRoofReverseTime s = GerverSofa.PartC.Stage4.coreReverseTime s := by
  rw [gerverRoofReverseTime, gerverStageTimes_four, gerverStageTimes_one,
    gerverStageTimes_three, gerverStageTimes_two]
  rfl

/-- The Gerver roof is the certified upper niche arc, read in plane coordinates.  The three
branches of `gerverNicheRoof` match the three branches of `nicheTopArc` piece for piece,
with the same cut points `params.theta` and `eta`. -/
private theorem gerverNicheRoof_eq_toPlane (s : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    gerverNicheRoof s = toPlane (GerverSofa.PartC.Stage4.nicheTopArc s.val) := by
  have hsI : (s : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := s.2
  simp only [gerverNicheRoof, GerverSofa.PartC.Stage4.nicheTopArc, gerverStageTimes_two,
    gerverStageTimes_three, gerverRoofReverseTime_eq]
  split_ifs with h1 h2
  · exact paperGerverContacts_three_eq_toPlane hsI
  · rfl
  · exact paperGerverContacts_one_eq_toPlane hsI

end Roof

/-- The three graph pieces of the niche roof join up: the second contact curve at `eta`
meets the ambient path at `params.phi`, the fourth contact curve at `params.theta` meets
the ambient path at `tau`, and the two outer ends touch the wall. -/
theorem gerver_niche_piece_endpoints :
    paperGerverContacts (gerverStageTimes 3) 1 = paperGerverPath (gerverStageTimes 1) ∧
    paperGerverContacts (gerverStageTimes 2) 3 = paperGerverPath (gerverStageTimes 4) ∧
    paperGerverContacts (Real.pi / 2) 1 1 = 0 ∧ paperGerverContacts 0 3 1 = 0 := by
  open GerverSofa.PartF.Coordinates GerverSofa.PartC GerverSofa.PartC.Stage4 in
  obtain ⟨hB, hD, hBT, hD0⟩ := GerverSofa.PartC.Stage4.niche_piece_endpoints
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hTeq : GerverSofa.PartC.T = Real.pi / 2 := rfl
  have hchain : 0 < params.theta ∧ params.theta < eta ∧ eta < tau ∧ tau < Real.pi / 2 :=
    ⟨GerverSofa.PartC.Stage4.theta_pos, GerverSofa.PartC.Stage4.theta_lt_eta,
      GerverSofa.PartC.Stage4.eta_lt_tau, hTeq ▸ GerverSofa.PartC.Stage4.tau_lt_T⟩
  obtain ⟨hθ0, hθη, hητ, hτT⟩ := hchain
  have hth : params.theta ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hθ0.le, by linarith⟩
  have heta : eta ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hTm : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hpi.le, le_rfl⟩
  have h0m : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, hpi.le⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gerverStageTimes_three, gerverStageTimes_one,
      paperGerverContacts_one_eq_toPlane heta, paperGerverPath_eq_toPlane]
    exact congrArg toPlane hB
  · rw [gerverStageTimes_two, gerverStageTimes_four,
      paperGerverContacts_three_eq_toPlane hth, paperGerverPath_eq_toPlane]
    exact congrArg toPlane hD
  · rw [paperGerverContacts_one_eq_toPlane hTm]
    exact hBT
  · rw [paperGerverContacts_three_eq_toPlane h0m]
    exact hD0

/-! ## The reverse-time reparametrization, and continuity of the roof -/

/-- The reverse-time reparametrization is affine, hence continuous. -/
theorem continuous_gerverRoofReverseTime : Continuous gerverRoofReverseTime := by
  unfold gerverRoofReverseTime
  fun_prop

/-- The reverse-time map sends the start of the middle roof stage to the late path time. -/
theorem gerverRoofReverseTime_two :
    gerverRoofReverseTime (gerverStageTimes 2) = gerverStageTimes 4 := by
  rw [gerverRoofReverseTime, sub_self, mul_zero, sub_zero]

/-- The reverse-time map sends the end of the middle roof stage to the early path time. -/
theorem gerverRoofReverseTime_three :
    gerverRoofReverseTime (gerverStageTimes 3) = gerverStageTimes 1 := by
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  rw [gerverRoofReverseTime, div_mul_cancel₀ _ (sub_ne_zero.mpr h23.ne')]
  ring

/-- The reverse-time map carries the middle roof interval into the central path interval. -/
theorem gerverRoofReverseTime_mem_Icc {s : ℝ} (h1 : gerverStageTimes 2 ≤ s)
    (h2 : s ≤ gerverStageTimes 3) :
    gerverRoofReverseTime s ∈ Set.Icc (gerverStageTimes 1) (gerverStageTimes 4) := by
  have h12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_strictMono (by decide)
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  have h34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_strictMono (by decide)
  have hd : (0 : ℝ) < gerverStageTimes 3 - gerverStageTimes 2 := by linarith
  have hL : 0 < (gerverStageTimes 4 - gerverStageTimes 1) /
      (gerverStageTimes 3 - gerverStageTimes 2) := div_pos (by linarith) hd
  have hmul := mul_le_mul_of_nonneg_left (show s - gerverStageTimes 2 ≤
    gerverStageTimes 3 - gerverStageTimes 2 by linarith) hL.le
  rw [div_mul_cancel₀ _ hd.ne'] at hmul
  have hnn : 0 ≤ (gerverStageTimes 4 - gerverStageTimes 1) /
      (gerverStageTimes 3 - gerverStageTimes 2) * (s - gerverStageTimes 2) :=
    mul_nonneg hL.le (by linarith)
  rw [gerverRoofReverseTime]
  constructor <;> linarith

/-! ## The three graph pieces of the roof -/

/-- Up to the second stage time the niche roof is the fourth contact curve. -/
theorem gerverNicheRoof_of_le_two {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h : s ≤ gerverStageTimes 2) : gerverNicheRoof ⟨s, hs⟩ = paperGerverContacts s 3 :=
  ite_eq_left h

/-- On the middle stage the niche roof is the reverse-time ambient path.  The identification
extends to the left endpoint of the stage by the piece-endpoint gluing. -/
theorem gerverNicheRoof_mid {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h1 : gerverStageTimes 2 ≤ s) (h2 : s ≤ gerverStageTimes 3) :
    gerverNicheRoof ⟨s, hs⟩ = paperGerverPath (gerverRoofReverseTime s) := by
  rcases eq_or_lt_of_le h1 with heq | hlt
  · rw [gerverNicheRoof_of_le_two hs heq.ge, ← heq, gerverRoofReverseTime_two]
    exact gerver_niche_piece_endpoints.2.1
  · rw [gerverNicheRoof, ite_eq_right (not_le.mpr hlt), ite_eq_left h2]

/-- From the third stage time on the niche roof is the second contact curve.  The
identification extends to the left endpoint of the stage by the piece-endpoint gluing. -/
theorem gerverNicheRoof_of_ge_three {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h : gerverStageTimes 3 ≤ s) : gerverNicheRoof ⟨s, hs⟩ = paperGerverContacts s 1 := by
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [gerverNicheRoof_mid hs (by linarith) heq.ge, ← heq, gerverRoofReverseTime_three]
    exact gerver_niche_piece_endpoints.1.symm
  · rw [gerverNicheRoof, ite_eq_right (not_le.mpr (by linarith)),
      ite_eq_right (not_le.mpr hlt)]

/-- On the rotation interval the real-parameter roof curve is the niche roof. -/
theorem gerverRoofCurve_eq (s : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    gerverRoofCurve s.val = gerverNicheRoof s := rfl

/-- The roof curve is continuous: its three graph pieces join up at the two cut times, by the
two endpoint identities of `gerver_niche_piece_endpoints`. -/
theorem continuous_gerverRoofCurve : Continuous gerverRoofCurve := by
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  have hinner : Continuous fun s : ℝ ↦
      if s ≤ gerverStageTimes 3 then paperGerverPath (gerverRoofReverseTime s)
      else paperGerverContacts s 1 := by
    refine continuous_if_le continuous_id continuous_const
      ((contDiff_paperGerverPath.continuous.comp continuous_gerverRoofReverseTime).continuousOn)
      ((continuous_paperGerverContact 1).continuousOn) ?_
    intro s hs
    rw [hs, gerverRoofReverseTime_three]
    exact gerver_niche_piece_endpoints.1.symm
  refine continuous_if_le continuous_id continuous_const
    ((continuous_paperGerverContact 3).continuousOn) hinner.continuousOn ?_
  intro s hs
  rw [ite_eq_left (by rw [hs]; exact h23.le), hs, gerverRoofReverseTime_two]
  exact gerver_niche_piece_endpoints.2.1

/-- The niche roof is continuous. -/
theorem continuous_gerverNicheRoof : Continuous gerverNicheRoof :=
  continuous_gerverRoofCurve.comp continuous_subtype_val

/-- The first coordinate of the niche roof is strictly increasing, so the roof really is a
graph over the horizontal axis. -/
theorem gerver_niche_roof_strictMono :
    StrictMono (fun s : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ gerverNicheRoof s 0) := by
  intro a b hab
  have h := GerverSofa.PartC.Stage4.nicheTopArc_fst_strictMono a.2 b.2 hab
  simp only [gerverNicheRoof_eq_toPlane]
  exact h

/-- The niche roof has positive height strictly inside the rotation interval. -/
theorem gerver_niche_roof_positive
    (s : Set.Icc (0 : ℝ) (Real.pi / 2)) (hs : 0 < s.val ∧ s.val < Real.pi / 2) :
    0 < gerverNicheRoof s 1 := by
  rw [gerverNicheRoof_eq_toPlane]
  exact GerverSofa.PartC.Stage4.nicheTopArc_y_pos ⟨hs.1, hs.2⟩

/-- Each of the three graph pieces of the niche roof stays inside the paper outer cap. -/
theorem gerver_niche_roof_membership :
    (∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      paperGerverContacts t 3 ∈ gerverOuterCap) ∧
    (∀ t ∈ Set.Icc (gerverStageTimes 1) (gerverStageTimes 4),
      paperGerverPath t ∈ gerverOuterCap) ∧
    (∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      paperGerverContacts t 1 ∈ gerverOuterCap) := by
  open GerverSofa.PartF.Coordinates GerverSofa.PartC GerverSofa.PartC.Stage4 in
  obtain ⟨hD, hx, hB⟩ := GerverSofa.PartC.Stage4.certified_roof_mem_K
  have hTeq : GerverSofa.PartC.T = Real.pi / 2 := rfl
  have hθ0 : 0 < params.theta := GerverSofa.PartC.Stage4.theta_pos
  have hθη : params.theta < eta := GerverSofa.PartC.Stage4.theta_lt_eta
  have hητ : eta < tau := GerverSofa.PartC.Stage4.eta_lt_tau
  have hτT : tau < Real.pi / 2 := hTeq ▸ GerverSofa.PartC.Stage4.tau_lt_T
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [gerverStageTimes_zero, gerverStageTimes_two] at ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨ht.1, by linarith [ht.2]⟩
    rw [paperGerverContacts_three_eq_toPlane htI]
    exact toPlane_mem_gerverOuterCap (hD t ht)
  · intro t ht
    rw [gerverStageTimes_one, gerverStageTimes_four] at ht
    exact toPlane_mem_gerverOuterCap (hx t ht)
  · intro t ht
    rw [gerverStageTimes_three, gerverStageTimes_five] at ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [ht.1], hTeq ▸ ht.2⟩
    rw [paperGerverContacts_one_eq_toPlane htI]
    exact toPlane_mem_gerverOuterCap (hB t ht)

/-- The strict region between the wall and the graph of `f` over the parameter set `I`. -/
def strictVerticalFill (f : ℝ → Point) (I : Set ℝ) : Set Point :=
  {q | ∃ t ∈ I, q 0 = f t 0 ∧ 0 ≤ q 1 ∧ q 1 < f t 1}

section Fills

open GerverSofa.PartF.Coordinates
open GerverSofa.PartC (params eta tau)

/-- A strict vertical fill is the coordinate preimage of the certified vertical fill under
the plane dictionary. -/
private theorem strictVerticalFill_eq_preimage {F : ℝ → Point} {g : ℝ → GerverSofa.Point}
    {I : Set ℝ} (h : ∀ t ∈ I, F t = toPlane (g t)) :
    strictVerticalFill F I = fromPlane ⁻¹' GerverSofa.PartC.Stage4.verticalFill g I := by
  ext q
  constructor
  · rintro ⟨t, ht, h0, h1, h2⟩
    rw [h t ht] at h0 h2
    exact ⟨t, ht, h0, h1, h2⟩
  · rintro ⟨t, ht, h0, h1, h2⟩
    refine ⟨t, ht, ?_, h1, ?_⟩
    · rw [h t ht]; exact h0
    · rw [h t ht]; exact h2

end Fills

/-- The paper literal niche is exactly the union of the three strict vertical fills under
the three graph pieces of the niche roof. -/
theorem gerver_niche_vertical_fills :
    gerverLiteralNiche =
      strictVerticalFill (fun t ↦ paperGerverContacts t 3)
        (Set.Icc (gerverStageTimes 0) (gerverStageTimes 2)) ∪
      strictVerticalFill paperGerverPath
        (Set.Icc (gerverStageTimes 1) (gerverStageTimes 4)) ∪
      strictVerticalFill (fun t ↦ paperGerverContacts t 1)
        (Set.Icc (gerverStageTimes 3) (gerverStageTimes 5)) := by
  open GerverSofa.PartF.Coordinates GerverSofa.PartC GerverSofa.PartC.Stage4 in
  have hTeq : GerverSofa.PartC.T = Real.pi / 2 := rfl
  have hθ0 : 0 < params.theta := GerverSofa.PartC.Stage4.theta_pos
  have hθη : params.theta < eta := GerverSofa.PartC.Stage4.theta_lt_eta
  have hητ : eta < tau := GerverSofa.PartC.Stage4.eta_lt_tau
  have hτT : tau < Real.pi / 2 := hTeq ▸ GerverSofa.PartC.Stage4.tau_lt_T
  have hDeq : ∀ t ∈ Set.Icc (0 : ℝ) params.theta,
      (fun t ↦ paperGerverContacts t 3) t = toPlane (GerverSofa.PartC.D t) := fun t ht =>
    paperGerverContacts_three_eq_toPlane ⟨ht.1, by linarith [ht.2]⟩
  have hpeq : ∀ t ∈ Set.Icc params.phi tau,
      paperGerverPath t = toPlane (GerverSofa.Romik.path params t) := fun _ _ => rfl
  have hBeq : ∀ t ∈ Set.Icc eta GerverSofa.PartC.T,
      (fun t ↦ paperGerverContacts t 1) t = toPlane (GerverSofa.PartC.B t) := fun t ht =>
    paperGerverContacts_one_eq_toPlane ⟨by linarith [ht.1], hTeq ▸ ht.2⟩
  rw [gerverStageTimes_zero, gerverStageTimes_two, gerverStageTimes_one, gerverStageTimes_four,
    gerverStageTimes_three, gerverStageTimes_five, strictVerticalFill_eq_preimage hDeq,
    strictVerticalFill_eq_preimage hpeq, strictVerticalFill_eq_preimage hBeq,
    ← Set.preimage_union, ← Set.preimage_union]
  exact Set.ext fun q =>
    (mem_gerverLiteralNiche_iff q).trans
      (by rw [GerverSofa.PartC.Stage4.niche_eq_certifiedNicheRegion]; rfl)

end MovingSofa

end

end

end
