/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Main.SerrinInteriorEstimates
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import LeanPool.CIVAxisymmetric.Statements.GlobalEnergyClass
public import LeanPool.CIVAxisymmetric.Statements.MultiPartial
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder

/-!
# Serrin Interior Estimates

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- Serrin's interior estimates, in the form in which the proof of `lem:aniso:annulus`
consumes them (Serrin 1962, Section 4 with `m = 1`): on a cylindrical annulus
`{Rm < |x| < Rp} × (t₀, 0)` inside `Q` on which the velocity is bounded, and with the force
bounded in `C²_x`, the velocity and its spatial derivatives through order two are bounded on
every smaller annulus `{Rm' < |x| < Rp'} × (t₀', 0)`, uniformly up to the blow-up time.

The bound `K` is produced after all the data, so no uniformity is asserted: the manuscript's
constants "depend only on the subset, on `M_f`, on `sup |u|` over the cylindrical annulus, and
on `‖∇u‖_{L²(Q)}`" (proof of `lem:aniso:annulus`), and the consumers fix the annulus before every other parameter.
The `L²(Q)` gradient norm and the pressure up to `t = 0` come from `henergy`, not from `hsol`,
whose integrability clauses only see boxes compactly contained in `Q` (design note R6).
The shrinking of the time interval is the manuscript's own `t₀ ↦ t₀ + ϱ²`.

This statement bundles Serrin's printed estimates with the manuscript's argument that
they are uniform up to `t = 0`, because his representation formulas are one-sided in time.
The force is the manuscript's own `f`: the correction of `foot:aniso:pressure` is not used here
("the derivative estimates ... are written with `f` itself", footnote `foot:aniso:pressure`). The proof uses fewer inputs
than listed here; see deviation D13 in `docs/DEVIATIONS.md`. -/
theorem serrinInteriorEstimates (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f)
    (Rm Rp t₀ : ℝ) (hR : 0 ≤ Rm ∧ Rm < Rp ∧ Rp ≤ 1) (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    (Mu : ℝ) (hbdd : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ 0, vec3EuclideanNorm (u (x, t)) ≤ Mu)
    (Rm' Rp' t₀' : ℝ) (hR' : Rm < Rm' ∧ Rm' < Rp' ∧ Rp' < Rp) (ht₀' : t₀ < t₀' ∧ t₀' < 0) :
    ∃ K : ℝ, ∀ x : Vec3, Rm' < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp' →
      ∀ t ∈ Ioo t₀' 0, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ K := by
  exact CIV.Main.serrinInteriorEstimates q u Du p f hsol henergy hu hp hf hMf Rm Rp t₀ hR ht₀
    Mu hbdd Rm' Rp' t₀' hR' ht₀'

end CIV
