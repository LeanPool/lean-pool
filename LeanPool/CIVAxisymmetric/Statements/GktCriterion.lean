/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Main.GktCriterion
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CIVAxisymmetric.Statements.BoundedNearOrigin
public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import LeanPool.CIVAxisymmetric.Statements.GlobalEnergyClass
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder

/-!
# Gkt Criterion

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The interior regularity criterion of Gustafson, Kang and Tsai (their Theorem 1.1(i) with
`p_* = 6`, `q = 4`), in the form in which the proof of `lem:aniso:closure` consumes it: if the
`L⁴_t L⁶_x` norm of the velocity on the backward cylinders
`B(r) × (−r², 0)` tends to zero as `r → 0`, then `(0,0)` is a regular point, that is, `u` is
bounded on a backward cylinder at the origin (design note R3).

The hypothesis is the fourth power of `‖u‖_{L⁴(−r²,0;L⁶(B(r)))}`, which tends to zero exactly
when the norm does. It is stronger than the smallness that Gustafson, Kang and Tsai 2007
requires, and it is what the
proof of `lem:aniso:closure` produces.

This statement bundles three things:
the criterion itself; its application at the top boundary point `(0,0)`, which the footnote in the
proof of `lem:aniso:annulus` justifies from the structure of the proof in Gustafson, Kang and
Tsai 2007 (backward cylinders inside `Q`,
and a local energy inequality which, for a pair smooth on compact subsets of `Q`, is an identity
at every `s < 0` — this is why `hu`, `hp`, `hf` are premises here and not mere conveniences);
and the reduction of `foot:aniso:pressure`, since the manuscript applies the criterion to the
pair `(u, π − π_f)` with the divergence-free force `f − ∇π_f`, whereas this statement takes the
manuscript's own bounded force (design note R1). The pressure in `L^{3/2}(Q)` and the energy
class up to `t = 0`, which the backward cylinders reach, come from `henergy` (design note R6). -/
theorem gktCriterion (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∫⁻ t in Ioo (-(r ^ 2)) 0,
        (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ))
          ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal ε) :
    BoundedNearOrigin u := by
  exact CIV.Main.gktCriterion q u Du p f hsol henergy hu hp hf hMf hsmall

end CIV
