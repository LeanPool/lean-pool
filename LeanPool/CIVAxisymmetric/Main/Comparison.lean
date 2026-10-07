/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Hypotheses
public import LeanPool.CIVAxisymmetric.Comparison.Direct.Assembly

/-!
# The public statement `CIV.Main.comparison`

This module proves the statement `CIV.comparison`, the first assertion of `lem:aniso:comparison`,
`eq:aniso:comparison:conclusion`. The proof is `CIV.comparison_of_isDistributionalDriftDiffusion`:
mollify in space, compare the mollified solution with the barrier `eq:aniso:comparison:barrier`
through the energy of `eq:aniso:comparison:positive:energy` from a reference time of the mollified
equation, let the mollification radius and then the barrier slope tend to zero, and exhaust `I` by
compact intervals. The hypothesis `1 ≤ d ≤ m` of the statement is not used: for `d = 0` the equation
has no diffusion and the argument applies verbatim, and for `d > m` the partial Laplacian is the
full Laplacian.
-/

public section

open MeasureTheory Set
open CKN


noncomputable section

namespace CIV
namespace Main

/-- The public statement of `lem:aniso:comparison`, first assertion. -/
theorem comparison (m d : ℕ) (hd : 1 ≤ d ∧ d ≤ m) (I : Set ℝ)
    (hI : IsOpen I ∧ I.OrdConnected)
    (B : Vec m × ℝ → Vec m) (divB : Vec m × ℝ → ℝ) (hB : IsAdmissibleDrift m I B divB)
    (q : Vec m × ℝ → ℝ) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) :
    ∀ᵐ τ₀ ∂(volume.restrict I), ∀ᵐ τ ∂(volume.restrict I), τ₀ < τ →
      eLpNorm (fun x => q (x, τ)) ⊤ volume ≤ eLpNorm (fun x => q (x, τ₀)) ⊤ volume := by
  obtain ⟨-, -⟩ := hd
  exact comparison_of_isDistributionalDriftDiffusion hI.1 hI.2 hB hq heq

end Main
end CIV
