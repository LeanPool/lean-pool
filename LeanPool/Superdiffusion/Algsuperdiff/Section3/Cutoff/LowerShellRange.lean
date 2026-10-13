/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.ShellRange
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Locality
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.RefinedIndependence

/-!
# LowerShellRange

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Range dependence of the lower shell stream

The lower stream is a countable join over the exact indices `m-r`.  Its range
proof combines `ShellRange` with the refined independent-pairs theorem, then
uses the explicitly defined a.e. completion needed by the genuine cutoff.
-/

namespace Algsuperdiff.Section3.Cutoff

open HCPolySupport MeasureTheory ProbabilityTheory
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

private theorem lower_shell_index_injective (m : ℤ) :
    Function.Injective (fun r : ℕ => m - (r : ℤ)) := by
  intro r s hrs
  have h : (r : ℤ) = (s : ℤ) := sub_right_injective hrs
  exact_mod_cast h

/-- The two lower-shell integral-local sigma-fields are independent whenever
the observation regions are separated by the literal cutoff range. -/
theorem indep_lowerShellLocalSigma_of_cutoff_separation (M : ABKModel d) (m : ℤ)
    {U V : Set (Vec d)}
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hsep : ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ m ≤ HCPolySupport.Book.Ch02.vecNorm (x - y)) :
    Indep (lowerShellLocalSigma m U) (lowerShellLocalSigma m V) M.P.toMeasure := by
  let κ : ℕ → MeasurableSpace (ℤ → ShellField d) := fun r =>
    MeasurableSpace.comap (fun omega : ℤ → ShellField d => omega (m - (r : ℤ))) inferInstance
  let a : ℕ → MeasurableSpace (ℤ → ShellField d) := fun r =>
    (ShellField.lihLocalSigma U).comap (fun omega : ℤ → ShellField d => omega (m - (r : ℤ)))
  let b : ℕ → MeasurableSpace (ℤ → ShellField d) := fun r =>
    (ShellField.lihLocalSigma V).comap (fun omega : ℤ → ShellField d => omega (m - (r : ℤ)))
  have hind : iIndep κ M.P.toMeasure := by
    exact M.shellPrefix.independent.iIndep.precomp (lower_shell_index_injective m)
  have hle : ∀ r, κ r ≤ (inferInstance : MeasurableSpace (ℤ → ShellField d)) := by
    intro r
    exact (ShellField.measurable_shellCoordinate (m - (r : ℤ))).comap_le
  have ha : ∀ r, a r ≤ κ r := by
    intro r
    exact MeasurableSpace.comap_mono (ShellField.lihLocalSigma_le_borel U)
  have hb : ∀ r, b r ≤ κ r := by
    intro r
    exact MeasurableSpace.comap_mono (ShellField.lihLocalSigma_le_borel V)
  have hab : ∀ r, Indep (a r) (b r) M.P.toMeasure := by
    intro r
    exact indep_shellLocal_of_cutoff_separation M m (m - (r : ℤ)) (by omega)
      U V hU hV hsep
  have hjoin := Algsuperdiff.Probability.indep_iSup_of_indep_of_iIndep
    hind hle ha hb hab
  change Indep (⨆ r : ℕ, a r) (⨆ r : ℕ, b r) M.P.toMeasure at hjoin
  exact hjoin

/-- Completion by ambient null sets preserves the lower-stream range
independence.  This is the input used to make the actual infinite cutoff
local, rather than an unproved direct restriction-field assertion. -/
theorem indep_lowerShellLocalCompletion_of_cutoff_separation (M : ABKModel d) (m : ℤ)
    {U V : Set (Vec d)}
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hsep : ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ m ≤ HCPolySupport.Book.Ch02.vecNorm (x - y)) :
    Indep (lowerShellLocalCompletion M m U) (lowerShellLocalCompletion M m V)
      M.P.toMeasure :=
  indep_lowerShellLocalCompletion_of_indep M m U V
    (indep_lowerShellLocalSigma_of_cutoff_separation M m hU hV hsep)

end

end Algsuperdiff.Section3.Cutoff
