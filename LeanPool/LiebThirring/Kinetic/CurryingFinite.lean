/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Interchanging finite Hilbert sums and L²

This module gives the canonical complex linear isometric equivalence between
`L²(X; ⨁₂ i, E i)` and `⨁₂ i, L²(X; E i)` for a finite family of complete
complex Hilbert spaces.  Its evaluation theorem records the representative
identity in every coordinate.
-/

@[expose] public section

open MeasureTheory WithLp
open scoped ENNReal

namespace LiebThirring

noncomputable section

variable {X ι : Type*} [MeasurableSpace X] (μ : Measure X) [Fintype ι]
variable (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)]

/-- Send a `PiLp`-valued L² class to its finite family of coordinate classes. -/
noncomputable def finiteLpPiLpForward
    (f : Lp (PiLp 2 E) 2 μ) : PiLp 2 (fun i => Lp (E i) 2 μ) :=
  toLp 2 fun i => (PiLp.proj (𝕜 := ℂ) 2 E i).compLpL 2 μ f

/-- Assemble a finite family of L² classes from their strongly measurable representatives. -/
noncomputable def finiteLpPiLpInverse
    (f : PiLp 2 (fun i => Lp (E i) 2 μ)) : Lp (PiLp 2 E) 2 μ :=
  (memLp_piLp_iff.mpr fun i => Lp.memLp (f i)).toLp
    (fun x => toLp 2 fun i => f i x)

theorem finiteLpPiLpInverse_forward (f : Lp (PiLp 2 E) 2 μ) :
    finiteLpPiLpInverse μ E (finiteLpPiLpForward μ E f) = f := by
  apply Lp.ext
  have hbmem : MemLp
      (fun x => toLp 2 fun i => (finiteLpPiLpForward μ E f) i x) 2 μ :=
    memLp_piLp_iff.mpr fun i => Lp.memLp ((finiteLpPiLpForward μ E f) i)
  have hfwd : ∀ᵐ x ∂μ, ∀ i,
      ((finiteLpPiLpForward μ E f) i) x =
        (PiLp.proj (𝕜 := ℂ) 2 E i) (f x) :=
    ae_all_iff.mpr fun i => ContinuousLinearMap.coeFn_compLp _ _
  filter_upwards [hbmem.coeFn_toLp, hfwd] with x hx hfx
  apply PiLp.ext
  intro i
  rw [show (finiteLpPiLpInverse μ E (finiteLpPiLpForward μ E f)) x =
    toLp 2 (fun i => (finiteLpPiLpForward μ E f) i x) from hx]
  rw [PiLp.toLp_apply]
  exact hfx i

theorem finiteLpPiLpForward_inverse (f : PiLp 2 (fun i => Lp (E i) 2 μ)) :
    finiteLpPiLpForward μ E (finiteLpPiLpInverse μ E f) = f := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  have hbmem : MemLp (fun x => toLp 2 fun i => f i x) 2 μ :=
    memLp_piLp_iff.mpr fun i => Lp.memLp (f i)
  filter_upwards [ContinuousLinearMap.coeFn_compLp
      (PiLp.proj (𝕜 := ℂ) 2 E i) (finiteLpPiLpInverse μ E f), hbmem.coeFn_toLp]
  intro x hp hx
  change ((PiLp.proj (𝕜 := ℂ) 2 E i).compLp (finiteLpPiLpInverse μ E f)) x = f i x
  rw [hp]
  exact congrArg (fun z => z i) hx

theorem finiteLpPiLpForward_add (f g : Lp (PiLp 2 E) 2 μ) :
    finiteLpPiLpForward μ E (f + g) =
      finiteLpPiLpForward μ E f + finiteLpPiLpForward μ E g := by
  apply PiLp.ext
  intro i
  simp [finiteLpPiLpForward]

theorem finiteLpPiLpForward_smul (c : ℂ) (f : Lp (PiLp 2 E) 2 μ) :
    finiteLpPiLpForward μ E (c • f) = c • finiteLpPiLpForward μ E f := by
  apply PiLp.ext
  intro i
  simp [finiteLpPiLpForward]

theorem finiteLpPiLpForward_norm (f : Lp (PiLp 2 E) 2 μ) :
    ‖finiteLpPiLpForward μ E f‖ = ‖f‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) (finiteLpPiLpForward μ E f),
    norm_sq_eq_re_inner (𝕜 := ℂ) f]
  rw [PiLp.inner_apply, MeasureTheory.L2.inner_def]
  simp_rw [MeasureTheory.L2.inner_def]
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
      ((finiteLpPiLpForward μ E f) i) ((finiteLpPiLpForward μ E f) i))]
  apply congrArg RCLike.re
  apply integral_congr_ae
  have hfwd : ∀ᵐ x ∂μ, ∀ i,
      ((finiteLpPiLpForward μ E f) i) x =
        (PiLp.proj (𝕜 := ℂ) 2 E i) (f x) :=
    ae_all_iff.mpr fun i => ContinuousLinearMap.coeFn_compLp _ _
  filter_upwards [hfwd] with x hx
  simp only [hx, PiLp.proj_apply, PiLp.inner_apply]

/-- The canonical finite-coordinate interchange `L²(X; ⨁₂ i, E i) ≃ ⨁₂ i, L²(X; E i)`. -/
noncomputable def finiteLpPiLpEquiv :
    Lp (PiLp 2 E) 2 μ ≃ₗᵢ[ℂ] PiLp 2 (fun i => Lp (E i) 2 μ) where
  toFun := finiteLpPiLpForward μ E
  invFun := finiteLpPiLpInverse μ E
  left_inv := finiteLpPiLpInverse_forward μ E
  right_inv := finiteLpPiLpForward_inverse μ E
  map_add' := finiteLpPiLpForward_add μ E
  map_smul' := finiteLpPiLpForward_smul μ E
  norm_map' := finiteLpPiLpForward_norm μ E

/-- Componentwise representative characterization of the finite-coordinate interchange. -/
theorem finiteLpPiLpEquiv_apply_ae (f : Lp (PiLp 2 E) 2 μ) (i : ι) :
    finiteLpPiLpEquiv μ E f i =ᵐ[μ] fun x => f x i :=
  ContinuousLinearMap.coeFn_compLp' (PiLp.proj (𝕜 := ℂ) 2 E i) f

end

end LiebThirring

end
