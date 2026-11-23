/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitRiemannLevel
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedInterface

/-! # `CDFactor`, part 1: gradients and carré du champ of functions pulled back from the level

For a frame `fr` and `π = fr.toLevel : M → fr.Level`, the differential `dπ_x` kills the frame
`X_i`, is surjective and isometric on the orthogonal complement of the `X_i`. Consequently
`∇(u' ∘ π)` is the horizontal lift of `∇u'` and `Γ_M(u'∘π, w'∘π) = Γ_N(u',w') ∘ π`.
-/

@[expose] public section

open Bundle MeasureTheory Set Filter Manifold
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

namespace Frame

open CutoffRigidity CutoffRigidity.Riemann

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] {k : ℕ} (fr : Frame F M k)

/-- Pythagoras in terms of `dπ`. -/
theorem norm_sq_split' (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    ‖v‖ ^ 2 = ‖fr.dsv x v‖ ^ 2 + ‖fr.dpi x v‖ ^ 2 := by
  rw [fr.norm_dpi]; exact fr.norm_sq_split x v

/-- Polarized Pythagoras. -/
theorem inner_split (x : M) (v w : TangentSpace 𝓘(ℝ, F) x) :
    inner ℝ v w = inner ℝ (fr.dsv x v) (fr.dsv x w) + inner ℝ (fr.dpi x v) (fr.dpi x w) := by
  have h1 := fr.norm_sq_split' x (v + w)
  have h2 := fr.norm_sq_split' x v
  have h3 := fr.norm_sq_split' x w
  have e1 : fr.dsv x (v + w) = fr.dsv x v + fr.dsv x w := map_add (mfderiv _ _ fr.sv x) v w
  have e2 : fr.dpi x (v + w) = fr.dpi x v + fr.dpi x w := map_add (fr.dpi x) v w
  rw [e1, e2] at h1
  rw [norm_add_sq_real, norm_add_sq_real (fr.dsv x v), norm_add_sq_real (fr.dpi x v)] at h1
  linarith


omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem dsv_apply (x : M) (v : TangentSpace 𝓘(ℝ, F) x) (j : Fin k) :
    (fr.dsv x v) j = inner ℝ (fr.X j x) v := fr.mfderiv_sv_apply x v j

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem dsv_X (i : Fin k) (x : M) : fr.dsv x (fr.X i x) = EuclideanSpace.single i 1 := by
  ext j
  rw [fr.dsv_apply, fr.inner_X]
  by_cases h : j = i <;> simp [h]

/-- The frame is killed by `dπ`. -/
theorem dpi_X (i : Fin k) (x : M) : fr.dpi x (fr.X i x) = 0 := by
  have h := fr.norm_sq_split' x (fr.X i x)
  rw [fr.norm_X, fr.dsv_X, EuclideanSpace.single, PiLp.norm_single, norm_one] at h
  have hz : ‖fr.dpi x (fr.X i x)‖ ^ 2 = 0 := by linarith
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hz)

/-- `dπ` is surjective. -/
theorem surjective_dpi (x : M) : Function.Surjective (fr.dpi x) := by
  have hsurj := (fr.splitEquiv.isInvertible_mfderiv (x := x) (by simp)).surjective
  rw [show (fr.splitEquiv : M → Rd k × fr.Level) = (fun y ↦ (fr.sv y, fr.toLevel y)) from rfl,
    mfderiv_prodMk (fr.mdiff_sv x) (fr.mdiff_toLevel x)] at hsurj
  intro w
  obtain ⟨v, hv⟩ := hsurj (0, w)
  exact ⟨v, congrArg Prod.snd hv⟩

/-- Chain rule for functions pulled back by `π`. -/
theorem mvfderiv_comp_toLevel {u' : fr.Level → ℝ}
    (hu' : ContMDiff 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, ℝ) ∞ u') (x : M)
    (v : TangentSpace 𝓘(ℝ, F) x) :
    mvfderiv 𝓘(ℝ, F) (fun z => u' (fr.toLevel z)) x v =
      mvfderiv 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) u' (fr.toLevel x) (fr.dpi x v) := by
  have hu : MDifferentiableAt 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, ℝ) u'
      (fr.toLevel x) := (hu'.mdifferentiable (by simp)) _
  exact mvfderiv_comp_apply x hu (fr.mdiff_toLevel x) v

/-- The gradient of `u' ∘ π` is horizontal and `dπ` maps it to `∇u'`. -/
theorem dsv_mgrad_comp {u' : fr.Level → ℝ}
    (hu' : ContMDiff 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, ℝ) ∞ u') (x : M) :
    fr.dsv x (mgrad F (fun z => u' (fr.toLevel z)) x) = 0 := by
  ext j
  rw [fr.dsv_apply, real_inner_comm, mgrad_inner, fr.mvfderiv_comp_toLevel hu', fr.dpi_X]
  simp

theorem dpi_mgrad_comp {u' : fr.Level → ℝ}
    (hu' : ContMDiff 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, ℝ) ∞ u') (x : M) :
    fr.dpi x (mgrad F (fun z => u' (fr.toLevel z)) x) =
      mgrad (LevelModel F (EuclideanSpace ℝ (Fin k))) u' (fr.toLevel x) := by
  have key : ∀ v : TangentSpace 𝓘(ℝ, F) x,
      inner ℝ (fr.dpi x (mgrad F (fun z => u' (fr.toLevel z)) x)) (fr.dpi x v) =
        inner ℝ (mgrad (LevelModel F (EuclideanSpace ℝ (Fin k))) u' (fr.toLevel x)) (fr.dpi x v)
            := by
    intro v
    have h := fr.inner_split x (mgrad F (fun z => u' (fr.toLevel z)) x) v
    rw [fr.dsv_mgrad_comp hu', inner_zero_left, zero_add, mgrad_inner,
      fr.mvfderiv_comp_toLevel hu', ← mgrad_inner] at h
    exact h.symm
  obtain ⟨w, hv⟩ := fr.surjective_dpi x (fr.dpi x (mgrad F (fun z => u' (fr.toLevel z)) x) -
    mgrad (LevelModel F (EuclideanSpace ℝ (Fin k))) u' (fr.toLevel x))
  have h := key w
  rw [hv] at h
  have h2 := sub_eq_zero.mpr h
  rw [← inner_sub_left, inner_self_eq_zero, sub_eq_zero] at h2
  exact h2

/-- **(I1)** `Γ_M(u'∘π, w'∘π) = Γ_N(u', w') ∘ π`. -/
theorem carre_comp_toLevel {u' w' : fr.Level → ℝ}
    (hu' : ContMDiff 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, ℝ) ∞ u')
    (hw' : ContMDiff 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, ℝ) ∞ w') (x : M) :
    carre F (fun z => u' (fr.toLevel z)) (fun z => w' (fr.toLevel z)) x =
      carre (LevelModel F (EuclideanSpace ℝ (Fin k))) u' w' (fr.toLevel x) := by
  unfold carre
  rw [fr.inner_split, fr.dsv_mgrad_comp hu', inner_zero_left, zero_add, fr.dpi_mgrad_comp hu',
    fr.dpi_mgrad_comp hw']


/-- `Γ(χ ∘ s, u' ∘ π) = 0`: functions of the frame coordinates are orthogonal to pulled back
functions. -/
theorem carre_sv_comp_toLevel {u' : fr.Level → ℝ}
    (hu' : ContMDiff 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, ℝ) ∞ u')
    {χ : EuclideanSpace ℝ (Fin k) → ℝ} (hχ : ContDiff ℝ ∞ χ) (x : M) :
    carre F (fun z => χ (fr.sv z)) (fun z => u' (fr.toLevel z)) x = 0 := by
  unfold carre
  rw [mgrad_inner]
  have hc : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, ℝ) χ (fr.sv x) :=
    (hχ.contMDiff.mdifferentiable (by simp)) _
  rw [show (fun y ↦ χ (fr.sv y)) = χ ∘ fr.sv from rfl,
    mvfderiv_comp_apply x hc (fr.mdiff_sv x)]
  change mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) χ (fr.sv x)
    (fr.dsv x (mgrad F (fun z ↦ u' (fr.toLevel z)) x)) = 0
  rw [fr.dsv_mgrad_comp hu']
  exact map_zero (mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) χ (fr.sv x))

end Frame

end CutCur
