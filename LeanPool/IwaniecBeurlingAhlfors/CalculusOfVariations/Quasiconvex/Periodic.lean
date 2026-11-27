/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.Periodic
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.Rescale
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Quasiconvex.Cutoff

/-!
# Quasiconvexity with periodic test maps

For a Borel, locally bounded `f`, quasiconvexity at `A` on the unit cube is equivalent to the
inequality `f (A) ≤ ∫_{(0,1)^m} f (A + ∇φ)` for `ℤ^m`-periodic Lipschitz `φ`
(`quasiconvexAtOn_iff_periodic`). This is Proposition 5.13 of B. Dacorogna, *Direct Methods in the
Calculus of Variations*, 2nd ed., Springer, 2008 ([D08], p. 173–174), with its proof.

"⇒": for a periodic `φ`, the maps `ψ_ν (x) = ν⁻¹ φ (ν x)`, `ν ∈ ℕ`, satisfy
`∫_Q f (A + ∇ψ_ν) = ∫_Q f (A + ∇φ)` by periodicity, and they converge to `0` uniformly with bounded
gradients. Multiplied by cut-offs `η_ν` (`0` off `Q`, `1` on `[1/ν, 1 − 1/ν]^m`, `|∇η_ν| ≤ c ν`)
they are test maps with bounded gradients, and the energies differ by at most a constant times the
measure of the boundary layer, since `f` is locally bounded (`le_of_quasiconvexAtOn_of_tendsto`,
`Quasiconvex.Cutoff`, which chooses the width `1/j` of the layer and the frequency `ν` separately).
"⇐": a test map on the cube extends periodically (`periodicExtension`). It is Lipschitz because
it vanishes on the boundary of the cube, and has the same gradient on the open cube ([D08]:
`W^{1,∞}_0 (Q) ⊂ W^{1,∞}_per (Q)`).
-/

@[expose] public section

open Metric Set MeasureTheory Filter Topology
open scoped Pointwise

namespace CalculusOfVariations

variable {d m : ℕ}

/-- Quasiconvexity on the cube gives the inequality for periodic test maps: the maps
`ψ_ν (x) = ν⁻¹ φ (ν x)` are Lipschitz with the constant of `φ`, converge to `0` uniformly, and
`∫_Q f (A + ∇ψ_ν) = ∫_Q f (A + ∇φ)` for `ν ≥ 1` by periodicity, so
`le_of_quasiconvexAtOn_of_tendsto` applies. -/
lemma rd_periodic_of_cube {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Measurable f) (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ)
    (hq : QuasiconvexAtOn (unitCube m) f A) : QuasiconvexAtPeriodic f A := by
  intro φ K hφ hper _
  obtain ⟨M, hM0, hM⟩ := rd_periodic_bounded hφ hper
  obtain ⟨C, -, hC⟩ := rd_bound_near hbdd A K
  have hFm : Measurable fun x => f (A + grad φ x) :=
    hf.comp (rd_measurable_add_grad A φ)
  set ψ : ℕ → (Fin m → ℝ) → Fin d → ℝ := fun ν x => (ν : ℝ)⁻¹ • φ ((ν : ℝ) • x) with hψ
  refine le_of_quasiconvexAtOn_of_tendsto hf hbdd hq (u := ψ) (K := K) (fun ν => ?_) ?_ ?_
  · -- the Lipschitz constants
    rcases Nat.eq_zero_or_pos ν with rfl | hν
    · refine LipschitzWith.of_dist_le_mul fun x y => ?_
      simp only [hψ, Nat.cast_zero, inv_zero, zero_smul, dist_self]
      positivity
    · have h := rescaleMap_lipschitz hφ 0 (inv_pos.2 (Nat.cast_pos (α := ℝ).2 hν))
      unfold rescaleMap at h
      simpa only [hψ, inv_inv, sub_zero] using h
  · -- `ψ_ν → 0` uniformly
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hlim : Tendsto (fun ν : ℕ => (ν : ℝ)⁻¹ * M) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ).mul_const M
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with ν hν x
    rw [Pi.zero_apply, dist_zero_left, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left (hM _) (by positivity)).trans_lt hν
  · -- the energies
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with ν hν
    have hν' : (ν : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hν.ne'
    have hGb : ∀ y, |f (A + grad φ y)| ≤ C := fun y => hC _ (rd_grad_abs_le hφ y)
    rw [← rd_setIntegral_comp_nsmul hFm hGb (fun x z => by rw [rd_grad_periodic hper]) hν]
    simp only [hψ, rd_grad_rescale φ hν']

/-- The inequality for periodic test maps gives quasiconvexity on the cube: a test map on the
cube extends periodically (`periodicExtension`,
Lipschitz since it vanishes on the boundary of the cube), with the same gradient on the open
cube. -/
private lemma rd_cube_of_periodic {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (A : Matrix (Fin d) (Fin m) ℝ) (hp : QuasiconvexAtPeriodic f A) :
    QuasiconvexAtOn (unitCube m) f A := by
  intro φ K hφ h0 hint
  have hopen : IsOpen (unitCube m) := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  have heq : ∀ x ∈ unitCube m, f (A + grad (periodicExtension φ) x) = f (A + grad φ x) :=
    fun x hx => by rw [rd_grad_perExt hx]
  have hmeas : MeasurableSet (unitCube m) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hint' : IntegrableOn (fun x => f (A + grad (periodicExtension φ) x)) (unitCube m) :=
    hint.congr_fun (fun x hx => (heq x hx).symm) hmeas
  have := hp (periodicExtension φ) _ (rd_perExt_lipschitz hφ h0) (rd_perExt_periodic φ) hint'
  rw [setIntegral_congr_fun hmeas heq] at this
  rw [rd_volume_unitCube, ENNReal.toReal_one, one_mul]
  exact this

/-- **Quasiconvexity with periodic test maps**: for a Borel, locally bounded `f`, quasiconvexity at
`A` on the unit cube is equivalent to the inequality for `ℤ^m`-periodic Lipschitz test maps, that
is, on the torus `𝕋^m = ℝ^m / ℤ^m`.

This is [D08], Proposition 5.13 (stated there for `f` quasiconvex at every matrix; its proof fixes
the matrix), with the proof of [D08]. "⇒": rescaled periodic maps and cut-offs
(`rd_periodic_of_cube`, `le_of_quasiconvexAtOn_of_tendsto`). "⇐": a test map on the cube extends
periodically (`periodicExtension`, `x ↦ φ (fract x)`). It is Lipschitz because it vanishes on the
boundary of the cube, and has the same gradient on the open cube. See also S. Müller, *Variational
models for microstructure and phase transitions*, lecture notes, MPI MiS Leipzig, 1998, Proposition
4.19. -/
theorem quasiconvexAtOn_iff_periodic {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Measurable f) (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtPeriodic f A :=
  ⟨rd_periodic_of_cube hf hbdd A, rd_cube_of_periodic A⟩

end CalculusOfVariations
