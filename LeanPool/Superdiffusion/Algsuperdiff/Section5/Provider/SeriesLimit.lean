/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.BallAverageRepresentative
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.HolderL2Interpolation
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SeriesIdentification
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ZeroTraceSupNorm

/-!
# SeriesLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# From a geometrically decaying series of representatives to a continuous limit

The perturbation iteration produces zero-trace increments `w_j` whose continuous
representatives obey `[w_j]_{C^{0,1/2}(y+□_n)} ≤ K_0 ρ^j` with `ρ < 1`.  Because
each increment vanishes on the boundary of the cube, its supremum norm is
controlled by its own Hölder seminorm, so the series of representatives
converges absolutely and uniformly on the cube.  Its sum is continuous, carries
the summed Hölder bound, and — since the partial sums converge in `L²` to a
prescribed `H¹` function — is a continuous representative of that function.

This is the step that turns the `C^{0,1/2}` contraction into a statement about
the solution itself: the Hölder bound of the limit is inherited from the uniform
bound on the partial sums, and the identification of the limit is the `L²`
convergence of the series identification.

## Main results

* `isCubeRepresentative_partialSum` — a finite sum of representatives represents
  the partial sum.
* `exists_isCubeRepresentative_of_tendsto` — the limit representative, its
  Hölder bound, and the Hölder bound of the tail after the first term.

## References

* ABK26, the summation of the iteration series in the proof of the injection
  estimate of Section 5.1.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-! ## 1. Representatives of finite sums -/

private theorem isCubeRepresentative_add {y : Vec d} {n : ℤ} {u v : H1Function (cubeSetAt y n)}
    {uRep vRep : Vec d → ℝ} (hu : IsCubeRepresentative y n u uRep)
    (hv : IsCubeRepresentative y n v vRep) :
    IsCubeRepresentative y n (u + v) fun x => uRep x + vRep x := by
  refine ⟨?_, hu.2.add hv.2⟩
  filter_upwards [hu.1, hv.1] with x hx hx'
  show uRep x + vRep x = (u + v).toFun x
  rw [hx, hx']
  rfl

/-- **A finite sum of representatives represents the partial sum.** -/
theorem isCubeRepresentative_partialSum {y : Vec d} {n : ℤ}
    {w : ℕ → H1Function (cubeSetAt y n)} {wRep : ℕ → Vec d → ℝ}
    (hrep : ∀ j, IsCubeRepresentative y n (w j) (wRep j)) (J : ℕ) :
    IsCubeRepresentative y n (iterationPartialSum w J)
      fun x => ∑ j ∈ Finset.range (J + 1), wRep j x := by
  induction J with
  | zero => simpa using hrep 0
  | succ J ih =>
      have h := isCubeRepresentative_add ih (hrep (J + 1))
      rw [iterationPartialSum_succ]
      refine ⟨?_, ?_⟩
      · filter_upwards [h.1] with x hx
        rw [Finset.sum_range_succ]
        exact hx
      · refine h.2.congr fun x _ => ?_
        rw [Finset.sum_range_succ]

/-! ## 2. The limit of the series of representatives -/

section Limit

variable {y : Vec d} {n : ℤ} {w : ℕ → H1Function (cubeSetAt y n)} {wRep : ℕ → Vec d → ℝ}
  {K0 rho : ℝ}

/-- Each increment is bounded on the cube by its own Hölder seminorm, because it
vanishes on the boundary. -/
private theorem abs_wRep_le (hd : 0 < d) (hK0 : 0 ≤ K0) (hrho0 : 0 ≤ rho)
    (hrep : ∀ j, IsCubeRepresentative y n (w j) (wRep j))
    (hzero : ∀ j, ∃ z : H10Function (cubeSetAt y n),
      ∀ x, (w j).toFun x = z.toH1Function.toFun x)
    (hK : ∀ j, HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) (K0 * rho ^ j) (wRep j))
    (j : ℕ) {x : Vec d} (hx : x ∈ cubeSetAt y n) :
    |wRep j x| ≤ Real.rpow 3 ((n : ℝ) / 2) * (K0 * rho ^ j) := by
  have hPnn : (0 : ℝ) ≤ Real.rpow 3 ((n : ℝ) / 2) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hKj : (0 : ℝ) ≤ K0 * rho ^ j := by positivity
  have h1 := supNormOn_le_rpow_mul_holderSeminormOn_of_zeroTrace hd (hzero j) (hrep j)
  have h2 : holderSeminormOn (cubeSetAt y n) (1 / 2) (wRep j) ≤
      ENNReal.ofReal (K0 * rho ^ j) := (holderSeminormOn_le_ofReal_iff hKj).2 (hK j)
  have h3 : supNormOn (cubeSetAt y n) (wRep j) ≤
      ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2) * (K0 * rho ^ j)) := by
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul hPnn]
    gcongr
  have h4 := (supNormOn_le_ofReal_iff (by positivity)).1 h3 x hx
  simpa only [Real.norm_eq_abs] using h4

/-- The tail of the series of representatives, as a function on the cube. -/
def seriesTail (wRep : ℕ → Vec d → ℝ) (k : ℕ) (x : Vec d) : ℝ :=
  ∑' j : ℕ, wRep (j + k) x

private theorem summable_wRep (hd : 0 < d) (hK0 : 0 ≤ K0) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hrep : ∀ j, IsCubeRepresentative y n (w j) (wRep j))
    (hzero : ∀ j, ∃ z : H10Function (cubeSetAt y n),
      ∀ x, (w j).toFun x = z.toH1Function.toFun x)
    (hK : ∀ j, HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) (K0 * rho ^ j) (wRep j))
    {x : Vec d} (hx : x ∈ cubeSetAt y n) : Summable fun j => wRep j x := by
  refine Summable.of_norm_bounded
    (g := fun j : ℕ => Real.rpow 3 ((n : ℝ) / 2) * K0 * rho ^ j)
    ((summable_geometric_of_lt_one hrho0 hrho1).mul_left _) fun j => ?_
  rw [Real.norm_eq_abs]
  have h := abs_wRep_le hd hK0 hrho0 hrep hzero hK j hx
  calc |wRep j x| ≤ Real.rpow 3 ((n : ℝ) / 2) * (K0 * rho ^ j) := h
    _ = Real.rpow 3 ((n : ℝ) / 2) * K0 * rho ^ j := by ring

private theorem summable_wRep_shift (hd : 0 < d) (hK0 : 0 ≤ K0) (hrho0 : 0 ≤ rho)
    (hrho1 : rho < 1) (hrep : ∀ j, IsCubeRepresentative y n (w j) (wRep j))
    (hzero : ∀ j, ∃ z : H10Function (cubeSetAt y n),
      ∀ x, (w j).toFun x = z.toH1Function.toFun x)
    (hK : ∀ j, HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) (K0 * rho ^ j) (wRep j))
    (k : ℕ) {x : Vec d} (hx : x ∈ cubeSetAt y n) : Summable fun j => wRep (j + k) x :=
  (summable_nat_add_iff k).2 (summable_wRep hd hK0 hrho0 hrho1 hrep hzero hK hx)

/-- The two-point bound of a tail of the series, summed geometrically. -/
private theorem abs_seriesTail_sub_le (hd : 0 < d) (hK0 : 0 ≤ K0) (hrho0 : 0 ≤ rho)
    (hrho1 : rho < 1) (hrep : ∀ j, IsCubeRepresentative y n (w j) (wRep j))
    (hzero : ∀ j, ∃ z : H10Function (cubeSetAt y n),
      ∀ x, (w j).toFun x = z.toH1Function.toFun x)
    (hK : ∀ j, HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) (K0 * rho ^ j) (wRep j))
    (k : ℕ) {x z : Vec d} (hx : x ∈ cubeSetAt y n) (hz : z ∈ cubeSetAt y n) :
    |seriesTail wRep k x - seriesTail wRep k z| ≤
      K0 * rho ^ k / (1 - rho) * ‖x - z‖ ^ (1 / 2 : ℝ) := by
  have hone : (0 : ℝ) < 1 - rho := by linarith only [hrho1]
  have hdist : (0 : ℝ) ≤ ‖x - z‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have hsx := summable_wRep_shift hd hK0 hrho0 hrho1 hrep hzero hK k hx
  have hsz := summable_wRep_shift hd hK0 hrho0 hrho1 hrep hzero hK k hz
  have hterm : ∀ j : ℕ, |wRep (j + k) x - wRep (j + k) z| ≤
      K0 * ‖x - z‖ ^ (1 / 2 : ℝ) * rho ^ (j + k) := by
    intro j
    have h := hK (j + k) x hx z hz
    rw [Real.norm_eq_abs] at h
    calc |wRep (j + k) x - wRep (j + k) z| ≤ K0 * rho ^ (j + k) * ‖x - z‖ ^ (1 / 2 : ℝ) := h
      _ = K0 * ‖x - z‖ ^ (1 / 2 : ℝ) * rho ^ (j + k) := by ring
  have hmaj : Summable fun j : ℕ => K0 * ‖x - z‖ ^ (1 / 2 : ℝ) * rho ^ (j + k) := by
    refine Summable.mul_left _ ?_
    exact (summable_nat_add_iff k).2 (summable_geometric_of_lt_one hrho0 hrho1)
  have habs : Summable fun j : ℕ => |wRep (j + k) x - wRep (j + k) z| := by
    refine Summable.of_nonneg_of_le (fun j => abs_nonneg _) hterm hmaj
  have hsub : seriesTail wRep k x - seriesTail wRep k z =
      ∑' j : ℕ, (wRep (j + k) x - wRep (j + k) z) := (hsx.tsum_sub hsz).symm
  have hnormsum : Summable fun j : ℕ => ‖wRep (j + k) x - wRep (j + k) z‖ := by
    simpa only [Real.norm_eq_abs] using habs
  have hbd : |∑' j : ℕ, (wRep (j + k) x - wRep (j + k) z)| ≤
      ∑' j : ℕ, |wRep (j + k) x - wRep (j + k) z| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnormsum
  rw [hsub]
  calc |∑' j : ℕ, (wRep (j + k) x - wRep (j + k) z)|
      ≤ ∑' j : ℕ, |wRep (j + k) x - wRep (j + k) z| := hbd
    _ ≤ ∑' j : ℕ, K0 * ‖x - z‖ ^ (1 / 2 : ℝ) * rho ^ (j + k) :=
        Summable.tsum_le_tsum hterm habs hmaj
    _ = K0 * rho ^ k / (1 - rho) * ‖x - z‖ ^ (1 / 2 : ℝ) := by
        rw [tsum_mul_left]
        have hgeo : ∑' j : ℕ, rho ^ (j + k) = rho ^ k / (1 - rho) := by
          calc ∑' j : ℕ, rho ^ (j + k) = ∑' j : ℕ, rho ^ k * rho ^ j := by
                refine tsum_congr fun j => ?_
                rw [pow_add]
                ring
            _ = rho ^ k * (1 - rho)⁻¹ := by
                rw [tsum_mul_left, tsum_geometric_of_lt_one hrho0 hrho1]
            _ = rho ^ k / (1 - rho) := by rw [div_eq_mul_inv]
        rw [hgeo]
        field_simp

/-- The supremum bound of a tail of the series on the cube. -/
private theorem abs_seriesTail_le (hd : 0 < d) (hK0 : 0 ≤ K0) (hrho0 : 0 ≤ rho)
    (hrho1 : rho < 1) (hrep : ∀ j, IsCubeRepresentative y n (w j) (wRep j))
    (hzero : ∀ j, ∃ z : H10Function (cubeSetAt y n),
      ∀ x, (w j).toFun x = z.toH1Function.toFun x)
    (hK : ∀ j, HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) (K0 * rho ^ j) (wRep j))
    (k : ℕ) {x : Vec d} (hx : x ∈ cubeSetAt y n) :
    |seriesTail wRep k x| ≤ Real.rpow 3 ((n : ℝ) / 2) * K0 * rho ^ k / (1 - rho) := by
  have hone : (0 : ℝ) < 1 - rho := by linarith only [hrho1]
  have hsx := summable_wRep_shift hd hK0 hrho0 hrho1 hrep hzero hK k hx
  have hterm : ∀ j : ℕ, |wRep (j + k) x| ≤
      Real.rpow 3 ((n : ℝ) / 2) * K0 * rho ^ (j + k) := by
    intro j
    have h := abs_wRep_le hd hK0 hrho0 hrep hzero hK (j + k) hx
    calc |wRep (j + k) x| ≤ Real.rpow 3 ((n : ℝ) / 2) * (K0 * rho ^ (j + k)) := h
      _ = Real.rpow 3 ((n : ℝ) / 2) * K0 * rho ^ (j + k) := by ring
  have hmaj : Summable fun j : ℕ => Real.rpow 3 ((n : ℝ) / 2) * K0 * rho ^ (j + k) :=
    Summable.mul_left _ ((summable_nat_add_iff k).2 (summable_geometric_of_lt_one hrho0 hrho1))
  have habs : Summable fun j : ℕ => |wRep (j + k) x| :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) hterm hmaj
  have hnormsum : Summable fun j : ℕ => ‖wRep (j + k) x‖ := by
    simpa only [Real.norm_eq_abs] using habs
  have hbd : |∑' j : ℕ, wRep (j + k) x| ≤ ∑' j : ℕ, |wRep (j + k) x| := by
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun j : ℕ => wRep (j + k) x) hnormsum
  calc |seriesTail wRep k x| ≤ ∑' j : ℕ, |wRep (j + k) x| := hbd
    _ ≤ ∑' j : ℕ, Real.rpow 3 ((n : ℝ) / 2) * K0 * rho ^ (j + k) :=
        Summable.tsum_le_tsum hterm habs hmaj
    _ = Real.rpow 3 ((n : ℝ) / 2) * K0 * rho ^ k / (1 - rho) := by
        rw [tsum_mul_left]
        have hgeo : ∑' j : ℕ, rho ^ (j + k) = rho ^ k / (1 - rho) := by
          calc ∑' j : ℕ, rho ^ (j + k) = ∑' j : ℕ, rho ^ k * rho ^ j := by
                refine tsum_congr fun j => ?_
                rw [pow_add]
                ring
            _ = rho ^ k * (1 - rho)⁻¹ := by
                rw [tsum_mul_left, tsum_geometric_of_lt_one hrho0 hrho1]
            _ = rho ^ k / (1 - rho) := by rw [div_eq_mul_inv]
        rw [hgeo]
        ring

/-- **The sum of the series of representatives is a continuous representative of
the `L²` limit of the partial sums**, with the summed Hölder bound, and its
distance to the first term carries the tail bound. -/
theorem exists_isCubeRepresentative_of_tendsto (hd : 0 < d) (hK0 : 0 ≤ K0) (hrho0 : 0 ≤ rho)
    (hrho1 : rho < 1) (hrep : ∀ j, IsCubeRepresentative y n (w j) (wRep j))
    (hzero : ∀ j, ∃ z : H10Function (cubeSetAt y n),
      ∀ x, (w j).toFun x = z.toH1Function.toFun x)
    (hK : ∀ j, HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) (K0 * rho ^ j) (wRep j))
    {u : H1Function (cubeSetAt y n)}
    (hlim : Filter.Tendsto (fun J => Real.sqrt (∫ x in cubeSetAt y n,
        (u.toFun x - (iterationPartialSum w J).toFun x) ^ (2 : ℕ) ∂volume))
      Filter.atTop (nhds 0)) :
    ∃ uRep : Vec d → ℝ, IsCubeRepresentative y n u uRep ∧
      HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) (K0 / (1 - rho)) uRep ∧
      HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) (K0 * rho / (1 - rho))
        fun x => uRep x - wRep 0 x := by
  have : IsFiniteMeasure (volumeMeasureOn (cubeSetAt y n)) :=
    (isOpenBoundedConvexDomain_cubeSetAt y n).isFiniteMeasure_restrict_volume
  have : IsFiniteMeasure (volume.restrict (cubeSetAt y n)) := inferInstance
  have hone : (0 : ℝ) < 1 - rho := by linarith only [hrho1]
  have hPpos : (0 : ℝ) < Real.rpow 3 ((n : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨seriesTail wRep 0, ?_, ?_, ?_⟩
  · -- the sum is a representative of `u`
    have hUholder : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) (K0 / (1 - rho))
        (seriesTail wRep 0) := by
      intro x hx z hz
      have h := abs_seriesTail_sub_le hd hK0 hrho0 hrho1 hrep hzero hK 0 hx hz
      rw [pow_zero, mul_one] at h
      simpa only [Real.norm_eq_abs] using h
    have hKq : (0 : ℝ) ≤ K0 / (1 - rho) := div_nonneg hK0 hone.le
    have hcont : ContinuousOn (seriesTail wRep 0) (cubeSetAt y n) :=
      continuousOn_of_holderSeminormBoundOn hKq (by norm_num) hUholder
    have hmemU : MemLp (seriesTail wRep 0) 2 (volume.restrict (cubeSetAt y n)) :=
      memLp_two_of_continuousOn_of_holder hKq hcont hUholder
    refine ⟨?_, hcont⟩
    -- the two `L²` limits of the partial sums agree
    have hFmem : MemLp (fun x => u.toFun x - seriesTail wRep 0 x) 2
        (volume.restrict (cubeSetAt y n)) := u.memL2.sub hmemU
    have hFint : Integrable
        (fun x => (u.toFun x - seriesTail wRep 0 x) ^ (2 : ℕ))
        (volume.restrict (cubeSetAt y n)) := hFmem.integrable_sq
    have hAnonneg : ∀ J : ℕ, (0 : ℝ) ≤ ∫ x in cubeSetAt y n,
        (u.toFun x - (iterationPartialSum w J).toFun x) ^ (2 : ℕ) ∂volume := fun J =>
      integral_nonneg fun x => by positivity
    have hAtends : Filter.Tendsto (fun J : ℕ => ∫ x in cubeSetAt y n,
        (u.toFun x - (iterationPartialSum w J).toFun x) ^ (2 : ℕ) ∂volume)
        Filter.atTop (nhds 0) := by
      have h : Filter.Tendsto (fun J : ℕ => (Real.sqrt (∫ x in cubeSetAt y n,
          (u.toFun x - (iterationPartialSum w J).toFun x) ^ (2 : ℕ) ∂volume)) ^ 2)
          Filter.atTop (nhds 0) := by simpa using hlim.pow 2
      exact h.congr fun J => Real.sq_sqrt (hAnonneg J)
    set delta : ℕ → ℝ := fun J =>
      Real.rpow 3 ((n : ℝ) / 2) * K0 * rho ^ (J + 1) / (1 - rho) with hdeltadef
    have hdeltatends : Filter.Tendsto delta Filter.atTop (nhds 0) := by
      have hpow : Filter.Tendsto (fun J : ℕ => rho ^ (J + 1)) Filter.atTop (nhds 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one hrho0 hrho1).comp (Filter.tendsto_add_atTop_nat 1)
      have := (hpow.const_mul (Real.rpow 3 ((n : ℝ) / 2) * K0)).div_const (1 - rho)
      simpa [hdeltadef, mul_assoc] using this
    have hdeltabound : ∀ J : ℕ, ∀ᵐ x ∂(volume.restrict (cubeSetAt y n)),
        ((iterationPartialSum w J).toFun x - seriesTail wRep 0 x) ^ (2 : ℕ) ≤
          delta J ^ (2 : ℕ) := by
      intro J
      have hSRep := isCubeRepresentative_partialSum hrep J
      filter_upwards [hSRep.1, self_mem_ae_restrict (measurableSet_cubeSetAt y n)] with x hx hxmem
      have hsum := (summable_wRep hd hK0 hrho0 hrho1 hrep hzero hK hxmem).sum_add_tsum_nat_add
        (J + 1)
      have hsplit : seriesTail wRep 0 x - (∑ j ∈ Finset.range (J + 1), wRep j x) =
          seriesTail wRep (J + 1) x := by
        simp only [seriesTail, Nat.add_zero]
        rw [← hsum]
        ring
      have habs := abs_seriesTail_le hd hK0 hrho0 hrho1 hrep hzero hK (J + 1) hxmem
      have hle : |(iterationPartialSum w J).toFun x - seriesTail wRep 0 x| ≤ delta J := by
        rw [← hx, abs_sub_comm]
        rw [hsplit]
        exact habs
      have hsq : ((iterationPartialSum w J).toFun x - seriesTail wRep 0 x) ^ (2 : ℕ) =
          |(iterationPartialSum w J).toFun x - seriesTail wRep 0 x| ^ (2 : ℕ) := (sq_abs _).symm
      rw [hsq]
      exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    have hbound : ∀ J : ℕ, ∫ x in cubeSetAt y n,
        (u.toFun x - seriesTail wRep 0 x) ^ (2 : ℕ) ∂volume ≤
        2 * (∫ x in cubeSetAt y n,
            (u.toFun x - (iterationPartialSum w J).toFun x) ^ (2 : ℕ) ∂volume) +
          2 * ((volume.restrict (cubeSetAt y n)).real Set.univ * delta J ^ (2 : ℕ)) := by
      intro J
      have hGint : Integrable
          (fun x => (u.toFun x - (iterationPartialSum w J).toFun x) ^ (2 : ℕ))
          (volume.restrict (cubeSetAt y n)) :=
        (u.memL2.sub (iterationPartialSum w J).memL2).integrable_sq
      have hHint : Integrable
          (fun x => ((iterationPartialSum w J).toFun x - seriesTail wRep 0 x) ^ (2 : ℕ))
          (volume.restrict (cubeSetAt y n)) :=
        ((iterationPartialSum w J).memL2.sub hmemU).integrable_sq
      have hsumint : Integrable
          (fun x => 2 * (u.toFun x - (iterationPartialSum w J).toFun x) ^ (2 : ℕ) +
            2 * ((iterationPartialSum w J).toFun x - seriesTail wRep 0 x) ^ (2 : ℕ))
          (volume.restrict (cubeSetAt y n)) := (hGint.const_mul 2).add (hHint.const_mul 2)
      have hptw : ∀ x : Vec d, (u.toFun x - seriesTail wRep 0 x) ^ (2 : ℕ) ≤
          2 * (u.toFun x - (iterationPartialSum w J).toFun x) ^ (2 : ℕ) +
            2 * ((iterationPartialSum w J).toFun x - seriesTail wRep 0 x) ^ (2 : ℕ) := by
        intro x
        set a : ℝ := u.toFun x - (iterationPartialSum w J).toFun x with hadef
        set b : ℝ := (iterationPartialSum w J).toFun x - seriesTail wRep 0 x with hbdef
        have hab : u.toFun x - seriesTail wRep 0 x = a + b := by
          rw [hadef, hbdef]; ring
        have hsq : 0 ≤ (a - b) ^ (2 : ℕ) := sq_nonneg _
        have hexp : (a - b) ^ (2 : ℕ) = 2 * a ^ (2 : ℕ) + 2 * b ^ (2 : ℕ) - (a + b) ^ (2 : ℕ) := by
          ring
        rw [hab]
        linarith only [hsq, hexp]
      have hHle : ∫ x in cubeSetAt y n,
          ((iterationPartialSum w J).toFun x - seriesTail wRep 0 x) ^ (2 : ℕ) ∂volume ≤
          (volume.restrict (cubeSetAt y n)).real Set.univ * delta J ^ (2 : ℕ) := by
        have h := integral_mono_ae hHint (integrable_const (delta J ^ (2 : ℕ))) (hdeltabound J)
        rwa [MeasureTheory.integral_const, smul_eq_mul] at h
      calc ∫ x in cubeSetAt y n, (u.toFun x - seriesTail wRep 0 x) ^ (2 : ℕ) ∂volume
          ≤ ∫ x in cubeSetAt y n,
              (2 * (u.toFun x - (iterationPartialSum w J).toFun x) ^ (2 : ℕ) +
                2 * ((iterationPartialSum w J).toFun x - seriesTail wRep 0 x) ^ (2 : ℕ))
              ∂volume := integral_mono hFint hsumint hptw
        _ = 2 * (∫ x in cubeSetAt y n,
              (u.toFun x - (iterationPartialSum w J).toFun x) ^ (2 : ℕ) ∂volume) +
            2 * (∫ x in cubeSetAt y n,
              ((iterationPartialSum w J).toFun x - seriesTail wRep 0 x) ^ (2 : ℕ) ∂volume) := by
            rw [integral_add (hGint.const_mul 2) (hHint.const_mul 2), integral_const_mul,
              integral_const_mul]
        _ ≤ 2 * (∫ x in cubeSetAt y n,
              (u.toFun x - (iterationPartialSum w J).toFun x) ^ (2 : ℕ) ∂volume) +
            2 * ((volume.restrict (cubeSetAt y n)).real Set.univ *
              delta J ^ (2 : ℕ)) := by
            linarith only [hHle]
    have hzeroint : ∫ x in cubeSetAt y n,
        (u.toFun x - seriesTail wRep 0 x) ^ (2 : ℕ) ∂volume = 0 := by
      refine le_antisymm ?_ (integral_nonneg fun x => by positivity)
      have hlimit : Filter.Tendsto (fun J : ℕ =>
          2 * (∫ x in cubeSetAt y n,
              (u.toFun x - (iterationPartialSum w J).toFun x) ^ (2 : ℕ) ∂volume) +
            2 * ((volume.restrict (cubeSetAt y n)).real Set.univ *
              delta J ^ (2 : ℕ))) Filter.atTop (nhds 0) := by
        have h1 : Filter.Tendsto (fun J : ℕ => 2 * (∫ x in cubeSetAt y n,
            (u.toFun x - (iterationPartialSum w J).toFun x) ^ (2 : ℕ) ∂volume))
            Filter.atTop (nhds 0) := by simpa using hAtends.const_mul 2
        have h2 : Filter.Tendsto (fun J : ℕ =>
            2 * ((volume.restrict (cubeSetAt y n)).real Set.univ *
              delta J ^ (2 : ℕ))) Filter.atTop (nhds 0) := by
          have hd2 : Filter.Tendsto (fun J : ℕ => delta J ^ (2 : ℕ)) Filter.atTop (nhds 0) := by
            simpa using hdeltatends.pow 2
          simpa using (hd2.const_mul
            ((volume.restrict (cubeSetAt y n)).real Set.univ)).const_mul 2
        simpa using h1.add h2
      exact ge_of_tendsto hlimit (Filter.Eventually.of_forall hbound)
    have hae := (integral_eq_zero_iff_of_nonneg
      (f := fun x => (u.toFun x - seriesTail wRep 0 x) ^ (2 : ℕ))
      (fun x => by positivity) hFint).1 hzeroint
    filter_upwards [hae] with x hx
    have hx0 : (u.toFun x - seriesTail wRep 0 x) ^ (2 : ℕ) = 0 := hx
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hx0
    change seriesTail wRep 0 x = u.toFun x
    linarith only [this]
  · intro x hx z hz
    have h := abs_seriesTail_sub_le hd hK0 hrho0 hrho1 hrep hzero hK 0 hx hz
    rw [pow_zero, mul_one] at h
    simpa only [Real.norm_eq_abs] using h
  · intro x hx z hz
    have hsx := (summable_wRep hd hK0 hrho0 hrho1 hrep hzero hK hx).sum_add_tsum_nat_add 1
    have hsz := (summable_wRep hd hK0 hrho0 hrho1 hrep hzero hK hz).sum_add_tsum_nat_add 1
    have hex : seriesTail wRep 0 x - wRep 0 x = seriesTail wRep 1 x := by
      simp only [seriesTail, Nat.add_zero]
      rw [← hsx]
      simp
    have hez : seriesTail wRep 0 z - wRep 0 z = seriesTail wRep 1 z := by
      simp only [seriesTail, Nat.add_zero]
      rw [← hsz]
      simp
    have h := abs_seriesTail_sub_le hd hK0 hrho0 hrho1 hrep hzero hK 1 hx hz
    rw [pow_one] at h
    rw [Real.norm_eq_abs]
    calc |seriesTail wRep 0 x - wRep 0 x - (seriesTail wRep 0 z - wRep 0 z)|
        = |seriesTail wRep 1 x - seriesTail wRep 1 z| := by rw [hex, hez]
      _ ≤ K0 * rho / (1 - rho) * ‖x - z‖ ^ (1 / 2 : ℝ) := h

end Limit

end

end Algsuperdiff.Section5.Provider
