/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LipschitzRepresentative
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.External.CubeSchauder
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ZeroExtensionGraph

/-!
# RepresentativeComparator

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Lipschitz representative of a zero-trace solution with bounded gradient

A zero-trace `H¹` function on `y + □_n` whose stored gradient field is bounded
by `Ksup` at every point of the cube has a Lipschitz representative, and that
representative is bounded on the whole cube by `d · Ksup · 3^n / 2`.

The two constants carry a factor `d`, which is the price of the supremum norm on
`Vec d = Fin d → ℝ` and is sharp: a linear function whose `d` partial
derivatives all equal `Ksup` has increments `d · Ksup · ‖x - z‖`.  The second
constant is `d · Ksup` times the distance from a point of the cube to the
complement of its closure, which is at most half the side length `3^n`.

## Main results

* `exists_lipschitzRepresentative_of_zeroTrace`.
* `exists_lipschitzRepresentative_comparator`.

## References

* ABK26, the localized Dirichlet problems of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Geometry: a nearby point outside the closed cube -/

theorem cubeSetAt_subset_cubeSetAt_succ (y : Vec d) (n : ℤ) :
    cubeSetAt y n ⊆ cubeSetAt y (n + 1) := by
  intro x hx
  rw [mem_cubeSetAt_iff_forall_coord] at hx ⊢
  intro i
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hsucc : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have h := hx i
  rw [hsucc]
  constructor <;> linarith only [h.1, h.2, h3]

/-- From a point of `y + □_n` one reaches, at distance at most half the side
length plus `t`, a point of `y + □_{n+1}` that is outside the closure of
`y + □_n`. -/
private theorem exists_exterior_point (hd : 0 < d) {y : Vec d} {n : ℤ} {x : Vec d}
    (hx : x ∈ cubeSetAt y n) {t : ℝ} (ht : 0 < t) (ht' : t < (3 : ℝ) ^ n) :
    ∃ z : Vec d, z ∈ cubeSetAt y (n + 1) ∧ z ∉ closure (cubeSetAt y n) ∧
      ‖x - z‖ ≤ (3 : ℝ) ^ n / 2 + t := by
  classical
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hsucc : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  set i0 : Fin d := ⟨0, hd⟩ with hi0
  rw [mem_cubeSetAt_iff_forall_coord] at hx
  set c : ℝ := x i0 - y i0 with hc
  have hcbd := hx i0
  set s : ℝ := if 0 ≤ c then (3 : ℝ) ^ n / 2 - c + t else -((3 : ℝ) ^ n / 2) - c - t with hs
  set z : Vec d := x + s • basisVec i0 with hz
  have hzcoord_i0 : z i0 - y i0 = c + s := by
    simp only [hz, Pi.add_apply, Pi.smul_apply, basisVec, Pi.single_eq_same, smul_eq_mul,
      mul_one, hc]
    ring
  have hzcoord_ne : ∀ j : Fin d, j ≠ i0 → z j - y j = x j - y j := by
    intro j hj
    simp [hz, basisVec, hj]
  have hshift : c + s = if 0 ≤ c then (3 : ℝ) ^ n / 2 + t else -((3 : ℝ) ^ n / 2) - t := by
    by_cases hcc : 0 ≤ c <;> simp [hs, hcc] <;> ring
  have habs_shift : |c + s| = (3 : ℝ) ^ n / 2 + t := by
    rw [hshift]
    by_cases hcc : 0 ≤ c
    · rw [ite_eq_left hcc, abs_of_nonneg (by linarith)]
    · rw [ite_eq_right hcc, abs_of_nonpos (by linarith)]
      ring
  have habs_s : |s| ≤ (3 : ℝ) ^ n / 2 + t := by
    by_cases hcc : 0 ≤ c
    · rw [hs, ite_eq_left hcc, abs_of_nonneg (by linarith [hcbd.2])]
      linarith
    · rw [hs, ite_eq_right hcc]
      rw [abs_of_nonpos (by linarith [hcbd.1])]
      linarith [hcbd.1]
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [mem_cubeSetAt_iff_forall_coord]
    intro j
    rw [hsucc]
    by_cases hj : j = i0
    · subst hj
      rw [hzcoord_i0]
      have hle := abs_le.1 habs_shift.le
      constructor <;> linarith [hle.1, hle.2, ht']
    · rw [hzcoord_ne j hj]
      have hj' := hx j
      constructor <;> linarith [hj'.1, hj'.2, h3]
  · rw [Metric.mem_closure_iff]
    push Not
    refine ⟨t, ht, fun q hq => ?_⟩
    rw [mem_cubeSetAt_iff_forall_coord] at hq
    have hqi := hq i0
    rw [dist_eq_norm]
    have hcoord : |z i0 - q i0| ≤ ‖z - q‖ := by
      have := norm_le_pi_norm (z - q) i0
      rwa [Pi.sub_apply, Real.norm_eq_abs] at this
    have hsplit : z i0 - q i0 = (c + s) - (q i0 - y i0) := by
      rw [← hzcoord_i0]; ring
    refine le_trans ?_ hcoord
    rw [hsplit]
    rcases le_or_gt 0 c with hcc | hcc
    · rw [hshift, ite_eq_left hcc]
      rw [abs_of_nonneg (by linarith [hqi.2])]
      linarith [hqi.2]
    · rw [hshift, ite_eq_right (not_le.2 hcc)]
      rw [abs_of_nonpos (by linarith [hqi.1])]
      linarith [hqi.1]
  · refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun j => ?_
    have hxz : (x - z) j = -(s * basisVec i0 j) := by
      simp [hz, Pi.sub_apply, basisVec, Pi.single_apply]
    rw [Real.norm_eq_abs, hxz, abs_neg, abs_mul]
    have hb : |basisVec i0 j| ≤ 1 := by
      by_cases hj : j = i0 <;> simp [basisVec, hj]
    calc |s| * |basisVec i0 j| ≤ |s| * 1 :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = |s| := mul_one _
      _ ≤ (3 : ℝ) ^ n / 2 + t := habs_s

/-! ## 2. The representative of a zero-trace solution with bounded gradient -/

/-- **A zero-trace `H¹` function whose stored gradient field is bounded on
`y + □_n` has a Lipschitz representative, and that representative is bounded on
the whole cube.**

Both constants carry the factor `d` of the supremum-norm geometry; the sup bound
is `d · Ksup` times half the side length, the distance from a point of the cube
to the complement of its closure. -/
theorem exists_lipschitzRepresentative_of_zeroTrace {y : Vec d} {n : ℤ} (hd : 0 < d)
    {v : H1Function (cubeSetAt y n)} {Ksup : ℝ} (hKsup : 0 ≤ Ksup)
    (hw : ∃ w : H10Function (cubeSetAt y n),
        (∀ x, v.toFun x = w.toH1Function.toFun x) ∧
          (∀ x, v.grad x = w.toH1Function.grad x))
    (hgrad : ∀ x ∈ cubeSetAt y n, ‖v.grad x‖ ≤ Ksup) :
    ∃ vRep : Vec d → ℝ,
      v.toFun =ᵐ[volume.restrict (cubeSetAt y n)] vRep ∧
        LipschitzWith (Real.toNNReal ((d : ℝ) * Ksup)) vRep ∧
          supNormOn (cubeSetAt y n) vRep ≤
            ENNReal.ofReal ((d : ℝ) * Ksup * (3 : ℝ) ^ n / 2) := by
  obtain ⟨w, hwf, hwg⟩ := hw
  have hUmeas : MeasurableSet (cubeSetAt y n) := measurableSet_cubeSetAt y n
  have hVopen : IsOpen (cubeSetAt y (n + 1)) := isOpen_cubeSetAt y (n + 1)
  have hUV : cubeSetAt y n ⊆ cubeSetAt y (n + 1) := cubeSetAt_subset_cubeSetAt_succ y n
  have hdK : (0 : ℝ) ≤ (d : ℝ) * Ksup := by positivity
  have hGbd : ∀ x, ‖(H10Function.extendByZeroToOpenSuperset w hUmeas hVopen
      hUV).toH1Function.grad x‖ ≤ Ksup := by
    intro x
    rw [H10Function.extendByZeroToOpenSuperset_grad]
    by_cases hx : x ∈ cubeSetAt y n
    · rw [H10Function.zeroExtensionGrad_apply_of_mem _ hx, ← hwg x]
      exact hgrad x hx
    · rw [H10Function.zeroExtensionGrad_apply_of_not_mem _ hx]
      simpa using hKsup
  obtain ⟨vRep, hLip, hae⟩ :=
    exists_lipschitzWith_representative_of_hasWeakGradientOn
      (isOpenBoundedConvexDomain_cubeSetAt y (n + 1)) (cubeSetAt_nonempty y (n + 1)) hKsup
      (H10Function.extendByZeroToOpenSuperset w hUmeas hVopen hUV).toH1Function.memL2
      (H10Function.extendByZeroToOpenSuperset w hUmeas hVopen hUV).toH1Function.gradMemL2
      (H10Function.extendByZeroToOpenSuperset w hUmeas hVopen hUV).toH1Function.hasWeakGradient
      hGbd
  have hvae : v.toFun =ᵐ[volume.restrict (cubeSetAt y n)] vRep := by
    have haeU := hae.filter_mono (ae_mono (Measure.restrict_mono hUV le_rfl))
    filter_upwards [haeU, ae_restrict_mem hUmeas] with x hx1 hx2
    rw [hwf x]
    rw [H10Function.extendByZeroToOpenSuperset_toFun,
      H10Function.zeroExtension_apply_of_mem w hx2] at hx1
    exact hx1
  have hOopen : IsOpen (cubeSetAt y (n + 1) ∩ (closure (cubeSetAt y n))ᶜ) :=
    hVopen.inter isClosed_closure.isOpen_compl
  have haeO : vRep =ᵐ[volume.restrict
      (cubeSetAt y (n + 1) ∩ (closure (cubeSetAt y n))ᶜ)] (0 : Vec d → ℝ) := by
    have hOsub : cubeSetAt y (n + 1) ∩ (closure (cubeSetAt y n))ᶜ ⊆ cubeSetAt y (n + 1) :=
      Set.inter_subset_left
    have h1 := hae.filter_mono (ae_mono (Measure.restrict_mono hOsub le_rfl))
    filter_upwards [h1, ae_restrict_mem hOopen.measurableSet] with x hx1 hx2
    have hxU : x ∉ cubeSetAt y n := fun hcon => hx2.2 (subset_closure hcon)
    rw [H10Function.extendByZeroToOpenSuperset_toFun,
      H10Function.zeroExtension_apply_of_not_mem w hxU] at hx1
    exact hx1.symm
  have hzeroOn : Set.EqOn vRep 0 (cubeSetAt y (n + 1) ∩ (closure (cubeSetAt y n))ᶜ) :=
    eqOn_of_ae_eq_of_continuousOn hOopen haeO hLip.continuous.continuousOn continuousOn_const
  refine ⟨vRep, hvae, hLip, ?_⟩
  rw [supNormOn_le_ofReal_iff (by positivity)]
  intro x hx
  rw [Real.norm_eq_abs]
  refine le_of_forall_pos_le_add fun eps heps => ?_
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hden : (0 : ℝ) < (d : ℝ) * Ksup + 1 := by linarith
  have ht : 0 < min (eps / ((d : ℝ) * Ksup + 1)) ((3 : ℝ) ^ n / 2) :=
    lt_min (by positivity) (by positivity)
  have ht' : min (eps / ((d : ℝ) * Ksup + 1)) ((3 : ℝ) ^ n / 2) < (3 : ℝ) ^ n :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨z, hzV, hzcl, hdist⟩ := exists_exterior_point hd hx ht ht'
  have hz0 : vRep z = 0 := hzeroOn ⟨hzV, hzcl⟩
  have hlipxz : |vRep x| ≤ (d : ℝ) * Ksup * ‖x - z‖ := by
    have hdd := hLip.dist_le_mul x z
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hdK, hz0, sub_zero] at hdd
    exact hdd
  have hteps : (d : ℝ) * Ksup * min (eps / ((d : ℝ) * Ksup + 1)) ((3 : ℝ) ^ n / 2) ≤ eps := by
    have hfrac : (d : ℝ) * Ksup / ((d : ℝ) * Ksup + 1) ≤ 1 := (div_le_one hden).2 (by linarith)
    calc (d : ℝ) * Ksup * min (eps / ((d : ℝ) * Ksup + 1)) ((3 : ℝ) ^ n / 2)
        ≤ (d : ℝ) * Ksup * (eps / ((d : ℝ) * Ksup + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hdK
      _ = eps * ((d : ℝ) * Ksup / ((d : ℝ) * Ksup + 1)) := by ring
      _ ≤ eps * 1 := mul_le_mul_of_nonneg_left hfrac heps.le
      _ = eps := mul_one eps
  calc |vRep x| ≤ (d : ℝ) * Ksup * ‖x - z‖ := hlipxz
    _ ≤ (d : ℝ) * Ksup *
          ((3 : ℝ) ^ n / 2 + min (eps / ((d : ℝ) * Ksup + 1)) ((3 : ℝ) ^ n / 2)) :=
        mul_le_mul_of_nonneg_left hdist hdK
    _ = (d : ℝ) * Ksup * (3 : ℝ) ^ n / 2 +
          (d : ℝ) * Ksup * min (eps / ((d : ℝ) * Ksup + 1)) ((3 : ℝ) ^ n / 2) := by ring
    _ ≤ (d : ℝ) * Ksup * (3 : ℝ) ^ n / 2 + eps := by linarith

/-! ## 3. From the Lipschitz bound to the `C^{0,1/2}` gauge -/

/-- **A zero-trace solution with bounded gradient has a representative
continuous on the cube.** -/
theorem hasCubeContinuousRepresentativeAt_of_zeroTrace {y : Vec d} {n : ℤ} (hd : 0 < d)
    {v : H1Function (cubeSetAt y n)} {Ksup : ℝ} (hKsup : 0 ≤ Ksup)
    (hw : ∃ w : H10Function (cubeSetAt y n),
        (∀ x, v.toFun x = w.toH1Function.toFun x) ∧
          (∀ x, v.grad x = w.toH1Function.grad x))
    (hgrad : ∀ x ∈ cubeSetAt y n, ‖v.grad x‖ ≤ Ksup) :
    HasCubeContinuousRepresentativeAt y n v := by
  obtain ⟨vRep, hvae, hLip, -⟩ := exists_lipschitzRepresentative_of_zeroTrace hd hKsup hw hgrad
  exact ⟨vRep, hvae.symm, hLip.continuous.continuousOn⟩

/-! ## 4. The comparator -/

private theorem holderSeminormBoundOn_cubeSetAt_of_originCube {E : Type*} [NormedAddCommGroup E]
    {y : Vec d} {n : ℤ} {alpha K : ℝ} {f : Vec d → E}
    (hf : HolderSeminormBoundOn (openCubeSet (originCube d n)) alpha K f) :
    HolderSeminormBoundOn (cubeSetAt y n) alpha K (fun x => f (x - y)) := by
  intro x hx z hz
  have hsub : (x - y) - (z - y) = x - z := by ring
  have h := hf (x - y) (mem_cubeSetAt_iff.1 hx) (z - y) (mem_cubeSetAt_iff.1 hz)
  rw [hsub] at h
  exact h

/-- **The comparator of Section 5.1 has a Lipschitz representative bounded on
the whole cube.**

At every scale and centre, and for every `1/2`-Hölder forcing field, the
constant-coefficient Dirichlet problem `-σ_n Δ v = ∇·g` on `y + □_n` with zero
boundary values has a solution whose stored gradient field is bounded and
`1/2`-Hölder, with the interior Schauder estimate, and whose values are those of
a `d · Ksup`-Lipschitz function bounded by `d · Ksup · 3^n / 2`.  In particular
the comparator satisfies `HasCubeContinuousRepresentativeAt` unconditionally. -/
theorem exists_lipschitzRepresentative_comparator (d : ℕ) (hdim : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (n : ℤ) (y : Vec d) (g : Vec d → Vec d) (Kg : ℝ),
        HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g →
        ∃ (v : H1Function (cubeSetAt y n)) (vRep : Vec d → ℝ) (Ksup KHol : ℝ),
          IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v g ∧
            0 ≤ Ksup ∧ 0 ≤ KHol ∧
            (∀ x ∈ cubeSetAt y n, ‖v.grad x‖ ≤ Ksup) ∧
            HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) KHol v.grad ∧
            Real.rpow 3 (-((1 / 2 : ℝ) * (n : ℝ))) * Ksup + KHol ≤
              C * (Real.rpow 3 ((1 / 2 : ℝ) * (n : ℝ)))⁻¹ *
                ((Annealed.sigmaBar M n : ℝ)⁻¹ * Real.rpow 3 ((n : ℝ) / 2) * Kg) ∧
            v.toFun =ᵐ[volume.restrict (cubeSetAt y n)] vRep ∧
            LipschitzWith (Real.toNNReal ((d : ℝ) * Ksup)) vRep ∧
            supNormOn (cubeSetAt y n) vRep ≤
              ENNReal.ofReal ((d : ℝ) * Ksup * (3 : ℝ) ^ n / 2) ∧
            HasCubeContinuousRepresentativeAt y n v := by
  obtain ⟨C, hC, hmain⟩ :=
    Algsuperdiff.Frozen.External.cube_schauder hdim (1 / 2 : ℝ) (by norm_num) le_rfl
  refine ⟨C, hC, fun M n y g Kg hg => ?_⟩
  have hd : 0 < d := by omega
  have hzeroGrad : ∀ x ∈ openCubeSet (originCube d n),
      ‖(0 : H1Function (openCubeSet (originCube d n))).grad x‖ ≤ (0 : ℝ) := by
    intro x _
    simp
  have hzeroHol : HolderSeminormBoundOn (openCubeSet (originCube d n)) (1 / 2) 0
      (0 : H1Function (openCubeSet (originCube d n))).grad := by
    simpa using!
      holderSeminormBoundOn_zero (openCubeSet (originCube d n)) (1 / 2 : ℝ) (le_refl (0 : ℝ))
  obtain ⟨vO, hvO, Ksup, KHol, hKsup, hKHol, hsup, hhol, hest⟩ :=
    hmain n (Annealed.sigmaBar M n : ℝ) (Provider.Orlicz.sigmaBar_pos M n)
      (fun x => g (y + x)) 0 Kg 0 0 (holderSeminormBoundOn_originCube_of_cubeSetAt hg)
      hzeroGrad hzeroHol
  have hvgrad : ∀ x, (translateSolution y n vO).grad x = vO.grad (x - y) := by
    intro x
    simp [translateSolution]
  have hvsol : IsDirichletSolutionAt
      (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n (translateSolution y n vO) g := by
    rw [isDirichletSolutionAt_iff_origin, originPullback_translateSolution]
    exact hvO
  have hvsupbd : ∀ x ∈ cubeSetAt y n, ‖(translateSolution y n vO).grad x‖ ≤ Ksup := by
    intro x hx
    rw [hvgrad x]
    exact hsup (x - y) (mem_cubeSetAt_iff.1 hx)
  have hvhol : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) KHol
      (translateSolution y n vO).grad := by
    intro x hx z hz
    rw [hvgrad x, hvgrad z]
    exact holderSeminormBoundOn_cubeSetAt_of_originCube (y := y) hhol x hx z hz
  obtain ⟨vRep, hvae, hLip, hsupN⟩ :=
    exists_lipschitzRepresentative_of_zeroTrace hd hKsup hvsol.1 hvsupbd
  refine ⟨translateSolution y n vO, vRep, Ksup, KHol, hvsol, hKsup, hKHol, hvsupbd, hvhol,
    ?_, hvae, hLip, hsupN,
    hasCubeContinuousRepresentativeAt_of_zeroTrace hd hKsup hvsol.1 hvsupbd⟩
  simpa using hest

end

end Algsuperdiff.Section5.Support
