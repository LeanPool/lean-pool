/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ConstantInvariance
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.DirichletSolvability
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionLinearity

/-!
# SolutionScaling

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Homogeneity of the localized regularity

The localized regularity `X(y+□_n)` is a supremum over the *normalized* forcing
class `[g]_{C^{0,1/2}(y+□_n)} ≤ 3^{-n/2}`, so by itself it says nothing about a
solution whose datum is not normalized.  The localized Dirichlet problem is
homogeneous of degree one in the pair `(solution, datum)`, so a datum with a
finite Hölder seminorm is brought into the class by the scalar factor
`3^{-n/2} [g]^{-1}`, and the bound for the normalized datum transfers with the
reciprocal factor.

This module proves that homogeneity and the resulting general bound.

## Main results

* `holderSeminormOn_const_smul` — the Hölder seminorm is homogeneous.
* `isDirichletSolutionAt_const_smul`, `isCubeRepresentative_const_smul` — the
  problem and its continuous representatives are homogeneous.
* `isDivFormWeakSolutionOn_congr_ae`, `isDirichletSolutionAt_congr_eqOn` — the
  weak equation only sees the forcing field on the cube, up to a null set.
* `localizedRegularity_apply_general` — the bound for an arbitrary datum of
  finite Hölder seminorm.
* `holderSeminormOn_le_localizedRegularity` — the same, evaluated at a named
  continuous representative.
* `exists_isCubeRepresentative_of_localizedRegularity_ne_top` — a finite
  localized regularity produces a continuous representative of every solution
  with a datum of finite Hölder seminorm.

## References

* ABK26, the localized regularity of Section 5.1 and its use in the iteration
  of Proposition 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The Hölder seminorm is homogeneous -/

/-- **The Hölder seminorm scales.**  For a nonnegative factor the seminorm of
`t f` is `t` times the seminorm of `f`, the identity holding in `ℝ≥0∞` also when
the seminorm is infinite and when `t = 0`. -/
theorem holderSeminormOn_const_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set (Vec d)) (alpha : ℝ) {t : ℝ} (ht : 0 ≤ t) (f : Vec d → E) :
    holderSeminormOn U alpha (fun x => t • f x) =
      ENNReal.ofReal t * holderSeminormOn U alpha f := by
  simp only [holderSeminormOn, ENNReal.mul_iSup]
  refine iSup_congr fun x => iSup_congr fun _ => iSup_congr fun z => iSup_congr fun _ =>
    iSup_congr fun _ => ?_
  rw [← ENNReal.ofReal_mul ht]
  congr 1
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, mul_div_assoc]

/-- The scalar case of the previous statement, in multiplicative notation. -/
theorem holderSeminormOn_const_mul (U : Set (Vec d)) (alpha : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (f : Vec d → ℝ) :
    holderSeminormOn U alpha (fun x => t * f x) =
      ENNReal.ofReal t * holderSeminormOn U alpha f := by
  simpa only [smul_eq_mul] using holderSeminormOn_const_smul (E := ℝ) U alpha ht f

/-- The Hölder seminorm of the zero field vanishes. -/
theorem holderSeminormOn_zero {E : Type*} [NormedAddCommGroup E] (U : Set (Vec d))
    (alpha : ℝ) :
    holderSeminormOn U alpha (fun _ : Vec d => (0 : E)) = 0 := by
  refine le_antisymm ?_ zero_le
  simp only [holderSeminormOn, iSup_le_iff]
  intro x _ z _ _
  simp

/-! ## 2. The localized Dirichlet problem is homogeneous -/

/-- **Representatives scale.** -/
theorem isCubeRepresentative_const_smul {y : Vec d} {n : ℤ}
    {u : H1Function (cubeSetAt y n)} {uRep : Vec d → ℝ} (t : ℝ)
    (h : IsCubeRepresentative y n u uRep) :
    IsCubeRepresentative y n (t • u) (fun x => t * uRep x) := by
  refine ⟨?_, continuousOn_const.mul h.2⟩
  filter_upwards [h.1] with x hx
  show t * uRep x = (t • u).toFun x
  rw [H1Function.smul_toFun, hx]

/-- **The localized Dirichlet problem is homogeneous of degree one.** -/
theorem isDirichletSolutionAt_const_smul {y : Vec d} {n : ℤ} {a : CoeffField d}
    {u : H1Function (cubeSetAt y n)} {g : Vec d → Vec d} (t : ℝ)
    (hu : IsDirichletSolutionAt a y n u g) :
    IsDirichletSolutionAt a y n (t • u) fun x => t • g x := by
  obtain ⟨⟨w, hwf, hwg⟩, heq⟩ := hu
  refine ⟨⟨t • w, fun x => ?_, fun x => ?_⟩, fun phi => ?_⟩
  · change (t • u).toFun x = (t • w.toH1Function).toFun x
    rw [H1Function.smul_toFun, H1Function.smul_toFun]
    change t * u.toFun x = t * w.toH1Function.toFun x
    rw [hwf x]
  · change (t • u).grad x = (t • w.toH1Function).grad x
    simp only [H1Function.smul_grad, hwg x]
  · have hkeyA : ∀ x : Vec d,
        vecDot (matVecMul (a x) ((t • u).grad x)) (phi.toH1Function.grad x) =
          t * vecDot (matVecMul (a x) (u.grad x)) (phi.toH1Function.grad x) := by
      intro x
      rw [H1Function.smul_grad, matVecMul_smul, vecDot_smul_left]
    have hkeyG : ∀ x : Vec d,
        vecDot (t • g x) (phi.toH1Function.grad x) =
          t * vecDot (g x) (phi.toH1Function.grad x) := by
      intro x
      rw [vecDot_smul_left]
    calc ∫ x in cubeSetAt y n,
          vecDot (matVecMul (a x) ((t • u).grad x)) (phi.toH1Function.grad x) ∂volume
        = ∫ x in cubeSetAt y n,
            t * vecDot (matVecMul (a x) (u.grad x)) (phi.toH1Function.grad x) ∂volume := by
          simp only [hkeyA]
      _ = t * ∫ x in cubeSetAt y n,
            vecDot (matVecMul (a x) (u.grad x)) (phi.toH1Function.grad x) ∂volume :=
          integral_const_mul _ _
      _ = t * -∫ x in cubeSetAt y n, vecDot (g x) (phi.toH1Function.grad x) ∂volume := by
          rw [heq phi]
      _ = -∫ x in cubeSetAt y n, t * vecDot (g x) (phi.toH1Function.grad x) ∂volume := by
          rw [integral_const_mul, mul_neg]
      _ = -∫ x in cubeSetAt y n, vecDot (t • g x) (phi.toH1Function.grad x) ∂volume := by
          simp only [hkeyG]

/-! ## 3. The equation only sees the forcing field on the cube -/

/-- **The weak equation is insensitive to a null set of the forcing field.** -/
theorem isDivFormWeakSolutionOn_congr_ae {W : Set (Vec d)} {a : CoeffField d}
    {u : H1Function W} {g g' : Vec d → Vec d}
    (h : g =ᵐ[volume.restrict W] g') :
    IsDivFormWeakSolutionOn a W u g ↔ IsDivFormWeakSolutionOn a W u g' := by
  have hint : ∀ p : Vec d → Vec d,
      ∫ x in W, vecDot (g x) (p x) ∂volume = ∫ x in W, vecDot (g' x) (p x) ∂volume := by
    intro p
    refine integral_congr_ae ?_
    filter_upwards [h] with x hx
    rw [hx]
  constructor <;> intro hsol phi
  · rw [hsol phi, hint fun x => phi.toH1Function.grad x]
  · rw [hsol phi, ← hint fun x => phi.toH1Function.grad x]

/-- **The Dirichlet problem is insensitive to a null set of the forcing
field.** -/
theorem isDirichletSolutionAt_congr_ae {y : Vec d} {n : ℤ} {a : CoeffField d}
    {u : H1Function (cubeSetAt y n)} {g g' : Vec d → Vec d}
    (h : g =ᵐ[volume.restrict (cubeSetAt y n)] g') :
    IsDirichletSolutionAt a y n u g ↔ IsDirichletSolutionAt a y n u g' :=
  and_congr_right' (isDivFormWeakSolutionOn_congr_ae h)

/-- **The Dirichlet problem only sees the forcing field on the cube.** -/
theorem isDirichletSolutionAt_congr_eqOn {y : Vec d} {n : ℤ} {a : CoeffField d}
    {u : H1Function (cubeSetAt y n)} {g g' : Vec d → Vec d}
    (h : Set.EqOn g g' (cubeSetAt y n)) :
    IsDirichletSolutionAt a y n u g ↔ IsDirichletSolutionAt a y n u g' :=
  isDirichletSolutionAt_congr_ae
    ((ae_restrict_iff' (measurableSet_cubeSetAt y n)).2 (Filter.Eventually.of_forall h))

/-- **The zero function solves the homogeneous problem.** -/
theorem isDirichletSolutionAt_zero (a : CoeffField d) (y : Vec d) (n : ℤ) :
    IsDirichletSolutionAt a y n 0 fun _ => 0 := by
  refine ⟨⟨0, fun _ => rfl, fun _ => rfl⟩, fun phi => ?_⟩
  simp only [H1Function.zero_grad, Pi.zero_apply, matVecMul_zero, vecDot_zero_left,
    integral_zero, neg_zero]

/-! ## 4. A datum of vanishing Hölder seminorm forces a vanishing solution -/

/-- **A datum constant on the cube produces the zero solution.**  A vanishing
Hölder seminorm on `y + □_n` says exactly that the forcing field is constant
there, and a constant field pairs to zero against every zero-trace gradient, so
the solution is almost everywhere zero and the zero function is one of its
continuous representatives. -/
theorem isCubeRepresentative_zero_of_holderSeminormOn_eq_zero (M : ABKModel d) (n : ℤ)
    (y : Vec d) (omega : Cutoff.CutoffSample d) {g : Vec d → Vec d}
    (hg0 : holderSeminormOn (cubeSetAt y n) (1 / 2) g = 0)
    {u : H1Function (cubeSetAt y n)}
    (hu : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField)
      y n u g) :
    IsCubeRepresentative y n u fun _ => 0 := by
  have : IsFiniteMeasure (volume.restrict (cubeSetAt y n)) :=
    (isOpenBoundedConvexDomain_cubeSetAt y n).isFiniteMeasure_restrict_volume
  have hbound : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) 0 g := by
    refine (holderSeminormOn_le_ofReal_iff le_rfl).1 ?_
    rw [hg0, ENNReal.ofReal_zero]
  have heqOn : Set.EqOn g (fun _ => g y) (cubeSetAt y n) := by
    intro x hx
    have h := hbound x hx y (mem_cubeSetAt_self y n)
    have hz : ‖g x - g y‖ ≤ 0 := by
      simpa using h
    have : g x - g y = 0 := by
      simpa using le_antisymm hz (norm_nonneg _)
    exact sub_eq_zero.1 this
  have huconst : IsDirichletSolutionAt
      ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n u fun _ => g y :=
    (isDirichletSolutionAt_congr_eqOn heqOn).1 hu
  have hL2 : MemVectorL2 (cubeSetAt y n) fun _ : Vec d => g y := memLp_const _
  have huzero : IsDirichletSolutionAt
      ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n u fun _ => (0 : Vec d) := by
    simpa using isDirichletSolutionAt_sub_const hL2 (g y) huconst
  have hae := (isDirichletSolutionAt_ae_unique_cutoff M n n y omega huzero
    (isDirichletSolutionAt_zero _ y n)).2
  refine ⟨?_, continuousOn_const⟩
  filter_upwards [hae] with x hx
  show (0 : ℝ) = u.toFun x
  rw [hx]
  rfl

/-! ## 5. The infimum over representatives scales -/

/-- **The infimum defining the localized regularity scales.**  Multiplying the
solution by a positive factor multiplies the infimum by the same factor,
including when no continuous representative exists and the infimum is `⊤`. -/
theorem iInf_isCubeRepresentative_const_smul {y : Vec d} {n : ℤ}
    {u : H1Function (cubeSetAt y n)} {t : ℝ} (ht : 0 < t) (c : ℝ≥0∞) :
    (⨅ r : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n (t • u) r,
        c * holderSeminormOn (cubeSetAt y n) (1 / 2) r) =
      ENNReal.ofReal t *
        ⨅ r : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u r,
          c * holderSeminormOn (cubeSetAt y n) (1 / 2) r := by
  by_cases hex : ∃ r : Vec d → ℝ, IsCubeRepresentative y n u r
  · obtain ⟨uRep, huRep⟩ := hex
    rw [iInf_isCubeRepresentative_holderSeminormOn (isCubeRepresentative_const_smul t huRep) c,
      iInf_isCubeRepresentative_holderSeminormOn huRep c,
      holderSeminormOn_const_mul _ _ ht.le, mul_left_comm]
  · have hnone : ¬∃ r : Vec d → ℝ, IsCubeRepresentative y n (t • u) r := by
      rintro ⟨r, hr⟩
      refine hex ⟨fun x => t⁻¹ * r x, ?_⟩
      have := isCubeRepresentative_const_smul t⁻¹ hr
      rwa [inv_smul_smul₀ ht.ne'] at this
    have hL : (⨅ r : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n (t • u) r,
        c * holderSeminormOn (cubeSetAt y n) (1 / 2) r) = ⊤ :=
      eq_top_iff.2 (le_iInf fun r => le_iInf fun hr => absurd ⟨r, hr⟩ hnone)
    have hR : (⨅ r : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u r,
        c * holderSeminormOn (cubeSetAt y n) (1 / 2) r) = ⊤ :=
      eq_top_iff.2 (le_iInf fun r => le_iInf fun hr => absurd ⟨r, hr⟩ hex)
    rw [hL, hR, ENNReal.mul_top]
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact ht

/-! ## 6. The general bound -/

/-- The inner infimum of the localized regularity is bounded by it, for every
normalized datum and every solution. -/
theorem iInf_isCubeRepresentative_le_localizedRegularity (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) {g : Vec d → Vec d} (hg : NormalizedForceAt y n g)
    {u : H1Function (cubeSetAt y n)}
    (hu : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField)
      y n u g) :
    (⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u uRep,
        ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
          holderSeminormOn (cubeSetAt y n) (1 / 2) uRep) ≤
      localizedRegularity M n y omega :=
  le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le u (le_iSup_of_le hu le_rfl)))

private theorem rpow_three_half_mul (n : ℤ) :
    Real.rpow 3 (-(n : ℝ) / 2) * Real.rpow 3 ((n : ℝ) / 2) = 1 := by
  have hsum : (-(n : ℝ) / 2) + ((n : ℝ) / 2) = 0 := by ring
  calc Real.rpow 3 (-(n : ℝ) / 2) * Real.rpow 3 ((n : ℝ) / 2)
      = Real.rpow 3 ((-(n : ℝ) / 2) + ((n : ℝ) / 2)) :=
        (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
    _ = 1 := by rw [hsum]; exact Real.rpow_zero 3

private theorem rpow_three_half_pos (t : ℝ) : (0 : ℝ) < Real.rpow 3 t :=
  Real.rpow_pos_of_pos (by norm_num) t

/-- **The localized regularity bounds every solution, normalized or not.**

For a datum `g` of finite `1/2`-Hölder seminorm on `y + □_n` and any solution
`u` of the rough-field problem with that datum,

```text
  σ_n 3^{-n/2} [u]_{C^{0,1/2}(y+□_n)}
      ≤ X(y+□_n) · 3^{n/2} [g]_{C^{0,1/2}(y+□_n)} ,
```

the left side being the infimum over continuous representatives that the
localized regularity is built from.  The proof is the homogeneity of the
problem: the datum `3^{-n/2}[g]^{-1} g` is normalized and the solution scales
with it. -/
theorem localizedRegularity_apply_general (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) {g : Vec d → Vec d}
    (hg : holderSeminormOn (cubeSetAt y n) (1 / 2) g ≠ ⊤)
    {u : H1Function (cubeSetAt y n)}
    (hu : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField)
      y n u g) :
    (⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u uRep,
        ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
          holderSeminormOn (cubeSetAt y n) (1 / 2) uRep) ≤
      localizedRegularity M n y omega * ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) *
        holderSeminormOn (cubeSetAt y n) (1 / 2) g := by
  set c : ℝ≥0∞ :=
    ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) with hcdef
  set A : ℝ≥0∞ := holderSeminormOn (cubeSetAt y n) (1 / 2) g with hAdef
  set I : ℝ≥0∞ := ⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u uRep,
    c * holderSeminormOn (cubeSetAt y n) (1 / 2) uRep with hIdef
  rcases eq_or_ne A 0 with h0 | h0
  · have hrep : IsCubeRepresentative y n u fun _ => 0 :=
      isCubeRepresentative_zero_of_holderSeminormOn_eq_zero M n y omega h0 hu
    have hIzero : I = 0 := by
      refine le_antisymm ?_ zero_le
      refine le_trans (iInf_le_of_le _ (iInf_le _ hrep)) ?_
      rw [holderSeminormOn_zero, mul_zero]
    rw [hIzero]
    exact zero_le
  · have hApos : 0 < A.toReal := ENNReal.toReal_pos h0 hg
    set t : ℝ := Real.rpow 3 (-(n : ℝ) / 2) / A.toReal with htdef
    have htpos : 0 < t := div_pos (rpow_three_half_pos _) hApos
    have hscaled : holderSeminormOn (cubeSetAt y n) (1 / 2) (fun x => t • g x) =
        ENNReal.ofReal (Real.rpow 3 (-(n : ℝ) / 2)) := by
      rw [holderSeminormOn_const_smul _ _ htpos.le, ← hAdef, ← ENNReal.ofReal_toReal hg,
        ← ENNReal.ofReal_mul htpos.le, htdef, div_mul_cancel₀ _ hApos.ne']
    have hnorm : NormalizedForceAt y n fun x => t • g x := by
      refine (holderSeminormOn_le_ofReal_iff (rpow_three_half_pos _).le).1 ?_
      rw [hscaled]
    have hsol := isDirichletSolutionAt_const_smul (a := _) t hu
    have hle : ENNReal.ofReal t * I ≤ localizedRegularity M n y omega := by
      rw [hIdef, ← iInf_isCubeRepresentative_const_smul htpos c]
      exact iInf_isCubeRepresentative_le_localizedRegularity M n y omega hnorm hsol
    have hne : ENNReal.ofReal t ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact htpos
    have hfin : ENNReal.ofReal t ≠ ⊤ := ENNReal.ofReal_ne_top
    have hinv : I ≤ (ENNReal.ofReal t)⁻¹ * localizedRegularity M n y omega := by
      calc I = (ENNReal.ofReal t)⁻¹ * (ENNReal.ofReal t * I) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hne hfin, one_mul]
        _ ≤ (ENNReal.ofReal t)⁻¹ * localizedRegularity M n y omega := by gcongr
    have hinvval : (ENNReal.ofReal t)⁻¹ = ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) * A := by
      rw [← ENNReal.ofReal_inv_of_pos htpos, ← ENNReal.ofReal_toReal hg,
        ← ENNReal.ofReal_mul (rpow_three_half_pos _).le]
      congr 1
      rw [htdef, inv_div, div_eq_iff (rpow_three_half_pos ((-(n : ℝ) / 2))).ne']
      rw [mul_comm (Real.rpow 3 ((n : ℝ) / 2)) A.toReal, mul_assoc,
        mul_comm (Real.rpow 3 ((n : ℝ) / 2)), rpow_three_half_mul, mul_one]
    rw [hinvval] at hinv
    calc I ≤ ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) * A * localizedRegularity M n y omega :=
          hinv
      _ = localizedRegularity M n y omega * ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) * A := by
          ring

/-- **The general bound, read at a named continuous representative.** -/
theorem holderSeminormOn_le_localizedRegularity (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) {g : Vec d → Vec d}
    (hg : holderSeminormOn (cubeSetAt y n) (1 / 2) g ≠ ⊤)
    {u : H1Function (cubeSetAt y n)} {uRep : Vec d → ℝ}
    (hu : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField)
      y n u g)
    (huRep : IsCubeRepresentative y n u uRep) :
    ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
        holderSeminormOn (cubeSetAt y n) (1 / 2) uRep ≤
      localizedRegularity M n y omega * ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) *
        holderSeminormOn (cubeSetAt y n) (1 / 2) g := by
  rw [← iInf_isCubeRepresentative_holderSeminormOn huRep]
  exact localizedRegularity_apply_general M n y omega hg hu

/-- **A finite localized regularity produces a continuous representative.**  The
infimum defining the localized regularity is `⊤` when the solution has no
continuous representative, so a finite value forces one to exist for every datum
of finite Hölder seminorm. -/
theorem exists_isCubeRepresentative_of_localizedRegularity_ne_top (M : ABKModel d) (n : ℤ)
    (y : Vec d) (omega : Cutoff.CutoffSample d)
    (hL : localizedRegularity M n y omega ≠ ⊤) {g : Vec d → Vec d}
    (hg : holderSeminormOn (cubeSetAt y n) (1 / 2) g ≠ ⊤)
    {u : H1Function (cubeSetAt y n)}
    (hu : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField)
      y n u g) :
    ∃ uRep : Vec d → ℝ, IsCubeRepresentative y n u uRep := by
  by_contra hnone
  have hI : (⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u uRep,
      ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
        holderSeminormOn (cubeSetAt y n) (1 / 2) uRep) = ⊤ :=
    eq_top_iff.2 (le_iInf fun r => le_iInf fun hr => absurd ⟨r, hr⟩ hnone)
  have hbound := localizedRegularity_apply_general M n y omega hg hu
  rw [hI, top_le_iff] at hbound
  exact (ENNReal.mul_ne_top (ENNReal.mul_ne_top hL ENNReal.ofReal_ne_top) hg) hbound

end

end Algsuperdiff.Section5.Support
