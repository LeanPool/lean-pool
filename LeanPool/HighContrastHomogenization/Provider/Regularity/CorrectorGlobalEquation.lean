/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalH1sLoc
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineRegularityJointAssembly
public import LeanPool.HighContrastHomogenization.Analytic.ClassPairing

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorGlobalEquation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Globalizing compatible local weak equations

A compactly supported test lies in one member of the centered-cube
exhaustion.  A weak equation available on every exhaustion cube therefore
gives the equation on all of Euclidean space.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set

noncomputable section

/-- Every compact set lies in one centered cube of the exhaustion. -/
theorem exists_localGradientCube_superset_of_isCompact {d : ℕ}
    {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ localGradientCube d n := by
  obtain ⟨R, hR, hKR⟩ := exists_euclideanBall_superset_of_isCompact hK
  obtain ⟨n, hn⟩ := exists_closedBall_zero_subset_localGradientCube hR
  refine ⟨n, fun x hx => hn ?_⟩
  exact Metric.ball_subset_closedBall
    (euclideanBallAt_subset_metricBall (0 : Vec d) hR (hKR hx))

/-- Weak equations on every centered exhaustion cube globalize to the whole
space, since each test function has compact support. -/
theorem isWeakSolutionOn_univ_of_localGradientCube
    {d : ℕ} {b : CoeffField d} {F : Vec d → Vec d}
    (hlocal : ∀ n : ℕ, IsWeakSolutionOn b (localGradientCube d n) F) :
    IsWeakSolutionOn b Set.univ F := by
  intro φ hφ
  obtain ⟨n, hsupport⟩ :=
    exists_localGradientCube_superset_of_isCompact hφ.hasCompactSupport
  have hφcube : IsLocalTest (localGradientCube d n) φ :=
    ⟨hφ.contDiff, hφ.hasCompactSupport, hsupport⟩
  obtain ⟨hint, hzero⟩ := hlocal n φ hφcube
  let f : Vec d → ℝ := fun x =>
    vecDot (smoothGrad φ x) (matVecMul (b x) (F x))
  have hfzero : ∀ x, x ∉ localGradientCube d n → f x = 0 := by
    intro x hx
    have hxnot : x ∉ tsupport φ := fun hmem => hx (hsupport hmem)
    simp only [f, smoothGrad_eq_zero_of_notMem_tsupport hxnot,
      vecDot_zero_left]
  refine ⟨?_, ?_⟩
  · exact hint.of_forall_sdiff_eq_zero MeasurableSet.univ fun x hx => hfzero x hx.2
  · change ∫ x in Set.univ, f x ∂volume = 0
    rw [setIntegral_univ]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hfzero]
    exact hzero

/-- An `H1Function` whose gradient is coefficient-harmonic satisfies the
project's weak-solution predicate. -/
theorem isWeakSolutionOn_of_isAHarmonicGradient
    {d : ℕ} {U : Set (Vec d)} {b : CoeffField d} {lam Lam : ℝ}
    (hU : IsOpen U) (hEll : IsEllipticFieldOn lam Lam U b)
    (u : H1Function U) (hu : IsAHarmonicGradient b U u.grad) :
    IsWeakSolutionOn b U u.grad := by
  intro φ hφ
  let ψ : H10Function U := H10Function.ofContDiff hU
    hφ.contDiff hφ.hasCompactSupport hφ.tsupport_subset
  have hψgrad : ψ.toH1Function.grad = smoothGrad φ := rfl
  have hflux : MemVectorL2 U (fun x => matVecMul (b x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have htest : MemVectorL2 U (smoothGrad φ) := by
    simpa only [← hψgrad] using ψ.toH1Function.grad_memVectorL2
  refine ⟨integrableOn_vecDot_of_memVectorL2 htest hflux, ?_⟩
  have hzero := hu.2 ψ
  simpa only [hψgrad, vecDot_comm] using hzero

/-- The weak-solution predicate is invariant under a.e. replacement of both
the coefficient and vector-field representatives. -/
theorem IsWeakSolutionOn.congr_ae
    {d : ℕ} {U : Set (Vec d)} {a b : CoeffField d}
    {F G : Vec d → Vec d}
    (hab : a =ᵐ[volume.restrict U] b)
    (hFG : F =ᵐ[volume.restrict U] G)
    (h : IsWeakSolutionOn a U F) : IsWeakSolutionOn b U G := by
  intro φ hφ
  obtain ⟨hint, hzero⟩ := h φ hφ
  have heq : (fun x => vecDot (smoothGrad φ x) (matVecMul (a x) (F x)))
      =ᵐ[volume.restrict U]
      fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (G x)) := by
    filter_upwards [hab, hFG] with x hax hFx
    simp only [hax, hFx]
  refine ⟨hint.congr heq, ?_⟩
  calc
    ∫ x in U, vecDot (smoothGrad φ x) (matVecMul (b x) (G x)) ∂volume =
        ∫ x in U, vecDot (smoothGrad φ x) (matVecMul (a x) (F x)) ∂volume :=
      integral_congr_ae heq.symm
    _ = 0 := hzero

/-- A joint local affine-corrector equation globalizes for any coefficient
representative agreeing a.e. with every centered-cube public coefficient. -/
theorem IsFiniteAffineCorrectionJointLocalEquation.isWeakSolutionOn_global
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {Phi : Vec d → NormalizedLocalH1Carrier d}
    (hPhi : IsFiniteAffineCorrectionJointLocalEquation a Phi)
    {b : CoeffField d}
    (hcoeff : ∀ n : ℕ,
      Book.Ch03.publicCoeffField (originCube d (n : ℤ)) a
        =ᵐ[volume.restrict (localGradientCube d n)] b)
    (e : Vec d) :
    IsWeakSolutionOn b Set.univ
      (fun x => e + (Phi e).globalGradientRepresentative x) := by
  apply isWeakSolutionOn_univ_of_localGradientCube
  intro n
  let u : H1Function (localGradientCube d n) :=
    (show H1Function (localGradientCube d n) from by
      simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
        finiteAffineBoundaryH1 (n : ℤ) e) + (Phi e).localH1Function n
  let bpub : CoeffField d := Book.Ch03.publicCoeffField (originCube d (n : ℤ)) a
  have hlocalCoeff :
      (a.coeffOn (originCube d (n : ℤ))).toCoeffField
        =ᵐ[volume.restrict (localGradientCube d n)] bpub := by
    simpa only [localGradientCube, bpub] using
      (Book.Ch03.publicCoeffField_ae_eq_openCubeSet
        (originCube d (n : ℤ)) a).symm
  have hharm : IsAHarmonicGradient bpub (localGradientCube d n) u.grad :=
    IsAHarmonicGradient.of_ae_eq_coeff hlocalCoeff (by
      simpa only [u] using hPhi.2 e n)
  have hEll : IsEllipticFieldOn
      (a.coeffOn (originCube d (n : ℤ))).lam
      (a.coeffOn (originCube d (n : ℤ))).Lam
      (localGradientCube d n) bpub := by
    simpa only [localGradientCube, bpub, Book.Ch02.cubeDomain_coe] using
      Book.Ch03.publicCoeffField_isEllipticFieldOn
        (originCube d (n : ℤ)) a
  have hweak : IsWeakSolutionOn bpub (localGradientCube d n) u.grad :=
    isWeakSolutionOn_of_isAHarmonicGradient
      (by simpa only [localGradientCube] using
        isOpen_openCubeSet (originCube d (n : ℤ))) hEll u hharm
  have hgrad : u.grad =ᵐ[volume.restrict (localGradientCube d n)]
      fun x => e + (Phi e).globalGradientRepresentative x := by
    have hboundary :
        (show H1Function (localGradientCube d n) from by
          simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
            finiteAffineBoundaryH1 (n : ℤ) e).grad = fun _ => e := by
      simpa only using! finiteAffineBoundaryH1_grad (m := (n : ℤ)) e
    have hae := (Phi e).globalGradientRepresentative_ae_eq_localH1Gradient n
    filter_upwards [hae] with x hx
    simp only [u, H1Function.add_grad, hboundary, hx]
  exact hweak.congr_ae (hcoeff n) hgrad

end

end HighContrast
end HCPolySupport
