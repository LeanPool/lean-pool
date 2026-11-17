/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.FoldAssemble
public import LeanPool.HyperellipticCurves.Log.Ftau.ChartMem
public import LeanPool.HyperellipticCurves.Series.LogIso

/-!
# The abelian logarithm on the kernel of reduction (blueprint `def:Lam`)

`ChabautyColeman.ftauFoldFGL` (`LeanPool.HyperellipticCurves.Log.Fold.FoldAssemble`) packages the
translated
Cantor addition `F_τ` — with its unit laws, commutativity (`lem:Ftau-basic`) and
associativity (`thm:Ftau-assoc`), all established at the fold — as a
`ChabautyColeman.FormalGroupLaw`. The abelian logarithm `ChabautyColeman.Lam` sends a
kernel element `c` to the value of the `π`-scaled formal logarithm of `F_τ` at the chart
coordinates of `c + τ` divided by the uniformizer `π` (the scaled coordinates of
`thm:log-iso`, in which `evalT y (HL i)` represents `Λ(π·y)`). It is additive
(`ChabautyColeman.Lam_add`: the chart coordinates of a product are the `F_τ`-sum of the
coordinates by `thm:chart-mem`, which the scaled logarithm turns into addition); its
injectivity (in the unramified case) is formalized in `upstream
HyperellipticCurves.Archive.LogInjective`;
the main theorems do not depend on it.

The pairing `λ` of blueprint `def:lambda1` is `ChabautyColeman.lambdaOne`: for a
coefficient vector `cs` (the coordinates of a regular differential in the `ω′`-basis of
`thm:omega-prime-global`), `λ_ω = ∑_i cs_i · Λ_i` on the kernel of reduction — additive
in the class and linear in `cs`.
-/

@[expose] public section

open Polynomial IsLocalRing MvPowerSeries

namespace ChabautyColeman

section NatCast

variable {O : Type*} [CommRing O] [CharZero (FractionRing O)] {p : ℕ}

/-- The image of a prime in the fraction field is nonzero. -/
theorem algebraMap_natCast_prime_ne_zero (hp : p.Prime) :
    algebraMap O (FractionRing O) (p : O) ≠ 0 := by
  rw [map_natCast]
  exact Nat.cast_ne_zero.mpr hp.ne_zero

end NatCast

section Lam

universe u'

open ChabautyColeman.MvPSeries FormalGroupLaw

variable {O : Type u'} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [UniformSpace O] [Fact (IsAdic (IsLocalRing.maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [CharZero (FractionRing O)] [IsAlgClosed (ResidueField O)]
  [NeZero (2 : ResidueField O)] [NeZero (2 : FractionRing O)]
  {n : ℕ} {f u v w c₁ c₂ : O[X]}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)
  {A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {a b : Fin n → O}
  {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]
  {π : O} {p e : ℕ}

/-- The `π`-scaled chart coordinates of a kernel element: the chart coordinates of
`c + τ` divided by the uniformizer `π`. -/
noncomputable def kerScaledCoords (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) (hram : IsUniformizer π p e)
    (c : (redJHom (K := FractionRing O) (f := f) hf hdeg).ker) : Fin n → O :=
  fun j ↦ (hram.mem_iff.mp
    ((reductionKernelEquivPolydisk hu hne hv hw hbez hf hdeg hfdeg hsq c).2 j)).choose

theorem kerScaledCoords_spec (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) (hram : IsUniformizer π p e)
    (c : (redJHom (K := FractionRing O) (f := f) hf hdeg).ker) (j : Fin n) :
    π * kerScaledCoords hu hne hv hw hbez hf hdeg hfdeg hsq hram c j
      = (reductionKernelEquivPolydisk hu hne hv hw hbez hf hdeg hfdeg hsq c).1 j :=
  (hram.mem_iff.mp
    ((reductionKernelEquivPolydisk hu hne hv hw hbez hf hdeg hfdeg hsq c).2 j)).choose_spec.symm

/-- **The abelian logarithm on the kernel of reduction** (blueprint `def:Lam`), in the
`π`-scaled coordinates of `thm:log-iso`: `Λ(c) = (evalT y (HL i))ᵢ` where `y` is the
chart coordinate vector of `c + τ` divided by `π` and `HL` is the `π`-scaled formal
logarithm of `F_τ`; so `Λ(c)` represents `log_{F_τ}` of the chart coordinates of
`c + τ`. A homomorphism (`ChabautyColeman.Lam_add`; injectivity is formalized in
`upstream HyperellipticCurves.Archive.LogInjective`). -/
noncomputable def Lam (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hbv : ∀ i, v.eval (a i) = b i)
    (hsplit : u = ∏ m, (Polynomial.X - Polynomial.C (a m)))
    (hunit : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (c : (redJHom (K := FractionRing O) (f := f) hf hdeg).ker) : Fin n → O :=
  fun i ↦ evalT (kerScaledCoords hu hne hv hw hbez hf hdeg hfdeg hsq hram c)
    ((ftauFoldFGL hu hne hv hw hbez hf
      ((hf.natDegree_map (algebraMap O (FractionRing O))).symm.trans hfdeg) hroot hcc ha hbv
      hd hram.maximalIdeal_eq hram.ne_zero_of_charZero_fractionRing hsplit hunit).scaledLog hram hpe
      (algebraMap O (FractionRing O)) (algebraMap_natCast_prime_ne_zero hram.prime) i)

/-- **The chart equivalence is multiplicative** (blueprint `thm:chart-mem`): the chart
coordinates of a product of two kernel elements are obtained by evaluating the translated
Cantor addition `F_τ` at the pair of coordinate vectors of the factors. -/
theorem J1_equiv_polydisk_mul (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hbv : ∀ i, v.eval (a i) = b i)
    (hsplit : u = ∏ m, (Polynomial.X - Polynomial.C (a m)))
    (hunit : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (c₁ c₂ : (redJHom (K := FractionRing O) (f := f) hf hdeg).ker) :
    (reductionKernelEquivPolydisk hu hne hv hw hbez hf hdeg hfdeg hsq (c₁ * c₂)).1
      = fun j ↦ MvPSeries.eval
          (Sum.elim (reductionKernelEquivPolydisk hu hne hv hw hbez hf hdeg hfdeg hsq c₁).1
            (reductionKernelEquivPolydisk hu hne hv hw hbez hf hdeg hfdeg hsq c₂).1)
          (FtauFold A a b hu hne hv hw hbez d j) := by
  set E := reductionKernelEquivPolydisk hu hne hv hw hbez hf hdeg hfdeg hsq
  have hx : ∀ s, Sum.elim (E c₁).1 (E c₂).1 s ∈ maximalIdeal O := fun s ↦ by
    cases s with
    | inl s => exact (E c₁).2 s
    | inr s => exact (E c₂).2 s
  have hfdegO : f.natDegree = 2 * n + 1 :=
    (hf.natDegree_map (algebraMap O (FractionRing O))).symm.trans hfdeg
  have he : ∀ j, MvPSeries.eval (Sum.elim (E c₁).1 (E c₂).1)
      (FtauFold A a b hu hne hv hw hbez d j) ∈ maximalIdeal O := fun j ↦
    eval_FtauFold_mem hu hne hv hw hbez hf hfdegO hroot hcc ha hbv hd hx j
  have hptk : ∀ c, polydiskToKer hu hne hv hw hbez hf hdeg hsq (E c) = c := fun c ↦
    (Equiv.ofBijective _
      (polydiskToKer_bijective hu hne hv hw hbez hf hdeg hfdeg hsq)).apply_symm_apply c
  have hprod : polydiskToKer hu hne hv hw hbez hf hdeg hsq
      ⟨fun j ↦ MvPSeries.eval (Sum.elim (E c₁).1 (E c₂).1)
        (FtauFold A a b hu hne hv hw hbez d j), he⟩ = c₁ * c₂ := by
    rw [polydiskToKer_eval_FtauFold hu hne hv hw hbez hf hdeg hfdegO hsq hroot hcc ha hbv
      hd hsplit hunit (E c₁).2 (E c₂).2 rfl he, hptk c₁, hptk c₂]
  have hEeq : E (c₁ * c₂) = ⟨fun j ↦ MvPSeries.eval (Sum.elim (E c₁).1 (E c₂).1)
      (FtauFold A a b hu hne hv hw hbez d j), he⟩ :=
    (congrArg E hprod).symm.trans ((Equiv.ofBijective _
      (polydiskToKer_bijective hu hne hv hw hbez hf hdeg hfdeg hsq)).symm_apply_apply _)
  exact congrArg Subtype.val hEeq

/-- **The abelian logarithm is a homomorphism** (blueprint `def:Lam`, via
`thm:chart-mem` and `thm:log-iso`). -/
theorem Lam_add (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hbv : ∀ i, v.eval (a i) = b i)
    (hsplit : u = ∏ m, (Polynomial.X - Polynomial.C (a m)))
    (hunit : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (c₁ c₂ : (redJHom (K := FractionRing O) (f := f) hf hdeg).ker) :
    Lam hu hne hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe (c₁ * c₂)
      = Lam hu hne hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe c₁
        + Lam hu hne hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe c₂ := by
  classical
  -- the chart coordinates of the product are the `F_τ`-sum of the coordinates
  have hcoords := J1_equiv_polydisk_mul hu hne hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv
    hsplit hunit hd c₁ c₂
  set Φ := ftauFoldFGL hu hne hv hw hbez hf
      ((hf.natDegree_map (algebraMap O (FractionRing O))).symm.trans hfdeg) hroot hcc ha hbv
      hd hram.maximalIdeal_eq hram.ne_zero_of_charZero_fractionRing hsplit hunit with hΦ
  set E := reductionKernelEquivPolydisk hu hne hv hw hbez hf hdeg hfdeg hsq with hE
  set y₁ := kerScaledCoords hu hne hv hw hbez hf hdeg hfdeg hsq hram c₁ with hy₁
  set y₂ := kerScaledCoords hu hne hv hw hbez hf hdeg hfdeg hsq hram c₂ with hy₂
  set y₁₂ := kerScaledCoords hu hne hv hw hbez hf hdeg hfdeg hsq hram (c₁ * c₂) with hy₁₂
  have hx : ∀ s, Sum.elim (E c₁).1 (E c₂).1 s ∈ maximalIdeal O := fun s ↦ by
    cases s with
    | inl s => exact (E c₁).2 s
    | inr s => exact (E c₂).2 s
  -- the scaled coordinates of the product are the scaled `F_τ`-sum
  have hFΦ : Φ.F = FtauFold A a b hu hne hv hw hbez d := rfl
  have hyprod : y₁₂ = fun j ↦ evalT (Sum.elim y₁ y₂) (Φ.scaledF π j) := by
    funext j
    refine mul_left_cancel₀ hram.ne_zero_of_charZero_fractionRing ?_
    rw [hy₁₂, kerScaledCoords_spec hu hne hv hw hbez hf hdeg hfdeg hsq hram (c₁ * c₂) j,
      ← hE, hcoords, Φ.mul_evalT_scaledF hram.mem (Sum.elim y₁ y₂) j, hFΦ]
    have hfam : (fun s ↦ π * Sum.elim y₁ y₂ s) = Sum.elim (E c₁).1 (E c₂).1 := by
      funext s
      cases s with
      | inl s =>
        rw [Sum.elim_inl, Sum.elim_inl, hy₁,
          kerScaledCoords_spec hu hne hv hw hbez hf hdeg hfdeg hsq hram c₁ s, ← hE]
      | inr s =>
        rw [Sum.elim_inr, Sum.elim_inr, hy₂,
          kerScaledCoords_spec hu hne hv hw hbez hf hdeg hfdeg hsq hram c₂ s, ← hE]
    rw [hfam, MvPSeries.evalT_eq_eval (hz₀ := MvPSeries.hasEval_of_mem hx) _]
  funext i
  simp only [Lam, Pi.add_apply]
  rw [← hΦ, ← hy₁₂, ← hy₁, ← hy₂, hyprod]
  exact Φ.evalT_scaledLog_add hram hpe
    (FaithfulSMul.algebraMap_injective O (FractionRing O)) _ y₁ y₂ i

/-- The abelian logarithm sends the trivial class to `0`. -/
theorem Lam_one (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hbv : ∀ i, v.eval (a i) = b i)
    (hsplit : u = ∏ m, (Polynomial.X - Polynomial.C (a m)))
    (hunit : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p) :
    Lam hu hne hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe 1 = 0 := by
  have h := Lam_add hu hne hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv
    hsplit hunit hd hram hpe 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

/-- **The pairing `λ` in `ω′`-coordinates** (blueprint `def:lambda1`): for a coefficient
vector `cs` — the coordinates of a regular differential `ω` in the basis `(ω'_i)` of
`thm:omega-prime-global`(c) — the functional `λ_ω = ∑_i cs_i · Λ_i` on the kernel of
reduction, valued in `Frac(O)`. Additive in the class
(`ChabautyColeman.lambdaOne_mul`) and linear in `cs`
(`ChabautyColeman.lambdaOne_add_left`, `ChabautyColeman.lambdaOne_smul_left`). -/
noncomputable def lambdaOne (cs : Fin n → FractionRing O) (hf : f.Monic)
    (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hbv : ∀ i, v.eval (a i) = b i)
    (hsplit : u = ∏ m, (Polynomial.X - Polynomial.C (a m)))
    (hunit : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (c : (redJHom (K := FractionRing O) (f := f) hf hdeg).ker) : FractionRing O :=
  ∑ i, cs i * algebraMap O (FractionRing O)
    (Lam hu hne hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe c i)

/-- `λ` is additive in the class (blueprint `def:lambda1`), via the additivity of the
abelian logarithm. -/
theorem lambdaOne_mul (cs : Fin n → FractionRing O) (hf : f.Monic)
    (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hbv : ∀ i, v.eval (a i) = b i)
    (hsplit : u = ∏ m, (Polynomial.X - Polynomial.C (a m)))
    (hunit : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (c₁' c₂' : (redJHom (K := FractionRing O) (f := f) hf hdeg).ker) :
    lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe (c₁' * c₂')
      = lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
          hsplit hunit hd hram hpe c₁'
        + lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
            hsplit hunit hd hram hpe c₂' := by
  simp only [lambdaOne, Lam_add hu hne hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv
      hsplit hunit hd hram hpe c₁' c₂',
    Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/-- `λ` is additive in the differential coordinates (blueprint `def:lambda1`). -/
theorem lambdaOne_add_left (cs cs' : Fin n → FractionRing O) (hf : f.Monic)
    (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hbv : ∀ i, v.eval (a i) = b i)
    (hsplit : u = ∏ m, (Polynomial.X - Polynomial.C (a m)))
    (hunit : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (c : (redJHom (K := FractionRing O) (f := f) hf hdeg).ker) :
    lambdaOne hu hne hv hw hbez (cs + cs') hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe c
      = lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe c
        + lambdaOne hu hne hv hw hbez cs' hf hdeg hfdeg hsq hroot hcc ha hbv
            hsplit hunit hd hram hpe c := by
  simp only [lambdaOne, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- `λ` is homogeneous in the differential coordinates (blueprint `def:lambda1`). -/
theorem lambdaOne_smul_left (r : FractionRing O) (cs : Fin n → FractionRing O)
    (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hbv : ∀ i, v.eval (a i) = b i)
    (hsplit : u = ∏ m, (Polynomial.X - Polynomial.C (a m)))
    (hunit : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (c : (redJHom (K := FractionRing O) (f := f) hf hdeg).ker) :
    lambdaOne hu hne hv hw hbez (r • cs) hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe c
      = r * lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
          hsplit hunit hd hram hpe c := by
  simp only [lambdaOne, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- `λ` sends the trivial class to `0` (blueprint `def:lambda1`). -/
theorem lambdaOne_one (cs : Fin n → FractionRing O) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hbv : ∀ i, v.eval (a i) = b i)
    (hsplit : u = ∏ m, (Polynomial.X - Polynomial.C (a m)))
    (hunit : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p) :
    lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe 1 = 0 := by
  simp [lambdaOne, Lam_one hu hne hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv
      hsplit hunit hd hram hpe]

/-- `λ` sends a finite product of kernel classes to the sum of its values (blueprint
`def:lambda1`), iterating `ChabautyColeman.lambdaOne_mul`. -/
theorem lambdaOne_prod (cs : Fin n → FractionRing O) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hbv : ∀ i, v.eval (a i) = b i)
    (hsplit : u = ∏ m, (Polynomial.X - Polynomial.C (a m)))
    (hunit : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    {ι : Type*} (s : Finset ι)
    (cd : ι → (redJHom (K := FractionRing O) (f := f) hf hdeg).ker) :
    lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe (∏ t ∈ s, cd t)
      = ∑ t ∈ s, lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
          hsplit hunit hd hram hpe (cd t) := by
  induction s using Finset.cons_induction with
  | empty =>
    simpa using lambdaOne_one hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
      hsplit hunit hd hram hpe
  | cons t s hts ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      lambdaOne_mul hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
          hsplit hunit hd hram hpe, ih]

end Lam

end ChabautyColeman

end
