/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.TraceDiff
public import LeanPool.HyperellipticCurves.Log.Cantor.PipelineCerts
public import LeanPool.HyperellipticCurves.Log.Charts.DiskIdentification
public import LeanPool.HyperellipticCurves.Log.Charts.PhiChart

/-!
# Transporting the trace matrix to the chart coordinates

The trace matrix `ChabautyColeman.traceMat` of the trace-form route lives on three data — the
**universal** chart datum over `MvPowerSeries (Fin n) O`, where the formal identity
`C(X)M(X) = C(0)` holds; the **global** chart datum over the function field, where
`2y·Θ_i = x^i` holds; and the **per-disk** datum over `O⟦z⟧`, which is where the two meet.
The substitution `X_j ↦ ζ_j` relating the first two is not a ring homomorphism on power
series, but each of its two halves is:

* `ChabautyColeman.traceMat_phiPipeline`: the universal chart datum maps onto the disk datum
  under the coefficient homomorphism `θ` sending the chart variables to the disk chart
  coordinates (`ChabautyColeman.map_chartU_eq_phiPipeline_fst`,
  `ChabautyColeman.map_chartV_eq_phiPipeline_snd`), so the disk trace matrix is `θ` of the
  universal one;
* `ChabautyColeman.globExpand_traceMat`: the disk expansion carries the global pipeline to the
  `φ`-pipeline (`ChabautyColeman.map_globExpand_globPipeline`), so the expansion of the global
  trace matrix is the disk one.

Both go through `ChabautyColeman.traceMat_map` — the matrix is built from `%ₘ` by a monic
polynomial and coefficient extraction, so a ring homomorphism passes straight through it — and
in both the two cofactors involved need not correspond, since the matrix does not depend on
that choice (`ChabautyColeman.traceMat_congr`).

Blueprint node: `thm:omega-prime-global`, clause (c).
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

section DiskChart

open scoped PowerSeries

variable {O : Type*} [CommRing O] {n : ℕ}
  {f : O[X]} {a b xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ : O[X]} {d : CantorCertData O⟦X⟧}

/-- The image of the chart `u`-polynomial under a coefficient homomorphism sending the
`j`-th variable to the `j`-th chart coordinate of a monic polynomial `U` of the center's
degree is `U` itself. -/
theorem map_chartU_eq_of_chartCoords {U : Polynomial O⟦X⟧} (hne : uτ.natDegree = n)
    (θ : MvPowerSeries (Fin n) O →+* O⟦X⟧)
    (hθC : θ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) = PowerSeries.C)
    (hθX : ∀ j : Fin n,
      θ (MvPowerSeries.X j) = chartCoords PowerSeries.C uτ U (Fin.cast hne.symm j))
    (huτ : uτ.Monic) (hUm : U.Monic) (hUdeg : U.natDegree = uτ.natDegree) :
    (chartU uτ n).map θ = U := by
  subst hne
  rw [chartU, Polynomial.map_add, Polynomial.map_map, hθC, Polynomial.map_sum,
    eq_add_chartCoords (φ := PowerSeries.C) huτ hUm hUdeg]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hθX j,
    Fin.cast_refl, id_eq]

/-- The image of the chart `u`-polynomial under a coefficient homomorphism sending the
`j`-th variable to the disk chart coordinate `phiZeta j` is the `u`-part of the disk
pipeline. -/
theorem map_chartU_eq_phiPipeline_fst (hne : uτ.natDegree = n)
    (θ : MvPowerSeries (Fin n) O →+* O⟦X⟧)
    (hθC : θ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) = PowerSeries.C)
    (hθX : ∀ j : Fin n,
      θ (MvPowerSeries.X j) = phiZeta f a b xQ yQ m m₀ uτ vτ d (Fin.cast hne.symm j))
    (huτ : uτ.Monic) (hmonic : (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1.Monic)
    (hdeg : (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1.natDegree = uτ.natDegree) :
    (chartU uτ n).map θ = (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1 :=
  map_chartU_eq_of_chartCoords hne θ hθC hθX huτ hmonic hdeg

variable [IsLocalRing O]

/-- Two power series whose constant coefficients differ by an element of the maximal
ideal have the same residue. -/
theorem residue_eq_of_constantCoeff_sub_mem {x y : O⟦X⟧}
    (h : PowerSeries.constantCoeff x - PowerSeries.constantCoeff y ∈ maximalIdeal O) :
    residue O⟦X⟧ x = residue O⟦X⟧ y := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    PowerSeries.isUnit_iff_constantCoeff, map_sub]
  exact mem_nonunits_iff.mp ((mem_maximalIdeal _).mp h)

/-- A polynomial over `O⟦z⟧` whose constant-coefficient image is `q` agrees with
`q` modulo the maximal ideal, coefficientwise. -/
theorem map_residue_eq {P : Polynomial O⟦X⟧} {q : O[X]}
    (h : P.map (PowerSeries.constantCoeff : O⟦X⟧ →+* O) = q) :
    P.map (residue O⟦X⟧) = (q.map (PowerSeries.C : O →+* O⟦X⟧)).map (residue O⟦X⟧) := by
  refine Polynomial.ext fun k ↦ ?_
  simp only [Polynomial.coeff_map]
  refine residue_eq_of_constantCoeff_sub_mem ?_
  rw [PowerSeries.constantCoeff_C, ← h, Polynomial.coeff_map, sub_self]
  exact zero_mem _

/-- The image of the chart square root under a coefficient homomorphism sending the
variables to the chart coordinates of a monic `U` is the square root `V` belonging to `U`:
both are square roots of `f` modulo `U`, of degree `< deg U`, with the same reduction `vτ`,
and such a square root is unique over the local ring `O⟦z⟧`. -/
theorem map_chartV_eq_of_chartCoords {w c₁ c₂ : O[X]} {U V : Polynomial O⟦X⟧}
    (hne : uτ.natDegree = n) (θ : MvPowerSeries (Fin n) O →+* O⟦X⟧)
    (hθC : θ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) = PowerSeries.C)
    (hθX : ∀ j : Fin n,
      θ (MvPowerSeries.X j) = chartCoords PowerSeries.C uτ U (Fin.cast hne.symm j))
    (hθ0 : ∀ g, PowerSeries.constantCoeff (θ g) = MvPowerSeries.constantCoeff g)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1) (hUm : U.Monic)
    (hUdeg : U.natDegree = uτ.natDegree)
    (hUres : U.map (PowerSeries.constantCoeff : O⟦X⟧ →+* O) = uτ)
    (hVres : V.map (PowerSeries.constantCoeff : O⟦X⟧ →+* O) = vτ)
    (hVdvd : U ∣ V ^ 2 - f.map PowerSeries.C) (hVdeg : V.degree < U.degree) :
    (chartV hu hne.ge hv hw hbez).map θ = V := by
  have hWres : ((chartV hu hne.ge hv hw hbez).map θ).map (residue O⟦X⟧)
      = (vτ.map (PowerSeries.C : O →+* O⟦X⟧)).map (residue O⟦X⟧) :=
    map_residue_eq (by rw [Polynomial.map_map, show (PowerSeries.constantCoeff : O⟦X⟧ →+* O).comp θ
          = (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) O →+* O) from
        RingHom.ext hθ0, chartV_map_constantCoeff])
  have hbezres : c₁.map ((residue O⟦X⟧).comp (PowerSeries.C : O →+* O⟦X⟧))
        * U.map (residue O⟦X⟧)
      + c₂.map ((residue O⟦X⟧).comp (PowerSeries.C : O →+* O⟦X⟧))
        * (2 * (vτ.map (PowerSeries.C : O →+* O⟦X⟧)).map (residue O⟦X⟧)) = 1 := by
    have h := map_bezout ((residue O⟦X⟧).comp (PowerSeries.C : O →+* O⟦X⟧)) hbez
    rw [map_residue_eq hUres]
    simp only [Polynomial.map_map]
    exact h
  refine eq_of_dvd_sq_sub_of_residue_bezout (f := f.map PowerSeries.C)
    (v := vτ.map (PowerSeries.C : O →+* O⟦X⟧)) hUm ?_ hVdvd ?_ hVdeg hbezres hWres
    (map_residue_eq hVres)
  · rw [← map_chartU_eq_of_chartCoords hne θ hθC hθX hu hUm hUdeg]
    exact chartU_map_dvd_chartV_map_sq_sub hu hne.ge hv hw hbez hθC
  · have hdegU : U.degree = uτ.degree := by
      rw [degree_eq_natDegree hUm.ne_zero, hUdeg, degree_eq_natDegree hu.ne_zero]
    rw [hdegU]
    exact Polynomial.degree_map_le.trans_lt (chartV_degree_lt hu hne.ge hv hw hbez)

variable [IsDomain O] [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- The image of the chart square root under a coefficient homomorphism sending the
variables to the disk chart coordinates is the `v`-part of the disk pipeline
(square-root uniqueness over the local ring `O⟦z⟧`). -/
theorem map_chartV_eq_phiPipeline_snd {w c₁ c₂ : O[X]} (hne : uτ.natDegree = n)
    (θ : MvPowerSeries (Fin n) O →+* O⟦X⟧)
    (hθC : θ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) = PowerSeries.C)
    (hθX : ∀ j : Fin n,
      θ (MvPowerSeries.X j) = phiZeta f a b xQ yQ m m₀ uτ vτ d (Fin.cast hne.symm j))
    (hθ0 : ∀ g, PowerSeries.constantCoeff (θ g) = MvPowerSeries.constantCoeff g)
    (hf : f.Monic) (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree) :
    (chartV hu hne.ge hv hw hbez).map θ = (phiPipeline f a b xQ yQ m m₀ uτ vτ d).2 := by
  obtain ⟨hPmonic, hPdvd, hPdeg⟩ :=
    phiPipeline_monic_dvd_degree_lt hsep hm hm₀ hb hfa h2 hyQ hu ⟨w, hw⟩ hcerts
  have hconst := phiPipeline_map_constantCoeff hf hsep hm hm₀ hb hfa h2 hyQ hu hv ⟨w, hw⟩
    hgτ hcerts
  exact map_chartV_eq_of_chartCoords hne θ hθC hθX hθ0 hu hv hw hbez hPmonic hcerts.hdeg
    hconst.1 hconst.2 hPdvd hPdeg

end DiskChart

section TraceDisk

open scoped PowerSeries

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsDomain O] {n : ℕ}
  {f : O[X]} {a b xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ : O[X]} {d : CantorCertData O⟦X⟧}
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  {cs s : Polynomial (MvPowerSeries (Fin n) O)} {cφ sφ : Polynomial O⟦X⟧}

/-- **The trace matrix specializes along the chart substitution.** The universal chart datum
maps onto the disk pipeline datum under the coefficient homomorphism `θ` that sends the chart
variables to the disk chart coordinates (`ChabautyColeman.map_chartU_eq_phiPipeline_fst` and
`ChabautyColeman.map_chartV_eq_phiPipeline_snd`), so the trace matrix of the disk datum is the
`θ`-image of the universal one — the cofactors need not correspond, the matrix not depending
on that choice. This is the substitution `X_j ↦ ζ_j(z)` in the only form in which it is a ring
homomorphism. -/
theorem traceMat_phiPipeline {w c₁ c₂ : O[X]} (hne : uτ.natDegree = n)
    (θ : MvPowerSeries (Fin n) O →+* O⟦X⟧)
    (hθC : θ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) = PowerSeries.C)
    (hθX : ∀ j : Fin n,
      θ (MvPowerSeries.X j) = phiZeta f a b xQ yQ m m₀ uτ vτ d (Fin.cast hne.symm j))
    (hθ0 : ∀ g, PowerSeries.constantCoeff (θ g) = MvPowerSeries.constantCoeff g)
    (hf : f.Monic) (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree)
    (hs : cs * chartU uτ n + s * (2 * chartV hu hne.ge hv hw hbez) = 1)
    (hsφ : cφ * (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1
      + sφ * (2 * (phiPipeline f a b xQ yQ m m₀ uτ vτ d).2) = 1) (i j : ℕ) :
    traceMat (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1 sφ i j
      = θ (traceMat (chartU uτ n) s i j) := by
  obtain ⟨hPmonic, -, -⟩ :=
    phiPipeline_monic_dvd_degree_lt hsep hm hm₀ hb hfa h2 hyQ hu ⟨w, hw⟩ hcerts
  have hU := map_chartU_eq_phiPipeline_fst hne θ hθC hθX hu hPmonic hcerts.hdeg
  have hV := map_chartV_eq_phiPipeline_snd hne θ hθC hθX hθ0 hf hsep hm hm₀ hb hfa h2 hyQ
    hu hv hw hbez hgτ hcerts
  have hsθ : cs.map θ * (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1
      + s.map θ * (2 * (phiPipeline f a b xQ yQ m m₀ uτ vτ d).2) = 1 := by
    have h := map_bezout θ hs
    rwa [hU, hV] at h
  rw [← traceMat_map θ (chartU_monic hu hne.ge) s i j, hU]
  exact traceMat_congr hPmonic hsφ hsθ i j

end TraceDisk

end ChabautyColeman

end
