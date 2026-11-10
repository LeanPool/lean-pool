/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Charts.InfIdentification
public import LeanPool.HyperellipticCurves.Log.Charts.InfTransport
public import LeanPool.HyperellipticCurves.Log.Ftau.Ftau
public import LeanPool.HyperellipticCurves.Log.Trace.TraceInf

import LeanPool.HyperellipticCurves.Log.Charts.InfGlue
import LeanPool.HyperellipticCurves.Log.Trace.TraceDisk

/-!
# Base change for the infinity-chart blocks

What the infinity-chart capstone `LeanPool.HyperellipticCurves.Log.Trace.TraceKzInf` needs about the
two-block Cantor addition and about the transported chart datum: the two-block addition survives
base change and computes the expected class, the coordinate series still solves its defining
equation after mapping, and the transported chart `u`- and `v`-parts are the closed
infinity-disk data of `LeanPool.HyperellipticCurves.Log.Charts.InfChart` (the disk side is not a
certified
pipeline but the scaled construction there, so the two sides meet by uniqueness of reduced
representatives).

## Main statements

* `ChabautyColeman.IsAddCerts.map`, `ChabautyColeman.mk0_cantorStage₂`: base change and the
  class computation for the two-block Cantor addition;
* `ChabautyColeman.map_infSeries_eq`: the mapped coordinate series still solves `u = z²·F(u)`;
* `ChabautyColeman.natDegree_odd_squarefree_map_comp`: oddness and squarefreeness survive the
  composition with the chart substitution;
* `ChabautyColeman.traceMat_infU`: the trace matrix of the transported `u`-part.

Blueprint node: `thm:omega-prime-global`, clause (c), infinity chart.
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped PowerSeries

namespace ChabautyColeman

/-! ### Base change and class computation for the two-block addition -/

section AddMap

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
  {f : R[X]} {D : PipelineData R} {dt : CantorCertData R} {n : ℕ}

/-- A valid two-block certificate pack stays valid under base change. -/
theorem IsAddCerts.map [Nontrivial S] (hu₁ : D.u₁.Monic) (hu₂ : D.u₂.Monic)
    (hcerts : IsAddCerts f D dt n) : IsAddCerts (f.map φ) (D.map φ) (dt.map φ) n := by
  obtain ⟨h1a, h1b⟩ := Prod.ext_iff.mp (cantorStage₁_map φ (f := f) (d := dt) hu₁ hu₂)
  dsimp only at h1a h1b
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
      CantorCertData.map_s₁, CantorCertData.map_s₂, CantorCertData.map_s₃,
      PipelineData.map_u₁, PipelineData.map_v₁, PipelineData.map_u₂,
      PipelineData.map_v₂] using congrArg (Polynomial.map φ) hcerts.hbez
  · have hS₁m : (cantorStage₁ f D dt).1.Monic := cantorCompose_monic f hu₁ hu₂
    have h := map_reduceCert φ f hS₁m hcerts.hc
    rwa [h1a, h1b] at h
  · obtain ⟨h2a, -⟩ := Prod.ext_iff.mp (cantorStage₂_map φ hu₁ hu₂ hcerts.hc)
    dsimp only at h2a
    have hm : (cantorStage₂ f D dt).1.Monic := cantorReduce_monic f hcerts.hc
    rw [← h2a, hm.natDegree_map]
    exact hcerts.hdeg

end AddMap

section AddClass

open nonZeroDivisors

variable {K : Type*} [Field K] {f : K[X]} {D : PipelineData K} [NeZero (2 : K)]
  [Fact (Odd f.natDegree)] [Fact (Squarefree f)] {dt : CantorCertData K} {n : ℕ}

/-- **The two-block Cantor addition computes the product class.** -/
theorem mk0_cantorStage₂ (hu₁ : D.u₁.Monic) (hd₁ : D.u₁ ∣ D.v₁ ^ 2 - f) (hu₂ : D.u₂.Monic)
    (hd₂ : D.u₂ ∣ D.v₂ ^ 2 - f) (hcerts : IsAddCerts f D dt n) :
    ClassGroup.mk0 ⟨mumfordIdeal f (cantorStage₂ f D dt).1 (cantorStage₂ f D dt).2,
        mumfordIdeal_mem_nonZeroDivisors f
          (cantorStage₂_monic_dvd_degree_lt hu₁ hd₁ hu₂ hd₂ hcerts).1.ne_zero _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f D.u₁ D.v₁,
            mumfordIdeal_mem_nonZeroDivisors f hu₁.ne_zero D.v₁⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f D.u₂ D.v₂,
            mumfordIdeal_mem_nonZeroDivisors f hu₂.ne_zero D.v₂⟩ :=
  (mk0_cantorReduce f (cantorCompose_monic f hu₁ hu₂)
    (cantorCompose_dvd f hcerts.hbez hd₁ hd₂) hcerts.hc).symm.trans
    (mk0_cantorCompose f hu₁ hu₂ hcerts.hbez hd₁ hd₂)

end AddClass

/-! ### Transport preliminaries -/

section InfBlockTransport

variable {O : Type*} [CommRing O] {K : Type*} [Field K] {ψ : O →+* K} {f : O[X]}

variable (hf : f.Monic)

/-- The mapped infinity coordinate series still solves `u = z²·F(u)`. -/
theorem map_infSeries_eq :
    PowerSeries.map ψ (infSeries hf) = PowerSeries.X ^ 2
      * aeval (PowerSeries.map ψ (infSeries hf)) (f.map ψ).reverse := by
  have hrev : (f.map ψ).reverse = f.reverse.map ψ := by
    rw [Polynomial.reverse, Polynomial.reverse, hf.natDegree_map, reflect_map]
  have h := congrArg (PowerSeries.map ψ) (infSeries_eq hf)
  rw [map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_aeval] at h
  rwa [hrev]

end InfBlockTransport

section MapComp

variable {O : Type*} [CommRing O] {K : Type*} [Field K] [CharZero K] {ψ : O →+* K}
  {f : O[X]} [Fact (Odd (f.map ψ).natDegree)] [Fact (Squarefree (f.map ψ))]

/-- The curve polynomial base-changed along a factorization `χ = σ ∘ ψ` keeps its degree,
its oddness and its squarefreeness. -/
theorem natDegree_odd_squarefree_map_comp {L : Type*} [Field L] {σ : K →+* L}
    {χ : O →+* L} (hf : f.Monic) (hχ : σ.comp ψ = χ) :
    (f.map χ).natDegree = f.natDegree ∧ Odd (f.map χ).natDegree ∧ Squarefree (f.map χ) := by
  have hmap : (f.map ψ).map σ = f.map χ := by rw [Polynomial.map_map, hχ]
  have hdeg : (f.map χ).natDegree = f.natDegree := by
    rw [← hmap, (hf.map ψ).natDegree_map, hf.natDegree_map]
  refine ⟨hdeg, ?_, ?_⟩
  · rw [hdeg, ← hf.natDegree_map ψ]
    exact Fact.out
  · rw [← hmap]
    exact squarefree_map_of_perfectField σ Fact.out

end MapComp

section InfDiskChart

variable {O : Type*} [CommRing O] [IsDomain O] {n : ℕ} {f uτ vτ : O[X]}

variable [IsLocalRing O]

/-- **The trace matrix specializes along the infinity chart substitution** — the analogue
of `ChabautyColeman.traceMat_wPipeline`. -/
theorem traceMat_infU {w c₁ c₂ : O[X]}
    {cs s : Polynomial (MvPowerSeries (Fin n) O)} {cφ sφ : Polynomial O⟦X⟧}
    (hf : f.Monic) (hne : uτ.natDegree = n)
    (θ : MvPowerSeries (Fin n) O →+* O⟦X⟧)
    (hθC : θ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) = PowerSeries.C)
    (hθX : ∀ j : Fin n, θ (MvPowerSeries.X j) = infZeta hf uτ vτ (Fin.cast hne.symm j))
    (hθ0 : ∀ g, PowerSeries.constantCoeff (θ g) = MvPowerSeries.constantCoeff g)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
    (hvτ : vτ.natDegree < uτ.natDegree) (hdeg : f.natDegree = 2 * uτ.natDegree + 1)
    {V : (O⟦X⟧)[X]} (hV : C PowerSeries.X * V = -(infV hf uτ vτ %ₘ infU hf uτ vτ))
    (hVdeg : V.degree < (infU hf uτ vτ).degree)
    (hVdvd : infU hf uτ vτ ∣ V ^ 2 - f.map PowerSeries.C)
    (hs : cs * chartU uτ n + s * (2 * chartV hu hne.ge hv hw hbez) = 1)
    (hsφ : cφ * infU hf uτ vτ + sφ * (2 * V) = 1) (i j : ℕ) :
    traceMat (infU hf uτ vτ) sφ i j = θ (traceMat (chartU uτ n) s i j) := by
  have hdvdτ : uτ ∣ vτ ^ 2 - f := ⟨w, hw⟩
  have hUm : (infU hf uτ vτ).Monic := infU_monic hf hu hvτ hdeg hdvdτ
  have hUdeg := natDegree_infU hf hu hvτ hdeg hdvdτ
  have hU := map_chartU_eq_of_chartCoords hne θ hθC hθX hu hUm hUdeg
  have hVe := map_chartV_eq_of_chartCoords hne θ hθC hθX hθ0 hu hv hw hbez hUm hUdeg
    (map_constantCoeff_infU hf hu hvτ hdeg hdvdτ)
    (map_constantCoeff_infVred hf hu hvτ hdeg hdvdτ hv hV) hVdvd hVdeg
  have hsθ : cs.map θ * infU hf uτ vτ + s.map θ * (2 * V) = 1 := by
    have h := map_bezout θ hs
    rwa [hU, hVe] at h
  rw [← traceMat_map θ (chartU_monic hu hne.ge) s i j, hU]
  exact traceMat_congr hUm hsφ hsθ i j

end InfDiskChart

end ChabautyColeman

end
