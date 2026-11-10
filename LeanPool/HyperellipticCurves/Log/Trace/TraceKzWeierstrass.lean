/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Charts.WeierstrassChart
public import LeanPool.HyperellipticCurves.Log.Trace.TraceChain
public import LeanPool.HyperellipticCurves.Log.Trace.TraceKz

import LeanPool.HyperellipticCurves.Log.Charts.WeierstrassIdentification
import LeanPool.HyperellipticCurves.Log.Fold.FoldTrace

/-!
# The trace-form identity at a Weierstrass centre, per residue disk

Clause (c) of `thm:omega-prime-global` at a Weierstrass centre `(ω, 0)`, run **directly on the
Weierstrass disk pipeline** over `Frac(K⟦z⟧)` with the derivation `d/dz` — the Weierstrass
mirror of `LeanPool.HyperellipticCurves.Log.Trace.TraceKz`, with the chart `x = W(z)`, `y = z`.

* `ChabautyColeman.two_mul_X_mul_traceDiff_wPipeline_map`: the per-disk trace identity —
  in `Frac(K⟦z⟧)`, `2·z·Θ_k = W(z)^k·W′(z)` on the mapped Weierstrass disk pipeline. The
  `τ`-block dies under `d/dz`; the singular constant pair block `[Q + ιP₀]`, `P₀ = (ω, 0)`,
  which admits no Bézout certificate over any ring, is crossed by the Θ-calculus extension
  (T2′) (`ChabautyColeman.traceDiff_cantorPipeline_of_dvd_dotDer`) — the second reduction
  step in its place; and the moving pair block evaluates at the disk
  point `(W(z), z)`, whose `x`-separation from the constant point is a unit outright (its
  constant coefficient is the unit `ω - xQ`).
* `ChabautyColeman.X_mul_omegaPrime_eq_aeval_tracePoly_mul_derivative`: the capstone —
  `z·ω′_i = tracePoly_i(W(z))·W′(z)` on the Weierstrass disk, from per-disk hypotheses only,
  by the shared solve driver `ChabautyColeman.kzOmega`.
* `ChabautyColeman.map_omegaExpansionWeierstrass_eq_sum_smul_omegaPrime_tracePoly`:
  consequently, a polynomial `h₀` whose coordinates in the trace-form basis are `cs` has
  `omegaExpansionWeierstrass h₀ = ∑ᵢ csᵢ·ω′ᵢ` — the `hW` hypothesis of
  `ChabautyColeman.encard_inter_residueDisk_le_ordPoint_weierstrass`.

The file also hosts the per-disk supporting material of the Weierstrass chart: the
chart-substitution transport (`ChabautyColeman.traceMat_wPipeline`), the moving pair block's
certificate over `Frac(K⟦z⟧)` (`ChabautyColeman.isCoprime_wU₁_map`), and the residue-field descent
of the Weierstrass-disk avoidance (`ChabautyColeman.isPipelineAvoid_w_of_residue`).

Blueprint node: `thm:omega-prime-global`, clause (c) (Weierstrass transport).
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped Matrix PowerSeries

namespace ChabautyColeman

/-! ### The Weierstrass chart substitution transports -/

section WeierstrassDiskChart

open scoped PowerSeries

variable {O : Type*} [CommRing O] {n : ℕ}
  {f : O[X]} {ω xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ : O[X]} {d : CantorCertData O⟦X⟧}

variable [IsLocalRing O] [IsDomain O] [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- **The trace matrix specializes along the Weierstrass chart substitution** — the
analogue of `ChabautyColeman.traceMat_phiPipeline`. -/
theorem traceMat_wPipeline {w c₁ c₂ : O[X]}
    {cs s : Polynomial (MvPowerSeries (Fin n) O)} {cφ sφ : Polynomial O⟦X⟧}
    (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω)) (hne : uτ.natDegree = n)
    (θ : MvPowerSeries (Fin n) O →+* O⟦X⟧)
    (hθC : θ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) = PowerSeries.C)
    (hθX : ∀ j : Fin n, θ (MvPowerSeries.X j)
      = wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d (Fin.cast hne.symm j))
    (hθ0 : ∀ g, PowerSeries.constantCoeff (θ g) = MvPowerSeries.constantCoeff g)
    (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
      uτ.natDegree)
    (hs : cs * chartU uτ n + s * (2 * chartV hu hne.ge hv hw hbez) = 1)
    (hsφ : cφ * (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1
      + sφ * (2 * (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).2) = 1) (i j : ℕ) :
    traceMat (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1 sφ i j
      = θ (traceMat (chartU uτ n) s i j) := by
  obtain ⟨hPmonic, hPdvd, hPdeg⟩ :=
    wPipeline_monic_dvd_degree_lt hf hdeg hω hωu hsep hm hm₀ hyQ hu ⟨w, hw⟩ hcerts
  have hconst := wPipeline_map_constantCoeff hf hdeg hω hωu hsep hm hm₀ hyQ hu hv ⟨w, hw⟩
    hgτ hcerts
  have hU := map_chartU_eq_of_chartCoords hne θ hθC hθX hu hPmonic hcerts.hdeg
  have hV := map_chartV_eq_of_chartCoords hne θ hθC hθX hθ0 hu hv hw hbez hPmonic hcerts.hdeg
    hconst.1 hconst.2 hPdvd hPdeg
  have hsθ : cs.map θ * (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1
      + s.map θ * (2 * (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).2) = 1 := by
    have h := map_bezout θ hs
    rwa [hU, hV] at h
  rw [← traceMat_map θ (chartU_monic hu hne.ge) s i j, hU]
  exact traceMat_congr hPmonic hsφ hsθ i j

end WeierstrassDiskChart

/-! ### The residue-field descent of the Weierstrass-disk avoidance -/

section WeierstrassResidue

open scoped PowerSeries

variable {O : Type*} [CommRing O] [IsLocalRing O]
  {f : O[X]} {ω xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ : O[X]} {d : CantorCertData O⟦X⟧}
  {n : ℕ}

/-- The `u`-part of the Weierstrass moving pair reduces to the centre pair `[P₀ + ιQ]`. -/
theorem wU₁_map_seriesResidue (hf : f.Monic) (hdeg : 0 < f.natDegree) (hω : f.eval ω = 0)
    (hωu : IsUnit (f.derivative.eval ω)) :
    (wU₁ hf hdeg hω hωu xQ).map (seriesResidue O) = ((X - C ω) * (X - C xQ)).map (residue O)
    := by
  simp only [wU₁, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, map_C, seriesResidue_C]
  rw [seriesResidue_apply, constantCoeff_weierstrassSeries]

/-- The `v`-part of the Weierstrass moving pair reduces to the centre pair's line. -/
theorem wV₁_map_seriesResidue (hf : f.Monic) (hdeg : 0 < f.natDegree) (hω : f.eval ω = 0)
    (hωu : IsUnit (f.derivative.eval ω)) :
    (wV₁ hf hdeg hω hωu m).map (seriesResidue O)
      = (pairV ω 0 (PowerSeries.constantCoeff m)).map (residue O) := by
  rw [wV₁, pairV_map, pairV_map, seriesResidue_X, seriesResidue_apply,
    constantCoeff_weierstrassSeries, seriesResidue_apply, map_zero]

/-- **The Weierstrass per-disk configuration reduces to the centre configuration.** -/
theorem wConfig_map_seriesResidue (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω)) :
    (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ).map (seriesResidue O)
      = (diskCenterConfig ω 0 xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map
        (residue O) := by
  simp only [PipelineData.map, wConfig, diskConfig, diskCenterConfig,
    wU₁_map_seriesResidue, wV₁_map_seriesResidue, map_C_map_seriesResidue, phiU₃, phiV₃]

variable (hf : f.Monic) (hdeg : 0 < f.natDegree) (hω : f.eval ω = 0)
  (hωu : IsUnit (f.derivative.eval ω)) (huτ : uτ.Monic)
  (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d n)

include huτ hcerts in
/-- **Weierstrass-disk avoidance at the first reduced datum is a residue-field condition**
on the reduced configuration `[P_bar₀ + ι Q_bar] + τ_bar + [Q_bar + ι P_bar₀]`, `P_bar₀ = (ω_bar,
0)`. -/
theorem isCoprime_wStage₂_of_residue
    (h : IsCoprime (cantorStage₂ (f.map (residue O))
        ((diskCenterConfig ω 0 xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O))
          (d.map (seriesResidue O))).1
      (2 * (cantorStage₂ (f.map (residue O))
        ((diskCenterConfig ω 0 xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O))
          (d.map (seriesResidue O))).2)) :
    IsCoprime (cantorStage₂ (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d).1
      (2 * (cantorStage₂ (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d).2) := by
  refine isCoprime_cantorStage₂_of_map (reflectsCoprime_of_ker_le_jacobson
    (seriesResidue_surjective O) (ker_seriesResidue_le_jacobson O))
    ((monic_X_sub_C _).mul (monic_X_sub_C _)) (huτ.map _) hcerts.hc₁ ?_
  rwa [map_C_map_seriesResidue, wConfig_map_seriesResidue]

include huτ hcerts in
/-- **Weierstrass-disk avoidance at the pipeline output is a residue-field condition.** -/
theorem isCoprime_wPipeline_of_residue
    (h : IsCoprime (cantorPipeline (f.map (residue O))
        ((diskCenterConfig ω 0 xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O))
          (d.map (seriesResidue O))).1
      (2 * (cantorPipeline (f.map (residue O))
        ((diskCenterConfig ω 0 xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O))
          (d.map (seriesResidue O))).2)) :
    IsCoprime (cantorPipeline (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d).1
      (2 * (cantorPipeline (f.map PowerSeries.C)
        (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d).2) := by
  refine isCoprime_cantorPipeline_of_map (reflectsCoprime_of_ker_le_jacobson
    (seriesResidue_surjective O) (ker_seriesResidue_le_jacobson O))
    ((monic_X_sub_C _).mul (monic_X_sub_C _)) (huτ.map _)
    (((monic_X_sub_C _).mul (monic_X_sub_C _)).map _) hcerts ?_
  rwa [map_C_map_seriesResidue, wConfig_map_seriesResidue]

include huτ hcerts in
/-- **Weierstrass-disk avoidance is a residue-field condition** on the reduced configuration
`[P_bar₀ + ι Q_bar] + τ_bar + [Q_bar + ι P_bar₀]` with `P_bar₀ = (ω_bar, 0)` the reduced Weierstrass
centre. -/
theorem isPipelineAvoid_w_of_residue
    (h : IsPipelineAvoid (f.map (residue O))
      ((diskCenterConfig ω 0 xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O))
        (d.map (seriesResidue O))) :
    IsPipelineAvoid (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d :=
  ⟨isCoprime_wStage₂_of_residue hf hdeg hω hωu huτ hcerts h.hcop₁,
    isCoprime_wPipeline_of_residue hf hdeg hω hωu huτ hcerts h.hcop₂⟩

end WeierstrassResidue

/-! ### Units over the fraction field of the disk series ring -/

section KzUnits

open scoped PowerSeries

variable {O : Type*} [CommRing O] {K : Type*} [Field K] [NeZero (2 : K)] {ψ : O →+* K}
  {f : O[X]} {ω xQ yQ : O} {m : O⟦X⟧}

/-- `2` is nonzero in `Frac(K⟦z⟧)`. -/
theorem two_ne_zero_fractionRing_powerSeries :
    (2 : FractionRing (PowerSeries K)) ≠ 0 := by
  have h2 : (2 : K⟦X⟧) ≠ 0 := fun h ↦ two_ne_zero (α := K) (by
    have := congrArg PowerSeries.constantCoeff h
    simpa [map_ofNat] using this)
  rw [show (2 : FractionRing (PowerSeries K))
    = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) 2 from (map_ofNat _ 2).symm]
  exact fun h ↦ h2 (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K))
    (by rw [h, map_zero]))

/-- **The Weierstrass moving pair block avoids the Weierstrass points over the fraction
field** `Frac(K⟦z⟧)` — over `O⟦z⟧` it does not: the moving point crosses the centre
`(ω, 0)` at `z = 0`, but `z` is invertible in the fraction field. -/
theorem isCoprime_wU₁_map (hyQu : IsUnit yQ) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X) :
    IsCoprime ((wU₁ hf hdeg hω hωu xQ).map
        ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (PowerSeries.map ψ)))
      (2 * (wV₁ hf hdeg hω hωu m).map
        ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ))) := by
  set ρ : O⟦X⟧ →+* FractionRing (PowerSeries K)
    := (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
      (PowerSeries.map ψ) with hρdef
  have hXinj := IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K))
  have h2 : (2 : FractionRing (PowerSeries K)) ≠ 0 := two_ne_zero_fractionRing_powerSeries
  have hmρ : ρ m * (ρ (PowerSeries.C xQ) - ρ (weierstrassSeries hf hdeg hω hωu))
      = ρ (PowerSeries.C (-yQ)) - ρ PowerSeries.X := by
    rw [← map_sub, ← map_mul, hm, map_sub]
  have hα : IsUnit (2 * ρ PowerSeries.X) := by
    refine isUnit_iff_ne_zero.mpr (mul_ne_zero h2 fun h ↦ ?_)
    rw [hρdef, RingHom.comp_apply, PowerSeries.map_X] at h
    exact PowerSeries.X_ne_zero (hXinj (by rw [h, map_zero]))
  have hβ : IsUnit (2 * ρ (PowerSeries.C (-yQ))) := by
    refine isUnit_iff_ne_zero.mpr (mul_ne_zero h2 fun h ↦ ?_)
    rw [hρdef, RingHom.comp_apply, PowerSeries.map_C] at h
    have h0 : PowerSeries.C (ψ (-yQ)) = (0 : K⟦X⟧) := hXinj (by rw [h, map_zero])
    have hc := congrArg PowerSeries.constantCoeff h0
    rw [PowerSeries.constantCoeff_C, map_zero, map_neg, neg_eq_zero] at hc
    exact (hyQu.map ψ).ne_zero hc
  simp only [wU₁, wV₁, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, pairV_map]
  exact isCoprime_pairV hmρ hα hβ

end KzUnits

/-! ### The per-disk trace identity, Weierstrass chart -/

section KzTraceWeierstrass

variable {O : Type*} [CommRing O] {K : Type*} [Field K] {ψ : O →+* K}
  {f : O[X]} {ω xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ c₁ c₂ : O[X]}
  {d : CantorCertData O⟦X⟧} {g k : ℕ}
  [NeZero (2 : K)]

local notation "Kz" => FractionRing (PowerSeries K)

/-- **The per-disk trace-form identity, Weierstrass chart**: in `Frac(K⟦z⟧)` with the
derivation `d/dz`, the trace-form differential of the mapped Weierstrass disk pipeline
satisfies `2·z·Θ_k = W(z)^k·W′(z)`, where `(W(z), z)` is the moving disk point. The `τ`-block
dies, the singular constant pair block `[Q + ιP₀]`, `P₀ = (ω, 0)`, is crossed by the
Θ-calculus extension (T2′) — the second reduction step in place of a Bézout certificate for
that block — and the moving pair block evaluates at the disk point,
whose `x`-separation from the constant point is a unit outright (its constant coefficient is
the unit `ω - xQ`). -/
theorem two_mul_X_mul_traceDiff_wPipeline_map (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ) (hyQu : IsUnit yQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
    (hfdeg : f.natDegree = 2 * g + 1) (hk : k < g)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
      uτ.natDegree)
    (hav : IsPipelineAvoid (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d)
    {cP sP : Polynomial O⟦X⟧}
    (hsP : cP * (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1
      + sP * (2 * (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).2) = 1) :
    2 * kzHom ψ PowerSeries.X
        * traceDiff (kzDerivation K)
            ((wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1.map (kzHom ψ))
            (sP.map (kzHom ψ)) k
      = kzHom ψ (weierstrassSeries hf hdeg hω hωu) ^ k
        * kzHom ψ (PowerSeries.derivative (weierstrassSeries hf hdeg hω hωu)) := by
  rw [wPipeline] at hsP ⊢
  set ρ : O⟦X⟧ →+* Kz := kzHom ψ with hρdef
  set F := f.map (PowerSeries.C : O →+* O⟦X⟧) with hFdef
  set D := wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ with hDdef
  set W := weierstrassSeries hf hdeg hω hωu with hWdef
  -- block data over `O⟦z⟧`
  have hu₁ : (wU₁ hf hdeg hω hωu xQ).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hd₁ : wU₁ hf hdeg hω hωu xQ ∣ wV₁ hf hdeg hω hωu m ^ 2 - F :=
    movingPair_dvd_weierstrass hf hdeg hω hωu hsep hm hyQ
  have hu₂ : (uτ.map (PowerSeries.C : O →+* O⟦X⟧)).Monic := huτ.map _
  have hd₂ : uτ.map (PowerSeries.C : O →+* O⟦X⟧)
      ∣ (vτ.map PowerSeries.C) ^ 2 - F := map_dvd_sq_sub _ hdvdτ
  have hu₃ : (phiU₃ ω xQ (O := O)).Monic := ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have hsep' : IsUnit (ω - xQ) := by rw [← neg_sub]; exact hsep.neg
  have hd₃ : phiU₃ ω xQ ∣ phiV₃ xQ yQ m₀ ^ 2 - F :=
    map_dvd_sq_sub _ (pair_dvd hsep' hm₀ hyQ
      (by rw [neg_zero, zero_pow two_ne_zero]; exact hω.symm))
  -- Bézout certificates: the moving pair over `Frac(K⟦z⟧)`, the `τ`-block over `O⟦z⟧`
  obtain ⟨e₁, s₁, hs₁'⟩ := isCoprime_wU₁_map (ψ := ψ) hyQu hf hdeg hω hωu hm
  have hs₁ : e₁ * (wU₁ hf hdeg hω hωu xQ).map ρ
      + s₁ * (2 * (wV₁ hf hdeg hω hωu m).map ρ) = 1 := hs₁'
  obtain ⟨e₂, s₂, hs₂⟩ := isCoprime_two_mul_map ⟨c₁, c₂, hbez⟩
    (PowerSeries.C : O →+* O⟦X⟧)
  -- transport everything to `Frac(K⟦z⟧)`
  have hPmap := map_cantorPipeline_generic ρ hu₁ hu₂ hu₃ hcerts
  have hcertsρ := IsPipelineCerts.map (φ := ρ) hu₁ hu₂ hu₃ hcerts
  have havρ := IsPipelineAvoid.map (φ := ρ) hu₁ hu₂ hu₃ hcerts hav
  obtain ⟨hPa, hPb⟩ := Prod.ext_iff.mp hPmap
  dsimp only at hPa hPb
  have hsPρ : cP.map ρ * (cantorPipeline (F.map ρ) (D.map ρ) (d.map ρ)).1
      + sP.map ρ * (2 * (cantorPipeline (F.map ρ) (D.map ρ) (d.map ρ)).2) = 1 := by
    rw [← hPa, ← hPb]
    exact map_bezout ρ hsP
  -- the `τ`-block dies; the singular constant block has `d`-constant coefficients
  have hτ0 : ∀ i, kzDerivation K (((D.map ρ).u₂).coeff i) = 0 := by
    intro i
    rw [hDdef, PipelineData.map_u₂, wConfig_u₂]
    exact kzDerivation_coeff_map_C_eq_zero uτ i
  have hB0 : ∀ i, kzDerivation K (((D.map ρ).u₃).coeff i) = 0 := by
    intro i
    rw [hDdef, PipelineData.map_u₃, wConfig_u₃, phiU₃]
    exact kzDerivation_coeff_map_C_eq_zero _ i
  have hv₃0 : ∀ i, kzDerivation K (((D.map ρ).v₃).coeff i) = 0 := by
    intro i
    rw [hDdef, PipelineData.map_v₃, wConfig_v₃, phiV₃]
    exact kzDerivation_coeff_map_C_eq_zero _ i
  have hfc : ∀ i, kzDerivation K ((F.map ρ).coeff i) = 0 := fun i ↦
    kzDerivation_coeff_map_C_eq_zero f i
  have h₂ : traceDiff (kzDerivation K) ((D.map ρ).u₂) (s₂.map ρ) k = 0 :=
    traceDiff_eq_zero_of_dotDer_eq_zero _ hτ0 _ k
  -- the moving pair block evaluates at the disk point
  have hdW : kzDerivation K (ρ W) = ρ (PowerSeries.derivative W) := by
    rw [hρdef, kzHom_apply, kzDerivation_algebraMap,
      ← PowerSeries.map_derivative]
    rfl
  have hαβ : IsUnit (ρ W - ρ (PowerSeries.C xQ)) := by
    rw [← map_sub]
    refine isUnit_iff_ne_zero.mpr fun h0 ↦ ?_
    rw [hρdef, kzHom_apply,
      map_eq_zero_iff _ (IsFractionRing.injective (PowerSeries K) Kz)] at h0
    have h1 := congrArg PowerSeries.constantCoeff h0
    rw [PowerSeries.constantCoeff_map, map_sub, hWdef, constantCoeff_weierstrassSeries,
      PowerSeries.constantCoeff_C, map_zero, map_sub] at h1
    exact (hsep.map ψ).ne_zero (by rw [map_sub]; linear_combination -h1)
  have hu₁ρ : (wU₁ hf hdeg hω hωu xQ).map ρ
      = (X - C (ρ W)) * (X - C (ρ (PowerSeries.C xQ))) := by
    rw [wU₁, ← hWdef]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, map_C]
  have h₁ := traceDiff_pair (kzDerivation K) (α := ρ W) (β := ρ (PowerSeries.C xQ))
    (kzDerivation_kzHom_C xQ) hαβ (hu₁ρ ▸ hs₁) k
  rw [show ((wV₁ hf hdeg hω hωu m).map ρ).eval (ρ W) = ρ PowerSeries.X by
      rw [wV₁, ← hWdef, pairV_map, pairV_eval_left], hdW] at h₁
  -- assemble along the pipeline over `Frac(K⟦z⟧)`, crossing the singular block by (T2′)
  have hfdegρ : (F.map ρ).natDegree = 2 * g + 1 := by
    rw [hFdef, Polynomial.map_map, hf.natDegree_map, hfdeg]
  -- the mapped blocks of `D` are the mapped blocks of the configuration, definitionally
  have htot := traceDiff_cantorPipeline_of_dvd_dotDer (kzDerivation K)
    (D := D.map ρ) (dt := d.map ρ) (f := F.map ρ)
    (hu₁.map ρ) (map_dvd_sq_sub ρ hd₁) (hu₂.map ρ) (map_dvd_sq_sub ρ hd₂)
    (hu₃.map ρ) (map_dvd_sq_sub ρ hd₃) hcertsρ havρ hfc hfdegρ hk hB0 hv₃0 hs₁
    (map_bezout ρ hs₂) hsPρ
  rw [hPa, htot, h₂, add_zero,
    show (D.map ρ).u₁ = (wU₁ hf hdeg hω hωu xQ).map ρ from rfl, hu₁ρ]
  exact h₁

end KzTraceWeierstrass

/-! ### The Weierstrass-chart capstone, per disk -/

section KzAssembleWeierstrass

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O]
  {K : Type*} [Field K] [NeZero (2 : K)] {ψ : O →+* K}
  {f : O[X]} {ω xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ w c₁ c₂ : O[X]}
  {d : CantorCertData O⟦X⟧}
  {dF : FoldCertData (MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O) uτ.natDegree}
  {Aτ : Fin uτ.natDegree → MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O}
  {aτ bτ : Fin uτ.natDegree → O}
  {hv : vτ.degree < uτ.degree} {hw : vτ ^ 2 - f = uτ * w}
  {hbez : c₁ * uτ + c₂ * (2 * vτ) = 1}
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

local notation "Kz" => FractionRing (PowerSeries K)

/-- Cancel the doubling at the endpoint of the Weierstrass trace-form solve. -/
theorem eq_aeval_mul_of_two_mul_eq {A U V : K⟦X⟧} {P : K[X]}
    (h : 2 * A = aeval U ((2 : K) • P) * V) : A = aeval U P * V := by
  have h2K : (2 : K⟦X⟧) ≠ 0 := fun h0 ↦ (NeZero.ne (2 : K)) (by
    have h1 := congrArg PowerSeries.constantCoeff h0
    rwa [map_ofNat, map_zero] at h1)
  refine mul_left_cancel₀ h2K ?_
  rw [h, map_smul, smul_mul_assoc, Algebra.smul_def, PowerSeries.algebraMap_eq, map_ofNat]

/-- **The trace-form identity on a Weierstrass residue disk, per disk**
(`thm:omega-prime-global`, clause (c), Weierstrass transport): with the chart `x = W(z)`,
`y = z`, the differential `ω′_i` associated to the chart coordinates `wZeta` of the
Weierstrass disk pipeline satisfies `z·ω′_i = tracePoly_i(W(z))·W′(z)` — from per-disk
hypotheses only: the fold avoidance of the `τ`-pack, `y_Q` a unit, and the Weierstrass
avoidance of the per-disk configuration (the second reduction step crosses the singular
constant block by (T2′)). The Weierstrass mirror of
`ChabautyColeman.yseries_mul_omegaPrime_eq_taylor_tracePoly_kz`. -/
theorem X_mul_omegaPrime_eq_aeval_tracePoly_mul_derivative {hu : uτ.Monic}
    (hroot : ∀ i, (ftauUY uτ uτ.natDegree).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (haτ : ∀ i, uτ.eval (aτ i) = 0) (hbτ : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplitτ : uτ = ∏ m' : Fin uτ.natDegree, (X - C (aτ m')))
    (hunitτ : ∀ i j : Fin uτ.natDegree, i ≠ j → IsUnit (aτ i - aτ j))
    (hdF : IsFtauFoldCerts Aτ aτ bτ hu rfl hv hw hbez dF)
    {π : O} (hπ : maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hω : f.eval ω = 0)
    (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ)
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
      uτ.natDegree)
    (hyQu : IsUnit yQ)
    (havF : IsFtauFoldAvoid Aτ aτ bτ hu rfl hv hw hbez dF)
    (havφ : IsPipelineAvoid (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d)
    (i : Fin uτ.natDegree) :
    PowerSeries.X * omegaPrime ((ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot hcc haτ hbτ
          hdF hπ hπ0 hsplitτ hunitτ).map ψ)
        (fun s ↦ PowerSeries.map ψ (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d s)) i
      = aeval (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
          (tracePoly (uτ.map ψ) (c₂.map ψ) (Fin.cast (hu.natDegree_map ψ).symm i))
        * PowerSeries.derivative (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu)) := by
  classical
  have hdvdτ : uτ ∣ vτ ^ 2 - f := ⟨w, hw⟩
  have hgτ : 2 * uτ.natDegree < f.natDegree := by rw [hfdeg]; lia
  set Φ := ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot hcc haτ hbτ hdF hπ hπ0
    hsplitτ hunitτ
  set ζK : Fin uτ.natDegree → K⟦X⟧ :=
    fun j ↦ PowerSeries.map ψ (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d j)
  set ι' : K⟦X⟧ →+* Kz := algebraMap (PowerSeries K) Kz with hιdef
  set ρ : O⟦X⟧ →+* Kz := kzHom (O := O) ψ with hρdef
  obtain ⟨cPτ, sPτ, hsPτ⟩ := isCoprime_ftauFoldPipe hu rfl hv hw hbez havF
  obtain ⟨cφ, sφ, hsφ⟩ : IsCoprime (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1
      (2 * (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).2) := by
    rw [wPipeline]
    exact havφ.hcop₂
  obtain ⟨hPm, hPd, -⟩ :=
    wPipeline_monic_dvd_degree_lt hf hdeg hω hωu hsep hm hm₀ hyQ hu hdvdτ hcerts
  have hcc0 (j : Fin uτ.natDegree) :
      PowerSeries.constantCoeff (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d j) = 0 :=
    constantCoeff_wZeta hf hdeg hω hωu hsep hm hm₀ hyQ hu hv hdvdτ hgτ hcerts j
  -- the chart's trace identity: the numerators are the powers of `x(z) = W(z)`, times `W′`
  have hΘ (k : Fin uτ.natDegree) : 2 * ρ PowerSeries.X
      * traceDiff (kzDerivation K)
          ((wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1.map ρ) (sφ.map ρ) k
      = ρ (weierstrassSeries hf hdeg hω hωu) ^ (k : ℕ)
        * ρ (PowerSeries.derivative (weierstrassSeries hf hdeg hω hωu)) :=
    two_mul_X_mul_traceDiff_wPipeline_map hf hdeg hω hωu hsep hm hm₀ hyQ hyQu hu hdvdτ
      hbez hfdeg k.isLt hcerts havφ hsφ
  have hdrive := two_mul_omegaPrime_kz_eq_sum hroot hcc haτ hbτ hsplitτ hunitτ hdF hπ hπ0 hf
    hfdeg havF hsPτ hPm hcerts.hdeg
    (ζ := fun j ↦ wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d j) (fun j ↦ by rw [wZeta]) hcc0
    (fun θ hθC hθX hθ0 k j ↦ traceMat_wPipeline hf hdeg hω hωu rfl θ hθC hθX hθ0 hsep hm hm₀
      hyQ hu hv hw hbez hgτ hcerts
      (bezout_ftauFoldPipe_map_setYZero hu rfl hv hw hbez hf hfdeg hroot hcc hbτ hdF hπ hπ0
        hsplitτ (fun i' j' hij ↦ by
          by_contra hne'
          exact (hunitτ i' j' hne').ne_zero (by rw [hij, sub_self])) hsPτ) hsφ k j)
    hΘ i
  -- both sides are `ι'`-images; identify them in `K⟦z⟧`
  have hcast : algebraMap K Kz = ι'.comp (PowerSeries.C : K →+* K⟦X⟧) := by
    rw [hιdef, ← PowerSeries.algebraMap_eq]
    exact IsScalarTower.algebraMap_eq K K⟦X⟧ Kz
  have hyv : ρ PowerSeries.X = ι' PowerSeries.X := by rw [hρdef, kzHom_apply, PowerSeries.map_X]
  have hRHS : (∑ j, algebraMap K Kz ((traceMatrix (uτ.map ψ) (c₂.map ψ))⁻¹
        (finCongr (hu.natDegree_map ψ).symm i) (finCongr (hu.natDegree_map ψ).symm j))
        * (ρ (weierstrassSeries hf hdeg hω hωu) ^ (j : ℕ)
          * ρ (PowerSeries.derivative (weierstrassSeries hf hdeg hω hωu))))
      = ι' (aeval (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
            ((2 : K) • tracePoly (uτ.map ψ) (c₂.map ψ) (Fin.cast (hu.natDegree_map ψ).symm i))
          * PowerSeries.derivative (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))) := by
    rw [two_smul_tracePoly, map_sum, Finset.sum_mul, map_sum]
    refine Fintype.sum_equiv (finCongr (hu.natDegree_map ψ).symm) _ _ fun j ↦ ?_
    rw [hcast, RingHom.comp_apply, map_mul, map_mul, map_mul,
      map_pow, aeval_C, aeval_X, ← PowerSeries.algebraMap_eq, ← PowerSeries.map_derivative,
      hρdef, kzHom_apply, kzHom_apply, map_pow]
    simp only [finCongr_apply, Fin.val_cast]
    ring
  -- cancel the embedding and the factor `2`
  have hend : ι' (2 * (PowerSeries.X * omegaPrime (Φ.map ψ) ζK i))
      = ι' (aeval (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
            ((2 : K) • tracePoly (uτ.map ψ) (c₂.map ψ) (Fin.cast (hu.natDegree_map ψ).symm i))
          * PowerSeries.derivative (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))) := by
    rw [map_mul, map_ofNat, ← hRHS, ← hdrive, hyv, map_mul]
  exact eq_aeval_mul_of_two_mul_eq ((IsFractionRing.injective (PowerSeries K) Kz) hend)

/-- **The `hW`-identification at a Weierstrass centre, from per-disk hypotheses only**: if
the numerator `h₀` has coordinates `cs` in the trace-form basis, then the integral disk
expansion of `h₀·dx/y` at the Weierstrass centre `(ω, 0)` is `∑_i cs_i·ω′_i` for the
Weierstrass chart coordinates `wZeta` of that disk — the `hW` slot of
`ChabautyColeman.encard_inter_residueDisk_le_ordPoint_weierstrass`. The coordinate identity
`hmap` is disk-independent (`ChabautyColeman.exists_annihilator_tracePoly`), so a single
differential serves every disk. -/
theorem map_omegaExpansionWeierstrass_eq_sum_smul_omegaPrime_tracePoly {hu : uτ.Monic}
    (hroot : ∀ i, (ftauUY uτ uτ.natDegree).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (haτ : ∀ i, uτ.eval (aτ i) = 0) (hbτ : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplitτ : uτ = ∏ m' : Fin uτ.natDegree, (X - C (aτ m')))
    (hunitτ : ∀ i j : Fin uτ.natDegree, i ≠ j → IsUnit (aτ i - aτ j))
    (hdF : IsFtauFoldCerts Aτ aτ bτ hu rfl hv hw hbez dF)
    {π : O} (hπ : maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hω : f.eval ω = 0)
    (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ)
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
      uτ.natDegree)
    (hyQu : IsUnit yQ)
    (havF : IsFtauFoldAvoid Aτ aτ bτ hu rfl hv hw hbez dF)
    (havφ : IsPipelineAvoid (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d)
    {cs : Fin uτ.natDegree → K} {h₀ : O[X]}
    (hmap : h₀.map ψ = ∑ i, cs i • tracePoly (uτ.map ψ) (c₂.map ψ)
      (Fin.cast (hu.natDegree_map ψ).symm i)) :
    PowerSeries.map ψ (omegaExpansionWeierstrass h₀ hf hdeg hω hωu)
      = ∑ i, cs i • omegaPrime ((ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot hcc haτ hbτ
          hdF hπ hπ0 hsplitτ hunitτ).map ψ)
          (fun s ↦ PowerSeries.map ψ (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d s)) i := by
  have hXne : (PowerSeries.X : K⟦X⟧) ≠ 0 := PowerSeries.X_ne_zero
  refine mul_left_cancel₀ hXne ?_
  calc PowerSeries.X * PowerSeries.map ψ (omegaExpansionWeierstrass h₀ hf hdeg hω hωu)
      = PowerSeries.map ψ (PowerSeries.X * omegaExpansionWeierstrass h₀ hf hdeg hω hωu) := by
        rw [map_mul, PowerSeries.map_X]
    _ = aeval (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu)) (h₀.map ψ)
        * PowerSeries.derivative (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu)) := by
        rw [X_mul_omegaExpansionWeierstrass, map_mul, PowerSeries.map_aeval,
          PowerSeries.map_derivative]
    _ = ∑ i, cs i • (aeval (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
          (tracePoly (uτ.map ψ) (c₂.map ψ) (Fin.cast (hu.natDegree_map ψ).symm i))
        * PowerSeries.derivative (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))) := by
        rw [hmap, map_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_mul_assoc]
    _ = ∑ i, cs i • (PowerSeries.X
          * omegaPrime ((ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot hcc haτ hbτ hdF hπ hπ0
              hsplitτ hunitτ).map ψ)
            (fun s ↦ PowerSeries.map ψ (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d s)) i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [X_mul_omegaPrime_eq_aeval_tracePoly_mul_derivative hroot hcc haτ hbτ hsplitτ
          hunitτ hdF hπ hπ0 hf hdeg hω hωu hsep hm hm₀ hyQ hfdeg hcerts hyQu havF havφ i]
    _ = PowerSeries.X * ∑ i, cs i • omegaPrime ((ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot
          hcc haτ hbτ hdF hπ hπ0 hsplitτ hunitτ).map ψ)
          (fun s ↦ PowerSeries.map ψ (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d s)) i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ (mul_smul_comm _ _ _).symm

end KzAssembleWeierstrass

end ChabautyColeman

end
