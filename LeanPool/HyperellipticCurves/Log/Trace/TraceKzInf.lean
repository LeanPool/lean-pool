/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.OmegaExpansionInf
public import LeanPool.HyperellipticCurves.Log.Charts.InfChart
public import LeanPool.HyperellipticCurves.Log.Charts.InfGlobTransport
public import LeanPool.HyperellipticCurves.Log.Charts.InfIdentification
public import LeanPool.HyperellipticCurves.Log.Charts.InfTransport
public import LeanPool.HyperellipticCurves.Log.Trace.TraceInf
public import LeanPool.HyperellipticCurves.Log.Trace.TraceKz

import LeanPool.HyperellipticCurves.Log.Charts.DiskTransport
import LeanPool.HyperellipticCurves.Log.Charts.InfGlue
import LeanPool.HyperellipticCurves.Log.Fold.FoldTrace

/-!
# The trace-form identity at the infinity centre, per residue disk

Clause (c) of `thm:omega-prime-global` at the disk at infinity, run **directly on the mapped
closed infinity-disk datum** `(infU, V)` over `Frac(K⟦z⟧)` with the derivation `d/dz` — the
infinity mirror of `LeanPool.HyperellipticCurves.Log.Trace.TraceKz`, with the chart `x = 1/u(z)`,
`y = 1/(u(z)^g·z)`.

* `ChabautyColeman.two_mul_y_mul_traceDiff_infU_map`: the per-disk trace identity —
  `2·y_hat·Θ_k = x̂^k·d(x̂)` on the mapped closed datum. The two-block Cantor addition
  `[P_z_hat - ∞] + τ` is run natively over `Frac(K⟦z⟧)` with the concrete one-step certificate
  pack (cofactor `-1`), its reduced output identified with the closed datum by uniqueness of
  reduced representatives; the moving point's separation from the `τ`-block is the pole-order
  argument (`ChabautyColeman.aeval_inv_eq_zero_iff`) — no transcendence enters.
* `ChabautyColeman.infSeries_mul_omegaPrime_kz`: the capstone —
  `u·ω′_i = -z·tracePoly_i*(u)·u′` on the infinity disk with `P* = reflect (g-1) P`, from
  per-disk hypotheses only, by the shared solve driver `ChabautyColeman.kzOmega` and the
  reflection bookkeeping.
* `ChabautyColeman.map_omegaExpansionInf_eq_sum_smul_omegaPrime_tracePoly`: consequently, a
  polynomial `h₀` whose coordinates in the trace-form basis are `cs` has
  `omegaExpansionInf h₀ = ∑ᵢ csᵢ·ω′ᵢ` — the `hW` hypothesis of
  `ChabautyColeman.encard_inter_residueDisk_le_ordPoint_inf`.

Blueprint node: `thm:omega-prime-global`, clause (c) (infinity transport).
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped Matrix PowerSeries

namespace ChabautyColeman

section KzTraceInf

variable {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [Field K] [CharZero K]
  {ψ : O →+* K}
  {f uτ vτ c₁ c₂ : O[X]} {k : ℕ}
  [Fact (Odd (f.map ψ).natDegree)] [Fact (Squarefree (f.map ψ))]

local notation "Kz" => FractionRing (PowerSeries K)

/-- **The per-disk trace-form identity at the infinity centre**: in `Frac(K⟦z⟧)` with the
derivation `d/dz`, the trace-form differential of the mapped closed infinity-disk datum
`(infU, V)` satisfies `2·y_hat·Θ_k = x̂^k·d(x̂)`, where `x̂ = 1/u(z)` and `y_hat = 1/(u(z)^g·z)` are
the coordinates of the moving disk point. The proof runs the two-block Cantor addition
`[P_z_hat - ∞] + τ` **natively over `Frac(K⟦z⟧)`** with the concrete one-step certificate pack
(cofactor `-1`); its reduced output is
identified with the mapped closed datum by uniqueness of reduced representatives
(`ChabautyColeman.mk0_cantorStage₂` against `ChabautyColeman.mk0_map_infU`), the `τ`-block
dies under `d/dz`, and the moving point contributes the differential itself
(`ChabautyColeman.traceDiff_single`); its separation from the `τ`-block is the pole-order
argument `ChabautyColeman.aeval_inv_eq_zero_iff` — no transcendence enters. -/
theorem two_mul_y_mul_traceDiff_infU_map (hf : f.Monic) (huτ : uτ.Monic)
    (hvτn : vτ.natDegree < uτ.natDegree) (hfdeg : f.natDegree = 2 * uτ.natDegree + 1)
    (hdvdτ : uτ ∣ vτ ^ 2 - f) (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
    {V : (O⟦X⟧)[X]} (hV : C PowerSeries.X * V = -(infV hf uτ vτ %ₘ infU hf uτ vτ))
    (hVdeg : V.degree < (infU hf uτ vτ).degree)
    (hVdvd : infU hf uτ vτ ∣ V ^ 2 - f.map PowerSeries.C)
    (hk : k < uτ.natDegree)
    {cP sP : Polynomial O⟦X⟧} (hsP : cP * infU hf uτ vτ + sP * (2 * V) = 1) :
    2 * (algebraMap (PowerSeries K) Kz PowerSeries.X)⁻¹
        * (algebraMap (PowerSeries K) Kz (PowerSeries.map ψ (infSeries hf)))⁻¹ ^ uτ.natDegree
        * traceDiff (kzDerivation K) ((infU hf uτ vτ).map (kzHom ψ)) (sP.map (kzHom ψ)) k
      = (algebraMap (PowerSeries K) Kz (PowerSeries.map ψ (infSeries hf)))⁻¹ ^ k
        * kzDerivation K
            ((algebraMap (PowerSeries K) Kz (PowerSeries.map ψ (infSeries hf)))⁻¹) := by
  classical
  set n := uτ.natDegree
  set aK : PowerSeries K →+* Kz := algebraMap (PowerSeries K) Kz with haKdef
  set ρ : O⟦X⟧ →+* Kz := kzHom ψ with hρdef
  set χ : O →+* Kz := ρ.comp (PowerSeries.C : O →+* O⟦X⟧) with hχdef
  set uψ := PowerSeries.map ψ (infSeries hf)
  set A : Kz := aK uψ with hAdef
  set Z : Kz := aK PowerSeries.X with hZdef
  have hinj : Function.Injective aK := IsFractionRing.injective (PowerSeries K) Kz
  have : CharZero (PowerSeries K) := (PowerSeries.constantCoeff : K⟦X⟧ →+* K).charZero
  have : CharZero Kz := charZero_of_injective_algebraMap hinj
  obtain ⟨huψ0, huψne⟩ := ne_zero_of_eq_X_sq_mul (hf.map ψ) (map_infSeries_eq hf)
  have hA0 : A ≠ 0 := fun h ↦ huψne (hinj (by rw [hAdef] at h; rw [h, map_zero]))
  have hZ0 : Z ≠ 0 := fun h ↦
    PowerSeries.X_ne_zero (hinj (by rw [hZdef] at h; rw [h, map_zero]))
  have hρX : ρ PowerSeries.X = Z := by rw [hρdef, kzHom_apply, PowerSeries.map_X]
  have hρinf : ρ (infSeries hf) = A := rfl
  -- the `Kz`-level curve polynomial and its `Fact`s
  obtain ⟨hFKzdeg, hOdd, hSq⟩ := natDegree_odd_squarefree_map_comp (ψ := ψ) (χ := χ)
    (σ := aK.comp (PowerSeries.C : K →+* K⟦X⟧)) hf
    (by ext c; simp [hχdef, hρdef, kzHom, haKdef])
  have : Fact (Odd (f.map χ).natDegree) := ⟨hOdd⟩
  have : Fact (Squarefree (f.map χ)) := ⟨hSq⟩
  have hFdeg : (f.map χ).natDegree = 2 * n + 1 := by rw [hFKzdeg, hfdeg]
  have hmapmap (p : O[X]) : (p.map (PowerSeries.C : O →+* O⟦X⟧)).map ρ = p.map χ := by
    rw [Polynomial.map_map]
  have hmapK (p : O[X]) : p.map χ = (p.map ψ).map (algebraMap K Kz) := by
    rw [Polynomial.map_map]
    refine congrArg (fun φ : O →+* Kz ↦ p.map φ) (RingHom.ext fun c ↦ ?_)
    rw [hχdef, RingHom.comp_apply, hρdef, kzHom_apply, PowerSeries.map_C,
      RingHom.comp_apply, IsScalarTower.algebraMap_apply K (PowerSeries K) Kz,
      PowerSeries.algebraMap_eq]
  -- the moving point over `Kz`
  set yKz : Kz := Z⁻¹ * A⁻¹ ^ n with hyKzdef
  -- the moving block is on the curve: the reflected on-curve identity
  have hAeq : A = Z ^ 2 * aK (aeval uψ (f.map ψ).reverse) := by
    have h := congrArg aK (map_infSeries_eq (ψ := ψ) hf)
    rwa [map_mul, map_pow] at h
  have hfdegψ : (f.map ψ).natDegree = 2 * n + 1 := by rw [hf.natDegree_map, hfdeg]
  have hcurve : yKz ^ 2 = (f.map χ).eval A⁻¹ := by
    have hrevA : Polynomial.eval₂ (algebraMap K Kz) A (f.map ψ).reverse
        = aK (aeval uψ (f.map ψ).reverse) :=
      (aeval_def _ _).symm.trans (aeval_algebraMap_apply _ uψ (f.map ψ).reverse)
    rw [hmapK, eval_map, hyKzdef]
    exact sq_inv_mul_inv_pow_eq_eval₂_inv hfdegψ hA0 hZ0 (hAeq.trans (by rw [hrevA]))
  -- the moving block avoids the `τ`-block: pole order at `x̂ = 1/u(z)`
  have hux : (uτ.map χ).eval A⁻¹ ≠ 0 := by
    rw [hmapK, eval_map, ← aeval_def]
    exact fun h0 ↦ (huτ.map ψ).ne_zero
      ((aeval_inv_eq_zero_iff (hf.map ψ) (map_infSeries_eq hf)).mp h0)
  obtain ⟨s₁', s₂', hs⟩ := (isCoprime_X_sub_C_of_eval_ne_zero hux).symm
  -- the two blocks over `Kz`, and their one-step certificate pack
  set Dinf : PipelineData Kz := .ofPair (X - C A⁻¹) (C yKz) (uτ.map χ) (vτ.map χ) with hDdef
  set dt : CantorCertData Kz := ⟨s₁', s₂', 0, -1, 1, 0, 0, 0⟩
  have hu₁ : (X - C A⁻¹ : Kz[X]).Monic := monic_X_sub_C _
  have hd₁ : (X - C A⁻¹ : Kz[X]) ∣ C yKz ^ 2 - f.map χ := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_pow, eval_C, hcurve]
    ring
  have hu₂ : (uτ.map χ).Monic := huτ.map χ
  have hd₂ : uτ.map χ ∣ (vτ.map χ) ^ 2 - f.map χ := map_dvd_sq_sub χ hdvdτ
  have hAdd : IsAddCerts (f.map χ) Dinf dt n :=
    isAddCerts_ofPair (hf.map χ) hFdeg hcurve hu₂ (huτ.natDegree_map χ) hd₂
      (by linear_combination hs)
  -- the reduced output is the mapped closed datum, by uniqueness of reduced representatives
  obtain ⟨hu2m, hd2m, hlt2⟩ := cantorStage₂_monic_dvd_degree_lt hu₁ hd₁ hu₂ hd₂ hAdd
  have hUm : (infU hf uτ vτ).Monic := infU_monic hf huτ hvτn hfdeg hdvdτ
  have hgKz : 2 * n < (f.map χ).natDegree := by rw [hFdeg]; lia
  have hclP := mk0_cantorStage₂ (D := Dinf) hu₁ hd₁ hu₂ hd₂ hAdd
  have hkey := mk0_map_infU (ρ := ρ) (χ := χ) rfl hf huτ hvτn hfdeg hdvdτ hV hρX hρinf
    hZ0 hA0
  obtain ⟨hmatch1, hmatch2⟩ := mumfordIdeal_reduced_unique (f.map χ) hu2m (hUm.map ρ)
    hlt2 (hUm.degree_map_lt_degree_map ρ hVdeg)
    (by rw [hAdd.hdeg]; exact hgKz)
    (by rw [hUm.natDegree_map, natDegree_infU hf huτ hvτn hfdeg hdvdτ]; exact hgKz)
    hd2m (by have h := map_dvd_sq_sub ρ hVdvd; rwa [hmapmap] at h)
    (hclP.trans hkey.symm)
  -- the Bézout data of the two blocks and of the output
  have hyKz0 : yKz ≠ 0 := mul_ne_zero (inv_ne_zero hZ0) (pow_ne_zero _ (inv_ne_zero hA0))
  have h2yKz : (2 : Kz) * yKz ≠ 0 := mul_ne_zero two_ne_zero hyKz0
  have ht₁ : (0 : Kz[X]) * (X - C A⁻¹) + C ((2 * yKz)⁻¹) * (2 * C yKz) = 1 := by
    rw [zero_mul, zero_add, show (2 : Kz[X]) = C (2 : Kz) from (map_ofNat C 2).symm,
      ← map_mul, ← map_mul, inv_mul_cancel₀ h2yKz, map_one]
  obtain ⟨d₁, d₂, hbezχ⟩ := isCoprime_two_mul_map (⟨c₁, c₂, hbez⟩ : IsCoprime uτ (2 * vτ)) χ
  have hsPρ : cP.map ρ * (cantorStage₂ (f.map χ) Dinf dt).1
      + sP.map ρ * (2 * (cantorStage₂ (f.map χ) Dinf dt).2) = 1 := by
    rw [hmatch1, hmatch2]
    exact map_bezout ρ hsP
  -- the `τ`-block dies under `d/dz`; the `f`-coefficients are constants
  have hχconst (c : O) : kzDerivation K (χ c) = 0 := by
    rw [hχdef, RingHom.comp_apply]
    exact kzDerivation_kzHom_C c
  have hτ0 : ∀ i, kzDerivation K ((uτ.map χ).coeff i) = 0 := fun i ↦ by
    rw [coeff_map]
    exact hχconst _
  have hfc : ∀ i, kzDerivation K ((f.map χ).coeff i) = 0 := fun i ↦ by
    rw [coeff_map]
    exact hχconst _
  have h₂ : traceDiff (kzDerivation K) (uτ.map χ) d₂ k = 0 :=
    traceDiff_eq_zero_of_dotDer_eq_zero _ hτ0 _ k
  -- the moving point contributes the differential itself
  have h₁ := traceDiff_single (kzDerivation K) ht₁ k
  rw [eval_C] at h₁
  -- assemble along the two-block addition
  have htot := traceDiff_cantorStage₂ (kzDerivation K) (D := Dinf) hu₁ hd₁ hu₂ hd₂ hAdd
    hfc hFdeg hk ht₁ hbezχ hsPρ
  rw [← hmatch1, htot]
  simp only [hDdef, PipelineData.ofPair_u₁, PipelineData.ofPair_u₂]
  rw [h₂, add_zero]
  linear_combination h₁

end KzTraceInf

/-! ### The infinity-chart capstone, per disk -/

section Reflection

variable {K : Type*} [Field K]

local notation "Kz" => FractionRing (PowerSeries K)

/-- **The reflection bookkeeping of the infinity capstone**: clearing the powers of
`x̂ = 1/u(z)` out of the solved identity replaces the evaluation of `P` at `x̂` by the
evaluation of its reflection at `u`. -/
private theorem eq_neg_X_mul_aeval_reflect {n : ℕ} (hn : 1 ≤ n) {P : K[X]}
    (hPdeg : P.natDegree ≤ n - 1) {u ω D : K⟦X⟧} (hu0 : u ≠ 0)
    (h1 : (algebraMap K⟦X⟧ Kz PowerSeries.X)⁻¹ * (algebraMap K⟦X⟧ Kz u)⁻¹ ^ n
        * algebraMap K⟦X⟧ Kz ω
      = aeval (algebraMap K⟦X⟧ Kz u)⁻¹ P
        * (-((algebraMap K⟦X⟧ Kz u)⁻¹ ^ 2) * algebraMap K⟦X⟧ Kz D)) :
    u * ω = -PowerSeries.X * aeval u (reflect (n - 1) P) * D := by
  set ι' : K⟦X⟧ →+* Kz := algebraMap K⟦X⟧ Kz
  have hinj : Function.Injective ι' := IsFractionRing.injective K⟦X⟧ Kz
  set A : Kz := ι' u
  set Z : Kz := ι' PowerSeries.X
  have hA0 : A ≠ 0 := fun h ↦ hu0 (hinj (h.trans (map_zero ι').symm))
  have hZ0 : Z ≠ 0 := fun h ↦ PowerSeries.X_ne_zero (hinj (h.trans (map_zero ι').symm))
  let : Invertible A := invertibleOfNonzero hA0
  have hrefl := eval₂_reflect_mul_pow (algebraMap K Kz) A (n - 1) (reflect (n - 1) P)
    (natDegree_reflect_le.trans (max_le le_rfl hPdeg))
  rw [reflect_reflect, invOf_eq_inv,
    show Polynomial.eval₂ (algebraMap K Kz) A (reflect (n - 1) P)
      = ι' (aeval u (reflect (n - 1) P)) from
      (aeval_def _ _).symm.trans (aeval_algebraMap_apply _ u (reflect (n - 1) P)),
    show Polynomial.eval₂ (algebraMap K Kz) A⁻¹ P = aeval A⁻¹ P by rw [aeval_def]] at hrefl
  have hAg : A ^ (n + 1) * A⁻¹ ^ 2 = A ^ (n - 1) := by
    rw [show n + 1 = n - 1 + 2 by lia, pow_add, mul_assoc, inv_pow,
      mul_inv_cancel₀ (pow_ne_zero 2 hA0), mul_one]
  refine hinj ?_
  rw [map_mul, map_mul, map_mul, map_neg]
  calc A * ι' ω
      = A * ((A ^ n * Z) * ((A ^ n * Z)⁻¹ * ι' ω)) := by
        rw [mul_inv_cancel_left₀ (mul_ne_zero (pow_ne_zero _ hA0) hZ0)]
    _ = A * ((A ^ n * Z) * (aeval A⁻¹ P * (-(A⁻¹ ^ 2) * ι' D))) := by
        rw [show (A ^ n * Z)⁻¹ = Z⁻¹ * A⁻¹ ^ n by rw [mul_inv, inv_pow]; ring, ← h1]
    _ = -Z * ι' D * (aeval A⁻¹ P * (A ^ (n + 1) * A⁻¹ ^ 2)) := by ring
    _ = -Z * ι' D * ι' (aeval u (reflect (n - 1) P)) := by rw [hAg, hrefl]
    _ = -Z * ι' (aeval u (reflect (n - 1) P)) * ι' D := by ring

end Reflection

section KzAssembleInf

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O]
  {K : Type*} [Field K] [CharZero K] [NeZero (2 : K)] {ψ : O →+* K}
  {f uτ vτ w c₁ c₂ : O[X]}
  {dF : FoldCertData (MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O) uτ.natDegree}
  {Aτ : Fin uτ.natDegree → MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O}
  {aτ bτ : Fin uτ.natDegree → O}
  {hv : vτ.degree < uτ.degree} {hw : vτ ^ 2 - f = uτ * w}
  {hbez : c₁ * uτ + c₂ * (2 * vτ) = 1}
  [Fact (Odd (f.map ψ).natDegree)] [Fact (Squarefree (f.map ψ))]
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

local notation "Kz" => FractionRing (PowerSeries K)

/-- **The trace-form identity on the infinity disk, per disk** (`thm:omega-prime-global`,
clause (c), infinity transport): with the chart `x = 1/u(z)`, `y = 1/(u(z)^g·z)`, the
differential `ω′_i` associated to the chart coordinates `infZeta` of the closed
infinity-disk datum satisfies `u·ω′_i = -z·P*(u)·u′` with `P* = reflect (g-1) tracePoly_i` —
from per-disk hypotheses only: the fold avoidance of the `τ`-pack and the reduced closed
datum `(infU, V)`; no global pack, no `N`-matrix realization, and no genericity beyond the
`τ`-pack enter. The infinity mirror of
`ChabautyColeman.yseries_mul_omegaPrime_eq_taylor_tracePoly_kz`. -/
theorem infSeries_mul_omegaPrime_kz {hu : uτ.Monic}
    (hroot : ∀ i, (ftauUY uτ uτ.natDegree).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (haτ : ∀ i, uτ.eval (aτ i) = 0) (hbτ : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplitτ : uτ = ∏ m' : Fin uτ.natDegree, (X - C (aτ m')))
    (hunitτ : ∀ i j : Fin uτ.natDegree, i ≠ j → IsUnit (aτ i - aτ j))
    (hdF : IsFtauFoldCerts Aτ aτ bτ hu rfl hv hw hbez dF)
    {π : O} (hπ : maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hf : f.Monic) (hvτn : vτ.natDegree < uτ.natDegree)
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1)
    {V : (O⟦X⟧)[X]} (hV : C PowerSeries.X * V = -(infV hf uτ vτ %ₘ infU hf uτ vτ))
    (hVdeg : V.degree < (infU hf uτ vτ).degree)
    (hVdvd : infU hf uτ vτ ∣ V ^ 2 - f.map PowerSeries.C)
    (havF : IsFtauFoldAvoid Aτ aτ bτ hu rfl hv hw hbez dF)
    (i : Fin uτ.natDegree) :
    PowerSeries.map ψ (infSeries hf)
        * omegaPrime ((ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot hcc haτ hbτ hdF hπ hπ0
            hsplitτ hunitτ).map ψ)
          (fun s ↦ PowerSeries.map ψ (infZeta hf uτ vτ s)) i
      = -PowerSeries.X
          * aeval (PowerSeries.map ψ (infSeries hf))
              (reflect (uτ.natDegree - 1) (tracePoly (uτ.map ψ) (c₂.map ψ)
                (Fin.cast (hu.natDegree_map ψ).symm i)))
        * PowerSeries.derivative (PowerSeries.map ψ (infSeries hf)) := by
  classical
  have hdvdτ : uτ ∣ vτ ^ 2 - f := ⟨w, hw⟩
  set Φ := ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot hcc haτ hbτ hdF hπ hπ0
    hsplitτ hunitτ
  set ζK : Fin uτ.natDegree → K⟦X⟧ :=
    fun j ↦ PowerSeries.map ψ (infZeta hf uτ vτ j)
  set ι' : K⟦X⟧ →+* Kz := algebraMap (PowerSeries K) Kz
  set ρ : O⟦X⟧ →+* Kz := kzHom (O := O) ψ
  set uψ := PowerSeries.map ψ (infSeries hf)
  obtain ⟨cPτ, sPτ, hsPτ⟩ := isCoprime_ftauFoldPipe hu rfl hv hw hbez havF
  have hcc0 (j : Fin uτ.natDegree) :
      PowerSeries.constantCoeff (infZeta hf uτ vτ j) = 0 :=
    constantCoeff_infZeta hf hu hvτn hfdeg hdvdτ j
  -- the closed datum's cofactor lifts by Nakayama from the τ-datum's certificate
  have hUm : (infU hf uτ vτ).Monic := infU_monic hf hu hvτn hfdeg hdvdτ
  have hUres : (infU hf uτ vτ).map (residue O⟦X⟧)
      = ((uτ.map (PowerSeries.C : O →+* O⟦X⟧)).map (residue O⟦X⟧)) :=
    map_residue_eq (map_constantCoeff_infU hf hu hvτn hfdeg hdvdτ)
  have hVres : V.map (residue O⟦X⟧)
      = (vτ.map (PowerSeries.C : O →+* O⟦X⟧)).map (residue O⟦X⟧) :=
    map_residue_eq (map_constantCoeff_infVred hf hu hvτn hfdeg hdvdτ hv hV)
  obtain ⟨cφ, sφ, s3, hsφ'⟩ := exists_bezout_lift (g := 2 * V) (h := 0) hUm
    ⟨c₁.map ((residue O⟦X⟧).comp (PowerSeries.C : O →+* O⟦X⟧)),
      c₂.map ((residue O⟦X⟧).comp (PowerSeries.C : O →+* O⟦X⟧)), 0, by
        have h := map_bezout ((residue O⟦X⟧).comp (PowerSeries.C : O →+* O⟦X⟧)) hbez
        rw [Polynomial.map_zero, zero_mul, add_zero, hUres, Polynomial.map_mul,
          Polynomial.map_ofNat, hVres]
        simp only [Polynomial.map_map]
        linear_combination h⟩
  have hsφ : cφ * infU hf uτ vτ + sφ * (2 * V) = 1 := by linear_combination hsφ'
  -- the ambient elements of `Frac(K⟦z⟧)`
  set A : Kz := ι' uψ with hAdef
  set Z : Kz := ι' PowerSeries.X with hZdef
  have hinj : Function.Injective ι' := IsFractionRing.injective (PowerSeries K) Kz
  obtain ⟨huψ0, huψne⟩ := ne_zero_of_eq_X_sq_mul (hf.map ψ) (map_infSeries_eq hf)
  have hA0 : A ≠ 0 := fun h ↦ huψne (hinj (by rw [hAdef] at h; rw [h, map_zero]))
  have hZ0 : Z ≠ 0 := fun h ↦
    PowerSeries.X_ne_zero (hinj (by rw [hZdef] at h; rw [h, map_zero]))
  set yv : Kz := Z⁻¹ * A⁻¹ ^ uτ.natDegree with hyvdef
  -- the chart's trace identity: the numerators are the powers of `x̂ = 1/u(z)`, times `x̂′`
  have hΘ (k : Fin uτ.natDegree) : 2 * yv
      * traceDiff (kzDerivation K) ((infU hf uτ vτ).map ρ) (sφ.map ρ) k
      = A⁻¹ ^ (k : ℕ) * kzDerivation K A⁻¹ := by
    have h : 2 * Z⁻¹ * A⁻¹ ^ uτ.natDegree
        * traceDiff (kzDerivation K) ((infU hf uτ vτ).map ρ) (sφ.map ρ) k
        = A⁻¹ ^ (k : ℕ) * kzDerivation K A⁻¹ :=
      two_mul_y_mul_traceDiff_infU_map hf hu hvτn hfdeg hdvdτ hbez hV hVdeg hVdvd k.isLt hsφ
    rw [hyvdef]
    linear_combination h
  have hdrive := two_mul_omegaPrime_kz_eq_sum hroot hcc haτ hbτ hsplitτ hunitτ hdF hπ hπ0 hf
    hfdeg havF hsPτ hUm (natDegree_infU hf hu hvτn hfdeg hdvdτ)
    (ζ := fun j ↦ infZeta hf uτ vτ j) (fun j ↦ by rw [infZeta]) hcc0
    (fun θ hθC hθX hθ0 k j ↦ traceMat_infU hf rfl θ hθC hθX hθ0 hu hv hw hbez hvτn hfdeg hV
      hVdeg hVdvd
      (bezout_ftauFoldPipe_map_setYZero hu rfl hv hw hbez hf hfdeg hroot hcc hbτ hdF hπ hπ0
        hsplitτ (fun i' j' hij ↦ by
          by_contra hne'
          exact (hunitτ i' j' hne').ne_zero (by rw [hij, sub_self])) hsPτ) hsφ k j)
    hΘ i
  -- the derivative of `x̂ = 1/u(z)`
  have hdA : kzDerivation K A = ι' (PowerSeries.derivative uψ) :=
    kzDerivation_algebraMap uψ
  have hdAinv : kzDerivation K A⁻¹ = -(A⁻¹ ^ 2) * ι' (PowerSeries.derivative uψ) := by
    rw [kzDerivation_inv hA0, hdA]
  -- the solved identity in the `h1` shape of the reflection bookkeeping
  set P : K[X] := tracePoly (uτ.map ψ) (c₂.map ψ) (Fin.cast (hu.natDegree_map ψ).symm i)
    with hPdef
  have hRHSsum : (∑ j, algebraMap K Kz ((traceMatrix (uτ.map ψ) (c₂.map ψ))⁻¹
        (finCongr (hu.natDegree_map ψ).symm i) (finCongr (hu.natDegree_map ψ).symm j))
        * (A⁻¹ ^ (j : ℕ) * kzDerivation K A⁻¹))
      = Polynomial.eval₂ (algebraMap K Kz) A⁻¹ ((2 : K) • P)
        * (-(A⁻¹ ^ 2) * ι' (PowerSeries.derivative uψ)) := by
    rw [hPdef, two_smul_tracePoly, Polynomial.eval₂_finsetSum, Finset.sum_mul]
    refine Fintype.sum_equiv (finCongr (hu.natDegree_map ψ).symm) _ _ fun j ↦ ?_
    rw [eval₂_mul, eval₂_C, eval₂_X_pow, hdAinv]
    simp only [finCongr_apply, Fin.val_cast]
    ring
  have : CharZero (PowerSeries K) := (PowerSeries.constantCoeff : K⟦X⟧ →+* K).charZero
  have : CharZero Kz := charZero_of_injective_algebraMap hinj
  have h1 : yv * ι' (omegaPrime (Φ.map ψ) ζK i)
      = aeval A⁻¹ P * (-(A⁻¹ ^ 2) * ι' (PowerSeries.derivative uψ)) := by
    have h2Kz : (2 : Kz) ≠ 0 := two_ne_zero
    refine mul_left_cancel₀ h2Kz ?_
    calc 2 * (yv * ι' (omegaPrime (Φ.map ψ) ζK i))
        = ∑ j, algebraMap K Kz ((traceMatrix (uτ.map ψ) (c₂.map ψ))⁻¹
            (finCongr (hu.natDegree_map ψ).symm i) (finCongr (hu.natDegree_map ψ).symm j))
            * (A⁻¹ ^ (j : ℕ) * kzDerivation K A⁻¹) := hdrive
      _ = Polynomial.eval₂ (algebraMap K Kz) A⁻¹ ((2 : K) • P)
            * (-(A⁻¹ ^ 2) * ι' (PowerSeries.derivative uψ)) := hRHSsum
      _ = 2 * (aeval A⁻¹ P * (-(A⁻¹ ^ 2) * ι' (PowerSeries.derivative uψ))) := by
          rw [smul_eq_C_mul, eval₂_mul, eval₂_C, aeval_def,
            show algebraMap K Kz 2 = (2 : Kz) from map_ofNat _ 2]
          ring
  -- the reflection bookkeeping
  have hPdeg : P.natDegree ≤ uτ.natDegree - 1 := by
    have hd := degree_tracePoly_lt (u := uτ.map ψ) (s := c₂.map ψ)
      (Fin.cast (hu.natDegree_map ψ).symm i)
    rcases eq_or_ne P 0 with h0 | h0
    · rw [h0, natDegree_zero]
      exact Nat.zero_le _
    · have h1' := (natDegree_lt_iff_degree_lt h0).mpr hd
      rw [hu.natDegree_map ψ] at h1'
      lia
  exact eq_neg_X_mul_aeval_reflect i.pos hPdeg huψne h1

/-- **The `hW`-identification at the infinity centre, from per-disk hypotheses only**: if
the numerator `h₀` has coordinates `cs` in the trace-form basis, then the integral disk
expansion of `h₀·dx/y` at `∞` is `∑_i cs_i·ω′_i` for the infinity chart coordinates
`infZeta` — the `hW` slot of `ChabautyColeman.encard_inter_residueDisk_le_ordPoint_inf`.
The coordinate identity `hmap` is disk-independent
(`ChabautyColeman.exists_annihilator_tracePoly`), so a single differential serves every
disk. -/
theorem map_omegaExpansionInf_eq_sum_smul_omegaPrime_tracePoly {hu : uτ.Monic}
    (hroot : ∀ i, (ftauUY uτ uτ.natDegree).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (haτ : ∀ i, uτ.eval (aτ i) = 0) (hbτ : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplitτ : uτ = ∏ m' : Fin uτ.natDegree, (X - C (aτ m')))
    (hunitτ : ∀ i j : Fin uτ.natDegree, i ≠ j → IsUnit (aτ i - aτ j))
    (hdF : IsFtauFoldCerts Aτ aτ bτ hu rfl hv hw hbez dF)
    {π : O} (hπ : maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hf : f.Monic) (hvτn : vτ.natDegree < uτ.natDegree)
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1)
    {V : (O⟦X⟧)[X]} (hV : C PowerSeries.X * V = -(infV hf uτ vτ %ₘ infU hf uτ vτ))
    (hVdeg : V.degree < (infU hf uτ vτ).degree)
    (hVdvd : infU hf uτ vτ ∣ V ^ 2 - f.map PowerSeries.C)
    (havF : IsFtauFoldAvoid Aτ aτ bτ hu rfl hv hw hbez dF)
    {cs : Fin uτ.natDegree → K} {h₀ : O[X]}
    (hmap : h₀.map ψ = ∑ i, cs i • tracePoly (uτ.map ψ) (c₂.map ψ)
      (Fin.cast (hu.natDegree_map ψ).symm i)) :
    PowerSeries.map ψ (omegaExpansionInf h₀ hf)
      = ∑ i, cs i • omegaPrime ((ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot hcc haτ hbτ
          hdF hπ hπ0 hsplitτ hunitτ).map ψ)
          (fun s ↦ PowerSeries.map ψ (infZeta hf uτ vτ s)) i := by
  set uψK := PowerSeries.map ψ (infSeries hf) with huψdef
  obtain ⟨-, huψ0⟩ := ne_zero_of_eq_X_sq_mul (hf.map ψ) (map_infSeries_eq hf)
  have hgen : genus f = uτ.natDegree := genus_eq_of_natDegree hfdeg
  have hreflsum : ∀ (s : Finset (Fin uτ.natDegree)) (F : Fin uτ.natDegree → K[X]),
      reflect (uτ.natDegree - 1) (∑ i ∈ s, F i)
        = ∑ i ∈ s, reflect (uτ.natDegree - 1) (F i) := by
    intro s F
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, reflect_add, ih]
  refine mul_left_cancel₀ huψ0 ?_
  calc uψK * PowerSeries.map ψ (omegaExpansionInf h₀ hf)
      = PowerSeries.map ψ (infSeries hf * omegaExpansionInf h₀ hf) := by rw [map_mul, huψdef]
    _ = -PowerSeries.X * aeval uψK (reflect (uτ.natDegree - 1) (h₀.map ψ))
        * PowerSeries.derivative uψK := by
        rw [infSeries_mul_omegaExpansionInf, hgen, map_mul, map_mul, map_neg,
          PowerSeries.map_X, PowerSeries.map_aeval, PowerSeries.map_derivative, ← reflect_map]
    _ = -PowerSeries.X * (∑ i, cs i • aeval uψK (reflect (uτ.natDegree - 1)
          (tracePoly (uτ.map ψ) (c₂.map ψ) (Fin.cast (hu.natDegree_map ψ).symm i))))
        * PowerSeries.derivative uψK := by
        rw [hmap, hreflsum]
        congr 2
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by
          rw [show cs i • tracePoly (uτ.map ψ) (c₂.map ψ)
                (Fin.cast (hu.natDegree_map ψ).symm i)
              = C (cs i) * tracePoly (uτ.map ψ) (c₂.map ψ)
                (Fin.cast (hu.natDegree_map ψ).symm i) from smul_eq_C_mul _,
            reflect_C_mul, map_mul, aeval_C, Algebra.smul_def]
    _ = ∑ i, cs i • (uψK * omegaPrime ((ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot hcc haτ
          hbτ hdF hπ hπ0 hsplitτ hunitτ).map ψ)
          (fun s ↦ PowerSeries.map ψ (infZeta hf uτ vτ s)) i) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [infSeries_mul_omegaPrime_kz hroot hcc haτ hbτ hsplitτ hunitτ hdF hπ hπ0 hf hvτn
          hfdeg hV hVdeg hVdvd havF i, mul_smul_comm, smul_mul_assoc]
    _ = uψK * ∑ i, cs i • omegaPrime ((ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot hcc haτ
          hbτ hdF hπ hπ0 hsplitτ hunitτ).map ψ)
          (fun s ↦ PowerSeries.map ψ (infZeta hf uτ vτ s)) i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ (mul_smul_comm _ _ _).symm

end KzAssembleInf

end ChabautyColeman

end
