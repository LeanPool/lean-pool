/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.OmegaExpansion
public import LeanPool.HyperellipticCurves.ForMathlib.PowerSeries
public import LeanPool.HyperellipticCurves.Log.Charts.DiskTransport
public import LeanPool.HyperellipticCurves.Log.Trace.TraceAvoid
public import LeanPool.HyperellipticCurves.Log.Trace.TraceDisk

import LeanPool.HyperellipticCurves.ForMathlib.Units
import LeanPool.HyperellipticCurves.Log.Fold.FoldTrace

/-!
# The trace-form identity, per residue disk

Clause (c) of `thm:omega-prime-global` run **directly on the per-disk pipeline** over
`Frac(K⟦z⟧)` with the derivation `d/dz` — no function field, no expansion homomorphisms, no
rational realization of the inverse differential matrix.

* `ChabautyColeman.kzDerivation`: `d/dz` on `Frac(K⟦z⟧)` as a bundled `K`-derivation (the
  fraction-field extension of `PowerSeries.derivative`).
* `ChabautyColeman.two_mul_y_mul_traceDiff_phiPipeline_map`: the per-disk trace identity at
  a generic centre — in `Frac(K⟦z⟧)`, `2·y(z)·Θ_k = x(z)^k` on the mapped disk pipeline,
  where `x(z) = a + z`, `y(z) = b·η(z)` is the moving disk point. The two constant blocks die
  and the moving pair block evaluates at the disk point; its `x`-separation from the constant
  point is a unit outright (`z`-coefficient `1`), so no transcendence enters.
* `ChabautyColeman.kzOmega` with `ChabautyColeman.two_mul_kzOmega_eq_sum`: the shared solve
  driver — numerators linear in the matrix, inverted through the constant trace matrix.
* `ChabautyColeman.two_mul_omegaPrime_kz_eq_sum`: the solve carried out once for all three
  charts. Given a chart datum (a monic `u`-part over `O⟦z⟧` with a Bézout partner, chart
  coordinates vanishing at `z = 0`, and its trace matrix identified with the substituted
  universal one) and the chart's trace identity, it returns `2·y·ω′_i` as the `i`-th
  coordinate of the numerators in the constant trace matrix. The generic, Weierstrass
  (`ChabautyColeman.X_mul_omegaPrime_eq_aeval_tracePoly_mul_derivative`) and infinity
  (`ChabautyColeman.infSeries_mul_omegaPrime_kz`) capstones are its three instances.
* `ChabautyColeman.yseries_mul_omegaPrime_eq_taylor_tracePoly_kz`: the capstone —
  `b·η·ω′_i = taylor (tracePoly i)` on the generic disk, from per-disk hypotheses only.
  The matrix `N` is the *honest* substituted inverse differential matrix
  `subst ζ (M⁻¹)` in `K⟦z⟧`, `NdM·N = 1` comes from
  `ChabautyColeman.FormalGroupLaw.isUnit_diffMatrix` upstairs, and the formal identity
  `C·M = C(0)` of the fold is pushed *forward* along the substitution homomorphism — no
  injective descent anywhere.
* `ChabautyColeman.map_omegaExpansionGeneric_eq_sum_smul_omegaPrime`: consequently, a
  polynomial `h₀` whose coordinates in the trace-form basis are `cs` has
  `omegaExpansionGeneric f h₀ a b = ∑ᵢ csᵢ·ω′ᵢ` — the `hW` hypothesis of
  `ChabautyColeman.encard_inter_residueDisk_le_ordPoint`.

Blueprint node: `thm:omega-prime-global`, clause (c).
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped Matrix PowerSeries

namespace ChabautyColeman

/-! ### The `z`-derivative on `Frac(K⟦z⟧)` as a derivation -/

section KzDerivation

variable {K : Type*} [Field K]

variable (K) in
/-- The `z`-derivative on the fraction field of `K⟦z⟧`, as a `K`-derivation. -/
noncomputable def kzDerivation : Derivation K (FractionRing K⟦X⟧) (FractionRing K⟦X⟧) :=
  IsFractionRing.derivation (PowerSeries.derivative (R := K))

/-- The bundled derivation and the bare quotient-rule derivative agree. -/
@[simp] theorem coe_kzDerivation : ⇑(kzDerivation K) = kzDeriv K := rfl

/-- The quotient rule for inverses, for the bundled derivation. -/
theorem kzDerivation_inv {x : FractionRing K⟦X⟧} (hx : x ≠ 0) :
    kzDerivation K x⁻¹ = -(x⁻¹ ^ 2) * kzDerivation K x :=
  kzDeriv_inv hx

theorem kzDerivation_algebraMap (G : K⟦X⟧) :
    kzDerivation K (algebraMap K⟦X⟧ (FractionRing K⟦X⟧) G)
      = algebraMap K⟦X⟧ (FractionRing K⟦X⟧) (PowerSeries.derivative G) :=
  IsFractionRing.derivation_algebraMap _ G

end KzDerivation

/-! ### The per-disk trace identity, generic chart -/

section KzGeneric

variable {O : Type*} [CommRing O] {K : Type*} [Field K] {ψ : O →+* K}

/-- The coefficient map from the disk series ring into `Frac(K⟦z⟧)`. -/
noncomputable def kzHom (ψ : O →+* K) : O⟦X⟧ →+* FractionRing (PowerSeries K) :=
  (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (PowerSeries.map ψ)

theorem kzHom_apply (G : O⟦X⟧) :
    kzHom ψ G = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (PowerSeries.map ψ G) :=
  rfl

theorem kzDerivation_kzHom_C (c : O) : kzDerivation K (kzHom ψ (PowerSeries.C c)) = 0 := by
  rw [kzHom_apply, PowerSeries.map_C, kzDerivation_algebraMap,
    PowerSeries.derivative_C, map_zero]

theorem kzDerivation_coeff_map_C_eq_zero (p : O[X]) (i : ℕ) :
    kzDerivation K (((p.map (PowerSeries.C : O →+* O⟦X⟧)).map (kzHom ψ)).coeff i) = 0 := by
  rw [Polynomial.map_map, coeff_map, RingHom.comp_apply]
  exact kzDerivation_kzHom_C _

end KzGeneric

section KzTraceGeneric

variable {O : Type*} [CommRing O] {K : Type*} [Field K] {ψ : O →+* K}
  {f : O[X]} {a b xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ c₁ c₂ : O[X]}
  {d : CantorCertData O⟦X⟧} {g k : ℕ}

local notation "Kz" => FractionRing (PowerSeries K)

/-- **The per-disk trace-form identity, generic chart**: in `Frac(K⟦z⟧)` with the
derivation `d/dz`, the trace-form differential of the mapped disk pipeline satisfies
`2·y(z)·Θ_k = x(z)^k`, where `x(z) = a + z` and `y(z) = b·η(z)` are the coordinates of the
moving disk point. The two constant blocks die and the moving pair block evaluates at the
disk point, whose `x`-separation from the constant point is a unit outright (`z`-coefficient
`1`) — no transcendence is involved. -/
theorem two_mul_y_mul_traceDiff_phiPipeline_map (hf : f.Monic)
    (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ) (hyQu : IsUnit yQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
    (hfdeg : f.natDegree = 2 * g + 1) (hk : k < g)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree)
    (hav : IsPipelineAvoid (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d)
    {cP sP : Polynomial O⟦X⟧}
    (hsP : cP * (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1
      + sP * (2 * (phiPipeline f a b xQ yQ m m₀ uτ vτ d).2) = 1) :
    2 * kzHom ψ (PowerSeries.C b * diskSeriesGeneric f a)
        * traceDiff (kzDerivation K)
            ((phiPipeline f a b xQ yQ m m₀ uτ vτ d).1.map (kzHom ψ)) (sP.map (kzHom ψ)) k
      = kzHom ψ (PowerSeries.C a + PowerSeries.X) ^ k := by
  rw [phiPipeline] at hsP ⊢
  set ρ : O⟦X⟧ →+* Kz := kzHom ψ with hρdef
  set F := f.map (PowerSeries.C : O →+* O⟦X⟧) with hFdef
  set D := phiConfig f a b xQ yQ m m₀ uτ vτ with hDdef
  -- block data over `O⟦z⟧`
  have hu₁ : (phiU₁ a xQ).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hd₁ : phiU₁ a xQ ∣ phiV₁ f a b m ^ 2 - F := movingPair_dvd hsep hm hb hfa h2 hyQ
  have hu₂ : (uτ.map (PowerSeries.C : O →+* O⟦X⟧)).Monic := huτ.map _
  have hd₂ : uτ.map (PowerSeries.C : O →+* O⟦X⟧)
      ∣ (vτ.map PowerSeries.C) ^ 2 - F := map_dvd_sq_sub _ hdvdτ
  have hu₃ : (phiU₃ a xQ (O := O)).Monic := ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have hsep' : IsUnit (a - xQ) := by rw [← neg_sub]; exact hsep.neg
  have hd₃ : phiU₃ a xQ ∣ phiV₃ xQ yQ m₀ ^ 2 - F :=
    map_dvd_sq_sub _ (pair_dvd hsep' hm₀ hyQ (by rwa [neg_pow_two]))
  -- Bézout certificates for the three blocks over `O⟦z⟧`
  have hbu : IsUnit b := (isUnit_pow_iff two_ne_zero).mp (hb ▸ hfa)
  obtain ⟨e₁, s₁, hs₁⟩ := isCoprime_phiU₁ hm h2 hbu hyQu
  obtain ⟨e₂, s₂, hs₂⟩ := isCoprime_two_mul_map ⟨c₁, c₂, hbez⟩
    (PowerSeries.C : O →+* O⟦X⟧)
  obtain ⟨e₃, s₃, hs₃⟩ := isCoprime_phiU₃ hm₀ h2 hbu hyQu
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
  -- the constant blocks die
  have hτ0 i : kzDerivation K (((D.map ρ).u₂).coeff i) = 0 := by
    rw [hDdef, PipelineData.map_u₂, phiConfig_u₂]
    exact kzDerivation_coeff_map_C_eq_zero uτ i
  have hB0 i : kzDerivation K (((D.map ρ).u₃).coeff i) = 0 := by
    rw [hDdef, PipelineData.map_u₃, phiConfig_u₃, phiU₃]
    exact kzDerivation_coeff_map_C_eq_zero _ i
  have hfc : ∀ i, kzDerivation K ((F.map ρ).coeff i) = 0 := fun i ↦
    kzDerivation_coeff_map_C_eq_zero f i
  have h₂ : traceDiff (kzDerivation K) ((D.map ρ).u₂) (s₂.map ρ) k = 0 :=
    traceDiff_eq_zero_of_dotDer_eq_zero _ hτ0 _ k
  have h₃ : traceDiff (kzDerivation K) ((D.map ρ).u₃) (s₃.map ρ) k = 0 :=
    traceDiff_eq_zero_of_dotDer_eq_zero _ hB0 _ k
  -- the moving pair block evaluates at the disk point
  have hd1 : kzDerivation K (ρ (PowerSeries.C a + PowerSeries.X)) = 1 := by
    rw [hρdef, kzHom_apply, kzDerivation_algebraMap]
    simp
  have hαβ : IsUnit (ρ (PowerSeries.C a + PowerSeries.X) - ρ (PowerSeries.C xQ)) := by
    rw [← map_sub]
    refine isUnit_iff_ne_zero.mpr fun h0 ↦ ?_
    rw [hρdef, kzHom_apply,
      map_eq_zero_iff _ (IsFractionRing.injective (PowerSeries K) Kz)] at h0
    have h1 := congrArg (PowerSeries.coeff 1) h0
    simp at h1
  have hs₁ρ : e₁.map ρ * ((X - C (ρ (PowerSeries.C a + PowerSeries.X)))
        * (X - C (ρ (PowerSeries.C xQ))))
      + s₁.map ρ * (2 * (phiV₁ f a b m).map ρ) = 1 := by
    have h := map_bezout ρ hs₁
    rwa [phiU₁_map] at h
  have h₁ := traceDiff_pair (kzDerivation K) (α := ρ (PowerSeries.C a + PowerSeries.X))
    (β := ρ (PowerSeries.C xQ)) (by
      rw [hρdef, kzHom_apply, PowerSeries.map_C, kzDerivation_algebraMap]
      simp) hαβ hs₁ρ k
  rw [show ((phiV₁ f a b m).map ρ).eval (ρ (PowerSeries.C a + PowerSeries.X))
      = ρ (PowerSeries.C b * diskSeriesGeneric f a) by
        rw [phiV₁, pairV_map, pairV_eval_left], hd1, mul_one] at h₁
  -- assemble along the pipeline over `Frac(K⟦z⟧)`
  have hfdegρ : (F.map ρ).natDegree = 2 * g + 1 := by
    rw [hFdef, Polynomial.map_map, hf.natDegree_map, hfdeg]
  -- the mapped blocks of `D` are the mapped blocks of the configuration, definitionally
  have htot := traceDiff_cantorPipeline (kzDerivation K)
    (D := D.map ρ) (dt := d.map ρ) (f := F.map ρ)
    (hu₁.map ρ) (map_dvd_sq_sub ρ hd₁) (hu₂.map ρ) (map_dvd_sq_sub ρ hd₂)
    (hu₃.map ρ) (map_dvd_sq_sub ρ hd₃) hcertsρ havρ hfc hfdegρ hk
    (map_bezout ρ hs₁) (map_bezout ρ hs₂) (map_bezout ρ hs₃) hsPρ
  rw [hPa, htot, h₂, h₃, add_zero, add_zero, show (D.map ρ).u₁ = (phiU₁ a xQ).map ρ from rfl,
    phiU₁_map]
  exact h₁

end KzTraceGeneric

/-- `a = c·d` from `a·b = c` and `b·d = 1`. -/
theorem eq_mul_of_mul_eq {M : Type*} [Monoid M] {a b c d : M} (h : a * b = c) (hb : b * d = 1) :
    a = c * d := by
  rw [← h, mul_assoc, hb, mul_one]

/-! ### The per-disk solve driver -/

section KzOmega

variable {n : Type*} [Fintype n] {A : Type*} [CommRing A]

/-- **The per-disk differential numerator family**: the combination `y·∑_j N_ij·D(ζ_j)` of
the derivatives of the chart coordinates, weighted by a matrix `N` — over `Frac(K⟦z⟧)` with
`N` the substituted inverse differential matrix this is `y·ω′_i`. The shared endpoint of the
three chart assemblies. -/
def kzOmega (yv : A) (dz : n → A) (N : Matrix n n A) (i : n) : A :=
  yv * ∑ j, N i j * dz j

/-- The numerators are linear in the matrix. -/
theorem kzOmega_matrix_mul (yv : A) (dz : n → A) (A' N : Matrix n n A) (i : n) :
    kzOmega yv dz (A' * N) i = ∑ l, A' i l * kzOmega yv dz N l := by
  simp only [kzOmega, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

variable [DecidableEq n]

/-- **The solve step**: if an invertible constant matrix `Ac` combines the numerators into
the family `pw` (in the applications: the powers `x(z)^i·dx/dz`), then each numerator is the
`Ac⁻¹`-combination of the `pw`. -/
theorem two_mul_kzOmega_eq_sum {K' : Type*} [CommRing K'] {χ : K' →+* A}
    {Ac : Matrix n n K'} (hAc : IsUnit Ac.det) {yv : A} {dz : n → A} {N : Matrix n n A}
    {pw : n → A} (h : ∀ i, 2 * kzOmega yv dz (Ac.map χ * N) i = pw i) (l : n) :
    2 * kzOmega yv dz N l = ∑ i, χ (Ac⁻¹ l i) * pw i := by
  have hmul := congrArg (RingHom.mapMatrix (m := n) χ) (Matrix.mul_nonsing_inv Ac hAc)
  rw [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at hmul
  have hdet : IsUnit (Ac.map χ).det := (RingHom.map_det χ Ac) ▸ hAc.map χ
  have hvec : Ac.map χ *ᵥ (fun l ↦ 2 * kzOmega yv dz N l) = pw := by
    funext i
    rw [← h i, kzOmega_matrix_mul, Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  let : Invertible (Ac.map χ) := (Ac.map χ).invertibleOfIsUnitDet hdet
  have hsol := congrFun (Matrix.inv_mulVec_eq_vec hvec.symm).symm l
  rw [hsol, Matrix.mulVec_apply_eq_sum, Matrix.inv_eq_right_inv hmul]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [Matrix.map_apply]

end KzOmega

/-! ### The trace-form solve, uniformly in the chart

The three per-disk capstones — generic, Weierstrass and infinity — differ only in their chart
datum and in the numerators produced by the chart's trace identity. Everything between is the
same computation, carried out once here.
-/

section KzOmegaChart

variable {K : Type*} [Field K]

local notation "Kz" => FractionRing (PowerSeries K)

/-- **The solved numerator is the differential.** With the substituted inverse differential
matrix as weights and the derivatives of the chart coordinates as entries, the numerator
family of the trace system is `y·ω′_i`, embedded in `Frac(K⟦z⟧)`. -/
theorem kzOmega_mapMatrix_diffMatrix_inv {m : ℕ} (Φ : FormalGroupLaw K (Fin m)) {ζ : Fin m → K⟦X⟧}
    (hζ : MvPowerSeries.HasSubst ζ) (yv : Kz) (i : Fin m) :
    kzOmega yv (fun j ↦ kzDerivation K (algebraMap (PowerSeries K) Kz (ζ j)))
        (((algebraMap (PowerSeries K) Kz).comp
          (MvPowerSeries.substRingHom hζ)).mapMatrix Φ.diffMatrix⁻¹) i
      = yv * algebraMap (PowerSeries K) Kz (omegaPrime Φ ζ i) := by
  rw [kzOmega, omegaPrime, map_sum]
  refine congrArg (yv * ·) (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [map_mul, RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.comp_apply,
    MvPowerSeries.substRingHom_apply, kzDerivation_algebraMap, pderiv_unit_eq_derivative]

end KzOmegaChart

section TraceMatrixReduce

variable {O : Type*} [CommRing O] {K : Type*} [Field K] {uτ vτ c₁ c₂ : O[X]}

/-- The constant trace matrix of the `τ`-datum, reindexed along the degree of the reduced
centre: `traceMat` at `Fin uτ.natDegree` is the trace matrix of the reduction. -/
theorem of_traceMat_map_eq_submatrix (hu : uτ.Monic) (ψ : O →+* K) :
    Matrix.of (fun k j : Fin uτ.natDegree ↦ traceMat (uτ.map ψ) (c₂.map ψ) k j)
      = (traceMatrix (uτ.map ψ) (c₂.map ψ)).submatrix
        (finCongr (hu.natDegree_map ψ).symm) (finCongr (hu.natDegree_map ψ).symm) := by
  ext k j
  rfl

/-- The reduction of a Bézout pair is coprime, so its trace matrix is invertible. -/
theorem isUnit_det_traceMatrix_map (hu : uτ.Monic)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1) (ψ : O →+* K) :
    IsUnit (traceMatrix (uτ.map ψ) (c₂.map ψ)).det :=
  isUnit_iff_ne_zero.mpr (det_traceMatrix_ne_zero (hu.map ψ)
    ⟨c₁.map ψ, 2 * vτ.map ψ, by have h := map_bezout ψ hbez; linear_combination h⟩)

end TraceMatrixReduce

section KzChartSolve

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O]
  {K : Type*} [Field K] {ψ : O →+* K}
  {f uτ vτ w c₁ c₂ : O[X]}
  {dF : FoldCertData (MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O) uτ.natDegree}
  {Aτ : Fin uτ.natDegree → MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O}
  {aτ bτ : Fin uτ.natDegree → O}
  {hv : vτ.degree < uτ.degree} {hw : vτ ^ 2 - f = uτ * w}
  {hbez : c₁ * uτ + c₂ * (2 * vτ) = 1}
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

local notation "Kz" => FractionRing (PowerSeries K)

/-- **The trace-form solve in chart coordinates.** Let `P` be the monic `u`-part of a chart
datum over `O⟦z⟧`, with `sφ` a Bézout partner, chart coordinates `ζ` vanishing at `z = 0`, and
trace matrix the substituted universal one (`hT`). If the chart's trace identity expresses
`2·yv·Θ_k` as a numerator `num k`, then the differential `ω′_i` of the folded formal group law
is the `i`-th coordinate of `num` in the constant trace matrix:
`2·yv·ω′_i = ∑_j (T(uτ, c₂)⁻¹)_{ij}·num_j` in `Frac(K⟦z⟧)`.

The chart enters only through `P`, `ζ`, `hT` and `num`; the generic, Weierstrass and infinity
capstones are the three instances. -/
theorem two_mul_omegaPrime_kz_eq_sum {hu : uτ.Monic}
    (hroot : ∀ i, (ftauUY uτ uτ.natDegree).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (haτ : ∀ i, uτ.eval (aτ i) = 0) (hbτ : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplitτ : uτ = ∏ m' : Fin uτ.natDegree, (X - C (aτ m')))
    (hunitτ : ∀ i j : Fin uτ.natDegree, i ≠ j → IsUnit (aτ i - aτ j))
    (hdF : IsFtauFoldCerts Aτ aτ bτ hu rfl hv hw hbez dF)
    {π : O} (hπ : maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hf : f.Monic) (hfdeg : f.natDegree = 2 * uτ.natDegree + 1)
    (havF : IsFtauFoldAvoid Aτ aτ bτ hu rfl hv hw hbez dF)
    {cPτ sPτ : (MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O)[X]}
    (hsPτ : cPτ * (ftauFoldPipe Aτ aτ bτ hu rfl hv hw hbez dF).1
      + sPτ * (2 * (ftauFoldPipe Aτ aτ bτ hu rfl hv hw hbez dF).2) = 1)
    {P sφ : (O⟦X⟧)[X]} (hPm : P.Monic) (hPdeg : P.natDegree = uτ.natDegree)
    {ζ : Fin uτ.natDegree → O⟦X⟧} (hζdef : ∀ j, ζ j = chartCoords PowerSeries.C uτ P j)
    (hcc0 : ∀ j, PowerSeries.constantCoeff (ζ j) = 0)
    (hT : ∀ θ : MvPowerSeries (Fin uτ.natDegree) O →+* O⟦X⟧,
      θ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin uτ.natDegree) O) = PowerSeries.C →
      (∀ j : Fin uτ.natDegree, θ (MvPowerSeries.X j) = ζ j) →
      (∀ g, PowerSeries.constantCoeff (θ g) = MvPowerSeries.constantCoeff g) →
      ∀ k j : ℕ, traceMat P sφ k j
        = θ (traceMat (chartU uτ uτ.natDegree) (sPτ.map setYZero) k j))
    {yv : Kz} {num : Fin uτ.natDegree → Kz}
    (hΘ : ∀ k : Fin uτ.natDegree, 2 * yv
      * traceDiff (kzDerivation K) (P.map (kzHom ψ)) (sφ.map (kzHom ψ)) k = num k)
    (i : Fin uτ.natDegree) :
    2 * (yv * algebraMap (PowerSeries K) Kz
        (omegaPrime ((ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot hcc haτ hbτ hdF hπ hπ0
            hsplitτ hunitτ).map ψ) (fun j ↦ PowerSeries.map ψ (ζ j)) i))
      = ∑ j : Fin uτ.natDegree,
          algebraMap K Kz ((traceMatrix (uτ.map ψ) (c₂.map ψ))⁻¹
            (finCongr (hu.natDegree_map ψ).symm i) (finCongr (hu.natDegree_map ψ).symm j))
          * num j := by
  classical
  have hainj := Function.injective_of_isUnit_sub hunitτ
  set Φ := ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot hcc haτ hbτ hdF hπ hπ0
    hsplitτ hunitτ
  set ζK : Fin uτ.natDegree → K⟦X⟧ := fun j ↦ PowerSeries.map ψ (ζ j) with hζKdef
  set ι' : K⟦X⟧ →+* Kz := algebraMap (PowerSeries K) Kz
  set ρ : O⟦X⟧ →+* Kz := kzHom (O := O) ψ with hρdef
  have hccK0 (j : Fin uτ.natDegree) : PowerSeries.constantCoeff (ζK j) = 0 := by
    simp only [hζKdef, PowerSeries.constantCoeff_map, hcc0 j, map_zero]
  have hζ : MvPowerSeries.HasSubst ζ := MvPowerSeries.hasSubst_of_constantCoeff_zero hcc0
  have hζK : MvPowerSeries.HasSubst ζK :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hccK0
  set θ := MvPowerSeries.substRingHom hζ with hθdef
  set χ : MvPowerSeries (Fin uτ.natDegree) K →+* Kz := ι'.comp (MvPowerSeries.substRingHom hζK)
    with hχdef
  obtain ⟨cY, sY, hsY⟩ := isCoprime_chartU_map_rename hu rfl hv hw hbez Sum.inr
  have hsχ := bezout_ftauFoldPipe_map_setYZero hu rfl hv hw hbez hf hfdeg hroot hcc hbτ hdF
    hπ hπ0 hsplitτ hainj hsPτ
  -- the two matrices over `Frac(K⟦z⟧)`
  set NdM : Matrix (Fin uτ.natDegree) (Fin uτ.natDegree) Kz :=
    χ.mapMatrix (Φ.map ψ).diffMatrix with hNdMdef
  set N : Matrix (Fin uτ.natDegree) (Fin uτ.natDegree) Kz :=
    χ.mapMatrix (Φ.map ψ).diffMatrix⁻¹ with hNdef
  have hmulN : NdM * N = 1 := by
    have h1 : (Φ.map ψ).diffMatrix * (Φ.map ψ).diffMatrix⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Φ.map ψ).isUnit_diffMatrix)
    have h2' := congrArg (RingHom.mapMatrix χ) h1
    rwa [map_mul, map_one] at h2'
  set T : Matrix (Fin uτ.natDegree) (Fin uτ.natDegree) Kz :=
    Matrix.of fun k j ↦ traceMat (P.map ρ) (sφ.map ρ) k j with hTdef
  have hTρ (k j : Fin uτ.natDegree) :
      T k j = ρ (θ (traceMat (chartU uτ uτ.natDegree) (sPτ.map setYZero) k j)) := by
    rw [hTdef, Matrix.of_apply, traceMat_map ρ hPm sφ, hθdef,
      hT (MvPowerSeries.substRingHom hζ) (MvPowerSeries.substRingHom_comp_C hζ)
        (MvPowerSeries.substRingHom_X hζ)
        (MvPowerSeries.constantCoeff_substRingHom hζ hcc0) k j]
  have hM (j k : Fin uτ.natDegree) : ρ (θ (Φ.diffMatrix j k)) = NdM j k := by
    have h := map_substRingHom_diffMatrix Φ ψ hζ
      (MvPowerSeries.hasSubst_map_of_constantCoeff_zero ψ hcc0) j k
    rw [hNdMdef, RingHom.mapMatrix_apply, Matrix.map_apply, hχdef, RingHom.comp_apply,
      hρdef, kzHom_apply]
    refine congrArg ι' ?_
    simp only [hθdef, hζKdef, MvPowerSeries.substRingHom_apply] at h ⊢
    exact h
  set Ac : Matrix (Fin uτ.natDegree) (Fin uτ.natDegree) K :=
    Matrix.of fun k j ↦ traceMat (uτ.map ψ) (c₂.map ψ) k j with hAcdef
  have hAc (k j : Fin uτ.natDegree) : ρ (θ (MvPowerSeries.C (traceMat uτ c₂ k j)))
      = algebraMap K Kz (Ac k j) := by
    rw [hθdef, show θ (MvPowerSeries.C (traceMat uτ c₂ k j))
        = PowerSeries.C (traceMat uτ c₂ k j) from
      RingHom.congr_fun (MvPowerSeries.substRingHom_comp_C hζ) _, hρdef, kzHom_apply,
      PowerSeries.map_C, hAcdef, Matrix.of_apply, traceMat_map ψ hu c₂ k j]
    rfl
  have hform (k j : Fin uτ.natDegree) :
      ∑ j' : Fin uτ.natDegree, T k j' * NdM j' j = algebraMap K Kz (Ac k j) := by
    have h := sum_traceMat_mul_setYZero_pderiv_FtauFold_eq_C hu rfl hv hw hbez hf hfdeg hroot
      hcc haτ hbτ hdF hπ hπ0 hsplitτ hainj hsY
      (sum_traceMat_ftauFoldPipe hu rfl hv hw hbez hf hfdeg hroot hcc haτ hbτ hdF hunitτ
        havF j k.isLt hsY hsPτ)
    have h2' := congrArg (ρ.comp θ) h
    rw [map_sum] at h2'
    rw [← hAc k j]
    refine Eq.trans (Finset.sum_congr rfl fun j' _ ↦ ?_) h2'
    rw [RingHom.comp_apply, map_mul, hTρ k j', ← hM j' j,
      ftauFoldFGL_diffMatrix_eq hf hfdeg hroot hcc haτ hbτ hdF hπ hπ0 hsplitτ hunitτ j' j]
    exact (map_mul ρ _ _).symm
  have hTNdM : T * NdM = Ac.map (algebraMap K Kz) :=
    Matrix.ext fun k j ↦ by rw [Matrix.mul_apply, hform k j, Matrix.map_apply]
  have hTAcN : T = Ac.map (algebraMap K Kz) * N := eq_mul_of_mul_eq hTNdM hmulN
  have he : Ac = (traceMatrix (uτ.map ψ) (c₂.map ψ)).submatrix
      (finCongr (hu.natDegree_map ψ).symm) (finCongr (hu.natDegree_map ψ).symm) :=
    of_traceMat_map_eq_submatrix hu ψ
  have hdet : IsUnit Ac.det := by
    rw [he, Matrix.det_submatrix_equiv_self]
    exact isUnit_det_traceMatrix_map hu hbez ψ
  have hAcinv : Ac⁻¹ = (traceMatrix (uτ.map ψ) (c₂.map ψ))⁻¹.submatrix
      (finCongr (hu.natDegree_map ψ).symm) (finCongr (hu.natDegree_map ψ).symm) := by
    rw [he, Matrix.inv_submatrix_equiv]
  -- the trace identity, in chart coordinates
  have hζdecomp : P.map ρ = uτ.map (ρ.comp (PowerSeries.C : O →+* O⟦X⟧))
      + ∑ j : Fin uτ.natDegree, C (ρ (ζ j)) * X ^ (j : ℕ) := by
    have hdeg' : (P.map ρ).natDegree = uτ.natDegree := by rw [hPm.natDegree_map, hPdeg]
    refine (eq_add_chartCoords (φ := ρ.comp (PowerSeries.C : O →+* O⟦X⟧)) hu (hPm.map ρ)
      hdeg').trans ?_
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hζdef j, map_chartCoords (φ := (PowerSeries.C : O →+* O⟦X⟧)) ρ]
  have hu₀0 : ∀ i', kzDerivation K
      ((uτ.map (ρ.comp (PowerSeries.C : O →+* O⟦X⟧))).coeff i') = 0 := by
    intro i'
    have h := kzDerivation_coeff_map_C_eq_zero (ψ := ψ) uτ i'
    rwa [Polynomial.map_map] at h
  have hsum (k : Fin uτ.natDegree) : traceDiff (kzDerivation K) (P.map ρ) (sφ.map ρ) k
      = ∑ j : Fin uτ.natDegree, T k j * kzDerivation K (ρ (ζ j)) :=
    traceDiff_eq_sum _ hu₀0 hζdecomp _ k
  -- the numerators, solved
  set dz : Fin uτ.natDegree → Kz := fun j ↦ kzDerivation K (ρ (ζ j)) with hdzdef
  have hOmega (k : Fin uτ.natDegree) :
      2 * kzOmega yv dz (Ac.map (algebraMap K Kz) * N) k = num k := by
    have h := hΘ k
    rw [hsum k] at h
    rw [← hTAcN, kzOmega]
    linear_combination h
  have hdrive := two_mul_kzOmega_eq_sum hdet hOmega i
  -- the left-hand side is the `ι'`-image of `ω′`
  have hLHS : kzOmega yv dz N i = yv * ι' (omegaPrime (Φ.map ψ) ζK i) := by
    rw [hdzdef, hNdef, hχdef]
    simp only [hρdef, kzHom_apply]
    exact kzOmega_mapMatrix_diffMatrix_inv (Φ.map ψ) hζK yv i
  rw [← hLHS, hdrive]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hAcinv, Matrix.submatrix_apply]

end KzChartSolve

/-! ### The generic-chart capstone, per disk -/

section KzAssembleGeneric

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O]
  {K : Type*} [Field K] [NeZero (2 : K)] {ψ : O →+* K}
  {f : O[X]} {a b xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ w c₁ c₂ : O[X]}
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

/-- Cancel the doubling and the coercion at the endpoint of the trace-form solve. -/
theorem eq_coe_taylor_of_two_mul_eq {K : Type*} [Field K] [NeZero (2 : K)] {A : K⟦X⟧} {a : K}
    {P : K[X]} (h : 2 * A = taylorSeriesHom a ((2 : K) • P)) :
    A = (taylor a P : K⟦X⟧) := by
  have h2K : (2 : K⟦X⟧) ≠ 0 :=
    fun h0 ↦ NeZero.ne (2 : K) (by simpa [map_ofNat] using congrArg PowerSeries.constantCoeff h0)
  refine mul_left_cancel₀ h2K ?_
  rw [h, Polynomial.smul_eq_C_mul, map_mul, taylorSeriesHom_C, taylorSeriesHom_apply,
    map_ofNat]

theorem yseries_mul_omegaPrime_eq_taylor_tracePoly_kz {hu : uτ.Monic}
    (hroot : ∀ i, (ftauUY uτ uτ.natDegree).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (haτ : ∀ i, uτ.eval (aτ i) = 0) (hbτ : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplitτ : uτ = ∏ m' : Fin uτ.natDegree, (X - C (aτ m')))
    (hunitτ : ∀ i j : Fin uτ.natDegree, i ≠ j → IsUnit (aτ i - aτ j))
    (hdF : IsFtauFoldCerts Aτ aτ bτ hu rfl hv hw hbez dF)
    {π : O} (hπ : maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hf : f.Monic) (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ)
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree)
    (hyQu : IsUnit yQ)
    (havF : IsFtauFoldAvoid Aτ aτ bτ hu rfl hv hw hbez dF)
    (havφ : IsPipelineAvoid (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d)
    (i : Fin uτ.natDegree) :
    PowerSeries.C (ψ b) * diskSeriesGeneric (f.map ψ) (ψ a)
        * omegaPrime ((ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot hcc haτ hbτ hdF hπ hπ0
          hsplitτ hunitτ).map ψ)
          (fun s ↦ PowerSeries.map ψ (phiZeta f a b xQ yQ m m₀ uτ vτ d s)) i
      = (taylor (ψ a) (tracePoly (uτ.map ψ) (c₂.map ψ)
          (Fin.cast (hu.natDegree_map ψ).symm i)) : K⟦X⟧) := by
  classical
  have hdvdτ : uτ ∣ vτ ^ 2 - f := ⟨w, hw⟩
  have hgτ : 2 * uτ.natDegree < f.natDegree := by rw [hfdeg]; lia
  set Φ := ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot hcc haτ hbτ hdF hπ hπ0
    hsplitτ hunitτ
  set ζK : Fin uτ.natDegree → K⟦X⟧ :=
    fun j ↦ PowerSeries.map ψ (phiZeta f a b xQ yQ m m₀ uτ vτ d j)
  set ι' : K⟦X⟧ →+* Kz := algebraMap (PowerSeries K) Kz with hιdef
  set ρ : O⟦X⟧ →+* Kz := kzHom (O := O) ψ with hρdef
  obtain ⟨cPτ, sPτ, hsPτ⟩ := isCoprime_ftauFoldPipe hu rfl hv hw hbez havF
  obtain ⟨cφ, sφ, hsφ⟩ := isCoprime_phiPipeline havφ
  obtain ⟨hPm, hPd, -⟩ :=
    phiPipeline_monic_dvd_degree_lt hsep hm hm₀ hb hfa h2 hyQ hu hdvdτ hcerts
  have hcc0 (j : Fin uτ.natDegree) :
      PowerSeries.constantCoeff (phiZeta f a b xQ yQ m m₀ uτ vτ d j) = 0 :=
    constantCoeff_phiZeta hf hsep hm hm₀ hb hfa h2 hyQ hu hv hdvdτ hgτ hcerts j
  -- the chart's trace identity: the numerators are the powers of `x(z) = a + z`
  have hΘ (k : Fin uτ.natDegree) : 2 * ρ (PowerSeries.C b * diskSeriesGeneric f a)
      * traceDiff (kzDerivation K)
          ((phiPipeline f a b xQ yQ m m₀ uτ vτ d).1.map ρ) (sφ.map ρ) k
      = ρ (PowerSeries.C a + PowerSeries.X) ^ (k : ℕ) :=
    two_mul_y_mul_traceDiff_phiPipeline_map hf hsep hm hm₀ hb hfa h2 hyQ hyQu hu hdvdτ
      hbez hfdeg k.isLt hcerts havφ hsφ
  have hdrive := two_mul_omegaPrime_kz_eq_sum hroot hcc haτ hbτ hsplitτ hunitτ hdF hπ hπ0 hf
    hfdeg havF hsPτ hPm hcerts.hdeg
    (ζ := fun j ↦ phiZeta f a b xQ yQ m m₀ uτ vτ d j) (fun j ↦ by rw [phiZeta]) hcc0
    (fun θ hθC hθX hθ0 k j ↦ traceMat_phiPipeline rfl θ hθC hθX hθ0 hf hsep hm hm₀ hb hfa h2
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
  have hyv : ρ (PowerSeries.C b * diskSeriesGeneric f a)
      = ι' (PowerSeries.C (ψ b) * diskSeriesGeneric (f.map ψ) (ψ a)) := by
    rw [hρdef, kzHom_apply, map_mul, PowerSeries.map_C,
      map_diskSeriesGeneric ψ f a hfa h2]
  have hRHS : (∑ j, algebraMap K Kz ((traceMatrix (uτ.map ψ) (c₂.map ψ))⁻¹
        (finCongr (hu.natDegree_map ψ).symm i) (finCongr (hu.natDegree_map ψ).symm j))
        * ρ (PowerSeries.C a + PowerSeries.X) ^ (j : ℕ))
      = ι' ((taylorSeriesHom (ψ a)) ((2 : K) • tracePoly (uτ.map ψ) (c₂.map ψ)
          (Fin.cast (hu.natDegree_map ψ).symm i))) := by
    rw [two_smul_tracePoly, map_sum, map_sum]
    refine Fintype.sum_equiv (finCongr (hu.natDegree_map ψ).symm) _ _ fun j ↦ ?_
    rw [hcast, RingHom.comp_apply, map_mul, map_mul, map_pow, taylorSeriesHom_C,
      taylorSeriesHom_X, map_pow, hρdef, kzHom_apply]
    simp only [PowerSeries.map_C, PowerSeries.map_X, map_add, finCongr_apply, Fin.val_cast]
    rfl
  have hend : ι' (2 * (PowerSeries.C (ψ b) * diskSeriesGeneric (f.map ψ) (ψ a)
        * omegaPrime (Φ.map ψ) ζK i))
      = ι' (taylorSeriesHom (ψ a) ((2 : K) • tracePoly (uτ.map ψ) (c₂.map ψ)
          (Fin.cast (hu.natDegree_map ψ).symm i))) := by
    rw [map_mul, map_ofNat, ← hRHS, ← hdrive, hyv, map_mul]
  exact eq_coe_taylor_of_two_mul_eq ((IsFractionRing.injective (PowerSeries K) Kz) hend)

/-- **The disk expansion of an integral differential is its `ω′`-combination** (the
`hW`-identification of blueprint `thm:disk-bound`): if the numerator `h₀` has coordinates
`cs` in the trace-form basis, then the integral disk expansion of `h₀·dx/y` at the generic
centre `(a, b)` is `∑_i cs_i·ω′_i` for the chart coordinates of that disk — from per-disk
hypotheses only. The coordinate identity `hmap` is disk-independent
(`ChabautyColeman.exists_annihilator_tracePoly`), so every differential of the annihilating
space is available in every generic disk. -/
theorem map_omegaExpansionGeneric_eq_sum_smul_omegaPrime {hu : uτ.Monic}
    (hroot : ∀ i, (ftauUY uτ uτ.natDegree).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (haτ : ∀ i, uτ.eval (aτ i) = 0) (hbτ : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplitτ : uτ = ∏ m' : Fin uτ.natDegree, (X - C (aτ m')))
    (hunitτ : ∀ i j : Fin uτ.natDegree, i ≠ j → IsUnit (aτ i - aτ j))
    (hdF : IsFtauFoldCerts Aτ aτ bτ hu rfl hv hw hbez dF)
    {π : O} (hπ : maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hf : f.Monic) (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ)
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree)
    (hyQu : IsUnit yQ)
    (havF : IsFtauFoldAvoid Aτ aτ bτ hu rfl hv hw hbez dF)
    (havφ : IsPipelineAvoid (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d)
    {cs : Fin uτ.natDegree → K} {h₀ : O[X]}
    (hmap : h₀.map ψ = ∑ i, cs i • tracePoly (uτ.map ψ) (c₂.map ψ)
      (Fin.cast (hu.natDegree_map ψ).symm i)) :
    PowerSeries.map ψ (omegaExpansionGeneric f h₀ a b)
      = ∑ i, cs i • omegaPrime ((ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot hcc haτ hbτ
          hdF hπ hπ0 hsplitτ hunitτ).map ψ)
          (fun s ↦ PowerSeries.map ψ (phiZeta f a b xQ yQ m m₀ uτ vτ d s)) i := by
  have hbu : IsUnit b := (isUnit_pow_iff two_ne_zero).mp (hb ▸ hfa)
  have hψb : ψ b ≠ 0 := (hbu.map ψ).ne_zero
  have hne0 : PowerSeries.C (ψ b) * diskSeriesGeneric (f.map ψ) (ψ a) ≠ 0 := fun h0 ↦
    hψb (by simpa [constantCoeff_diskSeriesGeneric] using congrArg PowerSeries.constantCoeff h0)
  refine mul_left_cancel₀ hne0 ?_
  have hbase := congrArg (PowerSeries.map ψ) (yseries_mul_omegaExpansionGeneric f h₀ (a := a) hbu)
  rw [map_mul, map_mul, PowerSeries.map_C, map_diskSeriesGeneric ψ f a hfa h2] at hbase
  rw [hbase, Finset.mul_sum]
  calc PowerSeries.map ψ (taylor a h₀ : O⟦X⟧)
      = ((taylor (ψ a) (h₀.map ψ) : K[X]) : K⟦X⟧) := by
        rw [← Polynomial.polynomial_map_coe, map_taylor]
    _ = ∑ i, cs i • ((taylor (ψ a) (tracePoly (uτ.map ψ) (c₂.map ψ)
          (Fin.cast (hu.natDegree_map ψ).symm i)) : K[X]) : K⟦X⟧) := by
        rw [hmap, map_sum, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by
          rw [map_smul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_smul]
    _ = ∑ i, PowerSeries.C (ψ b) * diskSeriesGeneric (f.map ψ) (ψ a)
          * (cs i • omegaPrime ((ftauFoldFGL hu rfl hv hw hbez hf hfdeg hroot hcc haτ hbτ
              hdF hπ hπ0 hsplitτ hunitτ).map ψ)
              (fun s ↦ PowerSeries.map ψ (phiZeta f a b xQ yQ m m₀ uτ vτ d s)) i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [mul_smul_comm, yseries_mul_omegaPrime_eq_taylor_tracePoly_kz hroot hcc haτ hbτ
          hsplitτ hunitτ hdF hπ hπ0 hf hsep hm hm₀ hb hfa h2 hyQ hfdeg hcerts hyQu havF
          havφ i]

end KzAssembleGeneric

end ChabautyColeman

end
