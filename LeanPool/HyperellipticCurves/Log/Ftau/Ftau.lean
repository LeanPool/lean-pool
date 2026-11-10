/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Cantor.CantorPipeline
public import LeanPool.HyperellipticCurves.Log.Ftau.Chart
public import Mathlib.RingTheory.MvPowerSeries.Rename

import LeanPool.HyperellipticCurves.ForMathlib.Polynomial
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# The chart data for the translated group law (blueprint `def:Ftau`)

The raw material of `F_τ(X, Y)` — the chart coordinates of `ch(X) + ch(Y) - τ` — over
`R := MvPowerSeries (Fin n ⊕ Fin n) O`: the two chart data
(`LeanPool.HyperellipticCurves.Log.Ftau.Chart`)
transported along the `Sum.inl`/`Sum.inr` variable renames
(`ChabautyColeman.ftauUX`/`ftauVX`, `ftauUY`/`ftauVY`), with their basic properties
(monicity, cofactor divisibility, coprimality of the `u`-parts, center specialization:
at `X = Y = 0` they collapse to the `τ`-datum itself, `ftauUX_map_constantCoeff`, …),
and the certificate container `ChabautyColeman.CantorCertData`.

The translated law itself is realized by the point-by-point **fold**
(`LeanPool.HyperellipticCurves.Log.Fold.FtauFold`,
`LeanPool.HyperellipticCurves.Log.Fold.FtauFoldBasic`), which
consumes the transported chart data from here; the certificate container steers the three-block
Cantor pipeline of the disk charts (`LeanPool.HyperellipticCurves.Log.Cantor.PipelineCerts`).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Ftau

variable {O : Type*} [CommRing O] {n : ℕ} {f u v w c₁ c₂ : O[X]}

/-- The `X`-side chart `u`-polynomial over the doubled power series ring. -/
noncomputable def ftauUX (u : O[X]) (n : ℕ) :
    Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O) :=
  (chartU u n).map (MvPowerSeries.rename (Sum.inl : Fin n → Fin n ⊕ Fin n)).toRingHom

/-- The `Y`-side chart `u`-polynomial over the doubled power series ring. -/
noncomputable def ftauUY (u : O[X]) (n : ℕ) :
    Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O) :=
  (chartU u n).map (MvPowerSeries.rename (Sum.inr : Fin n → Fin n ⊕ Fin n)).toRingHom

theorem rename_comp_C {σ σ' : Type*} (e : σ → σ') [Filter.TendstoCofinite e] :
    (MvPowerSeries.rename (R := O) e).toRingHom.comp MvPowerSeries.C
      = MvPowerSeries.C :=
  RingHom.ext fun a ↦ MvPowerSeries.rename_C e a

/-- Power series with zero constant coefficient lie in the Jacobson radical: adding `1` to
any multiple of one gives a unit. -/
theorem ker_constantCoeff_le_jacobson {σ : Type*} :
    RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries σ O →+* O) ≤ Ideal.jacobson ⊥ :=
  fun g hg ↦ Ideal.mem_jacobson_bot.mpr fun y ↦
    MvPowerSeries.isUnit_iff_constantCoeff.mpr (by simp [RingHom.mem_ker.mp hg])

variable [Nontrivial O]

/-- **Weierstrass avoidance for a chart datum**: the centre datum's Bézout certificate lifts
to the chart datum. The chart data reduce to `(u, v)` under `MvPowerSeries.constantCoeff`,
whose kernel lies in the Jacobson radical, so the relation lifts by Nakayama
(`ChabautyColeman.exists_bezout_lift_map`) — no genericity beyond the centre's own
certificate. -/
theorem isCoprime_chartU (hu : u.Monic) (hn : n ≤ u.natDegree) (hv : v.degree < u.degree)
    (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1) :
    IsCoprime (chartU u n) (2 * chartV hu hn hv hw hbez) := by
  obtain ⟨s₁, s₂, s₃, hs, -, -, -⟩ := exists_bezout_lift_map
    (φ := (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) O →+* O))
    (fun r ↦ ⟨MvPowerSeries.C r, by simp⟩) ker_constantCoeff_le_jacobson (chartU_monic hu hn)
    (g := 2 * chartV hu hn hv hw hbez) (h := 0) (a := c₁) (b := c₂) (c := 0) (by
      rw [chartU_map_constantCoeff, Polynomial.map_mul, Polynomial.map_ofNat,
        chartV_map_constantCoeff, Polynomial.map_zero, mul_zero, add_zero]
      exact hbez)
  rw [mul_zero, add_zero] at hs
  exact ⟨s₁, s₂, hs⟩

variable (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)

/-- The `X`-side chart square root over the doubled power series ring. -/
noncomputable def ftauVX : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O) :=
  (chartV hu hne.ge hv hw hbez).map
    (MvPowerSeries.rename (Sum.inl : Fin n → Fin n ⊕ Fin n)).toRingHom

/-- The `Y`-side chart square root over the doubled power series ring. -/
noncomputable def ftauVY : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O) :=
  (chartV hu hne.ge hv hw hbez).map
    (MvPowerSeries.rename (Sum.inr : Fin n → Fin n ⊕ Fin n)).toRingHom

section Transport

variable (e : Fin n → Fin n ⊕ Fin n) [Filter.TendstoCofinite e]

theorem chartU_map_rename_monic (hu : u.Monic) (hn : n ≤ u.natDegree) :
    ((chartU u n).map (MvPowerSeries.rename (R := O) e).toRingHom).Monic :=
  (chartU_monic hu hn).map _

theorem chartU_map_rename_natDegree (hu : u.Monic) (hn : n ≤ u.natDegree) :
    ((chartU u n).map (MvPowerSeries.rename (R := O) e).toRingHom).natDegree
      = u.natDegree := by
  rw [(chartU_monic hu hn).natDegree_map]
  exact natDegree_eq_of_degree_eq (chartU_degree hu hn)

theorem chartV_map_rename_dvd :
    (chartU u n).map (MvPowerSeries.rename (R := O) e).toRingHom
      ∣ ((chartV hu hne.ge hv hw hbez).map (MvPowerSeries.rename (R := O) e).toRingHom) ^ 2
        - f.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O) :=
  chartU_map_dvd_chartV_map_sq_sub hu hne.ge hv hw hbez (rename_comp_C e)

/-- Weierstrass avoidance is inherited by a transported chart datum: a variable rename is a
ring homomorphism, so it carries the chart datum's Bézout certificate along. -/
theorem isCoprime_chartU_map_rename :
    IsCoprime ((chartU u n).map (MvPowerSeries.rename (R := O) e).toRingHom)
      (2 * (chartV hu hne.ge hv hw hbez).map
        (MvPowerSeries.rename (R := O) e).toRingHom) := by
  have h := (isCoprime_chartU hu hne.ge hv hw hbez).map
    (Polynomial.mapRingHom (MvPowerSeries.rename (R := O) e).toRingHom)
  simpa only [coe_mapRingHom, Polynomial.map_mul, Polynomial.map_ofNat] using h

end Transport

/-- The raw certificate data of a compose–reduce–compose–reduce Cantor pipeline: two Bézout
triples for the compositions and two leading-coefficient inverses for the reductions. -/
structure CantorCertData (S : Type*) [CommRing S] where
  /-- First Bézout certificate, first component. -/
  s₁ : Polynomial S
  /-- First Bézout certificate, second component. -/
  s₂ : Polynomial S
  /-- First Bézout certificate, third component. -/
  s₃ : Polynomial S
  /-- Leading-coefficient inverse certificate of the first reduction. -/
  c₁ : S
  /-- Second Bézout certificate, first component. -/
  t₁ : Polynomial S
  /-- Second Bézout certificate, second component. -/
  t₂ : Polynomial S
  /-- Second Bézout certificate, third component. -/
  t₃ : Polynomial S
  /-- Leading-coefficient inverse certificate of the second reduction. -/
  c₂ : S

end Ftau

section Center

variable {O : Type*} [CommRing O] {n : ℕ} {f u v w c₁ c₂ : O[X]}

/-- `constantCoeff` undoes any rename. -/
theorem constantCoeff_comp_rename {σ σ' : Type*} (e : σ → σ') [Filter.TendstoCofinite e] :
    (MvPowerSeries.constantCoeff : MvPowerSeries σ' O →+* O).comp
      (MvPowerSeries.rename (R := O) e).toRingHom
      = (MvPowerSeries.constantCoeff : MvPowerSeries σ O →+* O) :=
  RingHom.ext fun p ↦ MvPowerSeries.constantCoeff_rename e p

/-- The center of the transported chart `u`-polynomial is `u`. -/
theorem ftauUX_map_constantCoeff :
    (ftauUX u n).map (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n ⊕ Fin n) O →+* O)
      = u := by
  rw [ftauUX, Polynomial.map_map, constantCoeff_comp_rename, chartU_map_constantCoeff]

theorem ftauUY_map_constantCoeff :
    (ftauUY u n).map (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n ⊕ Fin n) O →+* O)
      = u := by
  rw [ftauUY, Polynomial.map_map, constantCoeff_comp_rename, chartU_map_constantCoeff]

variable [Nontrivial O] (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)

/-- The center of the transported chart square root is `v`. -/
theorem ftauVX_map_constantCoeff :
    (ftauVX hu hne hv hw hbez).map
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n ⊕ Fin n) O →+* O) = v := by
  rw [ftauVX, Polynomial.map_map, constantCoeff_comp_rename, chartV_map_constantCoeff]

theorem ftauVY_map_constantCoeff :
    (ftauVY hu hne hv hw hbez).map
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n ⊕ Fin n) O →+* O) = v := by
  rw [ftauVY, Polynomial.map_map, constantCoeff_comp_rename, chartV_map_constantCoeff]

end Center

section CenterStages

variable {O : Type*} [CommRing O] {n : ℕ} {f u v w c₁ c₂ : O[X]}

/-- The center of `f` over the doubled power series ring is `f`. -/
theorem map_C_map_constantCoeff {σ : Type*} (g : O[X]) :
    (g.map (MvPowerSeries.C : O →+* MvPowerSeries σ O)).map
      (MvPowerSeries.constantCoeff : MvPowerSeries σ O →+* O) = g := by
  rw [Polynomial.map_map, MvPowerSeries.constantCoeff_comp_C, Polynomial.map_id]

end CenterStages

end ChabautyColeman

end
