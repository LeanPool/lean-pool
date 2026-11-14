/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Charts.PhiChart
public import LeanPool.HyperellipticCurves.Log.Witness.DiskWitness

import LeanPool.HyperellipticCurves.ForMathlib.PowerSeries
import LeanPool.HyperellipticCurves.Series.HenselRoot

/-!
# The auxiliary point of a residue disk (`lem:global-generic`, per-disk half over `O`)

`LeanPool.HyperellipticCurves.Log.Witness.DiskWitness` produces the auxiliary point of the per-disk
configuration over an algebraically closed field. Here it is transported to the base ring: over a
complete local ring with algebraically closed residue field, a disk centre `P₀ = (a, b)` whose
`x`-coordinate is off the support of `τ` admits a point `Q = (x_Q, y_Q)` of the curve over
`O` — obtained by lifting the residue point with the smooth Hensel lemma
(`ChabautyColeman.exists_lift_curve_point`) — together with a slope certificate, such that
the *reduced* configuration `[P_bar₀ + ι Q_bar] + τ_bar + [Q_bar + ι P_bar₀]` carries a certificate
pack,
avoids the Weierstrass points at both reduced data, and is coprime to the pair block
(`ChabautyColeman.exists_auxiliary_point`).

The two outer blocks are opposite: their `v`-parts satisfy
`pairV x_Q y_Q m₀ = -(pairV a b m)` (`ChabautyColeman.pairV_neg`), which is the form in
which `LeanPool.HyperellipticCurves.Log.Witness.DiskWitness` states the configuration, and the
reason the two
blocks cancel in the class group.

The reduced pack is then lifted to the disk pipeline over `O⟦z⟧`
(`ChabautyColeman.exists_isPipelineCerts_phi`), so that
`ChabautyColeman.exists_auxiliary_point_phi` delivers a single pack `d` carrying both
`ChabautyColeman.IsPipelineCerts` at the `φ` level and `ChabautyColeman.IsPipelineAvoid`
for its reduction — the two hypotheses that
`ChabautyColeman.omegaPrime_global_of_residue` imposes on the same `d`.

The **Weierstrass** residue disks (chart coverage) have the same chain with the moving point
`P_z = (W(z), z)`, `W` the Weierstrass disk series with `f(W(z)) = z²`: the auxiliary point is
the centre `(ω, 0)` of `ChabautyColeman.exists_auxiliary_point`, whose nonsingularity input is
the disjunction "`b` a unit, or `a` a simple root of `f`"; the moving pair is
`ChabautyColeman.movingPair_dvd_weierstrass` and the pack over `O⟦z⟧` is
`ChabautyColeman.exists_auxiliary_point_phi_weierstrass`.
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped PowerSeries

namespace ChabautyColeman

section PhiLift

variable {O : Type*} [CommRing O] [IsLocalRing O] {f uτ vτ : O[X]} {a b xQ yQ m₀ : O}
  {m : O⟦X⟧} {n : ℕ}

/-- **The per-disk certificate pack lifts from the residue field to `O⟦z⟧`**: a pack for the
reduced configuration `[P_bar₀ + ι Q_bar] + τ_bar + [Q_bar + ι P_bar₀]` steers the disk pipeline of
`def:phiD`,
and the lift reduces to the given pack. -/
theorem exists_isPipelineCerts_phi (hf : f.Monic) (hu : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f)
    (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ) (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a))
    (h2 : IsUnit (2 : O)) (hyQ : yQ ^ 2 = f.eval xQ) (d' : CantorCertData (ResidueField O))
    (hd' : IsPipelineCenterCerts (f.map (residue O))
      ((diskCenterConfig a b xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O))
      d' n) :
    ∃ d : CantorCertData O⟦X⟧,
      IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d n
        ∧ d.map (seriesResidue O) = d' := by
  have hu₁ : (phiU₁ a xQ).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₃ : (phiU₃ a xQ).Monic := ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have hd₁ : phiU₁ a xQ ∣ phiV₁ f a b m ^ 2 - f.map PowerSeries.C :=
    movingPair_dvd hsep hm hb hfa h2 hyQ
  have hd₃ : phiU₃ a xQ ∣ phiV₃ xQ yQ m₀ ^ 2 - f.map PowerSeries.C :=
    map_dvd_sq_sub _ (pair_dvd (neg_sub xQ a ▸ hsep.neg) hm₀ hyQ (by rwa [neg_pow_two]))
  refine exists_isPipelineCerts_powerSeries (hf.map _) hu₁ (hu.map _) hu₃ hd₁
    (map_dvd_sq_sub _ hdvdτ) hd₃ d' ?_
  rwa [map_C_map_seriesResidue, phiConfig_map_seriesResidue]

end PhiLift

section DiskPoint

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  {f : O[X]}

variable {uτ vτ : O[X]} {a b : O}

/-- **The auxiliary point of a residue disk** (`lem:global-generic`, per-disk half, over the
base ring): for a nonsingular disk centre `P₀ = (a, b)` — `b` a unit, or `a` a simple root of
`f`, which covers the Weierstrass centres `(ω, 0)` of the chart decomposition — whose
`x`-coordinate is off the support of `τ`, there is a point `Q = (x_Q, y_Q)` of the curve over
`O`, with a slope certificate, for which the reduced configuration
`[P_bar₀ + ι Q_bar] + τ_bar + [Q_bar + ι P_bar₀]` carries a certificate pack, avoids the Weierstrass
points at
both reduced data, and satisfies the CRT input for the singular constant block: the reduced
stage-2 `u`-part is coprime to the pair block. -/
theorem exists_auxiliary_point [IsAlgClosed (ResidueField O)] [NeZero (2 : ResidueField O)]
    [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]
    (h2 : IsUnit (2 : O)) (hf : f.Monic) (hu : uτ.Monic) (hv : vτ.degree < uτ.degree)
    (hd : uτ ∣ vτ ^ 2 - f) (hgp : IsCoprime (uτ.map (residue O)) (f.map (residue O)))
    (hτa : IsUnit (uτ.eval a)) (hb : b ^ 2 = f.eval a)
    (hns : IsUnit b ∨ IsUnit (f.derivative.eval a))
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1) :
    ∃ xQ yQ m₀ : O, IsUnit (xQ - a) ∧ IsUnit yQ ∧ yQ ^ 2 = f.eval xQ
      ∧ m₀ * (a - xQ) = -b - yQ
      ∧ ∀ m : O, m * (xQ - a) = -yQ - b → ∃ d' : CantorCertData (ResidueField O),
        IsPipelineCenterCerts (f.map (residue O))
          ((diskCenterConfig a b xQ yQ m m₀ uτ vτ).map (residue O))
          d' (uτ.map (residue O)).natDegree
        ∧ IsPipelineAvoid (f.map (residue O))
          ((diskCenterConfig a b xQ yQ m m₀ uτ vτ).map (residue O)) d'
        ∧ IsCoprime (cantorStage₂ (f.map (residue O))
            ((diskCenterConfig a b xQ yQ m m₀ uτ vτ).map (residue O)) d').1
          (((X - C a) * (X - C xQ)).map (residue O)) := by
  obtain ⟨xQ', yQ', hcurve, hyQ0, hax, huxQ, hQ⟩ := exists_isPipelineCerts_disk
    (hf.map (residue O)) (hu.map (residue O))
    (by rw [eval_map_apply]; exact (hτa.map (residue O)).ne_zero)
    (by simpa using Polynomial.map_dvd (residue O) hd)
    (by rw [← map_pow, eval_map_apply, hb])
    (hns.imp (fun h ↦ (h.map (residue O)).ne_zero) fun h ↦ by
      rw [derivative_map, eval_map_apply]
      exact (h.map (residue O)).ne_zero)
    (degree_map_le.trans_lt (hv.trans_le (hu.degree_map (residue O)).ge)) hgp
    (by rw [hf.natDegree_map, hu.natDegree_map, hfdeg])
  obtain ⟨xQ, yQ, hyQ, hxr, hyr⟩ := exists_lift_curve_point (f := f) h2 hcurve hyQ0
  have hsep : IsUnit (xQ - a) := (residue_ne_zero_iff_isUnit _).mp fun hz ↦ hax (by
    rw [map_sub, sub_eq_zero, hxr] at hz
    exact hz.symm)
  have hyu : IsUnit yQ := (residue_ne_zero_iff_isUnit _).mp (by rwa [hyr])
  have hsep' : IsUnit (a - xQ) := by rw [← neg_sub]; exact hsep.neg
  have hm₀ : Ring.inverse (a - xQ) * (-b - yQ) * (a - xQ) = -b - yQ := by
    rw [mul_comm, ← mul_assoc, Ring.mul_inverse_cancel _ hsep', one_mul]
  refine ⟨xQ, yQ, Ring.inverse (a - xQ) * (-b - yQ), hsep, hyu, hyQ, hm₀, fun m hm ↦ ?_⟩
  obtain ⟨d, hd₁⟩ := hQ ((pairV a b m).map (residue O))
    (by rw [pairV_map]; exact pairV_eval_left)
    (by
      rw [pairV_map, ← hxr, ← hyr, ← map_neg]
      exact pairV_eval_right (by rw [← map_sub, ← map_mul, hm, map_sub, map_neg]))
  have hv₃ : (pairV xQ yQ (Ring.inverse (a - xQ) * (-b - yQ))).map (residue O)
      = -((pairV a b m).map (residue O)) := by
    rw [pairV_neg (neg_slope_eq hsep hm hm₀) hm, Polynomial.map_neg]
  have hcfg : (diskCenterConfig a b xQ yQ m (Ring.inverse (a - xQ) * (-b - yQ)) uτ vτ).map
        (residue O)
      = pencilConfig (residue O a) xQ' ((pairV a b m).map (residue O)) (uτ.map (residue O))
        (vτ.map (residue O)) := by
    simp only [PipelineData.map, diskCenterConfig, pencilConfig, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hv₃, hxr]
  refine ⟨d, ?_⟩
  rwa [hcfg, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_C, hxr]

/-- **The auxiliary point of a residue disk, with its certificate pack over `O⟦z⟧`.** Unlike in
`ChabautyColeman.exists_auxiliary_point`, the slope certificate is the one of the *moving* disk
point `P_z = (a + z, b·η(z))`, and the pack `d` steering the disk pipeline is the same one whose
reduction avoids the Weierstrass points — the two conditions that
`ChabautyColeman.omegaPrime_global_of_residue` imposes on a single `d`. -/
theorem exists_auxiliary_point_phi [IsAlgClosed (ResidueField O)] [NeZero (2 : ResidueField O)]
    [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]
    (h2 : IsUnit (2 : O)) (hf : f.Monic) (hu : uτ.Monic) (hv : vτ.degree < uτ.degree)
    (hd : uτ ∣ vτ ^ 2 - f) (hgp : IsCoprime (uτ.map (residue O)) (f.map (residue O)))
    (hτa : IsUnit (uτ.eval a)) (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a))
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1) :
    ∃ xQ yQ m₀ : O, IsUnit (xQ - a) ∧ IsUnit yQ ∧ yQ ^ 2 = f.eval xQ
      ∧ m₀ * (a - xQ) = -b - yQ
      ∧ ∀ m : O⟦X⟧, m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
            = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a →
          ∃ d : CantorCertData O⟦X⟧,
            IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
                uτ.natDegree
              ∧ IsPipelineAvoid (f.map (residue O))
                ((diskCenterConfig a b xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map
                  (residue O)) (d.map (seriesResidue O))
              ∧ IsPipelineCenterCerts (f.map (residue O))
                ((diskCenterConfig a b xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map
                  (residue O)) (d.map (seriesResidue O))
                (uτ.map (residue O)).natDegree := by
  obtain ⟨xQ, yQ, m₀, hsep, hyu, hyQ, hm₀, hQ⟩ :=
    exists_auxiliary_point h2 hf hu hv hd hgp hτa hb (.inl (isUnit_b hb hfa)) hfdeg
  refine ⟨xQ, yQ, m₀, hsep, hyu, hyQ, hm₀, fun m hm ↦ ?_⟩
  obtain ⟨d', hcerts', havr', -⟩ := hQ (PowerSeries.constantCoeff m) (by
    have h := congrArg (PowerSeries.constantCoeff (R := O)) hm
    simpa [constantCoeff_diskSeriesGeneric] using h)
  obtain ⟨d, hcerts, hmap⟩ := exists_isPipelineCerts_phi hf hu hd hsep hm hm₀ hb hfa h2 hyQ d'
    (by rwa [hu.natDegree_map] at hcerts')
  exact ⟨d, hcerts, hmap ▸ havr', hmap ▸ hcerts'⟩

end DiskPoint

section MovingPairWeierstrass

variable {O : Type*} [CommRing O] {f : O[X]} {ω xQ yQ : O} {m : O⟦X⟧}

/-- **The Weierstrass moving pair lies on the curve**: the line through the moving disk
point `P_z = (W(z), z)` — with `W` the Weierstrass disk series, `f(W(z)) = z²` — and the
constant point `(x_Q, -y_Q)`, with slope certificate `m`, is a square root of `f` modulo
`(X - W(z))·(X - x_Q)` over `O⟦z⟧`. -/
theorem movingPair_dvd_weierstrass (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hyQ : yQ ^ 2 = f.eval xQ) :
    (X - Polynomial.C (weierstrassSeries hf hdeg hω hωu)) * (X - Polynomial.C (PowerSeries.C xQ))
      ∣ pairV (weierstrassSeries hf hdeg hω hωu) PowerSeries.X m ^ 2
          - f.map (PowerSeries.C : O →+* O⟦X⟧) := by
  refine pair_dvd ?_ hm ?_ ?_
  · rw [PowerSeries.isUnit_iff_constantCoeff, map_sub, PowerSeries.constantCoeff_C,
      constantCoeff_weierstrassSeries]
    exact hsep
  · rw [eval_map, ← PowerSeries.algebraMap_eq, ← aeval_def, weierstrassSeries_eval]
  · rw [← map_pow, neg_pow_two, hyQ, eval_map_apply]

end MovingPairWeierstrass

section PhiLiftWeierstrass

variable {O : Type*} [CommRing O] [IsLocalRing O] {f uτ vτ : O[X]} {ω xQ yQ m₀ : O}
  {m : O⟦X⟧} {n : ℕ}

/-- **The Weierstrass-disk certificate pack lifts from the residue field to `O⟦z⟧`**: a
validity pack for the reduced configuration `[P_bar₀ + ι Q_bar] + τ_bar + [Q_bar + ι P_bar₀]` at the
Weierstrass centre `P_bar₀ = (ω_bar, 0)` steers the Weierstrass disk pipeline — the moving point is
`(W(z), z)` — and the lift reduces to the given pack. -/
theorem exists_isPipelineCerts_phi_weierstrass (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hu : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ) (hyQ : yQ ^ 2 = f.eval xQ)
    (d' : CantorCertData (ResidueField O))
    (hd' : IsPipelineCenterCerts (f.map (residue O))
      ((diskCenterConfig ω 0 xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O)) d' n) :
    ∃ d : CantorCertData O⟦X⟧,
      IsPipelineCerts (f.map PowerSeries.C)
          (diskConfig ((X - C (weierstrassSeries hf hdeg hω hωu)) * (X - C (PowerSeries.C xQ)))
            (pairV (weierstrassSeries hf hdeg hω hωu) PowerSeries.X m) ω xQ yQ m₀ uτ vτ) d n
        ∧ d.map (seriesResidue O) = d' := by
  have hu₃ : (phiU₃ ω xQ).Monic := ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have hd₁ := movingPair_dvd_weierstrass hf hdeg hω hωu hsep hm hyQ
  have hd₃ : phiU₃ ω xQ ∣ phiV₃ xQ yQ m₀ ^ 2 - f.map PowerSeries.C :=
    map_dvd_sq_sub _ (pair_dvd (neg_sub xQ ω ▸ hsep.neg) hm₀ hyQ
      (by rw [neg_zero, zero_pow two_ne_zero]; exact hω.symm))
  refine exists_isPipelineCerts_powerSeries (hf.map _)
    ((monic_X_sub_C _).mul (monic_X_sub_C _)) (hu.map _) hu₃ hd₁
    (map_dvd_sq_sub _ hdvdτ) hd₃ d' ?_
  have hres : seriesResidue O (weierstrassSeries hf hdeg hω hωu) = residue O ω := by
    rw [seriesResidue_apply, constantCoeff_weierstrassSeries]
  have hU₁ : ((X - C (weierstrassSeries hf hdeg hω hωu))
        * (X - C (PowerSeries.C xQ))).map (seriesResidue O)
      = ((X - C ω) * (X - C xQ)).map (residue O) := by
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, map_C, hres,
      seriesResidue_C]
  have hV₁ : (pairV (weierstrassSeries hf hdeg hω hωu) PowerSeries.X m).map (seriesResidue O)
      = (pairV ω 0 (PowerSeries.constantCoeff m)).map (residue O) := by
    rw [pairV_map, pairV_map, hres, seriesResidue_X, seriesResidue_apply, map_zero]
  have hcfg : (diskConfig ((X - C (weierstrassSeries hf hdeg hω hωu)) * (X - C (PowerSeries.C xQ)))
        (pairV (weierstrassSeries hf hdeg hω hωu) PowerSeries.X m) ω xQ yQ m₀ uτ vτ).map
        (seriesResidue O)
      = (diskCenterConfig ω 0 xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O) := by
    simp only [PipelineData.map, diskConfig, diskCenterConfig, hU₁, hV₁,
      map_C_map_seriesResidue, phiU₃, phiV₃]
  rwa [map_C_map_seriesResidue, hcfg]

end PhiLiftWeierstrass

section DiskPointPhiWeierstrass

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  {f uτ vτ : O[X]} {ω : O}

/-- **The auxiliary point of a Weierstrass residue disk, with the pack over `O⟦z⟧`**: one
certificate pack `d` steers the Weierstrass disk pipeline, and its reduction is a validity
pack for the reduced configuration that moreover avoids the Weierstrass points at both
reduced data and satisfies the CRT coprimality for the singular constant block — the three
residue-field genericity inputs of the `(ω, 0)`-centred clause (c). -/
theorem exists_auxiliary_point_phi_weierstrass [IsAlgClosed (ResidueField O)]
    [NeZero (2 : ResidueField O)] [Fact (Odd (f.map (residue O)).natDegree)]
    [Fact (Squarefree (f.map (residue O)))]
    (h2 : IsUnit (2 : O)) (hf : f.Monic) (hdeg : 0 < f.natDegree) (hu : uτ.Monic)
    (hv : vτ.degree < uτ.degree) (hd : uτ ∣ vτ ^ 2 - f)
    (hgp : IsCoprime (uτ.map (residue O)) (f.map (residue O)))
    (hτa : IsUnit (uτ.eval ω)) (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω))
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1) :
    ∃ xQ yQ m₀ : O, IsUnit (xQ - ω) ∧ IsUnit yQ ∧ yQ ^ 2 = f.eval xQ
      ∧ m₀ * (ω - xQ) = -0 - yQ
      ∧ ∀ m : O⟦X⟧, m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
            = PowerSeries.C (-yQ) - PowerSeries.X →
          ∃ d : CantorCertData O⟦X⟧,
            IsPipelineCerts (f.map PowerSeries.C)
              (diskConfig ((X - C (weierstrassSeries hf hdeg hω hωu)) * (X - C (PowerSeries.C xQ)))
                (pairV (weierstrassSeries hf hdeg hω hωu) PowerSeries.X m) ω xQ yQ m₀ uτ vτ) d
              uτ.natDegree
            ∧ IsPipelineAvoid (f.map (residue O))
              ((diskCenterConfig ω 0 xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O))
                (d.map (seriesResidue O))
            ∧ IsCoprime (cantorStage₂ (f.map (residue O))
                ((diskCenterConfig ω 0 xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map
                  (residue O)) (d.map (seriesResidue O))).1
              (((X - C ω) * (X - C xQ)).map (residue O)) := by
  obtain ⟨xQ, yQ, m₀, hsep, hyu, hyQ, hm₀, hQ⟩ :=
    exists_auxiliary_point (b := 0) h2 hf hu hv hd hgp hτa (by simp [hω]) (.inr hωu) hfdeg
  refine ⟨xQ, yQ, m₀, hsep, hyu, hyQ, hm₀, fun m hm ↦ ?_⟩
  obtain ⟨d', hcerts', havr', hcop₃'⟩ := hQ (PowerSeries.constantCoeff m) (by
    have h := congrArg (PowerSeries.constantCoeff (R := O)) hm
    simpa [constantCoeff_weierstrassSeries] using h)
  obtain ⟨d, hcerts, hmap⟩ := exists_isPipelineCerts_phi_weierstrass hf hdeg hu hd hω hωu hsep
    hm hm₀ hyQ d' (by rwa [hu.natDegree_map] at hcerts')
  exact ⟨d, hcerts, hmap ▸ havr', hmap ▸ hcop₃'⟩

end DiskPointPhiWeierstrass

section Suppliers

variable {O : Type*} [CommRing O]

/-- The slope series of a generic residue disk exists: the moving denominator has unit
constant coefficient `x_Q - a`. -/
theorem exists_slope_series_generic {f : O[X]} {a xQ b yQ : O} (hsep : IsUnit (xQ - a)) :
    ∃ m : O⟦X⟧, m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a := by
  refine PowerSeries.exists_mul_eq_of_constantCoeff_isUnit ?_ _
  simpa using hsep

/-- The slope series at a Weierstrass centre exists: the moving denominator has unit
constant coefficient `x_Q - ω`. -/
theorem exists_slope_series_weierstrass {f : O[X]} {ω xQ yQ : O} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω))
    (hsep : IsUnit (xQ - ω)) :
    ∃ m : O⟦X⟧, m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X := by
  refine PowerSeries.exists_mul_eq_of_constantCoeff_isUnit ?_ _
  simpa [constantCoeff_weierstrassSeries] using hsep

/-- An element whose residue evaluation is nonzero evaluates to a unit — lifts the
`T`-avoidance of the `τ`-datum to the `hτa` inputs of the auxiliary-point lemmas. -/
theorem isUnit_eval_of_map_residue_ne_zero [IsLocalRing O] {u : O[X]} {a : O}
    (h : (u.map (residue O)).eval (residue O a) ≠ 0) : IsUnit (u.eval a) :=
  (residue_ne_zero_iff_isUnit _).mp fun hm ↦ h (by rwa [eval_map_apply])

end Suppliers


end ChabautyColeman

end
