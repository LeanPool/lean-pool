/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.ScalarChainRule
public import LeanPool.CIVAxisymmetric.Zoom.PotentialVorticityRescaled
public import LeanPool.CIVAxisymmetric.Identities.PotentialVorticityEquation

/-!
# The rescaled potential vorticity equation

`eq:aniso:zoom:finite:equation` is the equation satisfied by the rescaled potential
vorticity `Ω_n = zoomOmega = lam³ δ Ω` of `eq:aniso:zoom:fields` in the zoomed variables
`((R, Z), τ)` of `eq:aniso:zoom:finite:variables`, with `δ = lam ^ (2h)` and
`μ = lam ^ (1 - 2h)`, so that `δ μ = lam`.

It is `lam⁵ δ` times the potential vorticity equation `eq:aniso:q` of
`CIV.potential_vorticity_pde`, evaluated at the zoom point. Term by term, using the chain
rules `∂_R = lam ∂_r`, `∂_Z = μ ∂_z`, `∂_τ = lam² ∂_t` of `CIV.Zoom.ScalarChainRule`:

* `∂_τ Ω_n = lam² · lam³δ ∂_tΩ = lam⁵δ ∂_tΩ`;
* `V_n ∂_R Ω_n = (lam u_r)(lam · lam³δ ∂_rΩ) = lam⁵δ u_r ∂_rΩ`;
* `W_n ∂_Z Ω_n = (lam δ u_z)(μ lam³δ ∂_zΩ) = lam⁴δ²μ u_z ∂_zΩ = lam⁵δ u_z ∂_zΩ`;
* `∂_RR Ω_n = lam² lam³δ ∂_rrΩ = lam⁵δ ∂_rrΩ` and `(3/R) ∂_R Ω_n = lam⁵δ (3/r) ∂_rΩ`,
  the second because the zoomed radius satisfies `r = lam R`;
* `δ² ∂_ZZ Ω_n = δ²μ² lam³δ ∂_zzΩ = lam⁵δ ∂_zzΩ`;
* `∂_Z (S_n²/R²) = lam⁵δ ∂_z (u_θ²/r²)`, since `S_n²/R² = lam⁴δ² (u_θ²/r²) ∘ zoomPoint`;
* the force term is `lam⁵δ` times the potential vorticity of `f`.

Away from the axis `Ω = ω_θ / r` is the smooth quotient of the smooth azimuthal vorticity
by the radius, so every chain rule is applied on the *open off-axis part*
`D = {z ∈ unitCylinder | z₁ ≠ 0}` of the cylinder rather than on `unitCylinder` itself:
`Ω` is merely continuous across the axis.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The rescaled potential vorticity equation `eq:aniso:zoom:finite:equation`: at a zoomed
point off the axis whose image lies in the unit cylinder, the rescaled potential vorticity
`Ω_n` of a classical, forced, axisymmetric solution is transported by `(V_n, W_n)` against
the anisotropic diffusion `∂_RR + 3R⁻¹∂_R + δ²∂_ZZ`, the rescaled swirl source
`∂_Z (S_n²/R²)` and `lam⁵δ` times the potential vorticity of the force. It is `lam⁵δ`
times `CIV.potential_vorticity_pde` at the zoom point. -/
theorem zoomOmega_pde (lam h zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (pres : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u pres f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) (hr : p.1.1 ≠ 0) :
    dtPast (zoomOmega lam h zc u) p
        + zoomV lam h zc u p * dr (zoomOmega lam h zc u) p
        + zoomW lam h zc u p * dz (zoomOmega lam h zc u) p
      = dr (dr (zoomOmega lam h zc u)) p
        + 3 / p.1.1 * dr (zoomOmega lam h zc u) p
        + (lam ^ (2 * h)) ^ 2 * dz (dz (zoomOmega lam h zc u)) p
        + dz (fun q => zoomS lam h zc u q ^ 2 / q.1.1 ^ 2) p
        + lam ^ 5 * lam ^ (2 * h) * potentialVorticity f (zoomPoint lam h zc p) := by
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have hZ0 : (zoomPoint lam h zc p).1 0 = lam * p.1.1 := by simp [zoomPoint, meridional]
  have hZ0ne : (zoomPoint lam h zc p).1 0 ≠ 0 := by
    rw [hZ0]
    exact mul_ne_zero hlam_ne hr
  have hplane : (zoomPoint lam h zc p).1 1 = 0 := by simp [zoomPoint, meridional]
  have hdm : lam ^ (2 * h) * lam ^ (1 - 2 * h) = lam := by
    rw [← Real.rpow_add hlam]
    have hexp : 2 * h + (1 - 2 * h) = (1 : ℝ) := by ring
    rw [hexp, Real.rpow_one]
  -- the off-axis part of the cylinder, where `Ω` is the smooth quotient `ω_θ / r`
  set D : Set (Vec3 × ℝ) := {z : Vec3 × ℝ | z ∈ unitCylinder ∧ z.1 0 ≠ 0} with hD_def
  have hDopen : IsOpen D := by
    have hcont : Continuous (fun z : Vec3 × ℝ => z.1 0) := (continuous_apply 0).comp continuous_fst
    exact isOpen_unitCylinder_prod.inter (isOpen_ne.preimage hcont)
  have hsub : D ⊆ unitCylinder := fun z hz => hz.1
  have hZD : zoomPoint lam h zc p ∈ D := ⟨hp, hZ0ne⟩
  -- smoothness of the fields entering the equation
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  have huD : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) D := hu.mono hsub
  have hrad : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => z.1 0) D :=
    ((contDiff_apply ℝ ℝ (0 : Fin 3)).comp contDiff_fst).contDiffOn
  have hazi : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => azimuthalVorticity u z) D :=
    (contDiffOn_azimuthalVorticity hu).mono hsub
  have hOmegaTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => potentialVorticity u z) D :=
    (hazi.div hrad fun z hz => hz.2).congr fun z hz => potentialVorticity_eq_div u hz.2
  have hOmega2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => potentialVorticity u z) D :=
    hOmegaTop.of_le (by norm_num)
  have hOmega1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => potentialVorticity u z) D :=
    hOmega2.of_le (by norm_num)
  have hpar0 : ContDiffOn ℝ 1
      (fun z : Vec3 × ℝ => spatialPartial (potentialVorticity u) 0 z) D :=
    contDiffOn_spatialPartial_of_isOpen hDopen hOmega2 0
  have hpar2 : ContDiffOn ℝ 1
      (fun z : Vec3 × ℝ => spatialPartial (potentialVorticity u) 2 z) D :=
    contDiffOn_spatialPartial_of_isOpen hDopen hOmega2 2
  have hswirlSmooth : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z 1 ^ 2 / z.1 0 ^ 2) D := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z 1) D := contDiffOn_pi.1 huD 1
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z 1 ^ 2) D := h1.pow 2
    have h3 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => z.1 0 ^ 2) D := hrad.pow 2
    exact (h2.div h3 fun z hz => pow_ne_zero 2 hz.2).of_le (by norm_num)
  -- the chain rules for the rescaled potential vorticity
  have hdt : dtPast (zoomOmega lam h zc u) p
      = lam ^ 3 * lam ^ (2 * h) *
        (lam ^ 2 * timePartial (potentialVorticity u) (zoomPoint lam h zc p)) :=
    ((hasDerivAt_zoomScalar_t (Phi := potentialVorticity u) lam h zc hDopen hOmega1 p
      hZD).const_mul (lam ^ 3 * lam ^ (2 * h))).hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Iic p.2)
  have hdr : dr (zoomOmega lam h zc u) p
      = lam ^ 3 * lam ^ (2 * h) *
        (lam * spatialPartial (potentialVorticity u) 0 (zoomPoint lam h zc p)) :=
    ((hasDerivAt_zoomScalar_r (Phi := potentialVorticity u) lam h zc hDopen hOmega1 p
      hZD).const_mul (lam ^ 3 * lam ^ (2 * h))).deriv
  have hdz : dz (zoomOmega lam h zc u) p
      = lam ^ 3 * lam ^ (2 * h) *
        (lam ^ (1 - 2 * h) *
          spatialPartial (potentialVorticity u) 2 (zoomPoint lam h zc p)) :=
    ((hasDerivAt_zoomScalar_z (Phi := potentialVorticity u) lam h zc hDopen hOmega1 p
      hZD).const_mul (lam ^ 3 * lam ^ (2 * h))).deriv
  have hslice_r : p.1.1 ∈ {r : ℝ | zoomPoint lam h zc ((r, p.1.2), p.2) ∈ D} := by
    simpa using hZD
  have hslice_z : p.1.2 ∈ {s : ℝ | zoomPoint lam h zc ((p.1.1, s), p.2) ∈ D} := by
    simpa using hZD
  have hdrr : dr (dr (zoomOmega lam h zc u)) p
      = lam ^ 3 * lam ^ (2 * h) *
        (lam * (lam * spatialSecondPartial (potentialVorticity u) 0 0
          (zoomPoint lam h zc p))) := by
    have hev : (fun r : ℝ => dr (zoomOmega lam h zc u) ((r, p.1.2), p.2))
        =ᶠ[𝓝 p.1.1]
        fun r : ℝ => lam ^ 3 * lam ^ (2 * h) *
          (lam * spatialPartial (potentialVorticity u) 0
            (zoomPoint lam h zc ((r, p.1.2), p.2))) := by
      filter_upwards [(isOpen_zoomSlice_r lam h zc hDopen p).mem_nhds hslice_r] with r hrmem
      exact ((hasDerivAt_zoomScalar_r (Phi := potentialVorticity u) lam h zc hDopen hOmega1
        ((r, p.1.2), p.2) hrmem).const_mul (lam ^ 3 * lam ^ (2 * h))).deriv
    have hrhs : HasDerivAt
        (fun r : ℝ => lam ^ 3 * lam ^ (2 * h) *
          (lam * spatialPartial (potentialVorticity u) 0
            (zoomPoint lam h zc ((r, p.1.2), p.2))))
        (lam ^ 3 * lam ^ (2 * h) *
          (lam * (lam * spatialSecondPartial (potentialVorticity u) 0 0
            (zoomPoint lam h zc p)))) p.1.1 :=
      ((hasDerivAt_zoomScalar_r
        (Phi := fun w : ParabolicPoint => spatialPartial (potentialVorticity u) 0 w)
        lam h zc hDopen hpar0 p hZD).const_mul lam).const_mul (lam ^ 3 * lam ^ (2 * h))
    rw [dr]
    exact (hrhs.congr_of_eventuallyEq hev).deriv
  have hdzz : dz (dz (zoomOmega lam h zc u)) p
      = lam ^ 3 * lam ^ (2 * h) *
        (lam ^ (1 - 2 * h) * (lam ^ (1 - 2 * h) *
          spatialSecondPartial (potentialVorticity u) 2 2 (zoomPoint lam h zc p))) := by
    have hev : (fun s : ℝ => dz (zoomOmega lam h zc u) ((p.1.1, s), p.2))
        =ᶠ[𝓝 p.1.2]
        fun s : ℝ => lam ^ 3 * lam ^ (2 * h) *
          (lam ^ (1 - 2 * h) * spatialPartial (potentialVorticity u) 2
            (zoomPoint lam h zc ((p.1.1, s), p.2))) := by
      filter_upwards [(isOpen_zoomSlice_z lam h zc hDopen p).mem_nhds hslice_z] with s hsmem
      exact ((hasDerivAt_zoomScalar_z (Phi := potentialVorticity u) lam h zc hDopen hOmega1
        ((p.1.1, s), p.2) hsmem).const_mul (lam ^ 3 * lam ^ (2 * h))).deriv
    have hrhs : HasDerivAt
        (fun s : ℝ => lam ^ 3 * lam ^ (2 * h) *
          (lam ^ (1 - 2 * h) * spatialPartial (potentialVorticity u) 2
            (zoomPoint lam h zc ((p.1.1, s), p.2))))
        (lam ^ 3 * lam ^ (2 * h) *
          (lam ^ (1 - 2 * h) * (lam ^ (1 - 2 * h) *
            spatialSecondPartial (potentialVorticity u) 2 2
              (zoomPoint lam h zc p)))) p.1.2 :=
      ((hasDerivAt_zoomScalar_z
        (Phi := fun w : ParabolicPoint => spatialPartial (potentialVorticity u) 2 w)
        lam h zc hDopen hpar2 p hZD).const_mul (lam ^ (1 - 2 * h))).const_mul
        (lam ^ 3 * lam ^ (2 * h))
    rw [dz]
    exact (hrhs.congr_of_eventuallyEq hev).deriv
  -- the swirl source term
  have hswirlFun : (fun q : (ℝ × ℝ) × ℝ => zoomS lam h zc u q ^ 2 / q.1.1 ^ 2)
      = fun q : (ℝ × ℝ) × ℝ => lam ^ 4 * (lam ^ (2 * h)) ^ 2 *
          (u (zoomPoint lam h zc q) 1 ^ 2 / (zoomPoint lam h zc q).1 0 ^ 2) := by
    funext q
    have hq0 : (zoomPoint lam h zc q).1 0 = lam * q.1.1 := by simp [zoomPoint, meridional]
    rw [hq0]
    show (lam * lam ^ (2 * h) * u (zoomPoint lam h zc q) 1) ^ 2 / q.1.1 ^ 2 = _
    rcases eq_or_ne q.1.1 0 with hq | hq
    · rw [hq]
      simp
    · field_simp
  have hswirl : dz (fun q : (ℝ × ℝ) × ℝ => zoomS lam h zc u q ^ 2 / q.1.1 ^ 2) p
      = lam ^ 4 * (lam ^ (2 * h)) ^ 2 *
        (lam ^ (1 - 2 * h) *
          spatialPartial (fun w : ParabolicPoint => u w 1 ^ 2 / w.1 0 ^ 2) 2
            (zoomPoint lam h zc p)) := by
    rw [hswirlFun, dz]
    exact ((hasDerivAt_zoomScalar_z
      (Phi := fun w : ParabolicPoint => u w 1 ^ 2 / w.1 0 ^ 2)
      lam h zc hDopen hswirlSmooth p hZD).const_mul
      (lam ^ 4 * (lam ^ (2 * h)) ^ 2)).deriv
  -- the potential vorticity equation at the zoom point
  have hPDE := potential_vorticity_pde u pres f hsol haxi (zoomPoint lam h zc p) hp hplane hZ0ne
  rw [hZ0] at hPDE
  rw [hdt, hdr, hdz, hdrr, hdzz, hswirl]
  simp only [zoomV, zoomW]
  set T := timePartial (potentialVorticity u) (zoomPoint lam h zc p)
  set A := spatialPartial (potentialVorticity u) 0 (zoomPoint lam h zc p)
  set B := spatialPartial (potentialVorticity u) 2 (zoomPoint lam h zc p)
  set Arr := spatialSecondPartial (potentialVorticity u) 0 0 (zoomPoint lam h zc p)
  set Bzz := spatialSecondPartial (potentialVorticity u) 2 2 (zoomPoint lam h zc p)
  set Sw := spatialPartial (fun w : ParabolicPoint => u w 1 ^ 2 / w.1 0 ^ 2) 2
    (zoomPoint lam h zc p)
  set Fq := potentialVorticity f (zoomPoint lam h zc p)
  set u0 := u (zoomPoint lam h zc p) 0
  set u2 := u (zoomPoint lam h zc p) 2
  set dd := lam ^ (2 * h)
  set mm := lam ^ (1 - 2 * h)
  set R := p.1.1
  have hthree : 3 / R * (lam ^ 3 * dd * (lam * A)) = lam ^ 5 * dd * (3 / (lam * R) * A) := by
    field_simp
  linear_combination (lam ^ 5 * dd) * hPDE - hthree +
    (lam ^ 4 * dd * u2 * B - lam ^ 4 * dd * Sw - lam ^ 3 * dd * Bzz * (dd * mm + lam)) * hdm

end CIV
