/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusBackgroundParameters
public import LeanPool.FastDynamo.Global.TorusGlobalVelocityRegularity

/-!
# The global parameter chain `(v, I, Γ, 𝒢, g_*, f_*, L_*, q, ϑ) → τ → K₀`

The paper fixes its parameters in one order, stated in prose twice: in §3.1 "Choice of the
parameters" and in the paragraph collecting the parameter choices after the proof of
`prop:global-spectral-transfer` (end of §7.2).  Written as a chain (the paper does not display
it),
```
(v, I, Γ, cG, g_*, f_*, L_*, q, vartheta)  →  tau  →  K_0 .
```
A single ratio `1 < q < sqrt (delta_+/delta_-)` is chosen first, `tau` is fixed by
`eq:axial-separation-choice` from `tau`-free constants, and `K_0` is enlarged once, at the very
end, until the paper's five uniform thresholds hold.

This module builds that chain.

## Organisation

* `GlobalSeedInterface` — the seed-side inputs, as an interface record.  `LocalSeedParameters`
  already carries `N = 2 pi k_*`, the interval `I = [delta_-, delta_+]`, the contour `Gamma`
  and `g_* = Gamma.growthFloor > 0`; the record adds the helical profile data (the smoothing
  width and the two speeds, which determine `C_v` and `C_s`), the witness support radius `L_*`
  and the seed resolvent bound `L` of `cor:scaled-local-resolvents`.
* `GlobalSeedInterface.axialShift` — `tau := backgroundTauThreshold g_* M C_0 c_q`
  (`eq:axial-separation-choice`).  Every ingredient is `tau`-free and `K_0`-free, so
  the order `tau` then `K_0` is non-circular.
* `ScaleFamily.exists_ge_chartPacking_supportFit_ell_zero_lt_and_bufferRadius_zero_lt` — the
  single base-index funnel: for *every finite family* of conditions of the shape `ell_0 < t`
  or `sqrt (ell_0) < t` with `t > 0` there is a base index `K_0`, above any prescribed lower
  bound, that also satisfies `eq:chart-packing` and `eq:local-support-in-buffer`.
* `GlobalParameterChoice` — the parameter record, with one field per threshold, and
  `exists_globalParameterChoice` its existence theorem.
* the derived global velocity, the diffusivity threshold `eps_0 = delta_+ / K_0^2`, the
  interval covering `(0, eps_0]`, and the `BackgroundParameters` value.

The scaling package (`lem:exact-renormalization`) of a selected cell,
`ScaleFamily.MatchingCell.exactScalingParameters`, is *not* re-exported here.  Consumers
must call it with `Theta.tau`, so that the torus background resolvent and the rescaled local
resolvent live on exactly the same contour `Gamma_tau`.

## Dictionary to the paper

| paper | here |
|---|---|
| axial wavenumber `2 pi` (Lean: `N = 2 pi k_*`) | `S.parameters.wavenumber` |
| `I = [delta_-, delta_+]` | `S.parameters.interval` |
| `Gamma`, `cG`, `g_*` | `S.parameters.contour`, `.closedRegion`, `.growthFloor` |
| `M = max_cG |Im zeta|` | `S.imBound = |Gamma.center.im| + Gamma.radius` |
| `L_*` | `S.witnessSupportRadius` |
| bound of `eq:local-continuation-bound` (Lean: `L² → H²`) | `S.resolventBound` |
| `1 < q < sqrt (delta_+/delta_-)` | `Theta.ratios.q` |
| `R_v` of §3.3 | `S.placementRadius = max (1 + h) L_*` |
| `c_q = (q-1)/(1+q)` | `backgroundRatioGap Theta.ratios.q` |
| `tau` | `Theta.tau = S.axialShift Theta.ratios` |
| `K_n`, `ell_n = 1/K_n`, `R_n = sqrt (ell_n)` | `Theta.scaleFamily.fourierIndex/ell/bufferRadius` |
| `a_n = tau / (2 pi K_n)` | `Theta.axialAmplitude n` |
| `eps_0 = delta_+ / K_0^2` | `Theta.eps0` |
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Set

/-! ## The seed-side inputs -/

/--
**The seed-side inputs of the parameter chain** (§3.1):
`N, v, I, Gamma, cG, g_*, f_*, L_*`, as an interface record.

`LocalSeedParameters` already supplies `N = 2 pi k_*`, the diffusivity interval
`I = [delta_-, delta_+]` with `0 < delta_- < 1 < delta_+`, the contour `Gamma` with
`g_* = Gamma.growthFloor > 0` (so that `cG` lies in the open right half-plane), and hence also
`scaleRatioCeiling = sqrt (delta_+/delta_-)` and `exists_scaleRatios`.  The remaining fields
are exactly what §6 and §7 of the paper need on top of that: the helical profile (through the
smoothing width and the two speeds, which determine `C_v` and `C_s`), the witness support
radius `L_*` of `eq:scaled-witness-support`, and the uniform seed resolvent bound `L` of
`cor:scaled-local-resolvents`.  The placement radius `R_v = max (1 + h) L_*` is derived from
them; `R_v ≥ L_*` is `witnessSupportRadius_le_placementRadius` (§3.3).

This interface is what the parameter chain consumes; a concrete seed record (such as
`Local/LocalSeedC2.lean`) discharges it field by field.
-/
structure GlobalSeedInterface where
  /-- The scalar and contour data `N = 2 pi k_*`, `I = [delta_-, delta_+]`, `Gamma`, `g_*`. -/
  parameters : LocalSeedParameters
  /-- The smoothing width of the local helical profile `v`. -/
  smoothingWidth : PonomarenkoSmoothingWidth
  /-- The angular speed `Omega` of the local helical profile `v`. -/
  angularSpeed : ℝ
  /-- The axial speed `U` of the local helical profile `v`. -/
  axialSpeed : ℝ
  /-- The support radius `L_*` of the local spectral witness `f_*`
  (`prop:local-seed`). -/
  witnessSupportRadius : ℝ
  /-- `L_* > 0`. -/
  witnessSupportRadius_pos : 0 < witnessSupportRadius
  /-- The uniform local resolvent bound `L` on `Gamma`, uniform in `delta in I`
  (`cor:scaled-local-resolvents`). -/
  resolventBound : ℝ
  /-- `L ≥ 0`. -/
  resolventBound_nonneg : 0 ≤ resolventBound

namespace GlobalSeedInterface

variable (S : GlobalSeedInterface)

/-- The seed contour `Gamma`. -/
abbrev contour : SpectralCircle := S.parameters.contour

/-- The growth floor `g_* = Re(centre) - radius > 0` of the seed contour. -/
abbrev growthFloor : ℝ := S.parameters.contour.growthFloor

/-- `g_* > 0`. -/
theorem growthFloor_pos : 0 < S.growthFloor :=
  S.parameters.growthFloor_pos

/-- The imaginary height `M = max_cG |Im zeta|` of the seed contour, in its canonical form
`|Im centre| + radius`. -/
abbrev imBound : ℝ := S.parameters.contour.imaginaryBound

/-- `|Im zeta| ≤ M` on `cG`. -/
theorem abs_im_le_imBound {z : ℂ} (hz : z ∈ S.parameters.contour.closedRegion) :
    |z.im| ≤ S.imBound :=
  SpectralCircle.abs_im_le_imaginaryBound hz

/-- The support radius `1 + h` of the rescaled local profile, the radius at which the
torus velocity constructions are parameterised. -/
abbrev profileSupportRadius : ℝ := 1 + (S.smoothingWidth : ℝ)

/-- `1 + h > 0`. -/
theorem profileSupportRadius_pos : 0 < S.profileSupportRadius := by
  have := S.smoothingWidth.2.1
  simp only [profileSupportRadius]
  linarith

/--
**`R_v`** (§3.3): the support radius at which the cells are placed.  The paper
chooses `R_v ≥ L_*` with `supp v ∪ supp ∇_⊥ v ⊂ D(0, R_v)`; both clauses are literal here, as
`profileSupportRadius_le_placementRadius` and `witnessSupportRadius_le_placementRadius`.  The
maximum is unavoidable: the profile radius is `1 + h` with `h ∈ (0, 1)`, while the seed's
witness radius `L_*` is produced existentially by `prop:local-seed` and is not bounded above.
-/
abbrev placementRadius : ℝ := max S.profileSupportRadius S.witnessSupportRadius

/-- `supp v ∪ supp ∇_⊥ v ⊂ D(0, R_v)`: the profile radius `1 + h` is at most `R_v`
(§3.3). -/
theorem profileSupportRadius_le_placementRadius :
    S.profileSupportRadius ≤ S.placementRadius :=
  le_max_left _ _

/-- **`R_v ≥ L_*`** (§3.3).  This is what turns `eq:scaled-witness-support` into a consequence
of `eq:local-support-in-buffer` rather than a further threshold on `K_0` (proof of
`lem:global-riesz-nonzero`). -/
theorem witnessSupportRadius_le_placementRadius :
    S.witnessSupportRadius ≤ S.placementRadius :=
  le_max_right _ _

/-- The placement radius is nonnegative. -/
theorem placementRadius_nonneg : 0 ≤ S.placementRadius :=
  le_trans S.profileSupportRadius_pos.le S.profileSupportRadius_le_placementRadius

/-- `C_0` of `eq:background-coercivity`, assembled from the
seed's own constants `C_v`, `C_s`, `delta_-` and `N`.  It is free of `tau` and of `K_0`. -/
abbrev coercivityConstant : ℝ :=
  ScaleFamily.TorusCellPlacement.backgroundCoercivityConstant S.smoothingWidth S.angularSpeed
    S.axialSpeed S.parameters.deltaMinus S.parameters.wavenumber

/-- `C_0 ≥ 0`. -/
theorem coercivityConstant_nonneg : 0 ≤ S.coercivityConstant :=
  ScaleFamily.TorusCellPlacement.backgroundCoercivityConstant_nonneg _ _ _ _
    S.parameters.wavenumber_pos.le

/--
**The axial shift `tau`** (`eq:axial-separation-choice`):
`tau = max (2 M^2 / g_*) (2 (C_0 + 1) / c_q^2)`, the least value satisfying both
`M^2/(2 tau) ≤ g_*/4` and `tau c_q^2 / 2 ≥ C_0 + 1`.

It is a function of the seed inputs and of the ratio `q` only: `g_*`, `M`, `C_0` and
`c_q = (q-1)/(1+q)` involve neither `tau` nor `K_0`.  This is what makes the paper's
order `q → tau → K_0` (§3.1) non-circular.
-/
def axialShift (r : ScaleRatios S.parameters) : ℝ :=
  backgroundTauThreshold S.growthFloor S.imBound S.coercivityConstant (backgroundRatioGap r.q)

/-- The axial shift is strictly positive. -/
theorem axialShift_pos (r : ScaleRatios S.parameters) : 0 < S.axialShift r :=
  backgroundTauThreshold_pos S.coercivityConstant_nonneg (backgroundRatioGap_pos r.one_lt_q)

/-- Nonnegative form of `axialShift_pos`, the shape consumed by the placed axial velocity. -/
theorem axialShift_nonneg (r : ScaleRatios S.parameters) : 0 ≤ S.axialShift r :=
  (S.axialShift_pos r).le

end GlobalSeedInterface

/-! ## The base-index funnel -/

namespace ScaleFamily

variable {p : LocalSeedParameters} {r : ScaleRatios p}

/--
**The base-index funnel, an arbitrary finite family of thresholds.**  Every analytic condition
that the paper's proof imposes on `K_0` has one of the two shapes `ell_0 < t` or
`sqrt (ell_0) = R_0 < t` with `t > 0`; this theorem discharges any finite family of them at
once, together with `eq:chart-packing`, `eq:local-support-in-buffer` and a prescribed lower
bound on `K_0`.

This is the single existence statement behind `exists_globalParameterChoice`: one `min` over
the finitely many targets, matching the paper's single final choice of `K_0` large enough for
finitely many conditions (end of §7.2).
-/
theorem exists_ge_chartPacking_supportFit_ell_zero_lt_and_bufferRadius_zero_lt
    (supportRadius : ℝ) (hsupportRadius : 0 ≤ supportRadius) (M : ℕ)
    (ellTargets rootTargets : Finset ℝ)
    (hell : ∀ t ∈ ellTargets, 0 < t) (hroot : ∀ t ∈ rootTargets, 0 < t) :
    ∃ f : ScaleFamily r,
      M ≤ f.K0 ∧
      f.chartPackingQuantity < 1 / 4 ∧
      (∀ n, supportRadius * f.ell n < f.bufferRadius n / 10) ∧
      (∀ t ∈ ellTargets, f.ell 0 < t) ∧
      (∀ t ∈ rootTargets, Real.sqrt (f.ell 0) < t) := by
  classical
  set A : Finset ℝ := insert 1 (ellTargets.image Real.sqrt ∪ rootTargets) with hAdef
  have hAne : A.Nonempty := ⟨1, by rw [hAdef]; exact Finset.mem_insert_self _ _⟩
  have hApos : ∀ a ∈ A, 0 < a := by
    intro a ha
    rw [hAdef, Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · norm_num
    · rcases Finset.mem_union.mp ha with ha | ha
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ha
        exact Real.sqrt_pos.2 (hell s hs)
      · exact hroot a ha
  set target : ℝ := A.min' hAne with hTdef
  have htarget : 0 < target := hApos _ (A.min'_mem hAne)
  obtain ⟨f, hMf, hpack, hfit, hR0⟩ :=
    exists_ge_chartPacking_supportFit_bufferRadius_zero_lt (r := r) supportRadius target
      hsupportRadius htarget M
  have hroot0 : Real.sqrt (f.ell 0) < target := hR0
  refine ⟨f, hMf, hpack, hfit, ?_, ?_⟩
  · intro s hs
    have hmem : Real.sqrt s ∈ A := by
      rw [hAdef]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs))
    have hle : target ≤ Real.sqrt s := A.min'_le _ hmem
    have hlt : Real.sqrt (f.ell 0) < Real.sqrt s := hroot0.trans_le hle
    have hsq : f.ell 0 < s := by
      have h0 : 0 ≤ f.ell 0 := (f.ell_pos 0).le
      have := (Real.sqrt_lt_sqrt_iff h0).mp hlt
      exact this
    exact hsq
  · intro s hs
    have hmem : s ∈ A := by
      rw [hAdef]
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hs)
    exact hroot0.trans_le (A.min'_le _ hmem)

end ScaleFamily

/-! ## The parameter record -/

/--
**The global parameter chain** (§3.1 and the end of §7.2).

The seed data `S` and the two constants `errorConstant`, `errorTarget` of `eq:error-small` are
fixed first; then the ratio `q`; then `tau = S.axialShift ratios`, which is a function
of the previous data alone; and only then the base Fourier index `K_0`, carried by
`jointPlacement`, which is enlarged until the remaining thresholds hold.

`errorConstant` and `errorTarget` are explicit parameters because §7 of the paper produces
them: `errorConstant` is `C_app (1 + delta_+)` of `eq:explicit-error`
(`parametrixErrorConstant` composed with `scaleErrorMajorant_scaled_le`) and
`errorTarget` is the `eta_*` of the proof of `lem:global-contour-resolvent`.  Nothing in this
module depends on their provenance.

The paper's thresholds on `K_0` (end of §7.2) are exactly: the bounds on `K_{n+1}/K_n` in
`eq:ratio-choice` (the `rounding_bound` field of `ScaleFamily`), `eq:chart-packing` and
`eq:local-support-in-buffer` (the two fields of `TorusCellPlacement`, imposed at the placement
radius `R_v`), `eq:background-diffusion-small` and `eq:error-small`.
`eq:scaled-witness-support` is **not** a threshold: as in the proof of
`lem:global-riesz-nonzero`, it is the theorem `witnessSupport` below, derived from
`eq:local-support-in-buffer` because `R_v ≥ L_*`.  For `eq:local-support-in-buffer` the paper
states the sufficient threshold `K_0 > (10 R_v)^2` (§3.3); the Lean reaches it through
`R_0 < 1 / (10 (R_v + 1))`, i.e. `K_0 > (10 (R_v + 1))^2 k_*`, a slightly larger threshold.
-/
structure GlobalParameterChoice (S : GlobalSeedInterface) (errorConstant errorTarget : ℝ)
    where
  /-- The geometric ratio `1 < q < sqrt (delta_+/delta_-)` (§3.2). -/
  ratios : ScaleRatios S.parameters
  /-- The base Fourier index `K_0` together with `eq:chart-packing` and
  `eq:local-support-in-buffer` **at the placement radius `R_v`**, which is where
  the paper imposes the core containment.  The velocity layer reads the same certificate
  back at the profile radius `1 + h` through the derived `placement`. -/
  jointPlacement : ScaleFamily.TorusCellPlacement (r := ratios) S.placementRadius
  /-- **`eq:background-diffusion-small`**: `C_1 delta_+ ell_0 ≤ g_*/4`, with the explicit value
  `C_1 = 18 ‖vartheta'‖_inf^2` of the formalisation (the paper leaves `C_1` unspecified). -/
  diffusionSmall :
    ScaleFamily.TorusCellPlacement.backgroundDiffusionConstant * S.parameters.deltaPlus *
        jointPlacement.scaleFamily.ell 0 ≤
      S.growthFloor / 4
  /-- **`eq:error-small`**: the parametrix error majorant
  `C (sqrt (ell_0) + ell_0)` stays below `eta_*`.  The paper imposes the bound on the operator
  norms `‖E_{n,δ}(z)‖`; the Lean imposes it on their majorant from `eq:explicit-error`. -/
  errorSmall :
    errorConstant *
        (Real.sqrt (jointPlacement.scaleFamily.ell 0) + jointPlacement.scaleFamily.ell 0) <
      errorTarget

namespace GlobalParameterChoice

open ScaleFamily.TorusCellPlacement.FullVelocityConcrete

variable {S : GlobalSeedInterface} {errorConstant errorTarget : ℝ}
  (Theta : GlobalParameterChoice S errorConstant errorTarget)

/-! ### Scales -/

/-- **The placement at the profile radius `1 + h`**, the radius at which the whole velocity
layer is parameterised.  It is the record's `jointPlacement` restricted along `1 + h ≤ R_v`
(§3.3), and it carries exactly the same scale family — `restrictSupportRadius` leaves
the `scaleFamily` field untouched, so `restrictSupportRadius_scaleFamily` is `rfl` and every
consumer of `Theta.placement` sees the `K_0` of `Theta.jointPlacement`. -/
abbrev placement : ScaleFamily.TorusCellPlacement (r := Theta.ratios) S.profileSupportRadius :=
  Theta.jointPlacement.restrictSupportRadius S.profileSupportRadius_le_placementRadius

/-- The chosen scale family: `K_n`, `ell_n = k_*/K_n`, `R_n = sqrt (ell_n)`. -/
abbrev scaleFamily : ScaleFamily Theta.ratios :=
  Theta.placement.scaleFamily

/-- The base Fourier index `K_0`. -/
abbrev baseIndex : ℕ := Theta.scaleFamily.K0

/-- The axial shift `tau` of `eq:axial-separation-choice`. -/
abbrev tau : ℝ := S.axialShift Theta.ratios

/-- `tau > 0`. -/
theorem tau_pos : 0 < Theta.tau :=
  S.axialShift_pos Theta.ratios

/-- `tau ≥ 0`, the form consumed by the placed axial velocity. -/
theorem tau_nonneg : 0 ≤ Theta.tau :=
  S.axialShift_nonneg Theta.ratios

/-- The added axial speed `a_n` of cell `n`. -/
abbrev axialAmplitude (n : ℕ) : ℝ :=
  Theta.scaleFamily.axialAmplitude Theta.tau n

/-- The frequency-matching identity `2 pi K_n a_n = tau` of §3.3. -/
theorem axialAmplitude_match (n : ℕ) :
    2 * Real.pi * (Theta.scaleFamily.fourierIndex n : ℝ) * Theta.axialAmplitude n = Theta.tau :=
  Theta.scaleFamily.axialAmplitude_match Theta.tau n

/-- **`eq:scaled-witness-support`** (proof of `lem:global-riesz-nonzero`): `L_* ell_n < R_n / 5`
for every cell.

This is not a threshold on `K_0`.  Since `L_* ≤ R_v`
(`witnessSupportRadius_le_placementRadius`, §3.3), the core containment
`eq:local-support-in-buffer` at `R_v` — the `supportFit` field of `jointPlacement` — already
gives `L_* ell_n < R_n/10 < R_n/5`, as in the paper.  This is why `lem:global-riesz-nonzero` is
stated for every `n ≥ 0` with no further enlargement of `K_0`, and why the paragraph collecting
the parameter choices at the end of §7.2 lists five thresholds on `K_0` rather than six. -/
theorem witnessSupport (n : ℕ) :
    S.witnessSupportRadius * Theta.scaleFamily.ell n <
      Theta.scaleFamily.bufferRadius n / 5 := by
  have hle : S.witnessSupportRadius * Theta.scaleFamily.ell n ≤
      S.placementRadius * Theta.scaleFamily.ell n :=
    mul_le_mul_of_nonneg_right S.witnessSupportRadius_le_placementRadius
      (Theta.scaleFamily.ell_pos n).le
  have h10 : Theta.scaleFamily.bufferRadius n / 10 <
      Theta.scaleFamily.bufferRadius n / 5 := by
    have := Theta.scaleFamily.bufferRadius_pos n
    linarith
  exact (hle.trans_lt (Theta.jointPlacement.supportFit n)).trans h10

/-! ### The diffusivity threshold and the interval covering -/

/-- **The diffusivity threshold** `eps_0 = delta_+ ell_0^2 = delta_+ / K_0^2` of §3.2.
As in the paper, no further upper bound is imposed on it. -/
abbrev eps0 : ℝ := Theta.scaleFamily.epsilon0

/-- `eps_0 > 0`. -/
theorem eps0_pos : 0 < Theta.eps0 :=
  Theta.scaleFamily.epsilon0_pos

/-- `eps_0 = delta_+ k_*^2 / K_0^2`, the paper's closed formula (at `k_* = 1`,
`eps_0 = delta_+ / K_0^2`). -/
theorem eps0_formula :
    Theta.eps0 =
      S.parameters.deltaPlus * (S.parameters.kStar : ℝ) ^ 2 / (Theta.baseIndex : ℝ) ^ 2 :=
  Theta.scaleFamily.epsilon0_formula

/-- The matching cell selected by a physical diffusivity below the threshold: the first and
only `epsilon`-dependent choice (§3.2 and the end of §7.2). -/
def matchingCell {epsilon : ℝ} (hpos : 0 < epsilon) (hle : epsilon ≤ Theta.eps0) :
    ScaleFamily.MatchingCell Theta.scaleFamily epsilon :=
  (Theta.scaleFamily.exists_matchingCell hpos hle).some

/-- The left half `delta_- ell_n^2 ≤ epsilon` of the admissibility of a matching cell, in the
multiplied-out form consumed by the background resolvent. -/
theorem matchingCell_lower {epsilon : ℝ}
    (c : ScaleFamily.MatchingCell Theta.scaleFamily epsilon) :
    S.parameters.deltaMinus * Theta.scaleFamily.ell c.index ^ 2 ≤ epsilon := by
  have hpos : 0 < Theta.scaleFamily.ell c.index ^ 2 :=
    pow_pos (Theta.scaleFamily.ell_pos c.index) 2
  have hdelta : S.parameters.deltaMinus ≤ c.delta := c.admissible.1
  calc
    S.parameters.deltaMinus * Theta.scaleFamily.ell c.index ^ 2 ≤
        c.delta * Theta.scaleFamily.ell c.index ^ 2 :=
      mul_le_mul_of_nonneg_right hdelta hpos.le
    _ = epsilon := c.epsilon_eq_delta_mul_ell_sq.symm

/-- The right half `epsilon ≤ delta_+ ell_n^2` of the admissibility of a matching cell. -/
theorem matchingCell_upper {epsilon : ℝ}
    (c : ScaleFamily.MatchingCell Theta.scaleFamily epsilon) :
    epsilon ≤ S.parameters.deltaPlus * Theta.scaleFamily.ell c.index ^ 2 := by
  have hpos : 0 < Theta.scaleFamily.ell c.index ^ 2 :=
    pow_pos (Theta.scaleFamily.ell_pos c.index) 2
  have hdelta : c.delta ≤ S.parameters.deltaPlus := c.admissible.2
  calc
    epsilon = c.delta * Theta.scaleFamily.ell c.index ^ 2 := c.epsilon_eq_delta_mul_ell_sq
    _ ≤ S.parameters.deltaPlus * Theta.scaleFamily.ell c.index ^ 2 :=
      mul_le_mul_of_nonneg_right hdelta hpos.le

/-- The axial Fourier sector `K_n` of a matching cell, as a nonzero integer. -/
abbrev fourierIndex {epsilon : ℝ}
    (c : ScaleFamily.MatchingCell Theta.scaleFamily epsilon) : ℤ :=
  (Theta.scaleFamily.fourierIndex c.index : ℤ)

/-- The axial Fourier sector of a matching cell is nonzero, as the reduced induction operator
requires. -/
theorem fourierIndex_ne_zero {epsilon : ℝ}
    (c : ScaleFamily.MatchingCell Theta.scaleFamily epsilon) : Theta.fourierIndex c ≠ 0 := by
  intro hzero
  have hnat : Theta.scaleFamily.fourierIndex c.index = 0 := by exact_mod_cast hzero
  exact (Nat.ne_of_gt (Theta.scaleFamily.fourierIndex_pos c.index)) hnat

/-- **`eq:error-small` at every cell**.  The record stores the threshold at the
coarsest scale `ell_0`; since `ell_n ≤ ell_0`, the same bound holds uniformly in `n`, which is
the form the parametrix error estimate consumes. -/
theorem errorSmall_cell (hC : 0 ≤ errorConstant) (n : ℕ) :
    errorConstant * (Real.sqrt (Theta.scaleFamily.ell n) + Theta.scaleFamily.ell n) <
      errorTarget := by
  refine lt_of_le_of_lt ?_ Theta.errorSmall
  refine mul_le_mul_of_nonneg_left ?_ hC
  exact add_le_add (Real.sqrt_le_sqrt (Theta.scaleFamily.ell_le_ell_zero n))
    (Theta.scaleFamily.ell_le_ell_zero n)

/-! ### The background parameters of `prop:background-resolvent` -/

/--
**The `BackgroundParameters` value at this parameter chain.**  All ten hypotheses of
`prop:background-resolvent` are discharged: the contour and its growth floor come from the
seed, `M` is the canonical imaginary height, the diffusivity window is `I`, `tau` is
`eq:axial-separation-choice` by construction (hence `le_rfl`), and
`eq:background-diffusion-small` is the record's own field.
-/
def backgroundParameters :
    ScaleFamily.TorusCellPlacement.BackgroundParameters S.smoothingWidth Theta.placement
      S.angularSpeed S.axialSpeed where
  contour := S.parameters.contour
  growthFloor_pos := S.parameters.growthFloor_pos
  imBound := S.imBound
  abs_im_le := fun _ hz ↦ S.abs_im_le_imBound hz
  diffusivityLower := S.parameters.deltaMinus
  diffusivityUpper := S.parameters.deltaPlus
  diffusivityLower_pos := S.parameters.deltaMinus_pos
  tau := Theta.tau
  tau_ge := le_rfl
  diffusion_small := Theta.diffusionSmall

/-- The background parameters carry this chain's axial shift. -/
@[simp] theorem backgroundParameters_tau : Theta.backgroundParameters.tau = Theta.tau := rfl

/-- The background parameters carry the seed contour. -/
@[simp] theorem backgroundParameters_contour :
    Theta.backgroundParameters.contour = S.parameters.contour := rfl

/-- The background parameters carry the seed diffusivity window. -/
@[simp] theorem backgroundParameters_diffusivityLower :
    Theta.backgroundParameters.diffusivityLower = S.parameters.deltaMinus := rfl

/-- The background parameters carry the seed diffusivity window. -/
@[simp] theorem backgroundParameters_diffusivityUpper :
    Theta.backgroundParameters.diffusivityUpper = S.parameters.deltaPlus := rfl

/-- The background parameters carry the canonical imaginary height `M`. -/
@[simp] theorem backgroundParameters_imBound :
    Theta.backgroundParameters.imBound = S.imBound := rfl

/-! ### The global velocity -/

/--
**The global velocity `u = sum_n (u_n^loc + u_n^ax)`** of `eq:global-u` at this
parameter chain: the placed rescaled helical copies plus the cut-off axial offsets with
`a_n = tau/(2 pi K_n)`.  It is the general velocity layer evaluated at the parameters of this
chain.
-/
def velocity : TransverseRealW1Inf :=
  parameterizedFullGlobalW1Inf S.smoothingWidth Theta.placement S.angularSpeed S.axialSpeed
    Theta.tau Theta.tau_nonneg

/-- **`lem:global-velocity`, divergence-free clause**: `Div_perp u = 0` in the quotient
`W^{1,infinity}` graph sense. -/
theorem velocity_isTransverseDivergenceFree : IsTransverseDivergenceFree Theta.velocity :=
  parameterizedFullGlobalW1Inf_isTransverseDivergenceFree S.smoothingWidth Theta.placement
    S.angularSpeed S.axialSpeed Theta.tau Theta.tau_nonneg

/-- **`lem:global-velocity`, nonvanishing clause**: `u ≠ 0`, because `tau > 0` makes the axial
offset nonzero on an annulus of positive measure in every cell. -/
theorem velocity_ne_zero : Theta.velocity ≠ 0 :=
  parameterizedFullGlobalW1Inf_ne_zero S.smoothingWidth Theta.placement S.angularSpeed
    S.axialSpeed Theta.tau_pos

end GlobalParameterChoice

/-! ## Existence of the parameter chain -/

/--
**The parameter chain exists, above every prescribed lower bound on `K_0`.**

The proof follows the paper's order (§3.1 and the end of §7.2):

1. the ratio `q` from `LocalSeedParameters.exists_scaleRatios`;
2. `tau = S.axialShift ratios`, a closed term in `g_*, M, C_0, c_q` — no placement involved;
3. the two analytic targets for `K_0`:
   `t_bg = g_*/(4 (C_1 delta_+ + 1))` for `eq:background-diffusion-small`, imposed on `ell_0`,
   and `t_err = min 1 (eta_*/(2 (C + 1)))` for `eq:error-small`, imposed on `R_0 = sqrt (ell_0)`;
4. one call to `exists_ge_chartPacking_supportFit_ell_zero_lt_and_bufferRadius_zero_lt` at the
   placement radius `R_v = max (1 + h) L_*` (§3.3), which also yields
   `eq:chart-packing` and `eq:local-support-in-buffer`.

`eq:scaled-witness-support` needs no step of its own: it is the theorem
`GlobalParameterChoice.witnessSupport`, read off the same support fit (proof of
`lem:global-riesz-nonzero`).

No condition feeds back into an earlier choice, so the chain is non-circular.
-/
theorem exists_globalParameterChoice (S : GlobalSeedInterface) {errorConstant errorTarget : ℝ}
    (hC : 0 ≤ errorConstant) (heta : 0 < errorTarget) (M : ℕ) :
    ∃ Theta : GlobalParameterChoice S errorConstant errorTarget, M ≤ Theta.baseIndex := by
  classical
  obtain ⟨r⟩ := ScaleRatios.exists_for S.parameters
  -- the two analytic targets
  set C1 : ℝ := ScaleFamily.TorusCellPlacement.backgroundDiffusionConstant with hC1def
  have hC1 : 0 ≤ C1 := ScaleFamily.TorusCellPlacement.backgroundDiffusionConstant_nonneg
  have hprod : 0 ≤ C1 * S.parameters.deltaPlus :=
    mul_nonneg hC1 S.parameters.deltaPlus_pos.le
  set tbg : ℝ := S.growthFloor / (4 * (C1 * S.parameters.deltaPlus + 1)) with htbgdef
  have htbg : 0 < tbg := by
    rw [htbgdef]
    exact div_pos S.growthFloor_pos (by linarith)
  set terr : ℝ := min 1 (errorTarget / (2 * (errorConstant + 1))) with hterrdef
  have hterr : 0 < terr := by
    rw [hterrdef]
    refine lt_min one_pos ?_
    exact div_pos heta (by linarith)
  -- one placement above every threshold
  obtain ⟨f, hMf, hpack, hfit, hellT, hrootT⟩ :=
    ScaleFamily.exists_ge_chartPacking_supportFit_ell_zero_lt_and_bufferRadius_zero_lt
      (r := r) S.placementRadius S.placementRadius_nonneg M
      ({tbg} : Finset ℝ) ({terr} : Finset ℝ)
      (by intro t ht; rw [Finset.mem_singleton] at ht; exact ht ▸ htbg)
      (by intro t ht; rw [Finset.mem_singleton] at ht; exact ht ▸ hterr)
  have hell0 : f.ell 0 < tbg := hellT tbg (Finset.mem_singleton_self _)
  have hroot0 : Real.sqrt (f.ell 0) < terr := hrootT terr (Finset.mem_singleton_self _)
  have hellpos : 0 < f.ell 0 := f.ell_pos 0
  -- `eq:background-diffusion-small`
  have hdiff : C1 * S.parameters.deltaPlus * f.ell 0 ≤ S.growthFloor / 4 := by
    have hstep : C1 * S.parameters.deltaPlus * f.ell 0 ≤ C1 * S.parameters.deltaPlus * tbg :=
      mul_le_mul_of_nonneg_left hell0.le hprod
    refine hstep.trans ?_
    have hD : (0:ℝ) < 4 * (C1 * S.parameters.deltaPlus + 1) := by linarith
    have hrw : C1 * S.parameters.deltaPlus * tbg =
        C1 * S.parameters.deltaPlus * S.growthFloor / (4 * (C1 * S.parameters.deltaPlus + 1)) := by
      rw [htbgdef]; ring
    rw [hrw, div_le_div_iff₀ hD (by norm_num : (0:ℝ) < 4)]
    nlinarith [S.growthFloor_pos]
  -- `eq:error-small`
  have herr : errorConstant * (Real.sqrt (f.ell 0) + f.ell 0) < errorTarget := by
    have hsqrtnn : 0 ≤ Real.sqrt (f.ell 0) := Real.sqrt_nonneg _
    have hsqrtle1 : Real.sqrt (f.ell 0) ≤ 1 := hroot0.le.trans (min_le_left _ _)
    have hs : Real.sqrt (f.ell 0) ^ 2 = f.ell 0 := Real.sq_sqrt hellpos.le
    have hprod2 : 0 ≤ Real.sqrt (f.ell 0) * (1 - Real.sqrt (f.ell 0)) :=
      mul_nonneg hsqrtnn (by linarith)
    have hsq : f.ell 0 ≤ Real.sqrt (f.ell 0) := by nlinarith [hprod2, hs]
    have hden : (0:ℝ) < 2 * (errorConstant + 1) := by linarith
    have h3 : terr * (2 * (errorConstant + 1)) ≤ errorTarget :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    have hsum : Real.sqrt (f.ell 0) + f.ell 0 < 2 * terr := by linarith
    have hbound : errorConstant * (Real.sqrt (f.ell 0) + f.ell 0) ≤ errorConstant * (2 * terr) :=
      mul_le_mul_of_nonneg_left hsum.le hC
    have hlast : errorConstant * (2 * terr) < errorTarget := by nlinarith [hterr, h3]
    exact hbound.trans_lt hlast
  refine ⟨{ ratios := r
            jointPlacement := ⟨f, hpack, hfit⟩
            diffusionSmall := hdiff
            errorSmall := herr }, hMf⟩

/-- The parameter chain is inhabited, for every seed interface and
every pair of error constants. -/
theorem nonempty_globalParameterChoice (S : GlobalSeedInterface)
    {errorConstant errorTarget : ℝ} (hC : 0 ≤ errorConstant) (heta : 0 < errorTarget) :
    Nonempty (GlobalParameterChoice S errorConstant errorTarget) := by
  obtain ⟨Theta, -⟩ := exists_globalParameterChoice S hC heta 0
  exact ⟨Theta⟩

end

end FastDynamo
