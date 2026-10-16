/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepWeylKernel

/-!
# OneStepWeylRepresentative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Weyl's lemma, representative half

`OneStepSchauderWeyl` bridged *variational* harmonicity to *classical*
harmonicity for the smoothings of a weakly harmonic `H¹` function.  What was
missing — the residue — is the statement that some such smoothing **is** the
function, almost everywhere:

> for `u` weakly harmonic on an open `U` and `ε > 0` there is a globally `C^∞`
> function `v`, classically harmonic on the inner region
> `Ω_ε = {p : closedBall p ε ⊆ U}`, with `v = u` almost everywhere on `Ω_ε`.

This module proves it (`exists_harmonicRepresentative`,
`exists_harmonicRepresentative_on`), and then removes the inner-region
restriction: `exists_harmonicRepresentative_full` glues the representatives at
radii `1/(k+1)` into a single function which is classically harmonic on **all
of** `U` and agrees almost everywhere with the zero extension `𝟙_U u` — the
statement of Weyl's lemma proper, and the one the excess-decay compositions
consume (`OneStepSchauderComposeInterior`, `OneStepSchauderComposeBoundary`).

## The device

Two mollifications are used, and each supplies exactly one thing the other
cannot.

* the **radial** kernel `weylKernel d (ε/2)` reproduces classically harmonic
  functions (`convolution_weylKernel_eq_self`) — radiality is what the spherical
  mean value property needs, and mathlib's `ContDiffBump` is *not* radial;
* mathlib's **bump** kernels `(weylBump ρ n).normed volume` converge to the
  function almost everywhere
  (`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`) — the
  Lebesgue differentiation input, which the radial kernel does not carry in
  mathlib.

Both are smooth and compactly supported, so both mollify a weakly harmonic
function to a function with vanishing coordinate Laplacian
(`euclideanCoordLaplacian_mollify_eq_zero`, stated for a general kernel exactly
for this reason).  Writing `K := weylKernel d (ε/2)`, `b_n` for the `n`-th bump
mollification of the zero extension `g := 𝟙_U u`, and `v := K ⋆ g`, the two are
tied together at a point `p` of `Ω_ε` by

```text
  (b_n) p  =  (K ⋆ b_n) p          -- K reproduces the harmonic b_n on ball p (ε/2)
           =  (φ_n ⋆ (K ⋆ g)) p    -- associativity + commutativity of convolution
           =  (φ_n ⋆ v) p ,
```

and letting `n → ∞`: the left side tends to `g p` for almost every `p`, the
right side to `v p` because `v` is continuous.  Note that **no `ε`-independence
argument is needed**: the radial kernel is taken at *half* the margin, so a
single fixed `v` serves the whole inner region.
-/

open scoped Convolution Topology
open MeasureTheory Metric InnerProductSpace
open HCPolySupport (Vec H1Function euclideanCoordLaplacian)
open Algsuperdiff.Section4.Support (IsWeaklyHarmonicOn)

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. The inner region -/

/-- The `ε`-inner region of `U`: the points whose closed sup-metric `ε`-ball lies inside `U`. -/
def innerRegion (U : Set (Vec d)) (eps : ℝ) : Set (Vec d) :=
  {p : Vec d | closedBall p eps ⊆ U}

theorem self_mem_of_mem_innerRegion {U : Set (Vec d)} {eps : ℝ} (heps : 0 ≤ eps) {p : Vec d}
    (hp : p ∈ innerRegion U eps) : p ∈ U :=
  hp (mem_closedBall_self heps)

/-- **The inner region is open.**  The closed ball is compact and `U` is open, so a whole
neighbourhood of admissible centres is available. -/
theorem isOpen_innerRegion {U : Set (Vec d)} (hU : IsOpen U) (eps : ℝ) :
    IsOpen (innerRegion U eps) := by
  rw [Metric.isOpen_iff]
  intro p hp
  obtain ⟨delta, hdelta, hsub⟩ :=
    (isCompact_closedBall p eps).exists_thickening_subset_open hU hp
  refine ⟨delta, hdelta, fun q hq => ?_⟩
  refine fun z hz => hsub ?_
  refine Metric.mem_thickening_iff.2 ⟨p + (z - q), ?_, ?_⟩
  · rw [mem_closedBall, dist_eq_norm]
    have h : p + (z - q) - p = z - q := by abel
    rw [h]
    simpa only [dist_eq_norm] using (mem_closedBall.1 hz)
  · rw [dist_eq_norm]
    have hzq : z - (p + (z - q)) = q - p := by abel
    rw [hzq, ← dist_eq_norm]
    exact mem_ball.1 hq

/-! ## 2. The bump sequence -/

/-- The mathlib bump family used for the Lebesgue-differentiation input: outer radii
`ρ/(n+1) → 0`, inner radii exactly half of those (so the ratio stays bounded by `2`, as
`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable` requires). -/
def weylBump {rho : ℝ} (hrho : 0 < rho) (n : ℕ) : ContDiffBump (0 : Vec d) where
  rIn := rho / (2 * (n + 1))
  rOut := rho / (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff_of_pos_left hrho (by linarith only [h1]) h1]
    linarith only [h1]

theorem weylBump_rOut {rho : ℝ} (hrho : 0 < rho) (n : ℕ) :
    (weylBump (d := d) hrho n).rOut = rho / ((n : ℝ) + 1) := rfl

theorem weylBump_rOut_le {rho : ℝ} (hrho : 0 < rho) (n : ℕ) :
    (weylBump (d := d) hrho n).rOut ≤ rho := by
  rw [weylBump_rOut]
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith only [this]
  exact div_le_self hrho.le h1

theorem tendsto_weylBump_rOut {rho : ℝ} (hrho : 0 < rho) :
    Filter.Tendsto (fun n : ℕ => (weylBump (d := d) hrho n).rOut) Filter.atTop (𝓝 0) := by
  simp only [weylBump_rOut]
  exact Filter.Tendsto.const_div_atTop
    (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop) rho

theorem weylBump_rOut_le_two_mul_rIn {rho : ℝ} (hrho : 0 < rho) (n : ℕ) :
    (weylBump (d := d) hrho n).rOut ≤ 2 * (weylBump (d := d) hrho n).rIn := by
  change rho / ((n : ℝ) + 1) ≤ 2 * (rho / (2 * ((n : ℝ) + 1)))
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine le_of_eq ?_
  field_simp

theorem tsupport_weylBump_normed_subset {rho : ℝ} (hrho : 0 < rho) (n : ℕ) :
    tsupport ((weylBump (d := d) hrho n).normed volume)
      ⊆ closedBall (0 : Vec d) ((weylBump (d := d) hrho n).rOut) := by
  rw [(weylBump (d := d) hrho n).tsupport_normed_eq]

/-! ## 3. Associativity and commutativity of the two mollifications -/

private theorem lsmul_flip_self :
    (ContinuousLinearMap.lsmul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
  ext
  simp

/-- Commutativity of scalar convolution on the coordinate carrier. -/
theorem convolution_comm_real (f g : Vec d → ℝ) :
    f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure (Vec d))] g
      = g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
  have h := MeasureTheory.convolution_flip (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (volume : Measure (Vec d))) (f := g) (g := f)
  rwa [lsmul_flip_self] at h

/-- **Associativity of scalar convolution** for two smooth compactly supported kernels against a
locally integrable field.  The four integrability side conditions of
`MeasureTheory.convolution_assoc` are discharged from compact support alone. -/
theorem convolution_assoc_compactSupport {K b g : Vec d → ℝ}
    (hK_supp : HasCompactSupport K) (hKc : Continuous K)
    (hb_supp : HasCompactSupport b) (hbc : Continuous b)
    (hg : LocallyIntegrable g volume) (x₀ : Vec d) :
    ((K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] b)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x₀
      = (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (b ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)) x₀ := by
  have hgn : LocallyIntegrable (fun x => ‖g x‖) volume := by
    rw [← locallyIntegrableOn_univ] at hg ⊢
    exact hg.norm
  refine MeasureTheory.convolution_assoc (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ) (fun x y z => by simp [mul_assoc])
    hKc.aestronglyMeasurable hbc.aestronglyMeasurable hg.aestronglyMeasurable ?_ ?_ ?_
  · filter_upwards with y
    exact hK_supp.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (hf := hKc) (hg := hbc.locallyIntegrable) y
  · filter_upwards with x
    exact hb_supp.norm.convolutionExists_left (L := ContinuousLinearMap.mul ℝ ℝ)
      (hf := hbc.norm) (hg := hgn) x
  · exact hK_supp.norm.convolutionExists_left (L := ContinuousLinearMap.mul ℝ ℝ)
      (hf := hKc.norm)
      (hg := (hb_supp.norm.continuous_convolution_left (L := ContinuousLinearMap.mul ℝ ℝ)
        hbc.norm hgn).locallyIntegrable) x₀

/-- **The two mollifications commute.**  `K ⋆ (b ⋆ g) = b ⋆ (K ⋆ g)` for smooth compactly
supported `K`, `b` and locally integrable `g`. -/
theorem convolution_mollify_comm {K b g : Vec d → ℝ}
    (hK_supp : HasCompactSupport K) (hKc : Continuous K)
    (hb_supp : HasCompactSupport b) (hbc : Continuous b)
    (hg : LocallyIntegrable g volume) (x₀ : Vec d) :
    (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (b ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)) x₀
      = (b ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)) x₀ := by
  rw [← convolution_assoc_compactSupport hK_supp hKc hb_supp hbc hg x₀,
    convolution_comm_real K b,
    convolution_assoc_compactSupport hb_supp hbc hK_supp hKc hg x₀]

/-! ## 4. Weyl's lemma, representative half -/

/-- **Weyl's lemma, representative half.**

For `u` weakly harmonic on an open set `U` and `ε > 0` there is a globally `C^∞` function `v`
which is classically harmonic (mathlib's `HarmonicOnNhd`, after transport across `toEuc`) on the
inner region `Ω_ε = {p : closedBall p ε ⊆ U}` and agrees with `u` at almost every point of `Ω_ε`.

`U` is not assumed bounded or convex. -/
theorem exists_harmonicRepresentative [NeZero d] {U : Set (Vec d)} (hUopen : IsOpen U)
    {u : H1Function U} (hu : IsWeaklyHarmonicOn U u) {eps : ℝ} (heps : 0 < eps) :
    ∃ v : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      HarmonicOnNhd (v ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' innerRegion U eps) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)), p ∈ innerRegion U eps → v p = u.toFun p := by
  classical
  set rho : ℝ := eps / 2 with hrhodef
  have hrho : 0 < rho := by rw [hrhodef]; linarith only [heps]
  have hUm : MeasurableSet U := hUopen.measurableSet
  set g : Vec d → ℝ := Set.indicator U u.toFun with hgdef
  have hgloc : LocallyIntegrable g volume := locallyIntegrable_indicator_h1 hUm u
  set K : Vec d → ℝ := weylKernel d rho with hKdef
  have hK : ContDiff ℝ (⊤ : ℕ∞) K := weylKernel_contDiff
  have hKc : Continuous K := weylKernel_continuous
  have hK_supp : HasCompactSupport K := weylKernel_hasCompactSupport hrho
  have hKsub : tsupport K ⊆ closedBall (0 : Vec d) rho := tsupport_weylKernel_subset hrho
  set v : Vec d → ℝ := K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g with hvdef
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := contDiff_mollify hUm u hK_supp hK
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_cast)
  -- the geometric step: a point of the inner region has a `rho`-ball of admissible centres
  have hball : ∀ p ∈ innerRegion U eps, ∀ y ∈ ball p rho, ∀ r : ℝ, r ≤ rho →
      closedBall y r ⊆ U := by
    intro p hp y hy r hr
    refine subset_trans (closedBall_subset_closedBall' ?_) hp
    have hyp : dist y p < rho := mem_ball.1 hy
    rw [hrhodef] at hr hyp
    linarith only [hr, hyp]
  -- the coordinate Laplacian of `v` vanishes near every point of the inner region
  have hvzero : ∀ p ∈ innerRegion U eps, ∀ y ∈ ball p rho, euclideanCoordLaplacian v y = 0 := by
    intro p hp y hy
    exact euclideanCoordLaplacian_mollify_eq_zero hUopen hu hK_supp hK hKsub
      (hball p hp y hy rho le_rfl)
  refine ⟨v, hv, ?_, ?_⟩
  · rintro z ⟨p, hp, rfl⟩
    exact harmonicOnNhd_ball_comp_toEuc_symm hv2 hrho (hvzero p hp) (toEuc p)
      (mem_ball_self hrho)
  -- (b) the almost-everywhere identification
  have hae : ∀ᵐ x₀ ∂(volume : Measure (Vec d)),
      Filter.Tendsto (fun n : ℕ =>
        (((weylBump (d := d) hrho n).normed volume)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x₀) Filter.atTop (𝓝 (g x₀)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K := 2)
      (tendsto_weylBump_rOut hrho)
      (Filter.Eventually.of_forall (weylBump_rOut_le_two_mul_rIn hrho)) hgloc
  filter_upwards [hae] with x₀ hx₀ hmem
  -- the bump mollifications, and their reproducing identity against the radial kernel
  have hstep : ∀ n : ℕ,
      (((weylBump (d := d) hrho n).normed volume)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x₀
        = (((weylBump (d := d) hrho n).normed volume)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x₀ := by
    intro n
    set b : Vec d → ℝ := (weylBump (d := d) hrho n).normed volume with hbdef
    have hbC : ContDiff ℝ (⊤ : ℕ∞) b :=
      (weylBump (d := d) hrho n).contDiff_normed (n := (⊤ : ℕ∞))
    have hbc : Continuous b := hbC.continuous
    have hb_supp : HasCompactSupport b := (weylBump (d := d) hrho n).hasCompactSupport_normed
    set w : Vec d → ℝ := b ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g with hwdef
    have hw : ContDiff ℝ 2 w := (contDiff_mollify hUm u hb_supp hbC).of_le (by norm_cast)
    have hwzero : ∀ y ∈ ball x₀ rho, euclideanCoordLaplacian w y = 0 := by
      intro y hy
      exact euclideanCoordLaplacian_mollify_eq_zero hUopen hu hb_supp hbC
        (tsupport_weylBump_normed_subset hrho n)
        (hball x₀ hmem y hy _ (weylBump_rOut_le hrho n))
    have hrepr : (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) x₀ = w x₀ :=
      convolution_weylKernel_eq_self hw hrho hwzero
    rw [← hrepr, hwdef, convolution_mollify_comm hK_supp hKc hb_supp hbc hgloc x₀]
  -- pass to the limit on both sides
  have hlimv : Filter.Tendsto (fun n : ℕ =>
      (((weylBump (d := d) hrho n).normed volume)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x₀) Filter.atTop (𝓝 (v x₀)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous (tendsto_weylBump_rOut hrho)
      hv.continuous x₀
  have hlimg : Filter.Tendsto (fun n : ℕ =>
      (((weylBump (d := d) hrho n).normed volume)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x₀) Filter.atTop (𝓝 (g x₀)) := by
    refine hx₀.congr fun n => hstep n
  have hgv : g x₀ = v x₀ := tendsto_nhds_unique hlimg hlimv
  rw [← hgv, hgdef, Set.indicator_of_mem (self_mem_of_mem_innerRegion heps.le hmem)]

/-- **Weyl's lemma, representative half, on a supplied window.**  The window form consumed by the
interior Schauder producer: on any measurable `W` all of whose points carry an `ε`-ball inside `U`,
the weakly harmonic `u` has a globally smooth, classically harmonic representative. -/
theorem exists_harmonicRepresentative_on [NeZero d] {U : Set (Vec d)} (hUopen : IsOpen U)
    {u : H1Function U} (hu : IsWeaklyHarmonicOn U u) {eps : ℝ} (heps : 0 < eps)
    {W : Set (Vec d)} (hWm : MeasurableSet W) (hW : W ⊆ innerRegion U eps) :
    ∃ v : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      HarmonicOnNhd (v ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' W) ∧
      v =ᵐ[volume.restrict W] u.toFun := by
  obtain ⟨v, hv, hharm, hae⟩ := exists_harmonicRepresentative hUopen hu heps
  refine ⟨v, hv, hharm.mono (Set.image_mono hW), ?_⟩
  have hae' : ∀ᵐ p ∂(volume.restrict W), p ∈ innerRegion U eps → v p = u.toFun p :=
    MeasureTheory.ae_restrict_of_ae hae
  filter_upwards [hae', MeasureTheory.self_mem_ae_restrict hWm] with p h1 h2
  exact h1 (hW h2)

/-! ## 5. Weyl's lemma on the whole domain -/

/-- Two continuous functions which agree almost everywhere on an open set agree on it. -/
theorem eqOn_of_ae_eq_of_continuous {S : Set (Vec d)} (hS : IsOpen S) {f g : Vec d → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hae : ∀ᵐ p ∂(volume : Measure (Vec d)), p ∈ S → f p = g p) : Set.EqOn f g S := by
  intro p hp
  by_contra hne
  have hTopen : IsOpen (S ∩ {q : Vec d | f q ≠ g q}) := hS.inter (isOpen_ne_fun hf hg)
  have hTpos : 0 < volume (S ∩ {q : Vec d | f q ≠ g q}) :=
    hTopen.measure_pos volume ⟨p, hp, hne⟩
  have hnull : volume (S ∩ {q : Vec d | f q ≠ g q}) = 0 := by
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.ae_iff.1 hae)
    intro q hq hcon
    exact hq.2 (hcon hq.1)
  rw [hnull] at hTpos
  exact lt_irrefl 0 hTpos

/-- **Weyl's lemma.**

For `u` weakly harmonic on an open set `U` there is a function `v` on the coordinate carrier
which is classically harmonic (mathlib's `HarmonicOnNhd`, after transport across `toEuc`) on **all
of** `U`, and which agrees almost everywhere with the zero extension of `u`.

The fixed-radius representative `exists_harmonicRepresentative` is harmonic only on the inner
region `Ω_ε`; here the representatives at radii `1/(k+1)` are glued.  They are pairwise consistent
because each equals `u` almost everywhere on the common inner region and each is continuous
(`eqOn_of_ae_eq_of_continuous`), so on every inner region the sequence is eventually constant and
its limit is a single well-defined function.

The second conjunct is stated as a global almost-everywhere identity with the *zero extension*
`𝟙_U u`, which is what makes `v` square integrable on any window (see
`memLp_harmonicRepresentative_full`): `v` is **not** claimed smooth off `U`. -/
theorem exists_harmonicRepresentative_full [NeZero d] {U : Set (Vec d)} (hUopen : IsOpen U)
    {u : H1Function U} (hu : IsWeaklyHarmonicOn U u) :
    ∃ v : Vec d → ℝ,
      HarmonicOnNhd (v ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' U) ∧
      v =ᵐ[volume] Set.indicator U u.toFun := by
  classical
  choose w hwC hwharm hwae using fun k : ℕ =>
    exists_harmonicRepresentative hUopen hu (eps := 1 / ((k : ℝ) + 1)) (by positivity)
  set R : ℕ → Set (Vec d) := fun k => innerRegion U (1 / ((k : ℝ) + 1)) with hRdef
  have hRpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hRopen : ∀ k, IsOpen (R k) := fun k => isOpen_innerRegion hUopen _
  have hRsub : ∀ k, R k ⊆ U := fun k _ hp => self_mem_of_mem_innerRegion (hRpos k).le hp
  have hRmono : ∀ j k : ℕ, j ≤ k → R j ⊆ R k := by
    intro j k hjk p hp
    refine subset_trans (closedBall_subset_closedBall ?_) hp
    have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have h2 : ((j : ℝ) + 1) ≤ ((k : ℝ) + 1) := by
      have hcast : (j : ℝ) ≤ (k : ℝ) := Nat.cast_le.2 hjk
      linarith only [hcast]
    exact one_div_le_one_div_of_le h1 h2
  have hcover : ∀ p ∈ U, ∃ k : ℕ, p ∈ R k := by
    intro p hp
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hUopen p hp
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr
    exact ⟨k, subset_trans (Metric.closedBall_subset_ball hk) hsub⟩
  have hae_all : ∀ᵐ p ∂(volume : Measure (Vec d)), ∀ k : ℕ, p ∈ R k → w k p = u.toFun p :=
    MeasureTheory.ae_all_iff.2 hwae
  have hcons : ∀ j k : ℕ, j ≤ k → Set.EqOn (w k) (w j) (R j) := by
    intro j k hjk
    refine eqOn_of_ae_eq_of_continuous (hRopen j) (hwC k).continuous (hwC j).continuous ?_
    filter_upwards [hae_all] with p hp hpj
    rw [hp k (hRmono j k hjk hpj), hp j hpj]
  set v : Vec d → ℝ :=
    Set.indicator U (fun q => Filter.limUnder Filter.atTop (fun k => w k q)) with hvdef
  have hval : ∀ (k : ℕ) (p : Vec d), p ∈ R k → v p = w k p := by
    intro k p hpk
    rw [hvdef, Set.indicator_of_mem (hRsub k hpk)]
    refine Filter.Tendsto.limUnder_eq ?_
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop k] with j hj
    exact (hcons k j hj hpk).symm
  refine ⟨v, ?_, ?_⟩
  · rintro z ⟨p, hp, rfl⟩
    obtain ⟨k, hk⟩ := hcover p hp
    have hopen : IsOpen ((toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' R k) :=
      (hRopen k).preimage
        (toEuc.symm : EuclideanSpace ℝ (Fin d) ≃L[ℝ] Vec d).continuous
    have hmem : (toEuc p : EuclideanSpace ℝ (Fin d))
        ∈ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' R k := by
      simpa only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hk
    have heq : (v ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        =ᶠ[nhds (toEuc p)] ((w k) ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) := by
      filter_upwards [hopen.mem_nhds hmem] with z hz
      exact hval k _ hz
    exact (harmonicAt_congr_nhds heq).2 (hwharm k (toEuc p) ⟨p, hk, rfl⟩)
  · filter_upwards [hae_all] with p hp
    by_cases hpU : p ∈ U
    · obtain ⟨k, hk⟩ := hcover p hpU
      rw [hval k p hk, hp k hk, Set.indicator_of_mem hpU]
    · rw [hvdef, Set.indicator_of_notMem hpU, Set.indicator_of_notMem hpU]

/-- **Weyl's lemma, packaged for the excess-decay chain.**  The representative is additionally
square integrable on every window, because it agrees almost everywhere with the zero extension of
`u`. -/
theorem exists_harmonicRepresentative_memLp [NeZero d] {U : Set (Vec d)} (hUopen : IsOpen U)
    {u : H1Function U} (hu : IsWeaklyHarmonicOn U u) :
    ∃ v : Vec d → ℝ,
      HarmonicOnNhd (v ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' U) ∧
      MemLp v 2 (volume : Measure (Vec d)) ∧
      v =ᵐ[volume] Set.indicator U u.toFun := by
  obtain ⟨v, hharm, hae⟩ := exists_harmonicRepresentative_full hUopen hu
  exact ⟨v, hharm, (memLp_indicator_h1 hUopen.measurableSet u).ae_eq hae.symm, hae⟩

/-! ## 6. Harmonic representatives and measure-preserving involutions -/

/-- A classical harmonic representative is continuous on its coordinate window. -/
theorem continuousOn_of_harmonicOnNhd_toEuc {S : Set (Vec d)} {V : Vec d → ℝ}
    (hV : HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' S)) :
    ContinuousOn V S := by
  intro y hy
  have hcont := (hV (toEuc y) ⟨y, hy, rfl⟩).1.continuousAt
  have heq : V = (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) ∘
      (toEuc : Vec d → EuclideanSpace ℝ (Fin d)) := by
    funext z
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [heq]
  exact (hcont.comp (toEuc : Vec d ≃L[ℝ]
    EuclideanSpace ℝ (Fin d)).continuous.continuousAt).continuousWithinAt

/-- Harmonicity transfers through equality on an open coordinate window. -/
theorem harmonicOnNhd_toEuc_congr_eqOn {S : Set (Vec d)} (hS : IsOpen S)
    {V W : Vec d → ℝ} (h : Set.EqOn W V S)
    (hV : HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' S)) :
    HarmonicOnNhd (W ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' S) := by
  have hopen : IsOpen ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' S) :=
    (toEuc : Vec d ≃L[ℝ] EuclideanSpace ℝ (Fin d)).toHomeomorph.isOpenMap _ hS
  intro e he
  have hgerm : (W ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) =ᶠ[nhds e]
      (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) := by
    refine Filter.eventually_of_mem (hopen.mem_nhds he) ?_
    rintro z ⟨y, hy, rfl⟩
    simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using h hy
  exact (harmonicAt_congr_nhds hgerm).mpr (hV e he)

/-- On an invariant open set, an a.e.-equal continuous representative inherits oddness. -/
theorem eqOn_odd_of_ae_eq {S : Set (Vec d)} (hS : IsOpen S)
    {r : Vec d → Vec d} (hr : Continuous r) (hmp : MeasurePreserving r volume volume)
    (hsymm : ∀ y, r y ∈ S ↔ y ∈ S) {V O : Vec d → ℝ}
    (hV : ContinuousOn V S) (hae : V =ᵐ[volume.restrict S] O)
    (hO : ∀ y, O (r y) = -O y) : ∀ y ∈ S, V (r y) = -V y := by
  have hpre : r ⁻¹' S = S := Set.ext hsymm
  have hrestricted : MeasurePreserving r (volume.restrict S) (volume.restrict S) := by
    have h := hmp.restrict_preimage hS.measurableSet
    rwa [hpre] at h
  have hae2 : (fun y => V (r y)) =ᵐ[volume.restrict S] fun y => O (r y) :=
    hae.comp_tendsto hrestricted.quasiMeasurePreserving.tendsto_ae
  have hae3 : (fun y => V (r y)) =ᵐ[volume.restrict S] fun y => -V y := by
    filter_upwards [hae2, hae] with y h2 h3
    rw [h2, hO y, h3]
  have hVr : ContinuousOn (fun y => V (r y)) S :=
    hV.comp hr.continuousOn (fun y hy => (hsymm y).mpr hy)
  exact Measure.eqOn_open_of_ae_eq hae3 hS hVr hV.neg

/-- Symmetrization makes a harmonic a.e. representative globally odd under a
continuous measure-preserving involution, without changing it on the invariant open set. -/
theorem exists_oddHarmonic_of_ae_eq {S : Set (Vec d)} (hS : IsOpen S)
    {r : Vec d → Vec d} (hr : Continuous r) (hmp : MeasurePreserving r volume volume)
    (hinv : Function.Involutive r) (hsymm : ∀ y, r y ∈ S ↔ y ∈ S)
    {V O : Vec d → ℝ}
    (hVharm : HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' S))
    (hVmem : MemLp V 2 (volume : Measure (Vec d)))
    (hae : V =ᵐ[volume.restrict S] O) (hO : ∀ y, O (r y) = -O y) :
    ∃ W : Vec d → ℝ, (∀ y, W (r y) = -W y) ∧
      MemLp W 2 (volume : Measure (Vec d)) ∧
      HarmonicOnNhd (W ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' S) ∧ Set.EqOn W V S := by
  have hodd := eqOn_odd_of_ae_eq hS hr hmp hsymm
    (continuousOn_of_harmonicOnNhd_toEuc hVharm) hae hO
  let W : Vec d → ℝ := fun y => (1 / 2 : ℝ) * (V y - V (r y))
  have hWeq : Set.EqOn W V S := by
    intro y hy
    dsimp only [W]
    rw [hodd y hy]
    ring
  refine ⟨W, ?_, (hVmem.sub (hVmem.comp_measurePreserving hmp)).const_mul (1 / 2),
    harmonicOnNhd_toEuc_congr_eqOn hS hWeq hVharm, hWeq⟩
  intro y
  dsimp only [W]
  rw [hinv y]
  ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
