/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.IntervalIntegralLimit
public import LeanPool.CIVAxisymmetric.Comparison.PartialLaplacianParts

/-!
# The spatial integration of the per-point Kato identity

`CIV/Comparison/EnergyInequality3.lean` proves the per-point identity
`truncatedKatoSq_eq_add_intervalIntegral`: at a fixed spatial point `x`, the squared truncated
Kato regularization of the excess `g = q_ε - Ψ_σ` is its own primitive, with the mollified
equation's right side as integrand. That identity is pointwise in `x` and is stated in the
space-time language of `partialLaplacian` and `gradPair`.

Turning it into the integrated energy inequality needs, first, the spatial integration of that
integrand, and inside it the Green identity that moves one derivative off `partialLaplacian` and
onto the Kato test function `2 Φ_κ(g) Φ_κ'(g) χ_R²`. This file supplies that Green identity and
the spatial integration of the Laplacian term, the interchange of the `κ ↓ 0` limit with the
outer time integral, and a Fubini exchange.

## What is proved here

* `integral_partialLaplacian_mul_comm_of_hasCompactSupport` — Green's second identity for the
  truncated Laplacian with compact support required of **one** factor only. Both
  `CIV/Comparison/PartialLaplacianParts.lean` and `CIV/Comparison/EnergyInequality4.lean` carry
  one half of it: the first integrates by parts moving derivatives off the *differentiated*
  factor, which must therefore be compactly supported, and the second moves them off the *test*
  factor. Each identifies the pairing with the same Dirichlet form `∑_{i<d} ∫ ∂_i φ ∂_i ψ`, so
  the two combine into the symmetry statement for a merely smooth `φ` — which is what the
  application needs, since the differentiated factor is `mollifySlice`, smooth but not compactly
  supported.

* `integral_kappaTestFn_mul_partialLaplacian_eq` — the spatial integration of the Laplacian term
  of the per-point identity, in the `partialLaplacian` language that identity uses:
  `∫ (2 Φ_κ(g) Φ_κ'(g) χ_R²) · Δ_d g` equals the negative of the Dirichlet and mixed-cutoff terms.
  `partialLaplacian` at a fixed time is the `lapD` of the spatial slice, so this is the space-time
  reading of `integral_kappaTestFn_mul_lapD_eq`.

* `tendsto_intervalIntegral_integral_sq_kappaProfile_mul_mollifierCutoff` — the `κ ↓ 0` limit of
  the truncated Kato energy, taken *under* the outer time integral. The per-slice limit is
  `tendsto_integral_sq_kappaProfile_mul_mollifierCutoff_nhds_comparisonEnergy`; moving it across
  `∫ s in τ₀..tplus` is dominated convergence along `𝓝[>] 0`, supplied by
  `CIV/Comparison/IntervalIntegralLimit.lean`. The energy density is nonnegative for every `κ`,
  so only the upper half of the domination is a hypothesis.

* `integrable_uncurry_of_bounded_of_spatialSupport` and
  `intervalIntegral_integral_swap_of_bounded_of_spatialSupport` — the Fubini exchange of the
  spatial and the time integral, licensed by joint **measurability** together with a uniform bound
  and spatial compact support, rather than by joint continuity. Joint continuity is not available
  here: the drift is measurable in time only, so the integrands of the comparison argument are
  continuous in `x` for each `s` and merely measurable in `s`.

## Hypotheses

The time-measurability of `s ↦ ∫ x, (Φ_κ(g(x,s)) χ_R(x))²` and a `κ`-uniform integrable majorant
for it on `Icc τ₀ tplus` are hypotheses (`hmeas` and `hdom`/`hG`) of the limit lemma, as is the
joint measurability of the space-time integrand in the Fubini lemmas.
-/

public section

open MeasureTheory Set Filter Topology
open CKN


noncomputable section

namespace CIV

/-! ## Green's second identity with a single compact support -/

/-- **Green's second identity for the truncated Laplacian, with compact support on one side
only.** For test functions on `Vec m × ℝ` whose spatial slices at `τ` are smooth, with the slice
of `ψ` compactly supported, the two pairings agree. Both sides equal the negative Dirichlet form
`-∑_{i<d} ∫ ∂_i ψ ∂_i φ`: the left by
`CIV.Comparison.EnergyInequality4.integral_mul_lapD_eq`, which needs compact support of the test
factor only, the right by
`CIV.Comparison.PartialLaplacianParts.integral_partialLaplacian_mul_eq_neg_integral_gradPair_mul`,
which needs it of the differentiated factor. Neither file alone gives the symmetry for a `φ` that
is only smooth. -/
theorem integral_partialLaplacian_mul_comm_of_hasCompactSupport {m d : ℕ}
    {φ ψ : Vec m × ℝ → ℝ} {τ : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => φ (x, τ)))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => ψ (x, τ)))
    (hψsupp : HasCompactSupport (fun x : Vec m => ψ (x, τ))) :
    ∫ x : Vec m, ψ (x, τ) * partialLaplacian m d φ (x, τ)
      = ∫ x : Vec m, partialLaplacian m d ψ (x, τ) * φ (x, τ) := by
  classical
  have hDφ : ∀ i : Fin m,
      Continuous (fun x : Vec m => fderiv ℝ (fun y : Vec m => φ (y, τ)) x (basisVec i)) :=
    fun i => ((hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous).clm_apply continuous_const
  have hDψ : ∀ i : Fin m,
      Continuous (fun x : Vec m => fderiv ℝ (fun y : Vec m => ψ (y, τ)) x (basisVec i)) :=
    fun i => ((hψ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous).clm_apply continuous_const
  have hDψsupp : ∀ i : Fin m,
      HasCompactSupport (fun x : Vec m => fderiv ℝ (fun y : Vec m => ψ (y, τ)) x (basisVec i)) :=
    fun i => hψsupp.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hint : ∀ i : Fin m, Integrable (fun x : Vec m => if (i : ℕ) < d then
      fderiv ℝ (fun y : Vec m => ψ (y, τ)) x (basisVec i)
        * fderiv ℝ (fun y : Vec m => φ (y, τ)) x (basisVec i) else 0) volume := by
    intro i
    by_cases hi : (i : ℕ) < d
    · simp only [hi, ite_true]
      exact ((hDψ i).mul (hDφ i)).integrable_of_hasCompactSupport (hDψsupp i).mul_right
    · simp only [hi, ite_false]
      exact integrable_zero _ _ _
  have hswap : (∫ x : Vec m, ∑ i : Fin m, if (i : ℕ) < d then
        fderiv ℝ (fun y : Vec m => ψ (y, τ)) x (basisVec i)
          * fderiv ℝ (fun y : Vec m => φ (y, τ)) x (basisVec i) else 0)
      = ∑ i : Fin m, if (i : ℕ) < d then
          ∫ x : Vec m, fderiv ℝ (fun y : Vec m => ψ (y, τ)) x (basisVec i)
            * fderiv ℝ (fun y : Vec m => φ (y, τ)) x (basisVec i) else 0 := by
    rw [integral_finsetSum Finset.univ fun i _ => hint i]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : (i : ℕ) < d
    · simp only [hi, ite_true]
    · simp only [hi, ite_false, integral_zero]
  have h1 : (∫ x : Vec m, ψ (x, τ) * partialLaplacian m d φ (x, τ))
      = -∑ i : Fin m, if (i : ℕ) < d then
          ∫ x : Vec m, fderiv ℝ (fun y : Vec m => ψ (y, τ)) x (basisVec i)
            * fderiv ℝ (fun y : Vec m => φ (y, τ)) x (basisVec i) else 0 :=
    integral_mul_lapD_eq hψ hψsupp hφ
  have h2 : (∫ x : Vec m, partialLaplacian m d ψ (x, τ) * φ (x, τ))
      = -∫ x : Vec m, ∑ i : Fin m, if (i : ℕ) < d then
          fderiv ℝ (fun y : Vec m => ψ (y, τ)) x (basisVec i)
            * fderiv ℝ (fun y : Vec m => φ (y, τ)) x (basisVec i) else 0 :=
    integral_partialLaplacian_mul_eq_neg_integral_gradPair_mul (d := d) hψ hφ hψsupp
  rw [h1, h2, hswap]

/-! ## The Laplacian term of the per-point identity, integrated in space -/

/-- **The spatial integration of the Laplacian term.** The per-point identity of
`CIV/Comparison/EnergyInequality3.lean` carries the Laplacian as
`partialLaplacian m d g (x, τ)`, a space-time expression; the Green identity for the truncated
Kato test function is `integral_kappaTestFn_mul_lapD_eq`, stated for `lapD` on `Vec m`. At a fixed
time the two are the same object, so pairing the per-point integrand against the Kato test
function and integrating over `Vec m` produces the Dirichlet and mixed-cutoff decomposition
directly. No inequality and no limit is taken: this is the integration by parts alone. -/
theorem integral_kappaTestFn_mul_partialLaplacian_eq {m d : ℕ} {kap τ R : ℝ} (hkap : 0 < kap)
    (hR : 0 < R) {g : Vec m × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => g (x, τ))) :
    ∫ x : Vec m, (2 * kappaProfile kap (g (x, τ)) * deriv (kappaProfile kap) (g (x, τ))
          * mollifierCutoff m R x ^ 2) * partialLaplacian m d g (x, τ)
      = -∫ x : Vec m, (mollifierCutoff m R x ^ 2 * (2 * deriv (kappaProfile kap) (g (x, τ)) ^ 2
            + 2 * kappaProfile kap (g (x, τ)) * kappaProfile2 kap (g (x, τ)))
              * dirichletD m d (fun y : Vec m => g (y, τ)) x
          + 4 * kappaProfile kap (g (x, τ)) * deriv (kappaProfile kap) (g (x, τ))
              * mollifierCutoff m R x
              * mixedD m d (fun y : Vec m => g (y, τ)) (mollifierCutoff m R) x) :=
  integral_kappaTestFn_mul_lapD_eq hkap hg (contDiff_mollifierCutoff m R hR)
    (hasCompactSupport_mollifierCutoff m R hR)

/-! ## The `κ ↓ 0` limit under the outer time integral -/

/-- **The truncated Kato energy converges to `comparisonEnergy` under the time integral.** For
each time `s` of the working interval the slice limit is
`tendsto_integral_sq_kappaProfile_mul_mollifierCutoff_nhds_comparisonEnergy`; this moves it across
`∫ s in τ₀..tplus` by dominated convergence along `𝓝[>] 0`. The integrand is a squared quantity,
so its nonnegativity is automatic and only the majorant `G` is assumed. -/
theorem tendsto_intervalIntegral_integral_sq_kappaProfile_mul_mollifierCutoff {m : ℕ}
    {ε M σ K τ₀ tplus Minf R : ℝ} {G : ℝ → ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hab : τ₀ ≤ tplus) (hR : 0 < R) (hRM : Minf / σ ≤ R) {q : Vec m × ℝ → ℝ}
    (hqmeas : ∀ s ∈ Set.Icc τ₀ tplus, AEStronglyMeasurable (fun y => q (y, s)) volume)
    (hqbdd : ∀ s ∈ Set.Icc τ₀ tplus, ∀ᵐ y ∂(volume : Measure (Vec m)), |q (y, s)| ≤ Minf)
    (hmeas : ∀ kap : ℝ, AEStronglyMeasurable
      (fun s => ∫ x : Vec m, (kappaProfile kap
        (mollifySlice m ε q (x, s) - barrier m M σ K τ₀ (x, s)) * mollifierCutoff m R x) ^ 2)
      (volume.restrict (Set.Icc τ₀ tplus)))
    (hdom : ∀ᶠ kap in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
      ∀ᵐ s ∂(volume.restrict (Set.Icc τ₀ tplus)),
        (∫ x : Vec m, (kappaProfile kap
          (mollifySlice m ε q (x, s) - barrier m M σ K τ₀ (x, s)) * mollifierCutoff m R x) ^ 2)
          ≤ G s)
    (hG : IntegrableOn G (Set.Icc τ₀ tplus) volume) :
    Tendsto (fun kap : ℝ => ∫ s in τ₀..tplus, ∫ x : Vec m, (kappaProfile kap
        (mollifySlice m ε q (x, s) - barrier m M σ K τ₀ (x, s)) * mollifierCutoff m R x) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ s in τ₀..tplus, comparisonEnergy m ε M σ K τ₀ q s)) := by
  have hlim : ∀ᵐ s ∂(volume.restrict (Set.Icc τ₀ tplus)),
      Tendsto (fun kap : ℝ => ∫ x : Vec m, (kappaProfile kap
          (mollifySlice m ε q (x, s) - barrier m M σ K τ₀ (x, s)) * mollifierCutoff m R x) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (comparisonEnergy m ε M σ K τ₀ q s)) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun s hs => ?_)
    exact tendsto_integral_sq_kappaProfile_mul_mollifierCutoff_nhds_comparisonEnergy hε hσ hK hM
      hs.1 hR hRM (hqmeas s hs) (hqbdd s hs)
  refine tendsto_intervalIntegral_of_tendsto_of_dominated_nonneg hab hmeas hlim ?_ hG
  filter_upwards [hdom] with kap hkap
  filter_upwards [hkap] with s hs
  exact ⟨integral_nonneg fun _ => sq_nonneg _, hs⟩

/-! ## The Fubini exchange of the spatial and time integrals -/

/-- **A measurable-time integrability bound for the space-time integrand.** Joint continuity is
not available for the integrands of the comparison argument: the drift is only measurable in time,
so `(s, x) ↦ F s x` is jointly measurable and continuous in `x`, not continuous. Compact support
in the spatial variable, a uniform bound, and joint measurability are enough, and they are what the
Kato test function supplies, its spatial support being the fixed cutoff's. -/
theorem integrable_uncurry_of_bounded_of_spatialSupport {m : ℕ} {F : ℝ → Vec m → ℝ}
    {a b C : ℝ} {S : Set (Vec m)} (hS : IsCompact S)
    (hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc a b)).prod (volume : Measure (Vec m))))
    (hbdd : ∀ (s : ℝ) (x : Vec m), ‖F s x‖ ≤ C)
    (hsupp : ∀ (s : ℝ) (x : Vec m), x ∉ S → F s x = 0) :
    Integrable (Function.uncurry F)
      ((volume.restrict (Set.uIoc a b)).prod (volume : Measure (Vec m))) := by
  classical
  have hTmeas : MeasurableSet ((Set.univ : Set ℝ) ×ˢ S) :=
    MeasurableSet.univ.prod hS.measurableSet
  have hTfin : ((volume.restrict (Set.uIoc a b)).prod (volume : Measure (Vec m)))
      ((Set.univ : Set ℝ) ×ˢ S) ≠ ⊤ := by
    rw [Measure.prod_prod, Measure.restrict_apply_univ]
    refine ENNReal.mul_ne_top ?_ hS.measure_ne_top
    rw [Set.uIoc, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hzero : ∀ z : ℝ × Vec m, z ∉ (Set.univ : Set ℝ) ×ˢ S → Function.uncurry F z = 0 := by
    intro z hz
    exact hsupp z.1 z.2 fun h => hz ⟨Set.mem_univ _, h⟩
  have hind : ((Set.univ : Set ℝ) ×ˢ S).indicator (Function.uncurry F) = Function.uncurry F := by
    funext z
    by_cases h : z ∈ (Set.univ : Set ℝ) ×ˢ S
    · exact Set.indicator_of_mem h _
    · rw [Set.indicator_of_notMem h, hzero z h]
  rw [← hind, integrable_indicator_iff hTmeas]
  exact Measure.integrableOn_of_bounded hTfin hmeas (M := C)
    (Filter.Eventually.of_forall fun z => hbdd z.1 z.2)

/-- **The spatial and time integrals of the energy argument commute.** One of the two ingredients
of the integrated energy inequality; the other, the interchange of the
`κ ↓ 0` limit with the outer time integral, is
`tendsto_intervalIntegral_integral_sq_kappaProfile_mul_mollifierCutoff` above. The licence is
`integrable_uncurry_of_bounded_of_spatialSupport`, which asks for measurability in time rather
than continuity. -/
theorem intervalIntegral_integral_swap_of_bounded_of_spatialSupport {m : ℕ} {F : ℝ → Vec m → ℝ}
    {a b C : ℝ} {S : Set (Vec m)} (hS : IsCompact S)
    (hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc a b)).prod (volume : Measure (Vec m))))
    (hbdd : ∀ (s : ℝ) (x : Vec m), ‖F s x‖ ≤ C)
    (hsupp : ∀ (s : ℝ) (x : Vec m), x ∉ S → F s x = 0) :
    (∫ s in a..b, ∫ x : Vec m, F s x) = ∫ x : Vec m, ∫ s in a..b, F s x :=
  intervalIntegral_integral_swap
    (integrable_uncurry_of_bounded_of_spatialSupport (C := C) hS hmeas hbdd hsupp)

end CIV
