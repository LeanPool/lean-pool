/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralProcessL2Infinite
public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralProcessLocalMartingaleGeneral

/-!
# The unbounded-horizon Itô integral as a continuous local martingale on `ℝ≥0`

The finite-horizon follow-on (`exists_continuous_localMartingale_modification`) gives, for each
horizon `T = n`, an everywhere-continuous local-martingale modification `Xₙ` of the band-restricted
integrand. Horizon consistency (`itoProcessL2Inf_eq_itoProcessCLM`) makes every `Xₙ` a modification
of the *same* unbounded-horizon process `itoProcessL2Inf · f` on `[0,n]`, so on a co-null set the
`Xₙ` agree on overlaps (`indistinguishable_of_modification_on`). Gluing them — at time `t` read the
horizon `⌈t⌉₊+1`, which is strictly above `t` — yields a single process `gluedProc` continuous on
**all** of `ℝ≥0`, a modification of `itoProcessL2Inf · f` at **every** `t`, and adapted to the
null-augmented filtration. Its martingale property is the **global** `itoProcessL2Inf_isMartingale`
transported across the augmentation by `condExp_sup_nulls` — no horizon clamp is needed (unlike the
`[0,T]` follow-on), because the unbounded-horizon process is genuinely a martingale on the whole
half-line.

## Main definitions

* `horizonProc`: the per-horizon (`T = n`) everywhere-continuous local-martingale modification
  of the `[0,n]`-band-restricted integrand.
* `gluedProc`: the glued unbounded-horizon process, reading at time `t` the horizon `⌈t⌉₊ + 1`
  restricted to the good set `G`.

## Main results

* `horizonProc_agree`: for `m ≤ n`, the two horizon processes agree almost surely as paths on
  `[0,m)`.
* `exists_continuous_martingale_modification_infinite`: the unbounded-horizon Itô process has a
  modification, at every `t`, with everywhere-continuous paths on `ℝ≥0` that is a `Martingale`
  for the null-augmented Brownian filtration.
* `exists_continuous_localMartingale_modification_infinite`: the same modification statement, with
  `IsLocalMartingale` in place of `Martingale`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Ch 7

## Tags

continuous local martingale, gluing modifications, infinite horizon, Itô integral,
null-augmented filtration, MSC 60G44, MSC 60H05
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace ItoLocalMartingaleInfinite

open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral
open ItoIntegralProcessL2Infinite ItoIntegralProcessLocalMartingaleGeneral ItoLocalMartingale

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
  (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
  (f : Lp ℝ 2 ((timeMeasure.prod μ).trim (natFiltration (mΩ := m0) hBmeas).predictable_le_prod))

/-- The per-horizon (`T = n`) everywhere-continuous local-martingale modification of the
`[0,n]`-band-restricted integrand, from the finite-horizon follow-on. -/
noncomputable def horizonProc (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  (exists_continuous_localMartingale_modification hB (n : ℝ≥0) hBmeas hBcont
    (restrictToBand (μ := μ) (n : ℝ≥0) hBmeas f)).choose

/-- Every horizon process is a modification of the **unbounded-horizon** process on `[0,n]`:
its finite-horizon modification clause composed with horizon consistency. -/
lemma horizonProc_mod_inf (n : ℕ) (t : ℝ≥0) (ht : t ≤ (n : ℝ≥0)) :
    horizonProc hB hBmeas hBcont f n t =ᵐ[μ] (itoProcessL2Inf hB t hBmeas f : Ω → ℝ) := by
  have hmod := (exists_continuous_localMartingale_modification hB (n : ℝ≥0) hBmeas hBcont
    (restrictToBand (μ := μ) (n : ℝ≥0) hBmeas f)).choose_spec.1 t ht
  exact (itoProcessL2Inf_eq_itoProcessCLM hB (n : ℝ≥0) t hBmeas ht f).symm ▸ hmod

lemma horizonProc_cont (n : ℕ) (ω : Ω) :
    Continuous (fun t ↦ horizonProc hB hBmeas hBcont f n t ω) :=
  (exists_continuous_localMartingale_modification hB (n : ℝ≥0) hBmeas hBcont
    (restrictToBand (μ := μ) (n : ℝ≥0) hBmeas f)).choose_spec.2.1 ω

lemma horizonProc_adapted (n : ℕ) (i : ℝ≥0) :
    StronglyMeasurable[augFiltration (μ := μ) hBmeas i] (horizonProc hB hBmeas hBcont f n i) :=
  (exists_continuous_localMartingale_modification hB (n : ℝ≥0) hBmeas hBcont
    (restrictToBand (μ := μ) (n : ℝ≥0) hBmeas f)).choose_spec.2.2.2 i

/-- **Pairwise indistinguishability on overlaps.** For `m ≤ n`, the two horizon processes agree
a.e.-pathwise on `[0,m)`: both are continuous and both modify `itoProcessL2Inf · f` there, so
`indistinguishable_of_modification_on` upgrades the a.e.-at-each-`t` agreement to a.e.-for-all-`t`.
-/
lemma horizonProc_agree (m n : ℕ) (hmn : m ≤ n) :
    ∀ᵐ ω ∂μ, ∀ t < (m : ℝ≥0),
      horizonProc hB hBmeas hBcont f m t ω = horizonProc hB hBmeas hBcont f n t ω := by
  refine indistinguishable_of_modification_on (P := μ) (isOpen_Iio)
    (Filter.Eventually.of_forall fun ω ↦ (horizonProc_cont hB hBmeas hBcont f m ω).continuousOn)
    (Filter.Eventually.of_forall fun ω ↦ (horizonProc_cont hB hBmeas hBcont f n ω).continuousOn)
    (fun t ht ↦ ?_)
  have htm : t ≤ (m : ℝ≥0) := le_of_lt ht
  have htn : t ≤ (n : ℝ≥0) := htm.trans (by exact_mod_cast hmn)
  exact (horizonProc_mod_inf hB hBmeas hBcont f m t htm).trans
    (horizonProc_mod_inf hB hBmeas hBcont f n t htn).symm

/-- **The glued unbounded-horizon process.** At time `t` it reads the horizon `⌈t⌉₊+1` (strictly
above `t`), restricted to the good set `G`. On `G` all horizons agree on overlaps, so this is a
single continuous path; off the `μ`-null `Gᶜ` it is `0`. -/
noncomputable def gluedProc (G : Set Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  G.indicator (fun ω ↦ horizonProc hB hBmeas hBcont f (⌈t⌉₊ + 1) t ω) ω

include hBcont

/-- **The unbounded-horizon Itô integral admits a continuous GLOBAL martingale modification.**
There is a process `X` that (i) is a **modification** of the unbounded-horizon `L²` process at
**every** `t` — `X t =ᵐ itoProcessL2Inf t f`; (ii) has **everywhere**-continuous paths on the whole
half-line; and (iii) is a genuine `Martingale` for the null-augmented Brownian filtration. Unlike
the `[0,T]` follow-on there is no horizon clamp: the martingale property holds globally on `ℝ≥0`,
supplied directly by `itoProcessL2Inf_isMartingale` through `condExp_sup_nulls`. The
local-martingale corollary `exists_continuous_localMartingale_modification_infinite` wraps this;
the exposed global martingale is what a genuine localizing sequence (e.g. exit times, Summit C)
needs in order to stop `X`. -/
theorem exists_continuous_martingale_modification_infinite :
    ∃ X : ℝ≥0 → Ω → ℝ,
      (∀ t, X t =ᵐ[μ] (itoProcessL2Inf hB t hBmeas f : Ω → ℝ)) ∧
      (∀ ω, Continuous fun t ↦ X t ω) ∧
      Martingale X (augFiltration (μ := μ) hBmeas) μ := by
  -- co-null good set on which every pair of horizons agrees on its overlap
  have hae : ∀ᵐ ω ∂μ, ∀ m n : ℕ, m ≤ n → ∀ t < (m : ℝ≥0),
      horizonProc hB hBmeas hBcont f m t ω = horizonProc hB hBmeas hBcont f n t ω := by
    refine ae_all_iff.mpr fun m ↦ ae_all_iff.mpr fun n ↦ ?_
    by_cases hmn : m ≤ n
    · filter_upwards [horizonProc_agree hB hBmeas hBcont f m n hmn] with ω hω
      exact fun _ ↦ hω
    · exact Filter.Eventually.of_forall fun ω h ↦ absurd h hmn
  obtain ⟨N, hsubN, hNmeas, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hae)
  set G : Set Ω := Nᶜ with hGdef
  have hGnull : μ Gᶜ = 0 := by rw [hGdef, compl_compl]; exact hNnull
  have hGaug : MeasurableSet[nullsAlg m0 μ] G :=
    (MeasurableSpace.measurableSet_generateFrom
      (show N ∈ {s | MeasurableSet[m0] s ∧ μ s = 0} from ⟨hNmeas, hNnull⟩)).compl
  have hGgood : ∀ ω ∈ G, ∀ m n : ℕ, m ≤ n → ∀ t < (m : ℝ≥0),
      horizonProc hB hBmeas hBcont f m t ω = horizonProc hB hBmeas hBcont f n t ω := by
    intro ω hω
    rw [hGdef, Set.mem_compl_iff] at hω
    exact not_not.mp fun h ↦ hω (hsubN h)
  -- symmetric agreement: any two horizons strictly above `t` agree at `t`, on `G`
  have hGsymm : ∀ ω ∈ G, ∀ (p q : ℕ) (t : ℝ≥0), t < (p : ℝ≥0) → t < (q : ℝ≥0) →
      horizonProc hB hBmeas hBcont f p t ω = horizonProc hB hBmeas hBcont f q t ω := by
    intro ω hω p q t htp htq
    rcases le_total p q with hpq | hqp
    · exact hGgood ω hω p q hpq t htp
    · exact (hGgood ω hω q p hqp t htq).symm
  -- `⌈t⌉₊+1` is a horizon strictly above `t`
  have hceil : ∀ t : ℝ≥0, t < ((⌈t⌉₊ + 1 : ℕ) : ℝ≥0) := fun t ↦
    lt_of_le_of_lt (Nat.le_ceil t) (by exact_mod_cast Nat.lt_succ_self ⌈t⌉₊)
  -- on `G`, the glued process equals horizon `K` on `[0,K)` for every `K`
  have hglueK : ∀ ω ∈ G, ∀ (K : ℕ) (t : ℝ≥0), t < (K : ℝ≥0) →
      gluedProc hB hBmeas hBcont f G t ω = horizonProc hB hBmeas hBcont f K t ω := by
    intro ω hω K t htK
    simp only [gluedProc, Set.indicator_of_mem hω]
    exact hGsymm ω hω (⌈t⌉₊ + 1) K t (hceil t) htK
  -- (1) everywhere continuity of the glued paths
  have hcont : ∀ ω, Continuous (fun t ↦ gluedProc hB hBmeas hBcont f G t ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · refine continuous_iff_continuousAt.mpr fun t₀ ↦ ?_
      set K : ℕ := ⌈t₀⌉₊ + 1
      have ht₀K : t₀ < (K : ℝ≥0) := hceil t₀
      refine (horizonProc_cont hB hBmeas hBcont f K ω).continuousAt.congr ?_
      refine (Filter.eventuallyEq_of_mem (Iio_mem_nhds ht₀K) fun t ht ↦ ?_).symm
      exact hglueK ω hω K t ht
    · have hrw : (fun t ↦ gluedProc hB hBmeas hBcont f G t ω) = fun _ ↦ (0 : ℝ) :=
        funext fun t ↦ by simp only [gluedProc, Set.indicator_of_notMem hω]
      rw [hrw]; exact continuous_const
  -- (2) modification at every `t`
  have hmod : ∀ t : ℝ≥0, (fun ω ↦ gluedProc hB hBmeas hBcont f G t ω)
      =ᵐ[μ] (itoProcessL2Inf hB t hBmeas f : Ω → ℝ) := by
    intro t
    have hG_ae : ∀ᵐ ω ∂μ, ω ∈ G := by rw [ae_iff]; exact hGnull
    have hstep : (fun ω ↦ gluedProc hB hBmeas hBcont f G t ω)
        =ᵐ[μ] (fun ω ↦ horizonProc hB hBmeas hBcont f (⌈t⌉₊ + 1) t ω) := by
      filter_upwards [hG_ae] with ω hω
      simp only [gluedProc, Set.indicator_of_mem hω]
    exact hstep.trans
      (horizonProc_mod_inf hB hBmeas hBcont f (⌈t⌉₊ + 1) t (le_of_lt (hceil t)))
  -- (3) adaptedness to the augmented filtration
  have hadapt : ∀ i : ℝ≥0, StronglyMeasurable[natFiltration hBmeas i ⊔ nullsAlg m0 μ]
      (fun ω ↦ gluedProc hB hBmeas hBcont f G i ω) := by
    intro i
    have h := horizonProc_adapted hB hBmeas hBcont f (⌈i⌉₊ + 1) i
    rw [augFiltration_apply] at h
    exact h.indicator
      ((le_sup_right : nullsAlg m0 μ ≤ natFiltration hBmeas i ⊔ nullsAlg m0 μ) _ hGaug)
  -- (4) the augmented martingale identity, from the GLOBAL itoProcessL2Inf martingale
  have hmart : ∀ {i j : ℝ≥0}, i ≤ j →
      μ[(fun ω ↦ gluedProc hB hBmeas hBcont f G j ω) | natFiltration hBmeas i ⊔ nullsAlg m0 μ]
        =ᵐ[μ] (fun ω ↦ gluedProc hB hBmeas hBcont f G i ω) := by
    intro i j hij
    calc μ[(fun ω ↦ gluedProc hB hBmeas hBcont f G j ω)
            | natFiltration hBmeas i ⊔ nullsAlg m0 μ]
        =ᵐ[μ] μ[(itoProcessL2Inf hB j hBmeas f : Ω → ℝ)
            | natFiltration hBmeas i ⊔ nullsAlg m0 μ] := condExp_congr_ae (hmod j)
      _ =ᵐ[μ] μ[(itoProcessL2Inf hB j hBmeas f : Ω → ℝ) | natFiltration hBmeas i] :=
          condExp_sup_nulls ((natFiltration hBmeas).le i) ((Lp.memLp _).integrable (by norm_num))
      _ =ᵐ[μ] (itoProcessL2Inf hB i hBmeas f : Ω → ℝ) :=
          itoProcessL2Inf_isMartingale hB hBmeas f hij
      _ =ᵐ[μ] (fun ω ↦ gluedProc hB hBmeas hBcont f G i ω) := (hmod i).symm
  -- assemble the GLOBAL martingale
  refine ⟨fun t ω ↦ gluedProc hB hBmeas hBcont f G t ω, hmod, hcont,
    ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩⟩
  · rw [augFiltration_apply]; exact hadapt i
  · rw [augFiltration_apply]; exact hmart hij

/-- **The unbounded-horizon Itô integral is a continuous local martingale on all of `ℝ≥0`** —
the local-martingale wrapper of `exists_continuous_martingale_modification_infinite` (its global
martingale plus the everywhere-continuous, hence càdlàg, paths). -/
theorem exists_continuous_localMartingale_modification_infinite :
    ∃ X : ℝ≥0 → Ω → ℝ,
      (∀ t, X t =ᵐ[μ] (itoProcessL2Inf hB t hBmeas f : Ω → ℝ)) ∧
      (∀ ω, Continuous fun t ↦ X t ω) ∧
      IsLocalMartingale X (augFiltration (μ := μ) hBmeas) μ := by
  obtain ⟨X, hmod, hcont, hmart⟩ :=
    exists_continuous_martingale_modification_infinite hB hBmeas hBcont f
  exact ⟨X, hmod, hcont,
    Martingale.IsLocalMartingale hmart (fun ω ↦ (hcont ω).isCadlag)⟩

end ItoLocalMartingaleInfinite
end MathFin
