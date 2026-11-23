/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.Definitions
public import Mathlib.Analysis.Complex.HasPrimitives
import LeanPool.Bruck.LogarithmicPrimitive

/-! # Entire quotients and the reduction from value sharing to an ODE -/

public section

open Filter Set Topology

namespace Bruck

/-- A nowhere-zero entire function is the exponential of an entire function. -/
theorem exists_entire_log {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf₀ : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, Complex.exp (g z) = f z := by
  have hlogDeriv : Differentiable ℂ (fun z => deriv f z / f z) :=
    hf.deriv.div hf hf₀
  obtain ⟨P, hP⟩ := hlogDeriv.isExactOn_univ
  have hPd (z : ℂ) : HasDerivAt P (deriv f z / f z) z := hP z (mem_univ z)
  obtain ⟨c, hc, hq⟩ :=
    exists_mul_exp_of_logarithmic_primitive isOpen_univ isPreconnected_univ
      hf.differentiableOn (fun z _ => hf₀ z) hP
  refine ⟨fun z => P z + Complex.log c,
    (show Differentiable ℂ P from fun z => (hPd z).differentiableAt).add_const _, ?_⟩
  intro z
  rw [Complex.exp_add, Complex.exp_log hc, mul_comm]
  exact (hq z (mem_univ z)).symm

/-- Equal zero orders make the apparent singularities of the quotient removable
and ensure the extended quotient is nowhere zero. -/
theorem exists_entire_quotient_of_order_eq {F G : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (hF₀ : F ≠ 0)
    (horder : ∀ z, analyticOrderAt F z = analyticOrderAt G z) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ (∀ z, Q z ≠ 0) ∧ ∀ z, G z = Q z * F z := by
  let q : ℂ → ℂ := fun z => G z / F z
  have hqm : MeromorphicOn q univ := fun z _ =>
    (hG.analyticAt z).meromorphicAt.div (hF.analyticAt z).meromorphicAt
  let Q := toMeromorphicNFOn q univ
  have hQ_rep (z : ℂ) : Q =ᶠ[𝓝[≠] z] q :=
    hqm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)
  have hQ_nf (z : ℂ) : MeromorphicNFAt Q z :=
    meromorphicNFOn_toMeromorphicNFOn q univ (mem_univ z)
  have hF_ne_top (z : ℂ) : meromorphicOrderAt F z ≠ ⊤ := by
    rw [(hF.analyticAt z).meromorphicOrderAt_eq, ne_eq, ENat.map_eq_top_iff]
    exact fun h =>
      hF₀ ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hF.analyticAt).mp h)
  have hQ_order (z : ℂ) : meromorphicOrderAt Q z = 0 := by
    rw [meromorphicOrderAt_congr (hQ_rep z)]
    change meromorphicOrderAt (G / F) z = 0
    rw [meromorphicOrderAt_div (hG.analyticAt z).meromorphicAt (hF.analyticAt z).meromorphicAt]
    have horder' : meromorphicOrderAt G z = meromorphicOrderAt F z := by
      rw [(hG.analyticAt z).meromorphicOrderAt_eq, (hF.analyticAt z).meromorphicOrderAt_eq, horder]
    rw [horder']
    exact LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top (hF_ne_top z)
  have hQa (z : ℂ) : AnalyticAt ℂ Q z :=
    (hQ_nf z).meromorphicOrderAt_nonneg_iff_analyticAt.mp (by rw [hQ_order z])
  refine ⟨Q, fun z => (hQa z).differentiableAt,
    fun z => (hQ_nf z).meromorphicOrderAt_eq_zero_iff.mp (hQ_order z), ?_⟩
  intro z
  have hF_nonzero : ∀ᶠ w in 𝓝[≠] z, F w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hF.analyticAt z).meromorphicAt).mp
      (hF_ne_top z)
  have hn : G =ᶠ[𝓝[≠] z] (fun w => Q w * F w) := by
    filter_upwards [hF_nonzero, hQ_rep z] with w hw hQw
    rw [hQw]
    exact (div_mul_cancel₀ (G w) hw).symm
  exact (((hG z).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    ((hQa z).continuousAt.mul (hF z).continuousAt)).mp hn).eq_of_nhds

/-- An entire function sharing zero with its derivative is nowhere zero,
and its derivative is nowhere zero. -/
theorem zero_free_of_sharesCM_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hshare : SharesCM f (deriv f) 0) : ∀ z, f z ≠ 0 ∧ deriv f z ≠ 0 := by
  have hord (z : ℂ) : analyticOrderAt f z = analyticOrderAt (deriv f) z := by
    simpa using hshare.2.2 z
  intro z
  have hfz : f z ≠ 0 := by
    intro hz
    have hntop : analyticOrderAt f z ≠ ⊤ := fun h =>
      hshare.1 ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hf.analyticAt).mp h)
    have heq := (hf.analyticAt z).analyticOrderAt_deriv_add_one
    rw [hz, show (fun x => f x - 0) = f from funext fun _ => sub_zero _,
      ← hord z] at heq
    exact (ne_of_gt ((ENat.lt_add_one_iff hntop).mpr le_rfl)) heq
  refine ⟨hfz, (hf.analyticAt z).deriv.analyticOrderAt_eq_zero.mp ?_⟩
  rw [← hord z]
  exact (hf.analyticAt z).analyticOrderAt_eq_zero.mpr hfz

/-- The quotient of the two shared-value differences is an entire exponential. -/
theorem exists_exp_mul_of_sharesCM {f : ℂ → ℂ} {a : ℂ} (hf : Differentiable ℂ f)
    (hshare : SharesCM f (deriv f) a) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      ∀ z, deriv f z - a = Complex.exp (h z) * (f z - a) := by
  have hF₀ : (fun z => f z - a) ≠ 0 := by
    intro h
    exact hshare.1 (funext fun z => sub_eq_zero.mp (congrFun h z))
  obtain ⟨Q, hQ, hQ₀, heq⟩ :=
    exists_entire_quotient_of_order_eq (hf.sub_const a) (hf.deriv.sub_const a) hF₀ hshare.2.2
  obtain ⟨h, hh, h_exp⟩ := exists_entire_log hQ hQ₀
  exact ⟨h, hh, fun z => by rw [h_exp, ← heq z]⟩

/-- Normalizing by a nonzero shared value gives the inhomogeneous first-order equation
`y' = exp(h) * y + 1` for `y = (f - a)/a`. -/
theorem normalized_solution_of_sharesCM {f : ℂ → ℂ} {a : ℂ} (ha : a ≠ 0)
    (hf : Differentiable ℂ f) (hshare : SharesCM f (deriv f) a) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      (∀ z, deriv f z - a = Complex.exp (h z) * (f z - a)) ∧
      ∀ z, deriv (fun w => (f w - a) / a) z = Complex.exp (h z) * ((f z - a) / a) + 1 := by
  obtain ⟨h, hh, heq⟩ := exists_exp_mul_of_sharesCM hf hshare
  refine ⟨h, hh, heq, fun z => ?_⟩
  rw [((hf z).hasDerivAt.sub_const a |>.div_const a).deriv, sub_eq_iff_eq_add.mp (heq z),
    add_div, div_self ha, mul_div_assoc]

end Bruck
