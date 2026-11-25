/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.Friedrichs.FormSublevels
public import LeanPool.CutoffRigidity.Friedrichs.Resolvent

/-! # Transfer of energy-decreasing maps and resolvent comparison -/

public section

open Filter Set
open scoped InnerProductSpace Topology

namespace CutoffRigidity.Riemann.Diff.FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

/-- A continuous map that preserves the operator core and decreases energy there also
preserves the Friedrichs form domain and decreases the closed energy. -/
theorem contraction_energy {T : H → H} (hT : Continuous T)
    (hcore : ∀ f : S.Dom, ∃ g : S.Dom, S.emb g = T (S.emb f) ∧
      inner ℝ (S.opA g) (S.emb g) ≤ inner ℝ (S.opA f) (S.emb f))
    (u : S.Q) :
    ∃ v : S.Q, (v : H) = T (u : H) ∧ S.E v v ≤ S.E u u := by
  obtain ⟨x, rfl⟩ := S.qEquiv.surjective u
  have hx : x ∈ closure (range fun f : S.Dom => (f : S.K)) :=
    UniformSpace.Completion.denseRange_coe x
  obtain ⟨seq, hseq, hlim⟩ := mem_closure_iff_seq_limit.mp hx
  choose f hf using hseq
  choose g hg hE using fun n => hcore (f n)
  have hι : Tendsto (fun n => S.ι (seq n)) atTop (𝓝 (S.ι x)) :=
    (S.ι.continuous.tendsto x).comp hlim
  have hfι (n : ℕ) : S.ι (seq n) = S.emb (f n) := by rw [← hf n, S.ι_coe]
  have hgι : Tendsto (fun n => S.emb (g n)) atTop (𝓝 (T (S.ι x))) := by
    simpa only [Function.comp_def, hfι, hg] using (hT.tendsto (S.ι x)).comp hι
  have henergy : Tendsto (fun n => inner ℝ (S.opA (f n)) (S.emb (f n))) atTop
      (𝓝 (S.E (S.qEquiv x) (S.qEquiv x))) := by
    have hh := (hlim.inner (𝕜 := ℝ) hlim).sub (hι.inner (𝕜 := ℝ) hι)
    rw [← S.E_eq] at hh
    convert hh using 1
    ext n
    rw [← hf n, S.ι_coe, UniformSpace.Completion.inner_coe, inner_dom, add_sub_cancel_left]
  have bounds {ε : ℝ} (hε : 0 < ε) :
      ∃ v : S.Q, (v : H) = T (S.ι x) ∧ S.E v v ≤ S.E (S.qEquiv x) (S.qEquiv x) + ε := by
    refine S.energy_le_of_tendsto (u := fun n =>
      ⟨S.emb (g n), S.emb_mem_Q (g n)⟩) hgι ?_
    filter_upwards [henergy.eventually_lt_const (lt_add_of_pos_right _ hε)] with n hn
    rw [S.E_emb]
    exact (hE n).trans hn.le
  obtain ⟨v, hv, _⟩ := bounds one_pos
  refine ⟨v, hv, le_of_forall_pos_le_add fun ε hε => ?_⟩
  obtain ⟨w, hw, hbound⟩ := bounds hε
  have h : v = w := Subtype.ext (hv.trans hw.symm)
  simpa only [h] using hbound

/-- Variational comparison for the Friedrichs resolvent. The energy and norm
inequalities, together with the sign of the forcing term, force the comparison map
to fix the resolvent vector. -/
theorem resolvent_fixed_of_comparison {T : H → H} (hT : Continuous T)
    (hcore : ∀ f : S.Dom, ∃ g : S.Dom, S.emb g = T (S.emb f) ∧
      inner ℝ (S.opA g) (S.emb g) ≤ inner ℝ (S.opA f) (S.emb f))
    {parameter : ℝ} (hparameter : 0 < parameter) (g : H)
    (hnorm : ‖T (S.resolvent parameter g)‖ ≤ ‖S.resolvent parameter g‖)
    (hforce : 0 ≤ inner ℝ g (T (S.resolvent parameter g) - S.resolvent parameter g)) :
    T (S.resolvent parameter g) = S.resolvent parameter g := by
  let u : S.Q := ⟨S.resolvent parameter g, S.resolvent_mem_Q hparameter g⟩
  obtain ⟨v, hv, henergy⟩ := S.contraction_energy hT hcore u
  change (v : H) = T (u : H) at hv
  change ‖T (u : H)‖ ≤ ‖(u : H)‖ at hnorm
  change 0 ≤ inner ℝ g (T (u : H) - (u : H)) at hforce
  rw [← hv] at hnorm hforce ⊢
  have weak (w : S.Q) : S.E u w + parameter * inner ℝ (u : H) (w : H) = inner ℝ g (w : H) :=
    S.E_resolvent hparameter g w
  have energyDiff : S.E (v - u) (v - u) = S.E v v - 2 * S.E u v + S.E u u := by
    simp only [E, E1, map_sub, Submodule.coe_sub, inner_sub_left, inner_sub_right]
    rw [real_inner_comm (S.qEquiv.symm v) (S.qEquiv.symm u), real_inner_comm (v : H) (u : H)]
    ring
  have nonnegDiff := S.E_nonneg (v - u)
  rw [energyDiff] at nonnegDiff
  rw [inner_sub_right] at hforce
  have normSquare : ‖(v : H)‖ ^ 2 ≤ ‖(u : H)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have normDiff : parameter * ‖(v : H) - (u : H)‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, real_inner_comm (u : H) (v : H)]
    have hself := weak u
    rw [real_inner_self_eq_norm_sq] at hself
    have hnorm' := mul_le_mul_of_nonneg_left normSquare hparameter.le
    linarith only [hnorm', hself, weak v, nonnegDiff, hforce, henergy]
  have zero : ‖(v : H) - (u : H)‖ ^ 2 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right normDiff hparameter) (sq_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp zero))

end CutoffRigidity.Riemann.Diff.FormData
