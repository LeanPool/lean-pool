/-
Copyright (c) 2026 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Normed.Module.HahnBanach


/-!
# Translation-invariant Hahn–Banach extensions by finite averaging

Background for Lemma 3.2 (`lem:exotic-mean`). Let `R` be an action of the additive group
`ℝ` on a real normed space `E` by linear contractions (no continuity in the translation
parameter is assumed). Let `e ∈ E` be fixed by `R` and `V` an `R`-invariant subspace such
that `|c| ≤ ‖c • e + v‖` for all `c ∈ ℝ` and `v ∈ V`. Then
`exists_invariant_extension` provides `m ∈ E*` with `‖m‖ ≤ 1`, `m e = 1`, `m = 0` on `V`
and `m ∘ R a = m` for all `a`.

Proof: finite Cesàro averages of translations make every coboundary `R a x - x`
arbitrarily small without moving `e` nor leaving `V` (`difference_annihilable`), so the
separation of `e` from `V` persists from `V` to `V ⊔ coboundaries`
(`separation_sup_coboundaries`); then apply the Hahn–Banach theorem to the coefficient
of `e` (`extend_from_separation`).
-/

namespace AbstractLinearControl

@[expose] public section

noncomputable section
open scoped BigOperators

namespace ExoticMean.HahnBanach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A contractive real-translation action, with no continuity assumption in `a`. -/
structure Action (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- Translation by the real parameter. -/
  T : ℝ → E →ₗ[ℝ] E
  zero_apply : ∀ x, T 0 x = x
  add_apply : ∀ a b x, T (a + b) x = T a (T b x)
  bound : ∀ a x, ‖T a x‖ ≤ ‖x‖

namespace Action

variable (R : Action E)

lemma commute (a b : ℝ) (x : E) : R.T a (R.T b x) = R.T b (R.T a x) := by
  rw [← R.add_apply, ← R.add_apply, add_comm a b]

end Action

/-- An averaging operator preserves `e` and `V`, is contractive, and belongs
algebraically to the bicommutant of the translation action. The last field
lets us compose averaging operators without introducing a finite-product API.
Every finite Cesàro average of translations has this property. -/
structure Averager (R : Action E) (e : E) (V : Submodule ℝ E) where
  /-- The contractive averaging operator. -/
  op : E →ₗ[ℝ] E
  fixes : op e = e
  preserves : ∀ x ∈ V, op x ∈ V
  bound : ∀ x, ‖op x‖ ≤ ‖x‖
  bicommutes : ∀ L : E →ₗ[ℝ] E,
    (∀ a x, L (R.T a x) = R.T a (L x)) → ∀ x, op (L x) = L (op x)

namespace Averager

variable {R : Action E} {e : E} {V : Submodule ℝ E}

/-- The identity averaging operator. -/
def identity (R : Action E) (e : E) (V : Submodule ℝ E) : Averager R e V where
  op := LinearMap.id
  fixes := rfl
  preserves := fun _ hx => hx
  bound := fun _ => le_rfl
  bicommutes := by intros; rfl

lemma commute_translation (Q : Averager R e V) (a : ℝ) (x : E) :
    Q.op (R.T a x) = R.T a (Q.op x) :=
  Q.bicommutes (R.T a) (fun b y => R.commute a b y) x

lemma commute (Q P : Averager R e V) (x : E) : Q.op (P.op x) = P.op (Q.op x) :=
  Q.bicommutes P.op (fun a y => P.commute_translation a y) x

/-- Composition of two averaging operators. -/
def comp (Q P : Averager R e V) : Averager R e V where
  op := Q.op.comp P.op
  fixes := by change Q.op (P.op e) = e; rw [P.fixes, Q.fixes]
  preserves := fun x hx => Q.preserves _ (P.preserves x hx)
  bound := fun x => (Q.bound _).trans (P.bound x)
  bicommutes := by
    intro L hL x
    change Q.op (P.op (L x)) = L (Q.op (P.op x))
    rw [P.bicommutes L hL, Q.bicommutes L hL]

/-- The ordinary finite Cesàro average. `N` must be strictly positive. -/
def cesaro (R : Action E) (e : E) (V : Submodule ℝ E)
    (he : ∀ a, R.T a e = e)
    (hV : ∀ a x, x ∈ V → R.T a x ∈ V)
    (a : ℝ) (N : ℕ) (hN : 0 < N) : Averager R e V where
  op := (N : ℝ)⁻¹ • ∑ k ∈ Finset.range N, R.T ((k : ℝ) * a)
  fixes := by
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
    change (N : ℝ)⁻¹ • (∑ k ∈ Finset.range N, R.T ((k : ℝ) * a) e) = e
    simp_rw [he]
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul, inv_mul_cancel₀ (by exact_mod_cast hN.ne'), one_smul]
  preserves := by
    intro x hx
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
    change (N : ℝ)⁻¹ • (∑ k ∈ Finset.range N, R.T ((k : ℝ) * a) x) ∈ V
    exact V.smul_mem _ (V.sum_mem (fun k _ => hV _ x hx))
  bound := by
    intro x
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    have hi : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNr.le
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
    change ‖(N : ℝ)⁻¹ • (∑ k ∈ Finset.range N, R.T ((k : ℝ) * a) x)‖ ≤ ‖x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hi]
    calc
      (N : ℝ)⁻¹ * ‖∑ k ∈ Finset.range N, R.T ((k : ℝ) * a) x‖
          ≤ (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, ‖R.T ((k : ℝ) * a) x‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) hi
      _ ≤ (N : ℝ)⁻¹ * ∑ _k ∈ Finset.range N, ‖x‖ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => R.bound _ x)) hi
      _ = ‖x‖ := by simp [hNr.ne', nsmul_eq_mul]
  bicommutes := by
    intro L hL x
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
    change (N : ℝ)⁻¹ • (∑ k ∈ Finset.range N, R.T ((k : ℝ) * a) (L x)) =
      L ((N : ℝ)⁻¹ • (∑ k ∈ Finset.range N, R.T ((k : ℝ) * a) x))
    rw [map_smul, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact (hL ((k : ℝ) * a) x).symm

lemma cesaro_difference (R : Action E) (e : E) (V : Submodule ℝ E)
    (he : ∀ a, R.T a e = e)
    (hV : ∀ a x, x ∈ V → R.T a x ∈ V)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (x : E) :
    (cesaro R e V he hV a N hN).op (R.T a x - x) =
      (N : ℝ)⁻¹ • (R.T ((N : ℝ) * a) x - x) := by
  have telescoping : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, R.T ((k : ℝ) * a) (R.T a x - x)) =
        R.T ((n : ℝ) * a) x - x := by
    intro n
    induction n with
    | zero => simp [R.zero_apply]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, map_sub, ← R.add_apply]
      have harg : (n : ℝ) * a + a = ((n + 1 : ℕ) : ℝ) * a := by
        push_cast
        ring
      rw [harg]
      abel
  change ((N : ℝ)⁻¹ • ∑ k ∈ Finset.range N, R.T ((k : ℝ) * a)) (R.T a x - x) = _
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  rw [telescoping]

lemma cesaro_difference_bound (R : Action E) (e : E) (V : Submodule ℝ E)
    (he : ∀ a, R.T a e = e)
    (hV : ∀ a x, x ∈ V → R.T a x ∈ V)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (x : E) :
    ‖(cesaro R e V he hV a N hN).op (R.T a x - x)‖ ≤ 2 * ‖x‖ / (N : ℝ) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [cesaro_difference, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hNr.le)]
  calc
    (N : ℝ)⁻¹ * ‖R.T ((N : ℝ) * a) x - x‖
        ≤ (N : ℝ)⁻¹ * (‖R.T ((N : ℝ) * a) x‖ + ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hNr.le)
    _ ≤ (N : ℝ)⁻¹ * (‖x‖ + ‖x‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (R.bound _ x) le_rfl)
        (inv_nonneg.mpr hNr.le)
    _ = 2 * ‖x‖ / (N : ℝ) := by ring

end Averager

/-- Vectors made arbitrarily small by finite contractive averaging. -/
def annihilable (R : Action E) (e : E) (V : Submodule ℝ E) : Submodule ℝ E where
  carrier := {x | ∀ ε : ℝ, 0 < ε → ∃ Q : Averager R e V, ‖Q.op x‖ < ε}
  zero_mem' := by
    intro ε hε
    exact ⟨Averager.identity R e V, by simpa using hε⟩
  add_mem' := by
    intro x y hx hy ε hε
    obtain ⟨Q, hQ⟩ := hx (ε / 2) (by linarith)
    obtain ⟨P, hP⟩ := hy (ε / 2) (by linarith)
    refine ⟨Q.comp P, ?_⟩
    change ‖Q.op (P.op (x + y))‖ < ε
    rw [map_add, map_add]
    have hx' : ‖Q.op (P.op x)‖ < ε / 2 := by
      rw [Q.commute P x]
      exact (P.bound _).trans_lt hQ
    have hy' : ‖Q.op (P.op y)‖ < ε / 2 := (Q.bound _).trans_lt hP
    have ht := norm_add_le (Q.op (P.op x)) (Q.op (P.op y))
    linarith
  smul_mem' := by
    intro c x hx ε hε
    by_cases hc : c = 0
    · subst c
      exact ⟨Averager.identity R e V, by simpa using hε⟩
    · have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
      obtain ⟨Q, hQ⟩ := hx (ε / ‖c‖) (div_pos hε hc')
      refine ⟨Q, ?_⟩
      rw [map_smul, norm_smul]
      have h := (lt_div_iff₀ hc').mp hQ
      simpa [mul_comm] using h

/-- All finite real linear combinations of translation differences. -/
def coboundaries (R : Action E) : Submodule ℝ E :=
  Submodule.span ℝ {d | ∃ a : ℝ, ∃ x : E, d = R.T a x - x}

lemma difference_annihilable (R : Action E) (e : E) (V : Submodule ℝ E)
    (he : ∀ a, R.T a e = e)
    (hV : ∀ a x, x ∈ V → R.T a x ∈ V) (a : ℝ) (x : E) :
    R.T a x - x ∈ annihilable R e V := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * ‖x‖ / ε)
  have hNr : 0 < (N : ℝ) :=
    lt_of_le_of_lt (div_nonneg (by positivity) hε.le) hN
  have hNnat : 0 < N := by exact_mod_cast hNr
  refine ⟨Averager.cesaro R e V he hV a N hNnat, ?_⟩
  apply (Averager.cesaro_difference_bound R e V he hV a N hNnat x).trans_lt
  apply (div_lt_iff₀ hNr).mpr
  have h := (div_lt_iff₀ hε).mp hN
  simpa [mul_comm] using h

lemma coboundaries_le_annihilable (R : Action E) (e : E) (V : Submodule ℝ E)
    (he : ∀ a, R.T a e = e)
    (hV : ∀ a x, x ∈ V → R.T a x ∈ V) :
    coboundaries R ≤ annihilable R e V := by
  apply Submodule.span_le.mpr
  rintro d ⟨a, x, rfl⟩
  exact difference_annihilable R e V he hV a x

/-- The key estimate: adjoining all translation differences preserves the
norm separation of the constants. -/
theorem separation_sup_coboundaries (R : Action E) (e : E) (V : Submodule ℝ E)
    (he : ∀ a, R.T a e = e)
    (hV : ∀ a x, x ∈ V → R.T a x ∈ V)
    (hsep : ∀ c : ℝ, ∀ v ∈ V, |c| ≤ ‖c • e + v‖) :
    ∀ c : ℝ, ∀ w ∈ V ⊔ coboundaries R, |c| ≤ ‖c • e + w‖ := by
  intro c w hw
  obtain ⟨v, hv, d, hd, rfl⟩ := Submodule.mem_sup.mp hw
  by_contra h
  have hgap : 0 < |c| - ‖c • e + (v + d)‖ := sub_pos.mpr (lt_of_not_ge h)
  have hd' := coboundaries_le_annihilable R e V he hV hd
  obtain ⟨Q, hQ⟩ := hd' (|c| - ‖c • e + (v + d)‖) hgap
  have hlow := hsep c (Q.op v) (Q.preserves v hv)
  have htriangle : ‖c • e + Q.op v‖ ≤
      ‖Q.op (c • e + (v + d))‖ + ‖Q.op d‖ := by
    calc
      ‖c • e + Q.op v‖ = ‖Q.op (c • e + (v + d)) - Q.op d‖ := by
        congr 1
        rw [map_add, map_add, map_smul, Q.fixes]
        abel
      _ ≤ _ := norm_sub_le _ _
  have hbound := Q.bound (c • e + (v + d))
  linarith

/-- Hahn--Banach applied to the coefficient of `e`, without presupposing a
choice of direct-sum decomposition. The separation estimate itself proves
that the coefficient is well-defined. -/
theorem extend_from_separation (e : E) (W : Submodule ℝ E)
    (hsep : ∀ c : ℝ, ∀ w ∈ W, |c| ≤ ‖c • e + w‖) :
    ∃ m : E →L[ℝ] ℝ,
      ‖m‖ ≤ 1 ∧ m e = 1 ∧ ∀ w ∈ W, m w = 0 := by
  classical
  have scalar_zero : ∀ c : ℝ, c • e ∈ W → c = 0 := by
    intro c hc
    have h := hsep c (-(c • e)) (W.neg_mem hc)
    simp only [add_neg_cancel, norm_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg c))
  let S : Submodule ℝ E :=
    { carrier := {x | ∃ c : ℝ, x - c • e ∈ W}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro x y ⟨c, hc⟩ ⟨d, hd⟩
        refine ⟨c + d, ?_⟩
        convert W.add_mem hc hd using 1
        rw [add_smul]
        abel
      smul_mem' := by
        rintro a x ⟨c, hc⟩
        refine ⟨a * c, ?_⟩
        convert W.smul_mem a hc using 1
        rw [smul_sub, mul_smul] }
  let coord : S → ℝ := fun x => Classical.choose x.property
  have coord_spec (x : S) : (x : E) - coord x • e ∈ W :=
    Classical.choose_spec x.property
  have coord_eq (x : S) (c : ℝ) (hc : (x : E) - c • e ∈ W) : coord x = c := by
    have hmem : (coord x - c) • e ∈ W := by
      convert W.sub_mem hc (coord_spec x) using 1
      rw [sub_smul]
      abel
    exact sub_eq_zero.mp (scalar_zero (coord x - c) hmem)
  let f : S →ₗ[ℝ] ℝ :=
    { toFun := coord
      map_add' := by
        intro x y
        change coord (x + y) = coord x + coord y
        apply coord_eq
        change (x : E) + (y : E) - (coord x + coord y) • e ∈ W
        convert W.add_mem (coord_spec x) (coord_spec y) using 1
        rw [add_smul]
        abel
      map_smul' := by
        intro a x
        change coord (a • x) = a * coord x
        apply coord_eq
        change a • (x : E) - (a * coord x) • e ∈ W
        convert W.smul_mem a (coord_spec x) using 1
        rw [smul_sub, mul_smul] }
  have hf (x : S) : ‖f x‖ ≤ ‖x‖ := by
    have h := hsep (coord x) ((x : E) - coord x • e) (coord_spec x)
    have heq : coord x • e + ((x : E) - coord x • e) = (x : E) := by abel
    rw [heq] at h
    change ‖coord x‖ ≤ ‖(x : E)‖
    simpa only [Real.norm_eq_abs] using h
  let fC : S →L[ℝ] ℝ := f.mkContinuous 1 (fun x => by simpa using hf x)
  have hfC : ‖fC‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    change ‖f x‖ ≤ 1 * ‖x‖
    simpa using hf x
  obtain ⟨m, hm, hnorm⟩ := exists_extension_norm_eq S fC
  refine ⟨m, hnorm.le.trans hfC, ?_, ?_⟩
  · have heS : e ∈ S := ⟨1, by simp⟩
    calc
      m e = fC ⟨e, heS⟩ := hm ⟨e, heS⟩
      _ = coord ⟨e, heS⟩ := rfl
      _ = 1 := coord_eq _ 1 (by simp)
  · intro w hw
    have hwS : w ∈ S := ⟨0, by simpa using hw⟩
    calc
      m w = fC ⟨w, hwS⟩ := hm ⟨w, hwS⟩
      _ = coord ⟨w, hwS⟩ := rfl
      _ = 0 := coord_eq _ 0 (by simpa using hw)

/-- Translation-invariant Hahn–Banach extension: the main result of this file. -/
theorem exists_invariant_extension (R : Action E) (e : E) (V : Submodule ℝ E)
    (he : ∀ a, R.T a e = e)
    (hV : ∀ a x, x ∈ V → R.T a x ∈ V)
    (hsep : ∀ c : ℝ, ∀ v ∈ V, |c| ≤ ‖c • e + v‖) :
    ∃ m : E →L[ℝ] ℝ,
      ‖m‖ ≤ 1 ∧ m e = 1 ∧ (∀ v ∈ V, m v = 0) ∧
      ∀ a x, m (R.T a x) = m x := by
  obtain ⟨m, hnorm, he', hW⟩ := extend_from_separation e (V ⊔ coboundaries R)
    (separation_sup_coboundaries R e V he hV hsep)
  refine ⟨m, hnorm, he', ?_, ?_⟩
  · intro v hv
    exact hW v (Submodule.mem_sup.mpr ⟨v, hv, 0, (coboundaries R).zero_mem,
      by simp⟩)
  · intro a x
    have hd : R.T a x - x ∈ coboundaries R :=
      Submodule.subset_span ⟨a, x, rfl⟩
    have h := hW (R.T a x - x)
      (Submodule.mem_sup.mpr ⟨0, V.zero_mem, R.T a x - x, hd, by simp⟩)
    rw [map_sub] at h
    exact sub_eq_zero.mp h

end ExoticMean.HahnBanach

end
end

end AbstractLinearControl
