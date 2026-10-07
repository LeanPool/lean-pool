/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationStep
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrong

/-!
# Continuation of a Leray–Hopf solution by strong solutions

`lem:lps-continuation`: a Leray–Hopf solution of finite Serrin norm agrees, from a
good time of energy equality up to its final time and beyond, with a strong
solution. The strong solutions are built by repeated use of the local strong
existence theorem, whose lifespan is bounded below through the `H¹` estimate, and
are identified with the Leray–Hopf solution by uniqueness.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A finite-Serrin-norm Leray–Hopf solution on `(0, T)` coincides, from a good time
`t₀` of energy equality, with a strong solution on `[t₀, t₁]` for some `t₁ > T`
(`lem:lps-continuation`). The hypothesis `hLocal` is the local strong existence
theorem `prop:lps-local-strong`, in the form used here. -/
theorem lps_continuation_of_local
    (hLocal : ∃ c : ℝ, 0 < c ∧
      ∀ (t : ℝ) (b : Vec3 → Vec3) (Db : Vec3 → Fin 3 → Vec3),
        IsLpsGoodTime (fun z : ParabolicPoint => b z.1) (fun z i => Db z.1 i) t →
        ∃ τ : ℝ, 0 < τ ∧
          c * Real.rpow (1 + Real.sqrt (∫ x : Vec3,
            (∑ i : Fin 3, (b x i) ^ 2) + ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2))
              (-4 : ℝ) ≤ τ ∧
          ∃ (W : ParabolicPoint → Vec3) (DW : ParabolicPoint → Fin 3 → Vec3)
            (pW : ParabolicPoint → ℝ),
            IsLpsStrongSolution t (t + τ) W DW pW ∧
            (fun x : Vec3 => W (x, t)) =ᵐ[volume] b)
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hSerrin :
      (∃ s : ℝ, 3 < s ∧
        (∫⁻ t in Ioo (0 : ℝ) T,
          (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
            ((2 * s / (s - 3)) / s)) < ⊤) ∨
      (∫⁻ t in Ioo (0 : ℝ) T,
        (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) T) (hGood : IsLpsGoodTime u Du t₀)
    (hEq₀ : (∫ x : Vec3, ∑ k : Fin 3, u (x, t₀) k * u (x, t₀) k) -
        (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
      -2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
        ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j) :
    ∃ t₁ : ℝ, T < t₁ ∧
      ∃ (U : ParabolicPoint → Vec3) (DU : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ),
        IsLpsStrongSolution t₀ t₁ U DU p ∧
        (fun x : Vec3 => U (x, t₀)) =ᵐ[volume] (fun x : Vec3 => u (x, t₀)) ∧
        U =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))] u := by
  obtain ⟨c, hc, hLoc⟩ := hLocal
  have hE0 := lps_lh_energy_ennreal hLH ht₀ hGood.2.1 hEq₀
  obtain ⟨S, hSb⟩ := lps_continuation_bound hLH hSerrin ht₀.1.le
  set X₀ : ℝ := ∫ x : Vec3, (∑ i : Fin 3, (u (x, t₀) i) ^ 2) +
    ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t₀) i j) ^ 2 with hX₀
  set S' : ℝ := max S X₀ with hS'
  set τs : ℝ := c * Real.rpow (1 + Real.sqrt S') (-4 : ℝ) with hτs
  have hτpos : 0 < τs :=
    mul_pos hc (Real.rpow_pos_of_pos (by have := Real.sqrt_nonneg S'; linarith only [this]) _)
  have claim : ∀ n : ℕ, ∃ (t₁ : ℝ) (U : ParabolicPoint → Vec3)
      (DU : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ),
      IsLpsStrongSolution t₀ t₁ U DU p ∧
      (fun x : Vec3 => U (x, t₀)) =ᵐ[volume] (fun x : Vec3 => u (x, t₀)) ∧
      (fun x : Vec3 => DU (x, t₀)) =ᵐ[volume] (fun x : Vec3 => Du (x, t₀)) ∧
      U =ᵐ[volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (min t₁ T)))] u ∧
      (T < t₁ ∨ t₀ + ((n : ℝ) + 1) * τs ≤ t₁) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨t₁, hlen, U, DU, p, hU, hU0, hDU0, hae⟩ := lps_continuation_base hc.le hLoc hLH
        hSerrin ht₀.1 ht₀.2.le hGood hE0 (le_max_right S X₀)
      refine ⟨t₁, U, DU, p, hU, hU0, hDU0, hae, Or.inr ?_⟩
      simpa [hτs] using hlen
    | succ n ih =>
      obtain ⟨t₁, U, DU, p, hU, hU0, hDU0, hae, hor⟩ := ih
      by_cases hT : T < t₁
      · exact ⟨t₁, U, DU, p, hU, hU0, hDU0, hae, Or.inl hT⟩
      · have ht₁ : t₁ ≤ T := not_lt.mp hT
        have hge : t₀ + ((n : ℝ) + 1) * τs ≤ t₁ := hor.resolve_left hT
        have hae' : U =ᵐ[volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))] u := by
          rwa [min_eq_left ht₁] at hae
        have hSb1 := hSb hU ht₁ hU0 hDU0 hae'
        obtain ⟨t₁', hlen, U', DU', p', hU', hU0', hDU0', hae2⟩ :=
          lps_continuation_step hc.le hLoc hLH hSerrin ht₀.1 ht₁ hU hU0 hae' hE0
            (hSb1.trans (le_max_left S X₀))
        refine ⟨t₁', U', DU', p', hU',
          (by rw [show (fun x : Vec3 => U' (x, t₀)) = fun x => U (x, t₀) from funext hU0']
              exact hU0),
          (by rw [show (fun x : Vec3 => DU' (x, t₀)) = fun x => DU (x, t₀) from funext hDU0']
              exact hDU0), hae2, Or.inr ?_⟩
        push_cast
        simp only [hτs] at hge ⊢
        nlinarith only [hge, hlen]
  obtain ⟨n, hn⟩ := exists_nat_gt ((T - t₀) / τs)
  obtain ⟨t₁, U, DU, p, hU, hU0, -, hae, hor⟩ := claim n
  have hTt : T < t₁ := by
    rcases hor with h | h
    · exact h
    · have h1 : T - t₀ < (n : ℝ) * τs := by
        have := (div_lt_iff₀ hτpos).1 hn
        linarith only [this]
      nlinarith only [h, h1, hτpos]
  refine ⟨t₁, hTt, U, DU, p, hU, hU0, ?_⟩
  rwa [min_eq_right hTt.le] at hae

/-- A finite-Serrin-norm Leray–Hopf solution on `(0, T)` coincides, from a good time
`t₀` of energy equality, with a strong solution on `[t₀, t₁]` for some `t₁ > T`
(`lem:lps-continuation`). -/
theorem lps_continuation
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hSerrin :
      (∃ s : ℝ, 3 < s ∧
        (∫⁻ t in Ioo (0 : ℝ) T,
          (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
            ((2 * s / (s - 3)) / s)) < ⊤) ∨
      (∫⁻ t in Ioo (0 : ℝ) T,
        (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) T) (hGood : IsLpsGoodTime u Du t₀)
    (hEq₀ : (∫ x : Vec3, ∑ k : Fin 3, u (x, t₀) k * u (x, t₀) k) -
        (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
      -2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
        ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j) :
    ∃ t₁ : ℝ, T < t₁ ∧
      ∃ (U : ParabolicPoint → Vec3) (DU : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ),
        IsLpsStrongSolution t₀ t₁ U DU p ∧
        (fun x : Vec3 => U (x, t₀)) =ᵐ[volume] (fun x : Vec3 => u (x, t₀)) ∧
        U =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))] u := by
  refine lps_continuation_of_local ?_ hLH hSerrin ht₀ hGood hEq₀
  obtain ⟨c, hc, h⟩ := lps_local_strong
  refine ⟨c, hc, fun t b Db hg => ?_⟩
  obtain ⟨τ, hτ, hlb, W, DW, pW, hW, hW0, -⟩ := h t b Db hg
  exact ⟨τ, hτ, hlb, W, DW, pW, hW, hW0⟩

end ESS

end
