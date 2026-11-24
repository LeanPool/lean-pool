/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffCollarBuild

/-!
# Graph Minors VII, (5.9)

This is the end of the proof of (5.9), pages 233-237. It puts together the core and the collar at
each cuff, with the numbers of the paper, and then uses `isGFeasible_of_collars`.

(5.9) rests on (4.6), which is `theorem_4_6`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The number `v(Σ, k)` has the form `6X + 2k` with `X ≥ 1`, if `Σ` has at least two cuffs. -/
theorem vSurface_form {a b c : ℕ} (hc : 2 ≤ c) (he : Nonempty (S ≃ₜ SurfaceModel a b c))
  (k : ℕ) : ∃ X, 1 ≤ X ∧ vSurface S k = 6 * X + 2 * k := by
  have hne : {v : ℕ | ∃ a b c : ℕ, Nonempty (S ≃ₜ SurfaceModel a b c) ∧ v
    = vModel a b c k}.Nonempty := ⟨_, a, b, c, he, rfl⟩
  obtain ⟨a', b', c', he', hv⟩ := Nat.sInf_mem hne
  have hc' : c' = c := by
    rw [← ncard_cuffs_of_homeomorph_surfaceModel he', ncard_cuffs_of_homeomorph_surfaceModel he]
  refine ⟨(2 * a' + b' + c' - 1) * (wMaxModel a' b' c' k + 2 * muModel a' b' c' k + 1), ?_, ?_⟩
  · exact Nat.mul_pos (by omega) (by omega)
  · change sInf _ = _
    rw [hv, vModel, mul_assoc]

/-- The sums of (5.9). -/
theorem collar_numbers {k X K K' α A P v h : ℕ} (hv : v = 6 * X + 2 * k) (hX : 1 ≤ X) (hk : 2 ≤ k)
  (hK : K + 2 ≤ 2 * k) (hA : A + 2 * v ≤ 2 * P) (hA' : v ≤ A) (hP : 2 * v ≤ P) (hα : 9 * P < α)
    (hK' : K' ≤ 2 * k) (hh : h = v / 2) :
    A + (h + K + 2 + 3) + 1 ≤ 2 * P ∧ A + (h + K + 2 + 3) < α ∧ A + (A + (h + K + 2 + 3)) < α ∧ A +
      (h + K + 2 + 3) + K' < α ∧ 9 * (A + (h + K + 2 + 3) + 1) ≤ 2 * α := by
  have h1 : v / 2 = 3 * X + k := by omega
  omega

/-- Graph Minors VII, (5.9) (pages 233–237):
"(5.9) *Let $\Sigma \cong \Sigma(a, b, c)$, where $c \ge 2$ and $(a, b, c) \ne (0, 0, 2)$. Let
$k \ge 0$ be an integer. Let $G$ be a boundary-linked proper graph in $\Sigma$ with
$|V(G) \cap \mathrm{bd}(\Sigma)| \le 2k$ and with $\alpha(G) > 9k v(\Sigma, k)$, such that for
every cuff $C$, $|V(G) \cap C| \ge 2$. Let $H$ be a forest in $\Sigma$ with
$V(G) \cap \mathrm{bd}(\Sigma) = V(H) \cap \mathrm{bd}(\Sigma)$. Then $H$ is $G$-feasible.*"

See `IsCuffCore` for the parts of the proof at one cuff, `IsCuffCollar` for what they give, and
`isGFeasible_of_collars` for the final step. -/
theorem theorem_5_9_proof
    [T1Space S] (hS : IsSurface S) {a b c : ℕ} (hc : 2 ≤ c) (hne : (a, b, c) ≠ (0, 0, 2))
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (k : ℕ) (G H : Drawing S)
    (hBL : IsBoundaryLinked G) (hbd_card : (G.V ∩ bd S).ncard ≤ 2 * k)
    (halpha : 9 * k * vSurface S k < alpha G)
    (hcuff2 : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard)
    (hH : IsSurfaceForest H) (hbd_eq : G.V ∩ bd S = H.V ∩ bd S) :
    IsGFeasible G H := by
  classical
  have : ConnectedSpace S := connectedSpace_of_model he
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have habc : 3 ≤ 3 * a + 3 * b + c := by
    by_contra hlt
    have h1 : a = 0 := by omega
    have h2 : b = 0 := by omega
    have h3 : c = 2 := by omega
    exact hne (by rw [h1, h2, h3])
  have hcyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2) := not_cylinder_of_model habc he
  have hG := hBL.1
  have hnc := ncard_cuffs_of_homeomorph_surfaceModel he
  obtain ⟨X, hX, hv⟩ := vSurface_form hc he k
  set v := vSurface S k with hvdef
  have hfinV : ∀ A : Set S, (G.V ∩ A).Finite := fun A => G.finite_V.subset inter_subset_left
  have hKsum : ∀ C ∈ cuffs S, (G.V ∩ C).ncard + 2 ≤ 2 * k := fun C hC => by
    obtain ⟨C₁, hC₁, hne₁⟩ := exists_ne_of_one_lt_ncard (s := cuffs S) (by rw [hnc]; omega) C
    have hd : Disjoint (G.V ∩ C) (G.V ∩ C₁) := (disjoint_cuffs hC hC₁ hne₁.symm).mono
      inter_subset_right inter_subset_right
    have h1 := ncard_union_eq hd (hfinV C) (hfinV C₁)
    have hsub : (G.V ∩ C) ∪ (G.V ∩ C₁) ⊆ G.V ∩ bd S := union_subset (inter_subset_inter_right _
      (cuff_subset_bd hC)) (inter_subset_inter_right _ (cuff_subset_bd hC₁))
    have h2 := ncard_le_ncard hsub (hfinV _)
    have h3 := hcuff2 C₁ hC₁
    omega
  have hC₀ : (cuffs S).Nonempty := nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨C₀, hC₀m⟩ := hC₀
  have hk : 2 ≤ k := by
    have h1 := hKsum C₀ hC₀m
    have h2 := hcuff2 C₀ hC₀m
    omega
  set P := k * v with hPdef
  have hα : 9 * P < alpha G := by
    have h1 : 9 * P = 9 * k * v := by rw [hPdef]; ring
    omega
  have hP : 2 * v ≤ P := by
    rw [hPdef]
    exact Nat.mul_le_mul_right v hk
  have hcol : ∀ c' : cuffs S, ∃ (ι : Type u) (_ : Finite ι) (Mo AC Mo₂ Mo₃ : Set S) (φ : ι → ℝ × ℝ
    → S) (g f : ι → ℝ → ℝ) (Tr : S → Drawing S), IsCuffCollar G c'.1 (2 * P) v Mo AC Mo₂ Mo₃ φ g f
      Tr := fun c' => by
    obtain ⟨C, hC⟩ := c'
    obtain ⟨T, tT, j, D, hcap, hbT⟩ := exists_cappedCuff hS hC
    have hT := hcap.isSurface
    have : T2Space T := hT.2.1
    have hns : ¬ IsSphere T := not_isSphere_cap hS habc he hcap
    have hK := hKsum C hC
    have hK2 := hcuff2 C hC
    have hA : v * (G.V ∩ C).ncard + 2 * v ≤ 2 * P := by
      have h1 : v * ((G.V ∩ C).ncard + 2) ≤ v * (2 * k) := Nat.mul_le_mul_left v hK
      rw [hPdef]
      nlinarith
    have hA' : v ≤ v * (G.V ∩ C).ncard := Nat.le_mul_of_pos_right v (by omega)
    have hnum := fun K' (hK' : K' ≤ 2 * k) => collar_numbers (K' := K') hv hX hk hK hA hA' hP hα
      hK' rfl
    obtain ⟨n1, n2, n3, -, n5⟩ := hnum 0 (by omega)
    obtain ⟨Y, E₀, Δ', Do, Nk, Bo, R, x, t, Q, L, El, hcore⟩ := exists_cuff_core hS he habc hcyl hC
      hcap hbT hG hns hBL (v := v) (by omega) (by omega) hK2 (by omega) n2 n3 (fun C₁ hC₁ hne₁ => by
      have h1 := hKsum C₁ hC₁
      exact (hnum _ (by omega)).2.2.2.1) n5
    have hcore' : IsCuffCore G C j D (2 * P) v Y E₀ Δ' Do Nk Bo R x t Q L El := { hcore with
      reach := fun y hy => by
        obtain ⟨X', hX', hyX⟩ := hcore.reach y hy
        exact ⟨X', ⟨hX'.1, hX'.2.1, hX'.2.2.1, hX'.2.2.2.1, hX'.2.2.2.2.trans (by omega)⟩, hyX⟩ }
    exact hcore'.exists_collar hS hC hcap hbT hG hns
  choose ι hfin Mo AC Mo₂ Mo₃ φ g f Tr hcoll using hcol
  have : ∀ c', Finite (ι c') := hfin
  have hvP : v ≤ P := by omega
  exact isGFeasible_of_collars hS (by omega) hcyl hG hbd_card hcoll (by omega) (by omega)
    (by omega) (by omega) hcuff2 hH hbd_eq

end GraphMinor.GM07
