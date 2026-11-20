/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/

module

public import LeanPool.WordRepTensor.Graphs

/-!
# The folds, and the frozen statements `Lemma1Mu`, `Lemma1MuExt`, `Lemma2Mu`, `Lemma2MuExt`

(Written by Claude, 2026-09-28.) For odd `K ≥ k ≥ 3` the fold `Fin K → Fin k` is the identity
below `k` and then alternates between `k - 2` and `k - 1`; it maps the cycle `C_K` onto `C_k`.
-/

@[expose] public section

namespace WordRepTensor

open SimpleGraph

/-- The fold on values. -/
def foldVal (k i : ℕ) : ℕ := if i < k then i else if (i - k) % 2 = 0 then k - 2 else k - 1

/-- The fold `Fin K → Fin k`. -/
def fold {K k : ℕ} (hk : 3 ≤ k) (i : Fin K) : Fin k :=
  ⟨foldVal k i.val, by unfold foldVal; split_ifs <;> omega⟩

theorem fold_adj {K k : ℕ} (hk : 3 ≤ k) (hkK : k ≤ K) (hK : K % 2 = 1) (hk2 : k % 2 = 1)
    {i j : Fin K} (h : (cycleGraph K).Adj i j) : (cycleGraph k).Adj (fold hk i) (fold hk j) := by
  have hi := i.isLt
  have hj := j.isLt
  rw [cyc_adj_iff' (by omega)] at h
  rw [cyc_adj_iff' hk]
  simp only [fold, foldVal]
  split_ifs <;> omega

/-! ## Lemma 1: homomorphisms into the wheel -/

section Lemma1

variable {k K : ℕ}

/-- Fold the top row onto the rim and send the root to the wheel hub. -/
def homMu (hK : 3 ≤ K) : (Fin k ⊕ Fin k ⊕ Unit) → (Fin K ⊕ Unit)
  | .inl i => .inl (fold hK i)
  | .inr (.inl i) => .inl (fold hK i)
  | .inr (.inr _) => .inr ()

/-- Fold the top row onto the rim and send every shadow to the wheel hub. -/
def homExt (hK : 3 ≤ K) : (Fin k ⊕ Fin k ⊕ Unit) → (Fin K ⊕ Unit)
  | .inl i => .inl (fold hK i)
  | .inr (.inl _) => .inr ()
  | .inr (.inr _) => .inl ⟨0, by omega⟩

theorem homMu_adj (hK : 3 ≤ K) (hKk : K ≤ k) (hk : k % 2 = 1) (hK2 : K % 2 = 1)
    (a b : Fin k ⊕ Fin k ⊕ Unit) (h : (mu k).Adj a b) : (wheel K).Adj (homMu
    hK a) (homMu hK b) := by
  rcases a with i | i | u <;> rcases b with j | j | v
  · exact (wheel_adj_inl_inl _ _).mpr (fold_adj hK hKk hk hK2 ((myc_adj_inl_inl _ i j).mp h))
  · exact (wheel_adj_inl_inl _ _).mpr (fold_adj hK hKk hk hK2 ((myc_adj_inl_sh _ i j).mp h))
  · exact absurd h (myc_not_adj_inl_root _ i v)
  · exact (wheel_adj_inl_inl _ _).mpr
      (fold_adj hK hKk hk hK2 ((myc_adj_sh_inl _ j i).mp h)).symm
  · exact absurd h (myc_not_adj_sh_sh _ i j)
  · exact wheel_adj_inl_inr _ _
  · exact absurd h (myc_not_adj_root_inl _ j u)
  · exact wheel_adj_inr_inl _ _
  · exact absurd h (myc_not_adj_root_root _ u v)

theorem homExt_adj (hK : 3 ≤ K) (hKk : K ≤ k) (hk : k % 2 = 1) (hK2 : K % 2 = 1)
    (a b : Fin k ⊕ Fin k ⊕ Unit) (h : (muExt k).Adj a b) :
    (wheel K).Adj (homExt hK a) (homExt hK b) := by
  rcases a with i | i | u <;> rcases b with j | j | v
  · exact (wheel_adj_inl_inl _ _).mpr (fold_adj hK hKk hk hK2 ((ext_adj_inl_inl _ i j).mp h))
  · exact wheel_adj_inl_inr _ _
  · exact absurd h (ext_not_adj_inl_root _ i v)
  · exact wheel_adj_inr_inl _ _
  · exact absurd h (ext_not_adj_sh_sh _ i j)
  · exact wheel_adj_inr_inl _ _
  · exact absurd h (ext_not_adj_root_inl _ j u)
  · exact wheel_adj_inl_inr _ _
  · exact absurd h (ext_not_adj_root_root _ u v)

end Lemma1

theorem mycielskian_to_wheel :
  ∀ n m : ℕ, 2 ≤ m → m ≤ n → Nonempty (mu (2 * n + 1) →g wheel (2 * m + 1)) := by
  intro n m hm hmn
  exact ⟨⟨homMu (by omega : 3 ≤ 2 * m + 1),
    fun {a b} h => homMu_adj (by omega) (by omega) (by omega) (by omega) a b h⟩⟩

theorem extended_to_wheel :
  ∀ n m : ℕ, 2 ≤ m → m ≤ n → Nonempty (muExt (2 * n + 1) →g wheel (2 * m + 1)) := by
  intro n m hm hmn
  exact ⟨⟨homExt (by omega : 3 ≤ 2 * m + 1),
    fun {a b} h => homExt_adj (by omega) (by omega) (by omega) (by omega) a b h⟩⟩

/-! ## Lemma 2: an induced copy of `mu K` -/

section Lemma2

variable {k K : ℕ}

/-- Pair a vertex of the longer Mycielskian with its folded image and its wheel coordinate. -/
def emb2 (hk : 3 ≤ k) : (Fin K ⊕ Fin K ⊕ Unit) → (Fin k ⊕ Fin k ⊕ Unit) × (Fin K ⊕ Unit)
  | .inl i => (.inl (fold hk i), .inl i)
  | .inr (.inl i) => (.inr (.inl (fold hk i)), .inl i)
  | .inr (.inr _) => (.inr (.inr ()), .inr ())

theorem emb2_inj (hk : 3 ≤ k) : Function.Injective (emb2 (K := K) hk) := by
  intro a b h
  rcases a with i | i | u <;> rcases b with j | j | v <;> simp_all [emb2]

theorem emb2_adj_mu (hk : 3 ≤ k) (hkK : k ≤ K) (hk2 : k % 2 = 1) (hK2 : K % 2 = 1)
    (a b : Fin K ⊕ Fin K ⊕ Unit) :
    (tensorProd (mu k) (wheel K)).Adj (emb2 hk a) (emb2 hk b) ↔ (mu K).Adj a b := by
  rw [tensorProd_adj]
  rcases a with i | i | u <;> rcases b with j | j | v
  · simp only [emb2, mu, myc_adj_inl_inl, wheel_adj_inl_inl]
    exact ⟨fun h => h.2, fun h => ⟨fold_adj hk hkK hK2 hk2 h, h⟩⟩
  · simp only [emb2, mu, myc_adj_inl_sh, wheel_adj_inl_inl]
    exact ⟨fun h => h.2, fun h => ⟨fold_adj hk hkK hK2 hk2 h, h⟩⟩
  · simp [emb2, mu, myc_not_adj_inl_root]
  · simp only [emb2, mu, myc_adj_sh_inl, wheel_adj_inl_inl]
    exact ⟨fun h => h.2.symm, fun h => ⟨fold_adj hk hkK hK2 hk2 h, h.symm⟩⟩
  · simp [emb2, mu, myc_not_adj_sh_sh]
  · simp [emb2, mu, myc_adj_sh_root, wheel_adj_inl_inr]
  · simp [emb2, mu, myc_not_adj_root_inl]
  · simp [emb2, mu, myc_adj_root_sh, wheel_adj_inr_inl]
  · simp [emb2, mu]

theorem emb2_adj_ext (hk : 3 ≤ k) (hkK : k ≤ K) (hk2 : k % 2 = 1) (hK2 : K % 2 = 1)
    (a b : Fin K ⊕ Fin K ⊕ Unit) :
    (tensorProd (muExt k) (wheel K)).Adj (emb2 hk a) (emb2 hk b) ↔ (mu K).Adj a b := by
  rw [tensorProd_adj]
  rcases a with i | i | u <;> rcases b with j | j | v
  · simp only [emb2, mu, muExt, myc_adj_inl_inl, ext_adj_inl_inl, wheel_adj_inl_inl]
    exact ⟨fun h => h.2, fun h => ⟨fold_adj hk hkK hK2 hk2 h, h⟩⟩
  · simp only [emb2, mu, muExt, myc_adj_inl_sh, ext_adj_inl_sh, wheel_adj_inl_inl]
    exact ⟨fun h => h.2, fun h => ⟨(fold_adj hk hkK hK2 hk2 h).ne, h⟩⟩
  · simp [emb2, mu, muExt, myc_not_adj_inl_root, ext_not_adj_inl_root]
  · simp only [emb2, mu, muExt, myc_adj_sh_inl, ext_adj_sh_inl, wheel_adj_inl_inl]
    exact ⟨fun h => h.2.symm, fun h => ⟨(fold_adj hk hkK hK2 hk2 h).ne, h.symm⟩⟩
  · simp [emb2, mu, muExt, myc_not_adj_sh_sh, ext_not_adj_sh_sh]
  · simp [emb2, mu, muExt, myc_adj_sh_root, ext_adj_sh_root, wheel_adj_inl_inr]
  · simp [emb2, mu, muExt, myc_not_adj_root_inl, ext_not_adj_root_inl]
  · simp [emb2, mu, muExt, myc_adj_root_sh, ext_adj_root_sh, wheel_adj_inr_inl]
  · simp [emb2, mu, muExt]

end Lemma2

theorem mycielskian_embeds_tensor_wheel :
  ∀ n m : ℕ, 1 ≤ n → n ≤ m → 2 ≤ m →
      Nonempty (mu (2 * m + 1) ↪g tensorProd (mu (2 * n + 1)) (wheel (2 * m + 1))) := by
  intro n m hn hnm hm
  exact ⟨⟨⟨emb2 (by omega : 3 ≤ 2 * n + 1), emb2_inj _⟩,
    fun {a b} => emb2_adj_mu (by omega) (by omega) (by omega) (by omega) a b⟩⟩

theorem mycielskian_embeds_extended_tensor_wheel :
  ∀ n m : ℕ, 1 ≤ n → n ≤ m → 2 ≤ m →
      Nonempty (mu (2 * m + 1) ↪g tensorProd (muExt (2 * n + 1)) (wheel (2 * m + 1))) := by
  intro n m hn hnm hm
  exact ⟨⟨⟨emb2 (by omega : 3 ≤ 2 * n + 1), emb2_inj _⟩,
    fun {a b} => emb2_adj_ext (by omega) (by omega) (by omega) (by omega) a b⟩⟩

end WordRepTensor
