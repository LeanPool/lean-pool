/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/

module

public import LeanPool.WordRepTensor.OddCycles
public import LeanPool.WordRepTensor.Embedding
public import LeanPool.WordRepTensor.CycleFolding

/-!
# Problem 5.1 of arXiv:2609.20881v1: `mu (2n+1) × W (2m+1)` and `muExt (2n+1) × W (2m+1)` are not
word-representable (`Problem1Mu`, `Problem1MuExt`, `Problem5_1`)

(Written by Claude, 2026-09-28.) If `n ≥ m`, the graph of the homomorphism of Lemma 1 embeds the
first factor as an induced subgraph; if `n ≤ m`, Lemma 2 embeds `mu (2m+1)`. Both are not
word-representable, and word-representability passes to induced subgraphs.
-/

@[expose] public section

namespace WordRepTensor

/-- Alshammari’s Problem 5.1 for the ordinary Mycielskian. -/
theorem not_wordRepresentable_mycielskian_tensor_wheel :
  ∀ n m : ℕ, 1 ≤ n → 2 ≤ m →
      ¬ WordRepresentable (tensorProd (mu (2 * n + 1)) (wheel (2 * m + 1))) := by
  intro n m hn hm hWR
  rcases le_total m n with hmn | hnm
  · obtain ⟨h⟩ := mycielskian_to_wheel n m hm hmn
    exact mycielskiOddCycleNotWR n hn
      (wordRepresentableOfEmbedding _ _ _ _ (embeddingOfHom _ _ _ _ ⟨h⟩) hWR)
  · exact mycielskiOddCycleNotWR m (by omega)
      (wordRepresentableOfEmbedding _ _ _ _ (mycielskian_embeds_tensor_wheel n m hn hnm hm) hWR)

/-- Alshammari’s Problem 5.1 for the extended Mycielskian. -/
theorem not_wordRepresentable_extended_tensor_wheel :
  ∀ n m : ℕ, 1 ≤ n → 2 ≤ m →
      ¬ WordRepresentable (tensorProd (muExt (2 * n + 1)) (wheel (2 * m + 1))) := by
  intro n m hn hm hWR
  rcases le_total m n with hmn | hnm
  · obtain ⟨h⟩ := extended_to_wheel n m hm hmn
    exact extMycielskiOddCycleNotWR n hn
      (wordRepresentableOfEmbedding _ _ _ _ (embeddingOfHom _ _ _ _ ⟨h⟩) hWR)
  · exact mycielskiOddCycleNotWR m (by omega)
      (wordRepresentableOfEmbedding _ _ _ _
        (mycielskian_embeds_extended_tensor_wheel n m hn hnm hm) hWR)

end WordRepTensor
