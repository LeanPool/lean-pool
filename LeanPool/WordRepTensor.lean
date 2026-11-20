/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/

module

public import LeanPool.WordRepTensor.WheelProducts
public import LeanPool.WordRepTensor.MycielskiProducts

/-!
# Non-word-representability of tensor products of Mycielski graphs

Source: url:https://github.com/Horace-Maxwell/ai4math-results/blob/65dd8899dfe1abf289282f141222057d5593ca02/papers/wordrep-tensor/note.pdf
Authors: Horace Dong
Status: verified
Main declarations: `WordRepTensor.not_wordRepresentable_mycielskian_tensor_wheel`,
  `WordRepTensor.not_wordRepresentable_extended_tensor_wheel`,
  `WordRepTensor.not_wordRepresentable_mycielskian_tensor_extended`,
  `WordRepTensor.not_wordRepresentable_extended_tensor_extended`
Tags: graph-products, mycielski-graphs, word-representability
MSC: 05C76, 05C62
-/
