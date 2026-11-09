import LeanLab.LZCesaroShort.DecompJ209

/-!
AI wrote the Lean code. Binary Goldbach is open.
Source: https://arxiv.org/abs/1606.00869v2 page 3, Lemma 3.
The written proof is https://arxiv.org/abs/1011.3198 page 3, Lemma 3.
The sealed cited declaration moves here with its exact statement preserved.
DecompJ209 supplies the unconditional moment proof.
-/

namespace LeanLab.LZCesaroShort

/-- Lemma 3, from the existing unconditional raw moment and Parseval proof. -/
theorem lz_lemma3 : Lemma3 := lz_lemma3_decomp_assembly

end LeanLab.LZCesaroShort
