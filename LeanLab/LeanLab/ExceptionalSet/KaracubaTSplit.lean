/-
KaracubaTSplit: superseded within the same part 4 of 2026-11-12. Its content, the split of the
LEAF `KaracubaCore.leaf_T_bound` along Karacuba, Trudy Mat. Inst. Steklov 112 (1971), p. 248,
was moved into `KaracubaCore.lean` once its LEAF `leafT_lemma2` was proved from Lemma 2, so
that `KaracubaCore.leaf_T_bound` itself is now discharged one for one by `karTBound_of_split`,
with no import cycle. Keeping the declarations here too would clash with the core names, so
this file now holds only this note and the import; the first version is in git history,
commit dad867de6e.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.KaracubaCore
