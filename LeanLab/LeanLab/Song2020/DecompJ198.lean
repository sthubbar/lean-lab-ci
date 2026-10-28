import LeanLab.Song2020.Consequences139
import LeanLab.Song2020.Decomp139b

namespace LeanLab.Song2020.DecompJ198
open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- LEAF. Page 2. The lower bound for the singular series. -/
theorem leaf_singular_lower : SingularLower :=
  singular_lower

/-- LEAF. Page 9. The asymptotic formula for the integral R(n). -/
theorem leaf_asymptotic : Asymptotic :=
  song_asymptotic

/-- LEAF. Page 9. The deduction of Theorem 1 from the asymptotic formula. -/
theorem leaf_songTheorem1_of_asymptotic (H : Asymptotic) : SongTheorem1 :=
  songTheorem1_of_asymptotic139 H

/-- Assembly of Theorem 1 from the leaves. -/
theorem song_theorem1_decomposed : SongTheorem1 :=
  leaf_songTheorem1_of_asymptotic leaf_asymptotic

end

end LeanLab.Song2020.DecompJ198
