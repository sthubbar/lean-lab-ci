import LeanLab.ChenDoubleSieve.Task562ListData
import LeanLab.ChenDoubleSieve.Task562Polynomial

/-!
Kernel checks for the polynomial enclosure in Wu 2004 Lemma 5.2 page 26.
Source: https://arxiv.org/pdf/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LeanLab.ChenDoubleSieve.Task562

/-- The explicit coefficient list has the exact stated rational moment.
Wu 2004 page 26, derived finite arithmetic certificate. -/
theorem r3Terms_moment : listMomentQ r3Terms (100 / 291) (2 / 5) =
    (1331032446698958906352180399753674063507603432285078448678967637782243 /
      30833552085189034950799979968436065035185877655749765190333493625000000000 : ℚ) := by
  decide +kernel

end LeanLab.ChenDoubleSieve.Task562
