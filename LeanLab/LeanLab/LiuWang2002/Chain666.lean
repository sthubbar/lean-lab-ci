import LeanLab.LiuWang2002.Chain666Core
import LeanLab.LiuWang2002.Guard666A
import LeanLab.LiuWang2002.Guard666B
import LeanLab.LiuWang2002.Guard666C
import LeanLab.LiuWang2002.Guard666D
import LeanLab.Ported.Prove2Me.TaoFivePrimes_axler_chain_c1
import LeanLab.Ported.Prove2Me.TaoFivePrimes_axler_chain_c2
import LeanLab.Ported.Prove2Me.TaoFivePrimes_axler_chain_c3a

/-!
The same accepted Axler groups supply the missing c5 range.
Source Schoenfeld 1976 page 356 display 5.1 star, derived finite certificates.
No new primality data are introduced.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task666
open LeanLab.Ported.Prove2Me.Task666
open AxlerChain AxlerTheta
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


theorem primorial_c5_chain (n : ℕ) (hn : 16000000 < n) (hn' : n ≤ 32000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  have h0 := (TaoFivePrimes.axler_chain_c3a
    (TaoFivePrimes.axler_chain_c2 TaoFivePrimes.axler_chain_c1.1).1).1
  have h1 := grp_state_of gc3b_0 check_gc3b_0 wf_gc3b_0 h0.1 h0.2
  have h2 := grp_state_of gc3b_1 check_gc3b_1 wf_gc3b_1 h1.1 h1.2
  have h3 := grp_state_of gc4a1_0 check_gc4a1_0 wf_gc4a1_0 h2.1 h2.2
  by_cases hn0 : n ≤ 16795053
  · exact guardGroup_bound 16000000 gc3b_0 check_gc3b_0 wf_gc3b_0 guard_c3b_0
      h0.1 h0.2 n hn (by change 8409485 < n; omega) hn0
  by_cases hn1 : n ≤ 17387265
  · exact guardGroup_bound 16000000 gc3b_1 check_gc3b_1 wf_gc3b_1 guard_c3b_1
      h1.1 h1.2 n hn (by change 16795053 < n; omega) hn1
  by_cases hn2 : n ≤ 25762666
  · exact guardGroup_bound 16000000 gc4a1_0 check_gc4a1_0 wf_gc4a1_0 guard_c4a1_0
      h2.1 h2.2 n hn (by change 17387265 < n; omega) hn2
  exact guardGroup_bound 16000000 gc4a2_0 check_gc4a2_0 wf_gc4a2_0 guard_c4a2_0
    h3.1 h3.2 n hn (by change 25762666 < n; omega) (by change n ≤ 34129386; omega)

end LeanLab.LiuWang2002.Task666
#print axioms LeanLab.LiuWang2002.Task666.guardGo_sound
#print axioms LeanLab.LiuWang2002.Task666.guardGroup_bound
#print axioms LeanLab.LiuWang2002.Task666.guard_c3b_0
#print axioms LeanLab.LiuWang2002.Task666.guard_c3b_1
#print axioms LeanLab.LiuWang2002.Task666.guard_c4a1_0
#print axioms LeanLab.LiuWang2002.Task666.guard_c4a2_0
#print axioms LeanLab.LiuWang2002.Task666.primorial_c5_chain
