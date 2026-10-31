/-
Saouter 1998, P0018, unit U-0952, run 20261018T1404Z-22216.
An independent check of Table 1: the first 100 rungs of Saouter's ladder are prime by the
paper's own Theorem 2 test, proved in Theorem2.lean, one modular power per rung, with no Lucas
certificate. Table1.lean proved the same 100 primes by Lucas certificates.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Saouter1998.Table1
import LeanLab.Saouter1998.Theorem2

namespace LeanLab.Saouter1998.Table1Thm2

open LeanLab.Saouter1998.Paper LeanLab.Saouter1998.Thm2

/-- R = 10 k + 3 for each Table 1 value k, with the square witness for r^2 - 8s. -/
def W : List (ℕ × ℕ) := [(33, 0), (95373, 0), (190593, 0), (285753, 0), (381073, 0), (476223, 0), (571473, 0), (666513, 0), (761823, 0), (857133, 0), (952303, 0), (1047643, 0), (1142973, 0), (1238193, 0), (1333473, 0), (1428793, 0), (1524153, 0), (1619503, 0), (1714713, 0), (1810033, 0), (1905013, 0), (2000223, 0), (2095413, 0), (2190663, 0), (2285943, 0), (2381043, 0), (2476243, 0), (2571573, 0), (2666833, 0), (2762193, 0), (2857273, 0), (2952583, 0), (3047853, 0), (3143053, 0), (3238393, 0), (3333553, 0), (3428823, 0), (3524053, 0), (3619413, 0), (3714673, 0), (3810003, 0), (3905223, 0), (4000483, 0), (4095753, 0), (4190983, 0), (4286043, 0), (4381323, 0), (4476633, 0), (4571943, 0), (4667103, 0), (4762423, 0), (4857613, 0), (4952913, 0), (5048133, 0), (5143473, 0), (5238783, 0), (5333973, 0), (5429323, 0), (5524663, 0), (5619913, 0), (5715193, 0), (5810383, 0), (5905653, 0), (6000903, 0), (6096253, 0), (6191593, 0), (6286753, 0), (6381963, 0), (6477043, 0), (6572323, 0), (6667513, 0), (6762853, 0), (6858213, 0), (6953533, 0), (7048873, 0), (7144053, 0), (7239363, 0), (7334523, 0), (7429833, 0), (7524853, 0), (7619893, 0), (7715203, 0), (7810543, 0), (7905883, 0), (8001163, 0), (8096233, 0), (8191513, 0), (8286793, 0), (8381983, 0), (8477263, 88654), (8572323, 183714), (8667483, 278874), (8762683, 374074), (8858043, 469434), (8953333, 564724), (9048513, 659904), (9143773, 755164), (9239103, 850494), (9334453, 945844), (9429733, 1041124)]

theorem W_ok : W.all (fun x => thm2B x.1 x.2) = true := by decide +kernel

theorem W_match : W.map Prod.fst = LeanLab.Saouter1998.Table1.T1.map (fun k => 10 * k + 3) := by
  decide +kernel

/-- Every Table 1 rung is prime by Theorem 2. -/
theorem table1_prime_thm2 : ∀ k ∈ LeanLab.Saouter1998.Table1.T1, (N k).Prime := by
  intro k hk
  have hmem : 10 * k + 3 ∈ W.map Prod.fst := by
    rw [W_match]; exact List.mem_map_of_mem hk
  obtain ⟨x, hx, hx1⟩ := List.mem_map.mp hmem
  have h := prime_of_thm2B (List.all_eq_true.mp W_ok x hx)
  rw [N_form, ← hx1]
  exact h

end LeanLab.Saouter1998.Table1Thm2
