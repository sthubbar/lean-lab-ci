/-
AI wrote this Lean code for CODEX task654.
P0037 Section 5.2 page 212, regenerated candidate at index 176.
Every modular witness and every auxiliary prime is checked in Lean.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Pock

namespace LeanLab.DtRS1998.Recut654Prime176

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- The auxiliary Pocklington records for this candidate. -/
def factorChain : List Big.Cert := [(2137, 10, [(2, 3), (3, 1), (89, 1)]),
  (2671, 7, [(2, 1), (3, 1), (5, 1), (89, 1)]),
  (1423, 3, [(2, 1), (3, 2), (79, 1)]),
  (5693, 2, [(2, 2), (1423, 1)]),
  (61099, 2, [(2, 1), (3, 1), (17, 1), (599, 1)]),
  (3671, 13, [(2, 1), (5, 1), (367, 1)]),
  (87296381, 2, [(2, 2), (5, 1), (29, 1), (41, 1), (3671, 1)]),
  (116579, 2, [(2, 1), (7, 1), (11, 1), (757, 1)]),
  (2098423, 13, [(2, 1), (3, 2), (116579, 1)]),
  (1708116323, 5, [(2, 1), (11, 1), (37, 1), (2098423, 1)]),
  (11987, 2, [(2, 1), (13, 1), (461, 1)]),
  (431533, 6, [(2, 2), (3, 2), (11987, 1)]),
  (2589199, 3, [(2, 1), (3, 1), (431533, 1)]),
  (341774269, 2, [(2, 2), (3, 1), (11, 1), (2589199, 1)]),
  (16405164913, 47, [(2, 4), (3, 1), (341774269, 1)]),
  (2797, 2, [(2, 2), (3, 1), (233, 1)]),
  (3181, 7, [(2, 2), (3, 1), (5, 1), (53, 1)]),
  (39824122333, 5, [(2, 2), (3, 1), (373, 1), (2797, 1), (3181, 1)]),
  (6791, 7, [(2, 1), (5, 1), (7, 1), (97, 1)]),
  (13568419, 2, [(2, 1), (3, 3), (37, 1), (6791, 1)]),
  (461326247, 5, [(2, 1), (17, 1), (13568419, 1)]),
  (66430979569, 14, [(2, 4), (3, 2), (461326247, 1)]),
  (1777, 5, [(2, 4), (3, 1), (37, 1)]),
  (4194433, 7, [(2, 7), (3, 2), (11, 1), (331, 1)]),
  (268326267877, 2, [(2, 2), (3, 2), (1777, 1), (4194433, 1)]),
  (2179, 7, [(2, 1), (3, 2), (11, 2)]),
  (625630123, 2, [(2, 1), (3, 3), (13, 1), (409, 1), (2179, 1)]),
  (90090737713, 5, [(2, 4), (3, 2), (625630123, 1)]),
  (360362950853, 2, [(2, 2), (90090737713, 1)]),
  (2029, 2, [(2, 2), (3, 1), (13, 2)]),
  (6217, 5, [(2, 3), (3, 1), (7, 1), (37, 1)]),
  (78167, 5, [(2, 1), (11, 2), (17, 1), (19, 1)]),
  (1972042881863, 5, [(2, 1), (2029, 1), (6217, 1), (78167, 1)]),
  (6481, 7, [(2, 4), (3, 4), (5, 1)]),
  (2731, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1)]),
  (60083, 2, [(2, 1), (11, 1), (2731, 1)]),
  (8313645656051, 2, [(2, 1), (5, 2), (7, 1), (61, 1), (6481, 1), (60083, 1)]),
  (2153, 3, [(2, 3), (269, 1)]),
  (826753, 5, [(2, 7), (3, 1), (2153, 1)]),
  (1187, 2, [(2, 1), (593, 1)]),
  (9497, 3, [(2, 3), (1187, 1)]),
  (23552561, 3, [(2, 4), (5, 1), (31, 1), (9497, 1)]),
  (116832902786599, 3, [(2, 1), (3, 1), (826753, 1), (23552561, 1)]),
  (802642042143935131, 10, [(2, 1), (3, 1), (5, 1), (229, 1), (116832902786599, 1)])]

/-- Every listed auxiliary number is prime by its own Pocklington witness. -/
theorem factor_primes : ∀ p ∈ factorChain.map Prod.fst, p.Prime := by
  intro p hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact Big.chainP_sound factorChain [] (by simp) (by decide +kernel) c hc

/-- The factored part for certificate node 0. -/
def factors_0 : List (ℕ × ℕ) := [(2, 2), (3, 1), (47, 1), (263, 1), (277, 1), (268326267877, 1), (8313645656051, 1)]

/-- Certificate node 0 is prime by its explicit modular witnesses. -/
theorem prime_node_0 : (6188066116959254866696645747763588520743102368639706156738670809844894170173 : ℕ).Prime := by
  have hprimes : ∀ x ∈ factors_0, x.1.Prime := by
    intro x hx
    simp only [factors_0, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
  apply Recut654Pock.prime_of_factor_divisibility 6188066116959254866696645747763588520743102368639706156738670809844894170173 91657777374235430897807343921828 70808095422748485583678025990430
    (by decide +kernel) (by decide +kernel)
  · exact Recut654Pock.factor_congruence 6188066116959254866696645747763588520743102368639706156738670809844894170173 5 252 factors_0
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hprimes
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

/-- The factored part for certificate node 1. -/
def factors_1 : List (ℕ × ℕ) := [(2, 3), (67, 1), (787, 1), (5693, 1), (16405164913, 1), (39824122333, 1), (6188066116959254866696645747763588520743102368639706156738670809844894170173, 1)]

/-- Certificate node 1 is prime by its explicit modular witnesses. -/
theorem prime_node_1 : (9708730927651097213718585640300700667307581808404690193641487774807777957853107587556165613111326934578793 : ℕ).Prime := by
  have hprimes : ∀ x ∈ factors_1, x.1.Prime := by
    intro x hx
    simp only [factors_1, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact prime_node_0
  exact Big.pock 9708730927651097213718585640300700667307581808404690193641487774807777957853107587556165613111326934578793 3 353 factors_1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hprimes (by decide +kernel) (by decide +kernel)

/-- The factored part for certificate node 2. -/
def factors_2 : List (ℕ × ℕ) := [(2, 1), (17, 1), (2137, 1), (2671, 1), (87296381, 1), (66430979569, 1), (9708730927651097213718585640300700667307581808404690193641487774807777957853107587556165613111326934578793, 1)]

/-- Certificate node 2 is prime by its explicit modular witnesses. -/
theorem prime_node_2 : (10926641354562737611735230522390137744609672648989085446840741302214132910334251079012246884375864535057029057463241075216654725155687 : ℕ).Prime := by
  have hprimes : ∀ x ∈ factors_2, x.1.Prime := by
    intro x hx
    simp only [factors_2, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact prime_node_1
  exact Big.pock 10926641354562737611735230522390137744609672648989085446840741302214132910334251079012246884375864535057029057463241075216654725155687 5 442 factors_2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hprimes (by decide +kernel) (by decide +kernel)

/-- The factored part for certificate node 3. -/
def factors_3 : List (ℕ × ℕ) := [(2, 1), (360362950853, 1), (1972042881863, 1), (10926641354562737611735230522390137744609672648989085446840741302214132910334251079012246884375864535057029057463241075216654725155687, 1)]

/-- Certificate node 3 is prime by its explicit modular witnesses. -/
theorem prime_node_3 : (15530061408905575557787051147190711366814482764661143837087177597307331780271511047116319900858393328655085988804341929507602598192563278910444940060187826987 : ℕ).Prime := by
  have hprimes : ∀ x ∈ factors_3, x.1.Prime := by
    intro x hx
    simp only [factors_3, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact prime_node_2
  exact Big.pock 15530061408905575557787051147190711366814482764661143837087177597307331780271511047116319900858393328655085988804341929507602598192563278910444940060187826987 2 523 factors_3
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hprimes (by decide +kernel) (by decide +kernel)

/-- The factored part for certificate node 4. -/
def factors_4 : List (ℕ × ℕ) := [(2, 1), (31, 1), (167, 1), (727, 1), (1708116323, 1), (15530061408905575557787051147190711366814482764661143837087177597307331780271511047116319900858393328655085988804341929507602598192563278910444940060187826987, 1)]

/-- Certificate node 4 is prime by its explicit modular witnesses. -/
theorem prime_node_4 : (199679365230800549930336263537623859232656460513674518470861410299035652351583109818901964992858706037225161980782882063401844275723349334588705316660400759228304837715077759 : ℕ).Prime := by
  have hprimes : ∀ x ∈ factors_4, x.1.Prime := by
    intro x hx
    simp only [factors_4, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact prime_node_3
  exact Big.pock 199679365230800549930336263537623859232656460513674518470861410299035652351583109818901964992858706037225161980782882063401844275723349334588705316660400759228304837715077759 13 576 factors_4
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hprimes (by decide +kernel) (by decide +kernel)

/-- The factored part for certificate node 5. -/
def factors_5 : List (ℕ × ℕ) := [(2, 2), (3, 1), (23, 1), (37, 1), (61099, 1), (802642042143935131, 1), (199679365230800549930336263537623859232656460513674518470861410299035652351583109818901964992858706037225161980782882063401844275723349334588705316660400759228304837715077759, 1)]

/-- Certificate node 5 is prime by its explicit modular witnesses. -/
theorem prime_node_5 : (100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000162329853 : ℕ).Prime := by
  have hprimes : ∀ x ∈ factors_5, x.1.Prime := by
    intro x hx
    simp only [factors_5, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact prime_node_4
  exact Big.pock 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000162329853 5 665 factors_5
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hprimes (by decide +kernel) (by decide +kernel)

/-- LEAF: The regenerated candidate at index 176 is prime. -/
theorem candidate176_prime : (10 ^ 200 + 162329853 : ℕ).Prime := prime_node_5

end LeanLab.DtRS1998.Recut654Prime176
