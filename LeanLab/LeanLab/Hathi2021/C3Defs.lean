/-
P0080 Hathi 2021, arXiv 2109.13174v3, page 11: the constant
`c₃ = ∏_{p > 5} (1 + 1/c(p))/(1 + 1/(p - 1))`, definitions and the chain lemmas for
`c₃ ≤ 1.3904`. The kernel windows are in C3W*.lean, the assembly in C3.lean.
Unit U-6154, CLOUD 20261020T0717Z-cloud37. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

Head: a rounded-up chain over the survivors `n` of the mod 30 wheel and of trial division by the
primes 7 to 1423, `7 ≤ n < 2000007`. Every prime above 5 survives; a composite survivor only adds a
factor `1 + ε(n) > 1`, so the chain bounds the product over primes from above. Tail: for
`n ≥ 2000007` prime to 30, `ε(n) ≤ 5.01/n² ≤ (5.01/30)(1/(n - 15) - 1/(n + 15))`, telescoped in each
of the 8 classes mod 30. Generator gen/c3_chain_U6154.py.
-/
import LeanLab.Hathi2021.Lemma31Consts

set_option maxRecDepth 200000

namespace LeanLab.Hathi2021.C3
open Real Finset LeanLab.Hathi2021.Lemma31Consts

/-- `1 + ε(n)` by the class of `n` mod 4, pages 5 and 11. -/
noncomputable def epsF (n : ℕ) : ℝ := if n % 4 = 3 then onePlusEps3 n else onePlusEps1 n

/-- `c₃ = ∏_{p > 5} (1 + 1/c(p))/(1 + 1/(p - 1))`, page 11. -/
noncomputable def c3 : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 5 < p}, epsF p

lemma epsF_gt_one {n : ℕ} (hn : 7 ≤ n) : 1 < epsF n := by
  have h7 : (7 : ℝ) ≤ n := by exact_mod_cast hn
  unfold epsF; split_ifs
  · exact eps3_pos _ h7
  · exact eps1_pos _ (by linarith)

lemma epsF_pos {n : ℕ} (hn : 7 ≤ n) : 0 < epsF n := lt_trans one_pos (epsF_gt_one hn)

/-- The trial divisors, the primes from 7 to 1423. Only `2 ≤ d` is used in the proof. -/
def smallP : List ℕ := [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423]

/-- Trial division along a list, stopping once `d² > n`. -/
def tdL : List ℕ → ℕ → Bool
  | [], _ => true
  | d :: ds, n => if n < d * d then true else if n % d = 0 then false else tdL ds n

/-- A survivor: prime to 30 and to every listed divisor with `d² ≤ n`. -/
def surv (n : ℕ) : Bool := n % 2 != 0 && n % 3 != 0 && n % 5 != 0 && tdL smallP n

/-- The numerator `((n - 1)⁴ + b(n))(n - 1)`. -/
def numN (n : ℕ) : ℕ :=
  if n % 4 = 3 then ((n - 1) ^ 4 + (n - 1) * (n + 1) ^ 2) * (n - 1)
  else ((n - 1) ^ 4 + (n - 1) * (n ^ 2 + 6 * n + 1)) * (n - 1)

/-- The denominator `((n - 1)⁴ + a(n)) n`. -/
def denN (n : ℕ) : ℕ :=
  if n % 4 = 3 then ((n - 1) ^ 4 - (n + 1) ^ 2) * n
  else ((n - 1) ^ 4 + (3 * n + 1) * (n - 1)) * n

/-- One rounded-up step. -/
def step (s n : ℕ) : ℕ := if surv n then (s * numN n + denN n - 1) / denN n else s

/-- The chain from `s` over `a, a + 1, …, a + k - 1`. -/
def chainFrom (s a : ℕ) : ℕ → ℕ
  | 0 => s
  | k + 1 => step (chainFrom s a k) (a + k)

lemma chainFrom_add (s a l₁ l₂ : ℕ) :
    chainFrom s a (l₁ + l₂) = chainFrom (chainFrom s a l₁) (a + l₁) l₂ := by
  induction l₂ with
  | zero => rfl
  | succ l ih => rw [← Nat.add_assoc, chainFrom, ih, chainFrom, Nat.add_assoc]

lemma tdL_false {L : List ℕ} (hL : ∀ d ∈ L, 2 ≤ d) {n : ℕ} (h : tdL L n = false) : ¬ n.Prime := by
  induction L with
  | nil => simp [tdL] at h
  | cons d ds ih =>
    simp only [tdL] at h
    split_ifs at h with h1 h2
    · intro hp
      have hd := hL d List.mem_cons_self
      have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h2
      rcases (Nat.dvd_prime hp).mp hdvd with h3 | h3
      · omega
      · subst h3; push Not at h1; nlinarith
    · exact ih (fun x hx => hL x (List.mem_cons_of_mem d hx)) h

lemma smallP_ge : ∀ d ∈ smallP, 2 ≤ d := by decide

/-- Every prime above 5 survives. -/
lemma surv_of_prime {n : ℕ} (hp : n.Prime) (h5 : 5 < n) : surv n = true := by
  have h2 : n % 2 ≠ 0 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.dvd_of_mod_eq_zero h); omega
  have h3 : n % 3 ≠ 0 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h); omega
  have h5' : n % 5 ≠ 0 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp (Nat.dvd_of_mod_eq_zero h); omega
  have ht : tdL smallP n = true := by
    by_contra hc
    exact tdL_false smallP_ge (Bool.eq_false_iff.mpr hc) hp
  simp [surv, h3, h5', ht]; omega

lemma surv_odd {n : ℕ} (h : surv n = true) : n % 2 = 1 := by
  simp only [surv, Bool.and_eq_true, bne_iff_ne, ne_eq] at h; omega

/-- On odd `n ≥ 7`, `numN/denN = 1 + ε(n)`. -/
lemma epsF_eq {n : ℕ} (hn : 7 ≤ n) (hodd : n % 2 = 1) : epsF n = (numN n : ℝ) / (denN n : ℝ) := by
  have h7 : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
  unfold epsF numN denN
  split_ifs with h
  · have hle : (n + 1) ^ 2 ≤ (n - 1) ^ 4 := by
      have : n + 1 ≤ (n - 1) ^ 2 := by
        calc n + 1 = (n - 1) + 2 := by omega
          _ ≤ (n - 1) * (n - 1) := by nlinarith [(by omega : 6 ≤ n - 1)]
          _ = (n - 1) ^ 2 := by ring
      calc (n + 1) ^ 2 ≤ ((n - 1) ^ 2) ^ 2 := Nat.pow_le_pow_left this 2
        _ = (n - 1) ^ 4 := by ring
    have hA : 0 < ((n : ℝ) - 1) ^ 4 + -((n : ℝ) + 1) ^ 2 := by
      have h1 : 36 ≤ ((n : ℝ) - 1) ^ 2 := by nlinarith
      have h2 : ((n : ℝ) - 1) ^ 4 = (((n : ℝ) - 1) ^ 2) ^ 2 := by ring
      have h3 : ((n : ℝ) + 1) ^ 2 ≤ 4 * ((n : ℝ) - 1) ^ 2 := by nlinarith
      nlinarith
    unfold onePlusEps3
    rw [eps_form _ _ _ (by linarith) hA]
    push_cast [Nat.cast_sub hle, hq]
    ring
  · have hA : 0 < ((n : ℝ) - 1) ^ 4 + (3 * (n : ℝ) + 1) * ((n : ℝ) - 1) := by
      have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      positivity
    unfold onePlusEps1
    rw [eps_form _ _ _ (by linarith) hA]
    push_cast [hq]
    ring

lemma denN_pos {n : ℕ} (hn : 7 ≤ n) : 0 < denN n := by
  have h : (0 : ℝ) < (denN n : ℝ) := by
    have h7 : (7 : ℝ) ≤ n := by exact_mod_cast hn
    have hq : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
    unfold denN
    split_ifs with h
    · have hle : (n + 1) ^ 2 ≤ (n - 1) ^ 4 := by
        have : n + 1 ≤ (n - 1) ^ 2 := by
          calc n + 1 = (n - 1) + 2 := by omega
            _ ≤ (n - 1) * (n - 1) := by nlinarith [(by omega : 6 ≤ n - 1)]
            _ = (n - 1) ^ 2 := by ring
        calc (n + 1) ^ 2 ≤ ((n - 1) ^ 2) ^ 2 := Nat.pow_le_pow_left this 2
          _ = (n - 1) ^ 4 := by ring
      push_cast [Nat.cast_sub hle, hq]
      have h1 : 36 ≤ ((n : ℝ) - 1) ^ 2 := by nlinarith
      have h2 : ((n : ℝ) - 1) ^ 4 = (((n : ℝ) - 1) ^ 2) ^ 2 := by ring
      have h3 : ((n : ℝ) + 1) ^ 2 ≤ 4 * ((n : ℝ) - 1) ^ 2 := by nlinarith
      have : 0 < ((n : ℝ) - 1) ^ 4 - ((n : ℝ) + 1) ^ 2 := by nlinarith
      positivity
    · push_cast [hq]
      have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      positivity
  exact_mod_cast h

/-- The rounding goes up at a survivor. -/
lemma step_ge {s n : ℕ} (hn : 7 ≤ n) (hs : surv n = true) :
    (s : ℝ) * epsF n ≤ ((s * numN n + denN n - 1) / denN n : ℕ) := by
  set q := denN n with hqd
  have hq1 : 0 < q := denN_pos hn
  have hdiv : s * numN n ≤ (s * numN n + q - 1) / q * q := by
    have h := Nat.div_add_mod' (s * numN n + q - 1) q
    have hm := Nat.mod_lt (s * numN n + q - 1) hq1
    generalize s * numN n = P at h hm ⊢
    generalize (P + q - 1) / q * q = Z at h ⊢
    omega
  rw [epsF_eq hn (surv_odd hs), ← hqd]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  rw [mul_div_assoc', div_le_iff₀ hqpos]
  exact_mod_cast hdiv

/-- **The chain bound.** `s ∏_{a ≤ n < a + k, n survives} (1 + ε(n)) ≤ chainFrom s a k`, `a ≥ 7`. -/
theorem chain_bound (s a : ℕ) (ha : 7 ≤ a) (k : ℕ) :
    (s : ℝ) * ∏ n ∈ (Ico a (a + k)).filter (fun n => surv n = true), epsF n ≤ chainFrom s a k := by
  induction k with
  | zero => simp [chainFrom]
  | succ k ih =>
    have hI : Ico a (a + (k + 1)) = insert (a + k) (Ico a (a + k)) := by
      rw [← Nat.add_assoc, Nat.Ico_succ_right_eq_insert_Ico (by omega)]
    rw [hI, Finset.filter_insert]
    have hn : 7 ≤ a + k := by omega
    by_cases h : surv (a + k) = true
    · rw [if_pos h, Finset.prod_insert (by simp)]
      have hstep : step (chainFrom s a k) (a + k) =
          (chainFrom s a k * numN (a + k) + denN (a + k) - 1) / denN (a + k) := by
        unfold step; rw [if_pos h]
      simp only [chainFrom, hstep]
      calc (s : ℝ) * (epsF (a + k) * ∏ n ∈ (Ico a (a + k)).filter (fun n => surv n = true), epsF n)
          = epsF (a + k) * ((s : ℝ) * ∏ n ∈ (Ico a (a + k)).filter (fun n => surv n = true), epsF n) := by ring
        _ ≤ epsF (a + k) * (chainFrom s a k : ℝ) := mul_le_mul_of_nonneg_left ih (epsF_pos hn).le
        _ = (chainFrom s a k : ℝ) * epsF (a + k) := by ring
        _ ≤ _ := step_ge hn h
    · rw [if_neg h]
      have hstep : step (chainFrom s a k) (a + k) = chainFrom s a k := by
        unfold step; rw [if_neg h]
      simp only [chainFrom, hstep]
      exact ih

end LeanLab.Hathi2021.C3
