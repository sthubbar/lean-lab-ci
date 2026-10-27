/-
AI-written Lean code, Claude, 2026-10-20, run 20261020T2303Z-14596, unit U-1293.
P0048 A. Dudek, L. Dunn, arXiv 2602.22720, Section 2, Lemma 2.1, Case 4, `z < 286`.

`DDLemma21All.Case4Script N`: for integer `w ≥ 2` and real `w < z < 286`,
`∏_{w ≤ p < z} (1 - g(p))⁻¹ ≤ 3 (log z / log w)²`. PROVED here for every `N`, no cited input.

Reduction to a finite check. If no prime lies in `[w, z)` the product is `1` and `log z > log w > 0`.
Otherwise let `p` and `q` be the least and largest primes in `[w, z)`. The set is the primes of
`[p, q]`, each factor is at most `h(r) = r/(r - 2)`, `h(2) = 2`, and
`log z / log w ≥ log q / log p ≥ 1`. So it suffices that for the 61 primes `p ≤ q < 286`,
`H(p, q) = ∏_{p ≤ r ≤ q} h(r) ≤ 3` or `H(p, q) ≤ 3 (l_q / u_p)²`, where
`2^{l_n} ≤ n^64 ≤ 2^{u_n}`, so `l_n / 64 ≤ log n / log 2 ≤ u_n / 64`; `log 2` cancels.
Both tables are checked by `decide +kernel` on natural numbers. The case `p = q = 3` is sharp,
`H = 3`. Python minimum of the other margins: 1.256 at `p = 2, q = 3`.

PROVED: `case4`, `Case4Script N` for every `N`.
CONDITIONAL ON `RSHyp` and `Case2Script N` only: `lemma2_1_of_case2`, Lemma 2.1 with `K = 3`.
Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.DDLemma21All

open Real Finset LeanLab.AlmostPrimes.DDLemma21 LeanLab.AlmostPrimes.DDLemma21All

namespace LeanLab.AlmostPrimes.DDCase4

/-- The common denominator of the log tables. -/
def D : ℕ := 64

/-- `(n, l, u)` for the 61 primes `n < 286`, with `2^l ≤ n^64 ≤ 2^u`. -/
def T : List (ℕ × ℕ × ℕ) :=
  [(2, 64, 64),
  (3, 101, 102),
  (5, 148, 149),
  (7, 179, 180),
  (11, 221, 222),
  (13, 236, 237),
  (17, 261, 262),
  (19, 271, 272),
  (23, 289, 290),
  (29, 310, 311),
  (31, 317, 318),
  (37, 333, 334),
  (41, 342, 343),
  (43, 347, 348),
  (47, 355, 356),
  (53, 366, 367),
  (59, 376, 377),
  (61, 379, 380),
  (67, 388, 389),
  (71, 393, 394),
  (73, 396, 397),
  (79, 403, 404),
  (83, 408, 409),
  (89, 414, 415),
  (97, 422, 423),
  (101, 426, 427),
  (103, 427, 428),
  (107, 431, 432),
  (109, 433, 434),
  (113, 436, 437),
  (127, 447, 448),
  (131, 450, 451),
  (137, 454, 455),
  (139, 455, 456),
  (149, 462, 463),
  (151, 463, 464),
  (157, 466, 467),
  (163, 470, 471),
  (167, 472, 473),
  (173, 475, 476),
  (179, 478, 479),
  (181, 479, 480),
  (191, 484, 485),
  (193, 485, 486),
  (197, 487, 488),
  (199, 488, 489),
  (211, 494, 495),
  (223, 499, 500),
  (227, 500, 501),
  (229, 501, 502),
  (233, 503, 504),
  (239, 505, 506),
  (241, 506, 507),
  (251, 510, 511),
  (257, 512, 513),
  (263, 514, 515),
  (269, 516, 517),
  (271, 517, 518),
  (277, 519, 520),
  (281, 520, 521),
  (283, 521, 522)]

/-- The primes below 286. -/
def PL : List ℕ := T.map Prod.fst

def hn (r : ℕ) : ℕ := if r = 2 then 2 else r
def hd (r : ℕ) : ℕ := if r = 2 then 1 else r - 2

def seg (p q : ℕ) : List ℕ := PL.filter (fun r => p ≤ r && r ≤ q)
def num (p q : ℕ) : ℕ := ((seg p q).map hn).prod
def den (p q : ℕ) : ℕ := ((seg p q).map hd).prod

def logCheck : Bool := T.all fun e => 2 ^ e.2.1 ≤ e.1 ^ D && e.1 ^ D ≤ 2 ^ e.2.2

def pairCheck : Bool := T.all fun a => T.all fun b =>
  !(a.1 ≤ b.1) || (num a.1 b.1 ≤ 3 * den a.1 b.1 ||
    num a.1 b.1 * a.2.2 ^ 2 ≤ 3 * b.2.1 ^ 2 * den a.1 b.1)

theorem logCheck_ok : logCheck = true := by decide +kernel

theorem pairCheck_ok : pairCheck = true := by decide +kernel

theorem PL_nodup : PL.Nodup := by decide +kernel

theorem prime_iff_mem : ∀ n, n < 286 → (n.Prime ↔ n ∈ PL) := by decide +kernel

theorem PL_lt : ∀ n ∈ PL, n < 286 := by decide +kernel

theorem PL_two_le : ∀ n ∈ PL, 2 ≤ n := by decide +kernel

/-- From `2^l ≤ n^D`: `l log 2 ≤ D log n`. -/
lemma log_lo {n l : ℕ} (h : 2 ^ l ≤ n ^ D) : (l : ℝ) * log 2 ≤ (D : ℝ) * log n := by
  have h' : ((2 : ℕ) : ℝ) ^ l ≤ (n : ℝ) ^ D := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this
  exact this

/-- From `n^D ≤ 2^u` with `n ≥ 1`: `D log n ≤ u log 2`. -/
lemma log_hi {n u : ℕ} (hn : 1 ≤ n) (h : n ^ D ≤ 2 ^ u) : (D : ℝ) * log n ≤ (u : ℝ) * log 2 := by
  have h' : (n : ℝ) ^ D ≤ ((2 : ℕ) : ℝ) ^ u := by exact_mod_cast h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this
  exact this

/-- Each factor: `(1 - g(r))⁻¹ ≤ h(r)` for a prime `r`. -/
lemma factor_le (N r : ℕ) (hr : r.Prime) :
    (1 - g N r)⁻¹ ≤ (hn r : ℝ) / (hd r : ℝ) := by
  by_cases h2 : r = 2
  · subst h2; simp [g, hn, hd]; norm_num
  · have h3 : 3 ≤ r := by have := hr.two_le; omega
    obtain ⟨hpos, hle⟩ := one_sub_g_pos N r h3
    have hr3 : (3 : ℝ) ≤ r := by exact_mod_cast h3
    have e : (hn r : ℝ) / (hd r : ℝ) = (1 - 2 / (r : ℝ))⁻¹ := by
      simp only [hn, hd, h2, ite_false]
      rw [Nat.cast_sub (by omega)]
      push_cast
      have : (r : ℝ) - 2 ≠ 0 := by linarith
      have : (r : ℝ) ≠ 0 := by linarith
      field_simp
    rw [e]
    exact inv_anti₀ hpos hle

lemma factor_nonneg (N r : ℕ) (hr : r.Prime) : 0 ≤ (1 - g N r)⁻¹ := by
  by_cases h2 : r = 2
  · subst h2; simp [g]; norm_num
  · have h3 : 3 ≤ r := by have := hr.two_le; omega
    obtain ⟨hpos, hle⟩ := one_sub_g_pos N r h3
    exact (inv_pos.mpr (lt_of_lt_of_le hpos hle)).le

/-- The finite check read back over the reals: for `p ≤ q` in the table,
`H(p, q) ≤ 3` or `H(p, q) ≤ 3 (log q / log p)²`. -/
lemma pair_bound {p q : ℕ} (hp : p ∈ PL) (hq : q ∈ PL) (hpq : p ≤ q) :
    (num p q : ℝ) / (den p q : ℝ) ≤ 3 * max 1 ((log q / log p) ^ 2) := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
  have hpc := pairCheck_ok
  simp only [pairCheck, List.all_eq_true] at hpc
  have hab := hpc a ha b hb
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    not_le] at hab
  have hlc := logCheck_ok
  simp only [logCheck, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlc
  have ha2 := PL_two_le a.1 (List.mem_map_of_mem ha)
  have hb2 := PL_two_le b.1 (List.mem_map_of_mem hb)
  have hden : 0 < den a.1 b.1 := by
    unfold den
    apply List.prod_pos
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    have := PL_two_le r (List.mem_of_mem_filter hr)
    unfold hd; split_ifs <;> omega
  have hden' : (0 : ℝ) < den a.1 b.1 := by exact_mod_cast hden
  have hm1 : (3 : ℝ) ≤ 3 * max 1 ((log b.1 / log a.1) ^ 2) := by
    have := le_max_left (1 : ℝ) ((log b.1 / log a.1) ^ 2); linarith
  rcases hab with hlt | h1 | h2
  · omega
  · rw [div_le_iff₀ hden']
    have : (num a.1 b.1 : ℝ) ≤ 3 * den a.1 b.1 := by exact_mod_cast h1
    nlinarith
  · -- log branch
    have hlp : 0 < log (a.1 : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < a.1))
    have hlq : 0 < log (b.1 : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < b.1))
    have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have hlo := log_lo (hlc b hb).1
    have hhi := log_hi (by omega) (hlc a ha).2
    have hD : (D : ℝ) = 64 := by norm_num [D]
    rw [hD] at hlo hhi
    have hup : (0 : ℝ) < a.2.2 := by
      by_contra hc; push Not at hc
      have : (a.2.2 : ℝ) * log 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hl2.le
      nlinarith
    have hlq0 : (0 : ℝ) ≤ b.2.1 := Nat.cast_nonneg _
    -- lq / up ≤ log q / log p
    have hr : (b.2.1 : ℝ) / a.2.2 ≤ log b.1 / log a.1 := by
      rw [div_le_div_iff₀ hup hlp]
      have e1 : (b.2.1 : ℝ) * log a.1 * 64 ≤ b.2.1 * (a.2.2 * log 2) := by
        have := mul_le_mul_of_nonneg_left hhi hlq0; nlinarith
      have e2 : (a.2.2 : ℝ) * (b.2.1 * log 2) ≤ a.2.2 * (64 * log b.1) :=
        mul_le_mul_of_nonneg_left hlo hup.le
      nlinarith
    have hsq : ((b.2.1 : ℝ) / a.2.2) ^ 2 ≤ (log b.1 / log a.1) ^ 2 :=
      pow_le_pow_left₀ (div_nonneg hlq0 hup.le) hr 2
    have h2' : (num a.1 b.1 : ℝ) * (a.2.2 : ℝ) ^ 2 ≤ 3 * (b.2.1 : ℝ) ^ 2 * den a.1 b.1 := by
      exact_mod_cast h2
    have hq : (num a.1 b.1 : ℝ) / den a.1 b.1 ≤ 3 * ((b.2.1 : ℝ) / a.2.2) ^ 2 := by
      rw [div_le_iff₀ hden', div_pow, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    have := le_max_right (1 : ℝ) ((log b.1 / log a.1) ^ 2)
    nlinarith

/-- **Dudek-Dunn Lemma 2.1, Case 4**, the paper's computer check, for every `N`. PROVED. -/
theorem case4 (N : ℕ) : Case4Script N := by
  intro w hw z hwz hz
  have hw' : (2 : ℝ) ≤ w := by exact_mod_cast hw
  have hlw : 0 < log (w : ℝ) := log_pos (by linarith)
  have hlwz : log (w : ℝ) < log z := log_lt_log (by linarith) hwz
  have hratio : 1 ≤ log z / log w := by rw [le_div_iff₀ hlw]; linarith
  have hone : 1 ≤ (log z / log w) ^ 2 := by nlinarith
  set S := primesIn w z with hS
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.prod_empty]; linarith
  have memS : ∀ r, r ∈ S ↔ r.Prime ∧ (w : ℝ) ≤ r ∧ (r : ℝ) < z := by
    intro r
    simp only [hS, primesIn, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro h; exact ⟨Nat.lt_ceil.mpr h.2.2, h⟩
  set p := S.min' hne
  set q := S.max' hne
  have hpS := (memS p).mp (S.min'_mem hne)
  have hqS := (memS q).mp (S.max'_mem hne)
  have hlt : ∀ r ∈ S, r < 286 := by
    intro r hr
    have := ((memS r).mp hr).2.2
    have : (r : ℝ) < 286 := by linarith
    exact_mod_cast this
  have hpPL : p ∈ PL := (prime_iff_mem p (hlt p (S.min'_mem hne))).mp hpS.1
  have hqPL : q ∈ PL := (prime_iff_mem q (hlt q (S.max'_mem hne))).mp hqS.1
  have hpq : p ≤ q := S.min'_le q (S.max'_mem hne)
  -- the set is the table segment
  have hseg : S = (seg p q).toFinset := by
    ext r
    simp only [List.mem_toFinset, seg, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro hr
      exact ⟨(prime_iff_mem r (hlt r hr)).mp ((memS r).mp hr).1, S.min'_le r hr, S.le_max' r hr⟩
    · rintro ⟨hrPL, hpr, hrq⟩
      rw [memS]
      refine ⟨(prime_iff_mem r (PL_lt r hrPL)).mpr hrPL, ?_, ?_⟩
      · have : (p : ℝ) ≤ r := by exact_mod_cast hpr
        linarith [hpS.2.1]
      · have : (r : ℝ) ≤ q := by exact_mod_cast hrq
        linarith [hqS.2.2]
  have hnd : (seg p q).Nodup := PL_nodup.filter _
  -- bound the product by H(p, q)
  have hprod : ∏ r ∈ S, (1 - g N r)⁻¹ ≤ (num p q : ℝ) / (den p q : ℝ) := by
    calc ∏ r ∈ S, (1 - g N r)⁻¹ ≤ ∏ r ∈ S, ((hn r : ℝ) / (hd r : ℝ)) := by
          apply Finset.prod_le_prod₀
          · intro r hr; exact factor_nonneg N r ((memS r).mp hr).1
          · intro r hr; exact factor_le N r ((memS r).mp hr).1
      _ = (∏ r ∈ S, (hn r : ℝ)) / (∏ r ∈ S, (hd r : ℝ)) := Finset.prod_div_distrib _ _
      _ = (num p q : ℝ) / (den p q : ℝ) := by
          rw [← Nat.cast_prod, ← Nat.cast_prod, hseg, List.prod_toFinset _ hnd,
            List.prod_toFinset _ hnd]
          rfl
  have hb := pair_bound hpPL hqPL hpq
  -- log q / log p ≤ log z / log w
  have hp2 : (2 : ℝ) ≤ p := le_trans hw' hpS.2.1
  have hlp : 0 < log (p : ℝ) := log_pos (by linarith)
  have hlq : 0 ≤ log (q : ℝ) := log_nonneg (by linarith [hpq, (show (p : ℝ) ≤ q by exact_mod_cast hpq)])
  have hr : log (q : ℝ) / log p ≤ log z / log w := by
    have h1 : log (q : ℝ) ≤ log z := log_le_log (by linarith [(show (p : ℝ) ≤ q by exact_mod_cast hpq)]) hqS.2.2.le
    have h2 : log (w : ℝ) ≤ log p := log_le_log (by linarith) hpS.2.1
    calc log (q : ℝ) / log p ≤ log z / log p := div_le_div_of_nonneg_right h1 hlp.le
      _ ≤ log z / log w := div_le_div_of_nonneg_left (by linarith) hlw h2
  have hsq : (log (q : ℝ) / log p) ^ 2 ≤ (log z / log w) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hlq hlp.le) hr 2
  have hmax : max 1 ((log (q : ℝ) / log p) ^ 2) ≤ (log z / log w) ^ 2 := max_le hone hsq
  linarith

/-- **Dudek-Dunn Lemma 2.1**, `K = 3`, for integer `w ≥ 2` and real `z > w`.
CONDITIONAL ON `RSHyp` and `Case2Script N` only; Case 4 is `case4`. -/
theorem lemma2_1_of_case2 (N : ℕ) (hRS : RSHyp) (h2 : Case2Script N)
    (w : ℕ) (hw : 2 ≤ w) (z : ℝ) (hwz : (w : ℝ) < z) :
    ∏ p ∈ primesIn w z, (1 - g N p)⁻¹ ≤ 3 * (log z / log w) ^ 2 :=
  lemma2_1 N hRS h2 (case4 N) w hw z hwz

#print axioms logCheck_ok
#print axioms pairCheck_ok
#print axioms pair_bound
#print axioms case4
#print axioms lemma2_1_of_case2

end LeanLab.AlmostPrimes.DDCase4
