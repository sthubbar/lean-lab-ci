/-
# Pintz and Althöfer 2026, the tail of the singular series behind (4.16)

Unit U-1139, T2 FRONTIER, idea I-0080, run 20261020T0103Z-16649.

arXiv 2610.15559v1, Section 4.4: v_X(n) = n e^{−n/X} 𝔖(n) + O(X^{1+η}/P) needs the q > P part of
𝔖(n) = Σ_q μ(q) c_q(n)/φ(q)². Here, explicitly, for ANY finite set S of moduli q > P > 0:

  Σ_{q∈S} |c_q(n)|/φ(q)² ≤ 12 τ(n)² / √P,                                    `tail_sum`

from |c_q(n)| ≤ (q,n) τ(n), PintzAlthofer2026Ram; q³ ≤ 16 φ(q)⁴, VanDerCorput1939/Totient;
(q,n) ≤ Σ_{d | n, d | q} d; q = dm; and Σ_{m > M} 1/(m√m) ≤ 3/√M, `tail_gt`, by the
telescoping bound 1/(m√m) ≤ 2(1/√(m−1) − 1/√m), `f_le_tel`.

This is weaker than the paper's X^η/P, a power √P against P, but it is enough for the lower
half of the coefficient condition: with P a power of X the tail is o(1) times τ(n)², and
τ(n)² ≪ X^η, so n e^{−n/X} 𝔖(n) still dominates. It covers both the q > P part of the full
series, as a limit of finite S, and the q > P divisors of P# in `sing_trunc_ge`.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.PintzAlthofer2026Ram
import LeanLab.VanDerCorput1939.Totient

namespace LeanLab.ExceptionalSet.PintzAlthofer2026Tail

open Finset Real

/-- f(m) = 1/(m √m). -/
noncomputable def f (m : ℕ) : ℝ := 1 / ((m : ℝ) * Real.sqrt m)

lemma f_nonneg (m : ℕ) : 0 ≤ f m := by unfold f; positivity

/-- The telescoping step: 1/(m√m) ≤ 2(1/√(m−1) − 1/√m) for m ≥ 2. -/
lemma f_le_tel (m : ℕ) (hm : 2 ≤ m) :
    f m ≤ 2 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt m) := by
  have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hm1]
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set a := Real.sqrt ((m : ℝ) - 1) with ha_def
  set b := Real.sqrt (m : ℝ) with hb_def
  have ha2 : a ^ 2 = (m : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = (m : ℝ) := Real.sq_sqrt (by linarith)
  have ha0 : 0 < a := Real.sqrt_pos.2 (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.2 (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have h1 : (b - a) * (a + b) = 1 := by nlinarith
  unfold f
  rw [← hb_def, ← hb2]
  have hlhs : 1 / (b ^ 2 * b) = 1 / b ^ 3 := by ring_nf
  rw [hlhs, show 1 / a - 1 / b = (b - a) / (a * b) by field_simp]
  rw [div_le_iff₀ (by positivity)]
  have hba : b - a = 1 / (a + b) := by
    field_simp; linarith
  rw [hba]
  have key : a * b * (a + b) ≤ 2 * b ^ 3 := by nlinarith [mul_pos ha0 hb0]
  have hs : 0 < a + b := by linarith
  rw [show 2 * (1 / (a + b) / (a * b)) * b ^ 3 = 2 * b ^ 3 / (a * b * (a + b)) by
    field_simp]
  rw [le_div_iff₀ (by positivity)]; linarith

/-- Telescoped: Σ_{a < m ≤ N} 1/(m√m) ≤ 2(1/√a − 1/√N) for 1 ≤ a ≤ N. -/
lemma tail_Ioc (a : ℕ) (ha : 1 ≤ a) : ∀ N : ℕ, a ≤ N →
    ∑ m ∈ Ioc a N, f m ≤ 2 * (1 / Real.sqrt a - 1 / Real.sqrt N) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [sum_Ioc_succ_top (by omega)]
    have ht := f_le_tel (N + 1) (by omega)
    simp only [Nat.add_sub_cancel] at ht
    push_cast at ht ⊢
    linarith

lemma tail_Ioc' (a N : ℕ) (ha : 1 ≤ a) : ∑ m ∈ Ioc a N, f m ≤ 2 / Real.sqrt a := by
  rcases le_or_gt a N with h | h
  · have := tail_Ioc a ha N h
    have : 0 ≤ 1 / Real.sqrt N := by positivity
    have e : 2 * (1 / Real.sqrt a) = 2 / Real.sqrt a := by ring
    linarith
  · rw [Ioc_eq_empty (by omega)]; simp; positivity

/-- Σ_{m ∈ S} 1/(m√m) ≤ 3/√M when every m ∈ S has m ≥ 1 and m > M > 0. -/
theorem tail_gt (S : Finset ℕ) {M : ℝ} (hM : 0 < M) (hS : ∀ m ∈ S, 1 ≤ m ∧ M < m) :
    ∑ m ∈ S, f m ≤ 3 / Real.sqrt M := by
  set N := S.sup id
  have hmN : ∀ m ∈ S, m ≤ N := fun m hm => le_sup (f := id) hm
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  rcases lt_or_ge M 1 with h1 | h1
  · -- every m ≥ 1
    have hsub : S ⊆ insert 1 (Ioc 1 N) := by
      intro m hm
      rcases (hS m hm).1.eq_or_lt with e | e
      · rw [← e]; exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_Ioc.2 ⟨e, hmN m hm⟩)
    have h := sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => f_nonneg m)
    rw [sum_insert (by simp)] at h
    have h2 := tail_Ioc' 1 N le_rfl
    have hf1 : f 1 = 1 := by simp [f]
    have hsq1 : Real.sqrt M ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1.le
    have h3 : 3 ≤ 3 / Real.sqrt M := by
      rw [le_div_iff₀ hsM]; linarith
    simp at h2
    linarith
  · set a := ⌊M⌋₊ with ha_def
    have ha1 : 1 ≤ a := Nat.le_floor (by exact_mod_cast h1)
    have haM : (a : ℝ) ≤ M := Nat.floor_le hM.le
    have hMa : M < a + 1 := Nat.lt_floor_add_one M
    have hsub : S ⊆ Ioc a N := by
      intro m hm
      refine mem_Ioc.2 ⟨?_, hmN m hm⟩
      have : (a : ℝ) < m := lt_of_le_of_lt haM (hS m hm).2
      exact_mod_cast this
    have h := sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => f_nonneg m)
    have h2 := tail_Ioc' a N ha1
    have har : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 (by linarith)
    have h4 : 2 / Real.sqrt a ≤ 3 / Real.sqrt M := by
      rw [div_le_div_iff₀ hsa hsM]
      have : Real.sqrt (4 * M) ≤ Real.sqrt (9 * a) := Real.sqrt_le_sqrt (by linarith)
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num)] at this
      have e4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
      have e9 : Real.sqrt 9 = 3 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
      rw [e4, e9] at this; linarith
    linarith

/-- 1/φ(q)² ≤ 4/(q√q), from q³ ≤ 16 φ(q)⁴. -/
lemma inv_totient_sq_le (q : ℕ) (hq : 0 < q) : 1 / (Nat.totient q : ℝ) ^ 2 ≤ 4 * f q := by
  have h := LeanLab.VanDerCorput1939.cube_le_totient_pow4 q hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hr : ((q : ℝ) * Real.sqrt q) ^ 2 ≤ (4 * (Nat.totient q : ℝ) ^ 2) ^ 2 := by
    have : ((q ^ 3 : ℕ) : ℝ) ≤ ((16 * (Nat.totient q) ^ 4 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    rw [mul_pow, Real.sq_sqrt hqr.le]; nlinarith
  have hle : (q : ℝ) * Real.sqrt q ≤ 4 * (Nat.totient q : ℝ) ^ 2 :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hr
  unfold f
  rw [div_le_iff₀ (by positivity)]
  rw [show 4 * (1 / ((q : ℝ) * Real.sqrt q)) * (Nat.totient q : ℝ) ^ 2
      = 4 * (Nat.totient q : ℝ) ^ 2 / ((q : ℝ) * Real.sqrt q) by ring]
  rw [le_div_iff₀ (by positivity)]; linarith

/-- f(dm) · d = f(m)/√d. -/
lemma f_mul (d m : ℕ) (hd : 0 < d) : (d : ℝ) * f (d * m) = f m / Real.sqrt d := by
  unfold f
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  push_cast
  rw [Real.sqrt_mul hd'.le]
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd'
  have hsd : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt hd'.le
  rcases (Nat.cast_nonneg m : (0 : ℝ) ≤ m).eq_or_lt with hm | hm
  · rw [← hm]; simp
  · have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
    field_simp
    all_goals nlinarith [hsd]

/-- For one divisor d: Σ_{q ∈ S, d | q} d f(q) ≤ 3/√P, when every q ∈ S has q > P > 0. -/
lemma inner_le (S : Finset ℕ) {P : ℝ} (hP : 0 < P) (hS : ∀ q ∈ S, P < q) (d : ℕ) (hd : 0 < d) :
    ∑ q ∈ S.filter (d ∣ ·), (d : ℝ) * f q ≤ 3 / Real.sqrt P := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd'
  have hrw : ∀ q ∈ S.filter (d ∣ ·), (d : ℝ) * f q = f (q / d) / Real.sqrt d := by
    intro q hq
    obtain ⟨k, rfl⟩ := (mem_filter.1 hq).2
    rw [f_mul d k hd, Nat.mul_div_cancel_left k hd]
  rw [sum_congr rfl hrw, ← sum_div]
  have hinj : Set.InjOn (fun q => q / d) (S.filter (d ∣ ·) : Set ℕ) := by
    intro x hx y hy hxy
    obtain ⟨k, rfl⟩ := (mem_filter.1 hx).2
    obtain ⟨l, rfl⟩ := (mem_filter.1 hy).2
    simp only [Nat.mul_div_cancel_left _ hd] at hxy
    rw [hxy]
  rw [← sum_image (f := f) hinj]
  have hM : 0 < P / d := div_pos hP hd'
  have hT := tail_gt ((S.filter (d ∣ ·)).image (fun q => q / d)) hM (by
    intro m hm
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hm
    obtain ⟨k, rfl⟩ := (mem_filter.1 hq).2
    rw [Nat.mul_div_cancel_left k hd]
    have hPq := hS _ (mem_filter.1 hq).1
    push_cast at hPq
    have hk : P / d < k := by rw [div_lt_iff₀ hd']; linarith
    refine ⟨?_, hk⟩
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hk; simp at hk; linarith
    · exact h0)
  rw [div_le_iff₀ hs]
  refine hT.trans (le_of_eq ?_)
  rw [Real.sqrt_div hP.le]
  field_simp

/-- **The tail of the singular series**: for any finite S of moduli q > P > 0 and n ≥ 1,
Σ_{q∈S} |c_q(n)|/φ(q)² ≤ 12 τ(n)²/√P. -/
theorem tail_sum (n : ℕ) (hn : 1 ≤ n) {P : ℝ} (hP : 0 < P) (S : Finset ℕ) (hS : ∀ q ∈ S, P < q) :
    ∑ q ∈ S, |LeanLab.HeathBrown1985.ramanujan q n| / (Nat.totient q : ℝ) ^ 2 ≤
      12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P := by
  have hq0 : ∀ q ∈ S, 0 < q := fun q hq => by
    have := hS q hq; have : (0 : ℝ) < q := by linarith
    exact_mod_cast this
  set τ := (n.divisors.card : ℝ)
  have hτ0 : 0 ≤ τ := Nat.cast_nonneg _
  -- step A: one term
  have hA : ∀ q ∈ S, |LeanLab.HeathBrown1985.ramanujan q n| / (Nat.totient q : ℝ) ^ 2 ≤
      4 * τ * ((n.gcd q : ℝ) * f q) := by
    intro q hq
    have hc := LeanLab.ExceptionalSet.PintzAlthofer2026Ram.ramanujan_abs_le_gcd_mul_tau q n
    have hτg : (((n.gcd q).divisors.card : ℕ) : ℝ) ≤ τ := by
      show (((n.gcd q).divisors.card : ℕ) : ℝ) ≤ (n.divisors.card : ℝ)
      exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd (by omega) (Nat.gcd_dvd_left n q))
    have hc' : |LeanLab.HeathBrown1985.ramanujan q n| ≤ (n.gcd q : ℝ) * τ := by
      refine hc.trans ?_; push_cast
      exact mul_le_mul_of_nonneg_left hτg (Nat.cast_nonneg _)
    have hi := inv_totient_sq_le q (hq0 q hq)
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (hq0 q hq)
    calc |LeanLab.HeathBrown1985.ramanujan q n| / (Nat.totient q : ℝ) ^ 2
        = |LeanLab.HeathBrown1985.ramanujan q n| * (1 / (Nat.totient q : ℝ) ^ 2) := by ring
      _ ≤ ((n.gcd q : ℝ) * τ) * (4 * f q) :=
          mul_le_mul hc' hi (by positivity) (by positivity)
      _ = 4 * τ * ((n.gcd q : ℝ) * f q) := by ring
  -- step B: (n, q) ≤ Σ_{d | n, d | q} d
  have hB : ∀ q ∈ S, (n.gcd q : ℝ) ≤ ∑ d ∈ n.divisors, if d ∣ q then (d : ℝ) else 0 := by
    intro q hq
    have hmem : n.gcd q ∈ n.divisors := Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left n q, by omega⟩
    have := single_le_sum (f := fun d => if d ∣ q then (d : ℝ) else 0)
      (fun d _ => by split_ifs <;> positivity) hmem
    simpa [Nat.gcd_dvd_right n q] using this
  -- step C and D
  have hCD : ∑ q ∈ S, (n.gcd q : ℝ) * f q ≤ 3 * τ / Real.sqrt P := by
    calc ∑ q ∈ S, (n.gcd q : ℝ) * f q
        ≤ ∑ q ∈ S, ∑ d ∈ n.divisors, (if d ∣ q then (d : ℝ) else 0) * f q := by
          refine sum_le_sum fun q hq => ?_
          rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (hB q hq) (f_nonneg q)
      _ = ∑ d ∈ n.divisors, ∑ q ∈ S.filter (d ∣ ·), (d : ℝ) * f q := by
          rw [sum_comm]; refine sum_congr rfl fun d _ => ?_
          rw [sum_filter]; refine sum_congr rfl fun q _ => ?_
          split_ifs <;> simp
      _ ≤ ∑ d ∈ n.divisors, 3 / Real.sqrt P := by
          refine sum_le_sum fun d hd => inner_le S hP hS d (Nat.pos_of_mem_divisors hd)
      _ = 3 * τ / Real.sqrt P := by rw [sum_const, nsmul_eq_mul]; ring
  calc ∑ q ∈ S, |LeanLab.HeathBrown1985.ramanujan q n| / (Nat.totient q : ℝ) ^ 2
      ≤ ∑ q ∈ S, 4 * τ * ((n.gcd q : ℝ) * f q) := sum_le_sum hA
    _ = 4 * τ * ∑ q ∈ S, (n.gcd q : ℝ) * f q := by rw [mul_sum]
    _ ≤ 4 * τ * (3 * τ / Real.sqrt P) := mul_le_mul_of_nonneg_left hCD (by positivity)
    _ = 12 * τ ^ 2 / Real.sqrt P := by ring

/-- Vacuity: S = {2}, P = 1, n = 1 satisfy the hypotheses. -/
example : ∀ q ∈ ({2} : Finset ℕ), (1 : ℝ) < q := by simp

end LeanLab.ExceptionalSet.PintzAlthofer2026Tail
