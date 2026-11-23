import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
/-
Burst burst-20261122, session S78, target LiuWang2002. PROVES the MEDIUM LEAF
`RSMertens1122.rs1962_thm21_at_15000`: `Σ_{p≤15000} log p / p - log 15000 ∈ [-1.35, -1.30]`,
the value Rosser-Schoenfeld 1962 p. 72 Theorem 21 display (4.8) places in `[-1.33259, -1.31575]`.
Certificate: every prime `p ≤ 15000` gets `e = lg(p^1024)` with `2^e ≤ p^1024 < 2^(e+1)`, so
`e log 2 / 1024 ≤ log p < (e+1) log 2 / 1024`; with `q = ⌊10^9/p⌋` the two integer sums
`Σ e q` and `Σ (e+1)(q+1)` are computed by `decide +kernel` over `Nat.rec` folds, and
`2^14205 ≤ 15000^1024 ≤ 2^14206` bounds `log 15000`. Mathlib's `log 2` bounds finish it.
New definitions in namespace `RS62Leaf` are computational helpers for the certificate only:
trial division `isP`, a binary search `lg`, and folds; `isP_iff` and `sumTo_eq` tie them to
`Nat.Prime` and the Finset sum. Imports are cut below full Mathlib to keep memory under 7 GB.
AI-written Lean code, Claude workflow subagent for session S78, 2026-11-22. Checked only by
the Lean kernel. Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/

namespace LeanLab.LiuWang2002.RSMertens15000.RS62Leaf

def go (n : ℕ) (f : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => false)
    (fun _ ih d => if n < d*d then true else if n % d = 0 then false else ih (d+1)) f

def isP (n : ℕ) : Bool := decide (2 ≤ n) && go n 200 2

def sumTo (g : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k ih => ih + (if isP k then g k else 0)) n

def cnt (n : ℕ) : ℕ := sumTo (fun _ => 1) n

def lg (x : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun lo _ => lo)
    (fun _ ih lo hi => if 2^((lo+hi)/2) ≤ x then ih ((lo+hi)/2) hi else ih lo ((lo+hi)/2)) 15 0 16384

def gL (p : ℕ) : ℕ := lg (p^1024) * (1000000000 / p)
def gU (p : ℕ) : ℕ := (lg (p^1024) + 1) * (1000000000 / p + 1)
def chk (p : ℕ) : Bool := decide (2^(lg (p^1024)) ≤ p^1024) && decide (p^1024 < 2^(lg (p^1024)+1))
def allTo (n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && (!isP k || chk k)) n

theorem go_zero (n d : ℕ) : go n 0 d = false := rfl
theorem go_succ (n f d : ℕ) : go n (f+1) d =
    (if n < d*d then true else if n % d = 0 then false else go n f (d+1)) := rfl

theorem go_sound (n : ℕ) : ∀ f d, go n f d = true → ∀ k, d ≤ k → k*k ≤ n → ¬ k ∣ n := by
  intro f
  induction f with
  | zero => intro d h; rw [go_zero] at h; exact absurd h Bool.false_ne_true
  | succ f ih =>
    intro d h k hdk hkk hkn
    rw [go_succ] at h
    by_cases h1 : n < d*d
    · have : d*d ≤ k*k := Nat.mul_le_mul hdk hdk
      omega
    · rw [if_neg h1] at h
      by_cases h2 : n % d = 0
      · rw [if_pos h2] at h; exact Bool.false_ne_true h
      · rw [if_neg h2] at h
        rcases Nat.eq_or_lt_of_le hdk with h3 | h3
        · subst h3; exact h2 (Nat.mod_eq_zero_of_dvd hkn)
        · exact ih (d+1) h k h3 hkk hkn

theorem go_complete (n : ℕ) : ∀ f d, n < (d+f)*(d+f) →
    (∀ k, d ≤ k → k*k ≤ n → ¬ k ∣ n) → go n (f+1) d = true := by
  intro f
  induction f with
  | zero => intro d h _; rw [go_succ]; simp at h; simp [h]
  | succ f ih =>
    intro d h hk
    rw [go_succ]
    by_cases h1 : n < d*d
    · simp [h1]
    · rw [if_neg h1]
      have h2 : ¬ n % d = 0 := fun h0 => hk d le_rfl (by omega) (Nat.dvd_of_mod_eq_zero h0)
      rw [if_neg h2]
      exact ih (d+1) (by have : d + 1 + f = d + (f+1) := by omega
                         rw [this]; exact h)
        (fun k hk1 hk2 => hk k (by omega) hk2)

theorem isP_iff (n : ℕ) (hn : n < 40000) : isP n = true ↔ n.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [isP, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h2, hg⟩
    refine ⟨h2, fun m hm hms => go_sound n 200 2 hg m hm (Nat.le_sqrt.mp hms)⟩
  · rintro ⟨h2, hm⟩
    refine ⟨h2, go_complete n 199 2 (by omega) ?_⟩
    intro k hk hkk
    exact hm k hk (Nat.le_sqrt.mpr hkk)

theorem filter_eq : (Finset.range 15001).filter Nat.Prime =
    (Finset.range 15001).filter (fun n => isP n = true) :=
  Finset.filter_congr (fun n hn => (isP_iff n (by simp at hn; omega)).symm)

theorem sumTo_eq (g : ℕ → ℕ) (n : ℕ) :
    ((Finset.range n).filter (fun k => isP k = true)).sum g = sumTo g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs : sumTo g (n+1) = sumTo g n + (if isP n then g n else 0) := rfl
    rw [hs, Finset.range_add_one, Finset.filter_insert, ← ih]
    have hn : n ∉ (Finset.range n).filter (fun k => isP k = true) := by simp
    by_cases h : isP n = true
    · rw [if_pos h, Finset.sum_insert hn, if_pos h]; ring
    · rw [if_neg h, if_neg h]; simp

theorem allTo_spec (n : ℕ) (h : allTo n = true) : ∀ k < n, isP k = true → chk k = true := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    have hs : allTo (n+1) = (allTo n && (!isP n || chk n)) := rfl
    rw [hs, Bool.and_eq_true] at h
    intro k hk hp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
    · exact ih h.1 k hk hp
    · subst hk; simpa [hp] using h.2

set_option maxRecDepth 100000 in
theorem sumL : sumTo gL 15001 = 12248731220588 := by decide +kernel
set_option maxRecDepth 100000 in
theorem sumU : sumTo gU 15001 = 12251278804167 := by decide +kernel
set_option maxRecDepth 100000 in
theorem allOK : allTo 15001 = true := by decide +kernel

theorem chk_spec (p : ℕ) (h : chk p = true) :
    2^(lg (p^1024)) ≤ p^1024 ∧ p^1024 < 2^(lg (p^1024)+1) := by
  simpa [chk] using h

theorem lo_term (p : ℕ) (hp : 1 ≤ p) (h1 : 2^(lg (p^1024)) ≤ p^1024) :
    ((gL p : ℕ) : ℝ) * (Real.log 2 / (1024 * 1000000000)) ≤ Real.log p / p := by
  unfold gL
  set e := lg (p^1024) with he
  set q := 1000000000/p with hq
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
  have h2 : (e:ℝ) * Real.log 2 ≤ 1024 * Real.log p := by
    have := Real.log_le_log (by positivity) (show ((2:ℝ)^e) ≤ (p:ℝ)^1024 by exact_mod_cast h1)
    rwa [Real.log_pow, Real.log_pow] at this
  have h3 : (q:ℝ) ≤ 1000000000 / p := by
    have := Nat.cast_div_le (α := ℝ) (m := 1000000000) (n := p); push_cast at this; exact this
  have hlp : 0 ≤ Real.log p := Real.log_nonneg hpR
  have h2' : (e:ℝ) * Real.log 2 / 1024 ≤ Real.log p := by linarith
  have h3' : (q:ℝ) / 1000000000 ≤ 1 / p := by
    rw [div_le_iff₀ (by norm_num)]
    calc (q:ℝ) ≤ 1000000000 / p := h3
      _ = 1 / p * 1000000000 := by ring
  have hq0 : (0:ℝ) ≤ q / 1000000000 := by positivity
  have := mul_le_mul h2' h3' hq0 hlp
  push_cast
  calc (e:ℝ) * q * (Real.log 2 / (1024 * 1000000000)) = (e * Real.log 2 / 1024) * (q / 1000000000) := by ring
    _ ≤ Real.log p * (1 / p) := this
    _ = Real.log p / p := by ring

theorem hi_term (p : ℕ) (hp : 1 ≤ p) (h1 : p^1024 < 2^(lg (p^1024)+1)) :
    Real.log p / p ≤ ((gU p : ℕ) : ℝ) * (Real.log 2 / (1024 * 1000000000)) := by
  unfold gU
  set e := lg (p^1024) with he
  set q := 1000000000/p with hq
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
  have h2 : 1024 * Real.log p ≤ ((e:ℝ)+1) * Real.log 2 := by
    have := Real.log_le_log (by positivity) (show (p:ℝ)^1024 ≤ (2:ℝ)^(e+1) by exact_mod_cast h1.le)
    rw [Real.log_pow, Real.log_pow] at this; push_cast at this; exact this
  have h3 : (1000000000:ℕ) < p * (q + 1) := Nat.lt_mul_div_succ _ (by omega)
  have h3R : (1000000000:ℝ) ≤ p * (q+1) := by exact_mod_cast h3.le
  have h2' : Real.log p ≤ ((e:ℝ)+1) * Real.log 2 / 1024 := by linarith
  have h3' : 1 / (p:ℝ) ≤ ((q:ℝ)+1) / 1000000000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h0 : (0:ℝ) ≤ 1 / p := by positivity
  have hb : (0:ℝ) ≤ ((e:ℝ)+1) * Real.log 2 / 1024 := by
    have := Real.log_pos (show (1:ℝ) < 2 by norm_num); positivity
  have := mul_le_mul h2' h3' h0 hb
  push_cast
  calc Real.log p / p = Real.log p * (1 / p) := by ring
    _ ≤ ((e:ℝ)+1) * Real.log 2 / 1024 * (((q:ℝ)+1) / 1000000000) := this
    _ = ((e:ℝ)+1) * ((q:ℝ)+1) * (Real.log 2 / (1024 * 1000000000)) := by ring

theorem log15000_bounds : 14205 * Real.log 2 ≤ 1024 * Real.log 15000 ∧
    1024 * Real.log 15000 ≤ 14206 * Real.log 2 := by
  have a : (2:ℕ)^14205 ≤ 15000^1024 := by decide +kernel
  have b : (15000:ℕ)^1024 ≤ 2^14206 := by decide +kernel
  constructor
  · have := Real.log_le_log (by positivity) (show ((2:ℝ)^14205) ≤ (15000:ℝ)^1024 by exact_mod_cast a)
    rwa [Real.log_pow, Real.log_pow] at this
  · have := Real.log_le_log (by positivity) (show ((15000:ℝ)^1024) ≤ (2:ℝ)^14206 by exact_mod_cast b)
    rw [Real.log_pow, Real.log_pow] at this; push_cast at this; exact this

end LeanLab.LiuWang2002.RSMertens15000.RS62Leaf

namespace LeanLab.LiuWang2002.RSMertens15000

open RS62Leaf in
/-- Rosser-Schoenfeld 1962 p. 72 Theorem 21 display (4.8) at `x = 15000`, in the band used by
`RSMertens1122.rs1962_thm21_at_15000`. PROVED by a kernel certificate: the enclosure is
`[-1.32488, -1.32247]`. -/
theorem rs1962_thm21_at_15000 :
    -1.35 ≤ (∑ p ∈ (Finset.range (⌊(15000 : ℝ)⌋₊ + 1)).filter Nat.Prime, Real.log p / p) - Real.log 15000 ∧
      (∑ p ∈ (Finset.range (⌊(15000 : ℝ)⌋₊ + 1)).filter Nat.Prime, Real.log p / p) - Real.log 15000 ≤ -1.30 := by
  have hfl : ⌊(15000 : ℝ)⌋₊ + 1 = 15001 := by
    rw [show (15000:ℝ) = ((15000:ℕ):ℝ) by norm_num, Nat.floor_natCast]
  rw [hfl]
  set P := (Finset.range 15001).filter Nat.Prime with hP
  have hpos : ∀ p ∈ P, 1 ≤ p := fun p hp => (Finset.mem_filter.mp hp).2.one_lt.le
  have hchk : ∀ p ∈ P, chk p = true := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    have h1' : p < 15001 := Finset.mem_range.mp h1
    exact allTo_spec 15001 allOK p h1' ((isP_iff p (by omega)).mpr h2)
  have hlo : (12248731220588 : ℝ) * (Real.log 2 / (1024 * 1000000000)) ≤ ∑ p ∈ P, Real.log p / p := by
    have := Finset.sum_le_sum (fun p hp => lo_term p (hpos p hp) (chk_spec p (hchk p hp)).1)
    have hs : ∑ p ∈ P, gL p = 12248731220588 := by
      rw [hP, filter_eq, sumTo_eq, sumL]
    rw [← Finset.sum_mul, ← Nat.cast_sum, hs] at this
    push_cast at this
    exact this
  have hhi : ∑ p ∈ P, Real.log p / p ≤ (12251278804167 : ℝ) * (Real.log 2 / (1024 * 1000000000)) := by
    have := Finset.sum_le_sum (fun p hp => hi_term p (hpos p hp) (chk_spec p (hchk p hp)).2)
    have hs : ∑ p ∈ P, gU p = 12251278804167 := by
      rw [hP, filter_eq, sumTo_eq, sumU]
    rw [← Finset.sum_mul, ← Nat.cast_sum, hs] at this
    push_cast at this
    exact this
  obtain ⟨l1, l2⟩ := log15000_bounds
  have t1 := Real.log_two_gt_d9
  have t2 := Real.log_two_lt_d9
  constructor
  · nlinarith
  · nlinarith

end LeanLab.LiuWang2002.RSMertens15000
