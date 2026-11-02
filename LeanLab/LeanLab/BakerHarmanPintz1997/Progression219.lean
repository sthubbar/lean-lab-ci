/-
Baker, Harman and Pintz 1997, page 21, display 3.35.
Exact residue class reindexing and exponential phase normalization.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.LogPhase219
import Mathlib.Data.ZMod.Basic

namespace LeanLab.BakerHarmanPintz1997.Progression219
open Finset PortedVanDerCorput

/-- Page 21. The normalized negative logarithmic phase equals n to the power minus it. -/
theorem eK_log_eq_cpow {x : ℝ} (hx : 0 < x) (t : ℝ) :
    eK ((-t / (2 * Real.pi)) * Real.log x) =
      (x : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
  unfold eK
  have heq : 2 * Real.pi * ((-t / (2 * Real.pi)) * Real.log x) = -t * Real.log x := by
    field_simp
  rw [heq]
  congr 1
  push_cast
  ring

/-- Page 21. Conjugating every character does not change the norm of its finite sum. -/
theorem norm_sum_eK_neg {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ‖∑ i ∈ s, eK (-f i)‖ = ‖∑ i ∈ s, eK (f i)‖ := by
  simp_rw [eK_neg]
  rw [← map_sum, Complex.norm_conj]

/-- Page 21. Frequency signs do not affect these unweighted sum norms. -/
theorem norm_sum_eK_abs {ι : Type*} (s : Finset ι) (f : ι → ℝ) (t : ℝ) :
    ‖∑ i ∈ s, eK (t * f i)‖ = ‖∑ i ∈ s, eK (|t| * f i)‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    simpa only [neg_mul] using (norm_sum_eK_neg s (fun i => t * f i)).symm

/-- Page 21. A residue class sum is an integer interval sum after n equals qm plus r. -/
theorem progression_reindex (f : ℝ → ℂ) {N u : ℝ} (hN : 0 < N) (hNu : N ≤ u)
    (q : ℕ) [NeZero q] (r : ZMod q) :
    (∑ n ∈ (Ioc ⌊N⌋₊ ⌊u⌋₊).filter (fun n : ℕ => (n : ZMod q) = r), f n) =
      ∑ m ∈ Icc (⌊(N - (r.val : ℝ)) / q⌋ + 1 : ℤ) ⌊(u - (r.val : ℝ)) / q⌋,
        f ((q : ℝ) * m + r.val) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hu : 0 ≤ u := (hN.trans_le hNu).le
  have hrepr : ∀ n : ℕ, (n : ZMod q) = r → ∃ m : ℤ, (n : ℤ) = (r.val : ℤ) + q * m := by
    intro n hn
    exact (ZMod.intCast_eq_iff q n r).mp (by simpa only [Int.cast_natCast] using hn)
  have hmem : ∀ (n : ℕ) (m : ℤ), (n : ℤ) = (r.val : ℤ) + q * m →
      (n ∈ Ioc ⌊N⌋₊ ⌊u⌋₊ ↔
        m ∈ Icc (⌊(N - (r.val : ℝ)) / q⌋ + 1 : ℤ) ⌊(u - (r.val : ℝ)) / q⌋) := by
    intro n m hnm
    have hreal : (n : ℝ) = (r.val : ℝ) + (q : ℝ) * m := by exact_mod_cast hnm
    simp only [mem_Ioc, mem_Icc, Nat.floor_lt hN.le, Nat.le_floor_iff hu,
      Int.add_one_le_iff, Int.floor_lt, Int.le_floor]
    rw [div_lt_iff₀ hq, le_div_iff₀ hq]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  symm
  apply sum_bij (fun (m : ℤ) _ => ((r.val : ℤ) + q * m).toNat)
  · intro m hm
    have hlo : (N - (r.val : ℝ)) / q < (m : ℝ) :=
      Int.floor_lt.mp (by have := (mem_Icc.mp hm).1; omega)
    have hpos : (0 : ℝ) < (r.val : ℝ) + (q : ℝ) * m := by
      have := (div_lt_iff₀ hq).mp hlo
      linarith
    have hz : 0 ≤ (r.val : ℤ) + q * m := by exact_mod_cast hpos.le
    have hn : (((r.val : ℤ) + q * m).toNat : ℤ) = (r.val : ℤ) + q * m := Int.toNat_of_nonneg hz
    apply mem_filter.mpr
    refine ⟨(hmem _ _ hn).mpr hm, ?_⟩
    have hr := (ZMod.intCast_eq_iff q (((r.val : ℤ) + q * m).toNat : ℤ) r).mpr ⟨m, hn⟩
    simpa only [Int.cast_natCast] using hr
  · intro m hm k hk heq
    have hmlo : (N - (r.val : ℝ)) / q < (m : ℝ) :=
      Int.floor_lt.mp (by have := (mem_Icc.mp hm).1; omega)
    have hklo : (N - (r.val : ℝ)) / q < (k : ℝ) :=
      Int.floor_lt.mp (by have := (mem_Icc.mp hk).1; omega)
    have hmpos : 0 ≤ (r.val : ℤ) + q * m := by
      have := (div_lt_iff₀ hq).mp hmlo
      have : (0 : ℝ) ≤ (r.val : ℝ) + (q : ℝ) * m := by linarith
      exact_mod_cast this
    have hkpos : 0 ≤ (r.val : ℤ) + q * k := by
      have := (div_lt_iff₀ hq).mp hklo
      have : (0 : ℝ) ≤ (r.val : ℝ) + (q : ℝ) * k := by linarith
      exact_mod_cast this
    have heq' := congrArg (fun n : ℕ => (n : ℤ)) heq
    rw [Int.toNat_of_nonneg hmpos, Int.toNat_of_nonneg hkpos] at heq'
    have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne q
    exact (mul_left_cancel₀ hqz) (by linarith)
  · intro n hn
    obtain ⟨m, hm⟩ := hrepr n (mem_filter.mp hn).2
    refine ⟨m, (hmem _ _ hm).mp (mem_filter.mp hn).1, ?_⟩
    rw [← hm, Int.toNat_natCast]
  · intro m hm
    have hlo : (N - (r.val : ℝ)) / q < (m : ℝ) :=
      Int.floor_lt.mp (by have := (mem_Icc.mp hm).1; omega)
    have hz : 0 ≤ (r.val : ℤ) + q * m := by
      have := (div_lt_iff₀ hq).mp hlo
      have : (0 : ℝ) ≤ (r.val : ℝ) + (q : ℝ) * m := by linarith
      exact_mod_cast this
    congr 1
    have hcast : (((r.val : ℤ) + q * m).toNat : ℝ) = ((r.val : ℤ) + q * m : ℤ) := by
      exact_mod_cast Int.toNat_of_nonneg hz
    rw [hcast]
    push_cast
    ring

/-- Page 21. Exact normalized logarithmic phase identity for the norm of a progression sum. -/
theorem norm_progression_eq_logarithmic {N u t : ℝ} (hN : 0 < N) (hNu : N ≤ u)
    (q : ℕ) [NeZero q] (r : ZMod q) :
    ‖∑ n ∈ (Ioc ⌊N⌋₊ ⌊u⌋₊).filter (fun n : ℕ => (n : ZMod q) = r),
      (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ =
    ‖∑ m ∈ Icc (⌊(N - (r.val : ℝ)) / q⌋ + 1 : ℤ) ⌊(u - (r.val : ℝ)) / q⌋,
      eK ((|t| / (2 * Real.pi)) * (-Real.log ((q : ℝ) * m + r.val)))‖ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have heq := progression_reindex (fun z : ℝ => (z : ℂ) ^ (-(t : ℂ) * Complex.I)) hN hNu q r
  simp only [Complex.ofReal_natCast] at heq
  rw [heq]
  have hphase : (∑ m ∈ Icc (⌊(N - (r.val : ℝ)) / q⌋ + 1 : ℤ) ⌊(u - (r.val : ℝ)) / q⌋,
      (((q : ℝ) * m + r.val : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ∑ m ∈ Icc (⌊(N - (r.val : ℝ)) / q⌋ + 1 : ℤ) ⌊(u - (r.val : ℝ)) / q⌋,
        eK ((t / (2 * Real.pi)) * (-Real.log ((q : ℝ) * m + r.val))) := by
    apply sum_congr rfl
    intro m hm
    have hlo : (N - (r.val : ℝ)) / q < (m : ℝ) :=
      Int.floor_lt.mp (by have := (mem_Icc.mp hm).1; omega)
    have hx : 0 < (q : ℝ) * m + r.val := by
      have := (div_lt_iff₀ hq).mp hlo
      linarith
    rw [← eK_log_eq_cpow hx t]
    congr 1
    ring
  rw [hphase, norm_sum_eK_abs]
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]

/-- Page 21. The absolute bound controls every bounded initial length range. -/
theorem progression_trivial_bound {N u t : ℝ} (hN : 0 < N) (hNu : N ≤ u) (hu : u ≤ 2 * N)
    (q : ℕ) [NeZero q] (r : ZMod q) :
    ‖∑ n ∈ (Ioc ⌊N⌋₊ ⌊u⌋₊).filter (fun n : ℕ => (n : ZMod q) = r),
      (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤ 2 * N := by
  let S := (Ioc ⌊N⌋₊ ⌊u⌋₊).filter (fun n : ℕ => (n : ZMod q) = r)
  have hterm : ∀ n ∈ S, ‖(n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ = 1 := by
    intro n hn
    have hnpos : 0 < n := by have := (mem_Ioc.mp (mem_filter.mp hn).1).1; omega
    have hx : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hh := eK_log_eq_cpow hx t
    simp only [Complex.ofReal_natCast] at hh
    rw [← hh, eK_norm]
  calc
    _ ≤ ∑ n ∈ S, ‖(n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ := norm_sum_le _ _
    _ = (S.card : ℝ) := by simp only [sum_congr rfl hterm, sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ((Ioc ⌊N⌋₊ ⌊u⌋₊).card : ℝ) := by exact_mod_cast card_filter_le _ _
    _ ≤ (⌊u⌋₊ : ℝ) := by rw [Nat.card_Ioc]; exact_mod_cast Nat.sub_le ⌊u⌋₊ ⌊N⌋₊
    _ ≤ u := Nat.floor_le (hN.trans_le hNu).le
    _ ≤ _ := hu

#print axioms norm_progression_eq_logarithmic
#print axioms progression_trivial_bound
#print axioms eK_log_eq_cpow
#print axioms norm_sum_eK_neg
#print axioms norm_sum_eK_abs
#print axioms progression_reindex
end LeanLab.BakerHarmanPintz1997.Progression219
