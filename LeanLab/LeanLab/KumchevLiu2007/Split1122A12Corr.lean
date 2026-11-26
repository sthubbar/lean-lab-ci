/-
BURST 2026-11-22, unit P1122-0146. SPLIT of the cited named hypothesis A12Corr of
Prep1121KLMajorArc.lean, Kumchev and Liu 2007, P0088, arXiv 0801.0130.

Page 5 states hypothesis (A1.2) and page 15 asserts it for lambda1 the indicator of
the primes with f1(u) = 1/log u, when theta1 > 7/12, as "a short interval form of the
Siegel-Walfisz theorem that can be established by the same methods as Huxley's theorem
on primes in short intervals". No proof is printed. The paper's passage from the
standard form to (A1.2) is the partial summation that turns primes counted with
weight log p into primes counted with weight one against the main term 1/log m.

This file cuts A12Corr into
1. the LEAF thetaChi_short, the short interval Siegel-Walfisz theorem in its standard
   theta form, sum over u <= p < v of chi(p) log p minus D(chi) (v - u) up to rounding,
   with any log power saving, for moduli up to a power of log X and windows
   Y = X^(7/12 + eps/2). This is the cited Huxley type input and stays a CITATION WALL;
2. the PROVED transfer a12Corr_of_thetaChi_short, Abel summation with the decreasing
   weight 1/log m, proved here from abel_bound.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121KLMajorArc

namespace LeanLab.KumchevLiu2007.Split1122A12Corr

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Prep1121KLMajor
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 15, the short interval Siegel-Walfisz theorem behind (A1.2), cited
there to the methods of Huxley's theorem on primes in short intervals, Huxley 1972,
Invent. Math. 15, with Siegel's theorem for the moduli up to a power of log X. Theta form:
for every A, every modulus q up to (log X)^B, every character chi mod q and every
subinterval [u, v) of [X - Y, X) with Y = X^(7/12 + eps/2), the sum of chi(p) log p over
primes in [u, v) minus D(chi) times the number of integers in [u, v) is at most
C Y (log X)^(-A). Class HARD: needs a zero density estimate of Huxley strength for
L(s, chi), a zero free region of Vinogradov-Korobov type and Siegel's theorem.
CITATION WALL. -/
theorem thetaChi_short :
    ∀ A : ℝ, 0 < A → ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖∑ m ∈ (Finset.range (⌊X⌋₊ + 1)).filter (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
          ((if m.Prime then χ m * ((Real.log (m : ℝ) : ℝ) : ℂ) else 0) -
            (if χ = 1 then (1 : ℂ) else 0))‖ ≤
          C * windowY X ε * Real.log X ^ (-A) := by
  exact?

/-- PROVED. Abel summation with a nonnegative decreasing weight, the partial summation
step of P0088 page 15 that passes from weight log p to weight one: if every initial
partial sum of c over [a, t) is at most M, the weighted sum over [a, b) is at most
M w(a). Invariant form for the induction. -/
theorem abel_aux (c : ℕ → ℂ) (w : ℕ → ℝ) (a : ℕ) (M : ℝ)
    (hw : ∀ n, a ≤ n → w (n + 1) ≤ w n)
    (hM : ∀ t, a ≤ t → ‖∑ n ∈ Finset.Ico a t, c n‖ ≤ M) :
    ∀ k : ℕ, ‖∑ n ∈ Finset.Ico a (a + k + 1), (w n : ℂ) * c n -
        (w (a + k) : ℂ) * ∑ n ∈ Finset.Ico a (a + k + 1), c n‖ ≤ M * (w a - w (a + k)) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 : a + (k + 1) + 1 = (a + k + 1) + 1 := by ring
    have hle : a ≤ a + k + 1 := by omega
    rw [e1, Finset.sum_Ico_succ_top hle, Finset.sum_Ico_succ_top hle]
    have key : (∑ n ∈ Finset.Ico a (a + k + 1), (w n : ℂ) * c n + (w (a + k + 1) : ℂ) * c (a + k + 1)) -
        (w (a + (k + 1)) : ℂ) * (∑ n ∈ Finset.Ico a (a + k + 1), c n + c (a + k + 1)) =
        (∑ n ∈ Finset.Ico a (a + k + 1), (w n : ℂ) * c n -
          (w (a + k) : ℂ) * ∑ n ∈ Finset.Ico a (a + k + 1), c n) +
        ((w (a + k) - w (a + k + 1) : ℝ) : ℂ) * ∑ n ∈ Finset.Ico a (a + k + 1), c n := by
      have : a + (k + 1) = a + k + 1 := by ring
      rw [this]; push_cast; ring
    rw [key]
    have hd : 0 ≤ w (a + k) - w (a + k + 1) := by
      have := hw (a + k) (by omega); linarith
    have hS := hM (a + k + 1) hle
    calc _ ≤ ‖∑ n ∈ Finset.Ico a (a + k + 1), (w n : ℂ) * c n -
          (w (a + k) : ℂ) * ∑ n ∈ Finset.Ico a (a + k + 1), c n‖ +
          ‖((w (a + k) - w (a + k + 1) : ℝ) : ℂ) * ∑ n ∈ Finset.Ico a (a + k + 1), c n‖ :=
          norm_add_le _ _
      _ ≤ M * (w a - w (a + k)) + (w (a + k) - w (a + k + 1)) * M := by
          gcongr
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd]
          exact mul_le_mul_of_nonneg_left hS hd
      _ = M * (w a - w (a + (k + 1))) := by
          have : a + (k + 1) = a + k + 1 := by ring
          rw [this]; ring

/-- PROVED. Abel summation bound, P0088 page 15 partial summation: for w nonnegative and
decreasing from a on, and every partial sum of c over [a, t) at most M, the sum of
w(n) c(n) over [a, b) is at most M w(a). -/
theorem abel_bound (c : ℕ → ℂ) (w : ℕ → ℝ) (a b : ℕ) (M : ℝ)
    (hw0 : ∀ n, a ≤ n → 0 ≤ w n) (hw : ∀ n, a ≤ n → w (n + 1) ≤ w n)
    (hM : ∀ t, a ≤ t → ‖∑ n ∈ Finset.Ico a t, c n‖ ≤ M) :
    ‖∑ n ∈ Finset.Ico a b, (w n : ℂ) * c n‖ ≤ M * w a := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM a le_rfl)
  rcases Nat.lt_or_ge a b with hab | hab
  · obtain ⟨k, rfl⟩ : ∃ k, b = a + k + 1 := ⟨b - a - 1, by omega⟩
    have h1 := abel_aux c w a M hw hM k
    have h2 := hM (a + k + 1) (by omega)
    have hwk : 0 ≤ w (a + k) := hw0 _ (by omega)
    have split : ∑ n ∈ Finset.Ico a (a + k + 1), (w n : ℂ) * c n =
        (∑ n ∈ Finset.Ico a (a + k + 1), (w n : ℂ) * c n -
          (w (a + k) : ℂ) * ∑ n ∈ Finset.Ico a (a + k + 1), c n) +
        (w (a + k) : ℂ) * ∑ n ∈ Finset.Ico a (a + k + 1), c n := by ring
    rw [split]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ M * (w a - w (a + k)) + w (a + k) * M := by
          gcongr
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hwk]
          exact mul_le_mul_of_nonneg_left h2 hwk
      _ = M * w a := by ring
  · rw [Finset.Ico_eq_empty_of_le hab, Finset.sum_empty, norm_zero]
    exact mul_nonneg hM0 (hw0 a le_rfl)

/-- PROVED. The weight 1/log m is decreasing from 2 on. -/
theorem inv_log_succ_le (n : ℕ) (hn : 2 ≤ n) :
    1 / Real.log ((n + 1 : ℕ) : ℝ) ≤ 1 / Real.log (n : ℝ) := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  apply one_div_le_one_div_of_le hpos
  apply Real.log_le_log (by linarith)
  push_cast; linarith

/-- PROVED. The window [X - Y, X) of page 16 starts above 3 once X is large: for eps at
most 7/18 the exponent 7/12 + eps/2 is at most 7/9. -/
theorem window_start_ge (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 7 / 18) (X : ℝ) (hX : 512 ≤ X) :
    3 ≤ X - windowY X ε := by
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have h1 : windowY X ε ≤ X ^ (7 / 9 : ℝ) := by
    unfold windowY
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have h2 : (4 : ℝ) ≤ X ^ (2 / 9 : ℝ) := by
    have e : (4 : ℝ) = (512 : ℝ) ^ (2 / 9 : ℝ) := by
      rw [show (512 : ℝ) = 2 ^ (9 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [e]
    exact Real.rpow_le_rpow (by norm_num) hX (by norm_num)
  have h3 : X ^ (7 / 9 : ℝ) * X ^ (2 / 9 : ℝ) = X := by
    rw [← Real.rpow_add hX0]; norm_num
  have h4 : X ^ (7 / 9 : ℝ) ≤ X / 4 := by
    have hp : 0 < X ^ (7 / 9 : ℝ) := Real.rpow_pos_of_pos hX0 _
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- PROVED. For 0 <= u <= t <= X the integers of [u, t) in range are the Ico of the
ceilings. -/
theorem filter_eq_Ico (X u t : ℝ) (hu : 0 ≤ u) (ht : t ≤ X) :
    (Finset.range (⌊X⌋₊ + 1)).filter (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < t) =
      Finset.Ico ⌈u⌉₊ ⌈t⌉₊ := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨Nat.ceil_le.mpr h1, Nat.lt_ceil.mpr h2⟩
  · rintro ⟨h1, h2⟩
    have h1' := Nat.ceil_le.mp h1
    have h2' := Nat.lt_ceil.mp h2
    refine ⟨?_, h1', h2'⟩
    have : (m : ℝ) ≤ X := by linarith
    have hX : 0 ≤ X := by linarith
    exact Nat.lt_succ_of_le (Nat.le_floor this)

/-- PROVED. The set of page 5 (A1.2), primeWindow cut to [u, v), is the Ico of the
ceilings when X - Y >= 0. -/
theorem primeWindow_filter_eq_Ico (X Y u v : ℝ) (h0 : 0 ≤ X - Y) (hu : X - Y ≤ u)
    (hv : v ≤ X) :
    (primeWindow X Y).filter (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v) =
      Finset.Ico ⌈u⌉₊ ⌈v⌉₊ := by
  rw [← filter_eq_Ico X u v (by linarith) hv]
  ext m
  simp only [primeWindow, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨h0', -, -⟩, h1, h2⟩
    exact ⟨h0', h1, h2⟩
  · rintro ⟨h0', h1, h2⟩
    exact ⟨⟨h0', by linarith, by linarith⟩, h1, h2⟩

/-- PROVED. P0088 page 15, partial summation from the theta form to (A1.2): the leaf
statement thetaChi_short implies A12Corr. -/
theorem a12Corr_of_thetaChi_short (h : type_of% @thetaChi_short) : A12Corr := by
  intro B hB ε hε hε'
  obtain ⟨C, X1, hC, hk⟩ := h (5 * B) (by linarith) B hB ε hε hε'
  refine ⟨C, max X1 512, hC, ?_⟩
  intro X hX q hq hqB χ u v hu huv hv
  have hX1 : X1 ≤ X := le_trans (le_max_left _ _) hX
  have hX512 : (512 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hstart := window_start_ge ε hε hε' X hX512
  have hu3 : (3 : ℝ) ≤ u := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  set Y := windowY X ε with hYdef
  set c : ℕ → ℂ := fun m => (if m.Prime then χ m * ((Real.log (m : ℝ) : ℝ) : ℂ) else 0) -
    (if χ = 1 then (1 : ℂ) else 0) with hc
  set w : ℕ → ℝ := fun m => 1 / Real.log (m : ℝ) with hw
  set a := ⌈u⌉₊ with ha
  have ha3 : 2 < a := Nat.lt_ceil.mpr (by push_cast; linarith)
  set b := ⌈v⌉₊ with hb
  set M : ℝ := C * Y * Real.log X ^ (-(5 * B)) with hMdef
  have hY0 : 0 ≤ X - Y := by linarith
  -- the defect is the weighted sum of c over [a, b)
  have hdef : primeDefect χ X Y u v = ∑ n ∈ Finset.Ico a b, (w n : ℂ) *
      (if n < b then c n else 0) := by
    unfold primeDefect
    rw [primeWindow_filter_eq_Ico X Y u v hY0 hu hv]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mem_Ico] at hm
    have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm.1.trans' ha3
    have hlog : Real.log (m : ℝ) ≠ 0 := (Real.log_pos (by linarith)).ne'
    have hlogC : ((Real.log (m : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
    rw [if_pos hm.2, hc, hw]
    simp only [Complex.ofReal_div, Complex.ofReal_one]
    split_ifs
    · field_simp
    · field_simp; ring
    · ring
    · ring
  -- every truncated partial sum is a leaf sum
  have hpart : ∀ t, a ≤ t → ‖∑ n ∈ Finset.Ico a t, (if n < b then c n else 0)‖ ≤ M := by
    intro t hat
    set t' := min t b with ht'
    have hsum : ∑ n ∈ Finset.Ico a t, (if n < b then c n else 0) =
        ∑ n ∈ Finset.Ico a t', c n := by
      rw [← Finset.sum_filter]
      congr 1
      ext n; simp [Finset.mem_Ico, ht']
    rw [hsum]
    set s : ℝ := min (t' : ℝ) v with hs
    have hceil : ⌈s⌉₊ = t' := by
      rcases le_total (t' : ℝ) v with h | h
      · rw [hs, min_eq_left h, Nat.ceil_natCast]
      · rw [hs, min_eq_right h]
        have h1 : t' ≤ b := min_le_right _ _
        have h2 : b ≤ t' := Nat.ceil_le.mpr h
        omega
    have hus : u ≤ s := by
      rw [hs]
      refine le_min ?_ huv
      have h1 : u ≤ (a : ℝ) := Nat.le_ceil u
      have h2 : a ≤ t' := le_min hat (by
        rcases Nat.lt_or_ge a b with h | h
        · exact h.le
        · exact le_trans (Nat.ceil_mono huv) le_rfl)
      exact h1.trans (by exact_mod_cast h2)
    have hsv : s ≤ v := min_le_right _ _
    have hk' := hk X hX1 q hq hqB χ u s hu hus (hsv.trans hv)
    rw [filter_eq_Ico X u s (by linarith) (hsv.trans hv), hceil] at hk'
    exact hk'
  have hab := abel_bound (fun n => if n < b then c n else 0) w a b M
    (fun n hn => by
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn.trans' ha3
      exact one_div_nonneg.mpr (Real.log_nonneg (by linarith)))
    (fun n hn => by
      have := inv_log_succ_le n (by omega)
      simpa [hw] using this)
    hpart
  have hwa : w a ≤ 1 := by
    have h3 : (3 : ℝ) ≤ a := by exact_mod_cast ha3
    have hl : 1 < Real.log (a : ℝ) := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    rw [hw]; simp only
    rw [div_le_one (by linarith)]; exact hl.le
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hpart a le_rfl)
  have hpow : Real.log X ^ (-(5 * B)) = (Real.log X ^ B) ^ (-5 : ℤ) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul hlogX.le]
    congr 1; push_cast; ring
  rw [hdef]
  calc _ ≤ M * w a := hab
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hwa hM0
    _ = _ := by rw [mul_one, hMdef, hpow]

/-- A12Corr from the one LEAF thetaChi_short by the proved partial summation, so the
named hypothesis of Prep1121KLMajorArc now rests on the cited theta form only.
CONDITIONAL ON the LEAF thetaChi_short, the Huxley type citation wall. -/
theorem a12Corr : A12Corr := a12Corr_of_thetaChi_short thetaChi_short

end LeanLab.KumchevLiu2007.Split1122A12Corr
