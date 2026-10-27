/-
P0022, Kaniecki 1995, the near diagonal sum behind (21), p. 370.
PC run 20261021T0604Z-1697, unit U-1368, T1.

`Near21` of Lemma5Bound21.lean: `Σ a_m a_n` over the pairs with `2 |log m - log n| < δ`,
`a_n = Λ(n) n^{-2σ}`, is at most `0.886 + log² T/(8T a²c²) + log T/(4T² ac)`.
Proof here: `a_m a_n ≤ (a_m² + a_n²)/2` and the symmetry of the condition give
`near21 ≤ Σ_m a_m² N(m)`, `N(m)` the number of `n` with `2 |log m - log n| < δ`; `N(m)` counts
integers in `(m e^{-δ/2}, m e^{δ/2})`, an interval of length at most `m/T`, so `N(m) ≤ 1 + m/T`;
hence `near21 ≤ Σ Λ(n)² n^{-4σ} + T⁻¹ Σ Λ(n)² n^{-(4σ-1)}`. With `4σ - 1 = 1 + 4ac/log T` this is
`0.886 + log² T/(8T a²c²)` from two named inputs about `Λ` alone:
`DiagLam2`, `Σ Λ(n)²/n² ≤ 0.886`, numerically 0.80521, numerics/U1368_lamsq.out;
`LamSq2`, `Σ Λ(n)² n^{-s} ≤ 2/(s-1)²` for `1 < s ≤ 2`, numerically the left side times
`(s-1)²` is between 0.80 and 1.00 on that range, the classical `1/(s-1)² + O(1)`.
So `Near21` is CONDITIONAL ON `DiagLam2` and `LamSq2`.
AI wrote this Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Kaniecki1995.Lemma5Kernel9A

namespace LeanLab.Kaniecki1995.L5

open LeanLab.Kaniecki1995 Real MeasureTheory Set Filter
open scoped ArithmeticFunction.vonMangoldt

/-! ### The named inputs, statements about `Λ` only -/

/-- `Σ Λ(n)²/n² ≤ 0.886`. CITED numerical input, about 0.80521. -/
def DiagLam2 : Prop := ∑' n : ℕ, Λ n ^ 2 * (n : ℝ) ^ (-(2 : ℝ)) ≤ 0.886

/-- `Σ Λ(n)² n^{-s} ≤ 2/(s-1)²` for `1 < s ≤ 2`. CITED, a Chebyshev type bound. -/
def LamSq2 : Prop :=
  ∀ s : ℝ, 1 < s → s ≤ 2 → ∑' n : ℕ, Λ n ^ 2 * (n : ℝ) ^ (-s) ≤ 2 / (s - 1) ^ 2

/-! ### Summability -/

theorem summable_lamSq {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ => Λ n ^ 2 * (n : ℝ) ^ (-s) := by
  set ε := (s - 1) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  have hS := (summable_aL (σ := (s - ε) / 2) (by simp only [ε]; linarith)).mul_left ε⁻¹
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hS
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [aL]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Λ n ≤ (n : ℝ) ^ ε / ε :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_rpow_div hn'.le hε)
  unfold aL
  have e : (n : ℝ) ^ (-(2 * ((s - ε) / 2))) = (n : ℝ) ^ ε * (n : ℝ) ^ (-s) := by
    rw [← Real.rpow_add hn']; congr 1; ring
  rw [e, sq]
  have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have h1 : 0 ≤ (n : ℝ) ^ (-s) := by positivity
  calc Λ n * Λ n * (n : ℝ) ^ (-s) ≤ Λ n * ((n : ℝ) ^ ε / ε) * (n : ℝ) ^ (-s) := by gcongr
    _ = ε⁻¹ * (Λ n * ((n : ℝ) ^ ε * (n : ℝ) ^ (-s))) := by field_simp

theorem aL_sq (σ : ℝ) (n : ℕ) : aL σ n ^ 2 = Λ n ^ 2 * (n : ℝ) ^ (-(4 * σ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [aL]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold aL
  rw [mul_pow, sq ((n : ℝ) ^ _), ← Real.rpow_add hn']
  congr 2; ring

theorem aL_sq_mul (σ : ℝ) (n : ℕ) :
    aL σ n ^ 2 * n = Λ n ^ 2 * (n : ℝ) ^ (-(4 * σ - 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [aL]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [aL_sq, mul_assoc]
  congr 1
  conv_lhs => arg 2; rw [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hn']; congr 1; ring

/-! ### Counting the near partners of `m` -/

/-- the near diagonal condition -/
abbrev nr (T : ℝ) (m n : ℕ) : Prop := 2 * |Real.log m - Real.log n| < dl T

theorem nr_symm (T : ℝ) (m n : ℕ) : nr T m n ↔ nr T n m := by
  unfold nr; rw [abs_sub_comm]

theorem dl_lt_log2 {T : ℝ} (hT : 1 < T) : dl T < Real.log 2 := by
  unfold dl
  refine Real.log_lt_log (by positivity) ?_
  have : 1 / T < 1 := (div_lt_one (by linarith)).2 hT
  linarith

theorem exp_half_dl {T : ℝ} (hT : 0 < T) :
    Real.exp (dl T / 2) - Real.exp (-(dl T / 2)) ≤ 1 / T := by
  set u := Real.exp (dl T / 2)
  have hu : 1 ≤ u := Real.one_le_exp (by have := dl_pos hT; linarith)
  have hu2 : u ^ 2 = 1 + 1 / T := by
    simp only [u]; rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (dl T / 2) = dl T by ring, dl,
      Real.exp_log (by positivity)]
  rw [Real.exp_neg]
  have hu0 : 0 < u := by positivity
  have hT' : 0 < 1 / T := by positivity
  have e : u - u⁻¹ = (u ^ 2 - 1) / u := by field_simp
  rw [e, hu2, add_sub_cancel_left]
  exact div_le_self hT'.le hu

theorem mem_of_nr {T : ℝ} (hT : 1 < T) {m n : ℕ} (hm : 2 ≤ m) (h : nr T m n) :
    (m : ℝ) * Real.exp (-(dl T / 2)) < n ∧ (n : ℝ) < m * Real.exp (dl T / 2) := by
  unfold nr at h
  have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlogm : Real.log 2 ≤ Real.log m :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hm)
  have hd := dl_lt_log2 hT
  have hab := abs_lt.1 (show |Real.log m - Real.log n| < dl T / 2 by linarith)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exfalso; simp at hab; have := dl_pos (by linarith : (0 : ℝ) < T); linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rw [← Real.exp_log hm', ← Real.exp_add, ← Real.exp_log hn']
    exact Real.exp_lt_exp.2 (by linarith)
  · rw [← Real.exp_log hm', ← Real.exp_add, ← Real.exp_log hn']
    exact Real.exp_lt_exp.2 (by linarith)

theorem card_Ioo_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ((Finset.Ioo ⌊x⌋₊ ⌈y⌉₊).card : ℝ) ≤ y - x + 1 := by
  have hc : (Finset.Ioo ⌊x⌋₊ ⌈y⌉₊).card + ⌊x⌋₊ + 1 ≤ ⌈y⌉₊ ∨
      (Finset.Ioo ⌊x⌋₊ ⌈y⌉₊).card = 0 := by
    rw [Nat.card_Ioo]; omega
  have h1 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one (hx.trans hxy)
  have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  rcases hc with hc | hc
  · have : ((Finset.Ioo ⌊x⌋₊ ⌈y⌉₊).card : ℝ) + ⌊x⌋₊ + 1 ≤ ⌈y⌉₊ := by exact_mod_cast hc
    linarith
  · rw [hc]; push_cast; linarith

/-- `N(m) ≤ 1 + m/T`, in the form used: the row sum of the condition. -/
theorem row_le {T : ℝ} (hT : 1 < T) (σ : ℝ) (m : ℕ) :
    Summable (fun n : ℕ => if nr T m n then aL σ m ^ 2 else 0) ∧
      ∑' n : ℕ, (if nr T m n then aL σ m ^ 2 else 0) ≤ aL σ m ^ 2 * (1 + m / T) := by
  have hT0 : 0 < T := by linarith
  rcases lt_or_ge m 2 with hm | hm
  · have h0 : aL σ m = 0 := by
      unfold aL
      interval_cases m <;> simp [ArithmeticFunction.vonMangoldt_apply]
    simp [h0]
  set x := (m : ℝ) * Real.exp (-(dl T / 2))
  set y := (m : ℝ) * Real.exp (dl T / 2)
  set S := Finset.Ioo ⌊x⌋₊ ⌈y⌉₊
  have hx : 0 ≤ x := by positivity
  have hxy : x ≤ y := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (by have := dl_pos hT0; linarith)) (Nat.cast_nonneg m)
  have hsupp : ∀ n ∉ S, (if nr T m n then aL σ m ^ 2 else 0) = 0 := by
    intro n hn
    rw [if_neg]
    intro h
    obtain ⟨h1, h2⟩ := mem_of_nr hT hm h
    exact hn (Finset.mem_Ioo.2 ⟨(Nat.floor_lt hx).2 h1, Nat.lt_ceil.2 h2⟩)
  refine ⟨summable_of_ne_finset_zero hsupp, ?_⟩
  rw [tsum_eq_sum hsupp]
  have hle : ∑ n ∈ S, (if nr T m n then aL σ m ^ 2 else 0) ≤ ∑ n ∈ S, aL σ m ^ 2 :=
    Finset.sum_le_sum fun n _ => by split_ifs <;> simp [sq_nonneg]
  refine hle.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have hc := card_Ioo_le hx hxy
  have hyx : y - x ≤ m / T := by
    have h := mul_le_mul_of_nonneg_left (exp_half_dl hT0) (Nat.cast_nonneg (α := ℝ) m)
    calc y - x = (m : ℝ) * (Real.exp (dl T / 2) - Real.exp (-(dl T / 2))) := by ring
      _ ≤ (m : ℝ) * (1 / T) := h
      _ = m / T := by ring
  linarith

/-! ### `near21 ≤ Σ a_m² (1 + m/T)` -/

theorem near21_le {T σ : ℝ} (hT : 1 < T) (hσ : 1 / 2 < σ) :
    near21 T σ ≤ ∑' m : ℕ, aL σ m ^ 2 * (1 + m / T) := by
  have hT0 : 0 < T := by linarith
  set f1 : ℕ × ℕ → ℝ := fun p => if nr T p.1 p.2 then aL σ p.1 ^ 2 else 0
  set f2 : ℕ × ℕ → ℝ := fun p => if nr T p.1 p.2 then aL σ p.2 ^ 2 else 0
  have hf1n : 0 ≤ f1 := fun p => by simp only [f1]; split_ifs <;> simp [sq_nonneg]
  have hS4 := summable_lamSq (s := 4 * σ) (by linarith)
  have hS41 := summable_lamSq (s := 4 * σ - 1) (by linarith)
  have hrowsum : Summable fun m : ℕ => aL σ m ^ 2 * (1 + m / T) := by
    have : (fun m : ℕ => aL σ m ^ 2 * (1 + m / T)) = fun m =>
        Λ m ^ 2 * (m : ℝ) ^ (-(4 * σ)) + T⁻¹ * (Λ m ^ 2 * (m : ℝ) ^ (-(4 * σ - 1))) := by
      funext m; rw [← aL_sq, ← aL_sq_mul]; field_simp
    rw [this]; exact hS4.add (hS41.mul_left _)
  have hs1 : Summable f1 := by
    refine (summable_prod_of_nonneg hf1n).2 ⟨fun m => (row_le hT σ m).1, ?_⟩
    exact Summable.of_nonneg_of_le (fun m => tsum_nonneg fun n => hf1n (m, n))
      (fun m => (row_le hT σ m).2) hrowsum
  have hswap : ∀ p, f2 p = f1 (Prod.swap p) := fun p => by
    simp only [f1, f2, Prod.fst_swap, Prod.snd_swap]
    by_cases h : nr T p.1 p.2
    · rw [if_pos h, if_pos ((nr_symm T _ _).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((nr_symm T _ _).2 h'))]
  have hs2 : Summable f2 := by
    have : f2 = f1 ∘ Prod.swap := funext hswap
    rw [this]; exact (Equiv.prodComm ℕ ℕ).summable_iff.2 hs1
  have ht2 : ∑' p, f2 p = ∑' p, f1 p := by
    rw [show f2 = f1 ∘ Prod.swap from funext hswap]
    exact (Equiv.prodComm ℕ ℕ).tsum_eq f1
  have hpt : ∀ p : ℕ × ℕ, (if 2 * |Real.log p.1 - Real.log p.2| < dl T then
      aL σ p.1 * aL σ p.2 else 0) ≤ (1 / 2) * f1 p + (1 / 2) * f2 p := by
    intro p
    simp only [f1, f2]
    change (if nr T p.1 p.2 then aL σ p.1 * aL σ p.2 else 0) ≤ _
    split_ifs
    · nlinarith [sq_nonneg (aL σ p.1 - aL σ p.2)]
    · simp
  unfold near21
  calc ∑' p : ℕ × ℕ, (if 2 * |Real.log p.1 - Real.log p.2| < dl T then
        aL σ p.1 * aL σ p.2 else 0)
      ≤ ∑' p, ((1 / 2) * f1 p + (1 / 2) * f2 p) :=
        (summable_near hσ).tsum_le_tsum hpt ((hs1.mul_left _).add (hs2.mul_left _))
    _ = ∑' p, f1 p := by
        rw [Summable.tsum_add (hs1.mul_left _) (hs2.mul_left _)]
        simp only [tsum_mul_left, ht2]; ring
    _ = ∑' m, ∑' n, f1 (m, n) := hs1.tsum_prod' fun m => (row_le hT σ m).1
    _ ≤ ∑' m : ℕ, aL σ m ^ 2 * (1 + m / T) :=
        (Summable.of_nonneg_of_le (fun m => tsum_nonneg fun n => hf1n (m, n))
          (fun m => (row_le hT σ m).2) hrowsum).tsum_le_tsum (fun m => (row_le hT σ m).2)
          hrowsum

/-! ### `Near21`, CONDITIONAL ON `DiagLam2` and `LamSq2` -/

theorem diag_le (hD : DiagLam2) {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∑' n : ℕ, Λ n ^ 2 * (n : ℝ) ^ (-(4 * σ)) ≤ 0.886 := by
  refine le_trans ?_ hD
  refine (summable_lamSq (by linarith)).tsum_le_tsum (fun n => ?_)
    (summable_lamSq (by norm_num))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hn) (by linarith)) (sq_nonneg _)

/-- **`Near21`**, CONDITIONAL ON `DiagLam2` and `LamSq2`. -/
theorem near21_of (hD : DiagLam2) (hL : LamSq2) : Near21 := by
  intro a c T hT hc ha hs
  have hT1 : 1 < T := by linarith
  have hT0 : 0 < T := by linarith
  have hσ := sig_gt_half hT hc ha
  set σ := sig a c T
  have hL0 : 0 < Real.log T := Real.log_pos hT1
  have hac : 0 < a * c := mul_pos (by linarith) hc
  have h4 : 4 * σ - 1 - 1 = 4 * (a * c) / Real.log T := by simp only [σ, sig]; ring
  have hS4 := summable_lamSq (s := 4 * σ) (by linarith)
  have hS41 := summable_lamSq (s := 4 * σ - 1) (by linarith)
  refine (near21_le hT1 hσ).trans ?_
  have hsplit : ∑' m : ℕ, aL σ m ^ 2 * (1 + m / T) =
      ∑' m : ℕ, Λ m ^ 2 * (m : ℝ) ^ (-(4 * σ)) +
        T⁻¹ * ∑' m : ℕ, Λ m ^ 2 * (m : ℝ) ^ (-(4 * σ - 1)) := by
    rw [← tsum_mul_left, ← Summable.tsum_add hS4 (hS41.mul_left _)]
    refine tsum_congr fun m => ?_
    rw [← aL_sq, ← aL_sq_mul]; field_simp
  rw [hsplit]
  have hB := hL (4 * σ - 1) (by linarith) (by linarith)
  rw [h4] at hB
  have hmain : T⁻¹ * (2 / (4 * (a * c) / Real.log T) ^ 2) =
      Real.log T ^ 2 / (8 * T * a ^ 2 * c ^ 2) := by
    field_simp; ring
  have hlast : 0 ≤ Real.log T / (4 * T ^ 2 * a * c) := by
    have : 0 < 4 * T ^ 2 * a * c := by
      have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) (pow_pos hT0 2)) hac
      linarith [show 4 * T ^ 2 * a * c = 4 * T ^ 2 * (a * c) by ring]
    positivity
  have hD' := diag_le hD hσ
  have hTi : 0 ≤ T⁻¹ := inv_nonneg.2 hT0.le
  nlinarith [mul_le_mul_of_nonneg_left hB hTi]

/-- **(21), p. 370**, CONDITIONAL ON `DiagLam2` and `LamSq2` only. -/
theorem bound21_proved (hD : DiagLam2) (hL : LamSq2) : Bound21 :=
  bound21_of_near (near21_of hD hL)

/-- **Lemma 5, p. 368**, CONDITIONAL ON Lemma 4, `Parseval1920`, `DiagLam2`, `LamSq2`, `Const4`. -/
theorem lemma5_of_lam (h4 : Lemma4) (hP : Parseval1920) (hD : DiagLam2) (hL : LamSq2)
    (hC : Const4) : Lemma5 :=
  lemma5_of_near h4 hP (near21_of hD hL) hC

/-- Vacuity: the range hypotheses of `LamSq2` are satisfiable, at `s = 1.5`, and the bound of
`row_le` is attained shape wise: `N(2) ≤ 1 + 2/T` at `T = 10`. -/
theorem lamSq2_hyps : (1 : ℝ) < 1.5 ∧ (1.5 : ℝ) ≤ 2 := by norm_num

/-- Vacuity: `DiagLam2` is not trivial, its sum is at least the positive term `Λ(2)²/4`. -/
theorem diagLam2_nontrivial :
    Λ 2 ^ 2 * ((2 : ℕ) : ℝ) ^ (-(2 : ℝ)) ≤ ∑' n : ℕ, Λ n ^ 2 * (n : ℝ) ^ (-(2 : ℝ)) ∧
      0 < Λ 2 ^ 2 * ((2 : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
  refine ⟨(summable_lamSq (by norm_num)).le_tsum 2 (fun n _ => by positivity), ?_⟩
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

end LeanLab.Kaniecki1995.L5

#print axioms LeanLab.Kaniecki1995.L5.summable_lamSq
#print axioms LeanLab.Kaniecki1995.L5.aL_sq
#print axioms LeanLab.Kaniecki1995.L5.aL_sq_mul
#print axioms LeanLab.Kaniecki1995.L5.exp_half_dl
#print axioms LeanLab.Kaniecki1995.L5.mem_of_nr
#print axioms LeanLab.Kaniecki1995.L5.card_Ioo_le
#print axioms LeanLab.Kaniecki1995.L5.row_le
#print axioms LeanLab.Kaniecki1995.L5.near21_le
#print axioms LeanLab.Kaniecki1995.L5.diag_le
#print axioms LeanLab.Kaniecki1995.L5.near21_of
#print axioms LeanLab.Kaniecki1995.L5.bound21_proved
#print axioms LeanLab.Kaniecki1995.L5.lemma5_of_lam
#print axioms LeanLab.Kaniecki1995.L5.lamSq2_hyps
#print axioms LeanLab.Kaniecki1995.L5.diagLam2_nontrivial
