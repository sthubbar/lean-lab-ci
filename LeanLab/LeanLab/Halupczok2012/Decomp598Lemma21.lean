import LeanLab.Halupczok2012.Decomp532a
import LeanLab.Halupczok2012.Decomp598Pointwise

/-!
The dyadic overlap moment supplied directly by Lemma 2.1 for U-1672.
Source: Halupczok journal pages 336 and 340.
https://doi.org/10.5802/jtnb.839
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp598Lemma21

open Finset
open scoped Classical

/-- Finite duality extracts the overlap moment from a progression norm estimate.
This is the reverse Cauchy Schwarz substitution behind page 340. -/
theorem overlap_of_norm_bound {ι κ : Type*} (W : Finset ι) (U : Finset κ)
    (p : κ → ι → Prop) [∀ q n, Decidable (p q n)] (F : ℝ) (hF : 0 ≤ F)
    (hb : ∀ w : ι → ℂ,
      (∑ q ∈ U, ‖∑ n ∈ W.filter (p q), w n‖) ≤
        F * Real.sqrt (∑ n ∈ W, ‖w n‖ ^ 2)) :
    ∑ n ∈ W, ((U.filter (fun q => p q n)).card : ℝ) ^ 2 ≤ F ^ 2 := by
  let m : ι → ℝ := fun n => ((U.filter (fun q => p q n)).card : ℝ)
  have hm0 (n : ι) : 0 ≤ m n := Nat.cast_nonneg _
  let E := ∑ n ∈ W, m n ^ 2
  have hE : 0 ≤ E := sum_nonneg fun _ _ => sq_nonneg _
  have heach (q : κ) : ‖∑ n ∈ W.filter (p q), (m n : ℂ)‖ =
      ∑ n ∈ W.filter (p q), m n := by
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sum_nonneg fun n _ => hm0 n)]
  have hx : (∑ q ∈ U, ∑ n ∈ W.filter (p q), m n) = E := by
    simp_rw [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    change (∑ q ∈ U, if p q n then m n else 0) = m n ^ 2
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    dsimp [m]
    ring
  have hh := hb (fun n => (m n : ℂ))
  simp_rw [heach] at hh
  rw [hx] at hh
  have he : (∑ n ∈ W, ‖(m n : ℂ)‖ ^ 2) = E := by
    apply sum_congr rfl
    intro n _
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [he] at hh
  change E ≤ F ^ 2
  have hs := Real.sq_sqrt hE
  have hs0 := Real.sqrt_nonneg E
  nlinarith [sq_nonneg (F - Real.sqrt E)]

/-- The dyadic overlap moment follows directly from the existing lemma21_eventual.
This assembly is CONDITIONAL ON its existing Voronoi input. -/
theorem dyadic_overlap_eventual (a : ℤ) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ (X N : ℝ) (Q : ℕ),
      X0 ≤ X → 0 ≤ N → N ≤ X → 1 ≤ Q → (Q : ℝ) ≤ X →
      ∑ n ∈ kRange X N,
        (((Ico Q (2 * Q)).filter (fun q : ℕ => (n : ℤ) ≡ a [ZMOD q])).card : ℝ) ^ 2 ≤
          C * (N + (Q : ℝ) ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ)) * Real.log (X + 1) ^ 3 := by
  obtain ⟨C, X0, hC, hb⟩ := Decomp532a.lemma21_eventual a
  refine ⟨C ^ 2, max X0 1, by positivity, ?_⟩
  intro X N Q hX hN hNX hQ1 hQX
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 ≤ Real.log (X + 1) := Real.log_nonneg (by linarith)
  have hS : 0 ≤ N + (Q : ℝ) ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ) := by positivity
  have hh := overlap_of_norm_bound (kRange X N) (Ico Q (2 * Q))
    (fun q n : ℕ => (n : ℤ) ≡ a [ZMOD q])
    (C * Real.sqrt (N + (Q : ℝ) ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ)) *
      Real.log (X + 1) ^ (3 / 2 : ℝ)) (by positivity)
    (fun w => hb X N Q w ((le_max_left _ _).trans hX) hN hNX hQ1 hQX)
  have hpow : (Real.log (X + 1) ^ (3 / 2 : ℝ)) ^ 2 = Real.log (X + 1) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
    norm_num
  simpa only [mul_pow, Real.sq_sqrt hS, hpow] using hh

/-- Split the full positive modulus interval into dyadic blocks on page 340. -/
theorem sum_dyadic_blocks (g : ℕ → ℝ) (d : ℕ) :
    (∑ q ∈ Ico 1 (2 ^ d), g q) =
      ∑ j ∈ range d, ∑ q ∈ Ico (2 ^ j) (2 * 2 ^ j), g q := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, ← ih, pow_succ, Nat.mul_comm (2 ^ d) 2,
      sum_Ico_consecutive g (Nat.one_le_two_pow) (by omega)]

/-- A common bound for dyadic blocks bounds the full cutoff on page 340. -/
theorem cutoff_le_dyadic_blocks (g : ℕ → ℝ) (N : ℕ) (F : ℝ)
    (hg : ∀ q, 0 ≤ g q)
    (hb : ∀ j ∈ range (Nat.log 2 N + 1),
      (∑ q ∈ Ico (2 ^ j) (2 * 2 ^ j), g q) ≤ F) :
    (∑ q ∈ Icc 1 N, g q) ≤ (Nat.log 2 N + 1 : ℕ) * F := by
  calc
    _ ≤ ∑ q ∈ Ico 1 (2 ^ (Nat.log 2 N + 1)), g q := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact mem_Ico.mpr ⟨(mem_Icc.mp hq).1,
          lt_of_le_of_lt (mem_Icc.mp hq).2 (Nat.lt_pow_succ_log_self (by decide) N)⟩
      · intro q _ _
        exact hg q
    _ = ∑ j ∈ range (Nat.log 2 N + 1), ∑ q ∈ Ico (2 ^ j) (2 * 2 ^ j), g q :=
      sum_dyadic_blocks g _
    _ ≤ ∑ _j ∈ range (Nat.log 2 N + 1), F := sum_le_sum hb
    _ = _ := by simp

/-- Full small cutoff overlap from the existing dyadic lemma21_eventual.
The number of dyadic blocks is retained explicitly. -/
theorem cutoff_overlap_eventual (a : ℤ) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ (X N : ℝ) (Q : ℕ),
      X0 ≤ X → 0 ≤ N → N ≤ X → 1 ≤ Q → (Q : ℝ) ≤ X →
      ∑ n ∈ kRange X N,
        (((Icc 1 Q).filter (fun q : ℕ => (n : ℤ) ≡ a [ZMOD q])).card : ℝ) ^ 2 ≤
          C * ((Nat.log 2 Q + 1 : ℕ) : ℝ) ^ 2 *
            (N + (Q : ℝ) ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ)) * Real.log (X + 1) ^ 3 := by
  obtain ⟨C, X0, hC, hb⟩ := Decomp532a.lemma21_eventual a
  refine ⟨C ^ 2, max X0 1, by positivity, ?_⟩
  intro X N Q hX hN hNX hQ1 hQX
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 ≤ Real.log (X + 1) := Real.log_nonneg (by linarith)
  have hS : 0 ≤ N + (Q : ℝ) ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ) := by positivity
  let F := C * Real.sqrt (N + (Q : ℝ) ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ)) *
    Real.log (X + 1) ^ (3 / 2 : ℝ)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hfull (w : ℕ → ℂ) :
      (∑ q ∈ Icc 1 Q, ‖∑ n ∈ (kRange X N).filter
        (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), w n‖) ≤
        ((Nat.log 2 Q + 1 : ℕ) : ℝ) * F * Real.sqrt (∑ n ∈ kRange X N, ‖w n‖ ^ 2) := by
    have hh := cutoff_le_dyadic_blocks
      (fun q : ℕ => ‖∑ n ∈ (kRange X N).filter
        (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), w n‖) Q
      (F * Real.sqrt (∑ n ∈ kRange X N, ‖w n‖ ^ 2)) (fun _ => norm_nonneg _) ?_
    · simpa [mul_assoc] using hh
    intro j hj
    have hjQ : 2 ^ j ≤ Q := by
      calc
        _ ≤ 2 ^ Nat.log 2 Q := Nat.pow_le_pow_right (by decide) (by simpa using mem_range.mp hj)
        _ ≤ Q := Nat.pow_log_le_self 2 (by omega)
    have hjX : ((2 ^ j : ℕ) : ℝ) ≤ X :=
      (show ((2 ^ j : ℕ) : ℝ) ≤ Q by exact_mod_cast hjQ).trans hQX
    have hblock := hb X N (2 ^ j) w ((le_max_left _ _).trans hX) hN hNX
      Nat.one_le_two_pow hjX
    apply hblock.trans
    dsimp [F]
    gcongr
  have hh := overlap_of_norm_bound (kRange X N) (Icc 1 Q)
    (fun q n : ℕ => (n : ℤ) ≡ a [ZMOD q])
    (((Nat.log 2 Q + 1 : ℕ) : ℝ) * F) (by positivity) hfull
  have hpow : (Real.log (X + 1) ^ (3 / 2 : ℝ)) ^ 2 = Real.log (X + 1) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
    norm_num
  dsimp [F] at hh
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hS, hpow] at hh
  convert hh using 1 <;> ring

/-- Large divisors have distinct small complementary divisors.
This controls moduli above the left endpoint in the page 340 overlap bound. -/
theorem large_divisor_count_le (U : Finset ℕ) (s L B : ℕ)
    (hs : 0 < s) (hL : 0 < L) (hsB : s ≤ L * B)
    (hU : ∀ q ∈ U, L < q) :
    (U.filter (fun q => q ∣ s)).card ≤ B := by
  let V := U.filter (fun q => q ∣ s)
  have maps : Set.MapsTo (fun q => s / q) V (Icc 1 B) := by
    intro q hq
    obtain ⟨hqU, hqs⟩ := mem_filter.mp hq
    have hq0 : 0 < q := lt_trans hL (hU q hqU)
    apply mem_Icc.mpr
    constructor
    · exact Nat.div_pos (Nat.le_of_dvd hs hqs) hq0
    · change s / q ≤ B
      have hh : s < (B + 1) * q := by nlinarith [hU q hqU]
      have := (Nat.div_lt_iff_lt_mul hq0).mpr hh
      omega
  have hinj : Set.InjOn (fun q => s / q) V := by
    intro q hq r hr he
    change s / q = s / r at he
    have hq0 : 0 < q := lt_trans hL (hU q (mem_filter.mp hq).1)
    have hr0 : 0 < r := lt_trans hL (hU r (mem_filter.mp hr).1)
    have hdq := Nat.div_mul_cancel (mem_filter.mp hq).2
    have hdr := Nat.div_mul_cancel (mem_filter.mp hr).2
    have hdiv : 0 < s / q := Nat.div_pos (Nat.le_of_dvd hs (mem_filter.mp hq).2) hq0
    rw [← he] at hdr
    exact Nat.eq_of_mul_eq_mul_left hdiv (hdq.trans hdr.symm)
  simpa using card_le_card_of_injOn (fun q => s / q) maps hinj

/-- The even integer window embeds into the doubled full window on page 340. -/
theorem even_window_sum_le (X R : ℝ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    (∑ k ∈ kRange X R, f (2 * k)) ≤ ∑ n ∈ kRange (2 * X) (2 * R), f n := by
  have hi : Set.InjOn (fun k : ℕ => 2 * k) (kRange X R) := by
    intro k _ j _ he
    change 2 * k = 2 * j at he
    omega
  have hsub : (kRange X R).image (fun k => 2 * k) ⊆ kRange (2 * X) (2 * R) := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
    have hkR := (mem_filter.mp hk).2
    have hlo : 2 * X < ((2 * k : ℕ) : ℝ) := by push_cast; linarith
    have hhi : ((2 * k : ℕ) : ℝ) ≤ 2 * X + 2 * R := by push_cast; linarith
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, hlo, hhi⟩
    exact_mod_cast hhi.trans (Nat.le_ceil (2 * X + 2 * R))
  calc
    _ = ∑ n ∈ (kRange X R).image (fun k => 2 * k), f n := (sum_image hi).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)

/-- Split a progression count at L and bound the large divisors by four.
This elementary tail extends the small modulus form of Lemma 2.1. -/
theorem progression_count_split (n Q L : ℕ) (a : ℤ) (hL : 0 < L)
    (hn : 0 < (n : ℤ) - a) (hnL : (n : ℤ) - a ≤ 4 * L) :
    (((Icc 1 Q).filter (fun q : ℕ => (n : ℤ) ≡ a [ZMOD q])).card : ℝ) ^ 2 ≤
      2 * (((Icc 1 (min Q L)).filter (fun q : ℕ => (n : ℤ) ≡ a [ZMOD q])).card : ℝ) ^ 2 + 32 := by
  let U := (Icc 1 Q).filter (fun q : ℕ => (n : ℤ) ≡ a [ZMOD q])
  let s := ((n : ℤ) - a).toNat
  have hs : (s : ℤ) = (n : ℤ) - a := Int.toNat_of_nonneg hn.le
  have hs0 : 0 < s := by exact_mod_cast (show (0 : ℤ) < s by rw [hs]; exact hn)
  have hsL : s ≤ L * 4 := by
    have hh : (s : ℤ) ≤ (L * 4 : ℕ) := by rw [hs]; push_cast; linarith
    exact_mod_cast hh
  let T := (Icc 1 Q).filter (fun q => L < q)
  have hTail := large_divisor_count_le T s L 4 hs0 hL hsL
    (fun q hq => (mem_filter.mp hq).2)
  have he : U.filter (fun q => ¬ q ≤ L) = T.filter (fun q => q ∣ s) := by
    ext q
    simp only [U, T, mem_filter, not_le]
    have hp : (n : ℤ) ≡ a [ZMOD q] ↔ q ∣ s := by
      rw [← Int.natCast_dvd_natCast, hs, Int.modEq_iff_dvd, dvd_sub_comm]
    tauto
  have hsmall : U.filter (fun q => q ≤ L) =
      (Icc 1 (min Q L)).filter (fun q : ℕ => (n : ℤ) ≡ a [ZMOD q]) := by
    ext q
    simp only [U, mem_filter, mem_Icc, le_min_iff]
    tauto
  have hc := card_filter_add_card_filter_not (s := U) (fun q => q ≤ L)
  rw [he, hsmall] at hc
  have hcount : U.card ≤
      ((Icc 1 (min Q L)).filter (fun q : ℕ => (n : ℤ) ≡ a [ZMOD q])).card + 4 := by omega
  have hR : (U.card : ℝ) ≤
      (((Icc 1 (min Q L)).filter (fun q : ℕ => (n : ℤ) ≡ a [ZMOD q])).card : ℝ) + 4 := by
    exact_mod_cast hcount
  have h0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  have hsmall0 : (0 : ℝ) ≤
      ((Icc 1 (min Q L)).filter (fun q : ℕ => (n : ℤ) ≡ a [ZMOD q])).card := Nat.cast_nonneg _
  change (U.card : ℝ) ^ 2 ≤ _
  nlinarith [sq_nonneg ((((Icc 1 (min Q L)).filter
    (fun q : ℕ => (n : ℤ) ≡ a [ZMOD q])).card : ℝ) - 4)]

/-- The number of dyadic blocks is bounded by a constant times log Y.
This accounts for the full cutoff loss in the direct Lemma 2.1 route. -/
theorem block_count_log_bound {c Y : ℝ} (hc : 0 < c) (hY : Real.exp 1 ≤ Y)
    (N : ℕ) (hN : 1 ≤ N) (hNY : (N : ℝ) ≤ c * Y ^ 2) :
    ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤
      ((|Real.log c| + 3) / Real.log 2 + 1) * Real.log Y := by
  have hY0 : 0 < Y := (Real.exp_pos 1).trans_le hY
  have hL : 1 ≤ Real.log Y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hY
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : Real.log ((2 : ℝ) ^ Nat.log 2 N) ≤ Real.log N :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0))
  rw [Real.log_pow] at hp
  have hnlog := Decomp532a.polynomial_log_bound hc hY hN0 hNY
  have hd : (Nat.log 2 N : ℝ) ≤ ((|Real.log c| + 3) * Real.log Y) / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    linarith
  push_cast
  rw [add_mul, div_mul_eq_mul_div]
  linarith

set_option maxHeartbeats 800000 in
/-- The full even overlap estimate on page 340, directly from lemma21_eventual.
The explicit dyadic extension costs two logarithmic powers.
This assembly is CONDITIONAL ON the existing Voronoi leaf only. -/
theorem fixed_even_moment_via_lemma21 (c K : ℝ) (hc : 0 < c) (hK : 0 < K) (a : ℤ) :
    ∃ C Y0 : ℝ, 0 < C ∧ ∀ X Y Q : ℝ,
      Y0 ≤ Y → 1 ≤ Y → Y ≤ X → X ≤ K * Y ^ 2 → (a : ℝ) ≤ X →
      1 ≤ Q → Q ≤ c * Y ^ (3 / 2 : ℝ) * X ^ (-(1 / 2) : ℝ) →
      ∑ k ∈ kRange X Y,
        (((Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => ((2 * k : ℕ) : ℤ) ≡ a [ZMOD q])).card : ℝ) ^ 2 ≤
          C * Y * Real.log Y ^ 5 := by
  obtain ⟨CV, XV, hCV, hV⟩ := cutoff_overlap_eventual a
  let DE := (3 * c ^ 2) ^ (1 / 3 : ℝ)
  let DB := (|Real.log c| + 3) / Real.log 2 + 1
  let LM := |Real.log (2 * K + 1)| + 3
  let CC := CV * DB ^ 2 * (2 + DE) * LM ^ 3
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDB : 0 < DB := by dsimp [DB]; positivity
  have hLM : 0 < LM := by dsimp [LM]; positivity
  have hDE : 0 ≤ DE := Real.rpow_nonneg (by positivity) _
  have hCC : 0 < CC := by dsimp [CC]; positivity
  refine ⟨2 * CC + 64, max (Real.exp 1) (max XV (|(a : ℝ)| + 4)), by positivity, ?_⟩
  intro X Y Q hY hY1 hYX hX ha hQ1 hQ
  have hYe : Real.exp 1 ≤ Y := (le_max_left _ _).trans hY
  have hYV : XV ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYa : |(a : ℝ)| + 4 ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans hY)
  have hY4 : 4 ≤ Y := by linarith [abs_nonneg (a : ℝ)]
  have hY0 : 0 < Y := by linarith
  have hX0 : 0 < X := hY0.trans_le hYX
  have hX4 : 4 ≤ X := hY4.trans hYX
  have hL1 : 1 ≤ Real.log Y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hYe
  have hQ0 : 0 ≤ Q := by linarith
  let P := min ⌊Q⌋₊ ⌊2 * X⌋₊
  have hfloor : 2 * X < (⌊2 * X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hL : 1 ≤ ⌊2 * X⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hP1 : 1 ≤ P := le_min (Nat.le_floor (by simpa using hQ1)) hL
  have hPQ : (P : ℝ) ≤ Q :=
    (show (P : ℝ) ≤ ⌊Q⌋₊ by exact_mod_cast min_le_left _ _).trans (Nat.floor_le hQ0)
  have hPX : (P : ℝ) ≤ 2 * X :=
    (show (P : ℝ) ≤ ⌊2 * X⌋₊ by exact_mod_cast min_le_right _ _).trans (Nat.floor_le (by linarith))
  have hPlevel : (P : ℝ) ≤ c * Y ^ (3 / 2 : ℝ) * X ^ (-(1 / 2) : ℝ) := hPQ.trans hQ
  have hPpoly : (P : ℝ) ≤ c * Y ^ 2 :=
    Decomp532a.level_polynomial_bound hc hY1 le_rfl hYX hPlevel
  have hblocks : ((Nat.log 2 P + 1 : ℕ) : ℝ) ≤ DB * Real.log Y :=
    block_count_log_bound hc hYe P hP1 hPpoly
  have hErr : (2 * X) ^ (1 / 3 : ℝ) * (P : ℝ) ^ (2 / 3 : ℝ) ≤ DE * Y :=
    Decomp532a.level_third_absorption hc hY0 hX0 (by positivity) (by positivity)
      (by linarith) hPlevel
  have hArg : 2 * Y + (P : ℝ) ^ (2 / 3 : ℝ) * (2 * X) ^ (1 / 3 : ℝ) ≤ (2 + DE) * Y := by
    nlinarith
  have hlog : Real.log (2 * X + 1) ≤ LM * Real.log Y := by
    have hh := Decomp532a.polynomial_log_bound (by positivity : 0 < 2 * K + 1)
      hYe (by linarith : 0 < 2 * X + 1) (by nlinarith [sq_nonneg (Y - 1)])
    dsimp [LM]
    linarith
  have hlog0 : 0 ≤ Real.log (2 * X + 1) := Real.log_nonneg (by linarith)
  have hSmall := hV (2 * X) (2 * Y) P (by linarith) (by positivity) (by linarith) hP1 hPX
  have hSmall' : ∑ n ∈ kRange (2 * X) (2 * Y),
      (((Icc 1 P).filter (fun q : ℕ => (n : ℤ) ≡ a [ZMOD q])).card : ℝ) ^ 2 ≤
        CC * Y * Real.log Y ^ 5 := by
    apply hSmall.trans
    calc
      _ ≤ CV * (DB * Real.log Y) ^ 2 * ((2 + DE) * Y) * (LM * Real.log Y) ^ 3 := by
        gcongr
      _ = _ := by dsimp [CC]; ring
  have hEven := even_window_sum_le X Y
    (fun n => (((Icc 1 P).filter (fun q : ℕ => (n : ℤ) ≡ a [ZMOD q])).card : ℝ) ^ 2)
    (fun _ => sq_nonneg _)
  have hSplit : ∑ k ∈ kRange X Y,
      (((Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => ((2 * k : ℕ) : ℤ) ≡ a [ZMOD q])).card : ℝ) ^ 2 ≤
      2 * (∑ k ∈ kRange X Y,
        (((Icc 1 P).filter (fun q : ℕ => ((2 * k : ℕ) : ℤ) ≡ a [ZMOD q])).card : ℝ) ^ 2) +
        32 * ((kRange X Y).card : ℝ) := by
    calc
      _ ≤ ∑ k ∈ kRange X Y,
          (2 * (((Icc 1 P).filter (fun q : ℕ => ((2 * k : ℕ) : ℤ) ≡ a [ZMOD q])).card : ℝ) ^ 2 + 32) := by
        apply sum_le_sum
        intro k hk
        have hkR := (mem_filter.mp hk).2
        apply progression_count_split (2 * k) ⌊Q⌋₊ ⌊2 * X⌋₊ a hL
        · exact_mod_cast (show (0 : ℝ) < ((2 * k : ℕ) : ℝ) - a by push_cast; linarith [hkR.1])
        · have hnega : -(a : ℝ) ≤ X := (neg_le_abs _).trans (by linarith)
          exact_mod_cast (show ((2 * k : ℕ) : ℝ) - a ≤ 4 * (⌊2 * X⌋₊ : ℝ) by
            push_cast
            linarith [hkR.2])
      _ = _ := by rw [sum_add_distrib, ← mul_sum]; simp; ring
  have hcard : ((kRange X Y).card : ℝ) ≤ 2 * Y :=
    (card_kRange_le hY0.le).trans (by linarith)
  have hpow : 1 ≤ Real.log Y ^ 5 := one_le_pow₀ hL1
  have hsmall_final := hEven.trans hSmall'
  dsimp [CC] at hCC
  calc
    _ ≤ 2 * (CC * Y * Real.log Y ^ 5) + 64 * Y := by nlinarith
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 64 * Y)]

end LeanLab.Halupczok2012.Decomp598Lemma21
