/-
Independent split of the long coefficient replacement step of the periodic kernel
reduction. The replacement error is bounded at each even frequency by a logarithmic
saving times the mass of the short block, the mass itself is estimated from the
divisor type bound, the number of frequencies is counted, and the elementary
thresholds are collected separately.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561n
import LeanLab.BHP1997.EnergyLogC165
import LeanLab.BHP1997.Route512MajorSq

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

/-- LEAF. Counting step. The even frequencies below the frequency height form an
arithmetic progression of even numbers inside an interval of length at most that
height plus two, so their number is at most twice the height. Only the cardinality of
that progression is used here, with no analytic input. -/
theorem leaf_long_frequency_card561 (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ((frequencies512 ε x).card : ℝ) ≤
        2 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
  set H : ℝ := (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) with hH
  have hHpos : 0 < H := by
    rw [hH]
    have h1 : (0 : ℝ) < 11 / 20 + ε := by linarith
    have h2 : (0 : ℝ) < 2 * (1 / 16 - 1 / 10 ^ 5) := by norm_num
    exact mul_pos h1 h2
  refine ⟨1, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := hx
  have hH1 : (1 : ℝ) ≤ x ^ H := Real.one_le_rpow hx1 (le_of_lt hHpos)
  have hdefeq : frequencies512 ε x = (Finset.Icc ⌈x⌉₊ ⌊x + x ^ H⌋₊).filter (fun N => Even N) := by
    rw [frequencies512, ← hH]
  have hfloor : x ≤ (⌊x + x ^ H⌋₊ : ℝ) := by
    have h1 : x + x ^ H < (⌊x + x ^ H⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hle : ⌈x⌉₊ ≤ ⌊x + x ^ H⌋₊ + 1 :=
    le_trans (Nat.ceil_le.mpr hfloor) (Nat.le_succ _)
  have hfilter : (frequencies512 ε x).card ≤ (Finset.Icc ⌈x⌉₊ ⌊x + x ^ H⌋₊).card := by
    rw [hdefeq]
    exact Finset.card_filter_le _ _
  have hcardIcc : ((Finset.Icc ⌈x⌉₊ ⌊x + x ^ H⌋₊).card : ℝ)
      ≤ (⌊x + x ^ H⌋₊ : ℝ) + 1 - (⌈x⌉₊ : ℝ) := by
    rw [Nat.card_Icc, Nat.cast_sub hle]
    push_cast
    linarith
  calc ((frequencies512 ε x).card : ℝ)
      ≤ ((Finset.Icc ⌈x⌉₊ ⌊x + x ^ H⌋₊).card : ℝ) := by exact_mod_cast hfilter
    _ ≤ (⌊x + x ^ H⌋₊ : ℝ) + 1 - (⌈x⌉₊ : ℝ) := hcardIcc
    _ ≤ x ^ H + 1 := by
        have hb : (⌊x + x ^ H⌋₊ : ℝ) ≤ x + x ^ H := Nat.floor_le (by positivity)
        have ha : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
        linarith
    _ ≤ 2 * x ^ H := by linarith

open Classical Complex Finset LeanLab.BHP1997.Decomp561d

private theorem card_multiples561 (N d : ℕ) (hd : 0 < d) :
    ((Finset.Ioc 0 N).filter (fun m => d ∣ m)).card = N / d := by
  set s := (Finset.Ioc 0 N).filter (fun m => d ∣ m) with hs
  have hinto : ∀ m ∈ s, m / d ∈ Finset.Ioc 0 (N / d) := by
    intro m hm
    rw [hs, Finset.mem_filter, Finset.mem_Ioc] at hm
    obtain ⟨⟨hm0, hmN⟩, j, hj⟩ := hm
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · rw [h, Nat.mul_zero] at hj
        omega
      · exact h
    have h1 : m / d ≤ N / d := Nat.div_le_div_right hmN
    rw [hj, Nat.mul_div_cancel_left j hd] at h1
    rw [Finset.mem_Ioc, hj, Nat.mul_div_cancel_left j hd]
    exact ⟨hj0, h1⟩
  have hinj : Set.InjOn (fun m => m / d) ↑s := by
    intro a ha b hb hab
    have ha' : a ∈ s := ha
    have hb' : b ∈ s := hb
    rw [hs, Finset.mem_filter] at ha' hb'
    have hab' : a / d = b / d := hab
    rw [← Nat.div_mul_cancel ha'.2, ← Nat.div_mul_cancel hb'.2, hab']
  have himg : s.image (fun m => m / d) = Finset.Ioc 0 (N / d) := by
    apply Finset.Subset.antisymm
    · intro k hk
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
      exact hinto m hm
    · intro k hk
      rw [Finset.mem_Ioc] at hk
      refine Finset.mem_image.mpr ⟨d * k, ?_, Nat.mul_div_cancel_left k hd⟩
      rw [hs, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨Nat.mul_pos hd hk.1, by
        rw [Nat.mul_comm]
        exact (Nat.le_div_iff_mul_le hd).mp hk.2⟩, dvd_mul_right d k⟩
  have h1 : #(s.image (fun m => m / d)) = #s := Finset.card_image_of_injOn hinj
  rw [himg, Nat.card_Ioc, Nat.sub_zero] at h1
  exact h1.symm

private theorem sum_divisors_card_le561 (N : ℕ) :
    ∑ m ∈ Finset.Ioc 0 N, ((m.divisors.card : ℕ) : ℝ) ≤ (N : ℝ) * (1 + Real.log N) := by
  have hterm : ∀ m ∈ Finset.Ioc 0 N, ((m.divisors.card : ℕ) : ℝ)
      = ∑ d ∈ Finset.Icc 1 N, (if d ∣ m then (1 : ℝ) else 0) := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    obtain ⟨hm0, hmN⟩ := hm
    have hmn0 : m ≠ 0 := by omega
    have hset : m.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ m) := by
      ext d
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdv, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdv hm0,
          le_trans (Nat.le_of_dvd hm0 hdv) hmN⟩, hdv⟩
      · rintro ⟨⟨hd1, -⟩, hdv⟩
        exact ⟨hdv, hmn0⟩
    rw [hset, Finset.card_filter]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  calc ∑ m ∈ Finset.Ioc 0 N, ((m.divisors.card : ℕ) : ℝ)
      = ∑ m ∈ Finset.Ioc 0 N, ∑ d ∈ Finset.Icc 1 N, (if d ∣ m then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl hterm
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Ioc 0 N, (if d ∣ m then (1 : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 N, (((Finset.Ioc 0 N).filter (fun m => d ∣ m)).card : ℝ) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.card_filter]
        simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    _ ≤ ∑ d ∈ Finset.Icc 1 N, (N : ℝ) / (d : ℝ) := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        rw [Finset.mem_Icc] at hd
        rw [card_multiples561 N d (by omega : 0 < d)]
        exact Nat.cast_div_le
    _ = (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, (d : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [div_eq_mul_inv]
    _ = (N : ℝ) * ((harmonic N : ℚ) : ℝ) := by
        congr 1
        rw [harmonic_eq_sum_Icc]
        simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ (N : ℝ) * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity)

/-- The short-block mass leaf in the regime `B ≤ 1`: the coefficient bound is dominated by the
divisor count itself, whose block sum is `N (1 + log N)` by the elementary double count. -/
private theorem long_short_mass_le_one561 (B C₀ : ℝ) (hB : B ≤ 1) :
    ∃ K M : ℝ, 1 ≤ K ∧ 1 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ b : ℕ → ℂ,
        (∀ k : ℕ, ‖b k‖ ≤ C₀ * ((k.divisors.card : ℕ) : ℝ) ^ B) →
        ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖ ≤
          K * length512 ε x * Real.log x ^ M := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max 1 C₀, 2, le_max_left _ _, by norm_num, fun ε hε => ?_⟩
  by_cases hC : 0 ≤ C₀
  · set A : ℝ := max 1 (2 * (11 / 20 + ε) + 2 * (1 + Real.log 2) + 1) with hA
    refine ⟨Real.exp A, fun x hx => ?_⟩
    intro b hb
    have hA1 : 1 ≤ A := le_max_left _ _
    have hA2 : 2 * (11 / 20 + ε) + 2 * (1 + Real.log 2) + 1 ≤ A := le_max_right _ _
    have hxA : A ≤ Real.log x := by
      have h1 : Real.log (Real.exp A) ≤ Real.log x := Real.log_le_log (Real.exp_pos A) hx
      rwa [Real.log_exp] at h1
    have ht1 : 1 ≤ Real.log x := le_trans hA1 hxA
    have ht0 : 0 ≤ Real.log x := le_trans zero_le_one ht1
    have hx1 : (1 : ℝ) ≤ x := by
      have h2 : (1 : ℝ) ≤ Real.exp A := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith)
      linarith
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    have hL1 : 1 ≤ length512 ε x := by
      rw [length512]
      exact Real.one_le_rpow hx1 (by linarith)
    have hL0 : (0 : ℝ) < length512 ε x := lt_of_lt_of_le zero_lt_one hL1
    have hN2 : 2 ≤ ⌊2 * length512 ε x⌋₊ := by
      apply Nat.le_floor
      have h2 : (2 : ℝ) * 1 ≤ 2 * length512 ε x :=
        mul_le_mul_of_nonneg_left hL1 (by norm_num)
      simpa using h2
    have hN1 : (1 : ℝ) ≤ (⌊2 * length512 ε x⌋₊ : ℝ) := by
      have h : (2 : ℝ) ≤ (⌊2 * length512 ε x⌋₊ : ℝ) := by exact_mod_cast hN2
      linarith
    have hNpos : (0 : ℝ) < (⌊2 * length512 ε x⌋₊ : ℝ) := by
      have h : 0 < ⌊2 * length512 ε x⌋₊ := by omega
      exact_mod_cast h
    have hbase := sum_divisors_card_le561 ⌊2 * length512 ε x⌋₊
    have hsub : Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊
        ⊆ Finset.Ioc 0 ⌊2 * length512 ε x⌋₊ := by
      intro m hm
      rw [Finset.mem_Ioc] at hm ⊢
      exact ⟨by omega, hm.2⟩
    have hprod : Real.log (2 * length512 ε x) = Real.log 2 + (11 / 20 + ε) * Real.log x := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hL0), length512, Real.log_rpow hx0]
    have hτ : ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
          ((m.divisors.card : ℕ) : ℝ) ≤ length512 ε x * Real.log x ^ (2 : ℝ) := by
      have hmono : ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
            ((m.divisors.card : ℕ) : ℝ)
          ≤ ∑ m ∈ Finset.Ioc 0 ⌊2 * length512 ε x⌋₊, ((m.divisors.card : ℕ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
      calc ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
            ((m.divisors.card : ℕ) : ℝ)
          ≤ ∑ m ∈ Finset.Ioc 0 ⌊2 * length512 ε x⌋₊, ((m.divisors.card : ℕ) : ℝ) := hmono
        _ ≤ (⌊2 * length512 ε x⌋₊ : ℝ) * (1 + Real.log (⌊2 * length512 ε x⌋₊ : ℝ)) := hbase
        _ ≤ (2 * length512 ε x) * (1 + Real.log (2 * length512 ε x)) := by
            refine mul_le_mul (Nat.floor_le (by positivity)) ?_ ?_ (by positivity)
            · have := Real.log_le_log hNpos (Nat.floor_le (by positivity) :
                (⌊2 * length512 ε x⌋₊ : ℝ) ≤ 2 * length512 ε x)
              linarith
            · have := Real.log_nonneg hN1
              linarith
        _ = length512 ε x * (2 * (1 + Real.log 2 + (11 / 20 + ε) * Real.log x)) := by
            rw [hprod]
            ring
        _ ≤ length512 ε x * Real.log x ^ (2 : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hL0)
            have hprod2 : (2 * (11 / 20 + ε) + 2 * (1 + Real.log 2)) * Real.log x
                ≤ Real.log x * Real.log x := mul_le_mul_of_nonneg_right (by linarith) ht0
            rw [Real.rpow_two]
            nlinarith [hprod2, ht1]
    have hbB : ∀ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
        ‖b m‖ ≤ C₀ * ((m.divisors.card : ℕ) : ℝ) := by
      intro m hm
      rw [Finset.mem_Ioc] at hm
      have hd1 : (1 : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := by
        have hpos : 0 < m.divisors.card :=
          Finset.card_pos.mpr ⟨1, by rw [Nat.one_mem_divisors]; omega⟩
        exact_mod_cast hpos
      calc ‖b m‖ ≤ C₀ * ((m.divisors.card : ℕ) : ℝ) ^ B := hb m
        _ ≤ C₀ * ((m.divisors.card : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hd1 hB) hC
    calc ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖
        ≤ ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
            C₀ * ((m.divisors.card : ℕ) : ℝ) := Finset.sum_le_sum hbB
      _ = C₀ * ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
            ((m.divisors.card : ℕ) : ℝ) := by rw [Finset.mul_sum]
      _ ≤ C₀ * (length512 ε x * Real.log x ^ (2 : ℝ)) := mul_le_mul_of_nonneg_left hτ hC
      _ ≤ max 1 C₀ * (length512 ε x * Real.log x ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _)
            (mul_nonneg (le_of_lt hL0) (Real.rpow_nonneg ht0 2))
      _ = max 1 C₀ * length512 ε x * Real.log x ^ (2 : ℝ) := by ring
  · have hCn : C₀ < 0 := not_le.mp hC
    refine ⟨3, fun x hx => ?_⟩
    intro b hb
    have hx3 : (3 : ℝ) ≤ x := hx
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hb0 : ∀ k : ℕ, b k = 0 := by
      intro k
      have h1 : ‖b k‖ ≤ C₀ * ((k.divisors.card : ℕ) : ℝ) ^ B := hb k
      by_cases hk : k = 0
      · subst hk
        have hz : ((Nat.divisors 0).card : ℝ) = 0 := by simp
        rw [hz] at h1
        have hnn : C₀ * (0 : ℝ) ^ B ≤ 0 := by
          have hv := Real.rpow_nonneg (le_refl (0 : ℝ)) B
          nlinarith [hCn, hv]
        exact norm_eq_zero.mp (le_antisymm (le_trans h1 hnn) (norm_nonneg _))
      · have hd : 0 < ((k.divisors.card : ℕ) : ℝ) := by
          have hpos : 0 < k.divisors.card :=
            Finset.card_pos.mpr ⟨1, by rw [Nat.one_mem_divisors]; exact hk⟩
          exact_mod_cast hpos
        have h2 : C₀ * ((k.divisors.card : ℕ) : ℝ) ^ B < 0 :=
          mul_neg_of_neg_of_pos hCn (Real.rpow_pos_of_pos hd B)
        exact norm_eq_zero.mp (le_antisymm (le_trans h1 h2.le) (norm_nonneg _))
    have hzero : ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖ = 0 := by
      refine Finset.sum_eq_zero (fun m _ => ?_)
      rw [hb0 m, norm_zero]
    rw [hzero]
    have hL0 : (0 : ℝ) ≤ length512 ε x := by
      rw [length512]
      exact Real.rpow_nonneg hx0 _
    have hlog0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
    have hfin : (0 : ℝ) ≤ length512 ε x * Real.log x ^ (2 : ℝ) :=
      mul_nonneg hL0 (Real.rpow_nonneg hlog0 2)
    have hK1 : (1 : ℝ) ≤ max 1 C₀ := le_max_left _ _
    have hmul : (1 : ℝ) * (length512 ε x * Real.log x ^ (2 : ℝ))
        ≤ max 1 C₀ * (length512 ε x * Real.log x ^ (2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hK1 hfin
    have heq : max 1 C₀ * length512 ε x * Real.log x ^ (2 : ℝ)
        = max 1 C₀ * (length512 ε x * Real.log x ^ (2 : ℝ)) := by ring
    rw [heq]
    linarith

open Classical Complex Finset LeanLab.BHP1997.Decomp561d

private theorem long_short_mass_of_divisor_moment561 (B C₀ : ℝ)
    (hmom : ∃ K M : ℝ, 1 ≤ K ∧ 1 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
          ((m.divisors.card : ℕ) : ℝ) ^ B ≤ K * length512 ε x * Real.log x ^ M) :
    ∃ K M : ℝ, 1 ≤ K ∧ 1 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ b : ℕ → ℂ,
        (∀ k : ℕ, ‖b k‖ ≤ C₀ * ((k.divisors.card : ℕ) : ℝ) ^ B) →
        ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖ ≤
          K * length512 ε x * Real.log x ^ M := by
  obtain ⟨K, M, hK, hM, hmom⟩ := hmom
  by_cases hC : 0 ≤ C₀
  · refine ⟨max 1 (C₀ * K), M, le_max_left _ _, hM, fun ε hε => ?_⟩
    obtain ⟨X, hX⟩ := hmom ε hε
    refine ⟨max X 3, fun x hx b hb => ?_⟩
    have hxX : X ≤ x := le_trans (le_max_left _ _) hx
    have hx3 : (3 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hlog0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
    have hL0 : (0 : ℝ) ≤ length512 ε x := by
      rw [length512]
      exact Real.rpow_nonneg hx0 _
    calc ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖
        ≤ ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
            C₀ * ((m.divisors.card : ℕ) : ℝ) ^ B :=
          Finset.sum_le_sum (fun m _ => hb m)
      _ = C₀ * ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
            ((m.divisors.card : ℕ) : ℝ) ^ B := by rw [Finset.mul_sum]
      _ ≤ C₀ * (K * length512 ε x * Real.log x ^ M) :=
          mul_le_mul_of_nonneg_left (hX x hxX) hC
      _ = (C₀ * K) * (length512 ε x * Real.log x ^ M) := by ring
      _ ≤ max 1 (C₀ * K) * (length512 ε x * Real.log x ^ M) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _)
            (mul_nonneg hL0 (Real.rpow_nonneg hlog0 M))
      _ = max 1 (C₀ * K) * length512 ε x * Real.log x ^ M := by ring
  · have hCn : C₀ < 0 := not_le.mp hC
    refine ⟨1, 1, le_rfl, le_rfl, fun ε hε => ?_⟩
    refine ⟨3, fun x hx b hb => ?_⟩
    have hx3 : (3 : ℝ) ≤ x := hx
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hb0 : ∀ k : ℕ, b k = 0 := by
      intro k
      have h1 : ‖b k‖ ≤ C₀ * ((k.divisors.card : ℕ) : ℝ) ^ B := hb k
      by_cases hk : k = 0
      · subst hk
        have hz : ((Nat.divisors 0).card : ℝ) = 0 := by simp
        rw [hz] at h1
        have hnn : C₀ * (0 : ℝ) ^ B ≤ 0 := by
          have hv := Real.rpow_nonneg (le_refl (0 : ℝ)) B
          nlinarith [hCn, hv]
        exact norm_eq_zero.mp (le_antisymm (le_trans h1 hnn) (norm_nonneg _))
      · have hd : 0 < ((k.divisors.card : ℕ) : ℝ) := by
          have hpos : 0 < k.divisors.card :=
            Finset.card_pos.mpr ⟨1, by rw [Nat.one_mem_divisors]; exact hk⟩
          exact_mod_cast hpos
        have h2 : C₀ * ((k.divisors.card : ℕ) : ℝ) ^ B < 0 :=
          mul_neg_of_neg_of_pos hCn (Real.rpow_pos_of_pos hd B)
        exact norm_eq_zero.mp (le_antisymm (le_trans h1 h2.le) (norm_nonneg _))
    have hzero : ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖ = 0 := by
      refine Finset.sum_eq_zero (fun m _ => ?_)
      rw [hb0 m, norm_zero]
    rw [hzero]
    have hL0 : (0 : ℝ) ≤ length512 ε x := by
      rw [length512]
      exact Real.rpow_nonneg hx0 _
    have hlog0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
    have hfin : (0 : ℝ) ≤ length512 ε x * Real.log x ^ (1 : ℝ) :=
      mul_nonneg hL0 (Real.rpow_nonneg hlog0 1)
    nlinarith [hfin]

private theorem divisor_power_moment561 (k : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, ((n.divisors.card : ℕ) : ℝ) ^ k) ≤
      (N : ℝ) * (1 + Real.log N) ^ ((2 ^ ⌈k⌉₊ : ℕ) : ℝ) := by
  set m : ℕ := ⌈k⌉₊
  rw [Real.rpow_natCast]
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := Finset.ext (fun n => by
    simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega)
  have hterm : ∀ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ k ≤
      (N : ℝ) * (((n.divisors.card : ℕ) : ℝ) ^ m / (n : ℝ)) := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hτ : (1 : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
    have hk : ((n.divisors.card : ℕ) : ℝ) ^ k ≤ ((n.divisors.card : ℕ) : ℝ) ^ m := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hτ (Nat.le_ceil k)
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast h2
    have hpos : 0 ≤ ((n.divisors.card : ℕ) : ℝ) ^ m / (n : ℝ) := by positivity
    calc ((n.divisors.card : ℕ) : ℝ) ^ k ≤ ((n.divisors.card : ℕ) : ℝ) ^ m := hk
      _ = (n : ℝ) * (((n.divisors.card : ℕ) : ℝ) ^ m / (n : ℝ)) := by field_simp
      _ ≤ (N : ℝ) * (((n.divisors.card : ℕ) : ℝ) ^ m / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hnN hpos
  rw [hIoc]
  calc (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ k)
      ≤ ∑ n ∈ Finset.Icc 1 N, (N : ℝ) * (((n.divisors.card : ℕ) : ℝ) ^ m / (n : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (N : ℝ) * LeanLab.BHP1997.EnergyLogC165.harmonicDivisorMoment m N := by
        rw [← Finset.mul_sum]; rfl
    _ ≤ (N : ℝ) * (1 + Real.log N) ^ (2 ^ m) :=
        mul_le_mul_of_nonneg_left
          (LeanLab.BHP1997.EnergyLogC165.harmonicDivisorMoment_le m N) (Nat.cast_nonneg N)

private theorem block_divisor_moment561 (B : ℝ) :
    ∃ K M : ℝ, 1 ≤ K ∧ 1 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
          ((m.divisors.card : ℕ) : ℝ) ^ B ≤ K * length512 ε x * Real.log x ^ M := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2, ((2 ^ ⌈B⌉₊ + 1 : ℕ) : ℝ), by norm_num, ?_, fun ε hε => ?_⟩
  · have h' : (1 : ℝ) ≤ ((2 ^ ⌈B⌉₊ + 1 : ℕ) : ℝ) := by
      have h : (1 : ℕ) ≤ 2 ^ ⌈B⌉₊ + 1 := Nat.succ_le_succ (Nat.zero_le _)
      exact_mod_cast h
    exact h'
  · set θ : ℝ := 11 / 20 + ε with hθ
    have hθpos : 0 < θ := by rw [hθ]; linarith
    set c : ℝ := 1 + Real.log 2 + θ with hc
    have hcpos : 0 < c := by rw [hc]; linarith
    refine ⟨Real.exp (max 1 (c ^ (2 ^ ⌈B⌉₊))), fun x hx => ?_⟩
    have hAs1 : (1 : ℝ) ≤ max 1 (c ^ (2 ^ ⌈B⌉₊)) := le_max_left _ _
    have hAsc : c ^ (2 ^ ⌈B⌉₊) ≤ max 1 (c ^ (2 ^ ⌈B⌉₊)) := le_max_right _ _
    have ht_ge : max 1 (c ^ (2 ^ ⌈B⌉₊)) ≤ Real.log x := by
      have h1 : Real.log (Real.exp (max 1 (c ^ (2 ^ ⌈B⌉₊)))) ≤ Real.log x :=
        Real.log_le_log (Real.exp_pos _) hx
      rwa [Real.log_exp] at h1
    have ht1 : (1 : ℝ) ≤ Real.log x := le_trans hAs1 ht_ge
    have ht0 : (0 : ℝ) ≤ Real.log x := le_trans zero_le_one ht1
    have hct : c ^ (2 ^ ⌈B⌉₊) ≤ Real.log x := le_trans hAsc ht_ge
    have hx1 : (1 : ℝ) ≤ x := by
      have h2 : (1 : ℝ) ≤ Real.exp (max 1 (c ^ (2 ^ ⌈B⌉₊))) :=
        Real.one_le_exp (by linarith)
      linarith
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    have hL1 : (1 : ℝ) ≤ length512 ε x := by
      rw [length512]
      exact Real.one_le_rpow hx1 (le_of_lt hθpos)
    have hL0 : (0 : ℝ) < length512 ε x := lt_of_lt_of_le zero_lt_one hL1
    have hN2 : 2 ≤ ⌊2 * length512 ε x⌋₊ := by
      apply Nat.le_floor
      simpa using mul_le_mul_of_nonneg_left hL1 (by norm_num : (0 : ℝ) ≤ 2)
    have hN1 : (1 : ℝ) ≤ (⌊2 * length512 ε x⌋₊ : ℝ) := by
      have h : (2 : ℝ) ≤ (⌊2 * length512 ε x⌋₊ : ℝ) := by exact_mod_cast hN2
      linarith
    have hNpos : (0 : ℝ) < (⌊2 * length512 ε x⌋₊ : ℝ) := by
      have : 0 < ⌊2 * length512 ε x⌋₊ := by omega
      exact_mod_cast this
    have hlogN0 : (0 : ℝ) ≤ Real.log (⌊2 * length512 ε x⌋₊ : ℝ) := Real.log_nonneg hN1
    have hNle : (⌊2 * length512 ε x⌋₊ : ℝ) ≤ 2 * length512 ε x :=
      Nat.floor_le (by positivity)
    have hsub : Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊
        ⊆ Finset.Ioc 0 ⌊2 * length512 ε x⌋₊ := by
      intro m hm
      rw [Finset.mem_Ioc] at hm ⊢
      exact ⟨by omega, hm.2⟩
    have hb := divisor_power_moment561 B ⌊2 * length512 ε x⌋₊
    have hlogle : Real.log (⌊2 * length512 ε x⌋₊ : ℝ) ≤ Real.log 2 + θ * Real.log x := by
      have hstep : Real.log (⌊2 * length512 ε x⌋₊ : ℝ) ≤ Real.log (2 * length512 ε x) :=
        Real.log_le_log hNpos hNle
      have hmul : Real.log (2 * length512 ε x) = Real.log 2 + Real.log (length512 ε x) :=
        Real.log_mul (by norm_num) (ne_of_gt hL0)
      have hL : Real.log (length512 ε x) = θ * Real.log x := by
        rw [length512, Real.log_rpow hx0, hθ]
      linarith
    have hbase_le : 1 + Real.log (⌊2 * length512 ε x⌋₊ : ℝ) ≤ c * Real.log x := by
      have hmul : (0 : ℝ) ≤ (1 + Real.log 2) * (Real.log x - 1) :=
        mul_nonneg (by linarith) (by linarith)
      rw [hc]
      nlinarith [hlogle, hmul]
    have hpowle : (1 + Real.log (⌊2 * length512 ε x⌋₊ : ℝ)) ^ (2 ^ ⌈B⌉₊) ≤
        (Real.log x) ^ (2 ^ ⌈B⌉₊ + 1) := by
      have h1 : (1 + Real.log (⌊2 * length512 ε x⌋₊ : ℝ)) ^ (2 ^ ⌈B⌉₊) ≤
          (c * Real.log x) ^ (2 ^ ⌈B⌉₊) :=
        pow_le_pow_left₀ (by linarith [hlogN0]) hbase_le _
      have h2 : (c * Real.log x) ^ (2 ^ ⌈B⌉₊) =
          c ^ (2 ^ ⌈B⌉₊) * (Real.log x) ^ (2 ^ ⌈B⌉₊) := mul_pow c _ _
      have h3 : c ^ (2 ^ ⌈B⌉₊) * (Real.log x) ^ (2 ^ ⌈B⌉₊) ≤
          (Real.log x) * (Real.log x) ^ (2 ^ ⌈B⌉₊) :=
        mul_le_mul_of_nonneg_right hct (by positivity)
      have h4 : (Real.log x) * (Real.log x) ^ (2 ^ ⌈B⌉₊) =
          (Real.log x) ^ (2 ^ ⌈B⌉₊ + 1) := by
        rw [pow_succ]; ring
      linarith [h1, h2.le, h2.ge, h3, h4.le, h4.ge]
    have hsum : ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
          ((m.divisors.card : ℕ) : ℝ) ^ B
        ≤ (⌊2 * length512 ε x⌋₊ : ℝ) *
            (1 + Real.log (⌊2 * length512 ε x⌋₊ : ℝ)) ^ (2 ^ ⌈B⌉₊) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => ?_)) ?_
      · exact Real.rpow_nonneg (by positivity) B
      · rw [Real.rpow_natCast] at hb
        exact hb
    have hstep1 : (⌊2 * length512 ε x⌋₊ : ℝ) *
          (1 + Real.log (⌊2 * length512 ε x⌋₊ : ℝ)) ^ (2 ^ ⌈B⌉₊)
        ≤ (2 * length512 ε x) * (Real.log x) ^ (2 ^ ⌈B⌉₊ + 1) := by
      refine mul_le_mul hNle hpowle (by positivity) (by positivity)
    have hfin : (2 * length512 ε x) * (Real.log x) ^ (2 ^ ⌈B⌉₊ + 1) =
        2 * length512 ε x * Real.log x ^ (((2 ^ ⌈B⌉₊ + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    linarith [hsum, hstep1, hfin.le, hfin.ge]

/-- LEAF. Mass of the short block. From the divisor type bound alone, the sum of the
coefficient norms over the short support is at most a constant times the block length
times a single fixed power of the logarithm of x. The exponent is not fixed in advance:
it is returned with the constant, because the divisor moment on a block of length
about Y costs a power of the logarithm that grows with the divisor exponent. -/
theorem leaf_long_short_mass561 (B C₀ : ℝ) :
    ∃ K M : ℝ, 1 ≤ K ∧ 1 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ b : ℕ → ℂ,
        (∀ k : ℕ, ‖b k‖ ≤ C₀ * ((k.divisors.card : ℕ) : ℝ) ^ B) →
        ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖ ≤
          K * length512 ε x * Real.log x ^ M :=
  long_short_mass_of_divisor_moment561 B C₀ (block_divisor_moment561 B)

/-- Gauss-sum character expansion, unit form: for a unit `b` mod `q`, the sum of the Gauss
sums of all characters mod `q` weighted by `χ b` is `φ(q)` times the standard additive
character at `b⁻¹`. This is the identity behind display (2.4) of the paper. -/
private theorem gauss_sum_char_expansion561 (q : ℕ) [NeZero q] (b : (ZMod q)ˣ) :
    ∑ χ : DirichletCharacter ℂ q, gaussSum χ ZMod.stdAddChar * χ ((b : ZMod q))
      = (q.totient : ℂ) * ZMod.stdAddChar (((b⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
  have hb1 : ((b : ZMod q)) * (((b⁻¹ : (ZMod q)ˣ) : ZMod q)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hstep : ∀ χ : DirichletCharacter ℂ q,
      gaussSum χ ZMod.stdAddChar * χ ((b : ZMod q))
        = ∑ a : ZMod q, (ZMod.stdAddChar a * χ (a * (b : ZMod q))) := by
    intro χ
    rw [gaussSum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_mul]
    ring
  calc ∑ χ : DirichletCharacter ℂ q, gaussSum χ ZMod.stdAddChar * χ ((b : ZMod q))
      = ∑ χ : DirichletCharacter ℂ q, ∑ a : ZMod q,
          (ZMod.stdAddChar a * χ (a * (b : ZMod q))) :=
        Finset.sum_congr rfl (fun χ _ => hstep χ)
    _ = ∑ a : ZMod q, ∑ χ : DirichletCharacter ℂ q,
          (ZMod.stdAddChar a * χ (a * (b : ZMod q))) := Finset.sum_comm
    _ = ∑ a : ZMod q, ZMod.stdAddChar a *
          ∑ χ : DirichletCharacter ℂ q, χ (a * (b : ZMod q)) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ a : ZMod q, ZMod.stdAddChar a *
          (if a * (b : ZMod q) = 1 then (q.totient : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [DirichletCharacter.sum_characters_eq]
    _ = (q.totient : ℂ) * ZMod.stdAddChar (((b⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
        rw [Finset.sum_eq_single (((b⁻¹ : (ZMod q)ˣ) : ZMod q))]
        · have h1 : (((b⁻¹ : (ZMod q)ˣ) : ZMod q)) * (b : ZMod q) = 1 := by
            rw [mul_comm]; exact hb1
          rw [if_pos h1]
          ring
        · intro a _ ha
          rw [if_neg, mul_zero]
          intro h
          exact ha (by
            calc a = a * ((b : ZMod q) * (((b⁻¹ : (ZMod q)ˣ) : ZMod q))) := by rw [hb1, mul_one]
              _ = (a * (b : ZMod q)) * (((b⁻¹ : (ZMod q)ˣ) : ZMod q)) := by ring
              _ = 1 * (((b⁻¹ : (ZMod q)ˣ) : ZMod q)) := by rw [h]
              _ = (((b⁻¹ : (ZMod q)ˣ) : ZMod q)) := one_mul _)
        · intro h
          exact absurd (Finset.mem_univ _) h

/-- Bridge from the `AddCircle` Fourier kernel to the standard additive character mod `q`:
`e(k r/q)` computed on the circle at the arc point `r/q` is `stdAddChar` at `k r`. -/
private theorem fourier_div_eq_stdAddChar561 (q : ℕ) [NeZero q] (k r : ℕ) :
    @fourier 1 (k : ℤ) (((r : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ))
      = ZMod.stdAddChar ((k * r : ℕ) : ZMod q) := by
  rw [fourier_coe_apply]
  rw [show ((k * r : ℕ) : ZMod q) = ((k * r : ℤ) : ZMod q) by push_cast; ring]
  rw [ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp

/-- The phase at the arc point splits: `e(k (r/q + η)) = e(k r/q) · e(k η)`. -/
private theorem fourier_coe_arc_split561 (k : ℤ) (r q : ℕ) (eta : ℝ) :
    @fourier 1 k ((((r : ℝ) / (q : ℝ)) + eta : ℝ) : AddCircle (1 : ℝ))
      = Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * ((r : ℝ) / (q : ℝ))) *
        Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * eta) := by
  rw [fourier_coe_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Display (2.4) at one coefficient. For `k * r` coprime to `q` the phase at the arc point
`r/q + η` expands in the characters of modulus `q`: the coefficients are the Gauss sums, the
argument of the character is the inverse of the unit of `k * r`, and the local phase `e(k η)`
factors out. This is the identity that turns the character prefix hypothesis on `a` into a
statement about a single arc integral. -/
private theorem fourier_arc_gauss561 (q : ℕ) [NeZero q] (k r : ℕ) (eta : ℝ)
    (hcop : Nat.Coprime (k * r) q) :
    @fourier 1 (k : ℤ) ((((r : ℝ) / (q : ℝ)) + eta : ℝ) : AddCircle (1 : ℝ))
      = (1 / (q.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q,
          gaussSum χ ZMod.stdAddChar *
            χ (Units.val ((ZMod.unitOfCoprime (k * r) hcop : (ZMod q)ˣ)⁻¹)) *
            Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * eta) := by
  have hphi : (q.totient : ℂ) ≠ 0 := by
    have h : 0 < q.totient := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast h.ne'
  have hkey : ZMod.stdAddChar ((k * r : ℕ) : ZMod q)
      = (1 / (q.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q,
          gaussSum χ ZMod.stdAddChar *
            χ (Units.val ((ZMod.unitOfCoprime (k * r) hcop : (ZMod q)ˣ)⁻¹)) := by
    have hg := gauss_sum_char_expansion561 q (ZMod.unitOfCoprime (k * r) hcop)⁻¹
    have hinv : (((ZMod.unitOfCoprime (k * r) hcop : (ZMod q)ˣ))⁻¹)⁻¹ =
        (ZMod.unitOfCoprime (k * r) hcop) := inv_inv _
    rw [hinv, ZMod.coe_unitOfCoprime] at hg
    rw [hg]
    field_simp
  have hphase : Complex.exp (2 * Real.pi * Complex.I * ((k : ℤ) : ℂ) * ((r : ℝ) / (q : ℝ)))
      = ZMod.stdAddChar ((k * r : ℕ) : ZMod q) := by
    rw [← fourier_div_eq_stdAddChar561 q k r, fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [fourier_coe_arc_split561, hphase, hkey]
  conv_rhs => rw [← Finset.sum_mul, ← mul_assoc]
  rfl

/-- A prefix bound at every real cutoff gives a bound at every single coefficient: the prefix
sums at the cutoffs `k` and `k - 1` differ by the term of index `k` alone. This is how the
character prefix hypothesis on `a` becomes a pointwise statement about each `a k`. -/
private theorem prefix_pointwise_bound561 (s : Finset ℕ) (f : ℕ → ℂ) (R X : ℝ) (k : ℕ)
    (hk : k ∈ s) (hsX : ∀ m ∈ s, (m : ℝ) ≤ X)
    (h : ∀ t : ℝ, t ≤ X → ‖∑ m ∈ s.filter (fun m : ℕ => (m : ℝ) ≤ t), f m‖ ≤ R) :
    ‖f k‖ ≤ 2 * R := by
  have hset : s.filter (fun m : ℕ => (m : ℝ) ≤ (k : ℝ)) =
      insert k (s.filter (fun m : ℕ => (m : ℝ) ≤ (k : ℝ) - 1)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hms, hmle⟩
      by_cases hm : (m : ℝ) ≤ (k : ℝ) - 1
      · exact Or.inr ⟨hms, hm⟩
      · left
        push_neg at hm
        have h2 : k < m + 1 := by
          have h1 : (k : ℝ) < (m : ℝ) + 1 := by linarith
          exact_mod_cast h1
        have h3 : m ≤ k := by exact_mod_cast hmle
        omega
    · rintro (rfl | ⟨hms, hmle⟩)
      · exact ⟨hk, le_refl _⟩
      · exact ⟨hms, by linarith⟩
  have hknot : k ∉ s.filter (fun m : ℕ => (m : ℝ) ≤ (k : ℝ) - 1) := by
    simp only [Finset.mem_filter, not_and]
    intro _
    linarith
  have hsum1 := h ((k : ℝ) - 1) (by have := hsX k hk; linarith)
  have hsum2 := h (k : ℝ) (hsX k hk)
  have hdecomp : f k = (∑ m ∈ s.filter (fun m : ℕ => (m : ℝ) ≤ (k : ℝ)), f m) -
      (∑ m ∈ s.filter (fun m : ℕ => (m : ℝ) ≤ (k : ℝ) - 1), f m) := by
    rw [hset, Finset.sum_insert hknot]
    ring
  rw [hdecomp]
  calc ‖(∑ m ∈ s.filter (fun m : ℕ => (m : ℝ) ≤ (k : ℝ)), f m) -
        (∑ m ∈ s.filter (fun m : ℕ => (m : ℝ) ≤ (k : ℝ) - 1), f m)‖
      ≤ ‖∑ m ∈ s.filter (fun m : ℕ => (m : ℝ) ≤ (k : ℝ)), f m‖ +
        ‖∑ m ∈ s.filter (fun m : ℕ => (m : ℝ) ≤ (k : ℝ) - 1), f m‖ := norm_sub_le _ _
    _ ≤ R + R := add_le_add hsum2 hsum1
    _ = 2 * R := by ring

/-- The character prefix hypothesis read at a single coefficient: for every modulus below the
logarithmic cutoff and every character, the twisted coefficient of `a` is within twice the same
logarithmic saving times the block length of its principal part. -/
private theorem char_prefix_pointwise561 (ε : ℝ) (a : ℝ → ℕ → ℂ) (u : ℝ)
    (hdist : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
        ‖∑ k ∈ (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).filter
            (fun k : ℕ => (k : ℝ) ≤ t),
          (a x k * χ (k : ZMod q) - delta χ * u / Real.log x)‖ ≤
        C * length512 ε x * Real.log x ^ (-A)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, ∀ k : ℕ,
        k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊ →
        ‖a x k * χ (k : ZMod q) - delta χ * u / Real.log x‖ ≤
          2 * C * length512 ε x * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C, hC⟩ := hdist A hA
  refine ⟨C, fun x hx q hq hqL χ k hk => ?_⟩
  have hle : k ≤ ⌊x⌋₊ := (Finset.mem_Ioc.mp hk).2
  have hk1 : 1 ≤ k := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  have hpos : 0 < ⌊x⌋₊ := by omega
  have hx0 : (0 : ℝ) ≤ x := by
    have h1 : (1 : ℝ) ≤ x := Nat.floor_pos.mp hpos
    linarith
  have hsX : ∀ m ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊, (m : ℝ) ≤ x := by
    intro m hm
    have h2 : m ≤ ⌊x⌋₊ := (Finset.mem_Ioc.mp hm).2
    have h3 : (m : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h2
    have h4 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    linarith
  have hb := prefix_pointwise_bound561 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊)
    (fun m => a x m * χ (m : ZMod q) - delta χ * u / Real.log x)
    (C * length512 ε x * Real.log x ^ (-A)) x k hk hsX
    (fun t ht => hC x hx q hq hqL χ t ht)
  calc ‖a x k * χ (k : ZMod q) - delta χ * u / Real.log x‖
      ≤ 2 * (C * length512 ε x * Real.log x ^ (-A)) := hb
    _ = 2 * C * length512 ε x * Real.log x ^ (-A) := by ring

/-- Norm bound for the local short block integral on one arc: the short polynomial times the
frequency phase contributes at most the arc length times the mass of the short block, uniformly
in the frequency and in the arc centre. -/
private theorem short_arc_integral_norm_le561 (w : ℝ) (J : Finset ℕ) (c : ℕ → ℂ) (N : ℕ) :
    ‖∫ s in (-w)..w,
        (∑ m ∈ J, c m * @fourier 1 (m : ℤ) (s : AddCircle (1 : ℝ))) *
          @fourier 1 (-(N : ℤ)) (s : AddCircle (1 : ℝ))‖ ≤
      2 * |w| * ∑ m ∈ J, ‖c m‖ := by
  have hsum : ∀ s : ℝ, ‖(∑ m ∈ J, c m * @fourier 1 (m : ℤ) (s : AddCircle (1 : ℝ)))‖ ≤
      ∑ m ∈ J, ‖c m‖ := by
    intro s
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum (fun m _ => ?_)
    have hstep : ‖c m * @fourier 1 (m : ℤ) (s : AddCircle (1 : ℝ))‖ = ‖c m‖ * 1 := by
      rw [norm_mul, fourier_apply, Circle.norm_coe]
    rw [hstep, mul_one]
  have hb : ∀ s : ℝ, ‖(∑ m ∈ J, c m * @fourier 1 (m : ℤ) (s : AddCircle (1 : ℝ))) *
      @fourier 1 (-(N : ℤ)) (s : AddCircle (1 : ℝ))‖ ≤ ∑ m ∈ J, ‖c m‖ := by
    intro s
    have hstep : ‖(∑ m ∈ J, c m * @fourier 1 (m : ℤ) (s : AddCircle (1 : ℝ)))‖ *
        ‖@fourier 1 (-(N : ℤ)) (s : AddCircle (1 : ℝ))‖ =
        ‖(∑ m ∈ J, c m * @fourier 1 (m : ℤ) (s : AddCircle (1 : ℝ)))‖ := by
      rw [fourier_apply, Circle.norm_coe, mul_one]
    calc ‖(∑ m ∈ J, c m * @fourier 1 (m : ℤ) (s : AddCircle (1 : ℝ))) *
          @fourier 1 (-(N : ℤ)) (s : AddCircle (1 : ℝ))‖
        ≤ ‖(∑ m ∈ J, c m * @fourier 1 (m : ℤ) (s : AddCircle (1 : ℝ)))‖ *
            ‖@fourier 1 (-(N : ℤ)) (s : AddCircle (1 : ℝ))‖ := norm_mul_le _ _
      _ = ‖(∑ m ∈ J, c m * @fourier 1 (m : ℤ) (s : AddCircle (1 : ℝ)))‖ := hstep
      _ ≤ ∑ m ∈ J, ‖c m‖ := hsum s
  calc ‖∫ s in (-w)..w,
        (∑ m ∈ J, c m * @fourier 1 (m : ℤ) (s : AddCircle (1 : ℝ))) *
          @fourier 1 (-(N : ℤ)) (s : AddCircle (1 : ℝ))‖
      ≤ (∑ m ∈ J, ‖c m‖) * |w - (-w)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => hb x)
    _ = 2 * |w| * ∑ m ∈ J, ‖c m‖ := by
        rw [show w - (-w) = 2 * w by ring, abs_mul, abs_two]
        ring

/-- The rough support hypothesis makes every long coefficient coprime to every modulus below
the logarithmic cutoff: each prime factor of such a modulus is below the primorial argument, so
it is excluded by the gcd condition. -/
private theorem rough_coprime561 (a : ℝ → ℕ → ℂ)
    (hrough : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
      Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0) :
    ∀ A : ℝ, 0 < A → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ k q : ℕ, 1 ≤ q →
      q ≤ ⌊Real.log x ^ A⌋₊ → a x k ≠ 0 → Nat.Coprime k q := by
  intro A hA
  obtain ⟨C, hC⟩ := hrough (A + 2) (by linarith)
  refine ⟨max C (Real.exp 2), fun x hx k q hq hqL hak => ?_⟩
  have hxC : C ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 2 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) < Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 2) hxe
    rw [Real.log_exp] at h
    linarith
  have hz1 : (1 : ℝ) < Real.log x ^ (A + 2) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (A + 2) := (Real.one_rpow _).symm
      _ < Real.log x ^ (A + 2) := Real.rpow_lt_rpow (by norm_num) hx1 (by linarith)
  have hgcd : Nat.gcd k (primorialBelow (Real.log x ^ (A + 2))) = 1 := by
    by_contra h
    exact hak (hC x hxC k h)
  refine Nat.coprime_iff_gcd_eq_one.mpr ?_
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpk : p ∣ k := hpd.trans (Nat.gcd_dvd_left k q)
  have hpq : p ∣ q := hpd.trans (Nat.gcd_dvd_right k q)
  have hpz : (p : ℝ) < Real.log x ^ (A + 2) := by
    have h1 : p ≤ q := Nat.le_of_dvd (by omega) hpq
    have h2 : q ≤ ⌊Real.log x ^ A⌋₊ := hqL
    have hlog0 : (0 : ℝ) < Real.log x := by linarith
    have h3 : (⌊Real.log x ^ A⌋₊ : ℝ) ≤ Real.log x ^ A :=
      Nat.floor_le (le_of_lt (Real.rpow_pos_of_pos hlog0 A))
    have h4 : (p : ℝ) ≤ Real.log x ^ A := by
      have h5 : (p : ℝ) ≤ (⌊Real.log x ^ A⌋₊ : ℝ) := by exact_mod_cast le_trans h1 h2
      linarith
    have h5 : Real.log x ^ A < Real.log x ^ (A + 2) :=
      Real.rpow_lt_rpow_of_exponent_lt hx1 (by linarith)
    exact lt_of_le_of_lt h4 h5
  have hpmem : p ∈ (Finset.range ⌈Real.log x ^ (A + 2)⌉₊).filter
      (fun p : ℕ => p.Prime ∧ (p : ℝ) < Real.log x ^ (A + 2)) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by exact_mod_cast lt_of_lt_of_le hpz (Nat.le_ceil _), hp, hpz⟩
  have hpdvd : p ∣ primorialBelow (Real.log x ^ (A + 2)) := by
    rw [primorialBelow]
    exact Finset.dvd_prod_of_mem _ hpmem
  have hpg : p ∣ Nat.gcd k (primorialBelow (Real.log x ^ (A + 2))) := Nat.dvd_gcd hpk hpdvd
  rw [hgcd] at hpg
  have h1 : p = 1 := Nat.dvd_one.mp hpg
  exact absurd h1 (Nat.Prime.ne_one hp)

/-- The rough support read as coprimality turns a pointwise character bound into a pointwise
comparison of a long coefficient with the principal coefficient `u / log x`: take the principal
character of a modulus below the cutoff, on which every surviving coefficient is a unit. -/
private theorem principal_pointwise561 (ε : ℝ) (a : ℝ → ℕ → ℂ) (u : ℝ) (A K : ℝ) (hA : 0 < A)
    (hpoint : ∃ Xc : ℝ, ∀ x : ℝ, Xc ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ k : ℕ,
        k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊ → a x k ≠ 0 →
        ‖a x k * χ (k : ZMod q) - delta χ * u / Real.log x‖ ≤
          K * length512 ε x * Real.log x ^ (-A))
    (hrough : ∀ B : ℝ, 0 < B → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
      Nat.gcd k (primorialBelow (Real.log x ^ B)) ≠ 1 → a x k = 0) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ k : ℕ,
      k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊ → a x k ≠ 0 →
      ‖a x k - u / Real.log x‖ ≤ K * length512 ε x * Real.log x ^ (-A) := by
  obtain ⟨Xc, hXc⟩ := hpoint
  obtain ⟨Xr, hXr⟩ := rough_coprime561 a hrough A hA
  refine ⟨max Xc Xr, fun x hx q hq hqL k hk hak => ?_⟩
  have hcop : Nat.Coprime k q :=
    hXr x (le_trans (le_max_right _ _) hx) k q (by omega) (Nat.le_floor hqL) hak
  have hunit : IsUnit ((k : ZMod q)) := (ZMod.isUnit_iff_coprime k q).mpr hcop
  have h1 : ((1 : DirichletCharacter ℂ q) (k : ZMod q)) = 1 := MulChar.one_apply hunit
  have hd : delta (1 : DirichletCharacter ℂ q) = 1 := by simp [delta]
  have hpt := hXc x (le_trans (le_max_left _ _) hx) q (by omega) hqL
    (1 : DirichletCharacter ℂ q) k hk hak
  rw [h1, hd] at hpt
  simpa using hpt

/-- The arc half width is eventually below any prescribed multiple of `1/q`: the major arc of
modulus `q` has half width `log x ^ (4D) / (q * Y)`, and `Y = x ^ (11/20+ε)` beats every fixed
power of the logarithm. This is the elementary `Y ≫ ℒ ^ (4D)` estimate. -/
private theorem arc_width_small561 (ε D : ℝ) (hε : 0 < ε) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 1 ≤ q →
      Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x) ≤ η / (q : ℝ) := by
  intro η hη
  have hθ : (0 : ℝ) < 11 / 20 + ε := by linarith
  have hlittle := isLittleO_log_rpow_rpow_atTop (4 * D) hθ
  have hbound : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ (4 * D) ≤ η * x ^ (11 / 20 + ε) := by
    filter_upwards [hlittle.bound hη, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)] at hx
    exact hx
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hbound
  refine ⟨max X 1, fun x hx q hq => ?_⟩
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hmain : Real.log x ^ (4 * D) ≤ η * length512 ε x := by
    have h := hX x hxX
    rwa [length512]
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hLpos : (0 : ℝ) < length512 ε x := by
    rw [length512]
    exact Real.rpow_pos_of_pos hx0 _
  have e1 : Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x) =
      (Real.log x ^ (4 * D) / length512 ε x) / (q : ℝ) := by field_simp
  rw [e1, div_le_div_iff_of_pos_right hqpos, div_le_iff₀ hLpos]
  exact hmain

/-- A fixed power of the logarithm is eventually below any fixed positive power of `x`. -/
private lemma eventually_log_pow_le_rpow561 {k C c : ℝ} (hk : 0 ≤ k) (hC : 0 < C) (hc : 0 < c) :
    ∀ᶠ x : ℝ in Filter.atTop, C * Real.log x ^ k ≤ x ^ c := by
  set r : ℝ := c / (2 * (k + 1)) with hr
  have hk1 : 0 < k + 1 := by linarith
  have hrpos : 0 < r := by rw [hr]; positivity
  have hrk : r * k < c := by
    rw [hr, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_ge_atTop 1
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, C / r ^ k ≤ x ^ (c - r * k) :=
    (tendsto_rpow_atTop (by linarith : 0 < c - r * k)).eventually_ge_atTop (C / r ^ k)
  filter_upwards [h1, h2] with x hx1 hx2
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : Real.log x ≤ x ^ r / r := Real.log_le_rpow_div hx0.le hrpos
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hdiv : (0 : ℝ) ≤ x ^ r / r := by positivity
  have hpow : Real.log x ^ k ≤ (x ^ r / r) ^ k := Real.rpow_le_rpow hlog0 hlog hk
  have hstep : (x ^ r / r) ^ k = x ^ (r * k) * r ^ (-k) := by
    have hxr : (0 : ℝ) ≤ x ^ r := Real.rpow_nonneg hx0.le r
    rw [Real.div_rpow hxr hrpos.le, Real.rpow_mul hx0.le, Real.rpow_neg hrpos.le]
    field_simp
  have hmul : x ^ (c - r * k) * x ^ (r * k) = x ^ c := by
    rw [← Real.rpow_add hx0]
    ring_nf
  calc C * Real.log x ^ k ≤ C * ((x ^ r / r) ^ k) := by
        exact mul_le_mul_of_nonneg_left hpow hC.le
    _ = C * (x ^ (r * k) * r ^ (-k)) := by rw [hstep]
    _ = (C / r ^ k) * x ^ (r * k) := by
        rw [Real.rpow_neg hrpos.le]
        field_simp
    _ ≤ x ^ (c - r * k) * x ^ (r * k) := by
        refine mul_le_mul_of_nonneg_right hx2 (Real.rpow_nonneg hx0.le _)
    _ = x ^ c := hmul

/-- The explicit thresholds needed for the arc decomposition: `x` is large enough that
a fixed power of `log x` is dominated by any fixed positive power of `x`, uniformly in
the two free parameters. -/
private lemma exists_threshold561 (ε D : ℝ) (hc : 0 < 11 / 20 + ε) (hD : 0 ≤ D) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      (1 : ℝ) ≤ Real.log x ∧
      (4 : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) ∧
      8 * Real.log x ^ (2 * D) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) ∧
      Real.log x ^ (4 * D) ≤ length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)) ∧
      4 * Real.log x ^ (8 * D) ≤ length512 ε x := by
  have he : (0 : ℝ) < 1 / 16 - 1 / 10 ^ 5 := by norm_num
  have h1e : (0 : ℝ) < 1 - (1 / 16 - 1 / 10 ^ 5) := by norm_num
  have h2D : (0 : ℝ) ≤ 2 * D := by linarith
  have h4D : (0 : ℝ) ≤ 4 * D := by linarith
  have h8D : (0 : ℝ) ≤ 8 * D := by linarith
  have hce : (0 : ℝ) < (11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5) := mul_pos hc he
  have hc1 : (0 : ℝ) < (11 / 20 + ε) * (1 - (1 / 16 - 1 / 10 ^ 5)) := mul_pos hc h1e
  have ev2 : ∀ᶠ x : ℝ in Filter.atTop,
      (4 : ℝ) ≤ x ^ ((11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5)) :=
    (tendsto_rpow_atTop hce).eventually_ge_atTop 4
  have ev3 : ∀ᶠ x : ℝ in Filter.atTop,
      8 * Real.log x ^ (2 * D) ≤ x ^ ((11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5)) :=
    eventually_log_pow_le_rpow561 h2D (by norm_num) hce
  have ev4 : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ (4 * D) ≤ x ^ ((11 / 20 + ε) * (1 - (1 / 16 - 1 / 10 ^ 5))) := by
    filter_upwards [eventually_log_pow_le_rpow561 (C := 1) h4D (by norm_num) hc1] with x hx
    simpa using hx
  have ev6 : ∀ᶠ x : ℝ in Filter.atTop,
      4 * Real.log x ^ (8 * D) ≤ x ^ (11 / 20 + ε) :=
    eventually_log_pow_le_rpow561 h8D (by norm_num) hc
  have all : ∀ᶠ x : ℝ in Filter.atTop,
      (1 : ℝ) ≤ Real.log x ∧
      (4 : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) ∧
      8 * Real.log x ^ (2 * D) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) ∧
      Real.log x ^ (4 * D) ≤ length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)) ∧
      4 * Real.log x ^ (8 * D) ≤ length512 ε x := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 2), ev2, ev3, ev4, ev6]
      with x hxe h2 h3 h4 h6
    have hxe0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 2) hxe
    have hlen : ∀ e : ℝ, length512 ε x ^ e = x ^ ((11 / 20 + ε) * e) := by
      intro e
      unfold length512
      exact (Real.rpow_mul hxe0.le (11 / 20 + ε) e).symm
    have hL : length512 ε x = x ^ (11 / 20 + ε) := by
      unfold length512; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have h := Real.log_le_log (Real.exp_pos 2) hxe
      rw [Real.log_exp] at h
      linarith
    · have heq : x ^ ((11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5)) =
          length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) :=
        (hlen (1 / 16 - 1 / 10 ^ 5 : ℝ)).symm
      rw [heq] at h2
      exact h2
    · have heq : x ^ ((11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5)) =
          length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) :=
        (hlen (1 / 16 - 1 / 10 ^ 5 : ℝ)).symm
      rw [heq] at h3
      exact h3
    · have heq : x ^ ((11 / 20 + ε) * (1 - (1 / 16 - 1 / 10 ^ 5))) =
          length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)) :=
        (hlen (1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)).symm
      rw [heq] at h4
      exact h4
    · rw [hL]
      exact h6
  rw [Filter.eventually_atTop] at all
  obtain ⟨X, hX⟩ := all
  exact ⟨X, hX⟩

/-- The Farey order of the major arcs is close to the `(1/16 - 1e-5)` power of the block
length. -/
private lemma order_bounds561 {ε x : ℝ} (hlen0 : 0 ≤ length512 ε x)
    (h4 : (4 : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ))) :
    length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 4 ≤ (order512 ε x : ℝ) ∧
    (order512 ε x : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 2 := by
  have hkey : (length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ ((1 / 2 : ℝ)) =
      length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) := by
    rw [← Real.rpow_mul hlen0]
    norm_num
  have hfl : (order512 ε x : ℝ) =
      ⌊length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 2⌋₊ := by
    unfold order512
    rw [hkey]
  constructor
  · rw [hfl]
    have h1 : length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 2 - 1 <
        (⌊length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 2⌋₊ : ℝ) := by
      have h := Nat.lt_floor_add_one (length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 2)
      linarith
    nlinarith
  · rw [hfl]
    exact Nat.floor_le (by positivity)

/-- The modulus cutoff and its basic bound. -/
private lemma Q_facts561 {D x : ℝ} (hlog1 : 1 ≤ Real.log x) (hD : 0 ≤ D) :
    1 ≤ ⌊Real.log x ^ (2 * D)⌋₊ ∧
      ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ Real.log x ^ (2 * D) := by
  refine ⟨Nat.floor_pos.mpr (Real.one_le_rpow hlog1 (by linarith)),
    Nat.floor_le (Real.rpow_nonneg (by linarith) _)⟩

/-- Every reduced Farey arc of the major arcs lies inside the complete period; this is
where the block length dominates the arc width and the Farey order. -/
private lemma arc_containment561 {ε D x w : ℝ} (hx1 : 1 < x) (hlog1 : 1 ≤ Real.log x)
    (hD : 0 ≤ D)
    (h4 : (4 : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hQord : 8 * Real.log x ^ (2 * D) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hordhi : Real.log x ^ (4 * D) ≤ length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)))
    (hlenbig : 4 * Real.log x ^ (8 * D) ≤ length512 ε x)
    {Q q : ℕ} (hQ1 : 1 ≤ Q) (hQle : (Q : ℝ) ≤ Real.log x ^ (2 * D))
    (hq1 : 1 ≤ q) (hqQ : q ≤ Q)
    (hw : w = Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
    {r : ℕ} (hr1 : 1 ≤ r) (hrq : r ≤ q) :
    Set.Icc ((r : ℝ) / (q : ℝ) - w) ((r : ℝ) / (q : ℝ) + w) ⊆
      Set.Ioc (1 / (order512 ε x : ℝ)) (1 + 1 / (order512 ε x : ℝ)) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hlenpos : (0 : ℝ) < length512 ε x := by
    unfold length512
    exact Real.rpow_pos_of_pos hx0 _
  have hlen0 : (0 : ℝ) ≤ length512 ε x := le_of_lt hlenpos
  have hLpos : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have he : (0 : ℝ) < 1 / 16 - 1 / 10 ^ 5 := by norm_num
  obtain ⟨hordlo, hordub⟩ := order_bounds561 hlen0 h4
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have h : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    linarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    have h : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
    linarith
  have hQle' : (Q : ℝ) ≤ Real.log x ^ (2 * D) := hQle
  have hqleQ : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
  have hLepos : (0 : ℝ) < length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) :=
    Real.rpow_pos_of_pos hlenpos _
  have hordpos : (0 : ℝ) < (order512 ε x : ℝ) := by linarith
  have h2Q : 2 * (Q : ℝ) ≤ (order512 ε x : ℝ) := by
    have h3 : 2 * Real.log x ^ (2 * D) ≤
        length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 4 := by linarith
    have h4' : 2 * (Q : ℝ) ≤ 2 * Real.log x ^ (2 * D) := by linarith
    linarith
  have hinv1 : 1 / (order512 ε x : ℝ) ≤ 1 / (2 * (Q : ℝ)) :=
    one_div_le_one_div_of_le (by linarith : (0 : ℝ) < 2 * (Q : ℝ)) h2Q
  have hL4D : (0 : ℝ) < Real.log x ^ (4 * D) := Real.rpow_pos_of_pos hLpos _
  have h6 : 4 * (Q : ℝ) * Real.log x ^ (4 * D) ≤ length512 ε x := by
    have hL68 : Real.log x ^ (6 * D) ≤ Real.log x ^ (8 * D) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
    have hmul : Real.log x ^ (2 * D) * Real.log x ^ (4 * D) = Real.log x ^ (6 * D) := by
      rw [← Real.rpow_add hLpos]; ring_nf
    have h2 : (Q : ℝ) * Real.log x ^ (4 * D) ≤
        Real.log x ^ (2 * D) * Real.log x ^ (4 * D) :=
      mul_le_mul_of_nonneg_right hQle' (le_of_lt hL4D)
    have h3 : (Q : ℝ) * Real.log x ^ (4 * D) ≤ Real.log x ^ (8 * D) := by
      rw [hmul] at h2; exact le_trans h2 hL68
    linarith
  have hwq : w ≤ 1 / (4 * (Q : ℝ)) := by
    rw [hw, div_le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * length512 ε x)
      (by positivity : (0 : ℝ) < 4 * (Q : ℝ))]
    have hqlen : length512 ε x ≤ (q : ℝ) * length512 ε x := by
      have h1 : (1 : ℝ) * length512 ε x ≤ (q : ℝ) * length512 ε x :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hq1 : (1 : ℝ) ≤ (q : ℝ)) (le_of_lt hlenpos)
      simpa using h1
    nlinarith [h6, hqlen]
  have hqinv : 1 / (Q : ℝ) ≤ 1 / (q : ℝ) :=
    one_div_le_one_div_of_le hqpos hqleQ
  have hfrac1 : 1 / (q : ℝ) ≤ (r : ℝ) / (q : ℝ) := by
    have h : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    exact div_le_div_of_nonneg_right h (le_of_lt hqpos)
  have hlow : 1 / (order512 ε x : ℝ) < (r : ℝ) / (q : ℝ) - w := by
    have hA : 1 / (2 * (Q : ℝ)) < 1 / (Q : ℝ) - 1 / (4 * (Q : ℝ)) := by
      have hQ0 : (0 : ℝ) < (Q : ℝ) := hQpos
      field_simp
      linarith
    have hC : 1 / (q : ℝ) - 1 / (4 * (Q : ℝ)) ≤ (r : ℝ) / (q : ℝ) - w := by linarith
    linarith
  have hfrac2 : (r : ℝ) / (q : ℝ) ≤ 1 := by
    rw [div_le_one hqpos]
    exact_mod_cast hrq
  have hwsmall : w ≤ 1 / (order512 ε x : ℝ) := by
    rw [hw, div_le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * length512 ε x) hordpos]
    have hsplit : length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) *
        length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)) = length512 ε x := by
      rw [← Real.rpow_add hlenpos]
      norm_num
    have h1 : (order512 ε x : ℝ) * Real.log x ^ (4 * D) ≤ length512 ε x := by
      calc (order512 ε x : ℝ) * Real.log x ^ (4 * D)
          ≤ (length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 2) * Real.log x ^ (4 * D) :=
            mul_le_mul_of_nonneg_right hordub (le_of_lt hL4D)
        _ = (length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) * Real.log x ^ (4 * D)) / 2 := by
            ring
        _ ≤ (length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) *
              length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ))) / 2 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_left hordhi (le_of_lt hLepos)
        _ = length512 ε x / 2 := by rw [hsplit]
        _ ≤ length512 ε x := by linarith
    have h2 : Real.log x ^ (4 * D) * (order512 ε x : ℝ) ≤ length512 ε x := by
      rw [mul_comm]; exact h1
    have hqlen : length512 ε x ≤ (q : ℝ) * length512 ε x := by
      have h1 : (1 : ℝ) * length512 ε x ≤ (q : ℝ) * length512 ε x :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hq1 : (1 : ℝ) ≤ (q : ℝ)) (le_of_lt hlenpos)
      simpa using h1
    nlinarith [h1, hqlen]
  intro t ht
  exact ⟨by linarith [ht.1, hlow], by linarith [ht.2, hfrac2, hwsmall]⟩

/-- Distinct reduced fractions are separated by the reciprocal of the product of their
moduli. -/
private lemma frac_separation561 {q q' r r' : ℕ} (hq1 : 1 ≤ q) (hq'1 : 1 ≤ q')
    (hcq : Nat.Coprime r q) (hcq' : Nat.Coprime r' q')
    (hne : (q, r) ≠ (q', r')) :
    1 / ((q : ℝ) * q') ≤ |(r : ℝ) / (q : ℝ) - (r' : ℝ) / (q' : ℝ)| := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have h : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    linarith
  have hq'pos : (0 : ℝ) < (q' : ℝ) := by
    have h : (1 : ℝ) ≤ (q' : ℝ) := by exact_mod_cast hq'1
    linarith
  have hq0 : q ≠ 0 := by omega
  set m : ℤ := (r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) with hm
  have hcast : ((m : ℤ) : ℝ) = (r : ℝ) * (q' : ℝ) - (r' : ℝ) * (q : ℝ) := by
    simp only [hm, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  have hne_int : m ≠ 0 := by
    intro h0
    have h3 : (r : ℤ) * (q' : ℤ) = (r' : ℤ) * (q : ℤ) := by
      have := sub_eq_zero.mp h0
      exact this
    have h1' : r * q' = r' * q := by
      have h4 : ((r * q' : ℕ) : ℤ) = ((r' * q : ℕ) : ℤ) := by
        push_cast
        exact h3
      exact_mod_cast h4
    have hd1 : q ∣ q' := by
      have h : r * q' = q * r' := by rw [h1', mul_comm]
      exact hcq.symm.dvd_of_dvd_mul_left ⟨r', h⟩
    have hd2 : q' ∣ q := by
      have h : r' * q = q' * r := by rw [← h1', mul_comm]
      exact hcq'.symm.dvd_of_dvd_mul_left ⟨r, h⟩
    have hqq : q = q' := Nat.dvd_antisymm hd1 hd2
    have hr : r = r' := by
      have h2 : r * q = r' * q := by rw [← hqq] at h1'; exact h1'
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) h2
    exact hne (by rw [hqq, hr])
  have hA : (1 : ℝ) ≤ |(r : ℝ) * (q' : ℝ) - (r' : ℝ) * (q : ℝ)| := by
    have h1 : (1 : ℝ) ≤ ((|m| : ℤ) : ℝ) := by
      have h2 := Int.one_le_abs hne_int
      exact_mod_cast h2
    have h2 : ((|m| : ℤ) : ℝ) = |((m : ℤ) : ℝ)| := by simp
    rw [h2] at h1
    rwa [hcast] at h1
  have hfrac : (r : ℝ) / (q : ℝ) - (r' : ℝ) / (q' : ℝ) =
      ((r : ℝ) * (q' : ℝ) - (r' : ℝ) * (q : ℝ)) / ((q : ℝ) * (q' : ℝ)) := by
    field_simp
  have h1 : (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) ≤
      |(r : ℝ) * (q' : ℝ) - (r' : ℝ) * (q : ℝ)| / ((q : ℝ) * (q' : ℝ)) :=
    div_le_div_of_nonneg_right hA (by positivity)
  have h2 : |(r : ℝ) * (q' : ℝ) - (r' : ℝ) * (q : ℝ)| / ((q : ℝ) * (q' : ℝ)) =
      |(r : ℝ) / (q : ℝ) - (r' : ℝ) / (q' : ℝ)| := by
    rw [hfrac, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) * (q' : ℝ))]
  exact le_trans h1 (le_of_eq h2)

/-- Two closed arcs around distinct fractions are disjoint as soon as their widths add up
to less than the separation of the fractions. -/
private lemma arcs_disjoint561 {L4D len : ℝ} (hL4D : 0 ≤ L4D) (hlenpos : 0 < len)
    {q q' : ℕ} (hqpos : (0 : ℝ) < (q : ℝ)) (hq'pos : (0 : ℝ) < (q' : ℝ))
    {r r' : ℕ}
    (hsep : 1 / ((q : ℝ) * q') ≤ |(r : ℝ) / (q : ℝ) - (r' : ℝ) / (q' : ℝ)|)
    (hwidth : L4D / ((q : ℝ) * len) + L4D / ((q' : ℝ) * len) < 1 / ((q : ℝ) * q')) :
    Disjoint
      (Set.Icc ((r : ℝ) / (q : ℝ) - L4D / ((q : ℝ) * len))
        ((r : ℝ) / (q : ℝ) + L4D / ((q : ℝ) * len)))
      (Set.Icc ((r' : ℝ) / (q' : ℝ) - L4D / ((q' : ℝ) * len))
        ((r' : ℝ) / (q' : ℝ) + L4D / ((q' : ℝ) * len))) := by
  rw [Set.disjoint_left]
  intro t ht ht'
  have hA : (r' : ℝ) / (q' : ℝ) - (r : ℝ) / (q : ℝ) ≤
      L4D / ((q : ℝ) * len) + L4D / ((q' : ℝ) * len) := by
    linarith [ht.2, ht'.1]
  have hB : (r : ℝ) / (q : ℝ) - (r' : ℝ) / (q' : ℝ) ≤
      L4D / ((q : ℝ) * len) + L4D / ((q' : ℝ) * len) := by
    linarith [ht.1, ht'.2]
  have habs : |(r : ℝ) / (q : ℝ) - (r' : ℝ) / (q' : ℝ)| ≤
      L4D / ((q : ℝ) * len) + L4D / ((q' : ℝ) * len) :=
    abs_sub_le_iff.mpr ⟨hB, hA⟩
  linarith [hsep, hwidth, habs]

/-- The finite exponential polynomial is continuous (reproved here because
`Decomp512a` is not in the import closure of this file). -/
private lemma continuous_polynomial561 (S : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (fun t : ℝ => polynomial512 S c t) := by
  unfold polynomial512
  exact continuous_finsetSum S fun k hk => continuous_const.mul
    ((map_continuous (fourier (T := (1 : ℝ)) (k : ℤ))).comp (AddCircle.continuous_mk' 1))

/-- The integrand is continuous. -/
private lemma continuous_integrand561 (ε x : ℝ) (a b : ℕ → ℂ) (N : ℕ) :
    Continuous (fun t : ℝ => integrand512 ε x a b N t) := by
  unfold integrand512
  exact ((continuous_polynomial561 _ _).mul (continuous_polynomial561 _ _)).mul
    ((map_continuous (fourier (T := (1 : ℝ)) (-(N : ℤ)))).comp
      (AddCircle.continuous_mk' 1))

/-- On a single arc the integral equals the local integral in the variable of the arc. -/
private lemma arc_integral_shift561 (ε D x : ℝ) (a b : ℕ → ℂ) (N q r : ℕ) (hx1 : 1 < x) :
    (∫ t in Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
        ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
        integrand512 ε x a b N t)
      = ∫ s in (-(Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))..
          (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
          integrand512 ε x a b N ((r : ℝ) / (q : ℝ) + s) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hw : (0 : ℝ) ≤ Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x) := by
    have hL : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hl : (0 : ℝ) < length512 ε x := by
      unfold length512
      exact Real.rpow_pos_of_pos hx0 _
    have h1 : (0 : ℝ) < Real.log x ^ (4 * D) := Real.rpow_pos_of_pos hL _
    have h2 : (0 : ℝ) ≤ ((q : ℝ)) := Nat.cast_nonneg q
    by_cases hq : q = 0
    · simp [hq]
    · have hqpos : (0 : ℝ) < (q : ℝ) := by
        have : (0:ℕ) < q := Nat.pos_of_ne_zero hq
        exact_mod_cast this
      positivity
  have hle : (r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x) ≤
      (r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x) := by
    linarith
  have h1 : (∫ t in Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
        ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
        integrand512 ε x a b N t)
      = ∫ t in ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))..
          ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
          integrand512 ε x a b N t := by
    exact (MeasureTheory.integral_Icc_eq_integral_Ioc).trans
      (intervalIntegral.integral_of_le hle).symm
  rw [h1]
  exact (intervalIntegral.integral_comp_add_left (integrand512 ε x a b N)
    ((r : ℝ) / (q : ℝ))).symm

/-- The major arcs are exactly the union of the local Farey arcs of the reduced residues
of the moduli up to the logarithmic cutoff. -/
private lemma major512_eq_arcs561 {ε D x : ℝ} (hx1 : 1 < x) (hlog1 : 1 ≤ Real.log x)
    (hD : 0 ≤ D)
    (h4 : (4 : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hQord : 8 * Real.log x ^ (2 * D) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hordhi : Real.log x ^ (4 * D) ≤ length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)))
    (hlenbig : 4 * Real.log x ^ (8 * D) ≤ length512 ε x) :
    major512 ε D x = ⋃ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
      ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
          ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hlenpos : (0 : ℝ) < length512 ε x := by
    unfold length512
    exact Real.rpow_pos_of_pos hx0 _
  have hlen0 : (0 : ℝ) ≤ length512 ε x := le_of_lt hlenpos
  obtain ⟨hordlo, hordub⟩ := order_bounds561 hlen0 h4
  obtain ⟨hQ1, hQle⟩ := Q_facts561 hlog1 hD
  have hQord' : 2 * ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ (order512 ε x : ℝ) := by
    have h2 : 2 * Real.log x ^ (2 * D) ≤
        length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 4 := by linarith
    have h3 : 2 * ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ 2 * Real.log x ^ (2 * D) := by
      linarith
    linarith
  have hQleord : ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ (order512 ε x : ℝ) := by linarith
  have hmin : min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊ = ⌊Real.log x ^ (2 * D)⌋₊ :=
    min_eq_right (by exact_mod_cast hQleord)
  have hQpos : (0 : ℝ) < ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) := by
    have h : (1 : ℝ) ≤ ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hQ1
    linarith
  unfold major512 period512
  rw [hmin]
  ext t
  constructor
  · rintro ⟨-, ht⟩
    simpa only [Set.mem_iUnion, Finset.mem_Icc, Finset.mem_filter] using ht
  · intro ht
    simp only [Set.mem_iUnion, Finset.mem_Icc, Finset.mem_filter] at ht
    obtain ⟨q, ⟨hq1, hqQ⟩, r, ⟨⟨hr1, hrq⟩, hrc⟩, htr⟩ := ht
    have hsub := arc_containment561 hx1 hlog1 hD h4 hQord hordhi hlenbig
      (Q := ⌊Real.log x ^ (2 * D)⌋₊) (q := q) hQ1 hQle hq1 hqQ
      (w := Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) rfl hr1 hrq
    have h2 := hsub htr
    have h2' := Set.mem_Ioc.mp h2
    refine ⟨⟨h2'.1, h2'.2⟩, ?_⟩
    simp only [Set.mem_iUnion, Finset.mem_Icc, Finset.mem_filter]
    exact ⟨q, ⟨hq1, hqQ⟩, r, ⟨⟨hr1, hrq⟩, hrc⟩, htr⟩

/-- A single arc stays inside `[0, 2]`, hence the integrand is integrable on it. -/
private lemma arc_subset_Icc561 {ε D x : ℝ} (hx1 : 1 < x) (hlog1 : 1 ≤ Real.log x)
    (hD : 0 ≤ D)
    (h4 : (4 : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hQord : 8 * Real.log x ^ (2 * D) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hordhi : Real.log x ^ (4 * D) ≤ length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)))
    (hlenbig : 4 * Real.log x ^ (8 * D) ≤ length512 ε x)
    {q : ℕ} (hq1 : 1 ≤ q) (hqQn : q ≤ ⌊Real.log x ^ (2 * D)⌋₊)
    {r : ℕ} (hr1 : 1 ≤ r) (hrq : r ≤ q) :
    Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
      ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) ⊆
      Set.Icc (0 : ℝ) 2 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hlenpos : (0 : ℝ) < length512 ε x := by
    unfold length512
    exact Real.rpow_pos_of_pos hx0 _
  have hlen0 : (0 : ℝ) ≤ length512 ε x := le_of_lt hlenpos
  obtain ⟨hordlo, hordub⟩ := order_bounds561 hlen0 h4
  obtain ⟨hQ1, hQle⟩ := Q_facts561 hlog1 hD
  have hordpos : (0 : ℝ) < (order512 ε x : ℝ) := by
    have h1 : (0 : ℝ) < length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) :=
      Real.rpow_pos_of_pos hlenpos _
    linarith
  have hqQ' : (q : ℝ) ≤ ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hqQn
  have hsub := arc_containment561 hx1 hlog1 hD h4 hQord hordhi hlenbig
    (Q := ⌊Real.log x ^ (2 * D)⌋₊) (q := q) hQ1 hQle hq1 hqQn
    (w := Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) rfl hr1 hrq
  intro t ht
  have h1 := Set.mem_Ioc.mp (hsub ht)
  refine ⟨?_, ?_⟩
  · have h2 : (0 : ℝ) < 1 / (order512 ε x : ℝ) := by
      rw [one_div_pos]
      exact hordpos
    linarith [h1.1]
  · have h2 : 1 / (order512 ε x : ℝ) ≤ 1 := by
      rw [div_le_one hordpos]
      have h3 : (1 : ℝ) ≤ (order512 ε x : ℝ) := by linarith
      exact h3
    linarith [h1.2]

/-- Two arcs belonging to different moduli are disjoint. -/
private lemma arc_pair_disjoint561 {ε D x : ℝ} (hx1 : 1 < x) (hlog1 : 1 ≤ Real.log x)
    (hD : 0 ≤ D)
    (hlenbig : 4 * Real.log x ^ (8 * D) ≤ length512 ε x)
    {Q : ℕ} (hQle : (Q : ℝ) ≤ Real.log x ^ (2 * D)) (hQ1 : 1 ≤ Q)
    {q q' r r' : ℕ} (hq1 : 1 ≤ q) (hqQ : q ≤ Q) (hq'1 : 1 ≤ q') (hq'Q : q' ≤ Q)
    (hr1 : 1 ≤ r) (hrq : r ≤ q) (hr'1 : 1 ≤ r') (hr'q : r' ≤ q')
    (hrc : Nat.Coprime r q) (hr'c : Nat.Coprime r' q')
    (hne : (q, r) ≠ (q', r')) :
    Disjoint
      (Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
        ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))
      (Set.Icc ((r' : ℝ) / (q' : ℝ) - Real.log x ^ (4 * D) / ((q' : ℝ) * length512 ε x))
        ((r' : ℝ) / (q' : ℝ) + Real.log x ^ (4 * D) / ((q' : ℝ) * length512 ε x))) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hlenpos : (0 : ℝ) < length512 ε x := by
    unfold length512
    exact Real.rpow_pos_of_pos hx0 _
  have hLpos : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hLnn : (0 : ℝ) ≤ Real.log x := le_of_lt hLpos
  have hL4D : (0 : ℝ) < Real.log x ^ (4 * D) := Real.rpow_pos_of_pos hLpos _
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have h : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    linarith
  have hq'pos : (0 : ℝ) < (q' : ℝ) := by
    have h : (1 : ℝ) ≤ (q' : ℝ) := by exact_mod_cast hq'1
    linarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    have h : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
    linarith
  have hsep := frac_separation561 hq1 hq'1 hrc hr'c hne
  have hqq' : (q : ℝ) * (q' : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have h1 : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
    have h2 : (q' : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq'Q
    nlinarith [hqpos, hq'pos, hQpos]
  -- `log ^ 8D` beats `log ^ 4D * Q ^ 2`
  have hL6 : Real.log x ^ (4 * D) * (Q : ℝ) ^ 2 ≤ Real.log x ^ (8 * D) := by
    have h68 : Real.log x ^ (6 * D) ≤ Real.log x ^ (8 * D) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
    have hQ2 : (Q : ℝ) ^ 2 ≤ Real.log x ^ (2 * D) * Real.log x ^ (2 * D) := by
      rw [pow_two]
      exact mul_le_mul hQle hQle (le_of_lt hQpos) (Real.rpow_nonneg hLnn _)
    have hm1 : Real.log x ^ (4 * D) * (Real.log x ^ (2 * D) * Real.log x ^ (2 * D))
        = Real.log x ^ (6 * D) * Real.log x ^ (2 * D) := by
      have e1 : Real.log x ^ (4 * D) * Real.log x ^ (2 * D) = Real.log x ^ (6 * D) := by
        rw [← Real.rpow_add hLpos]; ring_nf
      rw [← e1]; ring
    have e2 : Real.log x ^ (6 * D) * Real.log x ^ (2 * D) = Real.log x ^ (8 * D) := by
      rw [← Real.rpow_add hLpos]; ring_nf
    calc Real.log x ^ (4 * D) * (Q : ℝ) ^ 2
        ≤ Real.log x ^ (4 * D) * (Real.log x ^ (2 * D) * Real.log x ^ (2 * D)) :=
          mul_le_mul_of_nonneg_left hQ2 (le_of_lt hL4D)
      _ = Real.log x ^ (6 * D) * Real.log x ^ (2 * D) := hm1
      _ = Real.log x ^ (8 * D) := e2
  have hsmall : 2 * Real.log x ^ (4 * D) * ((q : ℝ) * (q' : ℝ)) < length512 ε x := by
    have h1 : 2 * Real.log x ^ (4 * D) * ((q : ℝ) * (q' : ℝ)) ≤
        2 * Real.log x ^ (4 * D) * (Q : ℝ) ^ 2 := by
      refine mul_le_mul_of_nonneg_left hqq' ?_
      linarith
    have h2 : 2 * Real.log x ^ (4 * D) * (Q : ℝ) ^ 2 ≤ 2 * Real.log x ^ (8 * D) := by
      linarith [hL6]
    have h3 : (0 : ℝ) < Real.log x ^ (8 * D) := Real.rpow_pos_of_pos hLpos _
    nlinarith [hlenbig, h3, h1, h2]
  refine arcs_disjoint561 (le_of_lt hL4D) hlenpos hqpos hq'pos hsep ?_
  have hqc : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hq'c : (1 : ℝ) ≤ (q' : ℝ) := by exact_mod_cast hq'1
  have hw1 : Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x) ≤
      Real.log x ^ (4 * D) / length512 ε x := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * length512 ε x)
      (by positivity : (0 : ℝ) < length512 ε x)]
    have h : length512 ε x ≤ (q : ℝ) * length512 ε x := by
      have h' := mul_le_mul_of_nonneg_right hqc (le_of_lt hlenpos)
      simpa using h'
    exact mul_le_mul_of_nonneg_left h hL4D.le
  have hw2 : Real.log x ^ (4 * D) / ((q' : ℝ) * length512 ε x) ≤
      Real.log x ^ (4 * D) / length512 ε x := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (q' : ℝ) * length512 ε x)
      (by positivity : (0 : ℝ) < length512 ε x)]
    have h : length512 ε x ≤ (q' : ℝ) * length512 ε x := by
      have h' := mul_le_mul_of_nonneg_right hq'c (le_of_lt hlenpos)
      simpa using h'
    exact mul_le_mul_of_nonneg_left h hL4D.le
  have hmain : 2 * (Real.log x ^ (4 * D) / length512 ε x) < 1 / ((q : ℝ) * (q' : ℝ)) := by
    have h1 : 2 * (Real.log x ^ (4 * D) / length512 ε x)
        = 2 * Real.log x ^ (4 * D) / length512 ε x := by ring
    rw [h1]
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < length512 ε x)
      (by positivity : (0 : ℝ) < (q : ℝ) * (q' : ℝ))]
    linarith [hsmall]
  linarith [hw1, hw2, hmain]

/-- The major-arc integral is the sum of the local arc integrals. -/
private lemma integral_major512_arcs561 (ε D x : ℝ) (a b : ℝ → ℕ → ℂ) (N : ℕ)
    (hx1 : 1 < x) (hlog1 : 1 ≤ Real.log x) (hD : 0 ≤ D)
    (h4 : (4 : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hQord : 8 * Real.log x ^ (2 * D) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hordhi : Real.log x ^ (4 * D) ≤ length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)))
    (hlenbig : 4 * Real.log x ^ (8 * D) ≤ length512 ε x) :
    (∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) =
      ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∫ s in (-(Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))..
              (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s) := by
  rw [major512_eq_arcs561 hx1 hlog1 hD h4 hQord hordhi hlenbig]
  have hcont := continuous_integrand561 ε x (a x) (b x) N
  have hbig : MeasureTheory.IntegrableOn (integrand512 ε x (a x) (b x) N) (Set.Icc (0 : ℝ) 2) :=
    hcont.integrableOn_Icc
  obtain ⟨hQ1, hQle⟩ := Q_facts561 hlog1 hD
  have hfin : ∀ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊, MeasurableSet
      (⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
          ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))) := by
    intro q hq
    exact Finset.measurableSet_biUnion _ (fun r hr => measurableSet_Icc)
  have hint : ∀ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
      MeasureTheory.IntegrableOn (integrand512 ε x (a x) (b x) N)
        (⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
            ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))) := by
    intro q hq
    refine hbig.mono_set ?_
    intro t ht
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_Icc] at ht
    obtain ⟨r, ⟨⟨hr1, hrq⟩, hrc⟩, htr⟩ := ht
    exact arc_subset_Icc561 hx1 hlog1 hD h4 hQord hordhi hlenbig
      (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2 hr1 hrq htr
  have hdisj : ((Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊ : Finset ℕ) : Set ℕ).Pairwise
      (Function.onFun Disjoint
        (fun q => ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
            ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))) := by
    intro q hq q' hq' hne
    refine Set.disjoint_left.mpr ?_
    intro t ht ht'
    simp only [Set.mem_iUnion] at ht ht'
    obtain ⟨r, hr, htr⟩ := ht
    obtain ⟨r', hr', htr'⟩ := ht'
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr hr'
    exact (Set.disjoint_left.mp (arc_pair_disjoint561 hx1 hlog1 hD hlenbig
      (Q := ⌊Real.log x ^ (2 * D)⌋₊) hQle hQ1
      (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
      (Finset.mem_Icc.mp hq').1 (Finset.mem_Icc.mp hq').2
      hr.1.1 hr.1.2 hr'.1.1 hr'.1.2 hr.2 hr'.2
      (by rintro ⟨rfl, rfl⟩; exact hne rfl))) htr htr'
  rw [MeasureTheory.integral_biUnion_finset (Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊) hfin hdisj hint]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hfin' : ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), MeasurableSet
      (Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
        ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))) := by
    intro r hr
    exact measurableSet_Icc
  have hint' : ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
      MeasureTheory.IntegrableOn (integrand512 ε x (a x) (b x) N)
        (Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
          ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))) := by
    intro r hr
    refine hbig.mono_set ?_
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    exact arc_subset_Icc561 hx1 hlog1 hD h4 hQord hordhi hlenbig
      (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2 hr.1.1 hr.1.2 ht
  have hdisj' : (((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q) : Finset ℕ) : Set ℕ).Pairwise
      (Function.onFun Disjoint
        (fun r => Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
          ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))) := by
    intro r hr r' hr' hne
    obtain ⟨hrI, hrc⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr'I, hr'c⟩ := Finset.mem_filter.mp hr'
    obtain ⟨hr1, hrq⟩ := Finset.mem_Icc.mp hrI
    obtain ⟨hr'1, hr'q⟩ := Finset.mem_Icc.mp hr'I
    exact arc_pair_disjoint561 hx1 hlog1 hD hlenbig
      (Q := ⌊Real.log x ^ (2 * D)⌋₊) hQle hQ1
      (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
      (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
      hr1 hrq hr'1 hr'q hrc hr'c
      (by rintro ⟨rfl, rfl⟩; exact hne rfl)
  rw [MeasureTheory.integral_biUnion_finset ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q))
    hfin' hdisj' hint']
  exact Finset.sum_congr rfl (fun r hr => arc_integral_shift561 ε D x (a x) (b x) N q r hx1)

/-- Arc decomposition: the major-arc integral is the sum of the local arc integrals. -/
private theorem arc_decomposition561 (ε D : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ (a b : ℝ → ℕ → ℂ) (N : ℕ),
      (∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) =
        ∑ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
          ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
                (Real.log x ^ (4 * D) / (q * length512 ε x)),
              integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s) := by
  have hexp2 : (1 : ℝ) < Real.exp 2 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  by_cases hc : (0 : ℝ) < 11 / 20 + ε
  · by_cases hD : (0 : ℝ) ≤ D
    · obtain ⟨X, hX⟩ := exists_threshold561 ε D hc hD
      refine ⟨max X (Real.exp 2) + 1, ?_⟩
      intro x hx a b N
      have hXx : X ≤ x := by
        have h0 : X ≤ max X (Real.exp 2) := le_max_left _ _
        linarith
      have hexp : Real.exp 2 ≤ x := by
        have h0 : Real.exp 2 ≤ max X (Real.exp 2) := le_max_right _ _
        linarith
      obtain ⟨hlog1, h4, hQord, hordhi, hlenbig⟩ := hX x hXx
      have hx1 : 1 < x := lt_of_lt_of_le hexp2 hexp
      have hlen0 : (0 : ℝ) ≤ length512 ε x := by
        unfold length512
        exact Real.rpow_nonneg (by linarith) _
      have hQleord : ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ (order512 ε x : ℝ) := by
        obtain ⟨hordlo, -⟩ := order_bounds561 hlen0 h4
        have h1 : 2 * Real.log x ^ (2 * D) ≤
            length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 4 := by linarith
        have h2 : ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ Real.log x ^ (2 * D) :=
          (Q_facts561 hlog1 hD).2
        linarith
      have hmin : min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊ = ⌊Real.log x ^ (2 * D)⌋₊ :=
        min_eq_right (by exact_mod_cast hQleord)
      rw [hmin]
      exact integral_major512_arcs561 ε D x a b N hx1 hlog1 hD h4 hQord hordhi hlenbig
    · push Not at hD
      refine ⟨max 1 (Real.exp 2) + 1, ?_⟩
      intro x hx a b N
      have hexp : Real.exp 2 ≤ x := by
        have h0 : Real.exp 2 ≤ max 1 (Real.exp 2) := le_max_right _ _
        linarith
      have hlog : 1 < Real.log x := by
        have h := Real.log_le_log (Real.exp_pos 2) hexp
        rw [Real.log_exp] at h
        linarith
      have hQ0 : ⌊Real.log x ^ (2 * D)⌋₊ = 0 := by
        refine Nat.floor_eq_zero.mpr ?_
        exact Real.rpow_lt_one_of_one_lt_of_neg hlog (by linarith)
      have hmin0 : min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊ = 0 := by
        rw [hQ0, _root_.min_zero]
      rw [hmin0]
      simp [major512, hmin0]
  · push Not at hc
    refine ⟨max 1 (Real.exp 2) + 1, ?_⟩
    intro x hx a b N
    have hx1 : (1 : ℝ) ≤ x := by
      have h0 : (1 : ℝ) ≤ max 1 (Real.exp 2) := le_max_left _ _
      linarith
    have hlenle : length512 ε x ≤ 1 := by
      unfold length512
      exact Real.rpow_le_one_of_one_le_of_nonpos hx1 hc
    have hlen0 : (0 : ℝ) ≤ length512 ε x := by
      unfold length512
      exact Real.rpow_nonneg (by linarith) _
    have hdelta : (0 : ℝ) ≤ 2 * (1 / 16 - 1 / 10 ^ 5) := by norm_num
    have hord0 : order512 ε x = 0 := by
      unfold order512
      have h2 : (length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ ((1 / 2 : ℝ)) ≤ 1 := by
        refine Real.rpow_le_one (Real.rpow_nonneg hlen0 _) ?_ (by norm_num)
        exact Real.rpow_le_one hlen0 hlenle hdelta
      have h1 : (length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ ((1 / 2 : ℝ)) / 2 < 1 := by
        linarith
      exact Nat.floor_eq_zero.mpr h1
    have hmin0 : min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊ = 0 := by
      rw [hord0, _root_.zero_min]
    rw [hmin0]
    simp [major512, hmin0]

set_option maxHeartbeats 1200000 in
/-- One major arc: the arc integral of the long times short polynomial differs from the
principal model by at most the arc length times the pointwise character replacement error
times the mass of the short block. -/
private theorem arc_error_bound561 (lo hi loJ hiJ : ℕ) (a b : ℕ → ℂ) {q : ℕ} (hq : 0 < q)
    (r : ℕ) (hrr : r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q))
    (w : ℂ) (M h : ℝ) (N : ℕ) (hh : 0 ≤ h) (hM : 0 ≤ M)
    (hsupp : ∀ k ∈ Finset.Ioc lo hi, a k ≠ 0 → IsUnit ((k : ZMod q)))
    (hc : ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ (hi : ℝ) →
      ‖∑ k ∈ (Finset.Ioc lo hi).filter (fun k : ℕ => (k : ℝ) ≤ t),
        (a k * χ (k : ZMod q) - delta χ * w)‖ ≤ M) :
    ‖(∫ η in (-h)..h, (((∑ k ∈ Finset.Ioc lo hi, a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) -
      (w * ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * ∫ η in (-h)..h, (((∑ k ∈ Finset.Ioc lo hi, (1 : ℂ) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))))‖ ≤
      2 * h * (Real.sqrt q * ((1 + 2 * Real.pi * h * ((hi - lo : ℕ) : ℝ)) * M) *
        ∑ m ∈ Finset.Ioc loJ hiJ, ‖b m‖) := by
  haveI : NeZero q := ⟨Nat.pos_iff_ne_zero.mp hq⟩
  obtain ⟨hrI, hrc⟩ := Finset.mem_filter.mp hrr
  have hrunit : IsUnit ((((r : ℕ) : ℤ) : ZMod q)) := by
    rw [Int.cast_natCast]
    exact (ZMod.isUnit_iff_coprime r q).mpr hrc
  set V : ℝ := ∑ m ∈ Finset.Ioc loJ hiJ, ‖b m‖ with hVdef
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun m _ => norm_nonneg _)
  have hS2 : ∀ η : ℝ, ‖(∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))‖ ≤ V := by
    intro η
    refine le_trans (norm_sum_le _ _) ?_
    rw [hVdef]
    exact Finset.sum_le_sum (fun m _ => by
      rw [norm_mul, LeanLab.BHP1997.Route512Major.fourier_norm512j, mul_one])
  have hS1 : ∀ η : ℝ, |η| ≤ h →
      ‖(∑ k ∈ Finset.Ioc lo hi, a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) -
        (q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w * (∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)))‖ ≤
      Real.sqrt q * ((1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M) := by
    intro η _
    have h := LeanLab.BHP1997.Route512Major.major_character512j lo hi a (((r : ℕ) : ℤ))
      hrunit w M ((hi : ℝ)) le_rfl hsupp hc η
    rw [LeanLab.BHP1997.Route512Major.gauss_principal512j q] at h
    simpa using h
  have hpt : ∀ η : ℝ, |η| ≤ h → ‖((((∑ k ∈ Finset.Ioc lo hi, a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) - (q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w * (∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))‖ ≤
      Real.sqrt q * ((1 + 2 * Real.pi * h * ((hi - lo : ℕ) : ℝ)) * M) * V := by
    intro η hη
    have h1 := hS1 η hη
    have h2 := hS2 η
    have h3 : ‖@fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))‖ = 1 := LeanLab.BHP1997.Route512Major.fourier_norm512j _ _
    have hB : 0 ≤ Real.sqrt q * ((1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M) :=
      (norm_nonneg _).trans h1
    have hlen0 : (0 : ℝ) ≤ ((hi - lo : ℕ) : ℝ) := Nat.cast_nonneg _
    have hstep : Real.sqrt q * ((1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M) ≤
        Real.sqrt q * ((1 + 2 * Real.pi * h * ((hi - lo : ℕ) : ℝ)) * M) := by
      have : 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ) ≤
          2 * Real.pi * h * ((hi - lo : ℕ) : ℝ) := by
        have h4 : Real.pi * |η| * ((hi - lo : ℕ) : ℝ) ≤
            Real.pi * h * ((hi - lo : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hη Real.pi_pos.le) hlen0
        nlinarith [h4]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by linarith) hM) (Real.sqrt_nonneg _)
    calc ‖((((∑ k ∈ Finset.Ioc lo hi, a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) - (q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w * (∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))‖ = ‖(∑ k ∈ Finset.Ioc lo hi, a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) -
          (q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w * (∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)))‖ * ‖(∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))‖ * ‖@fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))‖ := by
          rw [norm_mul, norm_mul]
      _ = ‖(∑ k ∈ Finset.Ioc lo hi, a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) -
          (q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w * (∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)))‖ * ‖(∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))‖ := by
          rw [h3, mul_one]
      _ ≤ (Real.sqrt q * ((1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M)) * V :=
          mul_le_mul h1 h2 (norm_nonneg _) hB
      _ ≤ (Real.sqrt q * ((1 + 2 * Real.pi * h * ((hi - lo : ℕ) : ℝ)) * M)) * V :=
          mul_le_mul_of_nonneg_right hstep hV0
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  set c : ℂ := w * ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) with hcdef
  have hcontA : Continuous (fun η : ℝ => (((∑ k ∈ Finset.Ioc lo hi, a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) := by
    have hp : ∀ (S : Finset ℕ) (cc : ℕ → ℂ), Continuous (fun η : ℝ =>
        ∑ k ∈ S, cc k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) :=
      fun S cc => continuous_finsetSum S fun k _ => continuous_const.mul
        (((map_continuous (fourier (T := (1 : ℝ)) (k : ℤ))).comp
          (AddCircle.continuous_mk' 1)).comp (continuous_const.add continuous_id))
    exact ((hp _ a).mul (hp _ b)).mul
      (((map_continuous (fourier (T := (1 : ℝ)) (-(N : ℤ)))).comp
        (AddCircle.continuous_mk' 1)).comp (continuous_const.add continuous_id))
  have hcontB : Continuous (fun η : ℝ => (((∑ k ∈ Finset.Ioc lo hi, (1 : ℂ) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) := by
    have hp : Continuous (fun η : ℝ =>
        ∑ k ∈ Finset.Ioc lo hi, (1 : ℂ) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) :=
      continuous_finsetSum _ fun k _ => continuous_const.mul
        ((map_continuous (fourier (T := (1 : ℝ)) (k : ℤ))).comp (AddCircle.continuous_mk' 1))
    have hq2 : Continuous (fun η : ℝ =>
        ∑ m ∈ Finset.Ioc loJ hiJ,
          b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) :=
      continuous_finsetSum _ fun k _ => continuous_const.mul
        (((map_continuous (fourier (T := (1 : ℝ)) (k : ℤ))).comp
          (AddCircle.continuous_mk' 1)).comp (continuous_const.add continuous_id))
    exact (hp.mul hq2).mul
      (((map_continuous (fourier (T := (1 : ℝ)) (-(N : ℤ)))).comp
        (AddCircle.continuous_mk' 1)).comp (continuous_const.add continuous_id))
  have hcontBc : Continuous (fun η : ℝ => c * (((∑ k ∈ Finset.Ioc lo hi, (1 : ℂ) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) := continuous_const.mul hcontB
  have hsplit : (∫ η in (-h)..h, (((∑ k ∈ Finset.Ioc lo hi, a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) - c * (∫ η in (-h)..h, (((∑ k ∈ Finset.Ioc lo hi, (1 : ℂ) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) =
      ∫ η in (-h)..h, ((((∑ k ∈ Finset.Ioc lo hi, a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) - c * (((∑ k ∈ Finset.Ioc lo hi, (1 : ℂ) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) := by
    rw [← intervalIntegral.integral_const_mul]
    exact (intervalIntegral.integral_sub (hcontA.intervalIntegrable (-h) h)
      (hcontBc.intervalIntegrable (-h) h)).symm
  have hcongr : (∫ η in (-h)..h, ((((∑ k ∈ Finset.Ioc lo hi, a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) - c * (((∑ k ∈ Finset.Ioc lo hi, (1 : ℂ) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))))) = ∫ η in (-h)..h, ((((∑ k ∈ Finset.Ioc lo hi, a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) - (q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w * (∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro η _
    simp only [one_mul]
    rw [hcdef]
    simp only [div_eq_mul_inv]
    ring
  have hid := hsplit.trans hcongr
  have hgoal : (∫ η in (-h)..h, (((∑ k ∈ Finset.Ioc lo hi, a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) - (w * ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * ∫ η in (-h)..h, (((∑ k ∈ Finset.Ioc lo hi, (1 : ℂ) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) =
      ∫ η in (-h)..h, ((((∑ k ∈ Finset.Ioc lo hi, a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) - (q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w * (∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)) := by
    rw [← hcdef]
    exact hid
  rw [hgoal]
  have hfin : ‖∫ η in (-h)..h, ((((∑ k ∈ Finset.Ioc lo hi, a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) - (q.totient : ℂ)⁻¹ * (ArithmeticFunction.moebius q : ℂ) * w * (∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)))) * (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))‖ ≤
      (Real.sqrt q * ((1 + 2 * Real.pi * h * ((hi - lo : ℕ) : ℝ)) * M) *
        ∑ m ∈ Finset.Ioc loJ hiJ, ‖b m‖) * |h - (-h)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun η hη => ?_)
    rw [Set.uIoc_of_le (show (-h : ℝ) ≤ h by linarith)] at hη
    exact hpt η (abs_le.mpr ⟨by linarith [hη.1], hη.2⟩)
  refine hfin.trans (le_of_eq ?_)
  rw [show h - (-h) = 2 * h by ring, abs_of_nonneg (by linarith)]
  ring

/-- The Farey order of the major arcs eventually dominates the logarithmic modulus cutoff. -/
private lemma order_domination561 (ε D : ℝ) (hε : 0 < 11 / 20 + ε) (hD : 0 ≤ D) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ⌊Real.log x ^ (2 * D)⌋₊ ≤ order512 ε x := by
  obtain ⟨X, hX⟩ := exists_threshold561 ε D hε hD
  refine ⟨max X 1, fun x hx => ?_⟩
  obtain ⟨hlog1, h4, hQord, hordhi, hlenbig⟩ := hX x (le_trans (le_max_left _ _) hx)
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hlen0 : (0 : ℝ) ≤ length512 ε x := by
    unfold length512
    exact Real.rpow_nonneg (by linarith) _
  obtain ⟨hordlo, -⟩ := order_bounds561 hlen0 h4
  have hQle := (Q_facts561 hlog1 hD).2
  have hreal : ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ (order512 ε x : ℝ) := by linarith
  exact_mod_cast hreal

/-- Numeric absorption for one modulus: the sum over the reduced residues of the pointwise
arc bounds is within the logarithmic budget once the arc width, the modulus cutoff and the
number of residues are all charged to `log x`. Pure real arithmetic. -/
private lemma arc_term_absorb561 (ℓ L M V : ℝ) (q : ℕ) (D A C₁ : ℝ) (blk : ℝ)
    (hq1 : 1 ≤ q) (hℓ1 : 1 ≤ ℓ) (hD0 : 0 ≤ D) (hL0 : 0 < L)
    (hqD : (q : ℝ) ≤ ℓ ^ (2 * D))
    (hblk : blk ≤ 3 * L) (hblk0 : 0 ≤ blk)
    (hM0 : 0 ≤ M) (hM : M = |C₁| * L * ℓ ^ (-(A + 12 * D)))
    (hV0 : 0 ≤ V) :
    (q : ℝ) * (2 * (ℓ ^ (4 * D) / ((q : ℝ) * L)) *
      (Real.sqrt q * ((1 + 2 * Real.pi * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * blk) * M) * V))
      ≤ 14 * Real.pi * |C₁| * ℓ ^ (-A - 2 * D) * V := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have h : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    linarith
  have h4D : (0 : ℝ) ≤ 4 * D := by linarith
  have h2D : (0 : ℝ) ≤ 2 * D := by linarith
  have hP4 : (1 : ℝ) ≤ ℓ ^ (4 * D) := Real.one_le_rpow hℓ1 h4D
  have hP2 : (1 : ℝ) ≤ ℓ ^ (2 * D) := Real.one_le_rpow hℓ1 h2D
  have hq1r : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hsq : Real.sqrt q ≤ ℓ ^ (2 * D) := by
    refine le_trans (Real.sqrt_le_self_iff.mpr (Or.inr hq1r)) hqD
  have hhpos : (0 : ℝ) < ℓ ^ (4 * D) / ((q : ℝ) * L) := by positivity
  -- the local width times the block length
  have hhblk : (ℓ ^ (4 * D) / ((q : ℝ) * L)) * blk ≤ 3 * ℓ ^ (4 * D) / (q : ℝ) := by
    have h1 : (ℓ ^ (4 * D) / ((q : ℝ) * L)) * blk
        ≤ (ℓ ^ (4 * D) / ((q : ℝ) * L)) * (3 * L) :=
      mul_le_mul_of_nonneg_left hblk (le_of_lt hhpos)
    have h2 : (ℓ ^ (4 * D) / ((q : ℝ) * L)) * (3 * L) = 3 * ℓ ^ (4 * D) / (q : ℝ) := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  have h3div : 3 * ℓ ^ (4 * D) / (q : ℝ) ≤ 3 * ℓ ^ (4 * D) := by
    rw [div_le_iff₀ hqpos]
    nlinarith [hP4, hq1r]
  have hone : (1 : ℝ) ≤ Real.pi * ℓ ^ (4 * D) := by
    have hπ : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [hπ, hP4]
  have hfac : 1 + 2 * Real.pi * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * blk
      ≤ 7 * Real.pi * ℓ ^ (4 * D) := by
    have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have hb1 : 2 * Real.pi * ((ℓ ^ (4 * D) / ((q : ℝ) * L)) * blk)
        ≤ 2 * Real.pi * (3 * ℓ ^ (4 * D) / (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hhblk h2π
    have hb2 : 2 * Real.pi * (3 * ℓ ^ (4 * D) / (q : ℝ)) ≤ 2 * Real.pi * (3 * ℓ ^ (4 * D)) :=
      mul_le_mul_of_nonneg_left h3div h2π
    linarith [hb1, hb2, hone]
  have hstep : Real.sqrt q * ((1 + 2 * Real.pi * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * blk) * M)
      ≤ ℓ ^ (2 * D) * ((7 * Real.pi * ℓ ^ (4 * D)) * M) := by
    refine mul_le_mul hsq (mul_le_mul_of_nonneg_right hfac hM0) (by positivity) (by positivity)
  have hkey : ℓ ^ (4 * D) * ℓ ^ (2 * D) * ℓ ^ (4 * D) * ℓ ^ (-(A + 12 * D)) = ℓ ^ (-A - 2 * D) := by
    rw [← Real.rpow_add hℓ0, ← Real.rpow_add hℓ0, ← Real.rpow_add hℓ0]
    congr 1
    ring
  have hinner : (Real.sqrt q * ((1 + 2 * Real.pi * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * blk) * M) * V)
      ≤ (ℓ ^ (2 * D) * (7 * Real.pi * ℓ ^ (4 * D) * M) * V) :=
    mul_le_mul_of_nonneg_right hstep hV0
  have hwidth : (0 : ℝ) ≤ 2 * (ℓ ^ (4 * D) / ((q : ℝ) * L)) := by linarith [hhpos]
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := le_of_lt hqpos
  have hstep2 : (q : ℝ) * (2 * (ℓ ^ (4 * D) / ((q : ℝ) * L)) *
        (Real.sqrt q * ((1 + 2 * Real.pi * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * blk) * M) * V))
      ≤ (q : ℝ) * (2 * (ℓ ^ (4 * D) / ((q : ℝ) * L)) *
        (ℓ ^ (2 * D) * (7 * Real.pi * ℓ ^ (4 * D) * M) * V)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hwidth) hqnn
  have hmain : (q : ℝ) * (2 * (ℓ ^ (4 * D) / ((q : ℝ) * L)) *
        (ℓ ^ (2 * D) * (7 * Real.pi * ℓ ^ (4 * D) * M) * V))
      = 14 * Real.pi * |C₁| *
          (ℓ ^ (4 * D) * ℓ ^ (2 * D) * ℓ ^ (4 * D) * ℓ ^ (-(A + 12 * D))) * V := by
    rw [hM]
    field_simp
    ring
  refine le_trans hstep2 (le_of_eq ?_)
  rw [hmain, hkey]

set_option maxHeartbeats 2000000 in
/-- LEAF. Replacement at a single frequency. Assuming the prefix distribution of a
against every character of a small modulus and the rough support of a, the error made
by replacing the long polynomial by its principal model at one even frequency is at
most a logarithmic saving times the mass of the short block. The sum of squares over
the frequencies is not taken here. -/
theorem leaf_long_prefix_replacement561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (a b : ℝ → ℕ → ℂ) (u : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
          ‖∑ k ∈ (I x).filter (fun k : ℕ => (k : ℝ) ≤ t),
            (a x k * χ (k : ZMod q) - delta χ * u / Real.log x)‖ ≤ C * Y x * Real.log x ^ (-A)) →
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
        Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0) →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ N ∈ frequencies512 ε x,
          ‖(∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) -
              longPrincipal561 ε D x (b x) u N‖ ≤
            C * Real.log x ^ (-A) *
              ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
  refine ⟨1, one_pos, ?_⟩
  intro ε hε hε1 a b u
  dsimp only
  intro hdist hrough A hA
  have hεpos : (0 : ℝ) < 11 / 20 + ε := by linarith
  refine ⟨0, fun D hD => ?_⟩
  have hD0 : 0 ≤ D := hD
  obtain ⟨C₁, hC₁⟩ := hdist (A + 12 * D) (by linarith)
  obtain ⟨Xd, hXd⟩ := arc_decomposition561 ε D
  obtain ⟨Xo, hXo⟩ := order_domination561 ε D hεpos hD0
  obtain ⟨Xr, hXr⟩ := rough_coprime561 a hrough (2 * D + 2) (by linarith)
  obtain ⟨Xt, hXt⟩ := exists_threshold561 ε D hεpos hD0
  refine ⟨max (14 * Real.pi * |C₁|)
    (max (max (max (max Xd Xo) (max Xr Xt)) 2) C₁), fun x hx N hN => ?_⟩
  have hCge : 14 * Real.pi * |C₁| ≤
      max (14 * Real.pi * |C₁|) (max (max (max (max Xd Xo) (max Xr Xt)) 2) C₁) :=
    le_max_left _ _
  have hx2 : max (max (max (max Xd Xo) (max Xr Xt)) 2) C₁ ≤ x :=
    le_trans (le_max_right _ _) hx
  have hxC1 : C₁ ≤ x := le_trans (le_max_right _ _) hx2
  have hx3 : max (max (max Xd Xo) (max Xr Xt)) 2 ≤ x := le_trans (le_max_left _ _) hx2
  have h2x : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx3
  have hin : max (max Xd Xo) (max Xr Xt) ≤ x := le_trans (le_max_left _ _) hx3
  have hAB : max Xd Xo ≤ x := le_trans (le_max_left _ _) hin
  have hxd : Xd ≤ x := le_trans (le_max_left _ _) hAB
  have hxo : Xo ≤ x := le_trans (le_max_right _ _) hAB
  have hCD : max Xr Xt ≤ x := le_trans (le_max_right _ _) hin
  have hxr : Xr ≤ x := le_trans (le_max_left _ _) hCD
  have hxt : Xt ≤ x := le_trans (le_max_right _ _) hCD
  obtain ⟨hlog1, h4, hQord, hordhi, hlenbig⟩ := hXt x hxt
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set ℓ : ℝ := Real.log x with hℓdef
  set L : ℝ := length512 ε x with hLdef
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef]; exact hlog1
  have hℓ0 : 0 < ℓ := by linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef]; unfold length512
    exact Real.one_le_rpow hx1 (by linarith)
  have hL0 : 0 < L := by linarith
  have hQord2 : ⌊ℓ ^ (2 * D)⌋₊ ≤ order512 ε x := by rw [hℓdef]; exact hXo x hxo
  have hQle : ((⌊ℓ ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ ℓ ^ (2 * D) :=
    Nat.floor_le (Real.rpow_nonneg hℓ0.le _)
  have hmin : min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊ = ⌊ℓ ^ (2 * D)⌋₊ := by
    rw [hℓdef]
    exact min_eq_right hQord2
  set M : ℝ := |C₁| * L * ℓ ^ (-(A + 12 * D)) with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  set V : ℝ := ∑ m ∈ Finset.Ioc ⌊L⌋₊ ⌊2 * L⌋₊, ‖b x m‖ with hVdef
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun m _ => norm_nonneg _)
  have hblk : ((⌊x⌋₊ - ⌊x - 2 * L⌋₊ : ℕ) : ℝ) ≤ 3 * L := by
    have hb1 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
    have hb2 : x - 2 * L - 1 < ((⌊x - 2 * L⌋₊ : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (x - 2 * L); linarith
    have hb3 : ⌊x - 2 * L⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (by linarith)
    rw [Nat.cast_sub hb3]
    linarith
  have hdec := hXd x hxd a b N
  rw [hmin] at hdec
  have hlong : longPrincipal561 ε D x (b x) u N =
      ∑ q ∈ Finset.Icc 1 ⌊ℓ ^ (2 * D)⌋₊,
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          (u / ℓ) * ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) *
            ∫ s in (-(ℓ ^ (4 * D) / ((q : ℝ) * L)))..(ℓ ^ (4 * D) / ((q : ℝ) * L)),
              (((∑ k ∈ Finset.Ioc ⌊x - 2 * L⌋₊ ⌊x⌋₊, (1 : ℂ) * @fourier 1 (k : ℤ) (s : AddCircle (1 : ℝ))) * (∑ m ∈ Finset.Ioc ⌊L⌋₊ ⌊2 * L⌋₊, b x m * @fourier 1 (m : ℤ) (((r : ℝ) / q + s : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + s : ℝ) : AddCircle (1 : ℝ))) := by
    unfold longPrincipal561 polynomial512
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    dsimp only
    ring
  rw [hdec, hlong]
  simp only [← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun q _ => norm_sum_le _ _)) ?_
  have hper : ∀ q ∈ Finset.Icc 1 ⌊ℓ ^ (2 * D)⌋₊,
      ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
      ‖(∫ s in (-(ℓ ^ (4 * D) / ((q : ℝ) * L)))..(ℓ ^ (4 * D) / ((q : ℝ) * L)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          (u / ℓ) * ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) *
            ∫ s in (-(ℓ ^ (4 * D) / ((q : ℝ) * L)))..(ℓ ^ (4 * D) / ((q : ℝ) * L)),
              (((∑ k ∈ Finset.Ioc ⌊x - 2 * L⌋₊ ⌊x⌋₊, (1 : ℂ) * @fourier 1 (k : ℤ) (s : AddCircle (1 : ℝ))) * (∑ m ∈ Finset.Ioc ⌊L⌋₊ ⌊2 * L⌋₊, b x m * @fourier 1 (m : ℤ) (((r : ℝ) / q + s : ℝ) : AddCircle (1 : ℝ)))) * @fourier 1 (-(N : ℤ)) (((r : ℝ) / q + s : ℝ) : AddCircle (1 : ℝ)))‖ ≤ (2 * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * (Real.sqrt q * ((1 + 2 * Real.pi * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * ((⌊x⌋₊ - ⌊x - 2 * L⌋₊ : ℕ) : ℝ)) * M) * V)) := by
    intro q hq r hr
    obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      have h : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      linarith
    have hqD : (q : ℝ) ≤ ℓ ^ (2 * D) := le_trans (by exact_mod_cast hqQ) hQle
    have hqlog : (q : ℝ) ≤ Real.log x ^ (A + 12 * D) := by
      refine le_trans hqD ?_
      rw [← hℓdef]
      exact Real.rpow_le_rpow_of_exponent_le hℓ1 (by linarith)
    have hqfloor : q ≤ ⌊Real.log x ^ (2 * D + 2)⌋₊ := by
      apply Nat.le_floor
      refine le_trans hqD ?_
      rw [← hℓdef]
      exact Real.rpow_le_rpow_of_exponent_le hℓ1 (by linarith)
    have hhi : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
    have hwid0 : (0 : ℝ) ≤ (ℓ ^ (4 * D) / ((q : ℝ) * L)) := by positivity
    have hsupp : ∀ k ∈ Finset.Ioc ⌊x - 2 * L⌋₊ ⌊x⌋₊, a x k ≠ 0 → IsUnit ((k : ZMod q)) := by
      intro k hk hak
      have hc := hXr x hxr k q hq1 hqfloor hak
      exact (ZMod.isUnit_iff_coprime k q).mpr hc
    have hc : ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ ((⌊x⌋₊ : ℕ) : ℝ) →
        ‖∑ k ∈ (Finset.Ioc ⌊x - 2 * L⌋₊ ⌊x⌋₊).filter (fun k : ℕ => (k : ℝ) ≤ t),
          (a x k * χ (k : ZMod q) - delta χ * (u / ℓ))‖ ≤ M := by
      intro χ t ht
      have ht' : t ≤ x := le_trans ht hhi
      have h1 := hC₁ x hxC1 q hq1 hqlog χ t ht'
      have h2 : C₁ * x ^ (11 / 20 + ε) * Real.log x ^ (-(A + 12 * D)) ≤ M := by
        rw [hMdef]
        have hpos : (0 : ℝ) ≤ ℓ ^ (-(A + 12 * D)) := by rw [hℓdef]; positivity
        have hLL : C₁ * L ≤ |C₁| * L :=
          mul_le_mul_of_nonneg_right (le_abs_self C₁) (le_of_lt hL0)
        exact mul_le_mul_of_nonneg_right hLL hpos
      have hform : ∀ k : ℕ, (a x k * χ (k : ZMod q) - delta χ * (u / ℓ))
          = (a x k * χ (k : ZMod q) - delta χ * u / Real.log x) := by
        intro k
        rw [hℓdef]
        ring
      simp only [hform]
      exact le_trans h1 h2
    exact arc_error_bound561 ⌊x - 2 * L⌋₊ ⌊x⌋₊ ⌊L⌋₊ ⌊2 * L⌋₊ (a x) (b x) (by omega) r hr
      (u / ℓ) M (ℓ ^ (4 * D) / ((q : ℝ) * L)) N hwid0 hM0 hsupp hc
  refine le_trans (b := ∑ q ∈ Finset.Icc 1 ⌊ℓ ^ (2 * D)⌋₊,
      ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), (2 * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * (Real.sqrt q * ((1 + 2 * Real.pi * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * ((⌊x⌋₊ - ⌊x - 2 * L⌋₊ : ℕ) : ℝ)) * M) * V))) ?_ ?_
  · exact Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun r hr => hper q hq r hr))
  have hconst : ∀ q ∈ Finset.Icc 1 ⌊ℓ ^ (2 * D)⌋₊,
      ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), (2 * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * (Real.sqrt q * ((1 + 2 * Real.pi * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * ((⌊x⌋₊ - ⌊x - 2 * L⌋₊ : ℕ) : ℝ)) * M) * V))
        = (((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card : ℝ) * (2 * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * (Real.sqrt q * ((1 + 2 * Real.pi * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * ((⌊x⌋₊ - ⌊x - 2 * L⌋₊ : ℕ) : ℝ)) * M) * V)) := by
    intro q hq
    rw [Finset.sum_const, nsmul_eq_mul]
  calc ∑ q ∈ Finset.Icc 1 ⌊ℓ ^ (2 * D)⌋₊,
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), (2 * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * (Real.sqrt q * ((1 + 2 * Real.pi * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * ((⌊x⌋₊ - ⌊x - 2 * L⌋₊ : ℕ) : ℝ)) * M) * V))
      = ∑ q ∈ Finset.Icc 1 ⌊ℓ ^ (2 * D)⌋₊,
          (((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card : ℝ) * (2 * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * (Real.sqrt q * ((1 + 2 * Real.pi * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * ((⌊x⌋₊ - ⌊x - 2 * L⌋₊ : ℕ) : ℝ)) * M) * V)) :=
        Finset.sum_congr rfl hconst
    _ ≤ ∑ q ∈ Finset.Icc 1 ⌊ℓ ^ (2 * D)⌋₊, (q : ℝ) * (2 * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * (Real.sqrt q * ((1 + 2 * Real.pi * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * ((⌊x⌋₊ - ⌊x - 2 * L⌋₊ : ℕ) : ℝ)) * M) * V)) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
        have hqpos' : (0 : ℝ) < (q : ℝ) := by
          have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
          linarith
        have hc1 : (((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card : ℝ) ≤ (q : ℝ) := by
          have h1 : ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card ≤ q :=
            le_trans (Finset.card_filter_le _ _) (by simp)
          exact_mod_cast h1
        have hWnn : (0 : ℝ) ≤ (2 * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * (Real.sqrt q * ((1 + 2 * Real.pi * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * ((⌊x⌋₊ - ⌊x - 2 * L⌋₊ : ℕ) : ℝ)) * M) * V)) := by
          have hwid : (0 : ℝ) ≤ (ℓ ^ (4 * D) / ((q : ℝ) * L)) := by
            apply div_nonneg (Real.rpow_nonneg hℓ0.le _)
            positivity
          have hblk0 : (0 : ℝ) ≤ ((⌊x⌋₊ - ⌊x - 2 * L⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
          have hone : (0 : ℝ) ≤ 1 + 2 * Real.pi * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * ((⌊x⌋₊ - ⌊x - 2 * L⌋₊ : ℕ) : ℝ) := by
            have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
            have h3 : (0 : ℝ) ≤ 2 * Real.pi * (ℓ ^ (4 * D) / ((q : ℝ) * L)) * ((⌊x⌋₊ - ⌊x - 2 * L⌋₊ : ℕ) : ℝ) :=
              mul_nonneg (mul_nonneg h2π hwid) hblk0
            linarith
          exact mul_nonneg (mul_nonneg (by norm_num) hwid)
            (mul_nonneg (mul_nonneg (Real.sqrt_nonneg q) (mul_nonneg hone hM0)) hV0)
        exact mul_le_mul_of_nonneg_right hc1 hWnn
    _ ≤ ∑ q ∈ Finset.Icc 1 ⌊ℓ ^ (2 * D)⌋₊, 14 * Real.pi * |C₁| * ℓ ^ (-A - 2 * D) * V := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
        have hqD : (q : ℝ) ≤ ℓ ^ (2 * D) := le_trans (by exact_mod_cast hqQ) hQle
        exact arc_term_absorb561 ℓ L M V q D A C₁ ((⌊x⌋₊ - ⌊x - 2 * L⌋₊ : ℕ) : ℝ) hq1 hℓ1 hD0 hL0 hqD hblk
          (Nat.cast_nonneg _) hM0 hMdef hV0
    _ = ((⌊ℓ ^ (2 * D)⌋₊ : ℕ) : ℝ) * (14 * Real.pi * |C₁| * ℓ ^ (-A - 2 * D) * V) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
    _ ≤ ℓ ^ (2 * D) * (14 * Real.pi * |C₁| * ℓ ^ (-A - 2 * D) * V) := by
        refine mul_le_mul_of_nonneg_right hQle ?_
        have h1 : (0 : ℝ) ≤ 14 * Real.pi * |C₁| := by
          have h2 := abs_nonneg C₁
          nlinarith [Real.pi_pos]
        have h2 : (0 : ℝ) ≤ ℓ ^ (-A - 2 * D) := Real.rpow_nonneg hℓ0.le _
        exact mul_nonneg (mul_nonneg h1 h2) hV0
    _ = 14 * Real.pi * |C₁| * ℓ ^ (-A) * V := by
        have hkk : ℓ ^ (2 * D) * ℓ ^ (-A - 2 * D) = ℓ ^ (-A) := by
          rw [← Real.rpow_add hℓ0, show 2 * D + (-A - 2 * D) = -A by ring]
        calc ℓ ^ (2 * D) * (14 * Real.pi * |C₁| * ℓ ^ (-A - 2 * D) * V)
            = 14 * Real.pi * |C₁| * (ℓ ^ (2 * D) * ℓ ^ (-A - 2 * D)) * V := by ring
          _ = 14 * Real.pi * |C₁| * ℓ ^ (-A) * V := by rw [hkk]
    _ ≤ max (14 * Real.pi * |C₁|)
          (max (max (max (max Xd Xo) (max Xr Xt)) 2) C₁) * Real.log x ^ (-A) *
          ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
        have hgoal : max (14 * Real.pi * |C₁|)
              (max (max (max (max Xd Xo) (max Xr Xt)) 2) C₁) * Real.log x ^ (-A) *
              ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖
            = max (14 * Real.pi * |C₁|)
              (max (max (max (max Xd Xo) (max Xr Xt)) 2) C₁) * ℓ ^ (-A) * V := by
          rw [hℓdef, hVdef]
        rw [hgoal]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCge ?_) hV0
        rw [hℓdef]; positivity

/-- LEAF. Threshold step. For small enough ε the long interval length is at least one,
the logarithm of x exceeds one, and the frequency height is at least one, from some
point onwards. This produces the positive ε cut of the conclusion. -/
theorem leaf_long_length_bounds561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      1 ≤ length512 ε x ∧ 1 < Real.log x ∧
        1 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
  refine ⟨1, one_pos, fun ε hε _ => ⟨Real.exp 2, fun x hx => ?_⟩⟩
  have hexp : (1 : ℝ) ≤ Real.exp 2 := by
    have h := Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hx1 : (1 : ℝ) ≤ x := le_trans hexp hx
  have hxexp : Real.exp 2 ≤ x := hx
  have hlog : 1 < Real.log x := by
    have h1 : Real.log (Real.exp 2) ≤ Real.log x :=
      Real.log_le_log (Real.exp_pos 2) hxexp
    rw [Real.log_exp] at h1
    linarith
  refine ⟨?_, hlog, ?_⟩
  · unfold length512
    exact Real.one_le_rpow hx1 (by positivity)
  · exact Real.one_le_rpow hx1 (by positivity)

/-- The long coefficient replacement step, assembled from the frequency count, the
short block mass, the replacement at a single frequency and the elementary thresholds.
CONDITIONAL ON those four separate inputs. -/
theorem leaf_long_coefficient561_split :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (a b : ℝ → ℕ → ℂ) (u : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
          ‖∑ k ∈ (I x).filter (fun k : ℕ => (k : ℝ) ≤ t),
            (a x k * χ (k : ZMod q) - delta χ * u / Real.log x)‖ ≤ C * Y x * Real.log x ^ (-A)) →
      (∃ C : ℝ, ∀ x k, ‖a x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B ∧
        ‖b x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
        Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0) →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          longReplacementError561 ε D x (a x) (b x) u ≤ C * scale512 ε A x := by
  intro B
  obtain ⟨εp, hεp, hpre⟩ := leaf_long_prefix_replacement561
  obtain ⟨εl, hεl, hlen⟩ := leaf_long_length_bounds561
  refine ⟨min εp εl, lt_min hεp hεl, ?_⟩
  intro ε hε hεlt a b u
  dsimp only
  intro hdist hcoef hrough A hA
  obtain ⟨C₀, hC₀⟩ := hcoef
  obtain ⟨K, M, hK, hM, hmass⟩ := leaf_long_short_mass561 B C₀
  obtain ⟨Kc, hcard⟩ := leaf_long_frequency_card561 ε hε
  obtain ⟨Xlen, hXlen⟩ := hlen ε hε (lt_of_lt_of_le hεlt (min_le_right _ _))
  obtain ⟨Xmass, hXmass⟩ := hmass ε hε
  obtain ⟨Dp, hDp⟩ :=
    hpre ε hε (lt_of_lt_of_le hεlt (min_le_left _ _)) a b u hdist hrough
      (A + 14 + M) (by linarith)
  refine ⟨Dp, fun D hD => ?_⟩
  obtain ⟨Cpre, hCpre⟩ := hDp D hD
  refine ⟨max (max (max Kc Xmass) (max Cpre (max Xlen 3))) (2 * (|Cpre| * K) ^ 2 + 1), fun x hx => ?_⟩
  have hthr : max (max Kc Xmass) (max Cpre (max Xlen 3)) ≤
      max (max (max Kc Xmass) (max Cpre (max Xlen 3))) (2 * (|Cpre| * K) ^ 2 + 1) :=
    le_max_left _ _
  have hxKc : Kc ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans hthr hx))
  have hxXm : Xmass ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans hthr hx))
  have hxCp : Cpre ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans hthr hx))
  have hxXl : Xlen ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_trans (le_max_right _ _) (le_trans hthr hx))
  have hx3 : (3 : ℝ) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_max_right _ _) (le_trans hthr hx))
  obtain ⟨hL1, hlog1, hH1⟩ := hXlen x hxXl
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log x := by linarith
  have hlogpos : (0 : ℝ) < Real.log x := by linarith
  have hL0 : (0 : ℝ) ≤ length512 ε x := le_trans zero_le_one hL1
  have hH0 : (0 : ℝ) ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
    le_trans zero_le_one hH1
  have hmassx : ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ ≤
      K * length512 ε x * Real.log x ^ M :=
    hXmass x hxXm (fun k => b x k) (fun k => (hC₀ x k).2)
  have hmass0 : (0 : ℝ) ≤ ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ :=
    Finset.sum_nonneg (fun m _ => norm_nonneg _)
  have hsplit : Real.log x ^ (-(A + 14 + M)) * Real.log x ^ M = Real.log x ^ (-A - 14) := by
    rw [← Real.rpow_add hlogpos, show -(A + 14 + M) + M = -A - 14 by ring]
  have hper : ∀ N ∈ frequencies512 ε x,
      ‖(∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) -
          longPrincipal561 ε D x (b x) u N‖ ≤
        (|Cpre| * K) * length512 ε x * Real.log x ^ (-A - 14) := by
    intro N hN
    have h1 := hCpre x hxCp N hN
    have hlogA : (0 : ℝ) ≤ Real.log x ^ (-(A + 14 + M)) := Real.rpow_nonneg hlog0 _
    have habs : (0 : ℝ) ≤ |Cpre| * Real.log x ^ (-(A + 14 + M)) :=
      mul_nonneg (abs_nonneg _) hlogA
    calc ‖(∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) -
          longPrincipal561 ε D x (b x) u N‖
        ≤ Cpre * Real.log x ^ (-(A + 14 + M)) *
            ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := h1
      _ ≤ |Cpre| * Real.log x ^ (-(A + 14 + M)) *
            ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self Cpre) hlogA) hmass0
      _ ≤ |Cpre| * Real.log x ^ (-(A + 14 + M)) *
            (K * length512 ε x * Real.log x ^ M) :=
          mul_le_mul_of_nonneg_left hmassx habs
      _ = (|Cpre| * K) * length512 ε x *
            (Real.log x ^ (-(A + 14 + M)) * Real.log x ^ M) := by ring
      _ = (|Cpre| * K) * length512 ε x * Real.log x ^ (-A - 14) := by rw [hsplit]
  have hsq : ∀ N ∈ frequencies512 ε x,
      ‖(∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) -
          longPrincipal561 ε D x (b x) u N‖ ^ 2 ≤
        ((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) := by
    intro N hN
    have h1 := hper N hN
    have hq0 : (0 : ℝ) ≤ Real.log x ^ (-A - 14) := Real.rpow_nonneg hlog0 _
    have hq1 : Real.log x ^ (-A - 14) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hbase : (0 : ℝ) ≤ (|Cpre| * K) ^ 2 * length512 ε x ^ 2 := by positivity
    calc ‖(∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) -
          longPrincipal561 ε D x (b x) u N‖ ^ 2
        ≤ ((|Cpre| * K) * length512 ε x * Real.log x ^ (-A - 14)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * (Real.log x ^ (-A - 14)) ^ 2 := by ring
      _ ≤ ((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) := by
          apply mul_le_mul_of_nonneg_left _ hbase
          nlinarith [hq0, hq1]
  have hconst : ∑ _N ∈ frequencies512 ε x,
        ((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) =
      ((frequencies512 ε x).card : ℝ) *
        (((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard0 : (0 : ℝ) ≤ ((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) := by
    positivity
  have hscale0 : (0 : ℝ) ≤ scale512 ε A x := by
    unfold scale512
    positivity
  have hcoefge : 2 * (|Cpre| * K) ^ 2 ≤
      max (max (max Kc Xmass) (max Cpre (max Xlen 3))) (2 * (|Cpre| * K) ^ 2 + 1) :=
    le_trans (by linarith) (le_max_right _ _)
  have hle : Real.log x ^ (-A - 14) ≤ Real.log x ^ (-A - 7) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  unfold longReplacementError561
  refine le_trans (Finset.sum_le_sum hsq) ?_
  rw [hconst]
  calc ((frequencies512 ε x).card : ℝ) *
        (((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14))
      ≤ (2 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) *
          (((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14)) :=
        mul_le_mul_of_nonneg_right (hcard x hxKc) hcard0
    _ = (2 * (|Cpre| * K) ^ 2) *
          (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
            length512 ε x ^ 2 * Real.log x ^ (-A - 14)) := by ring
    _ ≤ (2 * (|Cpre| * K) ^ 2) *
          (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
            length512 ε x ^ 2 * Real.log x ^ (-A - 7)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
              length512 ε x ^ 2 * Real.log x ^ (-A - 14)
            = (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
                length512 ε x ^ 2) * Real.log x ^ (-A - 14) := by ring
          _ ≤ (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
                length512 ε x ^ 2) * Real.log x ^ (-A - 7) :=
              mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (2 * (|Cpre| * K) ^ 2) * scale512 ε A x := by
        unfold scale512
        ring
    _ ≤ max (max (max Kc Xmass) (max Cpre (max Xlen 3))) (2 * (|Cpre| * K) ^ 2 + 1) *
          scale512 ε A x :=
        mul_le_mul_of_nonneg_right hcoefge hscale0

end LeanLab.BHP1997.Decomp561n
