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
  sorry

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
