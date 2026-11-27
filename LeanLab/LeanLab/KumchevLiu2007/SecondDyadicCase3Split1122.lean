/-
BURST 2026-11-22, session S81, burst-20261122. SPLIT of the leaf
Split1122SecondDyadicBlock.case3_large_D, Case 3 of the proof of Lemma 3.4 of
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 12, applied on page 15 to the
second sum of display 52 in window form, t in [Y/4, Y] with the squareWindow Y
filter on m. Same cut at t = Y - 2H as SecondDyadicCases1122 for Cases 1 and 2,
for the same reason: the edge stretch needs a divisor moment bound the paper
does not state. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Split1122SecondDyadicBlock

namespace LeanLab.KumchevLiu2007.SecondDyadicCase3Split1122

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

private lemma divisors_card_le_two (b : ℝ) (hb : 0 ≤ b) (m : ℕ) (hm : (m : ℝ) ≤ b) :
    m.divisors.card ≤
      2 * ((Finset.Icc 1 (⌊Real.sqrt b⌋₊ + 1)).filter (fun d => d ∣ m)).card := by
  set K : ℕ := ⌊Real.sqrt b⌋₊ + 1 with hKdef
  have hK0 : 0 < K := Nat.succ_pos _
  have hbK : (m : ℝ) < (K : ℝ) ^ 2 := by
    have hsqrt : Real.sqrt b < (K : ℝ) := by
      have h := Nat.lt_floor_add_one (Real.sqrt b)
      rw [hKdef]; push_cast; linarith
    have hs0 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
    have hb2 : b = (Real.sqrt b) ^ 2 := (Real.sq_sqrt hb).symm
    nlinarith
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · simp [hm0]
  · set S := (Finset.Icc 1 K).filter (fun d => d ∣ m) with hS
    have hcard : m.divisors.card =
        (m.divisors.filter (fun d => d ≤ K)).card +
          (m.divisors.filter (fun d => ¬ d ≤ K)).card := by
      have h := Finset.card_filter_add_card_filter_not (s := m.divisors) (p := fun d => d ≤ K)
      omega
    have hT : (m.divisors.filter (fun d => d ≤ K)).card ≤ S.card := by
      apply Finset.card_le_card
      intro d hd
      obtain ⟨hdD, hdK⟩ := Finset.mem_filter.mp hd
      have hdm : d ∣ m := (Nat.mem_divisors.mp hdD).1
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdm hm0
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, hdK⟩, hdm⟩
    have hU : (m.divisors.filter (fun d => ¬ d ≤ K)).card ≤ S.card := by
      have key : ∀ d ∈ m.divisors.filter (fun d => ¬ d ≤ K),
          m / d ∈ S ∧ ∀ d2 ∈ m.divisors.filter (fun d => ¬ d ≤ K), m / d = m / d2 → d = d2 := by
        intro d hd
        obtain ⟨hdD, hdK⟩ := Finset.mem_filter.mp hd
        have hdm : d ∣ m := (Nat.mem_divisors.mp hdD).1
        have hdK' : K < d := by omega
        have hd0 : 0 < d := lt_trans hK0 hdK'
        have hmul : d * (m / d) = m := Nat.mul_div_cancel' hdm
        have he1 : 1 ≤ m / d := by
          rcases Nat.eq_zero_or_pos (m / d) with h | h
          · rw [h, mul_zero] at hmul; omega
          · exact h
        have hstep : (K + 1) * (m / d) ≤ m := by
          calc (K + 1) * (m / d) ≤ d * (m / d) := Nat.mul_le_mul_right _ (by omega)
            _ = m := hmul
        have hlt : (K + 1) * (m / d) < K * K := by
          have hcast : (((K + 1) * (m / d) : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hstep
          have hltR : (((K + 1) * (m / d) : ℕ) : ℝ) < (K : ℝ) ^ 2 := lt_of_le_of_lt hcast hbK
          have hcast2 : (((K * K : ℕ)) : ℝ) = (K : ℝ) ^ 2 := by push_cast; ring
          have hRR : (((K + 1) * (m / d) : ℕ) : ℝ) < ((K * K : ℕ) : ℝ) := by
            rw [hcast2]; exact hltR
          exact_mod_cast hRR
        have heK : m / d ≤ K := by
          by_contra hcon
          push_neg at hcon
          have h1 : K * (K + 1) ≤ (K + 1) * (m / d) := by
            rw [mul_comm K (K + 1)]
            exact Nat.mul_le_mul_left _ (le_of_lt hcon)
          have h2 : K * (K + 1) ≤ K * K := le_trans h1 (le_of_lt hlt)
          have h3 := Nat.le_of_mul_le_mul_left h2 hK0
          omega
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨he1, heK⟩,
          Nat.div_dvd_of_dvd hdm⟩, ?_⟩
        intro d2 hd2 heq
        obtain ⟨hd2D, _⟩ := Finset.mem_filter.mp hd2
        have h2 : d2 ∣ m := (Nat.mem_divisors.mp hd2D).1
        have hmul2 : d2 * (m / d2) = m := Nat.mul_div_cancel' h2
        have he : d * (m / d) = d2 * (m / d2) := by rw [hmul, hmul2]
        rw [heq] at he
        exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < m / d2) he
      exact Finset.card_le_card_of_injOn (fun d => m / d)
        (fun d hd => (key d hd).1) (fun d1 hd1 d2 hd2 he => (key d1 hd1).2 d2 hd2 he)
    omega

private lemma card_multiples_le (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (d : ℕ) (hd : 1 ≤ d) :
    ((((Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun m => d ∣ m)).card : ℕ) : ℝ) ≤ (b - a) / d + 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hb0 : 0 ≤ b := ha.trans hab
  set S := (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun m => d ∣ m) with hS
  have hmem : ∀ m ∈ S, m / d ∈ Finset.Ioc ⌊a / d⌋₊ ⌊b / d⌋₊ := by
    intro m hm
    obtain ⟨hmJ, hdm⟩ := Finset.mem_filter.mp hm
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hmJ
    have hm1 : ⌊a⌋₊ + 1 ≤ m := h1
    have ha_lt : a < (m : ℝ) := by
      have h2' : ((⌊a⌋₊ : ℝ) + 1) ≤ (m : ℝ) := by
        have h3 : ((⌊a⌋₊ + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
        push_cast at h3; linarith
      have h4 : a < ((⌊a⌋₊ : ℝ) + 1) := Nat.lt_floor_add_one a
      linarith
    have hmb : (m : ℝ) ≤ b := le_trans (by exact_mod_cast h2) (Nat.floor_le hb0)
    have hcast : ((m / d : ℕ) : ℝ) = (m : ℝ) / d := Nat.cast_div hdm (by positivity)
    have hlt : a / d < ((m / d : ℕ) : ℝ) := by
      rw [hcast, div_lt_div_iff_of_pos_right hd0]; exact ha_lt
    have hle : ((m / d : ℕ) : ℝ) ≤ b / d := by
      rw [hcast, div_le_div_iff_of_pos_right hd0]; exact hmb
    refine Finset.mem_Ioc.mpr ⟨?_, ?_⟩
    · exact (Nat.floor_lt (div_nonneg ha hd0.le)).mpr hlt
    · exact Nat.le_floor hle
  have hinj : ∀ m1 ∈ S, ∀ m2 ∈ S, m1 / d = m2 / d → m1 = m2 := by
    intro m1 hm1 m2 hm2 he
    have h1 : d ∣ m1 := (Finset.mem_filter.mp hm1).2
    have h2 : d ∣ m2 := (Finset.mem_filter.mp hm2).2
    have e1 : d * (m1 / d) = m1 := Nat.mul_div_cancel' h1
    have e2 : d * (m2 / d) = m2 := Nat.mul_div_cancel' h2
    rw [← e1, ← e2, he]
  have hcard : ((S.card : ℕ) : ℝ) ≤ ((⌊b / d⌋₊ - ⌊a / d⌋₊ : ℕ) : ℝ) := by
    have h := Finset.card_le_card_of_injOn (fun m => m / d) hmem hinj
    rw [Nat.card_Ioc] at h
    exact_mod_cast h
  have hmono : ⌊a / d⌋₊ ≤ ⌊b / d⌋₊ := Nat.floor_le_floor (by rw [div_le_div_iff_of_pos_right hd0]; linarith)
  have hb1 : ((⌊b / d⌋₊ : ℕ) : ℝ) ≤ b / d := Nat.floor_le (div_nonneg hb0 hd0.le)
  have ha1 : a / d < ((⌊a / d⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcast2 : ((⌊b / d⌋₊ - ⌊a / d⌋₊ : ℕ) : ℝ) =
      ((⌊b / d⌋₊ : ℕ) : ℝ) - ((⌊a / d⌋₊ : ℕ) : ℝ) := by
    rw [Nat.cast_sub hmono]
  have hkey : (b - a) / d = b / d - a / d := by ring
  rw [hcast2] at hcard
  rw [hkey]
  linarith

set_option maxHeartbeats 800000 in
private lemma tau_interval_le (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (m.divisors.card : ℝ)) ≤
      2 * ((b - a) * (1 + Real.log ((⌊Real.sqrt b⌋₊ + 1 : ℕ) : ℝ)) +
        ((⌊Real.sqrt b⌋₊ + 1 : ℕ) : ℝ)) := by
  set K : ℕ := ⌊Real.sqrt b⌋₊ + 1 with hKdef
  have hb0 : 0 ≤ b := ha.trans hab
  set J : Finset ℕ := Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with hJdef
  have stepA : (∑ m ∈ J, (m.divisors.card : ℝ)) ≤
      ∑ m ∈ J, 2 * ((((Finset.Icc 1 K).filter (fun x => x ∣ m)).card : ℕ) : ℝ) := by
    refine Finset.sum_le_sum (fun m hm => ?_)
    have hmle : (m : ℝ) ≤ b := by
      have h := (Finset.mem_Ioc.mp hm).2
      exact le_trans (by exact_mod_cast h) (Nat.floor_le hb0)
    exact_mod_cast divisors_card_le_two b hb0 m hmle
  have stepB : (∑ m ∈ J, (((Finset.Icc 1 K).filter (fun x => x ∣ m)).card : ℝ)) =
      ∑ x ∈ Finset.Icc 1 K, (((J.filter (fun m => x ∣ m)).card : ℕ) : ℝ) := by
    rw [Finset.sum_congr rfl
      (fun m _ => Finset.natCast_card_filter (fun x => x ∣ m) (Finset.Icc 1 K))]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun x _ => Finset.sum_boole (fun m => x ∣ m) J)
  have stepC : (∑ x ∈ Finset.Icc 1 K, (((J.filter (fun m => x ∣ m)).card : ℕ) : ℝ)) ≤
      ∑ x ∈ Finset.Icc 1 K, ((b - a) / x + 1) := by
    refine Finset.sum_le_sum (fun x hx => ?_)
    exact card_multiples_le a b ha hab x (Finset.mem_Icc.mp hx).1
  have hharm : ((harmonic K : ℚ) : ℝ) = ∑ x ∈ Finset.Icc 1 K, ((x : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_congr rfl (fun x _ => by simp)
  have stepD : (∑ x ∈ Finset.Icc 1 K, ((b - a) / x + 1)) =
      (b - a) * ((harmonic K : ℚ) : ℝ) + K := by
    have h1 : (∑ x ∈ Finset.Icc 1 K, ((b - a) / x + 1)) =
        (b - a) * (∑ x ∈ Finset.Icc 1 K, ((x : ℝ))⁻¹) + K := by
      simp only [div_eq_mul_inv, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
        Nat.card_Icc, Nat.add_sub_cancel]
      norm_num
    rw [h1, hharm]
  have stepE : ((harmonic K : ℚ) : ℝ) ≤ 1 + Real.log ((K : ℕ) : ℝ) := harmonic_le_one_add_log K
  have hbKa : (0 : ℝ) ≤ b - a := by linarith
  calc (∑ m ∈ J, (m.divisors.card : ℝ))
      ≤ ∑ m ∈ J, 2 * ((((Finset.Icc 1 K).filter (fun x => x ∣ m)).card : ℕ) : ℝ) := stepA
    _ = 2 * (∑ x ∈ Finset.Icc 1 K, (((J.filter (fun m => x ∣ m)).card : ℕ) : ℝ)) := by
        rw [← Finset.mul_sum, stepB]
    _ ≤ 2 * (∑ x ∈ Finset.Icc 1 K, ((b - a) / x + 1)) := by
        have := stepC
        linarith
    _ ≤ 2 * ((b - a) * (1 + Real.log ((K : ℕ) : ℝ)) + K) := by
        rw [stepD]
        have h1 : (b - a) * ((harmonic K : ℚ) : ℝ) + K ≤
            (b - a) * (1 + Real.log ((K : ℕ) : ℝ)) + K := by
          have := mul_le_mul_of_nonneg_left stepE hbKa
          linarith
        linarith

/-- The real length of the interval of squares on the edge stretch. -/
private lemma sqrt_diff_le (Y t H : ℝ) (hY : 0 < Y) (ht : Y / 2 ≤ t) (hH : 0 ≤ H) :
    Real.sqrt (t + H) - Real.sqrt t ≤ H / Real.sqrt Y := by
  have ht0 : 0 < t := lt_of_lt_of_le (by linarith) ht
  have hsum0 : 0 < Real.sqrt (t + H) + Real.sqrt t := by
    have h1 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have h2 : 0 ≤ Real.sqrt (t + H) := Real.sqrt_nonneg _
    linarith
  have hkey : Real.sqrt (t + H) - Real.sqrt t = H / (Real.sqrt (t + H) + Real.sqrt t) := by
    rw [eq_div_iff (ne_of_gt hsum0)]
    nlinarith [Real.mul_self_sqrt ht0.le, Real.mul_self_sqrt (by linarith : (0:ℝ) ≤ t + H)]
  rw [hkey]
  refine div_le_div_of_nonneg_left hH (Real.sqrt_pos.mpr hY) ?_
  have h3 : Real.sqrt (t + H) ≥ Real.sqrt t := Real.sqrt_le_sqrt (by linarith)
  have h4 : Real.sqrt Y ≤ Real.sqrt 2 * Real.sqrt t := by
    have h4a : Real.sqrt Y ≤ Real.sqrt (2 * t) := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_mul (by norm_num)] at h4a
  have h5 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  nlinarith [Real.sqrt_nonneg t]

set_option maxHeartbeats 1600000 in
private theorem tau_edge_sum_aux (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ t : ℝ, windowY X ε - 2 * H ≤ t → t ≤ windowY X ε →
        (∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (m.divisors.card : ℝ)) ^ 2 ≤ C * H / Real.log X ^ A := by
  have hB0 : 0 < A / 4 + 2 := by linarith
  refine ⟨A / 4 + 2, hB0, fun B hB ε hε hε' => ?_⟩
  have h4B : A + 8 ≤ 4 * B := by nlinarith
  have h4B' : A + 4 ≤ 4 * B := by nlinarith
  have hδ1 : 0 < 7 / 72 + 3 * ε / 4 := by linarith
  have hδ2 : 0 < 7 / 18 + ε := by linarith
  have e1 : ∀ᶠ X : ℝ in Filter.atTop, 8 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually_ge_atTop 8
  have e2 : ∀ᶠ X : ℝ in Filter.atTop, (2 : ℝ) ≤ X := Filter.eventually_ge_atTop 2
  have e3 : ∀ᶠ X : ℝ in Filter.atTop,
      Real.log X ^ (A + 4 * B) ≤ (1 / 128) * X ^ (7 / 72 + 3 * ε / 4) := by
    have h := (isLittleO_log_rpow_rpow_atTop (A + 4 * B) hδ1).bound
      (by norm_num : (0:ℝ) < 1 / 128)
    filter_upwards [h, e2] with X hX hX2
    have hL0 : (0:ℝ) ≤ Real.log X := Real.log_nonneg (by linarith)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hL0 _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ X) _)] at hX
    simpa using hX
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (e1.and (e2.and e3))
  refine ⟨4, max N 8, by norm_num, le_trans (by norm_num : (2:ℝ) ≤ 8) (le_max_right N 8),
    fun X H hX hlo hhi t ht1 ht2 => ?_⟩
  obtain ⟨hL8, hX2, hgrowth⟩ := hN X ((le_max_left _ _).trans hX)
  set L : ℝ := Real.log X with hLdef
  set P : ℝ := L ^ B with hPdef
  set Y : ℝ := windowY X ε with hYdef
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hLsq : 32 ≤ L ^ 2 := by nlinarith
  have hB0' : 0 < B := by linarith
  have hP0 : 0 < P := Real.rpow_pos_of_pos hLpos B
  have hP4 : P ^ 4 = L ^ (4 * B) := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num; ring_nf
  have hzpow : P ^ (-4 : ℤ) = (P ^ 4)⁻¹ := by rw [zpow_neg]; norm_cast
  rw [hzpow] at hlo hhi
  have hP4pos : 0 < P ^ 4 := by positivity
  have hlo' : X ^ (7 / 18 + ε) ≤ H * P ^ 4 := by
    rw [← div_le_iff₀ hP4pos]; simpa [div_eq_mul_inv] using hlo
  have hhi' : H * P ^ 4 ≤ Y := by
    rw [← le_div_iff₀ hP4pos]; simpa [div_eq_mul_inv] using hhi
  have hYeq : Y = X ^ (7 / 12 + ε / 2) := rfl
  have hY0 : 0 < Y := by
    rw [hYeq]; exact Real.rpow_pos_of_pos hX0 _
  have hY1 : 1 ≤ Y := by
    rw [hYeq]; exact Real.one_le_rpow (by linarith) (by linarith)
  have hYX : Y ≤ X := by
    rw [hYeq]
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ X)
      (show 7 / 12 + ε / 2 ≤ (1:ℝ) by linarith)
    rwa [Real.rpow_one] at h
  have hP4ge : 4 ≤ P ^ 4 := by
    rw [hP4]
    have h1 : (1:ℝ) ≤ 4 * B := by linarith
    have h2 : (4:ℝ) ≤ L := by linarith
    calc (4:ℝ) ≤ L := h2
      _ = L ^ (1:ℝ) := (Real.rpow_one L).symm
      _ ≤ L ^ (4 * B) := Real.rpow_le_rpow_of_exponent_le hL1 h1
  have hH0 : 0 < H := by
    have h1 : 0 < X ^ (7 / 18 + ε) := Real.rpow_pos_of_pos hX0 _
    nlinarith
  have hHH : 4 * H ≤ Y := by
    have h1 : 4 * H ≤ P ^ 4 * H := mul_le_mul_of_nonneg_right hP4ge hH0.le
    have h2 : P ^ 4 * H ≤ Y := by rw [mul_comm]; exact hhi'
    linarith
  have hH4 : 2 * H ≤ Y / 2 := by linarith
  have ht_half : Y / 2 ≤ t := by linarith
  have htH : t + H ≤ 2 * Y := by linarith
  have hYlog : Real.log Y = (7 / 12 + ε / 2) * L := by
    rw [hYeq, Real.log_rpow hX0]
  -- the block cutoff of the divisor sum
  set Kr : ℕ := ⌊Real.sqrt (Real.sqrt (t + H))⌋₊ + 1 with hKrdef
  have hKr4 : (Kr : ℝ) ≤ 4 * Y ^ (1 / 4 : ℝ) := by
    have h2 : Real.sqrt (Real.sqrt (t + H)) = (t + H) ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith : (0:ℝ) ≤ t + H)]
      norm_num
    have h1 : ((⌊Real.sqrt (Real.sqrt (t + H))⌋₊ : ℕ) : ℝ) ≤ (t + H) ^ (1 / 4 : ℝ) := by
      have h := Nat.floor_le (Real.sqrt_nonneg (Real.sqrt (t + H)))
      calc ((⌊Real.sqrt (Real.sqrt (t + H))⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (Real.sqrt (t + H)) := h
        _ = (t + H) ^ (1 / 4 : ℝ) := h2
    have hKreq : ((Kr : ℕ) : ℝ) = ((⌊Real.sqrt (Real.sqrt (t + H))⌋₊ : ℕ) : ℝ) + 1 := by
      simp [hKrdef]
    have h3 : (t + H) ^ (1 / 4 : ℝ) ≤ (2 * Y) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by linarith) htH (by norm_num)
    have h4 : (2 * Y) ^ (1 / 4 : ℝ) = (2 : ℝ) ^ (1 / 4 : ℝ) * Y ^ (1 / 4 : ℝ) :=
      Real.mul_rpow (by norm_num) hY0.le
    have h5 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      have h6 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      rwa [Real.rpow_one] at h6
    have h6 : (1 : ℝ) ≤ Y ^ (1 / 4 : ℝ) := Real.one_le_rpow hY1 (by norm_num)
    have h7 : (0:ℝ) ≤ Y ^ (1 / 4 : ℝ) := Real.rpow_nonneg hY0.le _
    rw [hKreq]
    nlinarith
  have hlogKr : Real.log (Kr : ℝ) ≤ L := by
    have h1 : Real.log (Kr : ℝ) ≤ Real.log (4 * Y ^ (1 / 4 : ℝ)) :=
      Real.log_le_log (by positivity) hKr4
    have h2 : Real.log (4 * Y ^ (1 / 4 : ℝ)) = Real.log 4 + (1 / 4 : ℝ) * Real.log Y := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hY0 _)), Real.log_rpow hY0]
    have h3 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4); linarith
    rw [h2, hYlog] at h1
    nlinarith
  -- the sum
  set S : ℝ := ∑ m ∈ (squareWindow Y).filter
      (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), (m.divisors.card : ℝ) with hSdef
  have hsub : (squareWindow Y).filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H) ⊆
      Finset.Ioc ⌊Real.sqrt t⌋₊ ⌊Real.sqrt (t + H)⌋₊ := by
    intro m hm
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hlt : Real.sqrt t < (m : ℝ) := by
      have h := Real.sqrt_lt_sqrt (show (0:ℝ) ≤ t by linarith) h1
      rwa [Real.sqrt_sq hm0] at h
    have hle : (m : ℝ) ≤ Real.sqrt (t + H) := Real.le_sqrt_of_sq_le h2
    refine Finset.mem_Ioc.mpr ⟨?_, ?_⟩
    · exact (Nat.floor_lt (show (0:ℝ) ≤ Real.sqrt t by positivity)).mpr hlt
    · exact Nat.le_floor hle
  have hstep1 : S ≤ ∑ m ∈ Finset.Ioc ⌊Real.sqrt t⌋₊ ⌊Real.sqrt (t + H)⌋₊,
      (m.divisors.card : ℝ) := by
    rw [hSdef]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
  have hstep2 := tau_interval_le (Real.sqrt t) (Real.sqrt (t + H))
    (Real.sqrt_nonneg t) (Real.sqrt_le_sqrt (by linarith))
  have hlen := sqrt_diff_le Y t H hY0 ht_half hH0.le
  have hS : S ≤ 4 * (H / Real.sqrt Y) * L + 8 * Y ^ (1 / 4 : ℝ) := by
    have hl0 : 0 ≤ Real.sqrt (t + H) - Real.sqrt t := by
      have h := Real.sqrt_le_sqrt (show t ≤ t + H by linarith); linarith
    have hp0 : 0 ≤ H / Real.sqrt Y := div_nonneg hH0.le (Real.sqrt_nonneg Y)
    have h1L : 1 + Real.log ((⌊Real.sqrt (Real.sqrt (t + H))⌋₊ + 1 : ℕ) : ℝ) ≤ 1 + L := by
      have := hlogKr; simp only [hKrdef] at this; linarith
    have h2L : 1 + L ≤ 2 * L := by linarith
    have hprod : (Real.sqrt (t + H) - Real.sqrt t) *
        (1 + Real.log ((⌊Real.sqrt (Real.sqrt (t + H))⌋₊ + 1 : ℕ) : ℝ)) ≤
        (H / Real.sqrt Y) * (2 * L) :=
      le_trans (mul_le_mul hlen (le_trans h1L h2L) (by positivity) hp0)
        (le_of_eq (by ring))
    have hk : ((⌊Real.sqrt (Real.sqrt (t + H))⌋₊ + 1 : ℕ) : ℝ) ≤ 4 * Y ^ (1 / 4 : ℝ) := by
      simpa only [hKrdef] using hKr4
    calc S ≤ ∑ m ∈ Finset.Ioc ⌊Real.sqrt t⌋₊ ⌊Real.sqrt (t + H)⌋₊,
          (m.divisors.card : ℝ) := hstep1
      _ ≤ 2 * ((Real.sqrt (t + H) - Real.sqrt t) *
            (1 + Real.log ((⌊Real.sqrt (Real.sqrt (t + H))⌋₊ + 1 : ℕ) : ℝ)) +
            ((⌊Real.sqrt (Real.sqrt (t + H))⌋₊ + 1 : ℕ) : ℝ)) := hstep2
      _ ≤ 4 * (H / Real.sqrt Y) * L + 8 * Y ^ (1 / 4 : ℝ) := by linarith
  have hsq : S ^ 2 ≤ 2 * ((4 * (H / Real.sqrt Y) * L) ^ 2 + (8 * Y ^ (1 / 4 : ℝ)) ^ 2) := by
    have hS0 : 0 ≤ S := by
      rw [hSdef]; exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have ha : (0:ℝ) ≤ 4 * (H / Real.sqrt Y) * L := by
      have h1 : (0:ℝ) ≤ H / Real.sqrt Y := div_nonneg hH0.le (Real.sqrt_nonneg Y)
      nlinarith
    have hb : (0:ℝ) ≤ 8 * Y ^ (1 / 4 : ℝ) := by
      have := Real.rpow_nonneg hY0.le (1 / 4 : ℝ); linarith
    have h1 : S * S ≤ (4 * (H / Real.sqrt Y) * L + 8 * Y ^ (1 / 4 : ℝ)) *
        (4 * (H / Real.sqrt Y) * L + 8 * Y ^ (1 / 4 : ℝ)) :=
      mul_le_mul hS hS hS0 (by linarith)
    nlinarith [h1, sq_nonneg (4 * (H / Real.sqrt Y) * L - 8 * Y ^ (1 / 4 : ℝ))]
  have hsqY : (Real.sqrt Y) ^ 2 = Y := Real.sq_sqrt hY0.le
  have hterm1 : (4 * (H / Real.sqrt Y) * L) ^ 2 = 16 * H ^ 2 * L ^ 2 / Y := by
    have h1 : (4 * (H / Real.sqrt Y) * L) ^ 2 = 16 * (H / Real.sqrt Y) ^ 2 * L ^ 2 := by ring
    rw [h1, div_pow, hsqY]
    field_simp
  have hterm2 : (8 * Y ^ (1 / 4 : ℝ)) ^ 2 = 64 * Y ^ (1 / 2 : ℝ) := by
    have h1 : (Y ^ (1 / 4 : ℝ)) ^ 2 = Y ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
      norm_num
    calc (8 * Y ^ (1 / 4 : ℝ)) ^ 2 = 64 * (Y ^ (1 / 4 : ℝ)) ^ 2 := by ring
      _ = 64 * Y ^ (1 / 2 : ℝ) := by rw [h1]
  have hbound1 : 32 * (H ^ 2 * L ^ 2 / Y) ≤ H * L ^ (-A) := by
    have hHY : H * L ^ (4 * B) ≤ Y := by rw [← hP4]; exact hhi'
    have h4Bpos : 0 < L ^ (4 * B) := Real.rpow_pos_of_pos hLpos _
    have hkey : H ^ 2 * L ^ 2 / Y ≤ H * L ^ (2 - 4 * B) := by
      have h1 : H ^ 2 * L ^ 2 / Y = (H / Y) * H * L ^ 2 := by field_simp
      rw [h1]
      have h2 : H / Y ≤ (L ^ (4 * B))⁻¹ := by
        rw [div_le_iff₀ hY0, inv_mul_eq_div, le_div_iff₀ h4Bpos]; linarith
      have h3 : (H / Y) * H * L ^ 2 ≤ (L ^ (4 * B))⁻¹ * H * L ^ 2 := by
        have h := mul_le_mul_of_nonneg_right h2 hH0.le
        nlinarith [sq_nonneg L]
      have h4 : (L ^ (4 * B))⁻¹ * H * L ^ 2 = H * L ^ (2 - 4 * B) := by
        rw [Real.rpow_sub hLpos, Real.rpow_two]
        field_simp
      linarith
    have hfin : 32 * (H * L ^ (2 - 4 * B)) ≤ H * L ^ (-A) := by
      have hLsq2 : (32:ℝ) ≤ Real.rpow L 2 := by
        have hh : Real.rpow L 2 = L ^ 2 := Real.rpow_natCast L 2
        rw [hh]; exact hLsq
      have hexp : (32:ℝ) ≤ L ^ (-A - 2 + 4 * B) :=
        le_trans hLsq2 (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
      have hpos : (0:ℝ) < L ^ (2 - 4 * B) := Real.rpow_pos_of_pos hLpos _
      have hprod2 : 32 * L ^ (2 - 4 * B) ≤ L ^ (-A - 2 + 4 * B) * L ^ (2 - 4 * B) :=
        mul_le_mul_of_nonneg_right hexp hpos.le
      have heq : L ^ (-A - 2 + 4 * B) * L ^ (2 - 4 * B) = L ^ (-A) := by
        rw [← Real.rpow_add hLpos]; ring_nf
      have h32 : 32 * L ^ (2 - 4 * B) ≤ L ^ (-A) := by rw [← heq]; exact hprod2
      calc 32 * (H * L ^ (2 - 4 * B)) = H * (32 * L ^ (2 - 4 * B)) := by ring
        _ ≤ H * L ^ (-A) := mul_le_mul_of_nonneg_left h32 hH0.le
    linarith
  have hbound2 : 128 * Y ^ (1 / 2 : ℝ) ≤ H * L ^ (-A) := by
    have hYs : Y ^ (1 / 2 : ℝ) = X ^ (7 / 24 + ε / 4) := by
      rw [hYeq, ← Real.rpow_mul hX0.le]; ring_nf
    rw [hYs]
    have hXsplit : X ^ (7 / 18 + ε) = X ^ (7 / 24 + ε / 4) * X ^ (7 / 72 + 3 * ε / 4) := by
      rw [← Real.rpow_add hX0]; ring_nf
    have hg : 128 * L ^ (A + 4 * B) ≤ X ^ (7 / 72 + 3 * ε / 4) := by
      have h := hgrowth; nlinarith
    have hXpos : (0:ℝ) < X ^ (7 / 24 + ε / 4) := Real.rpow_pos_of_pos hX0 _
    have hmul : 128 * X ^ (7 / 24 + ε / 4) * L ^ (A + 4 * B) ≤
        X ^ (7 / 24 + ε / 4) * X ^ (7 / 72 + 3 * ε / 4) := by
      calc 128 * X ^ (7 / 24 + ε / 4) * L ^ (A + 4 * B) =
            X ^ (7 / 24 + ε / 4) * (128 * L ^ (A + 4 * B)) := by ring
        _ ≤ X ^ (7 / 24 + ε / 4) * X ^ (7 / 72 + 3 * ε / 4) :=
            mul_le_mul_of_nonneg_left hg hXpos.le
    have hmain : 128 * X ^ (7 / 24 + ε / 4) * L ^ A ≤ H := by
      have hlo'' : X ^ (7 / 18 + ε) ≤ H * L ^ (4 * B) := by
        rw [← hP4]; exact hlo'
      have h1 : 128 * X ^ (7 / 24 + ε / 4) * L ^ (A + 4 * B) ≤ H * L ^ (4 * B) := by
        rw [← hXsplit] at hmul
        exact hmul.trans hlo''
      have h4Bpos : 0 < L ^ (4 * B) := Real.rpow_pos_of_pos hLpos _
      have hh : L ^ A * L ^ (4 * B) = L ^ (A + 4 * B) :=
        (Real.rpow_add hLpos A (4 * B)).symm
      have heq : 128 * X ^ (7 / 24 + ε / 4) * L ^ A * L ^ (4 * B) =
          128 * X ^ (7 / 24 + ε / 4) * L ^ (A + 4 * B) := by
        calc 128 * X ^ (7 / 24 + ε / 4) * L ^ A * L ^ (4 * B) =
              128 * X ^ (7 / 24 + ε / 4) * (L ^ A * L ^ (4 * B)) := by ring
          _ = 128 * X ^ (7 / 24 + ε / 4) * L ^ (A + 4 * B) := by rw [hh]
      have hm : (128 * X ^ (7 / 24 + ε / 4) * L ^ A) * L ^ (4 * B) ≤ H * L ^ (4 * B) := by
        rw [heq]; exact h1
      exact le_of_mul_le_mul_right hm h4Bpos
    have hLA : (0:ℝ) < L ^ A := Real.rpow_pos_of_pos hLpos A
    have hneg : (0:ℝ) < L ^ (-A) := Real.rpow_pos_of_pos hLpos (-A)
    have hstep := mul_le_mul_of_nonneg_right hmain hneg.le
    have heq2 : L ^ A * L ^ (-A) = 1 := by
      rw [← Real.rpow_add hLpos]
      norm_num
    nlinarith [hstep, heq2, hXpos, hneg]
  have hfinal : S ^ 2 ≤ 2 * (H * L ^ (-A)) := by
    rw [hterm1, hterm2] at hsq
    have h1 : 2 * (16 * H ^ 2 * L ^ 2 / Y + 64 * Y ^ (1 / 2 : ℝ)) =
        32 * (H ^ 2 * L ^ 2 / Y) + 128 * Y ^ (1 / 2 : ℝ) := by ring
    rw [h1] at hsq
    linarith [hsq, hbound1, hbound2]
  have key : (4 : ℝ) * H / Real.log X ^ A = 4 * (H * L ^ (-A)) := by
    rw [← hLdef, Real.rpow_neg hL0 A, div_eq_mul_inv]
    ring
  rw [key]
  have hpos : (0:ℝ) < H * L ^ (-A) :=
    mul_pos hH0 (Real.rpow_pos_of_pos hLpos (-A))
  linarith [hfinal, hpos]
/-- PROVED, S154. Three distinct primes at least z dividing m force z^3 at most m, so if
m < Y^(1/2) at most z^3, at most two such primes divide m. -/
private theorem three_primes_le (z Y : ℝ) (hz : Y ^ (1 / 2 : ℝ) ≤ z ^ 3) (hz0 : 0 ≤ z)
    (m : ℕ) (hm : (m : ℝ) < Real.sqrt Y) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ z ≤ (p : ℝ) ∧ p ∣ m) (hm0 : m ≠ 0) : s.card ≤ 2 := by
  by_contra h
  push_neg at h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 h
  obtain ⟨pa, za, da⟩ := hs a ha
  obtain ⟨pb, zb, db⟩ := hs b hb
  obtain ⟨pc, zc, dc⟩ := hs c hc
  have cab : Nat.Coprime a b := (Nat.coprime_primes pa pb).2 hab
  have cac : Nat.Coprime a c := (Nat.coprime_primes pa pc).2 hac
  have cbc : Nat.Coprime b c := (Nat.coprime_primes pb pc).2 hbc
  have hd : a * b * c ∣ m :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_mul_iff_left.2 ⟨cac, cbc⟩)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd cab da db) dc
  have hle : a * b * c ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd
  have hle' : (a : ℝ) * b * c ≤ m := by exact_mod_cast hle
  have h3 : z ^ 3 ≤ (a : ℝ) * b * c := by
    have h1 : z * z ≤ (a : ℝ) * b := mul_le_mul za zb hz0 (by linarith)
    calc z ^ 3 = z * z * z := by ring
      _ ≤ (a : ℝ) * b * c := mul_le_mul h1 zc hz0 (by positivity)
  rw [Real.sqrt_eq_rpow] at hm
  linarith

/-- PROVED, S154. P0088 pages 11 to 12, Lemma 3.4, the size of the coefficient of m in the
short sum. Three primes at least Y^(1/6 + eps/2) multiply to more than Y^(1/2) > m, so at most two
block primes divide m; for each, the Moebius sum over a set of divisors of m/p has modulus
at most the number of divisors of m/p, at most tau of m. -/
private theorem coef_norm_le (X ε B M D : ℝ) (hX : 1 ≤ X) (hε : 0 < ε) (m : ℕ)
    (hm : m ∈ squareWindow (windowY X ε)) :
    ‖∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
        windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
        (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
        p ∣ m)).filter
        (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
      ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
          (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
          (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 2 * (m.divisors.card : ℝ) := by
  set Y := windowY X ε with hYdef
  have hY : 1 ≤ Y := Real.one_le_rpow hX (by linarith)
  have hmw := (Finset.mem_filter.1 hm).2
  have hsq : 0 < Real.sqrt Y := Real.sqrt_pos.2 (by linarith)
  have hm0 : m ≠ 0 := by
    intro h; rw [h] at hmw; simp at hmw; linarith [hmw.1]
  set z := Y ^ (1 / 6 + ε / 2) with hz
  have hz0 : 0 ≤ z := Real.rpow_nonneg (by linarith) _
  have hz3 : Y ^ (1 / 2 : ℝ) ≤ z ^ 3 := by
    rw [hz, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hY (by push_cast; linarith)
  set P := ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧ z ≤ (p : ℝ) ∧
        (p : ℝ) < Y ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧ p ∣ m)).filter
        (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M) with hP
  have hcard : P.card ≤ 2 := by
    refine three_primes_le z Y hz3 hz0 m hmw.2 P (fun p hp => ?_) hm0
    have h := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ p ∈ P, ‖∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime →
      r ∣ d → (r : ℝ) < z)).filter (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ (m.divisors.card : ℝ) := by
    intro p hp
    have hpm : p ∣ m := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2.2.2.2
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime →
        r ∣ d → (r : ℝ) < z)).filter (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
        ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
      intro d _
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsub : ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime →
        r ∣ d → (r : ℝ) < z)).filter (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D) ⊆
        m.divisors :=
      (Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans
        (Nat.divisors_subset_of_dvd hm0 (Nat.div_dvd_of_dvd hpm)))
    exact_mod_cast Finset.card_le_card hsub
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have : (P.card : ℝ) ≤ 2 := by exact_mod_cast hcard
  have h0 : (0 : ℝ) ≤ m.divisors.card := Nat.cast_nonneg _
  nlinarith

/-- PROVED. The integral of the squared short sum over [Y - 2H, Y] is at most
2H times a pointwise bound K on that stretch. -/
private theorem edge_integral_le (S : Finset ℕ) (c : ℕ → ℂ) (Y H K : ℝ) (hH : 0 ≤ H)
    (h : ∀ t : ℝ, Y - 2 * H ≤ t → t ≤ Y →
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2 ≤ K) :
    (∫ t in Y - 2 * H..Y,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2) ≤
      2 * H * K := by
  have hab : Y - 2 * H ≤ Y := by linarith
  calc (∫ t in Y - 2 * H..Y,
        ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2)
      ≤ ∫ _t in Y - 2 * H..Y, K :=
        intervalIntegral.integral_mono_on hab
          (short_sum_sq_intervalIntegrable _ _ _ _ _) intervalIntegrable_const
          (fun t ht => h t ht.1 ht.2)
    _ = 2 * H * K := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- PROVED from coef_norm_le, PROVED, and the LEAF tau_edge_sum of SecondDyadicEdgePoint1123,
S154.
P0088 pages 11 to 12, Lemma 3.4 Cases 1 to 3, the edge stretch
t in [Y - 2H, Y] of the second sum of display 52 in window form.
The pointwise bound of the squared short sum, uniform in alpha, M and D: the
coefficient of m has modulus at most 2 tau of m, the m lie in an interval of
length at most 2H Y^(-1/2) below Y^(1/2), and the elementary hyperbola bound
for the sum of tau over a short interval gives at most a constant times
H^2 Y^(-1) log^2 X plus Y^(1/2), which is at most C H L^(-A) by the H range of
Theorem 1. Not a display of the paper: the paper has no window filter here; the
window filter comes from the window form of display 52. Elementary, no cited
input. -/
private theorem edge_pointwise (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α M D : ℝ, ∀ t : ℝ, windowY X ε - 2 * H ≤ t → t ≤ windowY X ε →
        ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 ≤
            C * H / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := tau_edge_sum_aux A hA
  refine ⟨B0, hB0, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε hε'
  refine ⟨4 * C, X0, by linarith, hX0, ?_⟩
  intro X H hX hlo hhi α M D t ht1 ht2
  have hX1 : 1 ≤ X := by linarith
  have hk := k X H hX hlo hhi t ht1 ht2
  set S := (squareWindow (windowY X ε)).filter
    (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H) with hS
  set T := ∑ m ∈ S, (m.divisors.card : ℝ) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun m _ => Nat.cast_nonneg _
  have hnorm : ‖∑ m ∈ S,
      (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
          windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
          (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
          p ∣ m)).filter
          (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
        ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
            (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
            (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ≤ 2 * T := by
    refine (norm_sum_le _ _).trans ?_
    rw [hT, Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    have hf : ‖fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ = 1 := Circle.norm_coe _
    rw [norm_mul, hf, mul_one]
    exact coef_norm_le X ε B M D hX1 hε m (Finset.mem_filter.1 hm).1
  have hn0 := norm_nonneg (∑ m ∈ S,
      (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
          windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
          (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
          p ∣ m)).filter
          (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
        ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
            (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
            (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)))
  calc _ ≤ (2 * T) ^ 2 := pow_le_pow_left₀ hn0 hnorm 2
    _ = 4 * T ^ 2 := by ring
    _ ≤ 4 * (C * H / Real.log X ^ A) := by linarith [hk]
    _ = 4 * C * H / Real.log X ^ A := by ring

/-- PROVED. H is nonnegative in the H range of Theorem 1. -/
private theorem H_nonneg (X H B ε : ℝ) (hX : 2 ≤ X)
    (hlo : X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H) : 0 ≤ H := by
  have hL : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have h1 : 0 ≤ X ^ (7 / 18 + ε) := Real.rpow_nonneg (by linarith) _
  have h2 : 0 ≤ (Real.log X ^ B) ^ (-4 : ℤ) := zpow_nonneg (Real.rpow_nonneg hL _) _
  exact (mul_nonneg h1 h2).trans hlo

/-- PROVED from edge_pointwise and edge_integral_le. Generic edge bound, for any
real M and D. -/
private theorem edge_all (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α M D : ℝ,
        (∫ t in windowY X ε - 2 * H..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := edge_pointwise A hA
  refine ⟨B0, hB0, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε hε'
  refine ⟨2 * C, X0, by linarith, hX0, ?_⟩
  intro X H hX hlo hhi α M D
  have hH : 0 ≤ H := H_nonneg X H B ε (hX0.trans hX) hlo
  refine (edge_integral_le _ _ _ H _ hH
    (fun t ht1 ht2 => k X H hX hlo hhi α M D t ht1 ht2)).trans (le_of_eq ?_)
  ring

/-- LEAF: P0088 page 12, Case 3 of the proof of Lemma 3.4 on the interior stretch
t in [Y/4, Y - 2H], D above V = H Y^(-1/2) L^(-B). Class HARD. On this stretch the
window filter is no restriction, as in Split1122KLLemma34M1.window_filter_eq, so
it is Case 3 in the general x, y form at x = Y/4 and x = Y/2 with the prime block
coefficient: the factorisation of d at the index s of page 12, the removal of
p' < p, pp'd1d2 in the block D and d1pp' at least V by Lemma 3.3, Kumchev 2006
Lemma 2.7, and Lemma 3.2 in u = mkp'd2, v = pd1. The M = 1 analogue is
Lemma34Case3General1122.case_three_of_leaves. Reduction not yet written. -/
theorem case3_interior (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, H / (Real.sqrt (windowY X ε) * Real.log X ^ B) < D →
        (∫ t in windowY X ε / 4..windowY X ε - 2 * H,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 12, Case 3 of the proof of Lemma 3.4 on the edge stretch
t in [Y - 2H, Y], where the squareWindow Y filter cuts the short sum at m^2 < Y.
Class HARD. Not treated in the paper. As for Cases 1 and 2 in
SecondDyadicCases1122, the trivial bound fails since the coefficient is bounded
only by a power of tau of m; it needs a Shiu type mean bound for tau powers over
the short interval of m near Y^(1/2) of length about H Y^(-1/2), or a smoothing. -/
theorem case3_edge (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, H / (Real.sqrt (windowY X ε) * Real.log X ^ B) < D →
        (∫ t in windowY X ε - 2 * H..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := edge_all A hA
  refine ⟨B0, hB0, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε hε'
  exact ⟨C, X0, hC, hX0, fun X H hX hlo hhi α _ _ _ _ _ _ M _ _ _ D _ =>
    k X H hX hlo hhi α M D⟩

/-- PROVED from case3_interior and case3_edge, CONDITIONAL ON them. The exact
statement of Split1122SecondDyadicBlock.case3_large_D: the integral over [Y/4, Y] is the sum
of the integrals over [Y/4, Y - 2H] and [Y - 2H, Y]. -/
theorem case3_large_D_of_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, H / (Real.sqrt (windowY X ε) * Real.log X ^ B) < D →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := case3_interior A hA
  obtain ⟨B2, hB2, h2⟩ := case3_edge A hA
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε hε'
  refine ⟨C1 + C2, max X1 X2, add_pos hC1 hC2, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hD
  have e1 := k1 X H ((le_max_left _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose
    M hM htop hlow D hD
  have e2 := k2 X H ((le_max_right _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose
    M hM htop hlow D hD
  refine le_of_eq_of_le (intervalIntegral.integral_add_adjacent_intervals
    (b := windowY X ε - 2 * H) ?_ ?_).symm ?_
  · exact short_sum_sq_intervalIntegrable _ _ _ _ _
  · exact short_sum_sq_intervalIntegrable _ _ _ _ _
  · calc _ ≤ C1 * H ^ 2 / Real.log X ^ A + C2 * H ^ 2 / Real.log X ^ A := add_le_add e1 e2
      _ = (C1 + C2) * H ^ 2 / Real.log X ^ A := by ring

/-- PROVED. The assembly has the exact type of the leaf. -/
example : type_of% @Split1122SecondDyadicBlock.case3_large_D := case3_large_D_of_split

end LeanLab.KumchevLiu2007.SecondDyadicCase3Split1122

#print axioms LeanLab.KumchevLiu2007.SecondDyadicCase3Split1122.case3_large_D_of_split
