/- AI wrote this Lean code for CODEX task410.
Finite corrections for journal Lemma 10 p. 1227.
Goldbach is open. -/
import LeanLab.BS2022GRH.ModelC233
import LeanLab.BS2022GRH.DecompC169c
import LeanLab.BS2022GRH.Verify1565

namespace LeanLab.BS2022GRH.Density410
open Real Finset ChenThresholdGRH
noncomputable section

/-- The complete prime divisor correction, Nathanson Theorem 10.3 p. 277.
Keep the factors from every odd prime divisor, including those above x. -/
theorem full_divisor_correction (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 2 < x)
    (hev : Even n) :
    (∏ p ∈ (Nat.primesBelow ⌈x⌉₊).filter (2 < ·), (1 - 1 / ((p : ℝ) - 1))) *
      UN n * (∏ p ∈ n.primeFactors.filter (fun p : ℕ => x ≤ (p : ℝ)),
        (1 - 1 / ((p : ℝ) - 1))) =
      ∏ p ∈ DecompC169a.primesBelow n x, (1 - 1 / ((p : ℝ) - 1)) := by
  let S := (Nat.primesBelow ⌈x⌉₊).filter (2 < ·)
  let D := n.primeFactors.filter (2 < ·)
  let a : ℕ → ℝ := fun p => 1 - 1 / ((p : ℝ) - 1)
  let b : ℕ → ℝ := fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)
  have hab (p : ℕ) (hp : 2 < p) : a p * b p = 1 := by
    dsimp [a, b]
    have hp' : (2 : ℝ) < p := by exact_mod_cast hp
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp
    <;> ring
  have hsmall : D.filter (fun p : ℕ => (p : ℝ) < x) = S.filter (fun p => p ∣ n) := by
    ext p
    simp only [D, S, mem_filter, Nat.mem_primeFactors, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨⟨hp, hpn, _⟩, hp2⟩, hpx⟩
      exact ⟨⟨⟨(Nat.lt_ceil).mpr hpx, hp⟩, hp2⟩, hpn⟩
    · rintro ⟨⟨⟨hpx, hp⟩, hp2⟩, hpn⟩
      exact ⟨⟨⟨hp, hpn, hn.ne'⟩, hp2⟩, (Nat.lt_ceil).mp hpx⟩
  have hlarge : D.filter (fun p : ℕ => ¬ (p : ℝ) < x) =
      n.primeFactors.filter (fun p : ℕ => x ≤ (p : ℝ)) := by
    ext p
    simp only [D, mem_filter, not_lt]
    constructor
    · rintro ⟨⟨hp, _⟩, hpx⟩
      exact ⟨hp, hpx⟩
    · rintro ⟨hp, hpx⟩
      exact ⟨⟨hp, by exact_mod_cast (hx.trans_le hpx)⟩, hpx⟩
  have heligible : S.filter (fun p => ¬ p ∣ n) = DecompC169a.primesBelow n x := by
    ext p
    simp only [S, DecompC169a.primesBelow, mem_filter, Nat.mem_primesBelow, mem_range]
    constructor
    · rintro ⟨⟨⟨hpceil, hp⟩, _⟩, hpn⟩
      exact ⟨hpceil, hp, hpn, (Nat.lt_ceil).mp hpceil⟩
    · rintro ⟨hpceil, hp, hpn, _⟩
      have hpne : p ≠ 2 := fun h => hpn (h ▸ hev.two_dvd)
      exact ⟨⟨⟨hpceil, hp⟩, by have := hp.two_le; omega⟩, hpn⟩
  have hcancel : (∏ p ∈ D.filter (fun p : ℕ => ¬ (p : ℝ) < x), b p) *
      (∏ p ∈ D.filter (fun p : ℕ => ¬ (p : ℝ) < x), a p) = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro p hp
    rw [mul_comm]
    exact hab p (mem_filter.mp (mem_filter.mp hp).1).2
  have hD : (∏ p ∈ D, b p) *
      (∏ p ∈ n.primeFactors.filter (fun p : ℕ => x ≤ (p : ℝ)), a p) =
      ∏ p ∈ S.filter (fun p => p ∣ n), b p := by
    rw [← hlarge, ← prod_filter_mul_prod_filter_not D (fun p : ℕ => (p : ℝ) < x) b,
      mul_assoc, hcancel, mul_one, hsmall]
  change (∏ p ∈ S, a p) * (∏ p ∈ D, b p) * _ = _
  rw [mul_assoc, hD]
  rw [← prod_filter_mul_prod_filter_not S (fun p => p ∣ n) a]
  calc
    _ = ((∏ p ∈ S.filter (fun p => p ∣ n), a p) *
          (∏ p ∈ S.filter (fun p => p ∣ n), b p)) *
          (∏ p ∈ S.filter (fun p => ¬ p ∣ n), a p) := by ring
    _ = ∏ p ∈ S.filter (fun p => ¬ p ∣ n), a p := by
      rw [← prod_mul_distrib]
      have hc : (∏ p ∈ S.filter (fun p => p ∣ n), a p * b p) = 1 := by
        apply prod_eq_one
        intro p hp
        exact hab p (mem_filter.mp (mem_filter.mp hp).1).2
      rw [hc, one_mul]
    _ = _ := by rw [heligible]

/-- The full odd prime product dominates twice the twin constant times the
ordinary prime product, journal p. 1227 and Nathanson p. 278. -/
theorem odd_product_lower (x : ℝ) (hx : 2 < x) :
    2 * LeanLab.ChenExplicit.twinC *
      (∏ p ∈ Nat.primesBelow ⌈x⌉₊, (1 - 1 / (p : ℝ))) ≤
      ∏ p ∈ (Nat.primesBelow ⌈x⌉₊).filter (2 < ·), (1 - 1 / ((p : ℝ) - 1)) := by
  let S := (Nat.primesBelow ⌈x⌉₊).filter (2 < ·)
  have hodd (p : ℕ) (hp : p ∈ S) : p.Prime ∧ 2 < p :=
    ⟨Nat.prime_of_mem_primesBelow (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
  have h2 : 2 ∉ S := by simp [S]
  have hfull : insert 2 S = Nat.primesBelow ⌈x⌉₊ := by
    ext p
    simp only [S, mem_insert, mem_filter, Nat.mem_primesBelow]
    constructor
    · rintro (rfl | ⟨hp, _⟩)
      · exact ⟨(Nat.lt_ceil).mpr (by exact_mod_cast hx), Nat.prime_two⟩
      · exact hp
    · intro hp
      by_cases h : p = 2
      · exact Or.inl h
      · exact Or.inr ⟨hp, by have := hp.2.two_le; omega⟩
  have hpos : 0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    apply prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (hodd p hp).2
    have hd : (1 : ℝ) / p ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  -- Reuse the closed finite argument below the original leaf to avoid an import cycle.
  have htwin : LeanLab.ChenExplicit.twinC ≤
      ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    have hnonpos (n : ℕ) : LeanLab.ChenExplicit.aT n ≤ 0 := by
      unfold LeanLab.ChenExplicit.aT
      split_ifs with hn
      · apply log_nonpos (LeanLab.ChenExplicit.gT_pos hn.2).le
        unfold LeanLab.ChenExplicit.gT
        have hnn : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1) ^ 2 := by positivity
        linarith
      · exact le_rfl
    have hsum := LeanLab.ChenExplicit.summable_aT.neg.sum_le_tsum S
      (fun n _ => neg_nonneg.mpr (hnonpos n))
    rw [sum_neg_distrib, tsum_neg] at hsum
    have hsum' : (∑' n, LeanLab.ChenExplicit.aT n) ≤ ∑ n ∈ S, LeanLab.ChenExplicit.aT n := by
      linarith
    rw [LeanLab.ChenExplicit.twinC_eq_exp]
    apply (exp_le_exp.mpr hsum').trans_eq
    rw [exp_sum]
    apply prod_congr rfl
    intro p hp
    rw [LeanLab.ChenExplicit.aT, if_pos (hodd p hp),
      exp_log (LeanLab.ChenExplicit.gT_pos (hodd p hp).2)]
    rfl
  have ht := mul_le_mul_of_nonneg_left htwin hpos
  change 2 * LeanLab.ChenExplicit.twinC *
    (∏ p ∈ Nat.primesBelow ⌈x⌉₊, (1 - 1 / (p : ℝ))) ≤
      ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))
  rw [← hfull, prod_insert h2]
  norm_num only [Nat.cast_ofNat] at *
  rw [Verify1565.prod_identity S (fun p hp => (hodd p hp).2)]
  convert ht using 1 <;> ring

/-- The inclusive ordinary prime product is no larger than the strict one.
This transfers Schoenfeld display 6.23 to the endpoint convention of Lemma 10. -/
theorem inclusive_product_le_strict (x : ℝ) (hx : 0 ≤ x) :
    (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - 1 / (p : ℝ))) ≤
      ∏ p ∈ Nat.primesBelow ⌈x⌉₊, (1 - 1 / (p : ℝ)) := by
  apply prod_le_prod_of_subset_of_le_one₀
  · intro p hp
    rw [Nat.mem_primesLE]
    have hpx : (p : ℝ) < x := (Nat.lt_ceil).mp (Nat.mem_primesBelow.mp hp).1
    exact ⟨(Nat.le_floor_iff hx).mpr hpx.le, (Nat.mem_primesBelow.mp hp).2⟩
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have hd : (1 : ℝ) / p ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  · intro p hp _
    have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
    have hd : 0 ≤ (1 : ℝ) / p := by positivity
    linarith

/-- The RH Mertens loss and the full divisor loss fit the journal 0.62 budget.
The variable x is n to the power one eighth, journal Lemma 10 p. 1227. -/
theorem density_error_budget (x L : ℝ) (hx : 64 ≤ x) (hL : 8 ≤ L)
    (hlog : log x = L / 8) :
    (3 * log x + 5) / (8 * π * √x) + 4 * L / x ≤ 0.62 * L / √x := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := sqrt_pos.mpr hx0
  have hs8 : 8 ≤ √x := by
    have h := sqrt_le_sqrt hx
    norm_num at h
    exact h
  have hm : (3 * log x + 5) / (8 * π * √x) ≤ (1 / 10 : ℝ) * L / √x := by
    have hp : 3 ≤ π := le_of_lt pi_gt_three
    have hLp := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ L)
    have hnum : 3 * log x + 5 ≤ (1 / 10 : ℝ) * L * (8 * π) := by
      rw [hlog]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hnum hs.le
    rw [div_le_div_iff₀ (by positivity) hs]
    nlinarith
  have ht : 4 * L / x ≤ (1 / 2 : ℝ) * L / √x := by
    rw [div_le_div_iff₀ hx0 hs]
    have hLS := mul_le_mul_of_nonneg_left hs8 (by linarith : 0 ≤ L)
    have hsquare := congrArg (fun y : ℝ => L * y) (sq_sqrt hx0.le)
    have hmul := mul_le_mul_of_nonneg_right hLS hs.le
    nlinarith
  have hLdiv : 0 ≤ L / √x := div_nonneg (by linarith) hs.le
  calc
    _ ≤ (1 / 10 : ℝ) * L / √x + (1 / 2 : ℝ) * L / √x := add_le_add hm ht
    _ = (0.60 : ℝ) * (L / √x) := by ring
    _ ≤ (0.62 : ℝ) * (L / √x) := mul_le_mul_of_nonneg_right (by norm_num) hLdiv
    _ = _ := by ring

/-- Combining the two multiplicative errors needs no positivity of one minus
an error. This is the lower bound calculation of journal Lemma 10 p. 1227. -/
theorem combine_lower_errors (P c E T H : ℝ) (hc : 0 ≤ c) (hE : 0 ≤ E)
    (hH0 : 0 ≤ H) (hH1 : H ≤ 1) (hH : 1 - T ≤ H)
    (hP : c * (1 - E) ≤ P) :
    c * (1 - E - T) ≤ P * H := by
  have hPH := mul_le_mul_of_nonneg_right hP hH0
  have hEH := mul_le_mul_of_nonneg_left hH1 hE
  have hsum : 1 - E - T ≤ (1 - E) * H := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsum hc
  nlinarith

/-- Exact reduction of the lower density bound to the ordinary RH Mertens
estimate, journal Lemma 10 p. 1227. CONDITIONAL ON the displayed product bound. -/
theorem density_lower_of_mertens (n : ℕ) (hn : (4e18 : ℝ) ≤ n) (hev : Even n)
    (hM : exp (-eulerMascheroniConstant) / log (U7153.zz n) *
      (1 - (3 * log (U7153.zz n) + 5) / (8 * π * √(U7153.zz n))) ≤
        ∏ p ∈ Nat.primesLE ⌊U7153.zz n⌋₊, (1 - 1 / (p : ℝ))) :
    8 * UNfull n / log n * (1 - 0.62 * log n / (n : ℝ) ^ (1 / 16 : ℝ)) ≤
      DecompC169a.density n := by
  let x := U7153.zz n
  let L := log (n : ℝ)
  let P := ∏ p ∈ Nat.primesBelow ⌈x⌉₊, (1 - 1 / (p : ℝ))
  let H := ∏ p ∈ n.primeFactors.filter (fun p : ℕ => x ≤ (p : ℝ)),
    (1 - 1 / ((p : ℝ) - 1))
  let c := exp (-eulerMascheroniConstant) / log x
  let E := (3 * log x + 5) / (8 * π * √x)
  let T := 4 * L / x
  have hn0R : (0 : ℝ) < n := by linarith
  have hn0 : 0 < n := by exact_mod_cast hn0R
  have hx64 : 64 ≤ x := by
    change (64 : ℝ) ≤ (n : ℝ) ^ (1 / 8 : ℝ)
    rw [one_div]
    apply (le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 64)
      (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 8)).mpr
    rw [show (8 : ℝ) = (8 : ℕ) by norm_num, rpow_natCast]
    calc
      (64 : ℝ) ^ (8 : ℕ) = 281474976710656 := by norm_num
      _ ≤ (n : ℝ) := by linarith
  have hx2 : 2 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hlog : log x = L / 8 := by
    dsimp [x, L, U7153.zz]
    rw [log_rpow hn0R]
    ring
  have hlog1 : 1 ≤ log x := by
    have h4 : log (4 : ℝ) ≤ log x := log_le_log (by norm_num) (by linarith)
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow] at h4
    norm_num only [Nat.cast_ofNat] at h4
    linarith [log_two_gt_d9]
  have hL : 8 ≤ L := by linarith
  have hroot : √x = (n : ℝ) ^ (1 / 16 : ℝ) := by
    dsimp [x, U7153.zz]
    rw [sqrt_eq_rpow, ← rpow_mul hn0R.le]
    congr 1
    norm_num
  have hH0 : 0 ≤ H := by
    apply prod_nonneg
    intro p hp
    have hp64 := hx64.trans (mem_filter.mp hp).2
    have hd : (1 : ℝ) / (p - 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  have hH1 : H ≤ 1 := by
    apply prod_le_one₀
    · intro p hp
      have hp64 := hx64.trans (mem_filter.mp hp).2
      have hd : (1 : ℝ) / (p - 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      linarith
    · intro p hp
      have hp64 := hx64.trans (mem_filter.mp hp).2
      have hd : 0 ≤ (1 : ℝ) / (p - 1) := div_nonneg (by norm_num) (by linarith)
      linarith
  have hH : 1 - T ≤ H := by
    change 1 - 4 * log (n : ℝ) / x ≤
      ∏ p ∈ n.primeFactors.filter (fun p : ℕ => x ≤ (p : ℝ)), (1 - 1 / ((p : ℝ) - 1))
    have hz3 : 3 ≤ x := by linarith
    -- The following closed arguments already occur in DecompC169a.
    -- They are localized here because that file imports the original leaf.
    have finite_prod_one_sub_lower (s : Finset ℕ) (f : ℕ → ℝ)
        (hf0 : ∀ p ∈ s, 0 ≤ f p) (hf1 : ∀ p ∈ s, f p ≤ 1) :
        1 - ∑ p ∈ s, f p ≤ ∏ p ∈ s, (1 - f p) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert p s hps ih =>
        have hp0 := hf0 p (mem_insert_self _ _)
        have hp1 := hf1 p (mem_insert_self _ _)
        have hs0 := fun q hq => hf0 q (mem_insert_of_mem hq)
        have hs1 := fun q hq => hf1 q (mem_insert_of_mem hq)
        have htail := ih hs0 hs1
        have hprod : ∏ q ∈ s, (1 - f q) ≤ 1 :=
          prod_le_one₀ (fun q hq => by linarith [hs1 q hq])
            (fun q hq => by linarith [hs0 q hq])
        have hm := mul_le_mul_of_nonneg_left hprod hp0
        rw [sum_insert hps, prod_insert hps]
        nlinarith
    have prime_factor_card_le_two_log (n : ℕ) (hn : 0 < n) :
        (n.primeFactors.card : ℝ) ≤ 2 * log (n : ℝ) := by
      have hpow : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
        rw [← prod_const]
        exact prod_le_prod fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
      have hprod : (∏ p ∈ n.primeFactors, p) ≤ n :=
        Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
      have hpowR : (2 : ℝ) ^ n.primeFactors.card ≤ n := by exact_mod_cast hpow.trans hprod
      have hlog := log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpowR
      rw [log_pow] at hlog
      have hlog2 : (1 / 2 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
      have hcard0 : (0 : ℝ) ≤ n.primeFactors.card := Nat.cast_nonneg _
      nlinarith
    let T : Finset ℕ := n.primeFactors.filter (fun p : ℕ => x ≤ (p : ℝ))
    have hp3 (p : ℕ) (hp : p ∈ T) : (3 : ℝ) ≤ p := hz3.trans (mem_filter.mp hp).2
    have hf0 (p : ℕ) (hp : p ∈ T) : 0 ≤ (1 : ℝ) / (p - 1) :=
      div_nonneg (by norm_num) (by linarith [hp3 p hp])
    have hf1 (p : ℕ) (hp : p ∈ T) : (1 : ℝ) / (p - 1) ≤ 1 :=
      (div_le_one (by linarith [hp3 p hp])).mpr (by linarith [hp3 p hp])
    have hsmall (p : ℕ) (hp : p ∈ T) : (1 : ℝ) / (p - 1) ≤ 2 / x := by
      rw [div_le_div_iff₀ (by linarith [hp3 p hp]) (by linarith : 0 < x)]
      have hzp := (mem_filter.mp hp).2
      linarith [hp3 p hp]
    have hcard : (T.card : ℝ) ≤ n.primeFactors.card := by
      exact_mod_cast card_filter_le n.primeFactors (fun p => x ≤ (p : ℝ))
    have hsum : (∑ p ∈ T, (1 : ℝ) / (p - 1)) ≤ 4 * log (n : ℝ) / x := by
      calc
        _ ≤ ∑ _p ∈ T, (2 / x : ℝ) := sum_le_sum hsmall
        _ = (T.card : ℝ) * (2 / x) := by simp
        _ ≤ (n.primeFactors.card : ℝ) * (2 / x) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ ≤ (2 * log (n : ℝ)) * (2 / x) :=
          mul_le_mul_of_nonneg_right (prime_factor_card_le_two_log n hn0) (by positivity)
        _ = _ := by ring
    exact (sub_le_sub_left hsum 1).trans (finite_prod_one_sub_lower T _ hf0 hf1)
  have hc : 0 ≤ c := div_nonneg (exp_pos _).le (by linarith)
  have hlog0 : 0 ≤ log x := by linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hP : c * (1 - E) ≤ P :=
    hM.trans (inclusive_product_le_strict x hx0.le)
  have hPH := combine_lower_errors P c E T H hc hE hH0 hH1 hH hP
  have hbudget : E + T ≤ 0.62 * L / √x := density_error_budget x L hx64 hL hlog
  have hbound : c * (1 - 0.62 * L / √x) ≤ P * H :=
    (mul_le_mul_of_nonneg_left (by linarith : 1 - 0.62 * L / √x ≤ 1 - E - T) hc).trans hPH
  have hUN : 0 ≤ UN n := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_UN n)
  have htwin : 0 ≤ LeanLab.ChenExplicit.twinC := by
    rw [LeanLab.ChenExplicit.twinC_eq_exp]
    exact (exp_pos _).le
  have hscale : 0 ≤ 2 * LeanLab.ChenExplicit.twinC * UN n := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hbound hscale
  have hfinite : (2 * LeanLab.ChenExplicit.twinC * UN n) * (P * H) ≤
      DecompC169a.density n := by
    calc
      _ = (2 * LeanLab.ChenExplicit.twinC * P) * (UN n * H) := by ring
      _ ≤ (∏ p ∈ (Nat.primesBelow ⌈x⌉₊).filter (2 < ·),
          (1 - 1 / ((p : ℝ) - 1))) * (UN n * H) :=
        mul_le_mul_of_nonneg_right (odd_product_lower x hx2) (mul_nonneg hUN hH0)
      _ = _ := by
        simpa only [mul_assoc, x, H, DecompC169a.density] using
          full_divisor_correction n hn0 x hx2 hev
  have hLnz : L ≠ 0 := by linarith
  have hrootnz : (n : ℝ) ^ (1 / 16 : ℝ) ≠ 0 := (rpow_pos_of_pos hn0R _).ne'
  have hid : 8 * UNfull n / log n * (1 - 0.62 * log n / (n : ℝ) ^ (1 / 16 : ℝ)) =
      (2 * LeanLab.ChenExplicit.twinC * UN n) * (c * (1 - 0.62 * L / √x)) := by
    rw [UNfull_eq, hroot]
    dsimp only [c]
    rw [hlog]
    change 8 * (2 * exp (-eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC * UN n) / L *
      (1 - 0.62 * L / (n : ℝ) ^ (1 / 16 : ℝ)) = _
    field_simp
  rw [hid]
  exact hscaled.trans hfinite

end
end LeanLab.BS2022GRH.Density410
#print axioms LeanLab.BS2022GRH.Density410.full_divisor_correction

#print axioms LeanLab.BS2022GRH.Density410.odd_product_lower
#print axioms LeanLab.BS2022GRH.Density410.inclusive_product_le_strict

#print axioms LeanLab.BS2022GRH.Density410.density_error_budget
#print axioms LeanLab.BS2022GRH.Density410.combine_lower_errors

#print axioms LeanLab.BS2022GRH.Density410.density_lower_of_mertens
