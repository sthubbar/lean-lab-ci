import Mathlib
import LeanLab.AlmostPrimes.PortedDusart.PiFinite

/-!
# ChebyshevExplicit, burst 1122 split of `pi_upper_finite_96098_3300000`

AI wrote this Lean code. Binary Goldbach is open.

The finite check `π n ≤ 1.10555 n / log n` on `96098 ≤ n < 3300000`, numerics of unit U-1615,
is split into three ranges.

* `[96098, 156979)`: a kernel certificate. The wheel stepper of
  `LeanLab/AlmostPrimes/PortedDusart/PiFinite.lean` is rerun on its own first data block
  `DusartCert.Gen.items0`, with the check `k (U/Q) ≤ 1.10555 L` in place of `k (U/Q - 1.1) ≤ L`.
  Here `k` bounds the prime count, `U/Q` bounds `log L` from above, `L` is the last kept
  candidate, and the step `log m ≤ log L + (m - L)/L` carries the check to all `m` in `[L, n)`.
* `[156979, 2000000]`: from the proved `S68PiCert.pi_good`, `π m (log m - 1.1) ≤ m`, since
  `m / (log m - 1.1) ≤ 1.10555 m / log m` once `log m ≥ 11.5217`, about `m ≥ 100872`.
* `(2000000, 3300000)`: in `..._p2_upper.lean`.
-/

namespace LeanLab.ChebyshevExplicit.Novelty1615.P2Cert

open S68PiCert DusartCert

/-- The modified wheel stepper: as `S68PiCert.pstep`, with the check
`100000 k U ≤ 110555 L Q` at each kept candidate `n ≥ L`. -/
noncomputable def pstep2 (Q : Nat) (cs : List Nat) : List Nat → Nat → Nat → Nat → Nat → Option St :=
  cs.rec (fun gs n k U L => some (n, gs, k, U, L)) (fun c _ ih gs n k U L =>
    gs.casesOn none (fun g t =>
    cond (Nat.beq c 0)
      (cond (Nat.blt n L) (ih (cond t.isEmpty gaps t) (n + g) (k + 1) U L)
        (cond (Nat.ble (100000 * k * U) (110555 * L * Q))
          (ih (cond t.isEmpty gaps t) (n + g) (k + 1) (U + (Q * (n - L) + L - 1) / L) n) none))
      (cond (Nat.blt 1 c && Nat.blt c n && Nat.beq (n % c) 0) (ih (cond t.isEmpty gaps t) (n + g) k U L) none)))

/-- Block runner for `pstep2`. -/
noncomputable def prun2 (Q : Nat) (l : List (List Nat × Option (Nat × Nat × Nat))) : St → Option St :=
  l.rec (fun s => some s) (fun x _ ih s =>
    (pstep2 Q x.1 s.2.1 s.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2).casesOn none ih)

/-- The stepper invariant, with start point `S`. -/
abbrev Inv2 (S Q n : ℕ) (gs : List ℕ) (k U L : ℕ) : Prop :=
  ∃ i < 48, gs = gaps.drop i ∧ n % 210 = res.getD i 0 ∧ 11 ≤ n ∧ Nat.count Nat.Prime n ≤ k ∧
    S ≤ L ∧ Real.log L ≤ (U : ℝ) / Q ∧ (L = S ∨ L < n) ∧
    ∀ m, S ≤ m → m < n → m < L →
      ((Nat.primeCounting m : ℝ) * Real.log m ≤ 110555 / 100000 * m)

lemma good_of_check2 {Q k U L m : ℕ} (hQ : 0 < Q) (hc : 100000 * k * U ≤ 110555 * L * Q)
    (hlog : Real.log L ≤ (U : ℝ) / Q) (hL : 60184 ≤ L) (hm : L ≤ m) (hk : Nat.primeCounting m ≤ k) :
    (Nat.primeCounting m : ℝ) * Real.log m ≤ 110555 / 100000 * m := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (by norm_num) (show (60184 : ℝ) ≤ L by exact_mod_cast hL)
  have hc' : (k : ℝ) * ((U : ℝ) / Q) ≤ 110555 / 100000 * L := by
    have : ((100000 * k * U : ℕ) : ℝ) ≤ ((110555 * L * Q : ℕ) : ℝ) := by exact_mod_cast hc
    push_cast at this
    have e : (k : ℝ) * ((U : ℝ) / Q) = (100000 * k * U : ℝ) / (100000 * Q) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]; linarith
  have h3 := three_le_log hL
  have hlm := log_le_lin (by omega) hm
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkL1 : (k : ℝ) * Real.log L ≤ 110555 / 100000 * L := by
    have : (k : ℝ) * Real.log L ≤ k * ((U : ℝ) / Q) := mul_le_mul_of_nonneg_left hlog hk0
    linarith
  have hkL : (k : ℝ) ≤ 110555 / 100000 * L := by nlinarith
  have hpk : (Nat.primeCounting m : ℝ) ≤ k := by exact_mod_cast hk
  have hmL : (L : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 3 ≤ Real.log m := le_trans h3 (Real.log_le_log hL0 hmL)
  have hfrac : (k : ℝ) * (((m : ℝ) - L) / L) ≤ 110555 / 100000 * ((m : ℝ) - L) := by
    rw [mul_div_assoc', div_le_iff₀ hL0]; nlinarith
  calc (Nat.primeCounting m : ℝ) * Real.log m ≤ k * Real.log m :=
        mul_le_mul_of_nonneg_right hpk (by linarith)
    _ ≤ k * (Real.log L + ((m : ℝ) - L) / L) := mul_le_mul_of_nonneg_left (by linarith) hk0
    _ = k * Real.log L + k * (((m : ℝ) - L) / L) := by ring
    _ ≤ 110555 / 100000 * L + 110555 / 100000 * ((m : ℝ) - L) := by linarith
    _ = 110555 / 100000 * m := by ring

theorem pstep2_sound (S Q : ℕ) (hS : 60184 ≤ S) (hQ : 0 < Q) : ∀ (cs gs : List ℕ) (n k U L : ℕ) (s : St),
    Inv2 S Q n gs k U L → pstep2 Q cs gs n k U L = some s →
    Inv2 S Q s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 := by
  intro cs
  induction cs with
  | nil =>
    intro gs n k U L s hI h
    simp only [pstep2, Option.some.injEq] at h
    subst h; exact hI
  | cons c cs ih =>
    intro gs n k U L s hI h
    obtain ⟨i, hi, hgs, hn, hn11, hk, hL, hlog, hLn, hgood⟩ := hI
    obtain ⟨hd, hrot⟩ := gs_step i hi
    rw [hgs, hd] at h
    have hg := gaps_pos i hi
    have hi' : (i + 1) % 48 < 48 := Nat.mod_lt _ (by norm_num)
    have hn' : (n + gaps.getD i 0) % 210 = res.getD ((i + 1) % 48) 0 := by
      rw [← res_next i hi, Nat.add_mod, hn, Nat.add_mod (res.getD i 0)]; simp
    have hnp : ∀ j, n < j → j < n + gaps.getD i 0 → ¬ j.Prime := fun j h1 h2 hp =>
      not_prime_between hi hn h1 h2 ⟨hp, by omega⟩
    have hcnt := count_gap hnp _ hg le_rfl
    change cond (Nat.beq c 0)
      (cond (Nat.blt n L) (pstep2 Q cs (cond (gaps.drop (i+1)).isEmpty gaps (gaps.drop (i+1))) (n + gaps.getD i 0) (k + 1) U L)
        (cond (Nat.ble (100000 * k * U) (110555 * L * Q))
          (pstep2 Q cs (cond (gaps.drop (i+1)).isEmpty gaps (gaps.drop (i+1))) (n + gaps.getD i 0) (k + 1)
            (U + (Q * (n - L) + L - 1) / L) n) none))
      (cond (Nat.blt 1 c && Nat.blt c n && Nat.beq (n % c) 0)
        (pstep2 Q cs (cond (gaps.drop (i+1)).isEmpty gaps (gaps.drop (i+1))) (n + gaps.getD i 0) k U L) none) = some s at h
    rw [hrot] at h
    cases hc0 : Nat.beq c 0
    · rw [hc0] at h
      cases hv : (Nat.blt 1 c && Nat.blt c n && Nat.beq (n % c) 0)
      · rw [hv] at h; simp at h
      rw [hv] at h
      simp only [cond_true] at h
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hv
      have hnot : ¬ n.Prime := fun hp =>
        Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hv.2) hv.1.1 hv.1.2 hp
      refine ih _ _ _ _ _ s ⟨_, hi', rfl, hn', by omega, ?_, hL, hlog, ?_, ?_⟩ h
      · rw [hcnt, if_neg hnot]; simpa using hk
      · rcases hLn with h1 | h1 <;> [left; right] <;> omega
      · intro m hm1 hm2 hm3
        by_cases hmn : m < n
        · exact hgood m hm1 hmn hm3
        · exfalso; rcases hLn with h1 | h1 <;> omega
    · rw [hc0] at h
      simp only [cond_true] at h
      have hk1 : Nat.count Nat.Prime (n + gaps.getD i 0) ≤ k + 1 := by
        rw [hcnt]; split_ifs <;> omega
      cases hb : Nat.blt n L
      · rw [hb] at h
        simp only [cond_false] at h
        have hb : L ≤ n := Nat.not_lt.mp (fun h' => by rw [Nat.blt_eq.mpr h'] at hb; exact Bool.noConfusion hb)
        cases hch : Nat.ble (100000 * k * U) (110555 * L * Q)
        · rw [hch] at h; simp at h
        rw [hch] at h
        simp only [cond_true] at h
        simp only [Nat.ble_eq] at hch
        refine ih _ _ _ _ _ s ⟨_, hi', rfl, hn', by omega, hk1, by omega, ?_, Or.inr (by omega), ?_⟩ h
        · have h1 := log_le_lin (by omega) hb
          rcases cdiv_real Q n L (by omega) with h2 | h2
          · push_cast; rw [add_div]; linarith
          · omega
        · intro m hm1 hm2 hm3
          by_cases hmL : m < L
          · exact hgood m hm1 hm3 hmL
          · exact good_of_check2 hQ hch hlog (by omega) (by omega) (pc_le hm3 hk)
      · rw [hb] at h
        simp only [cond_true] at h
        simp only [Nat.blt_eq] at hb
        have hLS : L = S := by rcases hLn with h1 | h1 <;> omega
        refine ih _ _ _ _ _ s ⟨_, hi', rfl, hn', by omega, hk1, hL, hlog, Or.inl hLS, ?_⟩ h
        intro m hm1 hm2 hm3; omega

theorem prun2_sound (S Q : ℕ) (hS : 60184 ≤ S) (hQ : 0 < Q) :
    ∀ (l : List (List ℕ × Option (ℕ × ℕ × ℕ))) (s s' : St),
    Inv2 S Q s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 → prun2 Q l s = some s' →
    Inv2 S Q s'.1 s'.2.1 s'.2.2.1 s'.2.2.2.1 s'.2.2.2.2 := by
  intro l
  induction l with
  | nil => intro s s' hI h; simp only [prun2, Option.some.injEq] at h; subst h; exact hI
  | cons x xs ih =>
    intro s s' hI h
    change (pstep2 Q x.1 s.2.1 s.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2).casesOn none (prun2 Q xs) = some s' at h
    cases hp : pstep2 Q x.1 s.2.1 s.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 with
    | none => rw [hp] at h; simp at h
    | some t =>
      rw [hp] at h
      exact ih t s' (pstep2_sound S Q hS hQ _ _ _ _ _ _ _ hI hp) h

lemma logS2 : Real.log ((96098 : ℕ) : ℝ) ≤ ((logHi QQ 96098 1 16 : ℕ) : ℝ) / (QQ : ℝ) := by
  have h := (log_bounds QQ 96098 1 16 (by decide +kernel)).2
  have hQ : (0 : ℝ) < QQ := by exact_mod_cast QQ_pos
  rw [le_div_iff₀ hQ]
  simp only [Nat.cast_one, div_one] at h
  linarith

lemma inv2_0 : Inv2 96098 QQ 11 (gaps.drop 1) 4 (logHi QQ 96098 1 16) 96098 := by
  refine ⟨1, by norm_num, rfl, by decide, le_rfl, by decide, le_rfl, logS2, Or.inl rfl, ?_⟩
  intro m h1 h2; omega

set_option maxRecDepth 200000 in
/-- The kernel certificate run of `pstep2` over the first data block, start point 96098. -/
theorem pc0 : prun2 QQ Gen.items0 (11, gaps.drop 1, 4, logHi QQ 96098 1 16, 96098) =
    some (157007, gaps.drop 30, 14433, 220695104579156346358, 156979) := by decide +kernel

/-- PROVED: `π m log m ≤ 1.10555 m` for `96098 ≤ m < 156979`, by the kernel certificate. -/
theorem pi_upper_96098_156979 (m : ℕ) (h1 : 96098 ≤ m) (h2 : m < 156979) :
    (Nat.primeCounting m : ℝ) * Real.log m ≤ 110555 / 100000 * m := by
  obtain ⟨i, hi, hgs, hn, hn11, hk, hL, hlog, hLn, hgood⟩ :=
    prun2_sound 96098 QQ (by norm_num) QQ_pos _ _ _ (by exact inv2_0) pc0
  exact hgood m h1 (by omega) h2

/-- PROVED: `11.5217 ≤ log 156979`, so `log m ≥ 11.5217` for `m ≥ 156979`. -/
lemma log_ge_of_ge {m : ℕ} (hm : 156979 ≤ m) : (11.5217 : ℝ) ≤ Real.log m := by
  have h1 : (11.5217 : ℝ) ≤ Real.log 156979 := by
    have h3 : (35 : ℝ) ≤ Real.log ((156979 : ℝ) ^ 3) := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h35 : Real.exp 35 = Real.exp 1 ^ 35 := by rw [← Real.exp_nat_mul]; norm_num
      have hd := Real.exp_one_lt_d9
      have : Real.exp 1 ^ 35 < (2.7182818286 : ℝ) ^ 35 :=
        pow_lt_pow_left₀ hd (Real.exp_pos 1).le (by norm_num)
      have : (2.7182818286 : ℝ) ^ 35 < (156979 : ℝ) ^ 3 := by norm_num
      linarith
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  have : (156979 : ℝ) ≤ m := by exact_mod_cast hm
  exact h1.trans (Real.log_le_log (by norm_num) this)

/-- PROVED from `S68PiCert.pi_good`: `π m log m ≤ 1.10555 m` for `156979 ≤ m ≤ 2000000`. -/
theorem pi_upper_156979_2000000 (m : ℕ) (h1 : 156979 ≤ m) (h2 : m ≤ 2000000) :
    (Nat.primeCounting m : ℝ) * Real.log m ≤ 110555 / 100000 * m := by
  have hg := pi_good m (by omega) h2
  have hl := log_ge_of_ge h1
  have hp : (0 : ℝ) ≤ Nat.primeCounting m := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  -- `π (log - 1.1) ≤ m` and `0.10555 log ≥ 1.216105` give `π log ≤ 1.10555 m`
  have hq : (0 : ℝ) ≤ (Nat.primeCounting m : ℝ) * (10555 / 100000 * Real.log m - 1216105 / 1000000) :=
    mul_nonneg hp (by linarith)
  nlinarith

end LeanLab.ChebyshevExplicit.Novelty1615.P2Cert
