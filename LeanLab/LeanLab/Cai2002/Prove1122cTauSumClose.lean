/-
Copies, under new names, of the proofs of tau_mono_eps_s77 of Prove1122cTauMono.lean and of the
tail bounds of Split1122cTauTail.lean, BJS arXiv 2207.09452v6, papers/P0009.pdf, display 31,
Lemma 11 and Proposition 13. Those files import Split1122cTauSum.lean, so their proofs cannot
close the LEAFs tau_mono_eps1122c, tau_odd_tail1122c and tau_even_tail1122c there; this file sits
below Split1122cTauSum.lean and does, with τ_500 ≤ 2e-12 from tau500_value1122e of
Prove1122cTauNum.lean. Proofs by the S77 workflow, copied in burst-20261124 S9.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Prove1122cTauNum

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

theorem mulXi_e1 (γ κ ε cp cc t : ℝ) (ht : 0 < t) :
    t * bjsXi306 γ κ ε cp cc t = κ * t + (γ + κ) * ε * t + 2 * γ * cp + 2 * cc := by
  unfold bjsXi306; field_simp

theorem mulXi_mono_e1 {γ κ ε ε' cp cc t t' : ℝ} (hγ : 0 ≤ γ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε)
    (hεε : ε ≤ ε') (ht : 0 < t) (htt : t ≤ t') :
    t * bjsXi306 γ κ ε cp cc t ≤ t' * bjsXi306 γ κ ε' cp cc t' := by
  rw [mulXi_e1 _ _ _ _ _ _ ht, mulXi_e1 _ _ _ _ _ _ (by linarith)]
  have h1 : ε * t ≤ ε' * t' := mul_le_mul hεε htt ht.le (hε.trans hεε)
  have h2 : κ * t ≤ κ * t' := mul_le_mul_of_nonneg_left htt hκ
  have h3 : (γ + κ) * (ε * t) ≤ (γ + κ) * (ε' * t') := mul_le_mul_of_nonneg_left h1 (by linarith)
  nlinarith

theorem mulXi_pos_e1 {γ κ ε cp cc t : ℝ} (hγ : 0 ≤ γ) (hκ : 0 < κ) (hε : 0 ≤ ε)
    (hcp : 0 ≤ cp) (hcc : 0 ≤ cc) (ht : 0 < t) : 0 < t * bjsXi306 γ κ ε cp cc t := by
  rw [mulXi_e1 _ _ _ _ _ _ ht]; positivity

theorem mulTil_e1 (ε cp cc t : ℝ) (ht : 0 < t) :
    t * (0.9214 + (5 + 4 * ε) * ε + 6 * (1 + ε) * cp / t + 2 * (2 + ε) * cc / t)
      = 0.9214 * t + (5 + 4 * ε) * ε * t + 6 * (1 + ε) * cp + 2 * (2 + ε) * cc := by
  field_simp

theorem mulTil_mono_e1 {ε ε' cp cc t t' : ℝ} (hε : 0 ≤ ε) (hεε : ε ≤ ε') (hcp : 0 ≤ cp)
    (hcc : 0 ≤ cc) (ht : 0 < t) (htt : t ≤ t') :
    t * (0.9214 + (5 + 4 * ε) * ε + 6 * (1 + ε) * cp / t + 2 * (2 + ε) * cc / t) ≤
      t' * (0.9214 + (5 + 4 * ε') * ε' + 6 * (1 + ε') * cp / t' + 2 * (2 + ε') * cc / t') := by
  rw [mulTil_e1 _ _ _ _ ht, mulTil_e1 _ _ _ _ (by linarith)]
  have h1 : ε * t ≤ ε' * t' := mul_le_mul hεε htt ht.le (hε.trans hεε)
  have h0 : (5 + 4 * ε) * (ε * t) ≤ (5 + 4 * ε') * (ε' * t') :=
    mul_le_mul (by linarith) h1 (by positivity) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hεε hcp, mul_le_mul_of_nonneg_right hεε hcc]

theorem tau_mono_gen_e1 (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (ε ε' : ℝ) (hε : 0 ≤ ε)
    (hεε : ε ≤ ε') (n : ℕ) :
    0 < bjsTau306 c ε (n + 1) ∧ bjsTau306 c ε (n + 1) ≤ bjsTau306 c ε' (n + 1) := by
  induction n with
  | zero => simp [bjsTau306]
  | succ k ih =>
    obtain ⟨hpos, hle⟩ := ih
    have hcp : 0 ≤ c (k + 1) ^ k := (pow_pos (hc _) _).le
    have hcc : 0 ≤ c (k + 2) ^ (k + 1) := (pow_pos (hc _) _).le
    have hpos' : 0 < bjsTau306 c ε' (k + 1) := lt_of_lt_of_le hpos hle
    simp only [bjsTau306]
    set t := bjsTau306 c ε (k + 1)
    set t' := bjsTau306 c ε' (k + 1)
    have e1 : 0 ≤ exp 0.2 := (exp_pos _).le
    have e2 : 0 ≤ exp 0.4 := (exp_pos _).le
    have e3 : 0 ≤ exp 0.6 := (exp_pos _).le
    have e4 : 0 ≤ exp 0.8 := (exp_pos _).le
    have e5 : 0 ≤ 4 * exp 1 / 3 := by positivity
    split_ifs with hev
    · rw [mul_max_of_nonneg _ _ hpos.le, mul_max_of_nonneg _ _ hpos.le,
        mul_max_of_nonneg _ _ hpos.le, mul_max_of_nonneg _ _ hpos.le,
        mul_max_of_nonneg _ _ hpos.le, mul_max_of_nonneg _ _ hpos'.le,
        mul_max_of_nonneg _ _ hpos'.le, mul_max_of_nonneg _ _ hpos'.le,
        mul_max_of_nonneg _ _ hpos'.le, mul_max_of_nonneg _ _ hpos'.le]
      refine ⟨?_, ?_⟩
      · refine lt_of_lt_of_le ?_ (le_max_left _ _)
        refine lt_of_lt_of_le ?_ (le_max_left _ _)
        refine lt_of_lt_of_le ?_ (le_max_left _ _)
        exact mulXi_pos_e1 zero_le_one (by norm_num) hε hcp hcc hpos
      · refine max_le_max (max_le_max (max_le_max ?_ ?_) (max_le_max ?_ ?_)) (max_le_max ?_ ?_)
        · exact mulXi_mono_e1 zero_le_one (by norm_num) hε hεε hpos hle
        · exact mulXi_mono_e1 e1 (by norm_num) hε hεε hpos hle
        · exact mulXi_mono_e1 e2 (by norm_num) hε hεε hpos hle
        · exact mulXi_mono_e1 e3 (by norm_num) hε hεε hpos hle
        · exact mulXi_mono_e1 e4 (by norm_num) hε hεε hpos hle
        · exact mulXi_mono_e1 e5 (by norm_num) hε hεε hpos hle
    · rw [mul_max_of_nonneg _ _ hpos.le, mul_max_of_nonneg _ _ hpos'.le]
      refine ⟨?_, ?_⟩
      · exact lt_of_lt_of_le (mulXi_pos_e1 e5 (by norm_num) hε hcp hcc hpos) (le_max_left _ _)
      · exact max_le_max (mulXi_mono_e1 e5 (by norm_num) hε hεε hpos hle)
          (mulTil_mono_e1 hε hεε hcp hcc hpos hle)

/-- Proof of the LEAF tau_mono_eps1122c of Split1122cTauSum.lean, statement verbatim: BJS
display 31 recursion is increasing in ε, by induction with the positivity of τ_n. -/
theorem tau_mono_eps_e1 (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000) (n : ℕ) :
    bjsTau306 bjsC306 ε n ≤ bjsTau306 bjsC306 (1 / 100000) n := by
  cases n with
  | zero => simp [bjsTau306]
  | succ k => exact (tau_mono_gen_e1 bjsC306 bjsC306_pos ε _ hε.le hε5 k).2


theorem c_eq_e1o (n : ℕ) (hn : 501 ≤ n) : bjsC306 n = 0.9607 := by
  unfold bjsC306
  repeat rw [if_neg (by omega)]

theorem c500_e1o : bjsC306 500 = 0.73 := by
  unfold bjsC306
  iterate 19 rw [if_neg (by norm_num)]
  rw [if_pos (by norm_num)]

theorem c_le_e1o (n : ℕ) (hn : 500 ≤ n) : 0 < bjsC306 n ∧ bjsC306 n ≤ 0.9607 := by
  rcases Nat.eq_or_lt_of_le hn with h | h
  · subst h; rw [c500_e1o]; norm_num
  · rw [c_eq_e1o n h]; norm_num

theorem xi_bd_e1o {γ κ cp cc t q : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 3.7) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 0.9607) (hcp0 : 0 ≤ cp) (hcp : cp ≤ q) (hcc0 : 0 ≤ cc) (hcc : cc ≤ q)
    (ht : 0 < t) : t * bjsXi306 γ κ (1 / 100000) cp cc t ≤ 0.961 * t + 11 * q := by
  rw [mulXi_e1 _ _ _ _ _ _ ht]
  nlinarith [mul_le_mul hγ hcp hcp0 (by norm_num : (0:ℝ) ≤ 3.7), mul_nonneg hγ0 hcp0]

theorem til_bd_e1o {cp cc t q : ℝ} (hcp0 : 0 ≤ cp) (hcp : cp ≤ q) (hcc0 : 0 ≤ cc)
    (hcc : cc ≤ q) (ht : 0 < t) :
    t * (0.9214 + (5 + 4 * (1 / 100000 : ℝ)) * (1 / 100000) + 6 * (1 + 1 / 100000) * cp / t
      + 2 * (2 + 1 / 100000) * cc / t) ≤ 0.961 * t + 11 * q := by
  rw [mulTil_e1 _ _ _ _ ht]
  nlinarith

theorem tau_pos_e1o (n : ℕ) (hn : 1 ≤ n) : 0 < bjsTau306 bjsC306 (1 / 100000) n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (tau_mono_gen_e1 bjsC306 bjsC306_pos _ _ (by norm_num) le_rfl k).1

theorem tau_step_e1o (k : ℕ) (hk : 499 ≤ k) :
    bjsTau306 bjsC306 (1 / 100000) (k + 2) ≤
      0.961 * bjsTau306 bjsC306 (1 / 100000) (k + 1) + 11 * 0.9607 ^ k := by
  have hpos := tau_pos_e1o (k + 1) (by omega)
  obtain ⟨hc1p, hc1⟩ := c_le_e1o (k + 1) (by omega)
  have hc2 := c_eq_e1o (k + 2) (by omega)
  have hcp0 : 0 ≤ bjsC306 (k + 1) ^ k := (pow_pos hc1p _).le
  have hcp : bjsC306 (k + 1) ^ k ≤ 0.9607 ^ k := pow_le_pow_left₀ hc1p.le hc1 _
  have hcc0 : 0 ≤ bjsC306 (k + 2) ^ (k + 1) := by rw [hc2]; positivity
  have hcc : bjsC306 (k + 2) ^ (k + 1) ≤ 0.9607 ^ k := by
    rw [hc2]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have he := Real.exp_one_lt_d9
  have hg : 4 * exp 1 / 3 ≤ 3.7 := by linarith
  have h08 : exp 0.8 ≤ 3.7 := by
    have := Real.exp_le_exp.2 (show (0.8:ℝ) ≤ 1 by norm_num); linarith
  have h06 : exp 0.6 ≤ 3.7 := by
    have := Real.exp_le_exp.2 (show (0.6:ℝ) ≤ 1 by norm_num); linarith
  have h04 : exp 0.4 ≤ 3.7 := by
    have := Real.exp_le_exp.2 (show (0.4:ℝ) ≤ 1 by norm_num); linarith
  have h02 : exp 0.2 ≤ 3.7 := by
    have := Real.exp_le_exp.2 (show (0.2:ℝ) ≤ 1 by norm_num); linarith
  have e1 : 0 ≤ exp 0.2 := (exp_pos _).le
  have e2 : 0 ≤ exp 0.4 := (exp_pos _).le
  have e3 : 0 ≤ exp 0.6 := (exp_pos _).le
  have e4 : 0 ≤ exp 0.8 := (exp_pos _).le
  have e5 : 0 ≤ 4 * exp 1 / 3 := by positivity
  simp only [bjsTau306]
  set t := bjsTau306 bjsC306 (1 / 100000) (k + 1)
  split_ifs with hev
  · rw [mul_max_of_nonneg _ _ hpos.le, mul_max_of_nonneg _ _ hpos.le,
      mul_max_of_nonneg _ _ hpos.le, mul_max_of_nonneg _ _ hpos.le,
      mul_max_of_nonneg _ _ hpos.le]
    refine max_le (max_le (max_le ?_ ?_) (max_le ?_ ?_)) (max_le ?_ ?_)
    · exact xi_bd_e1o zero_le_one (by norm_num) (by norm_num) (by norm_num) hcp0 hcp hcc0 hcc hpos
    · exact xi_bd_e1o e1 h02 (by norm_num) (by norm_num) hcp0 hcp hcc0 hcc hpos
    · exact xi_bd_e1o e2 h04 (by norm_num) (by norm_num) hcp0 hcp hcc0 hcc hpos
    · exact xi_bd_e1o e3 h06 (by norm_num) (by norm_num) hcp0 hcp hcc0 hcc hpos
    · exact xi_bd_e1o e4 h08 (by norm_num) (by norm_num) hcp0 hcp hcc0 hcc hpos
    · exact xi_bd_e1o e5 hg (by norm_num) (by norm_num) hcp0 hcp hcc0 hcc hpos
  · rw [mul_max_of_nonneg _ _ hpos.le]
    exact max_le (xi_bd_e1o e5 hg (by norm_num) (by norm_num) hcp0 hcp hcc0 hcc hpos)
      (til_bd_e1o hcp0 hcp hcc0 hcc hpos)

theorem pow499_e1o : (0.9607 : ℝ) ^ 499 ≤ 1e-8 := by
  have h83 : (0.9607 : ℝ) ^ 83 ≤ 0.04 := by norm_num
  have : ∀ x : ℝ, x ^ 499 = (x ^ 83) ^ 6 * x := fun x => by
    rw [← pow_mul, ← pow_succ]
  rw [this]
  have h6 : ((0.9607 : ℝ) ^ 83) ^ 6 ≤ 0.04 ^ 6 := pow_le_pow_left₀ (by positivity) h83 6
  nlinarith

theorem tau_geom_e1o (h500 : bjsTau306 bjsC306 (1 / 100000) 500 ≤ 2e-12) (m : ℕ) :
    bjsTau306 bjsC306 (1 / 100000) (500 + m) ≤ 1e-3 * 0.97 ^ m := by
  induction m with
  | zero => simp only [add_zero, pow_zero]; linarith
  | succ m ih =>
    have hs := tau_step_e1o (499 + m) (by omega)
    have e1 : 499 + m + 2 = 500 + (m + 1) := by omega
    have e2 : 499 + m + 1 = 500 + m := by omega
    rw [e1, e2] at hs
    have hq : (0.9607 : ℝ) ^ (499 + m) ≤ 1e-8 * 0.97 ^ m := by
      rw [pow_add]
      exact mul_le_mul pow499_e1o (pow_le_pow_left₀ (by norm_num) (by norm_num) m)
        (by positivity) (by norm_num)
    have hp : (0:ℝ) ≤ 0.97 ^ m := by positivity
    rw [pow_succ]
    nlinarith

theorem tau_tail_sum_e1o (h500 : bjsTau306 bjsC306 (1 / 100000) 500 ≤ 2e-12) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 500 N, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.04 := by
  have hb : ∀ n ∈ Finset.Ioc 500 N, bjsTau306 bjsC306 (1 / 100000) n ≤
      1e-3 * (0.97 : ℝ) ^ (n - 500) := by
    intro n hn
    have := tau_geom_e1o h500 (n - 500)
    rwa [show 500 + (n - 500) = n by simp at hn; omega] at this
  refine (Finset.sum_le_sum hb).trans ?_
  rw [← Finset.mul_sum]
  have hinj : Set.InjOn (fun n : ℕ => n - 500) (Finset.Ioc 500 N : Set ℕ) := by
    intro a ha b hb hab; simp at ha hb hab; omega
  rw [← Finset.sum_image (f := fun i => (0.97 : ℝ) ^ i) hinj]
  have hsum : Summable (fun i : ℕ => (0.97 : ℝ) ^ i) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h1 := hsum.sum_le_tsum ((Finset.Ioc 500 N).image (fun n => n - 500))
    (fun i _ => by positivity)
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h1
  have : (1 - (0.97 : ℝ))⁻¹ ≤ 34 := by norm_num
  nlinarith

theorem tau_filter_le_e1o (h500 : bjsTau306 bjsC306 (1 / 100000) 500 ≤ 2e-12) (N : ℕ)
    (p : ℕ → Prop) [DecidablePred p] :
    ∑ n ∈ (Finset.Ioc 500 N).filter p, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.04 := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
    (tau_tail_sum_e1o h500 N)
  intro n hn _
  exact (tau_pos_e1o n (by simp at hn; omega)).le

theorem tau_odd_tail_of500_e1 (h500 : bjsTau306 bjsC306 (1 / 100000) 500 ≤ 2e-12) (N : ℕ) :
    ∑ n ∈ (Finset.Ioc 500 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.49 :=
  (tau_filter_le_e1o h500 N Odd).trans (by norm_num)

theorem tau_even_tail_of500_e1 (h500 : bjsTau306 bjsC306 (1 / 100000) 500 ≤ 2e-12) (N : ℕ) :
    ∑ n ∈ (Finset.Ioc 500 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.16 :=
  (tau_filter_le_e1o h500 N Even).trans (by norm_num)


/-- The odd tail of BJS display 31 beyond 500 at ε = 1/100000 is at most 0.49. -/
theorem tau_odd_tail_e1 (N : ℕ) :
    ∑ n ∈ (Finset.Ioc 500 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.49 :=
  tau_odd_tail_of500_e1 tau500_value1122e N

/-- The even tail of BJS display 31 beyond 500 at ε = 1/100000 is at most 0.16. -/
theorem tau_even_tail_e1 (N : ℕ) :
    ∑ n ∈ (Finset.Ioc 500 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.16 :=
  tau_even_tail_of500_e1 tau500_value1122e N

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.tau_mono_eps_e1
#print axioms LeanLab.Cai2002.tau_odd_tail_e1
#print axioms LeanLab.Cai2002.tau_even_tail_e1
