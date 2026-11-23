/-
Proof of the LEAF tau_mono_eps1122c of Split1122cTauSum.lean: the bounds τ_n of BJS
display 31, Lemma 11, Bordignon, Johnston and Starichkova, arXiv 2207.09452v6,
papers/P0009.pdf, page 11, are increasing in ε. tau_mono_gen_s77 holds for any positive c.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122cTauSum

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

theorem mulXi_s77 (γ κ ε cp cc t : ℝ) (ht : 0 < t) :
    t * bjsXi306 γ κ ε cp cc t = κ * t + (γ + κ) * ε * t + 2 * γ * cp + 2 * cc := by
  unfold bjsXi306; field_simp

theorem mulXi_mono_s77 {γ κ ε ε' cp cc t t' : ℝ} (hγ : 0 ≤ γ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε)
    (hεε : ε ≤ ε') (ht : 0 < t) (htt : t ≤ t') :
    t * bjsXi306 γ κ ε cp cc t ≤ t' * bjsXi306 γ κ ε' cp cc t' := by
  rw [mulXi_s77 _ _ _ _ _ _ ht, mulXi_s77 _ _ _ _ _ _ (by linarith)]
  have h1 : ε * t ≤ ε' * t' := mul_le_mul hεε htt ht.le (hε.trans hεε)
  have h2 : κ * t ≤ κ * t' := mul_le_mul_of_nonneg_left htt hκ
  have h3 : (γ + κ) * (ε * t) ≤ (γ + κ) * (ε' * t') := mul_le_mul_of_nonneg_left h1 (by linarith)
  nlinarith

theorem mulXi_pos_s77 {γ κ ε cp cc t : ℝ} (hγ : 0 ≤ γ) (hκ : 0 < κ) (hε : 0 ≤ ε)
    (hcp : 0 ≤ cp) (hcc : 0 ≤ cc) (ht : 0 < t) : 0 < t * bjsXi306 γ κ ε cp cc t := by
  rw [mulXi_s77 _ _ _ _ _ _ ht]; positivity

theorem mulTil_s77 (ε cp cc t : ℝ) (ht : 0 < t) :
    t * (0.9214 + (5 + 4 * ε) * ε + 6 * (1 + ε) * cp / t + 2 * (2 + ε) * cc / t)
      = 0.9214 * t + (5 + 4 * ε) * ε * t + 6 * (1 + ε) * cp + 2 * (2 + ε) * cc := by
  field_simp

theorem mulTil_mono_s77 {ε ε' cp cc t t' : ℝ} (hε : 0 ≤ ε) (hεε : ε ≤ ε') (hcp : 0 ≤ cp)
    (hcc : 0 ≤ cc) (ht : 0 < t) (htt : t ≤ t') :
    t * (0.9214 + (5 + 4 * ε) * ε + 6 * (1 + ε) * cp / t + 2 * (2 + ε) * cc / t) ≤
      t' * (0.9214 + (5 + 4 * ε') * ε' + 6 * (1 + ε') * cp / t' + 2 * (2 + ε') * cc / t') := by
  rw [mulTil_s77 _ _ _ _ ht, mulTil_s77 _ _ _ _ (by linarith)]
  have h1 : ε * t ≤ ε' * t' := mul_le_mul hεε htt ht.le (hε.trans hεε)
  have h0 : (5 + 4 * ε) * (ε * t) ≤ (5 + 4 * ε') * (ε' * t') :=
    mul_le_mul (by linarith) h1 (by positivity) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hεε hcp, mul_le_mul_of_nonneg_right hεε hcc]

theorem tau_mono_gen_s77 (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (ε ε' : ℝ) (hε : 0 ≤ ε)
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
        exact mulXi_pos_s77 zero_le_one (by norm_num) hε hcp hcc hpos
      · refine max_le_max (max_le_max (max_le_max ?_ ?_) (max_le_max ?_ ?_)) (max_le_max ?_ ?_)
        · exact mulXi_mono_s77 zero_le_one (by norm_num) hε hεε hpos hle
        · exact mulXi_mono_s77 e1 (by norm_num) hε hεε hpos hle
        · exact mulXi_mono_s77 e2 (by norm_num) hε hεε hpos hle
        · exact mulXi_mono_s77 e3 (by norm_num) hε hεε hpos hle
        · exact mulXi_mono_s77 e4 (by norm_num) hε hεε hpos hle
        · exact mulXi_mono_s77 e5 (by norm_num) hε hεε hpos hle
    · rw [mul_max_of_nonneg _ _ hpos.le, mul_max_of_nonneg _ _ hpos'.le]
      refine ⟨?_, ?_⟩
      · exact lt_of_lt_of_le (mulXi_pos_s77 e5 (by norm_num) hε hcp hcc hpos) (le_max_left _ _)
      · exact max_le_max (mulXi_mono_s77 e5 (by norm_num) hε hεε hpos hle)
          (mulTil_mono_s77 hε hεε hcp hcc hpos hle)

/-- Proof of the LEAF tau_mono_eps1122c of Split1122cTauSum.lean, statement verbatim: BJS
display 31 recursion is increasing in ε, by induction with the positivity of τ_n. -/
theorem tau_mono_eps_s77 (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000) (n : ℕ) :
    bjsTau306 bjsC306 ε n ≤ bjsTau306 bjsC306 (1 / 100000) n := by
  cases n with
  | zero => simp [bjsTau306]
  | succ k => exact (tau_mono_gen_s77 bjsC306 bjsC306_pos ε _ hε.le hε5 k).2

#print axioms tau_mono_eps_s77
/-- tau_odd_sum_le132_twin1122c with the monotonicity LEAF discharged. -/
theorem tau_odd_sum_le132_mono1122c (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 ε n ≤ 132 := by
  have hm : ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 ε n ≤
      ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n :=
    Finset.sum_le_sum fun n _ => tau_mono_eps_s77 ε hε hε5 n
  refine hm.trans ?_
  rcases le_or_gt N 500 with h | h
  · linarith [tau_odd_le500_1122c N h]
  · rw [sum_split500_1122c Odd _ N h.le]
    linarith [tau_odd_le500_1122c 500 le_rfl, tau_odd_tail1122c N]

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.tau_mono_eps_s77
