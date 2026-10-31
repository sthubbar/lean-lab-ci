/-
AI-written Lean code, Claude, 2026-10-18, run 20261018T1803Z-10253, unit U-0963.
P0021 Bordignon, Starichkova 2022, arXiv 2211.08844 v1, Lemma 8, the ε(u) of display (6).

CONDITIONAL ON Lemma 7 of the paper, its two Mertens-sum bounds, which the paper cites
from Rosser-Schoenfeld 1962 and Broadbent, Kadiri, Lumley, Ng, Wilk 2021:
* `lemma8_of_mertensDiff`: for natural numbers 500 ≤ u ≤ z, if
  Σ_{u ≤ p < z} 1/p ≤ log log z − log log u + 1.5·10⁻⁴ / log u, display (9), then
  ∏_{u ≤ p < z} (1 − 1/(p − 1))⁻¹ ≤ (1 + ε(u)) log z / log u.
* `mertensDiff_of_lemma7`: display (9) follows from Lemma 7's upper bound at z and lower
  bound at u, with the same Mertens constant M, for any u ≥ 3.
* `lemma8`: the two together.
Everything else in the proof is PROVED here from first principles: the factorisation
(1 − 1/(p−1))⁻¹ = (1 + 1/(p(p−2))) (1 − 1/p)⁻¹, log(1 − t) ≥ −t − t² for 0 ≤ t ≤ 1/3,
two telescoping sums, e^x ≤ 1/(1 − x) and e^x ≤ 1 + x + x² for 0 ≤ x ≤ 1.

Two remarks on the paper's proof, neither a finding:
* The paper's first factor 1 + 1/(0.996u − 1) is derived through Lemma 6, a prime in
  [0.996x, x] for x ≥ 9551. Here it follows without Lemma 6 for every u ≥ 500, since
  Σ_{p ≥ u} 1/(p(p−2)) ≤ 1/(u − 2) by telescoping and e^{1/(u−2)} ≤ 1 + 1/(u − 3).
* The proof's last line says "u > 10^8", but Section 5.4 uses u = 10^{4.27}. The bound
  holds for every u ≥ 500 given (9), and (9) follows from Lemma 7 for every u ≥ 3, so the
  "u > 10^8" is not needed.
Goldbach is open.
-/
import Mathlib
import LeanLab.BS2022GRH.Params

open Real Finset

noncomputable section
namespace LeanLab.BS2022GRH

/-- The primes p with u ≤ p < z. -/
def primesIco (u z : ℕ) : Finset ℕ := (Ico u z).filter Nat.Prime

/-- Display (9) of the paper, the Mertens-sum difference. Cited input. -/
def MertensDiff (u z : ℕ) : Prop :=
  ∑ p ∈ primesIco u z, (1 : ℝ) / p ≤ log (log z) - log (log u) + 1.5e-4 / log u

/-- Lemma 7 of the paper, the two bounds used for (9), with Mertens' constant `M`:
the upper bound at z, valid for z > exp 1000, and the weaker of the two lower bounds,
which covers both of the paper's cases. Cited input. -/
def Lemma7Bounds (M : ℝ) (u z : ℕ) : Prop :=
  (∑ p ∈ (range z).filter Nat.Prime, (1 : ℝ) / p ≤ log (log z) + M + 4.47e-9 / log z) ∧
  (log (log u) + M - 1.4998e-4 / log u ≤ ∑ p ∈ (range u).filter Nat.Prime, (1 : ℝ) / p)

lemma tele1 (u : ℕ) (hu : 3 ≤ u) : ∀ z, u ≤ z →
    ∑ n ∈ Ico u z, (1 : ℝ) / (((n : ℝ) - 2) * ((n : ℝ) - 1)) = 1 / ((u : ℝ) - 2) - 1 / ((z : ℝ) - 2) := by
  intro z hz
  induction z, hz using Nat.le_induction with
  | base => simp
  | succ z hz ih =>
    rw [sum_Ico_succ_top hz, ih]
    have h3 : (3 : ℝ) ≤ z := by exact_mod_cast le_trans hu hz
    have a : (z : ℝ) - 2 ≠ 0 := by linarith
    have b : (z : ℝ) - 1 ≠ 0 := by linarith
    have c : ((z + 1 : ℕ) : ℝ) - 2 = (z : ℝ) - 1 := by push_cast; ring
    rw [c]; field_simp; ring

lemma tele2 (u : ℕ) (hu : 2 ≤ u) : ∀ z, u ≤ z →
    ∑ n ∈ Ico u z, (1 : ℝ) / (((n : ℝ) - 1) * (n : ℝ)) = 1 / ((u : ℝ) - 1) - 1 / ((z : ℝ) - 1) := by
  intro z hz
  induction z, hz using Nat.le_induction with
  | base => simp
  | succ z hz ih =>
    rw [sum_Ico_succ_top hz, ih]
    have h3 : (2 : ℝ) ≤ z := by exact_mod_cast le_trans hu hz
    have a : (z : ℝ) - 1 ≠ 0 := by linarith
    have b : (z : ℝ) ≠ 0 := by linarith
    have c : ((z + 1 : ℕ) : ℝ) - 1 = (z : ℝ) := by push_cast; ring
    rw [c]; field_simp; ring

/-- log(1 − t) ≥ −t − t² for 0 ≤ t ≤ 1/3. -/
lemma log_one_sub_ge {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 3) : -t - t ^ 2 ≤ log (1 - t) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := t) (by rw [abs_of_nonneg h0]; linarith) 2
  rw [abs_le, abs_of_nonneg h0] at h
  simp only [sum_range_succ, sum_range_zero] at h
  have h2 : t ^ (2 + 1) / (1 - t) ≤ t ^ 2 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have := mul_nonneg (sq_nonneg t) (by linarith : (0 : ℝ) ≤ 1 - 3 * t)
    have e : t ^ (2 + 1) = t ^ 2 * t := by ring
    rw [e]; nlinarith
  norm_num at h
  nlinarith [h.1]

/-- (1 − t)⁻¹ ≤ e^{t + t²} for 0 ≤ t ≤ 1/3. -/
lemma inv_one_sub_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 3) : (1 - t)⁻¹ ≤ exp (t + t ^ 2) := by
  have hp : 0 < 1 - t := by linarith
  rw [← exp_log hp, ← exp_neg]
  exact exp_le_exp.mpr (by linarith [log_one_sub_ge h0 h1])

/-- e^x ≤ 1/(1 − x) for x < 1. -/
lemma exp_le_inv {x : ℝ} (hx : x < 1) : exp x ≤ (1 - x)⁻¹ := by
  have h := Real.add_one_le_exp (-x)
  have hp : 0 < 1 - x := by linarith
  rw [← inv_inv (exp x), ← exp_neg]
  exact inv_anti₀ hp (by linarith)

/-- e^x ≤ 1 + x + x² for |x| ≤ 1. -/
lemma exp_le_quad {x : ℝ} (hx : |x| ≤ 1) : exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le hx
  rw [abs_le] at h
  linarith [h.2]

/-- The per-prime factorisation. -/
lemma factor {x : ℝ} (hx : 3 ≤ x) :
    (1 - 1 / (x - 1))⁻¹ = (1 + 1 / (x * (x - 2))) * (1 - 1 / x)⁻¹ := by
  have a : x - 1 ≠ 0 := by linarith
  have b : x - 2 ≠ 0 := by linarith
  have c : x ≠ 0 := by linarith
  have d : x - 1 - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **Lemma 8, CONDITIONAL ON display (9).** -/
theorem lemma8_of_mertensDiff (u z : ℕ) (hu : 500 ≤ u) (huz : u ≤ z) (hM : MertensDiff u z) :
    ∏ p ∈ primesIco u z, (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤ (1 + epsBS u) * (log z / log u) := by
  have hu' : (500 : ℝ) ≤ u := by exact_mod_cast hu
  have huz' : (u : ℝ) ≤ z := by exact_mod_cast huz
  have hP : ∀ p ∈ primesIco u z, (500 : ℝ) ≤ p := by
    intro p hp
    simp only [primesIco, mem_filter, mem_Ico] at hp
    exact_mod_cast le_trans hu hp.1.1
  have hsub : primesIco u z ⊆ Ico u z := filter_subset _ _
  -- split the product
  have hsplit : ∏ p ∈ primesIco u z, (1 - 1 / ((p : ℝ) - 1))⁻¹ =
      (∏ p ∈ primesIco u z, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))) *
      ∏ p ∈ primesIco u z, (1 - 1 / (p : ℝ))⁻¹ := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl (fun p hp => factor (by linarith [hP p hp]))
  -- first product
  have hA : ∏ p ∈ primesIco u z, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) ≤
      exp (1 / ((u : ℝ) - 2)) := by
    calc ∏ p ∈ primesIco u z, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))
        ≤ ∏ p ∈ primesIco u z, exp (1 / (((p : ℝ) - 2) * ((p : ℝ) - 1))) := by
          apply prod_le_prod₀
          · intro p hp; have := hP p hp
            have : 0 < (p : ℝ) * ((p : ℝ) - 2) := by nlinarith
            positivity
          · intro p hp; have h5 := hP p hp
            calc 1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)) ≤ exp (1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
                  linarith [Real.add_one_le_exp (1 / ((p : ℝ) * ((p : ℝ) - 2)))]
              _ ≤ exp (1 / (((p : ℝ) - 2) * ((p : ℝ) - 1))) := by
                  apply exp_le_exp.mpr
                  apply one_div_le_one_div_of_le (by nlinarith)
                  nlinarith
      _ = exp (∑ p ∈ primesIco u z, 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1))) := (exp_sum _ _).symm
      _ ≤ exp (∑ n ∈ Ico u z, 1 / (((n : ℝ) - 2) * ((n : ℝ) - 1))) := by
          apply exp_le_exp.mpr
          apply sum_le_sum_of_subset_of_nonneg hsub
          intro n hn _
          simp only [mem_Ico] at hn
          have : (500 : ℝ) ≤ n := by exact_mod_cast le_trans hu hn.1
          have : 0 < ((n : ℝ) - 2) * ((n : ℝ) - 1) := by nlinarith
          positivity
      _ ≤ exp (1 / ((u : ℝ) - 2)) := by
          apply exp_le_exp.mpr
          rw [tele1 u (by omega) z huz]
          have hz3 : (3 : ℝ) ≤ z := by linarith
          have : 0 ≤ 1 / ((z : ℝ) - 2) := by
            have : 0 < (z : ℝ) - 2 := by linarith
            positivity
          linarith
  have hA' : exp (1 / ((u : ℝ) - 2)) ≤ 1 + 1 / (0.996 * (u : ℝ) - 1) := by
    have h1 : 1 / ((u : ℝ) - 2) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    refine le_trans (exp_le_inv h1) ?_
    have e : (1 - 1 / ((u : ℝ) - 2))⁻¹ = 1 + 1 / ((u : ℝ) - 3) := by
      have a : (u : ℝ) - 2 ≠ 0 := by linarith
      have b : (u : ℝ) - 3 ≠ 0 := by linarith
      have c : (u : ℝ) - 2 - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [e]
    have : 1 / ((u : ℝ) - 3) ≤ 1 / (0.996 * (u : ℝ) - 1) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  -- second product
  have hB : ∏ p ∈ primesIco u z, (1 - 1 / (p : ℝ))⁻¹ ≤
      exp (∑ p ∈ primesIco u z, (1 : ℝ) / p) * exp (1 / ((u : ℝ) - 1)) := by
    calc ∏ p ∈ primesIco u z, (1 - 1 / (p : ℝ))⁻¹
        ≤ ∏ p ∈ primesIco u z, exp (1 / (p : ℝ) + 1 / (((p : ℝ) - 1) * (p : ℝ))) := by
          apply prod_le_prod₀
          · intro p hp; have h5 := hP p hp
            have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
            have : 0 < 1 - 1 / (p : ℝ) := by linarith
            positivity
          · intro p hp; have h5 := hP p hp
            have t0 : 0 ≤ 1 / (p : ℝ) := by positivity
            have t1 : 1 / (p : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (by linarith)
            refine le_trans (inv_one_sub_le t0 t1) (exp_le_exp.mpr ?_)
            have : (1 / (p : ℝ)) ^ 2 ≤ 1 / (((p : ℝ) - 1) * (p : ℝ)) := by
              rw [div_pow, one_pow]
              exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
            linarith
      _ = exp (∑ p ∈ primesIco u z, (1 / (p : ℝ) + 1 / (((p : ℝ) - 1) * (p : ℝ)))) :=
          (exp_sum _ _).symm
      _ = exp (∑ p ∈ primesIco u z, (1 : ℝ) / p) *
            exp (∑ p ∈ primesIco u z, 1 / (((p : ℝ) - 1) * (p : ℝ))) := by
          rw [sum_add_distrib, exp_add]
      _ ≤ exp (∑ p ∈ primesIco u z, (1 : ℝ) / p) * exp (1 / ((u : ℝ) - 1)) := by
          gcongr
          calc ∑ p ∈ primesIco u z, 1 / (((p : ℝ) - 1) * (p : ℝ))
              ≤ ∑ n ∈ Ico u z, 1 / (((n : ℝ) - 1) * (n : ℝ)) := by
                apply sum_le_sum_of_subset_of_nonneg hsub
                intro n hn _
                simp only [mem_Ico] at hn
                have : (500 : ℝ) ≤ n := by exact_mod_cast le_trans hu hn.1
                have : 0 < ((n : ℝ) - 1) * (n : ℝ) := by nlinarith
                positivity
            _ ≤ 1 / ((u : ℝ) - 1) := by
                rw [tele2 u (by omega) z huz]
                have : 0 ≤ 1 / ((z : ℝ) - 1) := by
                  have : 0 < (z : ℝ) - 1 := by linarith
                  positivity
                linarith
  -- the Mertens step
  have hlogu : 0 < log (u : ℝ) := Real.log_pos (by linarith)
  have hlogz : 0 < log (z : ℝ) := Real.log_pos (by linarith)
  set L := log (u : ℝ) with hL
  have hC : exp (∑ p ∈ primesIco u z, (1 : ℝ) / p) ≤
      (log z / L) * (1 + 1.5e-4 / L + 2.25e-8 / L ^ 2) := by
    calc exp (∑ p ∈ primesIco u z, (1 : ℝ) / p)
        ≤ exp (log (log z) - log L + 1.5e-4 / L) := exp_le_exp.mpr hM
      _ = (log z / L) * exp (1.5e-4 / L) := by
          rw [exp_add, exp_sub, exp_log hlogz, exp_log hlogu]
      _ ≤ (log z / L) * (1 + 1.5e-4 / L + 2.25e-8 / L ^ 2) := by
          gcongr
          have hL1 : (1 : ℝ) ≤ L := by
            rw [hL, Real.le_log_iff_exp_le (by linarith)]
            linarith [Real.exp_one_lt_d9]
          have : |1.5e-4 / L| ≤ 1 := by
            rw [abs_of_nonneg (by positivity), div_le_one (by linarith)]; linarith
          refine le_trans (exp_le_quad this) (le_of_eq ?_)
          rw [div_pow]; norm_num
  have hD : exp (1 / ((u : ℝ) - 1)) ≤ 1 + 1 / ((u : ℝ) - 1) + 1 / ((u : ℝ) - 1) ^ 2 := by
    have hu1 : 0 < (u : ℝ) - 1 := by linarith
    have : |1 / ((u : ℝ) - 1)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), div_le_one hu1]
      linarith
    refine le_trans (exp_le_quad this) (le_of_eq ?_)
    rw [div_pow, one_pow]
  -- assemble
  have pos1 : 0 ≤ exp (1 / ((u : ℝ) - 2)) := (exp_pos _).le
  rw [hsplit]
  have hprodB_nonneg : 0 ≤ ∏ p ∈ primesIco u z, (1 - 1 / (p : ℝ))⁻¹ := by
    apply prod_nonneg; intro p hp; have h5 := hP p hp
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have : 0 < 1 - 1 / (p : ℝ) := by linarith
    positivity
  have step1 := mul_le_mul (le_trans hA hA') hB hprodB_nonneg (by
    have : 0 < 0.996 * (u : ℝ) - 1 := by linarith
    positivity)
  have step2 : exp (∑ p ∈ primesIco u z, (1 : ℝ) / p) * exp (1 / ((u : ℝ) - 1)) ≤
      (log z / L) * (1 + 1.5e-4 / L + 2.25e-8 / L ^ 2) *
        (1 + 1 / ((u : ℝ) - 1) + 1 / ((u : ℝ) - 1) ^ 2) :=
    mul_le_mul hC hD (exp_pos _).le (by positivity)
  have step3 := mul_le_mul_of_nonneg_left step2 (by
    have : 0 < 0.996 * (u : ℝ) - 1 := by linarith
    positivity : (0 : ℝ) ≤ 1 + 1 / (0.996 * (u : ℝ) - 1))
  refine le_trans step1 (le_trans step3 (le_of_eq ?_))
  unfold epsBS
  rw [← hL]
  ring

/-- Display (9) from Lemma 7, for any u ≥ 3 and z ≥ u. -/
theorem mertensDiff_of_lemma7 (M : ℝ) (u z : ℕ) (hu : 3 ≤ u) (huz : u ≤ z)
    (h7 : Lemma7Bounds M u z) : MertensDiff u z := by
  obtain ⟨hz, hu7⟩ := h7
  have hsplit : ∑ p ∈ (range z).filter Nat.Prime, (1 : ℝ) / p =
      ∑ p ∈ (range u).filter Nat.Prime, (1 : ℝ) / p + ∑ p ∈ primesIco u z, (1 : ℝ) / p := by
    rw [primesIco, ← sum_union]
    · congr 1
      ext p; simp only [mem_filter, mem_range, mem_union, mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h : p < u
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr ⟨⟨by omega, h1⟩, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨⟨h1, h3⟩, h2⟩)
        · exact ⟨by omega, h2⟩
        · exact ⟨h3, h2⟩
    · rw [disjoint_left]
      intro p h1 h2
      simp only [mem_filter, mem_range, mem_Ico] at h1 h2
      omega
  have hu' : (3 : ℝ) ≤ u := by exact_mod_cast hu
  have huz' : (u : ℝ) ≤ z := by exact_mod_cast huz
  have hlogu : 0 < log (u : ℝ) := Real.log_pos (by linarith)
  have hlz : log (u : ℝ) ≤ log z := Real.log_le_log (by linarith) huz'
  have h1 : 4.47e-9 / log (z : ℝ) ≤ 4.47e-9 / log (u : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hlogu hlz
  have h2 : 4.47e-9 / log (u : ℝ) + 1.4998e-4 / log u ≤ 1.5e-4 / log u := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hlogu.le
  unfold MertensDiff
  linarith

/-- **Lemma 8, CONDITIONAL ON Lemma 7's two bounds.** -/
theorem lemma8 (M : ℝ) (u z : ℕ) (hu : 500 ≤ u) (huz : u ≤ z) (h7 : Lemma7Bounds M u z) :
    ∏ p ∈ primesIco u z, (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤ (1 + epsBS u) * (log z / log u) :=
  lemma8_of_mertensDiff u z hu huz (mertensDiff_of_lemma7 M u z (by omega) huz h7)

end LeanLab.BS2022GRH
