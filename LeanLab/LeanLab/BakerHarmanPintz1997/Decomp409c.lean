/-
P0069 pages 30 and 31, the three pm ranges in the written proof of Lemma 15.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp409b
import LeanLab.BakerHarmanPintz1997.DecompJ612

noncomputable section
namespace LeanLab.BakerHarmanPintz1997.Decomp409c
open Finset Decomp1518
attribute [local instance] Classical.propDecidable

/-- Page 31, index zero is pm at most x to 0.4, index one is the remaining pm
at most x to 0.46, and index two is pm above x to 0.46. -/
def primeRegion (x : ℝ) (m p : ℕ) : Fin 3 :=
  if ((m * p : ℕ) : ℝ) ≤ x ^ (0.4 : ℝ) then 0
  else if ((m * p : ℕ) : ℝ) ≤ x ^ (0.46 : ℝ) then 1 else 2

/-- Page 31, the prime error sum restricted to one of its three pm ranges. -/
def primePart (j : Fin 3) (x : ℝ) (a b : ℕ → ℂ) (M N w z : ℝ) (k : ℕ) : ℂ :=
  ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
    if m * n ∣ k then a m * b n *
      ∑ p ∈ ((k / (m * n)).primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).filter
          (fun p => primeRegion x m p = j), psi (k / (m * n) / p) (p : ℝ)
    else 0

/-- Page 31, the three restrictions partition the complete prime error sum exactly. -/
theorem primePart_sum (x : ℝ) (a b : ℕ → ℂ) (M N w z : ℝ) (k : ℕ) :
    jsum a b M N w z k = primePart 0 x a b M N w z k +
      primePart 1 x a b M N w z k + primePart 2 x a b M N w z k := by
  unfold jsum primePart
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hd : m * n ∣ k
  · simp only [hd, ite_true]
    rw [← mul_add, ← mul_add]
    congr 1
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    generalize primeRegion x m p = r
    fin_cases r <;> simp
  · simp [hd]

/-- Page 31, the displayed cofactor bound in the large pm case. -/
theorem large_prime_cofactor {x m n p h : ℝ} (hx : 0 < x)
    (hm : 0 ≤ m) (hp0 : 0 ≤ p) (hh : 0 ≤ h) (hmn : m ≤ n)
    (hprod : m * n * p * h ≤ x) (hp : p ≤ x ^ (0.1 : ℝ))
    (hmp : x ^ (0.46 : ℝ) < m * p) : h ≤ x ^ (0.18 : ℝ) := by
  have hm2 : m ^ 2 ≤ m * n := by nlinarith [mul_nonneg hm (sub_nonneg.mpr hmn)]
  have hb : h * (m * p) ^ 2 ≤ x ^ (1.1 : ℝ) := by
    calc
      _ = m ^ 2 * (p ^ 2 * h) := by ring
      _ ≤ (m * n) * (p ^ 2 * h) := mul_le_mul_of_nonneg_right hm2 (by positivity)
      _ = (m * n * p * h) * p := by ring
      _ ≤ x * x ^ (0.1 : ℝ) := mul_le_mul hprod hp hp0 hx.le
      _ = x ^ (1.1 : ℝ) := by
        calc
          _ = x ^ (1 : ℝ) * x ^ (0.1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ ((1 : ℝ) + 0.1) := (Real.rpow_add hx _ _).symm
          _ = _ := by norm_num
  exact cond422_z_le hx hmp hb

/-- Page 31, the two ratios in the large pm case, with the dyadic factor two retained. -/
theorem large_prime_ratios {x m n p : ℝ} (hx : 0 < x) (hn : 0 < n)
    (hp0 : 0 ≤ p) (hmn : m ≤ n) (hp : p ≤ x ^ (0.1 : ℝ))
    (hnx : n ≤ 2 * x ^ (0.4 : ℝ)) (hmp : x ^ (0.46 : ℝ) ≤ m * p) :
    m * p / n ≤ x ^ (0.1 : ℝ) ∧ n / (m * p) ≤ 2 * x ^ (-0.06 : ℝ) := by
  have hpow : 0 < x ^ (0.46 : ℝ) := Real.rpow_pos_of_pos hx _
  refine ⟨?_, ?_⟩
  · calc
      _ ≤ p := (div_le_iff₀ hn).mpr (by nlinarith [mul_le_mul_of_nonneg_right hmn hp0])
      _ ≤ _ := hp
  · calc
      _ ≤ (2 * x ^ (0.4 : ℝ)) / x ^ (0.46 : ℝ) := by gcongr
      _ = 2 * x ^ (-0.06 : ℝ) := by
        rw [mul_div_assoc, ← Real.rpow_sub hx]
        congr 1
        norm_num

/-- LEAF. OPEN. Page 31, the contribution with pm at most x to 0.4.
This is the terminating repeated Buchstab procedure, with the divisor bounded
coefficients treated as in the proof of Lemma13. It is only one prime error range. -/
theorem small_prime_transfer :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N z : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      Ev (fun x => z x = x ^ (0.1 : ℝ) ∧ M x ≤ N x ∧ N x ≤ x ^ (0.4 : ℝ)) →
      Holds42 ε fun x k => primePart 0 x (a x) (b x) (M x) (N x) (wof x) (z x) k := by
  sorry

/-- LEAF. OPEN. Page 31, x to 0.4 below pm at most x to 0.46.
The source groups m with p and invokes Lemma13 after removing the dependent cutoff.
This statement retains only that middle range, not the whole Lemma15 sum. -/
theorem middle_prime_transfer :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N z : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      Ev (fun x => z x = x ^ (0.1 : ℝ) ∧ M x ≤ N x ∧ N x ≤ x ^ (0.4 : ℝ)) →
      Holds42 ε fun x k => primePart 1 x (a x) (b x) (M x) (N x) (wof x) (z x) k := by
  sorry

/-- LEAF. OPEN. Page 31, pm above x to 0.46.
The source uses the cofactor upper bound x to 0.18 and the two displayed ratios,
then Theorem4. This statement concerns only the large pm prime error range. -/
theorem large_prime_transfer :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N z : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      Ev (fun x => z x = x ^ (0.1 : ℝ) ∧ M x ≤ N x ∧ N x ≤ x ^ (0.4 : ℝ)) →
      Holds42 ε fun x k => primePart 2 x (a x) (b x) (M x) (N x) (wof x) (z x) k := by
  sorry

/-- Pages 30 and 31, exact Lemma15 assembled from the smaller prime error ranges.
CONDITIONAL ON the three range leaves here and the three Lemma12 leaves in Decomp409b.
The existing Buchstab core and Holds42 addition are proved inputs. -/
theorem lemma15_decomposed : Lemma15 := by
  obtain ⟨εl, hεl, hl⟩ := lemma12_ev Decomp409b.lemma12_decomposed
  obtain ⟨εs, hεs, hs⟩ := small_prime_transfer
  obtain ⟨εm, hεm, hm⟩ := middle_prime_transfer
  obtain ⟨εg, hεg, hg⟩ := large_prime_transfer
  refine ⟨min εl (min εs (min εm εg)), lt_min hεl (lt_min hεs (lt_min hεm hεg)), ?_⟩
  intro ε hε hεsmall
  have hel : ε < εl := hεsmall.trans_le (min_le_left _ _)
  have hes : ε < εs := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hem : ε < εm := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heg : ε < εg := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  apply lemma15_core hε.le (hl ε hε hel)
  intro B a b M N z ha hb hcond
  have h0 := hs ε hε hes B a b M N z ha hb hcond
  have h1 := hm ε hε hem B a b M N z ha hb hcond
  have h2 := hg ε hε heg B a b M N z ha hb hcond
  have hadd := holds42_add (holds42_add h0 h1) h2
  apply holds42_congr_ev (c := fun x k =>
    primePart 0 x (a x) (b x) (M x) (N x) (wof x) (z x) k +
    primePart 1 x (a x) (b x) (M x) (N x) (wof x) (z x) k +
    primePart 2 x (a x) (b x) (M x) (N x) (wof x) (z x) k) _ hadd
  exact ⟨0, fun x hx k hk => (primePart_sum x (a x) (b x) (M x) (N x) (wof x) (z x) k).symm⟩

#print axioms primeRegion
#print axioms primePart
#print axioms primePart_sum
#print axioms large_prime_cofactor
#print axioms large_prime_ratios
#print axioms small_prime_transfer
#print axioms middle_prime_transfer
#print axioms large_prime_transfer
#print axioms lemma15_decomposed

end LeanLab.BakerHarmanPintz1997.Decomp409c
