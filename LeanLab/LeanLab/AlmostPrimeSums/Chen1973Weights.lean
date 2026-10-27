/-
AI-written Lean code, OpenAI Codex, task33, 2026-10-23, T1.
P0002 Chen 1973, p. 162 and pp. 170 to 171.
Elementary support and normalization of the weights used in display 24.
Goldbach is open.
-/
import LeanLab.AlmostPrimeSums.Chen1973Display24

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.AlmostPrimeSums.Chen1973Weights

open Chen1973Display24

lemma sv_mem_of_dvd {x D m d : ℕ} (hm : m ∈ sv x D) (hdm : d ∣ m) : d ∈ sv x D := by
  obtain ⟨hmI, hsq, hcop⟩ := mem_filter.mp hm
  obtain ⟨hm1, hmD⟩ := mem_Icc.mp hmI
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdm hm1
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hd0, (Nat.le_of_dvd hm1 hdm).trans hmD⟩,
    hsq.squarefree_of_dvd hdm, hcop.coprime_dvd_left hdm⟩

lemma lamC_eq_zero_of_not_mem {x D d : ℕ} (hd : d ∉ sv x D) : lamC x D d = 0 := by
  have he : (sv x D).filter (d ∣ ·) = ∅ := by
    apply eq_empty_of_forall_notMem
    intro m hm
    exact hd (sv_mem_of_dvd (mem_filter.mp hm).1 (mem_filter.mp hm).2)
  simp [lamC, he]

lemma lamC_one {x D : ℕ} (hx : Even x) (hD : 1 ≤ D) : lamC x D 1 = 1 := by
  have hS : Sv x D ≠ 0 := by linarith [one_le_Sv hx hD]
  unfold lamC
  simp only [Nat.totient_one, Nat.cast_one, one_mul, Nat.one_dvd, filter_true, Nat.div_one]
  have he : ∀ m : ℕ, ((μ m : ℤ) : ℝ) * (((μ m : ℤ) : ℝ) / (Sv x D * ψ m)) =
      (((μ m : ℤ) : ℝ) ^ 2 / ψ m) / Sv x D := by
    intro m
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [he]
  rw [← sum_div, ← Sv, div_self hS]

lemma psi_mul_of_squarefree {a b : ℕ} (hab : Squarefree (a * b)) :
    ψ (a * b) = ψ a * ψ b := by
  have hcop := (Nat.squarefree_mul_iff.mp hab).1
  unfold ψ
  rw [hcop.primeFactors_mul, prod_union hcop.disjoint_primeFactors]

lemma Sv_eq_sum_inv (x D : ℕ) : Sv x D = ∑ m ∈ sv x D, 1 / ψ m := by
  unfold Sv
  apply sum_congr rfl
  intro m hm
  have hsq := (mem_filter.mp hm).2.1
  have hmu : ((μ m : ℤ) : ℝ) ^ 2 = 1 := by
    exact_mod_cast moebius_sq_eq_one_of_squarefree hsq
  rw [hmu]

lemma weighted_multiples_le_Sv {x D d : ℕ} (hx : Even x) (hd : d ∈ sv x D) :
    (d.totient : ℝ) * (∑ m ∈ (sv x D).filter (d ∣ ·), 1 / ψ m) ≤ Sv x D := by
  let M := (sv x D).filter (d ∣ ·)
  let P := d.divisors ×ˢ M
  let F : ℕ × ℕ → ℕ := fun z => z.1 * (z.2 / d)
  have hdpos : 0 < d := (mem_Icc.mp (mem_filter.mp hd).1).1
  have hdsq : Squarefree d := (mem_filter.mp hd).2.1
  have hem : ∀ m ∈ M, d * (m / d) = m := by
    intro m hm
    exact Nat.mul_div_cancel' (mem_filter.mp hm).2
  have hcop : ∀ m ∈ M, d.Coprime (m / d) := by
    intro m hm
    have hsq := (mem_filter.mp (mem_filter.mp hm).1).2.1
    rw [← hem m hm] at hsq
    exact (Nat.squarefree_mul_iff.mp hsq).1
  have hF : ∀ z ∈ P, F z ∈ sv x D := by
    intro z hz
    obtain ⟨hr, hm⟩ := mem_product.mp hz
    have hrd := Nat.dvd_of_mem_divisors hr
    apply sv_mem_of_dvd (mem_filter.mp hm).1
    change z.1 * (z.2 / d) ∣ z.2
    simpa only [hem z.2 hm] using Nat.mul_dvd_mul_right hrd (z.2 / d)
  have hgcd : ∀ z ∈ P, (F z).gcd d = z.1 := by
    intro z hz
    obtain ⟨hr, hm⟩ := mem_product.mp hz
    dsimp [F]
    rw [mul_comm]
    exact Nat.gcd_mul_of_coprime_of_dvd (hcop z.2 hm).symm (Nat.dvd_of_mem_divisors hr)
  have hinj : Set.InjOn F (P : Set (ℕ × ℕ)) := by
    intro z hz w hw he
    have hr := congrArg (fun n => n.gcd d) he
    rw [hgcd z hz, hgcd w hw] at hr
    apply Prod.ext hr
    have hzP := mem_product.mp hz
    have hwP := mem_product.mp hw
    have hrpos : 0 < z.1 := Nat.pos_of_mem_divisors hzP.1
    have hquot : z.2 / d = w.2 / d := by
      change z.1 * (z.2 / d) = w.1 * (w.2 / d) at he
      rw [← hr] at he
      exact Nat.eq_of_mul_eq_mul_left hrpos he
    rw [← hem z.2 hzP.2, ← hem w.2 hwP.2, hquot]
  have hterm : ∀ z ∈ P, 1 / ψ (F z) = ψ (d / z.1) / ψ z.2 := by
    intro z hz
    obtain ⟨hr, hm⟩ := mem_product.mp hz
    have hfac : (d / z.1) * F z = z.2 := by
      dsimp [F]
      calc
        d / z.1 * (z.1 * (z.2 / d)) = (z.1 * (d / z.1)) * (z.2 / d) := by ring
        _ = d * (z.2 / d) := by rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hr)]
        _ = z.2 := hem z.2 hm
    have hmsq : Squarefree z.2 := (mem_filter.mp (mem_filter.mp hm).1).2.1
    have hpsi : ψ z.2 = ψ (d / z.1) * ψ (F z) := by
      rw [← hfac] at hmsq ⊢
      exact psi_mul_of_squarefree hmsq
    have hpm : ψ z.2 ≠ 0 :=
      (psi_pos_of_coprime hx (mem_filter.mp (mem_filter.mp hm).1).2.2).ne'
    have hpf : ψ (F z) ≠ 0 := (psi_pos_of_coprime hx (mem_filter.mp (hF z hz)).2.2).ne'
    apply (eq_div_iff hpm).mpr
    rw [hpsi]
    field_simp
  have hsum : (∑ z ∈ P, 1 / ψ (F z)) ≤ Sv x D := by
    rw [Sv_eq_sum_inv]
    calc
      _ = ∑ n ∈ P.image F, 1 / ψ n := (sum_image hinj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg
        (by intro n hn; obtain ⟨z, hz, rfl⟩ := mem_image.mp hn; exact hF z hz)
        (by intro n hn _; exact div_nonneg (by norm_num) (psi_pos_of_coprime hx (mem_filter.mp hn).2.2).le)
  have heq : ∑ z ∈ P, 1 / ψ (F z) =
      (d.totient : ℝ) * ∑ m ∈ M, 1 / ψ m := by
    rw [sum_congr rfl hterm]
    change (∑ z ∈ d.divisors ×ˢ M, ψ (d / z.1) / ψ z.2) = _
    rw [sum_product]
    simp only [div_eq_mul_inv, one_mul]
    rw [← sum_mul_sum, Nat.sum_div_divisors, ← totient_eq_sum_psi hdsq]
  rw [heq] at hsum
  exact hsum

/-- Chen p. 162: the Selberg weights have absolute value at most one. -/
theorem abs_lamC_le_one {x D : ℕ} (hx : Even x) (hD : 1 ≤ D) (d : ℕ) :
    |lamC x D d| ≤ 1 := by
  by_cases hd : d ∈ sv x D
  · have hS : 0 < Sv x D := lt_of_lt_of_le zero_lt_one (one_le_Sv hx hD)
    have ht := weighted_multiples_le_Sv hx hd
    have hmu : ∀ n : ℕ, |((μ n : ℤ) : ℝ)| ≤ 1 := by
      intro n
      exact_mod_cast (abs_moebius_le_one (n := n))
    have hterm : ∀ m ∈ (sv x D).filter (d ∣ ·),
        |((μ (m / d) : ℤ) : ℝ) * (((μ m : ℤ) : ℝ) / (Sv x D * ψ m))| ≤
          (1 / ψ m) / Sv x D := by
      intro m hm
      have hp : 0 < ψ m := psi_pos_of_coprime hx (mem_filter.mp (mem_filter.mp hm).1).2.2
      rw [abs_mul, abs_div, abs_of_pos (mul_pos hS hp)]
      calc
        _ ≤ 1 * (1 / (Sv x D * ψ m)) := by gcongr <;> exact hmu _
        _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
    unfold lamC
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ (d.totient : ℝ) * ∑ m ∈ (sv x D).filter (d ∣ ·),
          |((μ (m / d) : ℤ) : ℝ) * (((μ m : ℤ) : ℝ) / (Sv x D * ψ m))| := by
        gcongr
        exact abs_sum_le_sum_abs _ _
      _ ≤ (d.totient : ℝ) * ∑ m ∈ (sv x D).filter (d ∣ ·), (1 / ψ m) / Sv x D := by
        gcongr with m hm
        exact hterm m hm
      _ = ((d.totient : ℝ) * ∑ m ∈ (sv x D).filter (d ∣ ·), 1 / ψ m) / Sv x D := by
        rw [← sum_div, mul_div_assoc]
      _ ≤ 1 := (div_le_one hS).mpr ht
  · rw [lamC_eq_zero_of_not_mem hd, abs_zero]
    norm_num

end LeanLab.AlmostPrimeSums.Chen1973Weights

#print axioms LeanLab.AlmostPrimeSums.Chen1973Weights.sv_mem_of_dvd

#print axioms LeanLab.AlmostPrimeSums.Chen1973Weights.lamC_eq_zero_of_not_mem

#print axioms LeanLab.AlmostPrimeSums.Chen1973Weights.lamC_one

open LeanLab.AlmostPrimeSums.Chen1973Display24 LeanLab.AlmostPrimeSums.Chen1973Weights

example : lamC 2 1 1 = 1 := lamC_one even_two (by norm_num)

example : lamC 2 1 3 = 0 := lamC_eq_zero_of_not_mem (by simp [sv])

#print axioms LeanLab.AlmostPrimeSums.Chen1973Weights.psi_mul_of_squarefree

#print axioms LeanLab.AlmostPrimeSums.Chen1973Weights.Sv_eq_sum_inv

#print axioms LeanLab.AlmostPrimeSums.Chen1973Weights.weighted_multiples_le_Sv

#print axioms LeanLab.AlmostPrimeSums.Chen1973Weights.abs_lamC_le_one

example : |lamC 2 1 1| ≤ 1 := abs_lamC_le_one even_two (by norm_num) 1
