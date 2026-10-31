import LeanLab.RieselVaughan1983.Lemma2Convergence
import LeanLab.RieselVaughan1983.Euler23

/-! The zeroth moment on page 50, equation 3.9.
AI wrote the Lean code. Binary Goldbach is OPEN. -/
namespace LeanLab.RieselVaughan1983.Lemma2
open Finset Real
noncomputable section

def G (w : ℝ) : ℝ := ∑' n : ℕ, g n * (n : ℝ) ^ (-w)
def localG (p : ℕ) : ℝ := 1 + g p + g (p ^ 2) + g (p ^ 3)

lemma abs_g_le_mass (n : ℕ) : |g n| ≤ mass n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [mass]
  · have h := root_ge_one n hn
    unfold mass
    nlinarith [abs_nonneg (g n)]

lemma g_summable_norm : Summable (fun n : ℕ => ‖g n‖) := by
  apply mass_summable.of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  simpa only [Real.norm_eq_abs] using abs_g_le_mass n

lemma g_prime_pow_hasSum (p : ℕ) (hp : p.Prime) :
    HasSum (fun e : ℕ => g (p ^ e)) (localG p) := by
  have hz : ∀ e ∉ ({0, 1, 2, 3} : Finset ℕ), g (p ^ e) = 0 := by
    intro e he
    have he4 : 4 ≤ e := by
      simp only [mem_insert, mem_singleton, not_or] at he
      omega
    exact g_prime_pow_ge_four p e hp he4
  convert hasSum_sum_of_ne_finset_zero hz using 1
  · simp [localG, g_multiplicative.map_one, add_assoc]
  · infer_instance

lemma localG_two : localG 2 = 1 / 2 := by
  norm_num [localG, g_two, g_four, g_eight]

lemma localG_odd_inverse (p : ℕ) (hp : p.Prime) (h2 : 2 < p) :
    localG p * (1 - 1 / ((p : ℝ) - 1) ^ 2) = 1 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2 : (p : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt h2))
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hp.one_lt))
  rw [localG, g_odd_prime p hp h2, g_odd_prime_sq p hp h2, g_odd_prime_cube p hp h2]
  field_simp
  <;> ring

lemma hasProd_localG :
    HasProd (Set.mulIndicator {p : ℕ | p.Prime} localG) (∑' n : ℕ, g n) := by
  have h := EulerProduct.eulerProduct_hasProd_mulIndicator (f := fun n => g n)
    g_multiplicative.map_one (fun h => g_multiplicative.map_mul_of_coprime h)
    g_summable_norm (by simp)
  convert h using 1
  funext p
  by_cases hp : p.Prime
  · rw [Set.mulIndicator_of_mem (show p ∈ {p : ℕ | p.Prime} from hp), Set.mulIndicator_of_mem (show p ∈ {p : ℕ | p.Prime} from hp),
      (g_prime_pow_hasSum p hp).tsum_eq]
  · rw [Set.mulIndicator_of_notMem (show p ∉ {p : ℕ | p.Prime} from hp), Set.mulIndicator_of_notMem (show p ∉ {p : ℕ | p.Prime} from hp)]

lemma local_product_identity (n : ℕ) :
    (Set.mulIndicator {p : ℕ | p.Prime} localG n) *
      (Set.mulIndicator {p : ℕ | p.Prime} (fun p => 1 + Euler23.hq 1 p) n) =
      if n = 2 then (1 / 2 : ℝ) else 1 := by
  by_cases hp : n.Prime
  · rw [Set.mulIndicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hp), Set.mulIndicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hp)]
    by_cases h2 : n = 2
    · subst n
      simp [localG_two, Euler23.hq]
    · rw [if_neg h2, Euler23.hq_one_prime hp (by have := hp.two_le; omega)]
      simpa only [sub_eq_add_neg] using localG_odd_inverse n hp (by have := hp.two_le; omega)
  · rw [Set.mulIndicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hp), Set.mulIndicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hp)]
    have h2 : n ≠ 2 := by intro h; subst n; exact hp Nat.prime_two
    simp [h2]

lemma tsum_g_mul_twinC : (∑' n : ℕ, g n) * LeanLab.ChenExplicit.twinC = 1 / 2 := by
  have ht := Euler23.hasProd_hq 1
  rw [Euler23.tsum_h1_eq_twinC] at ht
  have h := hasProd_localG.mul ht
  have he : (fun n => (Set.mulIndicator {p : ℕ | p.Prime} localG n) *
      (Set.mulIndicator {p : ℕ | p.Prime} (fun p => 1 + Euler23.hq 1 p) n)) =
      (fun n => if n = 2 then (1 / 2 : ℝ) else 1) := funext local_product_identity
  rw [he] at h
  exact h.unique (hasProd_ite_eq (2 : ℕ) (1 / 2 : ℝ))

/-- Equation 3.9 with the paper's C equal to twice twinC. -/
theorem G_zero : G 0 = 1 / Ctw := by
  have h := tsum_g_mul_twinC
  have hC := Ctw_pos.ne'
  simp only [G, neg_zero, Real.rpow_zero, mul_one]
  apply (eq_div_iff hC).mpr
  unfold Ctw
  nlinarith

end
end LeanLab.RieselVaughan1983.Lemma2

#print axioms LeanLab.RieselVaughan1983.Lemma2.abs_g_le_mass
#print axioms LeanLab.RieselVaughan1983.Lemma2.g_summable_norm
#print axioms LeanLab.RieselVaughan1983.Lemma2.g_prime_pow_hasSum
#print axioms LeanLab.RieselVaughan1983.Lemma2.localG_two
#print axioms LeanLab.RieselVaughan1983.Lemma2.localG_odd_inverse
#print axioms LeanLab.RieselVaughan1983.Lemma2.hasProd_localG
#print axioms LeanLab.RieselVaughan1983.Lemma2.local_product_identity
#print axioms LeanLab.RieselVaughan1983.Lemma2.tsum_g_mul_twinC
#print axioms LeanLab.RieselVaughan1983.Lemma2.G_zero
