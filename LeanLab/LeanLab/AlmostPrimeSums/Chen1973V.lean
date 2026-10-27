/-
AI-written Lean code, Claude, 2026-10-20, session 20261020T2217Z-cloud52, unit U-6758, track T1.
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176, p. 171, display (25), read from the lab copy
papers/P0002.pdf, page images.

Chen sets `V_k(x) = ∑_{n ≤ x, (n,k)=1} μ²(n)/φ(n)`, proves `V_k(x) ≥ φ(k) log x / k`, and uses it in
`S = ∑_{k ≤ z, (k,x)=1} μ²(k)/φ(k) ∏_{p∣k} (1 + 1/(p-2)) ≥ ∑_{q ≤ z, (q,x)=1} μ²(q)/(ψ(q)φ(q)) ·
φ(qx)/(qx) · log(z/q)`, `ψ(q) = ∏_{p∣q}(p-2)`, `z = (x^{1/2-ε})^{1/2}`. This file proves both
steps for every real `z ≥ 0`, unconditionally; the final asymptotic equality of (25), the Euler
product evaluation `(1/8 - ε/4) log x / C_x + O(1)`, is Mertens-type analysis not done here.

`V_k(x) ≥ φ(k) log x / k` is the lab's PROVED `RieselVaughan1983.MuPhi.log_le_mu_phi_sum` of
P0032, unit U-6712, restated in Chen's form; it is a HELPER, not new work.
Binary Goldbach is OPEN.
-/
import LeanLab.AlmostPrimeSums.Chen1973Lemmas
import LeanLab.RieselVaughan1983.MuPhiSum

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.AlmostPrimeSums.Chen1973V

open LeanLab.AlmostPrimeSums.Chen1973Lemmas

/-- Chen's `V_k(x) = ∑_{n ≤ x, (n,k)=1} μ²(n)/φ(n)`. -/
def V (k : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n.Coprime k), ((μ n : ℤ) : ℝ) ^ 2 / (n.totient : ℝ)

/-- **Chen p. 171, `V_k(x) ≥ φ(k) log x / k`**, for `k ≥ 1`, `x ≥ 0`. HELPER: the lab's
`log_le_mu_phi_sum` of P0032 rearranged. -/
theorem chen_V_lower (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x) :
    (k.totient : ℝ) * log x / k ≤ V k x := by
  have h := LeanLab.RieselVaughan1983.MuPhi.log_le_mu_phi_sum k hk x hx
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
  rw [div_le_iff₀ hk0]
  unfold V
  rw [div_mul_eq_mul_div, le_div_iff₀ hφ] at h
  linarith

/-- The exchange of summation `∑_{k ≤ N} ∑_{qr = k} h(q,r) = ∑_{q ≤ N} ∑_{r ≤ N/q} h(q,r)`,
the proof of Mathlib's `sum_Ioc_mul_eq_sum_sum` for a general summand. -/
theorem sum_antidiag_swap (h : ℕ × ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Ioc 0 N, ∑ y ∈ k.divisorsAntidiagonal, h y =
      ∑ q ∈ Ioc 0 N, ∑ r ∈ Ioc 0 (N / q), h (q, r) := by
  trans ∑ y ∈ Ioc 0 N ×ˢ Ioc 0 N with y.1 * y.2 ≤ N, h y
  · trans ∑ k ∈ Ioc 0 N, ∑ y ∈ Ioc 0 N ×ˢ Ioc 0 N with y.1 * y.2 = k, h y
    · refine sum_congr rfl fun k hk => ?_
      simp only [mem_Ioc] at hk
      rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hk.1.ne' hk.2]
    · simp_rw [sum_filter]
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => (by simp_all)
  · rw [sum_filter, sum_product]
    refine sum_congr rfl fun q hq => ?_
    rw [← sum_filter]
    congr 1
    ext r
    simp only [mem_filter, mem_Ioc] at hq ⊢
    constructor
    · rintro ⟨⟨h0, -⟩, h⟩
      exact ⟨h0, (Nat.le_div_iff_mul_le hq.1).mpr (by linarith [Nat.mul_comm q r])⟩
    · rintro ⟨h0, h⟩
      have h' := (Nat.le_div_iff_mul_le hq.1).mp h
      refine ⟨⟨h0, ?_⟩, by linarith [Nat.mul_comm q r]⟩
      nlinarith

lemma Ioc_zero_eq_Icc_one (n : ℕ) : Ioc 0 n = Icc 1 n := by
  ext m; simp only [mem_Ioc, mem_Icc]; omega

/-- Chen's weight `1/(ψ(q)φ(q))` on squarefree `q`, as `∏_{p∣q} 1/((p-2)(p-1))`. -/
def F (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1))

lemma F_nonneg (q : ℕ) : 0 ≤ F q := by
  unfold F
  refine prod_nonneg fun p hp => ?_
  have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  apply one_div_nonneg.mpr
  apply mul_nonneg <;> linarith

/-- Chen's `S` with summation limit `z`, coprimality to `x`. -/
def S (x : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ Icc 1 ⌊z⌋₊, if Squarefree k ∧ k.Coprime x then
    ∏ p ∈ k.primeFactors, (1 / ((p : ℝ) - 1) * (1 + 1 / ((p : ℝ) - 2))) else 0

/-- **Chen 1973, display (25), the inequality step, PROVED**: for `x ≥ 1` and real `z ≥ 0`,
`S ≥ ∑_{q ≤ z, (q,x)=1} μ²(q)/(ψ(q)φ(q)) · φ(qx)/(qx) · log(z/q)`. -/
theorem chen25_lower (x : ℕ) (hx : 1 ≤ x) (z : ℝ) (hz : 0 ≤ z) :
    ∑ q ∈ Icc 1 ⌊z⌋₊, (if Squarefree q ∧ q.Coprime x then F q else 0) *
        (((q * x).totient : ℝ) * log (z / q) / (q * x : ℕ)) ≤ S x z := by
  classical
  set N := ⌊z⌋₊
  -- the antidiagonal form of `S`
  have hS : S x z = ∑ k ∈ Ioc 0 N, ∑ y ∈ k.divisorsAntidiagonal,
      (if Squarefree (y.1 * y.2) ∧ (y.1 * y.2).Coprime x then
        F y.1 * ∏ p ∈ y.2.primeFactors, 1 / ((p : ℝ) - 1) else 0) := by
    unfold S
    rw [Ioc_zero_eq_Icc_one]
    refine sum_congr rfl fun k _ => ?_
    have hk : ∀ y ∈ k.divisorsAntidiagonal, y.1 * y.2 = k := fun y hy =>
      (Nat.mem_divisorsAntidiagonal.mp hy).1
    rw [sum_congr rfl fun y hy => by rw [hk y hy]]
    split_ifs with hc
    · rw [chen25_pointwise hc.1]; rfl
    · simp
  rw [hS, sum_antidiag_swap, Ioc_zero_eq_Icc_one]
  refine sum_le_sum fun q hq => ?_
  have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
  have hqx : 1 ≤ q * x := Nat.one_le_iff_ne_zero.mpr (by positivity)
  split_ifs with hc
  swap
  · rw [zero_mul]
    refine sum_nonneg fun r _ => ?_
    rw [if_neg]
    rintro ⟨hsq, hcop⟩
    exact hc ⟨Squarefree.of_mul_left hsq, Nat.Coprime.coprime_dvd_left (dvd_mul_right q r) hcop⟩
  -- the inner sum is `V_{qx}(z/q)`
  have hinner : ∑ r ∈ Ioc 0 (N / q), (if Squarefree (q * r) ∧ (q * r).Coprime x then
      F q * ∏ p ∈ r.primeFactors, 1 / ((p : ℝ) - 1) else 0) = F q * V (q * x) (z / q) := by
    unfold V
    rw [mul_sum, sum_filter, Ioc_zero_eq_Icc_one, Nat.floor_div_natCast]
    refine sum_congr rfl fun r hr => ?_
    have hr1 : 1 ≤ r := (mem_Icc.mp hr).1
    by_cases hsr : Squarefree r ∧ r.Coprime (q * x)
    · have hcop : (q * r).Coprime x := Nat.coprime_mul_iff_left.mpr ⟨hc.2, Nat.Coprime.coprime_dvd_right
        (dvd_mul_left x q) hsr.2⟩
      have hsq : Squarefree (q * r) := Nat.squarefree_mul_iff.mpr
        ⟨(Nat.Coprime.coprime_dvd_right (dvd_mul_right q x) hsr.2).symm, hc.1, hsr.1⟩
      have hmu : ((μ r : ℤ) : ℝ) ^ 2 = 1 := by
        exact_mod_cast moebius_sq_eq_one_of_squarefree hsr.1
      rw [if_pos ⟨hsq, hcop⟩, if_pos hsr.2, ← chen_inv_totient hsr.1, hmu]
    · by_cases hcr : r.Coprime (q * x)
      · have hnsq : ¬ Squarefree r := fun h => hsr ⟨h, hcr⟩
        rw [if_neg (fun h => hnsq (Squarefree.of_mul_right h.1)), if_pos hcr,
          moebius_eq_zero_of_not_squarefree hnsq]
        simp
      · rw [if_neg hcr, if_neg]
        rintro ⟨hsq, hcop⟩
        apply hcr
        exact Nat.Coprime.mul_right ((Nat.squarefree_mul_iff.mp hsq).1).symm
          (Nat.Coprime.coprime_dvd_left (dvd_mul_left r q) hcop)
  rw [hinner]
  apply mul_le_mul_of_nonneg_left _ (F_nonneg q)
  have hzq : 0 ≤ z / q := div_nonneg hz (by positivity)
  exact chen_V_lower (q * x) hqx (z / q) hzq

end LeanLab.AlmostPrimeSums.Chen1973V
