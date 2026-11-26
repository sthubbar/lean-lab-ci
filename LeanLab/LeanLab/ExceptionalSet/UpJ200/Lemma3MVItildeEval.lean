import LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Split

/-!
# Proof of the LEAF `mv_Itilde_eval` of `Lemma3MV617Split`

Burst burst-20261122, unit mv617tilde_split-itilde.

Source P0015, Montgomery and Vaughan 1975, page 365: "Clearly `Ĩ(n) = Σ_{P<k<n-P} (k(n-k))^{β̃-1}`",
where `Ĩ(n) = ∫_0^1 T̃(η)² e(-nη) dη` is defined on page 364 and
`T̃(η) = -Σ_{P<k≤X} k^{β̃-1} e(kη)` on page 361. The proof is orthogonality of `e(kη)` on `[0,1]`:
expand `T̃²` as a double sum, integrate termwise, keep the pairs `k + l = n`, and match them with
the integers `k` of the finite sum `Itilde` of P0082 display (13).

* PROVED `integral_eC_int'`: `∫_0^1 e(kx) dx = [k = 0]` for integers `k`, a copy for `U1539.eC`
  of `BG2026.integral_eC_int`.
* PROVED `mv_Itilde_eval_proved`, with exactly the type of `Lemma3MV617Split.mv_Itilde_eval`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma3MVItildeEval

open Real Finset
open LeanLab.ExceptionalSet.U1539 (eC)
open LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082 (Itilde)
open LeanLab.ExceptionalSet.UpJ200.Lemma3MVSplit (Ttilde)

/-- `∫_0^1 e(kx) dx = [k = 0]` for integers `k`. -/
theorem integral_eC_int' (k : ℤ) :
    ∫ x in (0 : ℝ)..1, eC (k * x) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [eC]
  · have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hc : (2 * π * Complex.I * k : ℂ) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [this, Complex.I_ne_zero, hk']
    have e : ∀ x : ℝ, eC (k * x) = Complex.exp ((2 * π * Complex.I * k) * x) := by
      intro x; unfold eC; push_cast; ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * π * Complex.I * k) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * π * Complex.I * k) * ((1 : ℝ) : ℂ) = k * (2 * π * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [h1]; simp

theorem eC_continuous' : Continuous eC := by unfold eC; fun_prop

/-- The coefficient `k^{β̃-1}` of `T̃`. -/
private noncomputable abbrev cf (β : ℝ) (n : ℕ) : ℂ := (((n : ℝ) ^ (β - 1) : ℝ) : ℂ)

/-- Pointwise expansion of `T̃(η)² e(-mη)` as a double sum. -/
theorem Ttilde_sq_expand (β P X η : ℝ) (m : ℤ) :
    Ttilde β P X η ^ 2 * eC (-(η * m)) =
      ∑ k ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, ∑ l ∈ Ioc ⌊P⌋₊ ⌊X⌋₊,
        cf β k * cf β l * eC ((((k : ℤ) + l - m : ℤ) : ℝ) * η) := by
  unfold Ttilde
  rw [neg_sq, sq, Finset.sum_mul_sum, Finset.sum_mul]
  refine sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_mul]
  refine sum_congr rfl (fun l _ => ?_)
  unfold eC
  rw [show cf β k * Complex.exp (2 * ↑π * Complex.I * ↑(η * (k : ℝ))) *
      (cf β l * Complex.exp (2 * ↑π * Complex.I * ↑(η * (l : ℝ)))) *
      Complex.exp (2 * ↑π * Complex.I * ↑(-(η * (m : ℝ)))) =
      cf β k * cf β l * (Complex.exp (2 * ↑π * Complex.I * ↑(η * (k : ℝ))) *
      Complex.exp (2 * ↑π * Complex.I * ↑(η * (l : ℝ))) *
      Complex.exp (2 * ↑π * Complex.I * ↑(-(η * (m : ℝ))))) by ring]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- The integral of the double sum keeps the pairs `k + l = m`. -/
theorem integral_Ttilde_sq (β P X : ℝ) (m : ℤ) :
    (∫ η in (0 : ℝ)..1, Ttilde β P X η ^ 2 * eC (-(η * m))) =
      ∑ k ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, ∑ l ∈ Ioc ⌊P⌋₊ ⌊X⌋₊,
        cf β k * cf β l * (if ((k : ℤ) + l - m : ℤ) = 0 then 1 else 0) := by
  simp_rw [Ttilde_sq_expand]
  have ht : ∀ (c : ℂ) (j : ℤ),
      IntervalIntegrable (fun x : ℝ => c * eC (j * x)) MeasureTheory.volume 0 1 := fun c j =>
    (continuous_const.mul (eC_continuous'.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hi : ∀ k : ℕ, IntervalIntegrable (fun x : ℝ => ∑ l ∈ Ioc ⌊P⌋₊ ⌊X⌋₊,
      cf β k * cf β l * eC ((((k : ℤ) + l - m : ℤ) : ℝ) * x)) MeasureTheory.volume 0 1 := by
    intro k
    exact (continuous_finsetSum _ fun l _ => continuous_const.mul (eC_continuous'.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (fun k _ => hi k)]
  refine sum_congr rfl (fun k _ => ?_)
  rw [intervalIntegral.integral_finsetSum (fun l _ => ht _ _)]
  refine sum_congr rfl (fun l _ => ?_)
  rw [intervalIntegral.integral_const_mul, integral_eC_int']

/-- PROVED: P0015 page 365, `Ĩ(n) = Σ_{P<k<n-P} (k(n-k))^{β̃-1}`, the integral form of page 364
evaluated by orthogonality. Exactly the type of `Lemma3MV617Split.mv_Itilde_eval`. -/
theorem mv_Itilde_eval_proved : ∀ β P X : ℝ, 0 ≤ P → ∀ m : ℤ, 1 ≤ m → (m : ℝ) ≤ X →
    (∫ η in (0 : ℝ)..1, Ttilde β P X η ^ 2 * eC (-(η * m))) = ((Itilde β P m : ℝ) : ℂ) := by
  intro β P X hP m hm hmX
  rw [integral_Ttilde_sq]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_product' (f := fun (k l : ℕ) => if ((k : ℤ) + l - m : ℤ) = 0 then cf β k * cf β l
    else 0), ← Finset.sum_filter]
  unfold Itilde
  push_cast
  have hX0 : (0 : ℝ) ≤ X := le_trans (by exact_mod_cast (show (0 : ℤ) ≤ m by omega)) hmX
  have memS : ∀ n : ℕ, n ∈ Ioc ⌊P⌋₊ ⌊X⌋₊ ↔ P < n ∧ (n : ℝ) ≤ X := by
    intro n
    rw [Finset.mem_Ioc, Nat.floor_lt hP, Nat.le_floor_iff hX0]
  refine Finset.sum_nbij' (fun p => (p.1 : ℤ)) (fun k => (k.toNat, (m - k).toNat)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, memS] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hp
    have e : (p.2 : ℤ) = m - p.1 := by omega
    have e' : ((p.2 : ℕ) : ℝ) = (m : ℝ) - (p.1 : ℝ) := by exact_mod_cast e
    simp only [Finset.mem_filter, Finset.mem_Ioo]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have : (0 : ℝ) < p.1 := lt_of_le_of_lt hP h1
      exact_mod_cast this
    · have : (0 : ℝ) < p.2 := lt_of_le_of_lt hP h3
      have : (0 : ℝ) < (m : ℝ) - (p.1 : ℝ) := e' ▸ this
      have : ((p.1 : ℤ) : ℝ) < (m : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · push_cast; exact h1
    · push_cast; linarith
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ioo] at hk
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hk
    simp only [Finset.mem_filter, Finset.mem_product, memS]
    have ek : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
      have : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have el : (((m - k).toNat : ℕ) : ℝ) = (m : ℝ) - (k : ℝ) := by
      have : (((m - k).toNat : ℕ) : ℤ) = m - k := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have hk1 : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2.le
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1.le
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [ek]; exact h3
    · rw [ek]; linarith
    · rw [el]; linarith
    · rw [el]; linarith
    · omega
  · intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨_, h5⟩ := hp
    have e : (p.2 : ℤ) = m - p.1 := by omega
    ext
    · simp
    · simp only [Int.toNat_natCast]
      omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ioo] at hk
    exact Int.toNat_of_nonneg (by omega)
  · intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpS, h5⟩ := hp
    have e : (p.2 : ℤ) = m - p.1 := by omega
    have e' : ((p.2 : ℕ) : ℝ) = (m : ℝ) - (p.1 : ℝ) := by exact_mod_cast e
    unfold cf
    have hm0 : (0 : ℝ) ≤ (m : ℝ) - (p.1 : ℝ) := by rw [← e']; exact Nat.cast_nonneg _
    rw [e', Int.cast_natCast, ← Complex.ofReal_mul, ← Real.mul_rpow (Nat.cast_nonneg _) hm0]

/-- The proof has exactly the type of the LEAF. -/
example : type_of% @mv_Itilde_eval_proved =
    type_of% @Lemma3MV617Split.mv_Itilde_eval := rfl

end LeanLab.ExceptionalSet.UpJ200.Lemma3MVItildeEval

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MVItildeEval.mv_Itilde_eval_proved
