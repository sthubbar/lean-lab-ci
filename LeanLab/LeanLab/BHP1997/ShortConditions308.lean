/-
BHP1997, page 3. Exact projections and finite distribution assembly.
The new paper Props require Claude review before merge.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SieveConditionsC165

namespace LeanLab.BHP1997.Task308
open Classical Complex DecompC165b

/-- Page 3, condition iii, exactly the distribution clause in RightConditions.
This paper Prop requires Claude review before merge. -/
def ShortDistribution (ε v : ℝ) (b : ℝ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
    1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
    ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
      ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        ((b x m : ℂ) * χ (m : ZMod q) -
          Thm2.delta χ * v / Real.log (x ^ (11 / 20 + ε)))‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)

/-- Page 3, condition iv, exactly the last clause in RightConditions.
The exceptional sets depend on A, x and q. The paper norm sums over their complement.
This paper Prop requires Claude review before merge. -/
def ShortMeanSquare (ε v : ℝ) (b : ℝ → ℕ → ℝ) : Prop :=
  ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → q ≤ sieveQ ε x →
      ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              ((b x m : ℂ) * χ (m : ZMod q) -
                Thm2.delta χ * v / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                  C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                    x ^ (11 / 20 + ε) * Real.log x ^ (-A)

/-- Page 3. Reassemble the three exact short-weight conditions. -/
theorem right_conditions_of_parts {ε B v : ℝ} {b : ℝ → ℕ → ℝ}
    (hdiv : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hdist : ShortDistribution ε v b) (hmean : ShortMeanSquare ε v b) :
    RightConditions ε B v b := by
  exact ⟨hdiv, hdist, hmean⟩

/-- Page 3 condition iii and page 53 four-term identity. Distribution estimates
are closed under addition with the sum of the two densities. -/
theorem short_distribution_add {ε u v : ℝ} {a b : ℝ → ℕ → ℝ}
    (ha : ShortDistribution ε u a) (hb : ShortDistribution ε v b) :
    ShortDistribution ε (u+v) (fun x k => a x k+b x k) := by
  intro A hA
  obtain ⟨Ca,hCa⟩ := ha A hA
  obtain ⟨Cb,hCb⟩ := hb A hA
  let C := max (max Ca Cb) (max 1 (Ca+Cb))
  refine ⟨C,fun x hx q hq hqx χ t ht => ?_⟩
  have hxa : Ca ≤ x := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hx
  have hxb : Cb ≤ x := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hx
  have hx1 : 1 ≤ x := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hx
  have hsum : Ca+Cb ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have he : (∑ k ∈ (rightInterval ε x).filter (fun k : ℕ => (k:ℝ) ≤ t),
      (((a x k+b x k:ℝ):ℂ)*χ (k:ZMod q)-Thm2.delta χ*((u+v:ℝ):ℂ)/Real.log (x^(11/20+ε)))) =
    (∑ k ∈ (rightInterval ε x).filter (fun k : ℕ => (k:ℝ) ≤ t),
      ((a x k:ℂ)*χ (k:ZMod q)-Thm2.delta χ*u/Real.log (x^(11/20+ε)))) +
    ∑ k ∈ (rightInterval ε x).filter (fun k : ℕ => (k:ℝ) ≤ t),
      ((b x k:ℂ)*χ (k:ZMod q)-Thm2.delta χ*v/Real.log (x^(11/20+ε))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    ring
  dsimp only
  rw [he]
  calc
    _ ≤ ‖∑ k ∈ (rightInterval ε x).filter (fun k : ℕ => (k:ℝ) ≤ t),
        ((a x k:ℂ)*χ (k:ZMod q)-Thm2.delta χ*u/Real.log (x^(11/20+ε)))‖ +
      ‖∑ k ∈ (rightInterval ε x).filter (fun k : ℕ => (k:ℝ) ≤ t),
        ((b x k:ℂ)*χ (k:ZMod q)-Thm2.delta χ*v/Real.log (x^(11/20+ε)))‖ := norm_add_le _ _
    _ ≤ Ca*x^(11/20+ε)*Real.log x^(-A)+Cb*x^(11/20+ε)*Real.log x^(-A) :=
      add_le_add (hCa x hxa q hq hqx χ t ht) (hCb x hxb q hq hqx χ t ht)
    _ = (Ca+Cb)*x^(11/20+ε)*Real.log x^(-A) := by ring
    _ ≤ C*x^(11/20+ε)*Real.log x^(-A) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg (by linarith) _))
        (Real.rpow_nonneg (Real.log_nonneg hx1) _)

/-- Page 3 condition iii and page 53 four-term identity. Negation changes
both the coefficient and its density by a minus sign. -/
theorem short_distribution_neg {ε u : ℝ} {a : ℝ → ℕ → ℝ}
    (ha : ShortDistribution ε u a) : ShortDistribution ε (-u) (fun x k => -a x k) := by
  intro A hA
  obtain ⟨C,hC⟩ := ha A hA
  refine ⟨C,fun x hx q hq hqx χ t ht => ?_⟩
  have he : (∑ k ∈ (rightInterval ε x).filter (fun k : ℕ => (k:ℝ) ≤ t),
      (((-a x k:ℝ):ℂ)*χ (k:ZMod q)-Thm2.delta χ*((-u:ℝ):ℂ)/Real.log (x^(11/20+ε)))) =
    -(∑ k ∈ (rightInterval ε x).filter (fun k : ℕ => (k:ℝ) ≤ t),
      ((a x k:ℂ)*χ (k:ZMod q)-Thm2.delta χ*u/Real.log (x^(11/20+ε)))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    ring
  dsimp only
  rw [he,norm_neg]
  exact hC x hx q hq hqx χ t ht

/-- Page 3 condition iii. The zero family has zero distribution error. -/
theorem short_distribution_zero (ε : ℝ) :
    ShortDistribution ε 0 (fun _ _ => 0) := by
  intro A hA
  refine ⟨1, ?_⟩
  intro x hx q hq hqx χ t ht
  have hx0 : 0 ≤ x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  simp only [Complex.ofReal_zero, zero_mul, mul_zero, zero_div, sub_zero,
    Finset.sum_const_zero, norm_zero]
  positivity

/-- Page 3 condition iii and page 53 four-term identity. Subtracting two
distributed coefficient families subtracts their densities. -/
theorem short_distribution_sub {ε u v : ℝ} {a b : ℝ → ℕ → ℝ}
    (ha : ShortDistribution ε u a) (hb : ShortDistribution ε v b) :
    ShortDistribution ε (u-v) (fun x k => a x k-b x k) := by
  simpa only [sub_eq_add_neg] using short_distribution_add ha (short_distribution_neg hb)

/-- Page 3 condition iii and page 53. Finite Buchstab combinations preserve
distribution if every actual summand has its own distribution estimate. -/
theorem short_distribution_sum {ι : Type*} (s : Finset ι) (v : ι → ℝ)
    (b : ι → ℝ → ℕ → ℝ) (ε : ℝ) (hb : ∀ i ∈ s, ShortDistribution ε (v i) (b i)) :
    ShortDistribution ε (∑ i ∈ s, v i) (fun x k => ∑ i ∈ s, b i x k) := by
  induction s using Finset.induction_on with
  | empty => simpa using short_distribution_zero ε
  | @insert i s hi ih =>
    have hsum := ih (fun j hj => hb j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using
      short_distribution_add (hb i (Finset.mem_insert_self _ _)) hsum

/-- Page 3. The two projected short-condition statements have the zero instance.
This checks the predicates only and does not construct the required positive density. -/
theorem short_conditions_zero_instance :
    ShortDistribution 0 0 (fun _ _ => 0) ∧ ShortMeanSquare 0 0 (fun _ _ => 0) := by
  refine ⟨short_distribution_zero 0, fun _ _ _ => ∅, ?_⟩
  intro A hA
  refine ⟨1, ?_⟩
  intro x hx q hq hqx
  have hx0 : 0 ≤ x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  constructor
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · intro z hzl hzu
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, zero_div, sub_zero,
      Finset.sum_const_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      intervalIntegral.integral_zero]
    positivity

end LeanLab.BHP1997.Task308
