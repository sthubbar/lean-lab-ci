/-
Supply for the finite smooth expansion in Decomp247a.
Source: Pintz Part I pages 19 and 20 displays 7.10 to 7.14.
Separate the finite character coefficient identity from summation over exponent vectors.
The tensor summation induction adapts Michael Stoll's Mathlib EulerProduct.Basic proof.
That source is copyright 2023 Michael Stoll and licensed under Apache 2.0.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp436a

namespace LeanLab.BhowmikGrimmelt2026

open Filter Topology

/-- Adjoining a new prime splits the tensor of local prime power coefficients.
Source: exponent bookkeeping for Pintz page 20 display 7.14. -/
theorem factored_tensor_split436 (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime)
    {p : ℕ} (hp : p.Prime) (hps : p ∉ s) (f : ℕ → ℕ → ℂ)
    {m : ℕ} (hm : m ∈ Nat.factoredNumbers s) (k : ℕ) :
    (∏ l ∈ insert p s, f l ((p ^ k * m).factorization l)) =
      f p k * ∏ l ∈ s, f l (m.factorization l) := by
  have hpm : ¬ p ∣ m := by
    intro hd
    exact hps (hm.2 p ((Nat.mem_primeFactorsList hm.1).mpr ⟨hp, hd⟩))
  rw [Finset.prod_insert hps]
  have hep : (p ^ k * m).factorization p = k := by
    rw [Nat.factorization_mul (pow_ne_zero k hp.ne_zero) hm.1, Finsupp.add_apply,
      Nat.factorization_pow_self hp, Nat.factorization_eq_zero_of_not_dvd hpm, add_zero]
  rw [hep]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  congr 1
  have hne : l ≠ p := by rintro rfl; exact hps hl
  rw [Nat.factorization_mul (pow_ne_zero k hp.ne_zero) hm.1, Finsupp.add_apply,
    Nat.factorization_pow]
  simp [hp.factorization, Finsupp.single_apply, hne, Ne.symm hne]

/-- Absolutely summable local sequences expand over numbers with the given prime factors.
No local sequence is required to have zeroth term one.
Source: finite prime expansion in Pintz page 20 display 7.14. -/
theorem factored_tensor_hasSum436 (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime)
    (f : ℕ → ℕ → ℂ) (hsum : ∀ p ∈ s, Summable (fun k => ‖f p k‖)) :
    Summable (fun m : Nat.factoredNumbers s => ‖∏ p ∈ s, f p (m.val.factorization p)‖) ∧
      HasSum (fun m : Nat.factoredNumbers s => ∏ p ∈ s, f p (m.val.factorization p))
        (∏ p ∈ s, ∑' k : ℕ, f p k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Nat.factoredNumbers_empty]
    simp only [Finset.prod_empty, norm_one]
    exact ⟨(Set.finite_singleton 1).summable (fun _ => (1 : ℝ)), hasSum_singleton 1 (fun _ => (1 : ℂ))⟩
  | @insert p s hps ih =>
    have hp := hprime p (Finset.mem_insert_self p s)
    have hpr : ∀ l ∈ s, l.Prime := fun l hl => hprime l (Finset.mem_insert_of_mem hl)
    have hsr : ∀ l ∈ s, Summable (fun k => ‖f l k‖) :=
      fun l hl => hsum l (Finset.mem_insert_of_mem hl)
    obtain ⟨hiNorm, hiSum⟩ := ih hpr hsr
    have hpSum := hsum p (Finset.mem_insert_self p s)
    have hterm (x : ℕ × Nat.factoredNumbers s) :
        (∏ l ∈ insert p s, f l ((p ^ x.1 * x.2.val).factorization l)) =
          f p x.1 * ∏ l ∈ s, f l (x.2.val.factorization l) :=
      factored_tensor_split436 s hpr hp hps f x.2.property x.1
    constructor
    · rw [← (Nat.equivProdNatFactoredNumbers hp hps).summable_iff]
      simp only [Function.comp_def, Nat.equivProdNatFactoredNumbers_apply']
      simpa only [hterm] using hpSum.mul_norm hiNorm
    · rw [Finset.prod_insert hps, ← (Nat.equivProdNatFactoredNumbers hp hps).hasSum_iff]
      simp only [Function.comp_def, Nat.equivProdNatFactoredNumbers_apply']
      have : T3Space ℂ := instT3Space
      simp_rw [hterm]
      apply hpSum.of_norm.hasSum.mul hiSum
      exact (hpSum.mul_norm hiNorm).of_norm

/-- The new coefficient majorant makes every prime power subsequence absolutely summable.
Source: Pintz page 20 display 7.13, before finite prime expansion.
CONDITIONAL ON twisted_fiber_bound436. -/
theorem component_power_summable436 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (N : ℤ) (hN : 1 ≤ N) {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => ‖aqZero247 χ₁ χ₂ N (p ^ k)‖) := by
  obtain ⟨C, hC, hc⟩ := aqZero247_totient_supply436 χ₁ χ₂ hχ₁ hχ₂ N hN
  have hs := aqZero247_norm_summable_of_bound χ₁ χ₂ N C hC hc
  exact hs.comp_injective (Nat.pow_right_injective hp.two_le)

/-- LEAF. Pintz Part I pages 19 and 20 displays 7.10 to 7.14.
OPEN finite CRT character identity with cancellation of the two Gauss phases
against the twisted Ramanujan phase. Every conductor prime is included.
This is one coefficient identity and contains no infinite sum or limit. -/
theorem aq_component_identity436 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : IsPrimeComponents χ₁ ψ₁) (h₂ : IsPrimeComponents χ₂ ψ₂)
    (N : ℤ) (hN : 1 ≤ N) (X : ℕ) (hX₁ : r₁ < X) (hX₂ : r₂ < X)
    (q : X.smoothNumbers) :
    aqZero247 χ₁ χ₂ N q = ∏ p ∈ (Finset.range X).filter Nat.Prime,
      aqZero247 (ψ₁ p) (ψ₂ p) N (p ^ q.val.factorization p) := by
  sorry

/-- Exact aqZero247_smooth_expansion statement from the smaller CRT identity and local sums.
CONDITIONAL ON twisted_fiber_bound436 and aq_component_identity436.
Source: Pintz page 20 display 7.14. No old smooth expansion leaf is used. -/
theorem aqZero247_smooth_supply436 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : IsPrimeComponents χ₁ ψ₁) (h₂ : IsPrimeComponents χ₂ ψ₂)
    (N : ℤ) (hN : 1 ≤ N) (X : ℕ) (hX₁ : r₁ < X) (hX₂ : r₂ < X) :
    ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorGen (ψ₁ p) (ψ₂ p) N p =
      ∑' q : X.smoothNumbers, aqZero247 χ₁ χ₂ N q := by
  let s := (Finset.range X).filter Nat.Prime
  let f : ℕ → ℕ → ℂ := fun p k => aqZero247 (ψ₁ p) (ψ₂ p) N (p ^ k)
  have hs : ∀ p ∈ s, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hsum : ∀ p ∈ s, Summable (fun k => ‖f p k‖) := fun p hp =>
    component_power_summable436 (ψ₁ p) (ψ₂ p) (h₁.1 p) (h₂.1 p) N hN (hs p hp)
  have h := (factored_tensor_hasSum436 s hs f hsum).2.tsum_eq
  have hsets : Nat.factoredNumbers s = X.smoothNumbers := by
    simpa [s, Nat.primesBelow] using (Nat.smoothNumbers_eq_factoredNumbers_primesBelow X).symm
  have hlocal (p : ℕ) : (∑' k : ℕ, f p k) = eulerFactorGen (ψ₁ p) (ψ₂ p) N p := by
    rfl
  simp_rw [hlocal] at h
  rw [hsets] at h
  rw [← h]
  apply tsum_congr
  intro q
  exact (aq_component_identity436 χ₁ χ₂ hχ₁ hχ₂ ψ₁ ψ₂ h₁ h₂ N hN X hX₁ hX₂ q).symm

/-- Exact original euler_gen_eq statement from the two smaller arithmetic leaves.
CONDITIONAL ON twisted_fiber_bound436 and aq_component_identity436.
Source: Pintz pages 19 and 20 displays 7.13 to 7.15. -/
theorem euler_gen_eq_supply436 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : IsPrimeComponents χ₁ ψ₁) (h₂ : IsPrimeComponents χ₂ ψ₂) (N : ℤ) (hN : 1 ≤ N) :
    Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorGen (ψ₁ p) (ψ₂ p) N p)
      atTop (𝓝 (genSing χ₁ χ₂ N)) := by
  obtain ⟨C, hC, hc⟩ := aqZero247_totient_supply436 χ₁ χ₂ hχ₁ hχ₂ N hN
  have hsum := (aqZero247_norm_summable_of_bound χ₁ χ₂ N C hC hc).of_norm
  apply (aqZero247_smooth_tendsto χ₁ χ₂ N hsum).congr'
  filter_upwards [eventually_gt_atTop r₁, eventually_gt_atTop r₂] with X hX₁ hX₂
  exact (aqZero247_smooth_supply436 χ₁ χ₂ hχ₁ hχ₂ ψ₁ ψ₂ h₁ h₂ N hN X hX₁ hX₂).symm

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.factored_tensor_split436
#print axioms LeanLab.BhowmikGrimmelt2026.factored_tensor_hasSum436
#print axioms LeanLab.BhowmikGrimmelt2026.component_power_summable436
#print axioms LeanLab.BhowmikGrimmelt2026.aq_component_identity436
#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247_smooth_supply436

#print axioms LeanLab.BhowmikGrimmelt2026.euler_gen_eq_supply436
