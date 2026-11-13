/-
Gallagher 1975 P0094 pp.129, 131 and 132, helper lemmas for display 17.
This file carries the printed arithmetic of displays 7 and 17 from the CITED-LEFT
leaf `induced_cn_bound` of display 5, with every new name prefixed by t345 so
that it cannot collide with the module `Linnik.MajorArcEnergy.Display17`, which
proves the same statement under unprefixed names from the same cited leaf.
The final theorem `t345_exceptional_weight_bound_of_cited` is the statement of
the leaf `exceptional_weight_bound` of `Linnik.MajorArcEnergy.Leaves1517`. That
leaf cannot be closed from here: `Display17.lean` imports `Leaves1517.lean`, so
pointing the leaf at either proof would make an import cycle, which is why main
relabelled it OFF ROUTE and why this landed module stands beside it.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.MajorArcEnergy.Leaves13

namespace LeanLab.Linnik.MajorArcEnergy

open Finset
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a

/-- Gallagher 1975 p.128: chi_q is chi lifted to modulus q when the conductor divides q. -/
theorem t345_induced_eq_changeLevel {x : PChar} {q : ℕ} (h : x.1 + 1 ∣ q) :
    induced x q = DirichletCharacter.changeLevel h x.2 := by
  unfold induced
  simp only [h, ↓reduceDIte]

/-- Gallagher 1975 p.129 Proof of (7): for primitive chi to conductor r dividing q,
the induced character chi_q has conductor r. -/
theorem t345_conductor_induced {x : PChar} (hx : x.2.IsPrimitive) {q : ℕ} (hq : 1 ≤ q)
    (h : x.1 + 1 ∣ q) : (induced x q).conductor = x.1 + 1 := by
  have : NeZero q := ⟨by omega⟩
  rw [t345_induced_eq_changeLevel h, DirichletCharacter.conductor_changeLevel]
  exact hx

/-- Gallagher 1975 p.129 Proof of (7): conj chi_q also has conductor r. -/
theorem t345_conductor_induced_inv {x : PChar} (hx : x.2.IsPrimitive) {q : ℕ} (hq : 1 ≤ q)
    (h : x.1 + 1 ∣ q) : (induced x q)⁻¹.conductor = x.1 + 1 := by
  rw [DirichletCharacter.conductor_inv, t345_conductor_induced hx hq h]

/-- Gallagher 1975 p.129 display 6, the case n = 1 of display 5: |tau(chi_q)| is at most
r^(1/2), and tau(chi_q) vanishes unless q = r s with s squarefree and prime to r. -/
theorem t345_tau_bound {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) :
    ‖tau χ‖ ≤ Real.sqrt χ.conductor ∧
      (tau χ ≠ 0 → χ.conductor ∣ q ∧ Squarefree (q / χ.conductor) ∧
        Nat.Coprime (q / χ.conductor) χ.conductor) := by
  have h := induced_cn_bound hq χ 1
  simp only [Int.natAbs_one, Nat.gcd_one_right, Nat.div_one] at h
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  refine ⟨?_, h.2⟩
  have h1 := h.1
  rw [mul_div_assoc, div_self hφ.ne', mul_one] at h1
  exact h1

/-- Gallagher 1975 p.129 Proof of (7): for q = m s with s prime to m, writing k_n = k/(k, n),
one has (m, q_n) = m_n, phi(q) = phi(m) phi(s) and phi(q_n) = phi(m_n) phi(s_n). -/
theorem t345_split_q {m s N : ℕ} (hcop : Nat.Coprime s m) :
    Nat.gcd m (m * s / Nat.gcd (m * s) N) = m / Nat.gcd m N ∧
      (m * s).totient = m.totient * s.totient ∧
      (m * s / Nat.gcd (m * s) N).totient =
        (m / Nat.gcd m N).totient * (s / Nat.gcd s N).totient := by
  have hg : Nat.gcd (m * s) N = Nat.gcd m N * Nat.gcd s N := by
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul N hcop.symm, Nat.gcd_comm N m, Nat.gcd_comm N s]
  have hdiv : m * s / Nat.gcd (m * s) N = (m / Nat.gcd m N) * (s / Nat.gcd s N) := by
    rw [hg, Nat.div_mul_div_comm (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)]
  have hsd : s / Nat.gcd s N ∣ s := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have hmd : m / Nat.gcd m N ∣ m := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have hc1 : Nat.Coprime (s / Nat.gcd s N) m := Nat.Coprime.coprime_dvd_left hsd hcop
  have hc2 : Nat.Coprime (m / Nat.gcd m N) (s / Nat.gcd s N) :=
    Nat.Coprime.coprime_dvd_left hmd hc1.symm
  refine ⟨?_, Nat.totient_mul hcop.symm, ?_⟩
  · rw [hdiv, Nat.Coprime.gcd_mul_right_cancel_right _ hc1]
    exact Nat.gcd_eq_right hmd
  · rw [hdiv, Nat.totient_mul hc2]

/-- Gallagher 1975 p.129 Proof of (7): the summand mu^2(s)/(phi(s) phi(s_n)), taken on
squarefree s, with s_n = s/(s, n). -/
noncomputable def t345_eulerTerm (N s : ℕ) : ℝ :=
  1 / ((s.totient : ℝ) * (s / Nat.gcd s N).totient)

theorem t345_eulerTerm_nonneg (N s : ℕ) : 0 ≤ t345_eulerTerm N s := by
  unfold t345_eulerTerm; positivity

/-- Gallagher 1975 p.129 Proof of (7), the Euler product bound: the product over k from 2
to X of 1 + 1/(k - 1)^2, which dominates the product over p not dividing mn of
1 + 1/(p - 1)^2, is at most 4. Telescoping with 1 + 1/j^2 at most j^2/(j^2 - 1). -/
theorem t345_tele_le (X : ℕ) :
    ∏ k ∈ Icc 2 X, (1 + ((k : ℝ) - 1)⁻¹ * ((k : ℝ) - 1)⁻¹) ≤ 4 := by
  have key : ∀ X : ℕ, 2 ≤ X →
      ∏ k ∈ Icc 2 X, (1 + ((k : ℝ) - 1)⁻¹ * ((k : ℝ) - 1)⁻¹) ≤ 4 * ((X : ℝ) - 1) / X := by
    intro X hX
    induction X, hX using Nat.le_induction with
    | base => norm_num
    | succ X hX ih =>
      rw [Finset.prod_Icc_succ_top (by omega)]
      have hX' : (2 : ℝ) ≤ X := by exact_mod_cast hX
      push_cast
      have e : ((X : ℝ) + 1 - 1) = X := by ring
      rw [e]
      have hpos : 0 ≤ 1 + (X : ℝ)⁻¹ * (X : ℝ)⁻¹ := by positivity
      calc (∏ k ∈ Icc 2 X, (1 + ((k : ℝ) - 1)⁻¹ * ((k : ℝ) - 1)⁻¹)) *
            (1 + (X : ℝ)⁻¹ * (X : ℝ)⁻¹)
          ≤ 4 * ((X : ℝ) - 1) / X * (1 + (X : ℝ)⁻¹ * (X : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_right ih hpos
        _ ≤ 4 * (X : ℝ) / ((X : ℝ) + 1) := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
            have hX0 : (0 : ℝ) < X := by linarith
            field_simp
            nlinarith [sq_nonneg ((X : ℝ)), mul_pos hX0 hX0]
  by_cases hX : 2 ≤ X
  · refine (key X hX).trans ?_
    have hX' : (2 : ℝ) ≤ X := by exact_mod_cast hX
    rw [div_le_iff₀ (by linarith)]
    linarith
  · rw [Finset.Icc_eq_empty (by omega), Finset.prod_empty]
    norm_num

/-- Gallagher 1975 p.129 Proof of (7): for squarefree s, phi(s) is the product of p - 1
over the primes p dividing s. -/
theorem t345_totient_squarefree_real {s : ℕ} (hs : Squarefree s) :
    (s.totient : ℝ) = ∏ p ∈ s.primeFactors, ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors s
  rw [Nat.prod_primeFactors_of_squarefree hs, mul_comm s] at h
  have hs0 : 0 < s := Nat.pos_of_ne_zero hs.ne_zero
  have h2 : s.totient = ∏ p ∈ s.primeFactors, (p - 1) := Nat.eq_of_mul_eq_mul_right hs0 h
  rw [h2, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]

/-- Gallagher 1975 p.129 Proof of (7): for squarefree s, the primes dividing
s_n = s/(s, n) are the primes dividing s and not n. -/
theorem t345_primeFactors_div_gcd {s : ℕ} (hs : Squarefree s) (N : ℕ) :
    (s / Nat.gcd s N).primeFactors = s.primeFactors.filter (fun p => ¬ p ∣ N) := by
  have hs0 : s ≠ 0 := hs.ne_zero
  have hgd : Nat.gcd s N ∣ s := Nat.gcd_dvd_left _ _
  have hst : s = Nat.gcd s N * (s / Nat.gcd s N) := (Nat.mul_div_cancel' hgd).symm
  have ht0 : s / Nat.gcd s N ≠ 0 := by
    intro h; rw [h, mul_zero] at hst; exact hs0 hst
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hpt, -⟩
    refine ⟨⟨hp, hpt.trans (Nat.div_dvd_of_dvd hgd), hs0⟩, fun hpN => ?_⟩
    have hpg : p ∣ Nat.gcd s N := Nat.dvd_gcd (hpt.trans (Nat.div_dvd_of_dvd hgd)) hpN
    have : p * p ∣ s := by rw [hst]; exact Nat.mul_dvd_mul hpg hpt
    exact (Nat.squarefree_iff_prime_squarefree.mp hs) p hp this
  · rintro ⟨⟨hp, hps, -⟩, hpN⟩
    refine ⟨hp, ?_, ht0⟩
    rw [hst] at hps
    rcases (Nat.Prime.dvd_mul hp).mp hps with h | h
    · exact absurd (h.trans (Nat.gcd_dvd_right _ _)) hpN
    · exact h

/-- Gallagher 1975 p.129 Proof of (7): for squarefree s, mu^2(s)/(phi(s) phi(s_n)) is the
product over p dividing s of 1/(p - 1) times 1 if p divides n and 1/(p - 1) otherwise. -/
theorem t345_eulerTerm_eq_prod {s : ℕ} (hs : Squarefree s) (N : ℕ) :
    t345_eulerTerm N s = ∏ p ∈ s.primeFactors,
      ((p : ℝ) - 1)⁻¹ * (if p ∣ N then 1 else ((p : ℝ) - 1)⁻¹) := by
  have ht : Squarefree (s / Nat.gcd s N) :=
    Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)) hs
  unfold t345_eulerTerm
  rw [t345_totient_squarefree_real hs, t345_totient_squarefree_real ht, t345_primeFactors_div_gcd hs N,
    Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, one_mul,
    Finset.prod_inv_distrib, Finset.prod_inv_distrib, one_div, mul_inv]

/-- Gallagher 1975 p.129 Proof of (7), "The sum is" the Euler product: the sum over squarefree
s at most X prime to m of mu^2(s)/(phi(s) phi(s_n)) is at most the product over primes p at
most X not dividing m of 1 + 1/(p - 1)^2 when p does not divide n and 1 + 1/(p - 1) when it
does. -/
theorem t345_euler_sum_le_prod {N m : ℕ} (X : ℕ) :
    ∑ s ∈ (Icc 1 X).filter (fun s => Squarefree s ∧ Nat.Coprime s m), t345_eulerTerm N s ≤
      ∏ p ∈ (Icc 1 X).filter Nat.Prime, (1 + (if p ∣ m then 0 else
        ((p : ℝ) - 1)⁻¹ * (if p ∣ N then 1 else ((p : ℝ) - 1)⁻¹))) := by
  set f : ℕ → ℝ := fun p => if p ∣ m then 0 else
        ((p : ℝ) - 1)⁻¹ * (if p ∣ N then 1 else ((p : ℝ) - 1)⁻¹) with hf
  have hf0 : ∀ p, Nat.Prime p → 0 ≤ f p := by
    intro p hp
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    simp only [hf]
    split_ifs <;> first | exact le_rfl | (apply mul_nonneg <;> positivity)
  set S := (Icc 1 X).filter (fun s => Squarefree s ∧ Nat.Coprime s m) with hS
  set T := (Icc 1 X).filter Nat.Prime with hT
  have h1 : ∀ s ∈ S, t345_eulerTerm N s = ∏ p ∈ s.primeFactors, f p := by
    intro s hs
    obtain ⟨-, hsq, hcop⟩ := Finset.mem_filter.mp hs
    rw [t345_eulerTerm_eq_prod hsq N]
    apply Finset.prod_congr rfl
    intro p hp
    have hpm : ¬ p ∣ m := by
      intro hpm
      have hps : p ∣ s := Nat.dvd_of_mem_primeFactors hp
      have := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hps hpm : p ∣ 1)
      exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' this
    simp only [hf, hpm, ↓reduceIte]
  calc ∑ s ∈ S, t345_eulerTerm N s = ∑ s ∈ S, ∏ p ∈ s.primeFactors, f p := Finset.sum_congr rfl h1
    _ = ∑ t ∈ S.image Nat.primeFactors, ∏ p ∈ t, f p := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        have ha' := (Finset.mem_filter.mp ha).2.1
        have hb' := (Finset.mem_filter.mp hb).2.1
        rw [← Nat.prod_primeFactors_of_squarefree ha', ← Nat.prod_primeFactors_of_squarefree hb']
        rw [hab]
    _ ≤ ∑ t ∈ T.powerset, ∏ p ∈ t, f p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t ht
          rw [Finset.mem_image] at ht
          obtain ⟨s, hs, rfl⟩ := ht
          rw [Finset.mem_powerset]
          intro p hp
          have hsX := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1)
          have hpp := Nat.prime_of_mem_primeFactors hp
          rw [hT, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hpp.one_le, (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans
            hsX.2⟩, hpp⟩
        · intro t ht _
          apply Finset.prod_nonneg
          intro p hp
          exact hf0 p (Finset.mem_filter.mp (Finset.mem_powerset.mp ht hp)).2
    _ = ∏ p ∈ T, (1 + f p) := (Finset.prod_one_add T).symm

/-- Gallagher 1975 p.129 Proof of (7): the Euler product is at most 4 times the product over
p dividing n and not m of 1 + 1/(p - 1), since the product of 1 + 1/(p - 1)^2 is bounded. -/
theorem t345_euler_prod_le {N m : ℕ} (hN : N ≠ 0) (X : ℕ) :
    ∏ p ∈ (Icc 1 X).filter Nat.Prime, (1 + (if p ∣ m then 0 else
        ((p : ℝ) - 1)⁻¹ * (if p ∣ N then 1 else ((p : ℝ) - 1)⁻¹))) ≤
      4 * ∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ m), (1 + ((p : ℝ) - 1)⁻¹) := by
  set T := (Icc 1 X).filter Nat.Prime with hT
  set a : ℕ → ℝ := fun p => 1 + ((p : ℝ) - 1)⁻¹ * ((p : ℝ) - 1)⁻¹ with ha
  set b : ℕ → ℝ := fun p => if p ∣ N ∧ ¬ p ∣ m then 1 + ((p : ℝ) - 1)⁻¹ else 1 with hb
  have hv : ∀ p ∈ T, 0 ≤ ((p : ℝ) - 1)⁻¹ := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    exact inv_nonneg.mpr (by linarith)
  have hstep : ∏ p ∈ T, (1 + (if p ∣ m then 0 else
        ((p : ℝ) - 1)⁻¹ * (if p ∣ N then 1 else ((p : ℝ) - 1)⁻¹))) ≤ ∏ p ∈ T, (a p * b p) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have := hv p hp
      split_ifs <;> positivity
    · intro p hp
      have v0 := hv p hp
      set v := ((p : ℝ) - 1)⁻¹
      simp only [ha, hb]
      by_cases hpm : p ∣ m
      · simp only [hpm, ↓reduceIte, not_true_eq_false, and_false, add_zero, mul_one]
        nlinarith [mul_nonneg v0 v0]
      · by_cases hpN : p ∣ N
        · simp only [hpm, hpN, ↓reduceIte, not_false_eq_true, and_self, mul_one]
          nlinarith [mul_nonneg (mul_nonneg v0 v0) v0, mul_nonneg v0 v0]
        · simp only [hpm, hpN, ↓reduceIte, false_and, mul_one]
          exact le_rfl
  have hA : ∏ p ∈ T, a p ≤ 4 := by
    refine le_trans ?_ (t345_tele_le X)
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      rw [hT, Finset.mem_filter, Finset.mem_Icc] at hp
      rw [Finset.mem_Icc]
      exact ⟨hp.2.two_le, hp.1.2⟩
    · intro p hp
      have := hv p hp
      positivity
    · intro p _ _
      simp only [ha]
      nlinarith [mul_self_nonneg ((p : ℝ) - 1)⁻¹]
  have hB : ∏ p ∈ T, b p ≤ ∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ m),
      (1 + ((p : ℝ) - 1)⁻¹) := by
    simp only [hb]
    rw [← Finset.prod_filter]
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      rw [Nat.mem_primeFactors]
      exact ⟨⟨(Finset.mem_filter.mp hp.1).2, hp.2.1, hN⟩, hp.2.2⟩
    · intro p hp
      have := hv p (Finset.mem_filter.mp hp).1
      positivity
    · intro p hp _
      have hp2 : (2 : ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
      have : 0 ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
      linarith
  have hA0 : 0 ≤ ∏ p ∈ T, a p := Finset.prod_nonneg fun p hp => by
    have := hv p hp
    positivity
  have hB0 : 0 ≤ ∏ p ∈ T, b p := Finset.prod_nonneg fun p hp => by
    have := hv p hp
    simp only [hb]
    split_ifs <;> positivity
  calc _ ≤ ∏ p ∈ T, (a p * b p) := hstep
    _ = (∏ p ∈ T, a p) * ∏ p ∈ T, b p := Finset.prod_mul_distrib
    _ ≤ 4 * ∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ m), (1 + ((p : ℝ) - 1)⁻¹) :=
        mul_le_mul hA hB hB0 (by norm_num)

/-- Gallagher 1975 p.129 Proof of (7), last line: k/phi(k) is the product over p dividing k
of 1 + 1/(p - 1). -/
theorem t345_ratio_eq_prod {k : ℕ} (hk : k ≠ 0) :
    (k : ℝ) / k.totient = ∏ p ∈ k.primeFactors, (1 + ((p : ℝ) - 1)⁻¹) := by
  have hφ : (k.totient : ℝ) * ∏ p ∈ k.primeFactors, (p : ℝ) =
      k * ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) := by
    have := Nat.totient_mul_prod_primeFactors k
    have h2 : ((k.totient * ∏ p ∈ k.primeFactors, p : ℕ) : ℝ) =
        ((k * ∏ p ∈ k.primeFactors, (p - 1) : ℕ) : ℝ) := by rw [this]
    push_cast at h2
    rw [h2]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have hpos : ∀ p ∈ k.primeFactors, (0 : ℝ) < (p : ℝ) - 1 := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  have hQ : (0 : ℝ) < ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) := Finset.prod_pos hpos
  have hφ0 : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hk)
  have e : ∏ p ∈ k.primeFactors, (1 + ((p : ℝ) - 1)⁻¹) =
      ∏ p ∈ k.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    apply Finset.prod_congr rfl
    intro p hp
    have := hpos p hp
    field_simp
    ring
  rw [e, Finset.prod_div_distrib, div_eq_div_iff hφ0.ne' hQ.ne']
  linarith [hφ]

/-- Gallagher 1975 p.131 proof of display 17: the character 1 induces the principal
character 1_q to every modulus q. -/
theorem t345_induced_one (q : ℕ) : induced one q = 1 := by
  unfold induced one
  split_ifs <;> simp

/-- Gallagher 1975 p.131 proof of display 17: the factor r/(phi(r) phi(r_n)) in front of
the sum over s, with r_n = r/(r, n). When the q term is nonzero, r_n = r and this is the
printed r/phi^2(r). -/
noncomputable def t345_excFactor (r N : ℕ) : ℝ :=
  (r : ℝ) / ((r.totient : ℝ) * (r / Nat.gcd r N).totient)

theorem t345_excFactor_nonneg (r N : ℕ) : 0 ≤ t345_excFactor r N := by
  unfold t345_excFactor; positivity

/-- Gallagher 1975 pp.131 and 132 proof of display 17, one term: if the q coefficient z has
|z| at most r phi(q)/phi(q_n), and vanishes unless q = r s with s squarefree and prime to r,
then the q term of C_n is at most r/(phi(r) phi(r_n)) times mu^2(s)/(phi(s) phi(s_n)). -/
theorem t345_exc_term_le {q r N : ℕ} (hq : 1 ≤ q) (hr : r ∣ q) (z : ℂ)
    (hn : ‖z‖ ≤ (r : ℝ) * q.totient / (q / Nat.gcd q N).totient)
    (hz : z ≠ 0 → Squarefree (q / r) ∧ Nat.Coprime (q / r) r) :
    1 / (q.totient : ℝ) ^ 2 * ‖z‖ ≤
      if Squarefree (q / r) ∧ Nat.Coprime (q / r) r then
        t345_excFactor r N * t345_eulerTerm N (q / r) else 0 := by
  have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hr hq
  by_cases h0 : z = 0
  · rw [h0, norm_zero, mul_zero]
    split_ifs
    · exact mul_nonneg (t345_excFactor_nonneg _ _) (t345_eulerTerm_nonneg _ _)
    · exact le_rfl
  obtain ⟨hsq, hcop⟩ := hz h0
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hsq, hcop⟩)]
  obtain ⟨s, rfl⟩ := hr
  rw [Nat.mul_div_cancel_left _ hr0] at hcop hsq ⊢
  have hs0 : 0 < s := Nat.pos_of_ne_zero hsq.ne_zero
  obtain ⟨-, h2, h3⟩ := t345_split_q (m := r) (N := N) hcop
  rw [h3, h2] at hn
  rw [h2]
  have hφr : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr hr0
  have hφs : (0 : ℝ) < s.totient := by exact_mod_cast Nat.totient_pos.mpr hs0
  have hrn : 0 < r / Nat.gcd r N :=
    Nat.div_pos (Nat.gcd_le_left _ hr0) (Nat.gcd_pos_of_pos_left _ hr0)
  have hsn : 0 < s / Nat.gcd s N :=
    Nat.div_pos (Nat.gcd_le_left _ hs0) (Nat.gcd_pos_of_pos_left _ hs0)
  have hφrn : (0 : ℝ) < (r / Nat.gcd r N).totient := by exact_mod_cast Nat.totient_pos.mpr hrn
  have hφsn : (0 : ℝ) < (s / Nat.gcd s N).totient := by exact_mod_cast Nat.totient_pos.mpr hsn
  push_cast at hn ⊢
  calc 1 / ((r.totient : ℝ) * s.totient) ^ 2 * ‖z‖
      ≤ 1 / ((r.totient : ℝ) * s.totient) ^ 2 *
          ((r : ℝ) * (r.totient * s.totient) /
            ((r / Nat.gcd r N).totient * (s / Nat.gcd s N).totient)) := by gcongr
    _ = t345_excFactor r N * t345_eulerTerm N s := by
        unfold t345_excFactor t345_eulerTerm
        field_simp

/-- Gallagher 1975 p.131 proof of display 17: summing the q terms over q = r s, the weight
C_n is at most r/(phi(r) phi(r_n)) times the sum over squarefree s prime to r of
mu^2(s)/(phi(s) phi(s_n)); here s runs up to P, a finite part of Gallagher's sum. -/
theorem t345_weight_le_exc (P : ℝ) (n : ℤ) {x y : PChar} {r : ℕ} (hr : 0 < r)
    (hm : Nat.lcm (x.1 + 1) (y.1 + 1) = r)
    (hterm : ∀ q ∈ pairModuli P x y, 1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q x y‖ ≤
      if Squarefree (q / r) ∧ Nat.Coprime (q / r) r then
        t345_excFactor r n.natAbs * t345_eulerTerm n.natAbs (q / r) else 0) :
    pairWeight P n x y ≤ t345_excFactor r n.natAbs *
      ∑ s ∈ (Icc 1 ⌊P⌋₊).filter (fun s => Squarefree s ∧ Nat.Coprime s r),
        t345_eulerTerm n.natAbs s := by
  set H : ℕ → ℝ := fun s => if Squarefree s ∧ Nat.Coprime s r then
    t345_excFactor r n.natAbs * t345_eulerTerm n.natAbs s else 0 with hH
  have hH0 : ∀ s, 0 ≤ H s := by
    intro s
    simp only [hH]
    split_ifs
    · exact mul_nonneg (t345_excFactor_nonneg _ _) (t345_eulerTerm_nonneg _ _)
    · exact le_rfl
  have hdvd : ∀ q ∈ pairModuli P x y, r ∣ q := fun q hq => hm ▸ (Finset.mem_filter.mp hq).2
  unfold pairWeight
  calc ∑ q ∈ pairModuli P x y, 1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q x y‖
      ≤ ∑ q ∈ pairModuli P x y, H (q / r) :=
        Finset.sum_le_sum fun q hq => hterm q hq
    _ = ∑ s ∈ (pairModuli P x y).image (fun q => q / r), H s := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        simp only at hab
        rw [← Nat.div_mul_cancel (hdvd a ha), ← Nat.div_mul_cancel (hdvd b hb), hab]
    _ ≤ ∑ s ∈ Icc 1 ⌊P⌋₊, H s := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro s hs
          rw [Finset.mem_image] at hs
          obtain ⟨q, hq, rfl⟩ := hs
          have hrq := hdvd q hq
          have hq' := Finset.mem_filter.mp hq
          rw [Finset.mem_Icc] at hq' ⊢
          obtain ⟨⟨hq1, hqP⟩, -⟩ := hq'
          refine ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hrq) hr, ?_⟩
          exact (Nat.div_le_self _ _).trans hqP
        · intro s _ _
          exact hH0 s
    _ = t345_excFactor r n.natAbs * ∑ s ∈ (Icc 1 ⌊P⌋₊).filter (fun s => Squarefree s ∧
          Nat.Coprime s r), t345_eulerTerm n.natAbs s := by
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        simp only [hH]
        split_ifs
        · rfl
        · rw [mul_zero]

/-- Gallagher 1975 p.132 proof of display 17, an arithmetic step: phi(a b) is at most
a phi(b), since b/phi(b) is at most a b/phi(a b). -/
theorem t345_totient_mul_le_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ((a * b).totient : ℝ) ≤ a * b.totient := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have h1 : (b : ℝ) / b.totient ≤ ((a * b : ℕ) : ℝ) / (a * b).totient := by
    rw [t345_ratio_eq_prod hb, t345_ratio_eq_prod hab]
    apply Finset.prod_le_prod_of_subset_of_one_le₀
      (Nat.primeFactors_mono (dvd_mul_left b a) hab)
    · intro p hp
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : 0 ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
      linarith
    · intro p hp _
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : 0 ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
      linarith
  have hφb : (0 : ℝ) < b.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hb)
  have hφab : (0 : ℝ) < (a * b).totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hab)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
  rw [div_le_div_iff₀ hφb hφab] at h1
  push_cast at h1
  have : (b : ℝ) * (a * b).totient ≤ b * (a * b.totient) := by linarith
  exact le_of_mul_le_mul_left this hb0

/-- Gallagher 1975 p.132 proof of display 17, the last inequality: with g = (r, n),
r/(phi(r) phi(r_n)) times the product over p dividing n and not r of 1 + 1/(p - 1) is at
most r phi(g)/phi^2(r) times n/phi(n). This uses phi(r) at most g phi(r_n) and
g/phi(g) times that product equal to n/phi(n). -/
theorem t345_excFactor_mul_le {r N : ℕ} (hr : 0 < r) (hN : N ≠ 0) :
    t345_excFactor r N * ∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ r), (1 + ((p : ℝ) - 1)⁻¹) ≤
      (r : ℝ) * (Nat.gcd r N).totient / (r.totient : ℝ) ^ 2 * ((N : ℝ) / N.totient) := by
  set g := Nat.gcd r N with hgdef
  set k := r / g with hkdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hr
  have hrk : r = g * k := (Nat.mul_div_cancel' (Nat.gcd_dvd_left r N)).symm
  have hk : 1 ≤ k := Nat.div_pos (Nat.le_of_dvd hr (Nat.gcd_dvd_left r N)) hg0
  have hφr : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr hr
  have hφk : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
  have hφg : (0 : ℝ) < g.totient := by exact_mod_cast Nat.totient_pos.mpr hg0
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hg0' : (0 : ℝ) < g := by exact_mod_cast hg0
  have hle : (r.totient : ℝ) ≤ g * k.totient := by
    rw [hrk]; exact t345_totient_mul_le_mul hg0.ne' (by omega)
  have hgpf : g.primeFactors = N.primeFactors.filter (fun p => p ∣ r) := by
    rw [hgdef, Nat.primeFactors_gcd hr.ne' hN]
    ext p
    simp only [Finset.mem_inter, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, hpm, -⟩, hpN⟩
      exact ⟨hpN, hpm⟩
    · rintro ⟨hpN, hpm⟩
      exact ⟨⟨hpN.1, hpm, hr.ne'⟩, hpN⟩
  set PP := ∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ r), (1 + ((p : ℝ) - 1)⁻¹) with hPP
  have hprod : ((g : ℝ) / g.totient) * PP = (N : ℝ) / N.totient := by
    rw [hPP, t345_ratio_eq_prod hg0.ne', t345_ratio_eq_prod hN, hgpf,
      Finset.prod_filter_mul_prod_filter_not]
  have hP0 : 0 ≤ PP := by
    apply Finset.prod_nonneg
    intro p hp
    have : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
    have : 0 ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    linarith
  have hfac : t345_excFactor r N ≤ (r : ℝ) * g / (r.totient : ℝ) ^ 2 := by
    unfold t345_excFactor
    rw [← hgdef, ← hkdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (r : ℝ) * r.totient * r.totient ≤ (r : ℝ) * r.totient * (g * k.totient) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    nlinarith
  calc t345_excFactor r N * PP ≤ (r : ℝ) * g / (r.totient : ℝ) ^ 2 * PP :=
        mul_le_mul_of_nonneg_right hfac hP0
    _ = (r : ℝ) * g.totient / (r.totient : ℝ) ^ 2 * ((g : ℝ) / g.totient * PP) := by
        field_simp
    _ = _ := by rw [hprod]

/-- Gallagher 1975 p.131 proof of display 17, assembly for one weight: if every q term
satisfies the bound of `t345_exc_term_le`, then C_n is at most
4 n/phi(n) r phi((n, r))/phi^2(r), via the Euler product of Display7.lean. -/
theorem t345_weight_le_final (P : ℝ) (n : ℤ) (hn : n ≠ 0) {x y : PChar} {r : ℕ} (hr : 0 < r)
    (hm : Nat.lcm (x.1 + 1) (y.1 + 1) = r)
    (hterm : ∀ q ∈ pairModuli P x y, 1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q x y‖ ≤
      if Squarefree (q / r) ∧ Nat.Coprime (q / r) r then
        t345_excFactor r n.natAbs * t345_eulerTerm n.natAbs (q / r) else 0) :
    pairWeight P n x y ≤ 4 * totientWeight n * exceptionalWeight r n := by
  have hN : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have h1 := t345_weight_le_exc P n hr hm hterm
  have h2 := t345_euler_sum_le_prod (N := n.natAbs) (m := r) ⌊P⌋₊
  have h3 := t345_euler_prod_le (m := r) hN ⌊P⌋₊
  have h4 := t345_excFactor_mul_le hr hN
  have hA := t345_excFactor_nonneg r n.natAbs
  unfold totientWeight exceptionalWeight
  calc pairWeight P n x y
      ≤ t345_excFactor r n.natAbs * (4 * ∏ p ∈ n.natAbs.primeFactors.filter (fun p => ¬ p ∣ r),
          (1 + ((p : ℝ) - 1)⁻¹)) :=
        h1.trans (mul_le_mul_of_nonneg_left (h2.trans h3) hA)
    _ = 4 * (t345_excFactor r n.natAbs * ∏ p ∈ n.natAbs.primeFactors.filter (fun p => ¬ p ∣ r),
          (1 + ((p : ℝ) - 1)⁻¹)) := by ring
    _ ≤ 4 * ((r : ℝ) * (Nat.gcd r n.natAbs).totient / (r.totient : ℝ) ^ 2 *
          ((n.natAbs : ℝ) / n.natAbs.totient)) :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = _ := by ring

/-- Gallagher 1975 p.131 proof of display 17, C_n(chi~, 1): the q coefficient is
c_n(conj chi~_q) conj tau(conj chi~_q) tau(1_q), bounded by display 5 and display 6. -/
theorem t345_term_x_one (P : ℝ) (n : ℤ) {x : PChar} (hx : x.2.IsPrimitive) :
    ∀ q ∈ pairModuli P x one, 1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q x one‖ ≤
      if Squarefree (q / (x.1 + 1)) ∧ Nat.Coprime (q / (x.1 + 1)) (x.1 + 1) then
        t345_excFactor (x.1 + 1) n.natAbs * t345_eulerTerm n.natAbs (q / (x.1 + 1)) else 0 := by
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq'.1).1
  have hrq : x.1 + 1 ∣ q := (Nat.dvd_lcm_left _ _).trans hq'.2
  have : NeZero q := ⟨by omega⟩
  apply t345_exc_term_le hq1 hrq
  · unfold pairCoeff
    rw [t345_induced_one, inv_one, mul_one, norm_mul, norm_mul, norm_star]
    have hC := (induced_cn_bound hq1 (induced x q)⁻¹ n).1
    have hT := (t345_tau_bound hq1 (induced x q)⁻¹).1
    have hT1 := (t345_tau_bound hq1 (1 : DirichletCharacter ℂ q)).1
    rw [t345_conductor_induced_inv hx hq1 hrq] at hC hT
    rw [DirichletCharacter.conductor_one] at hT1
    simp only [Nat.cast_one, Real.sqrt_one] at hT1
    have hs := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) (x.1 + 1))
    calc ‖cn (induced x q)⁻¹ n‖ * ‖tau (induced x q)⁻¹‖ * ‖tau (1 : DirichletCharacter ℂ q)‖
        ≤ (Real.sqrt ((x.1 + 1 : ℕ) : ℝ) * q.totient / (q / Nat.gcd q n.natAbs).totient) *
            Real.sqrt ((x.1 + 1 : ℕ) : ℝ) * 1 := by gcongr
      _ = _ := by
        generalize Real.sqrt ((x.1 + 1 : ℕ) : ℝ) = t at hs ⊢
        rw [← hs]; ring
  · intro hz
    unfold pairCoeff at hz
    rw [t345_induced_one, inv_one, mul_one] at hz
    have ht : tau (induced x q)⁻¹ ≠ 0 := fun h => hz (by rw [h]; simp)
    have h := (t345_tau_bound hq1 (induced x q)⁻¹).2 ht
    rw [t345_conductor_induced_inv hx hq1 hrq] at h
    exact ⟨h.2.1, h.2.2⟩

/-- Gallagher 1975 p.131 proof of display 17, C_n(1, chi~), treated in the same way as
C_n(chi~, 1): the q coefficient is c_n(chi~_q) conj tau(1_q) tau(conj chi~_q). -/
theorem t345_term_one_x (P : ℝ) (n : ℤ) {x : PChar} (hx : x.2.IsPrimitive) :
    ∀ q ∈ pairModuli P one x, 1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q one x‖ ≤
      if Squarefree (q / (x.1 + 1)) ∧ Nat.Coprime (q / (x.1 + 1)) (x.1 + 1) then
        t345_excFactor (x.1 + 1) n.natAbs * t345_eulerTerm n.natAbs (q / (x.1 + 1)) else 0 := by
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq'.1).1
  have hrq : x.1 + 1 ∣ q := (Nat.dvd_lcm_right _ _).trans hq'.2
  have : NeZero q := ⟨by omega⟩
  apply t345_exc_term_le hq1 hrq
  · unfold pairCoeff
    rw [t345_induced_one, inv_one, one_mul, norm_mul, norm_mul, norm_star]
    have hC := (induced_cn_bound hq1 (induced x q) n).1
    have hT := (t345_tau_bound hq1 (induced x q)⁻¹).1
    have hT1 := (t345_tau_bound hq1 (1 : DirichletCharacter ℂ q)).1
    rw [t345_conductor_induced hx hq1 hrq] at hC
    rw [t345_conductor_induced_inv hx hq1 hrq] at hT
    rw [DirichletCharacter.conductor_one] at hT1
    simp only [Nat.cast_one, Real.sqrt_one] at hT1
    have hs := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) (x.1 + 1))
    calc ‖cn (induced x q) n‖ * ‖tau (1 : DirichletCharacter ℂ q)‖ * ‖tau (induced x q)⁻¹‖
        ≤ (Real.sqrt ((x.1 + 1 : ℕ) : ℝ) * q.totient / (q / Nat.gcd q n.natAbs).totient) *
            1 * Real.sqrt ((x.1 + 1 : ℕ) : ℝ) := by gcongr
      _ = _ := by
        generalize Real.sqrt ((x.1 + 1 : ℕ) : ℝ) = t at hs ⊢
        rw [← hs]; ring
  · intro hz
    unfold pairCoeff at hz
    rw [t345_induced_one, inv_one, one_mul] at hz
    have ht : tau (induced x q)⁻¹ ≠ 0 := fun h => hz (by rw [h]; simp)
    have h := (t345_tau_bound hq1 (induced x q)⁻¹).2 ht
    rw [t345_conductor_induced_inv hx hq1 hrq] at h
    exact ⟨h.2.1, h.2.2⟩

/-- Gallagher 1975 p.132 proof of display 17, C_n(chi~, chi~): the q coefficient is
|tau(conj chi~_q)|^2 c_q(n), with c_q(n) = c_n(1_q) bounded by display 5 for the principal
character and |tau|^2 at most r by display 6. -/
theorem t345_term_x_x (P : ℝ) (n : ℤ) {x : PChar} (hx : x.2.IsPrimitive) :
    ∀ q ∈ pairModuli P x x, 1 / (q.totient : ℝ) ^ 2 * ‖pairCoeff n q x x‖ ≤
      if Squarefree (q / (x.1 + 1)) ∧ Nat.Coprime (q / (x.1 + 1)) (x.1 + 1) then
        t345_excFactor (x.1 + 1) n.natAbs * t345_eulerTerm n.natAbs (q / (x.1 + 1)) else 0 := by
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq'.1).1
  have hrq : x.1 + 1 ∣ q := (Nat.dvd_lcm_left _ _).trans hq'.2
  have : NeZero q := ⟨by omega⟩
  apply t345_exc_term_le hq1 hrq
  · unfold pairCoeff
    rw [MulChar.inv_mul, norm_mul, norm_mul, norm_star]
    have hC := (induced_cn_bound hq1 (1 : DirichletCharacter ℂ q) n).1
    have hT := (t345_tau_bound hq1 (induced x q)⁻¹).1
    rw [t345_conductor_induced_inv hx hq1 hrq] at hT
    rw [DirichletCharacter.conductor_one] at hC
    simp only [Nat.cast_one, Real.sqrt_one, one_mul] at hC
    have hs := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) (x.1 + 1))
    calc ‖cn (1 : DirichletCharacter ℂ q) n‖ * ‖tau (induced x q)⁻¹‖ * ‖tau (induced x q)⁻¹‖
        ≤ ((q.totient : ℝ) / (q / Nat.gcd q n.natAbs).totient) *
            Real.sqrt ((x.1 + 1 : ℕ) : ℝ) * Real.sqrt ((x.1 + 1 : ℕ) : ℝ) := by gcongr
      _ = _ := by rw [mul_assoc, hs, mul_comm, mul_div_assoc]
  · intro hz
    unfold pairCoeff at hz
    have ht : tau (induced x q)⁻¹ ≠ 0 := fun h => hz (by rw [h]; simp)
    have h := (t345_tau_bound hq1 (induced x q)⁻¹).2 ht
    rw [t345_conductor_induced_inv hx hq1 hrq] at h
    exact ⟨h.2.1, h.2.2⟩

/-- Gallagher 1975 p.131 display 17, proved by the printed argument on pp.131 and 132 from
display 5, the CITED-LEFT leaf `induced_cn_bound`: C_n(chi~, 1) + C_n(1, chi~) + C_n(chi~, chi~)
is at most 12 n/phi(n) r phi((n, r))/phi^2(r) for every primitive chi~ to conductor r,
uniformly in P. Same statement as `exceptional_weight_bound`. -/
theorem t345_exceptional_weight_bound_of_cited :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℝ) (n : ℤ) (x : PChar), n ≠ 0 → x.2.IsPrimitive →
      pairWeight P n x one + pairWeight P n one x + pairWeight P n x x ≤
        K * totientWeight n * exceptionalWeight (x.1 + 1) n := by
  refine ⟨12, by norm_num, ?_⟩
  intro P n x hn hx
  have hr : 0 < x.1 + 1 := by omega
  have hone : one.1 = 0 := rfl
  have h1 := t345_weight_le_final P n hn hr (by rw [hone, Nat.lcm_one_right]) (t345_term_x_one P n hx)
  have h2 := t345_weight_le_final P n hn hr (by rw [hone, Nat.lcm_one_left]) (t345_term_one_x P n hx)
  have h3 := t345_weight_le_final P n hn hr (Nat.lcm_self _) (t345_term_x_x P n hx)
  linarith

end LeanLab.Linnik.MajorArcEnergy
