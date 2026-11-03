import LeanLab.LanguascoPintzZaccagnini2007.Decomp131
import LeanLab.ChebyshevExplicit.Psi30Upper
import LeanLab.AlmostPrimes.Decomp1528c

/-!
P0045 U-1608. Audit of the old leaves of DecompJ218.lean, display 25 and Corollary 4.2.
The old statements are kept here as definitions. Every audit theorem takes the leaves it
refutes as hypotheses and uses no sorry, so its axioms are the standard three.
AI wrote the Lean code. Goldbach is open.

Main results. `old_j1_false : ¬ OldJ1` and `old_j2_false : ¬ OldJ2` are UNCONDITIONAL, so the
false side of the lomos inconsistency is settled: it is J1 and J2, not combine. They average
over N: Chebyshev gives a sum of R'' over even N in J of order X^2 L, truncation and the proved
minor mean square reduce this to the major integrals, and S(N) is o(L) pointwise.

Finding. Old `major_arcs_j1_131` read Corollary 4.2, a statement on the binary integral at
k = 0, as a statement on the integral at k = 1. Old `major_arcs_j2_131` compared the k-fold
integral with N S(N) for every k. Each contradicts display 25 at the powers of two, where
S(N) is at most 2 while 2c0 C(1,N) N L has an extra factor L. Old `major_arcs_combine131`
quantified over all admissible P, which the paper does not prove: page 3 says P cannot be
fixed directly. It is NOT refuted; it is retired since it implies display 25 outright.
-/

namespace LeanLab.LPZ2007

open Finset Real Filter

noncomputable section

/-- Old leaf `major_arcs_j1_131`, verbatim. -/
def OldJ1 : Prop :=
  ∀ η : ℝ, 0 < η → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ, AdmissibleP131 X P →
    ∀ N ∈ evenJ131 X,
      |majorContribution131 1 X N P - (N : ℝ) * Sing N| ≤ η * (N : ℝ) * Sing N

/-- Old leaf `major_arcs_j2_131`, verbatim. -/
def OldJ2 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ η : ℝ, 0 < η → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    ∀ P : ℝ, AdmissibleP131 X P → ∀ N ∈ evenJ131 X,
      |majorContribution131 k X N P - (N : ℝ) * Sing N| ≤ η * (N : ℝ) * Lg X ^ k

/-- Old leaf `major_arcs_combine131`, verbatim. -/
def OldCombine : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ η : ℝ, 0 < η → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    ∀ P : ℝ, AdmissibleP131 X P → ∀ N ∈ evenJ131 X,
      |majorContribution131 k X N P - coefficient131 k N * N * Lg X ^ k| ≤
        η * (N : ℝ) * Lg X ^ k

/-- Display 25, the unchanged statement of `major_asymptotic131`. -/
def MajorAsymptoticStatement : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    ∃ P : ℝ, AdmissibleP131 X P ∧ ∀ N ∈ evenJ131 X,
      |majorContribution131 k X N P - coefficient131 k N * N * Lg X ^ k| ≤
        ε * N * Lg X ^ k

theorem Lg_two_pow1608 (a : ℕ) : Lg (2 ^ a) = a := by
  unfold Lg
  push_cast
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

theorem two_pow_mem1608 {a : ℕ} (ha : 1 ≤ a) : 2 ^ a ∈ evenJ131 (2 ^ a) := by
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨h1, le_rfl⟩, ?_, ?_⟩
  · exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  · have : (0 : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith

/-- The singular series at a power of two is at most 2. -/
theorem Sing_two_pow_le1608 (a : ℕ) : Sing (2 ^ a) ≤ 2 := by
  have h := sing_le_two_H (n := 2 ^ a) (by positivity)
  have hH : H (2 ^ a) = 1 := by
    unfold H
    have he : ((2 ^ a).primeFactors.filter (fun p => 2 < p)) = ∅ := by
      refine filter_eq_empty_iff.mpr fun p hp => ?_
      have := (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hp) Nat.prime_two).mp
        ((Nat.prime_of_mem_primeFactors hp).dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hp))
      omega
    rw [he, prod_empty]
  rw [hH] at h
  linarith

/-- Display 2 and Ck at least 1: the corrected coefficient is at least 13/10. -/
theorem coefficient_ge1608 {k : ℕ} (hk : 1 ≤ k) (N : ℕ) : 13 / 10 ≤ coefficient131 k N := by
  unfold coefficient131
  have h1 := Ck_ge_one131 hk N
  have h2 := LeanLab.ChenExplicit.twinC_ge_065
  nlinarith

/-- Display 25 at k = 1 forces a large major integral at the powers of two. -/
theorem major_lower1608 (hM : MajorAsymptoticStatement) (a₀ : ℕ) :
    ∃ a : ℕ, a₀ ≤ a ∧ 5 ≤ a ∧ a₀ ≤ 2 ^ a ∧ ∃ P : ℝ, AdmissibleP131 (2 ^ a) P ∧
      (21 / 20 : ℝ) * ((2 ^ a : ℕ) : ℝ) * a ≤ majorContribution131 1 (2 ^ a) (2 ^ a) P := by
  obtain ⟨X₀, hX₀⟩ := hM 1 le_rfl (1 / 4) (by norm_num)
  obtain ⟨a, hadef⟩ : ∃ a, a = max 5 (max a₀ X₀) := ⟨_, rfl⟩
  have ha5 : 5 ≤ a := by omega
  have ha0 : a₀ ≤ a := by omega
  have haX : X₀ ≤ a := by omega
  have hlt : a < 2 ^ a := Nat.lt_two_pow_self
  obtain ⟨P, hP, hb⟩ := hX₀ (2 ^ a) (by omega)
  refine ⟨a, ha0, ha5, by omega, P, hP, ?_⟩
  have h := hb (2 ^ a) (two_pow_mem1608 (by omega))
  rw [Lg_two_pow1608, pow_one] at h
  have hc := coefficient_ge1608 (k := 1) le_rfl (2 ^ a)
  have hA : (0 : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) * a := by positivity
  have h' := (abs_le.mp h).1
  have hm := mul_le_mul_of_nonneg_right hc hA
  linarith

/-- INCONSISTENT: old J1 contradicts display 25. -/
theorem old_j1_inconsistent_with_display25 (h1 : OldJ1) (hM : MajorAsymptoticStatement) :
    False := by
  obtain ⟨X₀, hX₀⟩ := h1 1 one_pos
  obtain ⟨a, _, ha5, hax, P, hP, hl⟩ := major_lower1608 hM X₀
  have h := hX₀ (2 ^ a) hax P hP (2 ^ a) (two_pow_mem1608 (by omega))
  have hS := Sing_two_pow_le1608 a
  have hS0 := Sing_nonneg131 (2 ^ a)
  have hN : (0 : ℝ) < ((2 ^ a : ℕ) : ℝ) := by positivity
  have hu := (abs_le.mp h).2
  have ha : (5 : ℝ) ≤ a := by exact_mod_cast ha5
  have hb : ((2 ^ a : ℕ) : ℝ) * Sing (2 ^ a) ≤ ((2 ^ a : ℕ) : ℝ) * 2 :=
    mul_le_mul_of_nonneg_left hS hN.le
  have hc : (21 / 20 : ℝ) * ((2 ^ a : ℕ) : ℝ) * 5 ≤ (21 / 20 : ℝ) * ((2 ^ a : ℕ) : ℝ) * a :=
    mul_le_mul_of_nonneg_left ha (by positivity)
  linarith

/-- INCONSISTENT: old J2 contradicts display 25. -/
theorem old_j2_inconsistent_with_display25 (h2 : OldJ2) (hM : MajorAsymptoticStatement) :
    False := by
  obtain ⟨X₀, hX₀⟩ := h2 1 le_rfl (1 / 4) (by norm_num)
  obtain ⟨a, _, ha5, hax, P, hP, hl⟩ := major_lower1608 hM X₀
  have h := hX₀ (2 ^ a) hax P hP (2 ^ a) (two_pow_mem1608 (by omega))
  rw [Lg_two_pow1608, pow_one] at h
  have hS := Sing_two_pow_le1608 a
  have hN : (0 : ℝ) < ((2 ^ a : ℕ) : ℝ) := by positivity
  have hu := (abs_le.mp h).2
  have ha : (5 : ℝ) ≤ a := by exact_mod_cast ha5
  have hb : ((2 ^ a : ℕ) : ℝ) * Sing (2 ^ a) ≤ ((2 ^ a : ℕ) : ℝ) * 2 :=
    mul_le_mul_of_nonneg_left hS hN.le
  have hc : ((2 ^ a : ℕ) : ℝ) * 5 ≤ ((2 ^ a : ℕ) : ℝ) * a :=
    mul_le_mul_of_nonneg_left ha hN.le
  linarith

/-- Old combine implies display 25, using the existing admissible P. -/
theorem old_combine_implies_display25 (h : OldCombine) : MajorAsymptoticStatement := by
  intro k hk ε hε
  obtain ⟨X₁, hX₁⟩ := h k hk ε hε
  obtain ⟨X₂, hX₂⟩ := admissible_P_exists131
  refine ⟨max X₁ X₂, fun X hX => ?_⟩
  obtain ⟨P, hP⟩ := hX₂ X (le_trans (le_max_right _ _) hX)
  exact ⟨P, hP, hX₁ X (le_trans (le_max_left _ _) hX) P hP⟩

/-- The lomos finding, re-proved: old J1 and old combine are inconsistent. -/
theorem old_j1_and_combine_inconsistent (h1 : OldJ1) (h3 : OldCombine) : False :=
  old_j1_inconsistent_with_display25 h1 (old_combine_implies_display25 h3)

/-- The lomos finding, re-proved: old J2 and old combine are inconsistent. -/
theorem old_j2_and_combine_inconsistent (h2 : OldJ2) (h3 : OldCombine) : False :=
  old_j2_inconsistent_with_display25 h2 (old_combine_implies_display25 h3)

/-- Under the two new leaf statements, old J1 is false. -/
theorem old_j1_false_of_new_leaves (hj : Cor42Statement131)
    (hc : SingularAverageStatement131) : ¬ OldJ1 := fun h1 =>
  old_j1_inconsistent_with_display25 h1 (major_asymptotic_of_leaves131 hj hc)

/-- Under the two new leaf statements, old J2 is false. -/
theorem old_j2_false_of_new_leaves (hj : Cor42Statement131)
    (hc : SingularAverageStatement131) : ¬ OldJ2 := fun h2 =>
  old_j2_inconsistent_with_display25 h2 (major_asymptotic_of_leaves131 hj hc)

/-! Unconditional refutation of the old J1 and J2. -/

/-- The singular series is o(L) uniformly on [1, X]. -/
theorem Sing_le_small1608 :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N : ℕ, 1 ≤ N → N ≤ X → Sing N ≤ (1 / 10000) * Lg X := by
  have ht : Tendsto (fun X : ℕ => Lg X) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hE : 0 < Real.exp 27 := Real.exp_pos _
  set c : ℝ := (1 / 10000) / (4 * Real.exp 27) with hc
  have hc0 : 0 < c := by
    rw [hc]
    positivity
  have h1 := Real.isLittleO_log_id_atTop.bound hc0
  obtain ⟨X₀, hX₀⟩ := ((ht.eventually h1).and
    (ht.eventually_ge_atTop (max 5 (1 / c)))).exists_forall_of_atTop
  refine ⟨X₀, fun X hX N hN1 hNX => ?_⟩
  obtain ⟨hb, hL⟩ := hX₀ X hX
  set x := Lg X with hx
  have hx5 : 5 ≤ x := (le_max_left _ _).trans hL
  have hxc : 1 / c ≤ x := (le_max_right _ _).trans hL
  have hcx : 1 ≤ c * x := by
    have := (div_le_iff₀ hc0).mp hxc
    linarith
  have hlogx : Real.log x ≤ c * x := by
    have hb' : ‖Real.log x‖ ≤ c * ‖x‖ := hb
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < x)] at hb'
    exact (le_abs_self _).trans hb'
  have hX0 : 0 < X := by omega
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNXr : (N : ℝ) ≤ X := by exact_mod_cast hNX
  have hpow : (2 : ℝ) ^ N.primeFactors.card ≤ (N : ℝ) := by
    exact_mod_cast LeanLab.Romanov.two_pow_card_le N (by omega)
  have hω : (N.primeFactors.card : ℝ) ≤ x := by
    have h2 : (2 : ℝ) ^ N.primeFactors.card ≤ X := hpow.trans hNXr
    rw [hx]
    unfold Lg
    rw [Real.le_logb_iff_rpow_le (by norm_num) hXr, Real.rpow_natCast]
    exact h2
  obtain ⟨y, hydef⟩ : ∃ y : ℕ, y = ⌈x⌉₊ + 4 := ⟨_, rfl⟩
  have hyhi : (y : ℝ) ≤ 2 * x := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
    have : (y : ℝ) = (⌈x⌉₊ : ℝ) + 4 := by
      rw [hydef]
      simp
    linarith
  have hωy : N.primeFactors.card ≤ y := by
    have : (N.primeFactors.card : ℝ) ≤ ⌈x⌉₊ := hω.trans (Nat.le_ceil x)
    have h' : N.primeFactors.card ≤ ⌈x⌉₊ := by exact_mod_cast this
    omega
  have hH : H N ≤ Real.exp 27 * Real.log y := by
    rw [H_eq_sum]
    exact sum_W_opf_le N y (by omega) hωy
  have hy0 : (0 : ℝ) < y := by
    have : 0 < y := by omega
    exact_mod_cast this
  have hlogy : Real.log y ≤ 2 * (c * x) := by
    have h := Real.log_le_log hy0 hyhi
    rw [Real.log_mul (by norm_num) (fun h0 => by linarith)] at h
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  have hS := sing_le_two_H (n := N) (by omega)
  have hfin : 2 * (Real.exp 27 * (2 * (c * x))) = (1 / 10000) * x := by
    rw [hc]
    field_simp <;> ring
  have hmono := mul_le_mul_of_nonneg_left hlogy hE.le
  linarith

/-- The gap of the Chebyshev function between X/3 and 49X/100. -/
theorem theta_gap1608 :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (1 / 25 : ℝ) * X ≤ Chebyshev.theta ((49 * X / 100 : ℕ) : ℝ) -
        Chebyshev.theta ((X / 3 : ℕ) : ℝ) := by
  have h1 := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (show (0 : ℝ) < 1 / 200 by norm_num)
  obtain ⟨X₀, hX₀⟩ := (tendsto_natCast_atTop_atTop.eventually h1).exists_forall_of_atTop
  refine ⟨max X₀ (10 ^ 9), fun X hX => ?_⟩
  have hb := hX₀ X (le_trans (le_max_left _ _) hX)
  have hXbig : 10 ^ 9 ≤ X := le_trans (le_max_right _ _) hX
  have hXr : (10 : ℝ) ^ 9 ≤ X := by exact_mod_cast hXbig
  have hb' : Real.log X ^ 2 ≤ (1 / 200) * (X : ℝ) := by
    have hb2 : ‖Real.log (X : ℝ) ^ 2‖ ≤ (1 / 200) * ‖(X : ℝ)‖ := hb
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (Nat.cast_nonneg X)] at hb2
    exact hb2
  set b := 49 * X / 100 with hbdef
  set a := X / 3 with hadef
  have hbl : 49 * X ≤ 100 * b + 99 := by omega
  have hbr : (49 : ℝ) * X ≤ 100 * b + 99 := by exact_mod_cast hbl
  have hal : 3 * a ≤ X := by omega
  have har : (3 : ℝ) * a ≤ X := by exact_mod_cast hal
  have ha1 : 1 ≤ a := by omega
  have har1 : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hlow := LeanLab.AlmostPrimes.Decomp1528c.theta_ge_09_large (x := (b : ℝ)) (by linarith)
  have hup := LeanLab.ChebyshevExplicit.theta_le_11062 a
  have hloga0 : 0 ≤ Real.log a := Real.log_nonneg har1
  have hloga : Real.log a ≤ Real.log X :=
    Real.log_le_log (by linarith) (by linarith)
  have hsq : Real.log a ^ 2 ≤ Real.log X ^ 2 := pow_le_pow_left₀ hloga0 hloga 2
  have e1 : (0.9 : ℝ) = 9 / 10 := by norm_num
  have e2 : (1.1062 : ℝ) = 11062 / 10000 := by norm_num
  rw [e1] at hlow
  rw [e2] at hup
  linarith

/-- Chebyshev masses give the lower bound for the sum of R'' over even N in J(X). -/
theorem sum_Rpp_lower1608 {X K : ℕ} (hX : 9 ≤ X) (hK : K ≤ Lp X) (hK2 : 50 * 2 ^ K ≤ X) :
    (Chebyshev.theta ((49 * X / 100 : ℕ) : ℝ) - Chebyshev.theta ((X / 3 : ℕ) : ℝ)) ^ 2 * K ≤
      ∑ N ∈ evenJ131 X, Rpp 1 X N := by
  set a := X / 3 with hadef
  set b := 49 * X / 100 with hbdef
  have hab : a ≤ b := by omega
  let S₁ : Finset ℕ := (Ioc 0 b).filter Nat.Prime
  let S₀ : Finset ℕ := (Ioc 0 a).filter Nat.Prime
  have hsub : S₀ ⊆ S₁ := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_filter.mp hp
    obtain ⟨h3, h4⟩ := mem_Ioc.mp h1
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨h3, h4.trans hab⟩, h2⟩
  let A : Finset ℕ := S₁ \ S₀
  have hmem : ∀ p ∈ A, p.Prime ∧ a < p ∧ p ≤ b := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_sdiff.mp hp
    obtain ⟨h3, h4⟩ := mem_filter.mp h1
    obtain ⟨h5, h6⟩ := mem_Ioc.mp h3
    refine ⟨h4, ?_, h6⟩
    by_contra hcon
    exact h2 (mem_filter.mpr ⟨mem_Ioc.mpr ⟨h5, by omega⟩, h4⟩)
  have hgap : Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) = ∑ p ∈ A, Real.log p := by
    have he := sum_sdiff (f := fun p : ℕ => Real.log p) hsub
    have hb : Chebyshev.theta (b : ℝ) = ∑ p ∈ S₁, Real.log p := by
      simp only [Chebyshev.theta, Nat.floor_natCast, S₁]
    have ha : Chebyshev.theta (a : ℝ) = ∑ p ∈ S₀, Real.log p := by
      simp only [Chebyshev.theta, Nat.floor_natCast, S₀]
    rw [hb, ha]
    linarith
  rw [hgap]
  set T := exponentTuples131 1 (Lp X) with hT
  set T' := exponentTuples131 1 K with hT'
  have hTT : T' ⊆ T := Fintype.piFinset_subset _ _ fun _ => Icc_subset_Icc_right hK
  let g : ℕ → ℕ → (Fin 1 → ℕ) → ℝ := fun m₁ m₂ ν =>
    if m₁ + m₂ + ∑ i, 2 ^ ν i ∈ evenJ131 X then
      ArithmeticFunction.vonMangoldt m₁ * ArithmeticFunction.vonMangoldt m₂ else 0
  have hg0 : ∀ m₁ m₂ ν, 0 ≤ g m₁ m₂ ν := by
    intro m₁ m₂ ν
    simp only [g]
    split_ifs
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl
  have hsw : ∑ N ∈ evenJ131 X, Rpp 1 X N =
      ∑ ν ∈ T, ∑ m₁ ∈ Icc 1 X, ∑ m₂ ∈ Icc 1 X, g m₁ m₂ ν := by
    simp only [Rpp_tuple_sum131, tuplePair131]
    calc _ = ∑ ν ∈ T, ∑ N ∈ evenJ131 X, ∑ m₁ ∈ Icc 1 X, ∑ m₂ ∈ Icc 1 X,
          (if m₁ + m₂ + ∑ i, 2 ^ ν i = N then
            ArithmeticFunction.vonMangoldt m₁ * ArithmeticFunction.vonMangoldt m₂ else 0) :=
          sum_comm
      _ = ∑ ν ∈ T, ∑ m₁ ∈ Icc 1 X, ∑ N ∈ evenJ131 X, ∑ m₂ ∈ Icc 1 X,
          (if m₁ + m₂ + ∑ i, 2 ^ ν i = N then
            ArithmeticFunction.vonMangoldt m₁ * ArithmeticFunction.vonMangoldt m₂ else 0) :=
          sum_congr rfl fun _ _ => sum_comm
      _ = ∑ ν ∈ T, ∑ m₁ ∈ Icc 1 X, ∑ m₂ ∈ Icc 1 X, ∑ N ∈ evenJ131 X,
          (if m₁ + m₂ + ∑ i, 2 ^ ν i = N then
            ArithmeticFunction.vonMangoldt m₁ * ArithmeticFunction.vonMangoldt m₂ else 0) :=
          sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
      _ = _ := by
          refine sum_congr rfl fun ν _ => sum_congr rfl fun m₁ _ =>
            sum_congr rfl fun m₂ _ => ?_
          exact Finset.sum_ite_eq _ _ _
  rw [hsw]
  have hAsub : A ⊆ Icc 1 X := fun p hp => by
    obtain ⟨h1, h2, h3⟩ := hmem p hp
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hAodd : ∀ p ∈ A, Odd p := fun p hp => by
    obtain ⟨h1, h2, -⟩ := hmem p hp
    exact h1.odd_of_ne_two (by omega)
  have hvalue : ∀ m₁ ∈ A, ∀ m₂ ∈ A, ∀ ν ∈ T',
      g m₁ m₂ ν = Real.log m₁ * Real.log m₂ := by
    intro m₁ h₁ m₂ h₂ ν hν
    have hν0 := mem_Icc.mp (Fintype.mem_piFinset.mp hν 0)
    have hpw : 2 ^ ν 0 ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hν0.2
    have hs : ∑ i, 2 ^ ν i = 2 ^ ν 0 := by simp [Fin.sum_univ_succ]
    have hev : Even (2 ^ ν 0) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    obtain ⟨hp1, ha1, hb1⟩ := hmem m₁ h₁
    obtain ⟨hp2, ha2, hb2⟩ := hmem m₂ h₂
    have hin : m₁ + m₂ + ∑ i, 2 ^ ν i ∈ evenJ131 X := by
      rw [hs]
      have hle : m₁ + m₂ + 2 ^ ν 0 ≤ X := by omega
      have hge : 2 * X ≤ 3 * (m₁ + m₂ + 2 ^ ν 0) := by omega
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hle⟩,
        ((hAodd m₁ h₁).add_odd (hAodd m₂ h₂)).add hev, ?_⟩
      have h' : 2 * (X : ℝ) ≤ 3 * ((m₁ + m₂ + 2 ^ ν 0 : ℕ) : ℝ) := by exact_mod_cast hge
      linarith
    simp only [g]
    rw [if_pos hin, ArithmeticFunction.vonMangoldt_apply_prime hp1,
      ArithmeticFunction.vonMangoldt_apply_prime hp2]
  calc (∑ p ∈ A, Real.log p) ^ 2 * K
      = ∑ ν ∈ T', ∑ m₁ ∈ A, ∑ m₂ ∈ A, g m₁ m₂ ν := by
        have hc : T'.card = K := by
          rw [hT', exponentTuples_card131, pow_one]
        have h1 : ∀ ν ∈ T', ∑ m₁ ∈ A, ∑ m₂ ∈ A, g m₁ m₂ ν =
            (∑ p ∈ A, Real.log p) ^ 2 := by
          intro ν hν
          rw [sq, sum_mul_sum]
          exact sum_congr rfl fun m₁ h₁ => sum_congr rfl fun m₂ h₂ => hvalue m₁ h₁ m₂ h₂ ν hν
        rw [sum_congr rfl h1, sum_const, hc, nsmul_eq_mul]
        ring
    _ ≤ ∑ ν ∈ T, ∑ m₁ ∈ A, ∑ m₂ ∈ A, g m₁ m₂ ν :=
        sum_le_sum_of_subset_of_nonneg hTT fun ν _ _ =>
          sum_nonneg fun m₁ _ => sum_nonneg fun m₂ _ => hg0 _ _ _
    _ ≤ ∑ ν ∈ T, ∑ m₁ ∈ A, ∑ m₂ ∈ Icc 1 X, g m₁ m₂ ν :=
        sum_le_sum fun ν _ => sum_le_sum fun m₁ _ =>
          sum_le_sum_of_subset_of_nonneg hAsub fun m₂ _ _ => hg0 _ _ _
    _ ≤ _ := sum_le_sum fun ν _ => sum_le_sum_of_subset_of_nonneg hAsub fun m₁ _ _ =>
        sum_nonneg fun m₂ _ => hg0 _ _ _

/-- The eventual size facts for L. -/
theorem size_facts1608 (K' : ℝ) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → 9 ≤ X ∧ 20 ≤ Lg X ∧
      10 ^ 8 * K' * Lg X ^ 9 ≤ (X : ℝ) ^ ((2 : ℝ) / 5) := by
  have ht : Tendsto (fun X : ℕ => Lg X) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := Real.log 2 ^ 9 / (10 ^ 8 * (|K'| + 1)) with hc
  have hc0 : 0 < c := by
    rw [hc]
    positivity
  have hl := ((isLittleO_log_rpow_rpow_atTop (s := (2 : ℝ) / 5) (9 : ℝ)
    (by norm_num)).bound hc0)
  obtain ⟨X₀, hX₀⟩ := ((tendsto_natCast_atTop_atTop.eventually hl).and
    (ht.eventually_ge_atTop 20)).exists_forall_of_atTop
  refine ⟨max 9 X₀, fun X hX => ?_⟩
  obtain ⟨hb, hL⟩ := hX₀ X (le_trans (le_max_right _ _) hX)
  have hX9 : 9 ≤ X := le_trans (le_max_left _ _) hX
  refine ⟨hX9, hL, ?_⟩
  have hXr : (9 : ℝ) ≤ X := by exact_mod_cast hX9
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hb' : Real.log X ^ (9 : ℝ) ≤ c * (X : ℝ) ^ ((2 : ℝ) / 5) := by
    have hb2 : ‖Real.log (X : ℝ) ^ (9 : ℝ)‖ ≤ c * ‖(X : ℝ) ^ ((2 : ℝ) / 5)‖ := hb
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)] at hb2
    exact hb2
  have h9 : Real.log X ^ (9 : ℝ) = Real.log X ^ 9 := by
    exact_mod_cast Real.rpow_natCast (Real.log X) 9
  rw [h9] at hb'
  have hLe : Lg X ^ 9 = Real.log X ^ 9 / Real.log 2 ^ 9 := by
    unfold Lg Real.logb
    rw [div_pow]
  have hP : 0 ≤ (X : ℝ) ^ ((2 : ℝ) / 5) := by positivity
  have hLn : 0 ≤ Lg X ^ 9 := by
    have : 0 ≤ Lg X := by linarith
    positivity
  have hK : K' ≤ |K'| + 1 := by linarith [le_abs_self K']
  have hK0 : 0 < |K'| + 1 := by positivity
  calc 10 ^ 8 * K' * Lg X ^ 9 ≤ 10 ^ 8 * (|K'| + 1) * Lg X ^ 9 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by norm_num)) hLn
    _ = 10 ^ 8 * (|K'| + 1) * (Real.log X ^ 9 / Real.log 2 ^ 9) := by rw [hLe]
    _ ≤ 10 ^ 8 * (|K'| + 1) * ((c * (X : ℝ) ^ ((2 : ℝ) / 5)) / Real.log 2 ^ 9) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact div_le_div_of_nonneg_right hb' (by positivity)
    _ = (X : ℝ) ^ ((2 : ℝ) / 5) := by
        rw [hc]
        field_simp

/-- Averaging: the major integrals at k = 1 cannot all be small compared with X L. -/
theorem mean_major_lower1608 :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ, AdmissibleP131 X P → ∀ B : ℝ, 0 ≤ B →
      (∀ N ∈ evenJ131 X, majorContribution131 1 X N P ≤ B) →
        (1 / 2000 : ℝ) * X * Lg X ≤ B := by
  obtain ⟨K', hK'0, X₁, hX₁⟩ := minor_mean_square131 1 le_rfl
  obtain ⟨X₂, hX₂⟩ := truncation131 1 le_rfl (1 / 10000) (by norm_num)
  obtain ⟨X₃, hX₃⟩ := theta_gap1608
  obtain ⟨X₄, hX₄⟩ := size_facts1608 K'
  refine ⟨max X₁ (max X₂ (max X₃ X₄)), fun X hX P hP B hB hM => ?_⟩
  have hx1 : X₁ ≤ X := by omega
  have hx2 : X₂ ≤ X := by omega
  have hx3 : X₃ ≤ X := by omega
  have hx4 : X₄ ≤ X := by omega
  obtain ⟨hX9, hL20, hsize⟩ := hX₄ X hx4
  have hgap := hX₃ X hx3
  set L := Lg X with hLdef
  have hL0 : 0 < L := by linarith
  have hXr : (0 : ℝ) < X := by
    have : 0 < X := by omega
    exact_mod_cast this
  have hLfl : (Lp X : ℝ) ≤ L := Nat.floor_le hL0.le
  have hLfl2 : L < (Lp X : ℝ) + 1 := Nat.lt_floor_add_one L
  have hLp6 : 6 ≤ Lp X := by
    have : (6 : ℝ) < (Lp X : ℝ) + 1 := by linarith
    have h' : (6 : ℝ) ≤ (Lp X : ℝ) := by linarith
    exact_mod_cast h'
  set K := Lp X - 6 with hKdef
  have hKr : (K : ℝ) + 6 = (Lp X : ℝ) := by
    have h : K + 6 = Lp X := by omega
    exact_mod_cast h
  have h2L : ((2 : ℝ) ^ (Lp X)) ≤ X := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hLfl
    rw [Real.rpow_natCast] at h
    have he : (2 : ℝ) ^ L = X := Real.rpow_logb (by norm_num) (by norm_num) hXr
    linarith
  have hK2 : 50 * 2 ^ K ≤ X := by
    have h1 : 2 ^ Lp X ≤ X := by exact_mod_cast h2L
    have h2 : 2 ^ Lp X = 64 * 2 ^ K := by
      rw [show Lp X = K + 6 by omega, pow_add]
      ring
    omega
  have hlow := sum_Rpp_lower1608 hX9 (by omega : K ≤ Lp X) hK2
  have hKL : L / 2 ≤ (K : ℝ) := by linarith
  have hglow : ((1 / 25 : ℝ) * X) ^ 2 * (L / 2) ≤ ∑ N ∈ evenJ131 X, Rpp 1 X N := by
    refine le_trans ?_ hlow
    have hg0 : (0 : ℝ) ≤ (1 / 25 : ℝ) * X := by positivity
    exact mul_le_mul (pow_le_pow_left₀ hg0 hgap 2) hKL (by positivity) (by positivity)
  have hcard : ((evenJ131 X).card : ℝ) ≤ X := by
    have h : (evenJ131 X).card ≤ (Icc 1 X).card := card_filter_le _ _
    have h2 : (evenJ131 X).card ≤ X := by simpa using h
    exact_mod_cast h2
  have hsumB : ∑ N ∈ evenJ131 X, majorContribution131 1 X N P ≤ X * B := by
    calc _ ≤ ∑ _N ∈ evenJ131 X, B := sum_le_sum hM
      _ = ((evenJ131 X).card : ℝ) * B := by rw [sum_const, nsmul_eq_mul]
      _ ≤ X * B := mul_le_mul_of_nonneg_right hcard hB
  have htr : ∑ N ∈ evenJ131 X,
      (Rpp 1 X N - majorContribution131 1 X N P - minorContribution131 1 X N P) ≤
        (1 / 10000) * (X : ℝ) ^ 2 * L := by
    calc _ ≤ ∑ _N ∈ evenJ131 X, (1 / 10000) * (X : ℝ) * L := by
          refine sum_le_sum fun N hN => ?_
          have h := hX₂ X hx2 P hP N hN
          rw [pow_one] at h
          have hNX : (N : ℝ) ≤ X := by exact_mod_cast (evenJ_nat131 hN).2.1
          have h3 : (1 / 10000) * (N : ℝ) * L ≤ (1 / 10000) * (X : ℝ) * L :=
            mul_le_mul_of_nonneg_right (by linarith) hL0.le
          exact (le_abs_self _).trans (h.trans h3)
      _ = ((evenJ131 X).card : ℝ) * ((1 / 10000) * (X : ℝ) * L) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (X : ℝ) * ((1 / 10000) * (X : ℝ) * L) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  have hminor : ∑ N ∈ evenJ131 X, minorContribution131 1 X N P ≤
      (1 / 10000) * (X : ℝ) ^ 2 * L := by
    have hms := hX₁ X hx1 P hP
    have hcs : (∑ N ∈ evenJ131 X, minorContribution131 1 X N P) ^ 2 ≤
        ((evenJ131 X).card : ℝ) * ∑ N ∈ evenJ131 X, minorContribution131 1 X N P ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hL11 : 0 ≤ L ^ 11 := by positivity
    have hpow : (X : ℝ) * (X : ℝ) ^ ((13 : ℝ) / 5) * (X : ℝ) ^ ((2 : ℝ) / 5) = (X : ℝ) ^ 4 := by
      have h1 : (X : ℝ) ^ ((13 : ℝ) / 5) * (X : ℝ) ^ ((2 : ℝ) / 5) = (X : ℝ) ^ 3 := by
        have he : (13 : ℝ) / 5 + 2 / 5 = ((3 : ℕ) : ℝ) := by norm_num
        rw [← Real.rpow_add hXr, he, Real.rpow_natCast]
      rw [mul_assoc, h1]
      ring
    have hA : (0 : ℝ) ≤ (X : ℝ) ^ ((13 : ℝ) / 5) := by positivity
    have hsq : (∑ N ∈ evenJ131 X, minorContribution131 1 X N P) ^ 2 ≤
        ((1 / 10000) * (X : ℝ) ^ 2 * L) ^ 2 := by
      have h1 : (∑ N ∈ evenJ131 X, minorContribution131 1 X N P) ^ 2 ≤
          (X : ℝ) * (K' * (X : ℝ) ^ ((13 : ℝ) / 5) * L ^ 11) := by
        refine hcs.trans ?_
        have hs0 : 0 ≤ ∑ N ∈ evenJ131 X, minorContribution131 1 X N P ^ 2 :=
          sum_nonneg fun _ _ => sq_nonneg _
        have hms' : ∑ N ∈ evenJ131 X, minorContribution131 1 X N P ^ 2 ≤
            K' * (X : ℝ) ^ ((13 : ℝ) / 5) * L ^ 11 := hms
        exact mul_le_mul hcard hms' hs0 hXr.le
      have h2 : 10 ^ 8 * K' * L ^ 9 * ((X : ℝ) * (X : ℝ) ^ ((13 : ℝ) / 5) * L ^ 2) ≤
          (X : ℝ) ^ ((2 : ℝ) / 5) * ((X : ℝ) * (X : ℝ) ^ ((13 : ℝ) / 5) * L ^ 2) :=
        mul_le_mul_of_nonneg_right hsize (by positivity)
      have h3 : (X : ℝ) ^ ((2 : ℝ) / 5) * ((X : ℝ) * (X : ℝ) ^ ((13 : ℝ) / 5) * L ^ 2) =
          (X : ℝ) ^ 4 * L ^ 2 := by
        rw [← hpow]
        ring
      have h4 : ((1 / 10000) * (X : ℝ) ^ 2 * L) ^ 2 = (X : ℝ) ^ 4 * L ^ 2 / 10 ^ 8 := by
        ring
      rw [h4, le_div_iff₀ (by norm_num)]
      have h5 : (X : ℝ) * (K' * (X : ℝ) ^ ((13 : ℝ) / 5) * L ^ 11) * 10 ^ 8 =
          10 ^ 8 * K' * L ^ 9 * ((X : ℝ) * (X : ℝ) ^ ((13 : ℝ) / 5) * L ^ 2) := by
        ring
      have h1' := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 10 ^ 8)
      linarith
    by_contra hcon
    push_neg at hcon
    have hb0 : 0 ≤ (1 / 10000) * (X : ℝ) ^ 2 * L := by positivity
    exact absurd hsq (not_le.mpr (pow_lt_pow_left₀ hcon hb0 two_ne_zero))
  have hsplit : ∑ N ∈ evenJ131 X, Rpp 1 X N =
      ∑ N ∈ evenJ131 X,
        (Rpp 1 X N - majorContribution131 1 X N P - minorContribution131 1 X N P) +
      ∑ N ∈ evenJ131 X, majorContribution131 1 X N P +
      ∑ N ∈ evenJ131 X, minorContribution131 1 X N P := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun _ _ => ?_
    ring
  have hfin : (6 / 10000 : ℝ) * (X : ℝ) ^ 2 * L ≤ X * B := by
    have hexp : ((1 / 25 : ℝ) * X) ^ 2 * (L / 2) = (8 / 10000) * (X : ℝ) ^ 2 * L := by ring
    linarith
  have hfin2 : (X : ℝ) * ((6 / 10000 : ℝ) * X * L) ≤ X * B := by
    calc _ = (6 / 10000 : ℝ) * (X : ℝ) ^ 2 * L := by ring
      _ ≤ _ := hfin
  have hfin3 := le_of_mul_le_mul_left hfin2 hXr
  have : (1 / 2000 : ℝ) * X * L ≤ (6 / 10000 : ℝ) * X * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hXr.le) hL0.le
  linarith

/-- REFUTATION, unconditional: old `major_arcs_j1_131` is false. -/
theorem old_j1_false : ¬ OldJ1 := by
  intro h1
  obtain ⟨X₁, hX₁⟩ := h1 1 one_pos
  obtain ⟨X₂, hX₂⟩ := mean_major_lower1608
  obtain ⟨X₃, hX₃⟩ := Sing_le_small1608
  obtain ⟨X₄, hX₄⟩ := admissible_P_exists131
  obtain ⟨X₅, hX₅⟩ := size_facts1608 0
  obtain ⟨X, hXdef⟩ : ∃ X, X = max X₁ (max X₂ (max X₃ (max X₄ X₅))) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ := hX₄ X (by omega)
  obtain ⟨hX9, hL20, -⟩ := hX₅ X (by omega)
  have hXr : (0 : ℝ) < X := by
    have : 0 < X := by omega
    exact_mod_cast this
  have hL0 : 0 < Lg X := by linarith
  have hB : (2 / 10000 : ℝ) * X * Lg X < (1 / 2000 : ℝ) * X * Lg X :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right (by norm_num) hXr) hL0
  refine absurd (hX₂ X (by omega) P hP ((2 / 10000 : ℝ) * X * Lg X) (by positivity)
    (fun N hN => ?_)) (not_le.mpr hB)
  have h := hX₁ X (by omega) P hP N hN
  obtain ⟨hN1, hNX, -, -⟩ := evenJ_nat131 hN
  have hS := hX₃ X (by omega) N hN1 hNX
  have hS0 := Sing_nonneg131 N
  have hNr : (N : ℝ) ≤ X := by exact_mod_cast hNX
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hu := (abs_le.mp h).2
  have h3 : (N : ℝ) * Sing N ≤ X * ((1 / 10000) * Lg X) :=
    mul_le_mul hNr hS hS0 hXr.le
  linarith

/-- REFUTATION, unconditional: old `major_arcs_j2_131` is false, already at k = 1. -/
theorem old_j2_false : ¬ OldJ2 := by
  intro h2
  obtain ⟨X₁, hX₁⟩ := h2 1 le_rfl (1 / 10000) (by norm_num)
  obtain ⟨X₂, hX₂⟩ := mean_major_lower1608
  obtain ⟨X₃, hX₃⟩ := Sing_le_small1608
  obtain ⟨X₄, hX₄⟩ := admissible_P_exists131
  obtain ⟨X₅, hX₅⟩ := size_facts1608 0
  obtain ⟨X, hXdef⟩ : ∃ X, X = max X₁ (max X₂ (max X₃ (max X₄ X₅))) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ := hX₄ X (by omega)
  obtain ⟨hX9, hL20, -⟩ := hX₅ X (by omega)
  have hXr : (0 : ℝ) < X := by
    have : 0 < X := by omega
    exact_mod_cast this
  have hL0 : 0 < Lg X := by linarith
  have hB : (2 / 10000 : ℝ) * X * Lg X < (1 / 2000 : ℝ) * X * Lg X :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right (by norm_num) hXr) hL0
  refine absurd (hX₂ X (by omega) P hP ((2 / 10000 : ℝ) * X * Lg X) (by positivity)
    (fun N hN => ?_)) (not_le.mpr hB)
  have h := hX₁ X (by omega) P hP N hN
  rw [pow_one] at h
  obtain ⟨hN1, hNX, -, -⟩ := evenJ_nat131 hN
  have hS := hX₃ X (by omega) N hN1 hNX
  have hS0 := Sing_nonneg131 N
  have hNr : (N : ℝ) ≤ X := by exact_mod_cast hNX
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hu := (abs_le.mp h).2
  have h3 : (N : ℝ) * Sing N ≤ X * ((1 / 10000) * Lg X) :=
    mul_le_mul hNr hS hS0 hXr.le
  have h4 : (1 / 10000 : ℝ) * N * Lg X ≤ (1 / 10000) * X * Lg X :=
    mul_le_mul_of_nonneg_right (by linarith) hL0.le
  linarith

/-! Vacuity instances: the hypotheses of the new statements can hold. -/

theorem oddRad_three1608 : oddRad131 3 = 3 := by
  unfold oddRad131
  rw [Nat.Prime.primeFactors Nat.prime_three, Finset.filter_singleton, if_pos (by norm_num),
    prod_singleton]

/-- A nonempty family of exceptional moduli exists: E = {3}, K₁ = 1, c = 1, X = 2. -/
theorem exceptional_instance1608 : ExceptionalModuli131 1 1 2 {3} := by
  refine ⟨by simp, fun r hr => ?_⟩
  rw [mem_singleton.mp hr, oddRad_three1608]
  have : Lg 2 = 1 := by simpa using Lg_two_pow1608 1
  rw [this]
  norm_num

/-- The empty family is allowed at every X. -/
theorem exceptional_empty1608 (K₁ : ℕ) (c : ℝ) (X : ℕ) : ExceptionalModuli131 K₁ c X ∅ := by
  exact ⟨by simp, by simp⟩

/-- Display 9 can hold for a nonempty E. -/
theorem nonexceptional_instance1608 : Nonexceptional131 1 {3} 4 := by
  intro r hr
  rw [mem_singleton.mp hr]
  decide

/-- Display 9 can fail, so the split into J_1 and J_2 is real. -/
theorem exceptional_point1608 : ¬ Nonexceptional131 1 {3} 6 := by
  intro h
  exact h 3 (by simp) (by decide)

/-- The window is nonempty. -/
theorem window_instance1608 : 4 ∈ evenWindow131 8 := by
  refine mem_filter.mpr ⟨by simp, by decide, by norm_num⟩

/-- A J(X) point near 2X/3 has a shift below 2X/3: the reason for the window. X = 300,
N = 200, M = 2. It stays in the window [X/2, X] but leaves J(X). -/
theorem window_needed1608 :
    (200 : ℕ) ∈ evenJ131 300 ∧ (200 - 2 : ℕ) ∉ evenJ131 300 ∧ (200 - 2 : ℕ) ∈ evenWindow131 300 := by
  refine ⟨mem_filter.mpr ⟨by simp, by decide, by norm_num⟩, ?_,
    mem_filter.mpr ⟨by simp, by decide, by norm_num⟩⟩
  intro h
  have := (mem_filter.mp h).2.2
  norm_num at this

/-- A tuple exists at X = 16, where L' = 4 - 2 = 2. -/
theorem tuple_instance1608 : (fun _ => 1 : Fin 1 → ℕ) ∈ tuples131 1 16 := by
  have hL : Lg 16 = 4 := by simpa using Lg_two_pow1608 4
  have hs : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hf : ⌊Lg 16 - Real.sqrt (Lg 16)⌋₊ = 2 := by
    rw [hL, hs]
    norm_num
  simp only [tuples131, exponentTuples131, Fintype.mem_piFinset, mem_Icc]
  intro _
  rw [hf]
  omega

/-- The binary integral is the k = 0 integral. -/
theorem binaryMajor_is_k_zero1608 (X n : ℕ) (P : ℝ) :
    binaryMajor131 X n P = majorContribution131 0 X n P := rfl

end

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.old_j1_false
#print axioms LeanLab.LPZ2007.old_j2_false
#print axioms LeanLab.LPZ2007.old_j1_inconsistent_with_display25
#print axioms LeanLab.LPZ2007.old_j2_inconsistent_with_display25
#print axioms LeanLab.LPZ2007.old_j1_and_combine_inconsistent
#print axioms LeanLab.LPZ2007.old_j2_and_combine_inconsistent
#print axioms LeanLab.LPZ2007.old_combine_implies_display25
#print axioms LeanLab.LPZ2007.old_j1_false_of_new_leaves
#print axioms LeanLab.LPZ2007.old_j2_false_of_new_leaves
#print axioms LeanLab.LPZ2007.major_asymptotic_of_leaves131
#print axioms LeanLab.LPZ2007.major_arcs_j2_131
#print axioms LeanLab.LPZ2007.major_expand131
#print axioms LeanLab.LPZ2007.major_arcs_j1_131
#print axioms LeanLab.LPZ2007.major_arcs_combine131
#print axioms LeanLab.LPZ2007.major_asymptotic131_assembly
#print axioms LeanLab.LPZ2007.major_asymptotic131
#print axioms LeanLab.LPZ2007.repaired_mainJ131
#print axioms LeanLab.LPZ2007.tuple_instance1608
#print axioms LeanLab.LPZ2007.exceptional_instance1608
#print axioms LeanLab.LPZ2007.window_needed1608
