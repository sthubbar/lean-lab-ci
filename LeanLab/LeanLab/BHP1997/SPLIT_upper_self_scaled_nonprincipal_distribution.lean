/-
Split of the OPEN target `upper_self_scaled_nonprincipal_distribution` of
SPLIT_upper_self_scaled_conditions into four leaves, one per term of the four term identity for
the self scaled upper coefficient, and an assembly that has the target's statement verbatim and
uses no sorry.

The target asks condition iii of page 3 for the non-principal characters: the short interval sums
of the self scaled upper coefficient, truncated at `t`, save every power of the logarithm
uniformly in the modulus up to `log x ^ A`, in the character other than the trivial one and in
`t`. The coefficient on the window is the recentring factor `log m / log Y` times the raw page 53
weight at level `m`, and the raw weight is the alternating sum of the four terms of the identity
`psi(m, Y^c4) = g_m - h_m + j_m - (kept part of k_m)` with the level measured at `m` itself.

Leaf 1 is the `g` term, leaf 2 the `h` term, leaf 3 the `j` term and leaf 4 the kept part of the
`k` term, each with the same `A`, `x`, `q`, `chi`, `t` quantifiers as the target and with the whole
recentring factor inside the summand, so each is one summand of the target's sum and strictly
weaker than it. The assembly `upper_self_scaled_nonprincipal_distribution_split` splits the
summand by the identity, sums the four pieces with subadditivity of the norm, and takes one
constant serving the four pieces and the threshold at once.

Leaf 1, the `g` term, is PROVED. The self scaled rough indicator is split at its least prime
factor (`self_rough_sum_split`, from the minFac fibration of the self scaled sum): the fibre of a
prime factor above `⌊Y⌋` is exactly a prime, and every other fibre is a rough character sum at the
fixed level of its least prime factor, which `Rough514.rough_character_interval` bounds with an
arbitrary logarithmic saving. Partial summation against the monotone recentring factor
`log m / log Y` is `sum_mono_mul_le_of_prefix`, and the reciprocal sum over the fibres costs one
logarithm. That leaf therefore uses the import `LeanLab.BHP1997.RoughFamily514`, whose closure is
axiom clean (`propext`, `Classical.choice`, `Quot.sound`). Leaves 2, 3 and 4 remain OPEN. This file
adds no definition, changes no existing file, and leaves the sealed statement untouched. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_upper_self_scaled_conditions
import LeanLab.BHP1997.RoughFamily514

namespace LeanLab.BHP1997.Upper312Route
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators

/-! ### Elementary complex bookkeeping used by the assembly -/

/-- A sum of four alternating complex pieces is the alternating sum of the four sums. -/
private lemma sum_four_sub (s : Finset ℕ) (f g h k : ℕ → ℂ) :
    (∑ m ∈ s, (f m - g m + h m - k m)) =
      (∑ m ∈ s, f m) - (∑ m ∈ s, g m) + (∑ m ∈ s, h m) - (∑ m ∈ s, k m) := by
  have h1 : ∀ m, (f m - g m + h m - k m) = (f m - g m) + (h m - k m) := by
    intro m
    abel
  simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

/-- A real factor in front of an alternating sum of four real pieces multiplies each piece. -/
private lemma ofReal_mul_four (a b c d e : ℝ) (z : ℂ) :
    ((a * (b - c + d - e) : ℝ) : ℂ) * z =
      ((a * b : ℝ) : ℂ) * z - ((a * c : ℝ) : ℂ) * z + ((a * d : ℝ) : ℂ) * z -
        ((a * e : ℝ) : ℂ) * z := by
  push_cast
  ring

/-- The norm of an alternating sum of four complex numbers is at most the sum of the four norms. -/
private lemma norm_sub_add_sub_le (a b c d : ℂ) :
    ‖a - b + c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 : a - b + c - d = (a - b) + (c - d) := by abel
  rw [h1]
  calc ‖(a - b) + (c - d)‖ ≤ ‖a - b‖ + ‖c - d‖ := norm_add_le _ _
    _ ≤ (‖a‖ + ‖b‖) + (‖c‖ + ‖d‖) := add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
    _ = ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by ring

/-! ### Elementary bookkeeping for the self scaled rough indicator -/

/-- For `m ≥ 2` the page 53 rough indicator tests the level against the smallest prime factor. -/
private lemma forall_primeFactors_le_iff {m : ℕ} (hm : 2 ≤ m) (w : ℝ) :
    (∀ p ∈ m.primeFactors, w ≤ (p : ℝ)) ↔ w ≤ (m.minFac : ℝ) := by
  constructor
  · intro h
    exact h _ (Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd m, by omega⟩)
  · intro h p hp
    obtain ⟨hpq, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
    exact h.trans (by exact_mod_cast Nat.minFac_le_of_dvd hpq.two_le hpdvd)

/-- Rewriting `upperRough` at `m ≥ 2` as the test `w ≤ minFac m`. -/
private lemma upperRough_eq_minFac {m : ℕ} (hm : 2 ≤ m) (w : ℝ) :
    upperRough m w = if w ≤ (m.minFac : ℝ) then 1 else 0 := by
  unfold upperRough
  by_cases h : ∀ p ∈ m.primeFactors, w ≤ (p : ℝ)
  · rw [if_pos h, if_pos ((forall_primeFactors_le_iff hm w).1 h)]
  · rw [if_neg h, if_neg (fun hw => h ((forall_primeFactors_le_iff hm w).2 hw))]

/-- Rewriting the lab's `roughIndicator` at `n ≥ 2` as the test `z ≤ minFac n`. -/
private lemma roughIndicator_eq_minFac {n : ℕ} (hn : 2 ≤ n) (z : ℕ) :
    Task308.roughIndicator n z = if z ≤ n.minFac then 1 else 0 := by
  unfold Task308.roughIndicator
  by_cases h : z ≤ n.minFac
  · rw [if_pos (Or.inr h), if_pos h]
  · rw [if_neg (fun hh => hh.elim (by omega) h), if_neg h]

/-- The least prime factor of `p * n` is `p` when `p` is prime and the cofactor `n` has no
prime factor below `p`. -/
private lemma minFac_mul_of_rough {p n : ℕ} (hp : p.Prime) (hn1 : 1 ≤ n)
    (hn : Task308.roughIndicator n p = 1) :
    (p * n).minFac = p := by
  have hle : (p * n).minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le (Nat.dvd_mul_right p n)
  have hge : p ≤ (p * n).minFac := by
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn1' : n = 1 := by omega
      subst hn1'
      rw [mul_one, Nat.Prime.minFac_eq hp]
    · have hne : p * n ≠ 1 := by
        have h2 : 2 * 2 ≤ p * n := Nat.mul_le_mul hp.two_le hn2
        omega
      have hq := Nat.minFac_prime hne
      have hqdvd : (p * n).minFac ∣ p * n := Nat.minFac_dvd _
      rcases (hq.dvd_mul.mp hqdvd) with h | h
      · have heq : (p * n).minFac = p := (Nat.dvd_prime_two_le hp hq.two_le).1 h
        rw [heq]
      · have hrough : p ≤ n.minFac := by
          by_contra hlt
          push_neg at hlt
          rw [roughIndicator_eq_minFac hn2, if_neg (by omega)] at hn
          exact absurd hn (by norm_num)
        have := Nat.minFac_le_of_dvd hq.two_le h
        omega
  omega

/-! ### Partial summation -/

/-- Telescoping along an interval of the successive differences of a real sequence. -/
private lemma sum_Ioc_diff (g : ℕ → ℝ) {A M : ℕ} (hAM : A ≤ M) :
    ∑ m ∈ Finset.Ioc A M, (g (m + 1) - g m) = g (M + 1) - g (A + 1) := by
  induction M, hAM using Nat.le_induction with
  | base => simp
  | succ M hAM ih =>
      rw [Finset.sum_Ioc_succ_top hAM, ih]
      ring

/-- Abel summation: an alternating sum with a monotone factor is the top factor times the whole
prefix sum minus the increments against the shorter prefix sums. -/
private lemma abel_identity {f : ℕ → ℂ} (g : ℕ → ℝ) (A : ℕ) :
    ∀ B : ℕ, A ≤ B →
      ∑ m ∈ Finset.Ioc A B, (g m : ℂ) * f m =
        (g B : ℂ) * (∑ m ∈ Finset.Ioc A B, f m) -
          ∑ m ∈ Finset.Ioc A (B - 1), ((g (m + 1) - g m : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc A m, f k) := by
  intro B hAB
  induction B, hAB using Nat.le_induction with
  | base =>
      rw [Finset.Ioc_eq_empty_of_le (by omega : A - 1 ≤ A)]
      simp
  | succ B hAB ih =>
      by_cases hBA : A = B
      · subst hBA
        rw [show (A + 1) - 1 = A from by omega, Finset.sum_Ioc_succ_top (le_refl A)]
        simp
      · have hlt : A < B := lt_of_le_of_ne hAB hBA
        have hB1 : B - 1 + 1 = B := by omega
        have hsplit := Finset.sum_Ioc_succ_top (a := A) (b := B - 1)
          (by omega : A ≤ B - 1)
          (fun m => ((g (m + 1) - g m : ℝ) : ℂ) * (∑ k ∈ Finset.Ioc A m, f k))
        rw [hB1] at hsplit
        have hP : ∑ m ∈ Finset.Ioc A (B + 1), f m =
            ∑ m ∈ Finset.Ioc A B, f m + f (B + 1) := Finset.sum_Ioc_succ_top hAB _
        have hL : ∑ m ∈ Finset.Ioc A (B + 1), (g m : ℂ) * f m =
            ∑ m ∈ Finset.Ioc A B, (g m : ℂ) * f m + (g (B + 1) : ℂ) * f (B + 1) :=
          Finset.sum_Ioc_succ_top hAB _
        rw [show B + 1 - 1 = B from by omega, hsplit, hP, hL, ih]
        push_cast
        ring

/-- Partial summation bound: a nonnegative monotone factor in front of a sequence is controlled
by twice the value of the factor at the top times the maximal prefix bound. -/
private lemma sum_mono_mul_le_of_prefix {f : ℕ → ℂ} {g : ℕ → ℝ} {A B : ℕ} (hAB : A ≤ B)
    {M : ℝ} (hM : 0 ≤ M) (hgA : 0 ≤ g (A + 1)) (hgB : 0 ≤ g B)
    (hinc : ∀ m ∈ Finset.Ioc A (B - 1), g m ≤ g (m + 1))
    (hP : ∀ k, A ≤ k → k ≤ B → ‖∑ m ∈ Finset.Ioc A k, f m‖ ≤ M) :
    ‖∑ m ∈ Finset.Ioc A B, (g m : ℂ) * f m‖ ≤ 2 * g B * M := by
  rw [abel_identity g A B hAB]
  have hterm : ∀ m ∈ Finset.Ioc A (B - 1),
      ‖((g (m + 1) - g m : ℝ) : ℂ) * (∑ k ∈ Finset.Ioc A m, f k)‖
        ≤ (g (m + 1) - g m) * M := by
    intro m hm
    have hmlt : A < m := (Finset.mem_Ioc.mp hm).1
    have hmle : m ≤ B - 1 := (Finset.mem_Ioc.mp hm).2
    have hnn : 0 ≤ (g (m + 1) - g m) := by linarith [hinc m hm]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left (hP m (le_of_lt hmlt) (by omega)) hnn
  have htel : ∑ m ∈ Finset.Ioc A (B - 1), (g (m + 1) - g m) ≤ g B := by
    rcases Nat.lt_or_ge A B with hlt | hge
    · have h := sum_Ioc_diff g (show A ≤ B - 1 by omega)
      rw [show B - 1 + 1 = B from by omega] at h
      rw [h]
      linarith
    · have hnil : Finset.Ioc A (B - 1) = ∅ := Finset.Ioc_eq_empty_of_le (by omega)
      rw [hnil, Finset.sum_empty]
      exact hgB
  have hS : ‖∑ m ∈ Finset.Ioc A (B - 1),
      ((g (m + 1) - g m : ℝ) : ℂ) * (∑ k ∈ Finset.Ioc A m, f k)‖ ≤ g B * M := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ m ∈ Finset.Ioc A (B - 1),
          ‖((g (m + 1) - g m : ℝ) : ℂ) * (∑ k ∈ Finset.Ioc A m, f k)‖
        ≤ ∑ m ∈ Finset.Ioc A (B - 1), (g (m + 1) - g m) * M :=
          Finset.sum_le_sum hterm
      _ = M * ∑ m ∈ Finset.Ioc A (B - 1), (g (m + 1) - g m) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
      _ ≤ M * g B := mul_le_mul_of_nonneg_left htel hM
      _ = g B * M := by ring
  have h1 : ‖(g B : ℂ) * (∑ m ∈ Finset.Ioc A B, f m)‖ ≤ g B * M := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgB]
    exact mul_le_mul_of_nonneg_left (hP B hAB le_rfl) hgB
  calc ‖(g B : ℂ) * (∑ m ∈ Finset.Ioc A B, f m) -
        ∑ m ∈ Finset.Ioc A (B - 1),
          ((g (m + 1) - g m : ℝ) : ℂ) * (∑ k ∈ Finset.Ioc A m, f k)‖
      ≤ ‖(g B : ℂ) * (∑ m ∈ Finset.Ioc A B, f m)‖ +
        ‖∑ m ∈ Finset.Ioc A (B - 1),
          ((g (m + 1) - g m : ℝ) : ℂ) * (∑ k ∈ Finset.Ioc A m, f k)‖ := norm_sub_le _ _
    _ ≤ g B * M + g B * M := add_le_add h1 hS
    _ = 2 * g B * M := by ring

/-- Turning an exponential bound in a level into a bound in the exponent. -/
private lemma rpow_self_le_iff {cc x p : ℝ} (hcc : 0 < cc) (hx : 0 ≤ x) (hp : 0 ≤ p) :
    x ^ cc ≤ p ↔ x ≤ p ^ (1 / cc) := by
  have h1 : (p ^ (1 / cc)) ^ cc = p := by
    rw [← Real.rpow_mul hp, one_div_mul_cancel hcc.ne', Real.rpow_one]
  have h2 := Real.rpow_le_rpow_iff hx (show (0 : ℝ) ≤ p ^ (1 / cc) by positivity) hcc
  rw [h1] at h2
  exact h2

/-- The self scaled rough sum over an integer interval splits into one sum per possible least
prime factor, and each piece is a rough character sum at the fixed level of that prime. -/
private lemma self_rough_sum_eq {cc : ℝ} (hcc : 0 < cc) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {a b : ℕ} (ha : 1 ≤ a) :
    ∑ m ∈ Finset.Ioc a b, ((upperRough m ((m : ℝ) ^ cc) : ℝ) : ℂ) * χ (m : ZMod q) =
      ∑ p ∈ (Finset.Icc 2 b).filter Nat.Prime,
        χ (p : ZMod q) *
          ∑ n ∈ Finset.Ioc (a / p) (min (b / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p)),
            ((Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q) := by
  have hmem2 : ∀ m ∈ Finset.Ioc a b, 2 ≤ m := by
    intro m hm
    have h1 : a < m := (Finset.mem_Ioc.mp hm).1
    omega
  have hone : ∀ m, upperRough m ((m : ℝ) ^ cc) = 0 ∨ upperRough m ((m : ℝ) ^ cc) = 1 := by
    intro m
    unfold upperRough
    split_ifs <;> simp
  have hone2 : ∀ n p, Task308.roughIndicator n p = 0 ∨ Task308.roughIndicator n p = 1 := by
    intro n p
    unfold Task308.roughIndicator
    split_ifs <;> simp
  -- Step 1: the indicator turns the unfiltered sum into the sum over the rough set.
  have hstep1 : ∑ m ∈ Finset.Ioc a b, ((upperRough m ((m : ℝ) ^ cc) : ℝ) : ℂ) * χ (m : ZMod q) =
      ∑ m ∈ (Finset.Ioc a b).filter (fun m => upperRough m ((m : ℝ) ^ cc) = 1),
        χ (m : ZMod q) := by
    calc ∑ m ∈ Finset.Ioc a b, ((upperRough m ((m : ℝ) ^ cc) : ℝ) : ℂ) * χ (m : ZMod q)
        = ∑ m ∈ Finset.Ioc a b,
            (if upperRough m ((m : ℝ) ^ cc) = 1 then χ (m : ZMod q) else 0) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rcases hone m with h | h <;> rw [h] <;> simp
      _ = ∑ m ∈ (Finset.Ioc a b).filter (fun m => upperRough m ((m : ℝ) ^ cc) = 1),
            χ (m : ZMod q) := (Finset.sum_filter _ _).symm
  -- Step 2: split into the fibers of the least prime factor.
  have hstep2 : ∑ m ∈ (Finset.Ioc a b).filter (fun m => upperRough m ((m : ℝ) ^ cc) = 1),
        χ (m : ZMod q) =
      ∑ p ∈ (Finset.Icc 2 b).filter Nat.Prime,
        ∑ m ∈ ((Finset.Ioc a b).filter (fun m => upperRough m ((m : ℝ) ^ cc) = 1)).filter
            (fun m => m.minFac = p),
          χ (m : ZMod q) := by
    have hmemP : ∀ m ∈ (Finset.Ioc a b).filter (fun m => upperRough m ((m : ℝ) ^ cc) = 1),
        m.minFac ∈ (Finset.Icc 2 b).filter Nat.Prime := by
      intro m hm
      have hmI := (Finset.mem_filter.mp hm).1
      have hm2 : 2 ≤ m := hmem2 m hmI
      have hP := Nat.minFac_prime (by omega : m ≠ 1)
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hP.two_le, ?_⟩, hP⟩
      exact le_trans (Nat.minFac_le (by omega)) (Finset.mem_Ioc.mp hmI).2
    have hfib : ∀ m ∈ (Finset.Ioc a b).filter (fun m => upperRough m ((m : ℝ) ^ cc) = 1),
        (∑ p ∈ (Finset.Icc 2 b).filter Nat.Prime,
          if m.minFac = p then χ (m : ZMod q) else 0) = χ (m : ZMod q) := by
      intro m hm
      rw [Finset.sum_ite_eq, if_pos (hmemP m hm)]
    calc ∑ m ∈ (Finset.Ioc a b).filter (fun m => upperRough m ((m : ℝ) ^ cc) = 1),
          χ (m : ZMod q)
        = ∑ m ∈ (Finset.Ioc a b).filter (fun m => upperRough m ((m : ℝ) ^ cc) = 1),
            ∑ p ∈ (Finset.Icc 2 b).filter Nat.Prime,
              if m.minFac = p then χ (m : ZMod q) else 0 := by
          exact (Finset.sum_congr rfl fun m hm => (hfib m hm).symm)
      _ = ∑ p ∈ (Finset.Icc 2 b).filter Nat.Prime,
            ∑ m ∈ (Finset.Ioc a b).filter (fun m => upperRough m ((m : ℝ) ^ cc) = 1),
              if m.minFac = p then χ (m : ZMod q) else 0 := Finset.sum_comm
      _ = ∑ p ∈ (Finset.Icc 2 b).filter Nat.Prime,
            ∑ m ∈ ((Finset.Ioc a b).filter (fun m => upperRough m ((m : ℝ) ^ cc) = 1)).filter
                (fun m => m.minFac = p),
              χ (m : ZMod q) := by
          refine Finset.sum_congr rfl fun p _ => (Finset.sum_filter _ _).symm
  rw [hstep1, hstep2]
  -- Step 3: for each prime, replace the fiber of `minFac` by the rough sum in the cofactor.
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpP : p.Prime := (Finset.mem_filter.mp hp).2
  have hp2 : 2 ≤ p := hpP.two_le
  have hpb : p ≤ b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
  set S : Finset ℕ := ((Finset.Ioc a b).filter (fun m => upperRough m ((m : ℝ) ^ cc) = 1)).filter
      (fun m => m.minFac = p) with hS
  set T : Finset ℕ := (Finset.Ioc (a / p) (min (b / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p))).filter
      (fun n => Task308.roughIndicator n p = 1) with hT
  have hSdat : ∀ m ∈ S, a < m ∧ m ≤ b ∧ m.minFac = p ∧ upperRough m ((m : ℝ) ^ cc) = 1 := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmI, hm3⟩ := Finset.mem_filter.mp hm1
    exact ⟨(Finset.mem_Ioc.mp hmI).1, (Finset.mem_Ioc.mp hmI).2, hm2, hm3⟩
  have hdivm : ∀ m ∈ S, p * (m / p) = m := by
    intro m hm
    obtain ⟨-, -, hmf, -⟩ := hSdat m hm
    rw [← hmf]
    exact Nat.mul_div_cancel' (Nat.minFac_dvd m)
  -- the cofactor is rough at the level of the prime
  have hrough : ∀ m ∈ S, Task308.roughIndicator (m / p) p = 1 := by
    intro m hm
    obtain ⟨-, -, hmf, -⟩ := hSdat m hm
    rw [Task308.rough_indicator_support]
    intro q hq hqp hqd
    have hqm : q ∣ m := by
      rw [← hdivm m hm]
      exact Dvd.dvd.mul_left hqd p
    have hmin : m.minFac ≤ q := Nat.minFac_le_of_dvd hq.two_le hqm
    omega
  -- membership of the cofactor in `T`
  have hi : ∀ m ∈ S, m / p ∈ T := by
    intro m hm
    obtain ⟨hma, hmb, hmf, hmr⟩ := hSdat m hm
    have hm2 : 2 ≤ m := hmem2 m (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
    have hplevel : ((m : ℝ) ^ cc) ≤ (p : ℝ) := by
      have h1 : ((m : ℝ) ^ cc) ≤ (m.minFac : ℝ) := by
        have h2 := upperRough_eq_minFac hm2 ((m : ℝ) ^ cc)
        rw [h2] at hmr
        by_contra hcon
        push_neg at hcon
        rw [if_neg (by linarith)] at hmr
        exact absurd hmr (by norm_num)
      rwa [hmf] at h1
    have hmle : (m : ℝ) ≤ (p : ℝ) ^ (1 / cc) :=
      (rpow_self_le_iff hcc (by positivity) hpR).1 hplevel
    have hmfloor : m ≤ ⌊((p : ℝ) ^ (1 / cc))⌋₊ := Nat.le_floor hmle
    have hlower : a / p < m / p := by
      rw [Nat.div_lt_iff_lt_mul hp0]
      calc a < m := hma
        _ = (m / p) * p := by rw [Nat.mul_comm, hdivm m hm]
    have hupper : m / p ≤ min (b / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p) := by
      refine le_min (Nat.div_le_div_right hmb) ?_
      rw [Nat.le_div_iff_mul_le hp0]
      calc (m / p) * p = m := by rw [Nat.mul_comm, hdivm m hm]
        _ ≤ ⌊((p : ℝ) ^ (1 / cc))⌋₊ := hmfloor
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlower, hupper⟩, hrough m hm⟩
  -- the product of the prime and a member of `T` lies in `S`
  have hj : ∀ n ∈ T, p * n ∈ S := by
    intro n hn
    obtain ⟨hnI, hnrough⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hnI
    have hnble : n ≤ b / p := le_trans hn2 (min_le_left _ _)
    have hnfloor : n ≤ ⌊((p : ℝ) ^ (1 / cc))⌋₊ / p := le_trans hn2 (min_le_right _ _)
    have hnpos : 1 ≤ n := by
      have h0 : 0 ≤ a / p := Nat.zero_le _
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hp0] at hn1
      calc a < n * p := hn1
        _ = p * n := by ring
    · rw [Nat.le_div_iff_mul_le hp0] at hnble
      calc p * n = n * p := by ring
        _ ≤ b := hnble
    · have hfloor : p * n ≤ ⌊((p : ℝ) ^ (1 / cc))⌋₊ := by
        rw [Nat.le_div_iff_mul_le hp0] at hnfloor
        rw [Nat.mul_comm]
        exact hnfloor
      have hreal : ((n * p : ℕ) : ℝ) ≤ (p : ℝ) ^ (1 / cc) := by
        rw [Nat.mul_comm]
        exact le_trans (by exact_mod_cast hfloor) (Nat.floor_le (by positivity))
      have hrc : (((p * n : ℕ)) : ℝ) ^ cc ≤ (p : ℝ) := by
        have hpn : (((p * n : ℕ)) : ℝ) = ((n * p : ℕ) : ℝ) := by rw [Nat.mul_comm]
        rw [hpn]
        exact (rpow_self_le_iff hcc (by positivity) hpR).2 hreal
      have hmf : (p * n).minFac = p := minFac_mul_of_rough hpP hnpos hnrough
      have h2n : 2 ≤ p * n := by
        have := Nat.mul_le_mul hp2 hnpos
        simpa using this
      rw [upperRough_eq_minFac h2n, hmf, if_pos hrc]
    · exact minFac_mul_of_rough hpP hnpos hnrough
  -- assemble the bijection
  have hleft : ∀ m ∈ S, p * (m / p) = m := hdivm
  have hright : ∀ n ∈ T, p * n / p = n := by
    intro n _
    exact Nat.mul_div_cancel_left n hp0
  have hsummand : ∀ m ∈ S, χ (m : ZMod q) = χ (p : ZMod q) * χ ((m / p) : ZMod q) := by
    intro m hm
    conv_lhs => rw [← hdivm m hm]
    push_cast
    rw [map_mul]
  calc ∑ m ∈ S, χ (m : ZMod q)
      = ∑ n ∈ T, χ (p : ZMod q) * χ (n : ZMod q) :=
        Finset.sum_bij' (fun m _ => m / p) (fun n _ => p * n) hi hj hleft hright
          (fun m hm => hsummand m hm)
    _ = χ (p : ZMod q) * ∑ n ∈ T, χ (n : ZMod q) := by rw [Finset.mul_sum]
    _ = χ (p : ZMod q) * ∑ n ∈ Finset.Ioc (a / p) (min (b / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p)),
            ((Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q) := by
        rw [hT, Finset.sum_filter]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rcases hone2 n p with h | h <;> rw [h] <;> push_cast <;> simp

/-- Splitting a sum over an integer interval at the point where its lower index passes one. -/
private lemma sum_Ioc_split_low {f : ℕ → ℂ} {low B : ℕ} (hB : 1 ≤ B) :
    ∑ n ∈ Finset.Ioc low B, f n =
      ∑ n ∈ Finset.Ioc (max 1 low) B, f n + (if low = 0 then f 1 else 0) := by
  by_cases hlow : low = 0
  · subst hlow
    have hset : Finset.Ioc 0 B = insert 1 (Finset.Ioc 1 B) := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp), if_pos rfl,
      max_eq_left (by norm_num : (0 : ℕ) ≤ 1), add_comm]
  · have h1 : 1 ≤ low := by omega
    rw [if_neg hlow, add_zero, max_eq_right h1]

/-- The truncation of the right interval at `t` is again an integer interval. -/
private lemma filter_rightInterval {t : ℝ} {A B : ℕ} (hA : 1 ≤ A) :
    (Finset.Ioc A B).filter (fun m : ℕ => (m : ℝ) ≤ t) = Finset.Ioc A (min B ⌊t⌋₊) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, le_min h2 (Nat.le_floor h3)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, le_trans h2 (min_le_left _ _)⟩, ?_⟩
    have h3 : m ≤ ⌊t⌋₊ := le_trans h2 (min_le_right _ _)
    exact (Nat.le_floor_iff' (by omega)).mp h3

/-! ### The `g` term: the self scaled rough sum at a fixed scale -/

/-- The frozen level constant `c1` of page 53 is positive under the standing smallness of `ε`. -/
private lemma upperC1_pos {ε : ℝ} (hε8 : ε ≤ 1 / 10 ^ 8) : 0 < upperC1 ε := by
  unfold upperC1; nlinarith

/-- The frozen level constant `c1` is at most one, so the self scaled level `m ^ c1` never
exceeds `m` itself. -/
private lemma upperC1_le_one {ε : ℝ} (hε : 0 < ε) : upperC1 ε ≤ 1 := by
  unfold upperC1; nlinarith

/-- The reciprocal sum over the primes below `k` is at most one logarithm. -/
private lemma prime_inv_sum_le (k : ℕ) :
    ∑ p ∈ (Finset.Icc 2 k).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤ 1 + Real.log k := by
  have hsub : (Finset.Icc 2 k).filter Nat.Prime ⊆ Finset.Icc 1 k := by
    intro p hp
    obtain ⟨hp1, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp2, hpk⟩ := Finset.mem_Icc.mp hp1
    exact Finset.mem_Icc.mpr ⟨by omega, hpk⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) ?_
  have h := harmonic_le_one_add_log k
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-- The scale `2 Y` to the exponent `c / 2` is at most `Y ^ c` for `Y ≥ 2`. -/
private lemma level_ge {cc Y : ℝ} (hcc : 0 < cc) (hY : 2 ≤ Y) :
    (2 * Y) ^ (cc / 2) ≤ Y ^ cc := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have h1 : (2 : ℝ) ^ (cc / 2) ≤ Y ^ (cc / 2) :=
    Real.rpow_le_rpow (by norm_num) hY (by linarith)
  have h2 : Y ^ (cc / 2) * Y ^ (cc / 2) = Y ^ cc := by
    rw [← Real.rpow_add hY0]; congr 1; ring
  calc (2 * Y) ^ (cc / 2) = (2 : ℝ) ^ (cc / 2) * Y ^ (cc / 2) :=
        Real.mul_rpow (by norm_num) hY0.le
    _ ≤ Y ^ (cc / 2) * Y ^ (cc / 2) := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = Y ^ cc := h2

/-- The self scaled rough sum over `(L, k]` is the sum of the primes in `(L, k]` and a sum of
fixed level rough character sums in the cofactors `m / minFac m`, one per least prime factor. -/
private lemma self_rough_sum_split {cc : ℝ} (hcc : 0 < cc) (hcc1 : cc ≤ 1)
    {q : ℕ} (χ : DirichletCharacter ℂ q) {Y : ℝ} {L k : ℕ}
    (hLY : (L : ℝ) ≤ Y) (hLf : ⌊Y⌋₊ ≤ L) (hkY : (k : ℝ) ≤ 2 * Y) (hL : 1 ≤ L) :
    ∑ m ∈ Finset.Ioc L k, ((upperRough m ((m : ℝ) ^ cc) : ℝ) : ℂ) * χ (m : ZMod q) =
      (∑ p ∈ ((Finset.Icc 2 k).filter Nat.Prime).filter (fun p => p ≤ L),
          χ (p : ZMod q) *
            ∑ n ∈ Finset.Ioc (L / p) (min (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p)),
              ((Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)) +
      ∑ m ∈ Finset.Ioc L k, ((primeWeight m : ℝ) : ℂ) * χ (m : ZMod q) := by
  rw [self_rough_sum_eq hcc χ hL]
  rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.Icc 2 k).filter Nat.Prime)
    (p := fun p => p ≤ L)]
  congr 1
  · -- the least prime factors above `L`: the cofactor is `1`, so these are the primes in `(L, k]`
    have hinner : ∀ p ∈ ((Finset.Icc 2 k).filter Nat.Prime).filter (fun p => ¬ p ≤ L),
        (∑ n ∈ Finset.Ioc (L / p) (min (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p)),
              ((Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)) = 1 := by
      intro p hp
      obtain ⟨hp1, hpL⟩ := Finset.mem_filter.mp hp
      have hpP : p.Prime := (Finset.mem_filter.mp hp1).2
      have hpk : p ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).2
      have hp2 : 2 ≤ p := hpP.two_le
      have hp0 : 0 < p := by omega
      have hLp : L < p := lt_of_not_ge hpL
      have hpY : Y < (p : ℝ) := by
        have h1 : Y < (⌊Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Y
        have h2 : ⌊Y⌋₊ + 1 ≤ p := Nat.succ_le_of_lt (lt_of_le_of_lt hLf hLp)
        calc Y < (⌊Y⌋₊ : ℝ) + 1 := h1
          _ = ((⌊Y⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (p : ℝ) := by exact_mod_cast h2
      have hLdiv : L / p = 0 := Nat.div_eq_of_lt hLp
      have hkdiv : k / p = 1 := by
        have h1 : 0 < k / p := Nat.div_pos hpk hp0
        have h2 : k / p < 2 := by
          rw [Nat.div_lt_iff_lt_mul hp0]
          have : (k : ℝ) < 2 * (p : ℝ) := by nlinarith
          exact_mod_cast this
        omega
      have hFge : 1 ≤ ⌊((p : ℝ) ^ (1 / cc))⌋₊ / p := by
        have hple : (p : ℝ) ≤ (p : ℝ) ^ (1 / cc) := by
          have h1 : (p : ℝ) ^ (1 : ℝ) ≤ (p : ℝ) ^ (1 / cc) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp0) (by
              rw [one_le_div₀ hcc]; exact hcc1)
          rwa [Real.rpow_one] at h1
        have hple' : p ≤ ⌊((p : ℝ) ^ (1 / cc))⌋₊ := Nat.le_floor hple
        exact Nat.one_le_div_iff hp0 |>.mpr hple'
      have hmin : min (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p) = 1 := by
        rw [hkdiv]
        exact min_eq_left hFge
      rw [hLdiv, hmin]
      have hset : Finset.Ioc 0 1 = ({1} : Finset ℕ) := by
        ext n
        simp only [Finset.mem_Ioc, Finset.mem_singleton]
        omega
      rw [hset, Finset.sum_singleton]
      have hr : Task308.roughIndicator 1 p = 1 := by
        unfold Task308.roughIndicator; rw [if_pos (Or.inl rfl)]
      rw [hr]
      push_cast
      simp
    calc ∑ p ∈ ((Finset.Icc 2 k).filter Nat.Prime).filter (fun p => ¬ p ≤ L),
          χ (p : ZMod q) *
            ∑ n ∈ Finset.Ioc (L / p) (min (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p)),
              ((Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)
        = ∑ p ∈ ((Finset.Icc 2 k).filter Nat.Prime).filter (fun p => ¬ p ≤ L),
            χ (p : ZMod q) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [hinner p hp, mul_one]
      _ = ∑ m ∈ Finset.Ioc L k, ((primeWeight m : ℝ) : ℂ) * χ (m : ZMod q) := by
          have hset : ((Finset.Icc 2 k).filter Nat.Prime).filter (fun p => ¬ p ≤ L) =
              (Finset.Ioc L k).filter Nat.Prime := by
            ext p
            simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
            constructor
            · rintro ⟨⟨⟨hp2, hpk⟩, hpp⟩, hpL⟩
              exact ⟨⟨lt_of_not_ge hpL, hpk⟩, hpp⟩
            · rintro ⟨⟨hLp, hpk⟩, hpp⟩
              exact ⟨⟨⟨by omega, hpk⟩, hpp⟩, by omega⟩
          rw [hset, Finset.sum_filter]
          refine Finset.sum_congr rfl fun m _ => ?_
          unfold primeWeight
          by_cases h : m.Prime
          · rw [if_pos h, if_pos h]; push_cast; ring
          · rw [if_neg h, if_neg h]; simp


/-- The non-prime part of the self scaled rough sum at the scale `X = 2 Y`: each fibre of the
least prime factor is a fixed level rough character sum bounded by
`Rough514.rough_character_interval`, and the reciprocal sum over the fibres costs one logarithm. -/
private lemma self_rough_rest_bound {cc : ℝ} (hcc : 0 < cc) (hcc1 : cc ≤ 1)
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ A →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ Y : ℝ, X = 2 * Y → 2 ≤ Y → ∀ L k : ℕ,
        (L : ℝ) ≤ Y → ⌊Y⌋₊ ≤ L → (k : ℝ) ≤ 2 * Y →
          ‖∑ p ∈ ((Finset.Icc 2 k).filter Nat.Prime).filter (fun p => p ≤ L),
              χ (p : ZMod q) *
                ∑ n ∈ Finset.Ioc (L / p) (min (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p)),
                  ((Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
            C * (k : ℝ) * Real.log X ^ (-A) * (1 + Real.log k) := by
  obtain ⟨C0, hC0pos, hmain⟩ :=
    Rough514.rough_character_interval (c := cc / 2) (A := A) (by linarith) hA
  refine ⟨C0, hC0pos, ?_⟩
  intro X hX q hq hqX χ hχ Y hXY hY2 L k hLY hLf hkY
  have hY0 : (0 : ℝ) < Y := by linarith
  have hX4 : (4 : ℝ) ≤ X := by rw [hXY]; linarith
  have hlogX0 : 0 < Real.log X := Real.log_pos (by linarith)
  have hscale : 0 ≤ Real.log X ^ (-A) := Real.rpow_nonneg hlogX0.le _
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hterm : ∀ p ∈ ((Finset.Icc 2 k).filter Nat.Prime).filter (fun p => p ≤ L),
      ‖χ (p : ZMod q) *
          ∑ n ∈ Finset.Ioc (L / p) (min (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p)),
            ((Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
        C0 * ((k : ℝ) / (p : ℝ)) * Real.log X ^ (-A) := by
    intro p hp
    obtain ⟨hp1, hpL⟩ := Finset.mem_filter.mp hp
    have hpP : p.Prime := (Finset.mem_filter.mp hp1).2
    have hpk : p ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).2
    have hp2 : 2 ≤ p := hpP.two_le
    have hp0 : 0 < p := by omega
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
    have hLp : 1 ≤ L / p := Nat.one_le_div_iff hp0 |>.mpr hpL
    have hbX : ((min (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p) : ℕ) : ℝ) ≤ X := by
      have h1 : ((min (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p) : ℕ) : ℝ) ≤ ((k / p : ℕ) : ℝ) := by
        exact_mod_cast min_le_left (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p)
      have h2 : ((k / p : ℕ) : ℝ) ≤ (k : ℝ) / (p : ℝ) := Nat.cast_div_le
      have hp1' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp0
      have h3 : (k : ℝ) / (p : ℝ) ≤ 2 * Y := by
        rw [div_le_iff₀ hpR]
        nlinarith [hkY, hp1', hY2]
      have h4 : (2 : ℝ) * Y = X := hXY.symm
      linarith
    by_cases hz : p ≤ ⌊Y ^ cc⌋₊
    · have hF : ⌊((p : ℝ) ^ (1 / cc))⌋₊ ≤ L := by
        have hp1' : (p : ℝ) ≤ Y ^ cc :=
          le_trans (by exact_mod_cast hz) (Nat.floor_le (by positivity))
        have h2 : (p : ℝ) ^ (1 / cc) ≤ Y := by
          have hmono : (p : ℝ) ^ (1 / cc) ≤ (Y ^ cc) ^ (1 / cc) :=
            Real.rpow_le_rpow (by positivity) hp1' (by positivity)
          have hYcc : (Y ^ cc) ^ (1 / cc) = Y := by
            rw [← Real.rpow_mul hY0.le, show cc * (1 / cc) = 1 by
              rw [mul_one_div, div_self hcc.ne'], Real.rpow_one]
          rwa [hYcc] at hmono
        exact le_trans (Nat.floor_le_floor h2) hLf
      have hempty : min (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p) ≤ L / p :=
        le_trans (min_le_right _ _) (Nat.div_le_div_right hF)
      rw [Finset.Ioc_eq_empty_of_le hempty, Finset.sum_empty, mul_zero, norm_zero]
      positivity
    · have hlev : (2 * Y) ^ (cc / 2) ≤ (p : ℝ) := by
        have h1 : Y ^ cc < (⌊Y ^ cc⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        have h2 : ⌊Y ^ cc⌋₊ + 1 ≤ p := Nat.succ_le_of_lt (lt_of_not_ge hz)
        have h3 : Y ^ cc ≤ (p : ℝ) := by
          calc Y ^ cc ≤ (⌊Y ^ cc⌋₊ : ℝ) + 1 := le_of_lt h1
            _ = ((⌊Y ^ cc⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
            _ ≤ (p : ℝ) := by exact_mod_cast h2
        exact le_trans (level_ge hcc hY2) h3
      have hlev' : X ^ (cc / 2) ≤ (p : ℝ) := by rw [hXY]; exact hlev
      have hmain' := hmain X hX q hq hqX χ hχ p hlev' (L / p)
        (min (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p)) hLp hbX
      have hbnd : ((min (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p) : ℕ) : ℝ) ≤ (k : ℝ) / (p : ℝ) :=
        le_trans (by exact_mod_cast min_le_left (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p))
          Nat.cast_div_le
      rw [norm_mul]
      calc ‖χ (p : ZMod q)‖ *
            ‖∑ n ∈ Finset.Ioc (L / p) (min (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p)),
              ((Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)‖
          ≤ 1 * (C0 * ((min (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p) : ℕ) : ℝ) *
              Real.log X ^ (-A)) :=
            mul_le_mul (DirichletCharacter.norm_le_one χ _) hmain' (norm_nonneg _) zero_le_one
        _ = C0 * ((min (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p) : ℕ) : ℝ) *
              Real.log X ^ (-A) := by ring
        _ ≤ C0 * ((k : ℝ) / (p : ℝ)) * Real.log X ^ (-A) := by
            refine mul_le_mul_of_nonneg_right ?_ hscale
            exact mul_le_mul_of_nonneg_left hbnd hC0pos.le
  have hSsub : ∑ p ∈ ((Finset.Icc 2 k).filter Nat.Prime).filter (fun p => p ≤ L),
        (1 : ℝ) / (p : ℝ) ≤ 1 + Real.log k :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)) (prime_inv_sum_le k)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p ∈ ((Finset.Icc 2 k).filter Nat.Prime).filter (fun p => p ≤ L),
        ‖χ (p : ZMod q) *
          ∑ n ∈ Finset.Ioc (L / p) (min (k / p) (⌊((p : ℝ) ^ (1 / cc))⌋₊ / p)),
            ((Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)‖
      ≤ ∑ p ∈ ((Finset.Icc 2 k).filter Nat.Prime).filter (fun p => p ≤ L),
          C0 * ((k : ℝ) / (p : ℝ)) * Real.log X ^ (-A) := Finset.sum_le_sum hterm
    _ = (C0 * Real.log X ^ (-A) * (k : ℝ)) *
          ∑ p ∈ ((Finset.Icc 2 k).filter Nat.Prime).filter (fun p => p ≤ L), (1 : ℝ) / (p : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ (C0 * Real.log X ^ (-A) * (k : ℝ)) * (1 + Real.log k) := by
        refine mul_le_mul_of_nonneg_left hSsub ?_
        exact mul_nonneg (mul_nonneg hC0pos.le hscale) hk0
    _ = C0 * (k : ℝ) * Real.log X ^ (-A) * (1 + Real.log k) := by ring


/-- A saving of the logarithm of the scale `2 Y` in a logarithm power costs a factor of the
scale ratio; `11/20 · log x ≤ log (2 Y)` is the only thing used. -/
private lemma log_scale_transfer {A l lX : ℝ} (hA : 0 < A) (hl : 1 ≤ l)
    (h : (11 / 20) * l ≤ lX) :
    lX ^ (-(A + 3)) ≤ (((11 / 20 : ℝ) ^ (A + 3))⁻¹) * l ^ (-A) := by
  have hl0 : (0 : ℝ) < (11 / 20) * l := by nlinarith
  have hlX0 : 0 < lX := by nlinarith
  have h1 : lX ^ (-(A + 3)) ≤ ((11 / 20) * l) ^ (-(A + 3)) :=
    Real.rpow_le_rpow_of_nonpos hl0 h (by linarith)
  have h2 : ((11 / 20) * l) ^ (-(A + 3)) =
      (((11 / 20 : ℝ) ^ (A + 3))⁻¹) * l ^ (-(A + 3)) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 11 / 20) (by linarith : (0 : ℝ) ≤ l),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 11 / 20)]
  have h3 : l ^ (-(A + 3)) ≤ l ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hl (by linarith)
  calc lX ^ (-(A + 3)) ≤ ((11 / 20) * l) ^ (-(A + 3)) := h1
    _ = (((11 / 20 : ℝ) ^ (A + 3))⁻¹) * l ^ (-(A + 3)) := h2
    _ ≤ (((11 / 20 : ℝ) ^ (A + 3))⁻¹) * l ^ (-A) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

/-! ### The four terms of the identity, one at a time -/

set_option maxHeartbeats 4000000 in
/-- LEAF: the `g` term of the identity. The first term of the page 53 raw weight, the sifted
indicator at the level `m ^ c4`, taken with the recentring factor `log m / log Y`, against a
non-principal character over the truncated right interval, is bounded by
`C x^(11/20+eps) (log x)^(-A)` with a constant depending only on `A`. This is one summand of the
target's sum, so it is strictly easier than the target; it is the term the prime numbers fall into,
and it is the place where the sifted count has to be distributed over the residue classes.
Non-vacuity: at `t = 0` the index set is empty and the sum is zero. -/
theorem leaf_g_term_nonprincipal
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              upperG ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  have hcc : 0 < upperC1 ε := upperC1_pos hε8
  have hcc1 : upperC1 ε ≤ 1 := upperC1_le_one hε
  obtain ⟨C1, hC1pos, hrest⟩ :=
    self_rough_rest_bound (cc := upperC1 ε) hcc hcc1 (A := A + 4) (by linarith)
  obtain ⟨C2, hC2⟩ := Prime514.nonprincipal_prime_short hε hε8 A hA
  set beta : ℝ := (20 / 11 : ℝ) ^ ((A + 4) / 4) with hbetadef
  have hbeta1 : 1 ≤ beta := Real.one_le_rpow (by norm_num) (by linarith)
  have hbeta_ge : (20 / 11 : ℝ) ≤ beta := by
    have h1 : (1 : ℝ) ≤ (A + 4) / 4 := by linarith
    have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 20 / 11) h1
    rwa [Real.rpow_one] at h2
  have hbeta0 : 0 < beta := lt_of_lt_of_le (by norm_num) hbeta_ge
  let P : ℝ := max C1 C2
  let Q : ℝ := max (Real.exp beta) 4
  let R2 : ℝ := max P Q
  let G2 : ℝ := max R2 (C1 ^ 2)
  let S : ℝ := 16 * C1 * (((11 / 20 : ℝ) ^ (A + 3))⁻¹) + 4 * C2
  let T : ℝ := max G2 S
  let Cc : ℝ := max T 1
  refine ⟨Cc, fun x hx q hq hqA χ hχ t ht => ?_⟩
  have hC1x : C1 ≤ x := by
    have a : C1 ≤ P := le_max_left _ _
    have b : P ≤ R2 := le_max_left _ _
    have c : R2 ≤ G2 := le_max_left _ _
    have d : G2 ≤ T := le_max_left _ _
    have e : T ≤ Cc := le_max_left _ _
    exact le_trans (le_trans (le_trans (le_trans (le_trans a b) c) d) e) hx
  have hC2x : C2 ≤ x := by
    have a : C2 ≤ P := le_max_right _ _
    have b : P ≤ R2 := le_max_left _ _
    have c : R2 ≤ G2 := le_max_left _ _
    have d : G2 ≤ T := le_max_left _ _
    have e : T ≤ Cc := le_max_left _ _
    exact le_trans (le_trans (le_trans (le_trans (le_trans a b) c) d) e) hx
  have hexpx : Real.exp beta ≤ x := by
    have a : Real.exp beta ≤ Q := le_max_left _ _
    have b : Q ≤ R2 := le_max_right _ _
    have c : R2 ≤ G2 := le_max_left _ _
    have d : G2 ≤ T := le_max_left _ _
    have e : T ≤ Cc := le_max_left _ _
    exact le_trans (le_trans (le_trans (le_trans (le_trans a b) c) d) e) hx
  have h4x : (4 : ℝ) ≤ x := by
    have a : (4 : ℝ) ≤ Q := le_max_right _ _
    have b : Q ≤ R2 := le_max_right _ _
    have c : R2 ≤ G2 := le_max_left _ _
    have d : G2 ≤ T := le_max_left _ _
    have e : T ≤ Cc := le_max_left _ _
    exact le_trans (le_trans (le_trans (le_trans (le_trans a b) c) d) e) hx
  have hCsq : C1 ^ 2 ≤ x := by
    have c : C1 ^ 2 ≤ G2 := le_max_right _ _
    have d : G2 ≤ T := le_max_left _ _
    have e : T ≤ Cc := le_max_left _ _
    exact le_trans (le_trans (le_trans c d) e) hx
  have hSx : S ≤ x := by
    have d : S ≤ T := le_max_right _ _
    have e : T ≤ Cc := le_max_left _ _
    exact le_trans (le_trans d e) hx
  have h1x : (1 : ℝ) ≤ x := by
    have e : (1 : ℝ) ≤ Cc := le_max_right _ _
    exact le_trans e hx
  have hCc1 : (1 : ℝ) ≤ Cc := le_max_right _ _
  have hCc0 : (0 : ℝ) ≤ Cc := le_trans zero_le_one hCc1
  have hx0 : (0 : ℝ) < x := by linarith
  have hbeta_lx : beta ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hexpx
  have hlx1 : 1 ≤ Real.log x := le_trans hbeta1 hbeta_lx
  have hlx0 : 0 < Real.log x := by linarith
  have hlx_ge : (20 / 11 : ℝ) ≤ Real.log x := le_trans hbeta_ge hbeta_lx
  set Y : ℝ := x ^ (11 / 20 + ε) with hYdef
  have hY0 : 0 < Y := by rw [hYdef]; exact Real.rpow_pos_of_pos hx0 _
  have hY2 : 2 ≤ Y := by rw [hYdef]; exact upper_Y_ge_two hε h4x
  have hlogY : Real.log Y = (11 / 20 + ε) * Real.log x := by
    rw [hYdef]; exact Real.log_rpow hx0 _
  have hlogY0 : 0 < Real.log Y := by rw [hlogY]; nlinarith
  set X : ℝ := 2 * Y with hXdef
  have hX0 : 0 < X := by rw [hXdef]; linarith
  have hYX : Y ≤ X := by rw [hXdef]; linarith
  have hlogXge : (11 / 20) * Real.log x ≤ Real.log X := by
    rw [hXdef, Real.log_mul (by norm_num) hY0.ne', hlogY]
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have hlogX0 : 0 < Real.log X := by linarith
  have hlogX1 : 1 ≤ Real.log X := by nlinarith
  have hR0 : (0 : ℝ) ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlx0.le _
  have hLX0 : (0 : ℝ) ≤ Real.log X ^ (-(A + 4)) := Real.rpow_nonneg hlogX0.le _
  -- the threshold also passes the scale `X`
  have hX1 : C1 ≤ X := by
    rcases le_or_gt (1 : ℝ) C1 with hC1ge | hC1lt
    · have hlogC1 : 0 ≤ Real.log C1 := Real.log_nonneg hC1ge
      have hlogx : 2 * Real.log C1 ≤ Real.log x := by
        have h := Real.log_le_log (by positivity : (0 : ℝ) < C1 ^ 2) hCsq
        rwa [Real.log_pow] at h
      have hlogYle : Real.log C1 ≤ Real.log Y := by rw [hlogY]; nlinarith
      exact le_trans (Real.log_le_log_iff hC1pos hY0 |>.mp hlogYle) hYX
    · exact le_trans hC1lt.le (by linarith)
  -- the modulus bound at the scale `X`
  have hqX : (q : ℝ) ≤ Real.log X ^ (A + 4) := by
    have hb1 : (0 : ℝ) < (11 / 20) * Real.log x := by positivity
    have hstep : Real.log x ^ A ≤ ((11 / 20) * Real.log x) ^ (A + 4) := by
      have hbase : (20 / 11 : ℝ) ^ (A / 4) ≤ (11 / 20) * Real.log x := by
        have e : (20 / 11 : ℝ) ^ (A / 4) = beta / (20 / 11) := by
          rw [hbetadef, show (A + 4) / 4 = A / 4 + 1 by ring, Real.rpow_add (by norm_num),
            Real.rpow_one]
          ring
        rw [e, div_le_iff₀ (by norm_num : (0 : ℝ) < 20 / 11)]
        nlinarith
      have h4 : (20 / 11 : ℝ) ^ A ≤ ((11 / 20) * Real.log x) ^ (4 : ℝ) := by
        have h := Real.rpow_le_rpow (by positivity) hbase (show (0 : ℝ) ≤ 4 by norm_num)
        rwa [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 20 / 11), show A / 4 * 4 = A by ring]
          at h
      calc Real.log x ^ A = ((11 / 20) * Real.log x) ^ A * (20 / 11 : ℝ) ^ A := by
            rw [← Real.mul_rpow hb1.le (by norm_num : (0 : ℝ) ≤ 20 / 11)]
            congr 1
            ring
        _ ≤ ((11 / 20) * Real.log x) ^ A * ((11 / 20) * Real.log x) ^ (4 : ℝ) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = ((11 / 20) * Real.log x) ^ (A + 4) := by
            rw [← Real.rpow_add hb1]
    calc (q : ℝ) ≤ Real.log x ^ A := hqA
      _ ≤ ((11 / 20) * Real.log x) ^ (A + 4) := hstep
      _ ≤ Real.log X ^ (A + 4) := Real.rpow_le_rpow (by positivity) hlogXge (by linarith)
  -- the integer scale
  have hL1 : 1 ≤ ⌊Y⌋₊ := Nat.floor_pos.mpr (by linarith : (1 : ℝ) ≤ Y)
  set L : ℕ := ⌊Y⌋₊ with hLdef
  set B : ℕ := ⌊2 * Y⌋₊ with hBdef
  set K : ℕ := min B ⌊t⌋₊ with hKdef
  have hYB : Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊ = Finset.Ioc L B := by
    rw [← hYdef, hLdef, hBdef]
  have hS : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) = Finset.Ioc L K := by
    have h := filter_rightInterval (t := t) (A := L) (B := B) hL1
    rw [rightInterval, hYB]
    simpa [hKdef] using h
  rcases Nat.lt_or_ge L K with hLK | hLK
  · have hLpos : 1 ≤ L := hL1
    have hK1 : 1 ≤ K := le_trans hL1 hLK.le
    have hLY : (L : ℝ) ≤ Y := by rw [hLdef]; exact Nat.floor_le (by linarith)
    have hKB : K ≤ B := by rw [hKdef]; exact min_le_left _ _
    have hKY : (K : ℝ) ≤ 2 * Y := by
      rw [hKdef]
      exact le_trans (by exact_mod_cast min_le_left B ⌊t⌋₊) (Nat.floor_le (by linarith))
    have hKx : (K : ℝ) ≤ X := by rw [hXdef]; linarith
    -- the prime term on a prefix
    have hprime : ∀ k : ℕ, L ≤ k → k ≤ K →
        ‖∑ m ∈ Finset.Ioc L k, ((primeWeight m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
          C2 * Y * Real.log x ^ (-A) := by
      intro k hLk hkK
      have hkB : k ≤ B := le_trans hkK hKB
      have hkt : (k : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
        rw [← hYdef]
        exact le_trans (by exact_mod_cast hkB) (Nat.floor_le (by linarith))
      have hkeq : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ (k : ℝ)) =
          Finset.Ioc L k := by
        have h := filter_rightInterval (t := (k : ℝ)) (A := L) (B := B) hL1
        rw [rightInterval, hYB]
        simpa [Nat.floor_natCast, min_eq_right hkB] using h
      have hmain2 := hC2 x hC2x q hq hqA χ hχ (k : ℝ) hkt
      rwa [hkeq] at hmain2
    -- the prefix bound for the self scaled rough sum
    have hprefix : ∀ k : ℕ, L ≤ k → k ≤ K →
        ‖∑ m ∈ Finset.Ioc L k, ((upperRough m ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) *
            χ (m : ZMod q)‖ ≤
          C1 * (K : ℝ) * Real.log X ^ (-(A + 4)) * (1 + Real.log K) +
            C2 * Y * Real.log x ^ (-A) := by
      intro k hLk hkK
      have hkY : (k : ℝ) ≤ 2 * Y := le_trans (by exact_mod_cast hkK) hKY
      have hk1 : 1 ≤ k := le_trans hLpos hLk
      have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      have hkK' : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hkK
      have hsplit := self_rough_sum_split (cc := upperC1 ε) hcc hcc1 (χ := χ) (Y := Y)
        (L := L) (k := k) hLY le_rfl hkY hLpos
      rw [hsplit]
      refine le_trans (norm_add_le _ _) (add_le_add ?_ (hprime k hLk hkK))
      refine le_trans (hrest X hX1 q hq hqX χ hχ Y hXdef hY2 L k hLY le_rfl hkY) ?_
      have hlk : Real.log (k : ℝ) ≤ Real.log (K : ℝ) :=
        Real.log_le_log hk0 hkK'
      have hlogk0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
      have h1 : C1 * (k : ℝ) ≤ C1 * (K : ℝ) :=
        mul_le_mul_of_nonneg_left hkK' hC1pos.le
      have h2 : C1 * (k : ℝ) * Real.log X ^ (-(A + 4)) ≤
          C1 * (K : ℝ) * Real.log X ^ (-(A + 4)) :=
        mul_le_mul_of_nonneg_right h1 hLX0
      have h3 : (1 + Real.log (k : ℝ)) ≤ (1 + Real.log (K : ℝ)) := by linarith
      have h4 : (0 : ℝ) ≤ 1 + Real.log (k : ℝ) := by linarith
      exact mul_le_mul h2 h3 h4 (by positivity)
    -- partial summation against the recentring factor
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have hlogK0 : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK1)
    have hM0 : 0 ≤ C1 * (K : ℝ) * Real.log X ^ (-(A + 4)) * (1 + Real.log K) +
        C2 * Y * Real.log x ^ (-A) := by
      have h1 : (0 : ℝ) ≤ C1 * (K : ℝ) * Real.log X ^ (-(A + 4)) * (1 + Real.log K) := by positivity
      have h2 : (0 : ℝ) ≤ C2 * Y * Real.log x ^ (-A) := by
        rcases le_or_gt 0 C2 with h | h
        · exact mul_nonneg (mul_nonneg h hY0.le) hR0
        · have h3 := hC2 x hC2x q hq hqA χ hχ (0 : ℝ) (by linarith)
          have h4 : (0 : ℝ) ≤ Y * Real.log x ^ (-A) := mul_nonneg hY0.le hR0
          nlinarith [norm_nonneg (∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => (m : ℝ) ≤ (0 : ℝ)),
            ((primeWeight m : ℝ) : ℂ) * χ (m : ZMod q))]
      linarith
    have hginc : ∀ m ∈ Finset.Ioc L (K - 1),
        Real.log (m : ℝ) / Real.log Y ≤ Real.log ((m + 1 : ℕ) : ℝ) / Real.log Y := by
      intro m hm
      obtain ⟨hm1, -⟩ := Finset.mem_Ioc.mp hm
      have hm0 : (0 : ℝ) < (m : ℝ) := by
        have : 1 ≤ m := by omega
        exact_mod_cast this
      have hmono : Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
        push_cast
        exact Real.log_le_log hm0 (by linarith)
      exact div_le_div_of_nonneg_right hmono hlogY0.le
    have habel := sum_mono_mul_le_of_prefix
      (f := fun m : ℕ => ((upperRough m ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) * χ (m : ZMod q))
      (g := fun m : ℕ => Real.log (m : ℝ) / Real.log Y) (A := L) (B := K) hLK.le
      (M := C1 * (K : ℝ) * Real.log X ^ (-(A + 4)) * (1 + Real.log K) +
        C2 * Y * Real.log x ^ (-A)) hM0 ?_ ?_ hginc hprefix
    · rw [hS]
      have hpt : ∀ m : ℕ, ((Real.log (m : ℝ) / Real.log Y * upperG ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q) =
          ((Real.log (m : ℝ) / Real.log Y : ℝ) : ℂ) *
            (((upperRough m ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) * χ (m : ZMod q)) := by
        intro m
        rw [show upperG ε (m : ℝ) m = upperRough m ((m : ℝ) ^ upperC1 ε) from rfl]
        push_cast
        ring
      rw [Finset.sum_congr rfl (fun m _ => hpt m)]
      set M : ℝ := C1 * (K : ℝ) * Real.log X ^ (-(A + 4)) * (1 + Real.log K) +
        C2 * Y * Real.log x ^ (-A) with hMdef
      -- the factor at the top
      have hwK : Real.log (K : ℝ) / Real.log Y ≤ 2 := by
        rw [div_le_iff₀ hlogY0]
        have h1 : Real.log (K : ℝ) ≤ Real.log (2 * Y) :=
          Real.log_le_log (by exact_mod_cast hK1) hKY
        have h2 : Real.log (2 * Y) = Real.log 2 + Real.log Y :=
          Real.log_mul (by norm_num) hY0.ne'
        have h3 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY2
        nlinarith
      have hM0' : (0 : ℝ) ≤ M := by rw [hMdef]; exact hM0
      have hs1 : 2 * (Real.log (K : ℝ) / Real.log Y) * M ≤ 4 * M := by nlinarith [hwK, hM0']
      have hlogKle : Real.log (K : ℝ) ≤ Real.log X :=
        Real.log_le_log (by exact_mod_cast hK1) hKx
      have h1log : 1 + Real.log (K : ℝ) ≤ 2 * Real.log X := by linarith
      have hs2a : C1 * (K : ℝ) * Real.log X ^ (-(A + 4)) * (1 + Real.log (K : ℝ)) ≤
          C1 * (2 * Y) * Real.log X ^ (-(A + 4)) * (2 * Real.log X) := by
        have hK2' : C1 * (K : ℝ) * Real.log X ^ (-(A + 4)) ≤
            C1 * (2 * Y) * Real.log X ^ (-(A + 4)) := by
          have h1 : C1 * (K : ℝ) ≤ C1 * (2 * Y) := mul_le_mul_of_nonneg_left hKY hC1pos.le
          exact mul_le_mul_of_nonneg_right h1 hLX0
        have h19 : (0 : ℝ) ≤ 1 + Real.log (K : ℝ) := by linarith
        exact mul_le_mul hK2' h1log h19 (by positivity)
      have hs2 : M ≤ C1 * (2 * Y) * Real.log X ^ (-(A + 4)) * (2 * Real.log X) +
          C2 * Y * Real.log x ^ (-A) := by rw [hMdef]; linarith
      have hs3 : C1 * (2 * Y) * Real.log X ^ (-(A + 4)) * (2 * Real.log X) =
          4 * C1 * Y * (Real.log X ^ (-(A + 4)) * Real.log X) := by ring
      have hs4 : Real.log X ^ (-(A + 4)) * Real.log X = Real.log X ^ (-(A + 3)) := by
        nth_rewrite 2 [show Real.log X = Real.log X ^ (1 : ℝ) from (Real.rpow_one _).symm]
        rw [← Real.rpow_add hlogX0]
        congr 1
        ring
      have hs5 : Real.log X ^ (-(A + 3)) ≤
          (((11 / 20 : ℝ) ^ (A + 3))⁻¹) * Real.log x ^ (-A) :=
        log_scale_transfer hA hlx1 hlogXge
      have hs6 : 4 * C1 * Y * Real.log X ^ (-(A + 3)) ≤
          4 * C1 * Y * ((((11 / 20 : ℝ) ^ (A + 3))⁻¹) * Real.log x ^ (-A)) := by
        exact mul_le_mul_of_nonneg_left hs5 (by positivity : (0 : ℝ) ≤ 4 * C1 * Y)
      have hs7 : 4 * (4 * C1 * Y * ((((11 / 20 : ℝ) ^ (A + 3))⁻¹) * Real.log x ^ (-A)) +
          C2 * Y * Real.log x ^ (-A)) =
          (16 * C1 * (((11 / 20 : ℝ) ^ (A + 3))⁻¹) + 4 * C2) * (Y * Real.log x ^ (-A)) := by ring
      have hs8 : (16 * C1 * (((11 / 20 : ℝ) ^ (A + 3))⁻¹) + 4 * C2) ≤ Cc := by
        have a : S ≤ T := le_max_right _ _
        have b : T ≤ Cc := le_max_left _ _
        exact le_trans a b
      have hs9 : (16 * C1 * (((11 / 20 : ℝ) ^ (A + 3))⁻¹) + 4 * C2) * (Y * Real.log x ^ (-A)) ≤
          Cc * (Y * Real.log x ^ (-A)) :=
        mul_le_mul_of_nonneg_right hs8 (mul_nonneg hY0.le hR0)
      have hs10 : Cc * (Y * Real.log x ^ (-A)) = Cc * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
        rw [← hYdef]; ring
      refine le_trans habel ?_
      calc 2 * (Real.log (K : ℝ) / Real.log Y) * M ≤ 4 * M := hs1
        _ ≤ 4 * (C1 * (2 * Y) * Real.log X ^ (-(A + 4)) * (2 * Real.log X) +
              C2 * Y * Real.log x ^ (-A)) := by linarith [hs2]
        _ = 4 * (4 * C1 * Y * (Real.log X ^ (-(A + 4)) * Real.log X) +
              C2 * Y * Real.log x ^ (-A)) := by rw [hs3]
        _ = 4 * (4 * C1 * Y * Real.log X ^ (-(A + 3)) +
              C2 * Y * Real.log x ^ (-A)) := by rw [hs4]
        _ ≤ 4 * (4 * C1 * Y * ((((11 / 20 : ℝ) ^ (A + 3))⁻¹) * Real.log x ^ (-A)) +
              C2 * Y * Real.log x ^ (-A)) := by linarith [hs6]
        _ = (16 * C1 * (((11 / 20 : ℝ) ^ (A + 3))⁻¹) + 4 * C2) * (Y * Real.log x ^ (-A)) := hs7
        _ ≤ Cc * (Y * Real.log x ^ (-A)) := hs9
        _ = Cc * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := hs10
    · have h1 : 1 ≤ L + 1 := by omega
      have h2 : (0 : ℝ) < ((L + 1 : ℕ) : ℝ) := by exact_mod_cast h1
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast h1)) hlogY0.le
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hK1)) hlogY0.le
  · rw [hS, Finset.Ioc_eq_empty_of_le hLK, Finset.sum_empty, norm_zero]
    refine mul_nonneg (mul_nonneg hCc0 (Real.rpow_nonneg hx0.le _)) ?_
    exact Real.rpow_nonneg hlx0.le _

/-- LEAF: the `h` term of the identity. The second term of the page 53 raw weight, the sum over one
prime factor at a level between `m ^ c1` and `m ^ c4` of the sifted indicator of the cofactor,
again with the recentring factor and against a non-principal character over the truncated right
interval, is bounded by `C x^(11/20+eps) (log x)^(-A)` with a constant depending only on `A`.
One summand of the target's sum and strictly easier than the target. Non-vacuity: at `t = 0` the
index set is empty and the sum is zero. -/
theorem leaf_h_term_nonprincipal
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              upperH ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: the `j` term of the identity. The third term of the page 53 raw weight, the sum over two
decreasing prime factors at levels between `m ^ c1` and `m ^ c4` of the sifted indicator of the
cofactor, with the recentring factor and against a non-principal character over the truncated right
interval, is bounded by `C x^(11/20+eps) (log x)^(-A)` with a constant depending only on `A`. One
summand of the target's sum and strictly easier than the target. Non-vacuity: at `t = 0` the index
set is empty and the sum is zero. -/
theorem leaf_j_term_nonprincipal
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              upperJ ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: the kept part of the `k` term of the identity. The fourth term of the page 53 raw weight,
the part of the three prime sum on which the covering lemma applies to an arrangement of the three
exponents, with the recentring factor and against a non-principal character over the truncated
right interval, is bounded by `C x^(11/20+eps) (log x)^(-A)` with a constant depending only on `A`.
One summand of the target's sum and strictly easier than the target: it is at most the `k` term
itself, since the deleted terms are removed rather than added. Non-vacuity: at `t = 0` the index
set is empty and the sum is zero. -/
theorem leaf_kept_term_nonprincipal
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              upperKept ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-! ### Assembly -/

/-- The target `upper_self_scaled_nonprincipal_distribution` of
SPLIT_upper_self_scaled_conditions, verbatim, assembled from the four leaves. For each power of the
logarithm the four leaves give four constants; the largest of them raised to at least four serves
as the single constant of the statement, both as the threshold beyond which `x` is passed to the
leaves and as the multiplier of `x^(11/20+eps) (log x)^(-A)`. On the index set the coefficient is
the recentring factor times `g - h + j - kept`, by the four term identity at the level `m`, so the
sum splits into the four sums of the leaves and subadditivity of the norm gives the bound. No step
uses the sealed target. -/
theorem upper_self_scaled_nonprincipal_distribution_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {b1 : ℝ → ℕ → ℝ}
    (hb : ∀ x m, b1 x m = if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then
      Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m else 0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b1 x m : ℂ) * χ (m : ZMod q))‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨Cg, hCg⟩ := leaf_g_term_nonprincipal h4 h9 hω hz hε hε8 A hA
  obtain ⟨Ch, hCh⟩ := leaf_h_term_nonprincipal h4 h9 hω hz hε hε8 A hA
  obtain ⟨Cj, hCj⟩ := leaf_j_term_nonprincipal h4 h9 hω hz hε hε8 A hA
  obtain ⟨Ck, hCk⟩ := leaf_kept_term_nonprincipal h4 h9 hω hz hε hε8 A hA
  refine ⟨max (4 * max (max Cg Ch) (max (max Cj Ck) 1)) 4,
    fun x hx q hq hqA χ hχ t ht => ?_⟩
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hCgK : Cg ≤ max (max Cg Ch) (max (max Cj Ck) 1) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hChK : Ch ≤ max (max Cg Ch) (max (max Cj Ck) 1) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hCjK : Cj ≤ max (max Cg Ch) (max (max Cj Ck) 1) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hCkK : Ck ≤ max (max Cg Ch) (max (max Cj Ck) 1) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hK1 : (1 : ℝ) ≤ max (max Cg Ch) (max (max Cj Ck) 1) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hKM : max (max Cg Ch) (max (max Cj Ck) 1) ≤
      max (4 * max (max Cg Ch) (max (max Cj Ck) 1)) 4 := by
    have h0 : (0 : ℝ) ≤ max (max Cg Ch) (max (max Cj Ck) 1) := le_trans (by norm_num) hK1
    have h4' : max (max Cg Ch) (max (max Cj Ck) 1) ≤
        4 * max (max Cg Ch) (max (max Cj Ck) 1) := by nlinarith
    exact le_trans h4' (le_max_left _ _)
  have hxg : Cg ≤ x := le_trans (le_trans hCgK hKM) hx
  have hxh : Ch ≤ x := le_trans (le_trans hChK hKM) hx
  have hxj : Cj ≤ x := le_trans (le_trans hCjK hKM) hx
  have hxk : Ck ≤ x := le_trans (le_trans hCkK hKM) hx
  have hY0 : (0 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
  have hL0 : (0 : ℝ) ≤ Real.log x ^ (-A) :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hYL : (0 : ℝ) ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) := mul_nonneg hY0 hL0
  have hY2 : (2 : ℝ) ≤ x ^ (11 / 20 + ε) := upper_Y_ge_two hε hx4
  have hpt : ∀ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      ((b1 x m : ℂ) * χ (m : ZMod q)) =
        ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperG ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q) -
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperH ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q) +
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperJ ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q) -
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperKept ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q) := by
    intro m hm
    have hmI : m ∈ rightInterval ε x := (Finset.mem_filter.mp hm).1
    have hmY : (⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) < m := (Finset.mem_Ioc.mp hmI).1
    have hmpos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hmY
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hmpos
    have hraw4 : upperRawWeight ε (m : ℝ) m =
        upperG ε (m : ℝ) m - upperH ε (m : ℝ) m + upperJ ε (m : ℝ) m -
          upperKept ε (m : ℝ) m := by
      rw [upper_raw_eq_rough_add_deleted ε (Y := (m : ℝ)) hm1 m,
        upper_rough_four_term ε (Y := (m : ℝ)) hm1 m]
      unfold upperDeletedSum
      ring
    rw [hb x m, if_pos ⟨hY2, hmI⟩, hraw4]
    exact ofReal_mul_four _ _ _ _ _ _
  have hsum : ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        ((b1 x m : ℂ) * χ (m : ZMod q)) =
      (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperG ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q)) -
        (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperH ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q)) +
        (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperJ ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q)) -
        (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
            upperKept ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)) := by
    rw [show ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((b1 x m : ℂ) * χ (m : ZMod q)) =
        ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperG ε (m : ℝ) m : ℝ) : ℂ) *
              χ (m : ZMod q) -
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperH ε (m : ℝ) m : ℝ) : ℂ) *
              χ (m : ZMod q) +
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperJ ε (m : ℝ) m : ℝ) : ℂ) *
              χ (m : ZMod q) -
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              upperKept ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q))
      from Finset.sum_congr rfl hpt]
    exact sum_four_sub _ _ _ _ _
  have hG := hCg x hxg q hq hqA χ hχ t ht
  have hH := hCh x hxh q hq hqA χ hχ t ht
  have hJ := hCj x hxj q hq hqA χ hχ t ht
  have hK := hCk x hxk q hq hqA χ hχ t ht
  rw [hsum]
  calc ‖(∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperG ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q)) -
        (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperH ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q)) +
        (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperJ ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q)) -
        (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
            upperKept ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q))‖
      ≤ ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperG ε (m : ℝ) m : ℝ) : ℂ) *
              χ (m : ZMod q)‖ +
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperH ε (m : ℝ) m : ℝ) : ℂ) *
              χ (m : ZMod q)‖ +
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperJ ε (m : ℝ) m : ℝ) : ℂ) *
              χ (m : ZMod q)‖ +
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              upperKept ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)‖ :=
        norm_sub_add_sub_le _ _ _ _
    _ ≤ Cg * x ^ (11 / 20 + ε) * Real.log x ^ (-A) + Ch * x ^ (11 / 20 + ε) * Real.log x ^ (-A) +
        Cj * x ^ (11 / 20 + ε) * Real.log x ^ (-A) + Ck * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
          linarith [hG, hH, hJ, hK]
    _ = (Cg + Ch + Cj + Ck) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
    _ ≤ (4 * max (max Cg Ch) (max (max Cj Ck) 1)) *
          (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
          apply mul_le_mul_of_nonneg_right _ hYL
          nlinarith [hCgK, hChK, hCjK, hCkK]
    _ ≤ max (4 * max (max Cg Ch) (max (max Cj Ck) 1)) 4 *
          (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hYL
    _ = max (4 * max (max Cg Ch) (max (max Cj Ck) 1)) 4 * x ^ (11 / 20 + ε) *
          Real.log x ^ (-A) := by ring

end LeanLab.BHP1997.Upper312Route
