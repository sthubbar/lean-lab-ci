/-
Split of the OPEN target `upper_self_scaled_conditions` of Upper312RouteSelfScaled into three
leaves, with an assembly that has the target's statement verbatim and uses no sorry.

The target asks for conditions iii and iv of page 3 for the self scaled upper coefficient: the
short-interval character distribution clause at the density v1 plus the deleted integral, and the
short-interval mean square clause at that same density. Conditions iii and iv are the two halves of
the page 53 argument, and condition iii itself separates into the principal character and the
non-principal characters, exactly as in the lower lane of this folder.

Leaf 1: condition iii for the principal character, that is the density statement, with no
character sum to estimate; only the size of the filter `(1 : DirichletCharacter ℂ q) (m : ZMod q)`
factor stays in the summand so that the assembly is a substitution.
Leaf 2: condition iii for the non-principal characters, that is the uniform character sum estimate
on every short initial segment; here the density term is absent because the delta factor is zero.
Leaf 3: condition iii implies condition iv for this coefficient, using the divisor bound to bound
the square sum over a moving window.

This file adds no definition, changes no existing file, and leaves the sealed statement untouched.
The assembly declares neither the target nor any leaf as a hypothesis.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Upper312RouteSelfScaled
import LeanLab.BHP1997.RoughFamily514

namespace LeanLab.BHP1997.Upper312Route
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators

/-! ### Transplant of the sorry-free term-by-term proof of the non-principal leaf

The private helpers, the four term bounds and the assembly
`upper_self_scaled_nonprincipal_distribution_split` below are copied unchanged from the
sorry-free in-tree file `LeanLab/BHP1997/SPLIT_upper_self_scaled_nonprincipal_distribution.lean`
(on main, 2026-11-22), which imports this file and therefore cannot be imported here.
The only import added is `LeanLab.BHP1997.RoughFamily514`. -/


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


/-! ### The level ladder: a variable rough level as fixed level fibres

The `g` term needed only the least prime factor of `m`, so its level `m ^ c1` became the fixed level
of one peel prime. The `h`, `j` and `kept` terms sum over prime factors inside a window, so their
cofactor keeps a level that still depends on `m`. The identity below replaces any level `M` by a
lower level `z` plus one fibre per prime of `[z, M)`, and each fibre carries the *fixed* level of
that prime, with an index range that is an interval. That is the page 53 Buchstab step in the form
the three remaining leaves need. -/

/-- A real level can be rounded up to a natural level without changing the page 53 indicator. -/
private lemma upperRough_eq_roughIndicator_ceil {n : ℕ} (hn : 2 ≤ n) (L : ℝ) :
    upperRough n L = Task308.roughIndicator n ⌈L⌉₊ := by
  rw [upperRough_eq_minFac hn, roughIndicator_eq_minFac hn]
  have key : L ≤ (n.minFac : ℝ) ↔ ⌈L⌉₊ ≤ n.minFac := by
    constructor
    · intro h
      exact Nat.ceil_le.mpr h
    · intro h
      exact le_trans (Nat.le_ceil L) (by exact_mod_cast h)
  by_cases h : L ≤ (n.minFac : ℝ)
  · rw [if_pos h, if_pos (key.mp h)]
  · rw [if_neg h, if_neg (fun hc => h (key.mpr hc))]

/-- The level ladder. For `1 ≤ z ≤ M` the rough indicator at level `M` is the indicator at the
lower level `z` minus the fibre of every prime of `[z, M)` that is a least prime factor. Each fibre
is a rough indicator at the fixed level of its own prime. -/
private lemma roughIndicator_level_decomp {n z M : ℕ} (hn : 1 ≤ n) (hz : 1 ≤ z) (hzM : z ≤ M) :
    Task308.roughIndicator n M =
      Task308.roughIndicator n z -
        ∑ p ∈ Finset.Ico z M,
          (if p.Prime ∧ p ∣ n then Task308.roughIndicator n p else 0) := by
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- `n = 1`: no prime divides `n`, and both indicators are one
    have hn1 : n = 1 := by omega
    subst hn1
    have hzero : ∀ p ∈ Finset.Ico z M,
        (if p.Prime ∧ p ∣ 1 then Task308.roughIndicator 1 p else 0) = (0 : ℝ) := by
      intro p _
      rw [if_neg]
      rintro ⟨hpp, hpd⟩
      have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) hpd
      have h2 := hpp.two_le
      omega
    rw [Finset.sum_eq_zero hzero, sub_zero]
    simp [Task308.roughIndicator]
  · -- `n ≥ 2`: only the least prime factor can contribute
    have hqP : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hqd : n.minFac ∣ n := Nat.minFac_dvd n
    have hterm : ∀ p ∈ Finset.Ico z M,
        (if p.Prime ∧ p ∣ n then Task308.roughIndicator n p else 0) =
          (if p = n.minFac then (1 : ℝ) else 0) := by
      intro p _
      by_cases hc : p.Prime ∧ p ∣ n
      · have hle : n.minFac ≤ p := Nat.minFac_le_of_dvd hc.1.two_le hc.2
        rw [if_pos hc, roughIndicator_eq_minFac hn2 p]
        by_cases hpe : p = n.minFac
        · rw [if_pos (le_of_eq hpe), if_pos hpe]
        · rw [if_neg (by omega : ¬ p ≤ n.minFac), if_neg hpe]
      · rw [if_neg hc, if_neg]
        rintro rfl
        exact hc ⟨hqP, hqd⟩
    have hsum : ∑ p ∈ Finset.Ico z M, (if p = n.minFac then (1 : ℝ) else 0) =
        if n.minFac ∈ Finset.Ico z M then (1 : ℝ) else 0 := by
      by_cases hq : n.minFac ∈ Finset.Ico z M
      · rw [if_pos hq, Finset.sum_eq_single n.minFac]
        · rw [if_pos rfl]
        · intro b _ hb
          rw [if_neg hb]
        · intro hq'
          exact absurd hq hq'
      · rw [if_neg hq, Finset.sum_eq_zero]
        intro p hp
        by_cases hpq : p = n.minFac
        · rw [if_pos hpq]
          exact absurd (hpq ▸ hp) hq
        · rw [if_neg hpq]
    rw [Finset.sum_congr rfl hterm, hsum, roughIndicator_eq_minFac hn2 M,
      roughIndicator_eq_minFac hn2 z]
    by_cases h1 : M ≤ n.minFac
    · have hzq : z ≤ n.minFac := le_trans hzM h1
      have hnot : n.minFac ∉ Finset.Ico z M := by
        simp only [Finset.mem_Ico]; omega
      rw [if_pos h1, if_pos hzq, if_neg hnot]
      norm_num
    · have hqM : n.minFac < M := by omega
      by_cases h2 : z ≤ n.minFac
      · have hin : n.minFac ∈ Finset.Ico z M := Finset.mem_Ico.mpr ⟨h2, hqM⟩
        rw [if_neg h1, if_pos h2, if_pos hin]
        norm_num
      · have hin : n.minFac ∉ Finset.Ico z M := by
          simp only [Finset.mem_Ico]; omega
        rw [if_neg h1, if_neg h2, if_neg hin]
        norm_num


/-- The level condition of one fibre, read as an interval condition on the cofactor: a prime `p`
is below the level `(d n) ^ c` exactly when the cofactor `n` exceeds `p ^ (1/c) / d`. This is what
turns the ladder's variable upper end into an interval on the summed variable. -/
private lemma peel_level_iff {c : ℝ} (hc : 0 < c) {d p n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (p : ℝ) < ((d : ℝ) * n) ^ c ↔ (p : ℝ) ^ (1 / c) / d < n := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hdn : (0 : ℝ) ≤ (d : ℝ) * (n : ℝ) := by positivity
  have hp_eq : ((p : ℝ) ^ (1 / c)) ^ c = (p : ℝ) := by
    rw [← Real.rpow_mul hp0, one_div_mul_cancel hc.ne', Real.rpow_one]
  constructor
  · intro h
    have h1 : (p : ℝ) ^ (1 / c) < (d : ℝ) * (n : ℝ) := by
      by_contra hcon
      push_neg at hcon
      have hle : ((d : ℝ) * (n : ℝ)) ^ c ≤ ((p : ℝ) ^ (1 / c)) ^ c :=
        Real.rpow_le_rpow hdn hcon hc.le
      rw [hp_eq] at hle
      linarith
    exact (div_lt_iff₀ hd0).mpr (by rw [mul_comm]; exact h1)
  · intro h
    have h1 : (p : ℝ) ^ (1 / c) < (d : ℝ) * (n : ℝ) := by
      have h2 := (div_lt_iff₀ hd0).mp h
      rw [mul_comm] at h2
      exact h2
    have h2 : ((p : ℝ) ^ (1 / c)) ^ c < ((d : ℝ) * (n : ℝ)) ^ c :=
      Real.rpow_lt_rpow (by positivity) h1 hc
    rwa [hp_eq] at h2


/-! ### The `h` term: fibres of one outer prime factor

`upperH` sums over the prime factors of `m` inside the page 53 window. The lemma below isolates one
outer prime `p1` and rewrites its contribution as a sum over the cofactor `n = m / p1`, with the
window read on `n` as an explicit condition. That is the reindexing the `h`, `j` and `kept` leaves
need; the conditions themselves are turned into intervals by `peel_level_iff` when the bound is
applied. -/

/-- The multiples of one prime inside an interval, with the page 53 window and the rough cofactor
carried to the cofactor variable. -/
private lemma upperH_fibre_reindex {ε : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q) {L K p1 : ℕ}
    (hp1 : p1.Prime) :
    ∑ m ∈ Finset.Ioc L K,
        (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε)) then
          ((upperRough (m / p1) ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) * χ (m : ZMod q) else 0)
      = χ (p1 : ZMod q) *
          ∑ n ∈ Finset.Ioc (L / p1) (K / p1),
            (if (((p1 : ℝ) * n) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < ((p1 : ℝ) * n) ^ upperC4 ε)
              then ((upperRough n (((p1 : ℝ) * n) ^ upperC1 ε) : ℝ) : ℂ) * χ (n : ZMod q)
              else 0) := by
  have hp1pos : 0 < p1 := hp1.pos
  have hp1one : 1 ≤ p1 := by omega
  -- split the conjunction so that the divisibility test can reindex
  have hsplit : ∀ m : ℕ,
      (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε)) then
        ((upperRough (m / p1) ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) * χ (m : ZMod q) else 0)
      = (if p1 ∣ m then
          (if ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε) then
            ((upperRough (m / p1) ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) * χ (m : ZMod q) else 0)
          else 0) := by
    intro m
    by_cases h : p1 ∣ m <;>
      by_cases h2 : ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε) <;>
      simp [h, h2]
  rw [Finset.sum_congr rfl (fun m _ => hsplit m)]
  rw [Rough514.sum_dvd_reindex hp1one L K
    (fun m => if ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε) then
        ((upperRough (m / p1) ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) * χ (m : ZMod q) else 0)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hdiv : (p1 * n) / p1 = n := Nat.mul_div_cancel_left n hp1pos
  have hcast : (((p1 * n : ℕ)) : ℝ) = (p1 : ℝ) * (n : ℝ) := by push_cast; ring
  have hchi : χ (((p1 * n : ℕ)) : ZMod q) = χ (p1 : ZMod q) * χ (n : ZMod q) := by
    push_cast
    rw [map_mul]
  rw [hdiv, hcast, hchi]
  by_cases hw : ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
      (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε
  · rw [if_pos hw, if_pos hw]
    ring
  · rw [if_neg hw, if_neg hw]
    ring


/-- The page 53 window read on the cofactor: for a prime `p1 ≥ 2` and a positive exponent `c`, the
two window tests `(p1 n) ^ c ≤ p1` and `p1 < (p1 n) ^ c` are the two halves of an interval in `n`,
with the endpoint `p1 ^ (1 / c - 1)`. -/
private lemma window_interval {c : ℝ} (hc : 0 < c) {p1 n : ℕ} (hp1 : 1 ≤ p1) (hn : 1 ≤ n) :
    (((p1 : ℝ) * n) ^ c ≤ (p1 : ℝ) ↔ n ≤ (p1 : ℝ) ^ (1 / c - 1)) ∧
      ((p1 : ℝ) < ((p1 : ℝ) * n) ^ c ↔ (p1 : ℝ) ^ (1 / c - 1) < n) := by
  have hp1R : (0 : ℝ) < (p1 : ℝ) := by exact_mod_cast hp1
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpnR : (0 : ℝ) < (p1 : ℝ) * (n : ℝ) := by positivity
  have hsub : (p1 : ℝ) ^ (1 / c - 1) = (p1 : ℝ) ^ (1 / c) / (p1 : ℝ) := by
    rw [Real.rpow_sub hp1R (1 / c) 1, Real.rpow_one]
  constructor
  · -- the upper test
    have heq : ((p1 : ℝ) ^ (1 / c)) ^ c = (p1 : ℝ) := by
      rw [← Real.rpow_mul hp1R.le, one_div_mul_cancel hc.ne', Real.rpow_one]
    constructor
    · intro h
      have h1 : (p1 : ℝ) * (n : ℝ) ≤ (p1 : ℝ) ^ (1 / c) := by
        by_contra hcon
        push_neg at hcon
        have hle : ((p1 : ℝ) ^ (1 / c)) ^ c < (((p1 : ℝ) * (n : ℝ))) ^ c :=
          Real.rpow_lt_rpow (by positivity) hcon hc
        rw [heq] at hle
        linarith
      rw [hsub, le_div_iff₀ hp1R]
      calc (n : ℝ) * (p1 : ℝ) = (p1 : ℝ) * (n : ℝ) := by ring
        _ ≤ (p1 : ℝ) ^ (1 / c) := h1
    · intro h
      have h2 : (p1 : ℝ) * (n : ℝ) ≤ (p1 : ℝ) ^ (1 / c) := by
        rw [hsub, le_div_iff₀ hp1R] at h
        calc (p1 : ℝ) * (n : ℝ) = (n : ℝ) * (p1 : ℝ) := by ring
          _ ≤ (p1 : ℝ) ^ (1 / c) := h
      have h3 := Real.rpow_le_rpow (le_of_lt hpnR) h2 hc.le
      rwa [heq] at h3
  · -- the lower test, from the fibre level identity
    have hiff := peel_level_iff (c := c) hc (d := p1) (p := p1) (n := n) hp1 hn
    rw [hsub]
    exact hiff


/-- The `h` term reindexed by its outer prime factor. The page 53 fibre sum of `upperH` over the
interval is the double sum over the outer prime `p1` and the cofactor, with the window carried to
the cofactor variable. This is the sum level form of `upperH_fibre_reindex`. -/
private lemma upperH_sum_reindex {ε : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q) {L K : ℕ} :
    ∑ m ∈ Finset.Ioc L K, ((upperH ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)
      = ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          χ (p1 : ZMod q) *
            ∑ n ∈ Finset.Ioc (L / p1) (K / p1),
              (if (((p1 : ℝ) * n) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                  (p1 : ℝ) < ((p1 : ℝ) * n) ^ upperC4 ε)
                then ((upperRough n (((p1 : ℝ) * n) ^ upperC1 ε) : ℝ) : ℂ) * χ (n : ZMod q)
                else 0) := by
  have hper : ∀ m ∈ Finset.Ioc L K,
      ((upperH ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q) =
        ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
            then ((upperRough (m / p1) ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) * χ (m : ZMod q)
            else 0) := by
    intro m hm
    obtain ⟨hmL, hmK⟩ := Finset.mem_Ioc.mp hm
    have hm0 : 0 < m := by omega
    have hset : m.primeFactors.filter
          (fun p : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (m : ℝ) ^ upperC4 ε)
        = ((Finset.Icc 2 K).filter Nat.Prime).filter
            (fun p1 => p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < (m : ℝ) ^ upperC4 ε)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨hpp, hpd, -⟩, hW⟩
        exact ⟨⟨⟨hpp.two_le, (Nat.le_of_dvd hm0 hpd).trans hmK⟩, hpp⟩, hpd, hW⟩
      · rintro ⟨⟨⟨h2p, hpK⟩, hpp⟩, hpd, hW⟩
        exact ⟨⟨hpp, hpd, by omega⟩, hW⟩
    unfold upperH
    rw [hset, Finset.sum_filter]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p1 _ => ?_
    by_cases h : (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
        (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      simp
  calc ∑ m ∈ Finset.Ioc L K, ((upperH ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)
      = ∑ m ∈ Finset.Ioc L K, ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
            then ((upperRough (m / p1) ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) * χ (m : ZMod q)
            else 0) := Finset.sum_congr rfl hper
    _ = ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          ∑ m ∈ Finset.Ioc L K,
            (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
              then ((upperRough (m / p1) ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) * χ (m : ZMod q)
              else 0) := Finset.sum_comm
    _ = ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          χ (p1 : ZMod q) *
            ∑ n ∈ Finset.Ioc (L / p1) (K / p1),
              (if (((p1 : ℝ) * n) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                  (p1 : ℝ) < ((p1 : ℝ) * n) ^ upperC4 ε)
                then ((upperRough n (((p1 : ℝ) * n) ^ upperC1 ε) : ℝ) : ℂ) * χ (n : ZMod q)
                else 0) := by
        refine Finset.sum_congr rfl fun p1 hp1 => ?_
        exact upperH_fibre_reindex (ε := ε) χ (L := L) (K := K) (p1 := p1)
          (Finset.mem_filter.mp hp1).2


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


/-! ### The `h` term: the recentring factor inside the reindexed double sum

`upperH` sums the rough indicator of the cofactor over the prime factors of `m` inside the window of
page 53. `upperH_sum_reindex` moves the outer prime factor out; the two lemmas below do the same with
the recentring factor `log m / log Y` carried along, which is what the leaf's summand has. The factor
of `m = p1 * n` is `log (p1 * n) / log Y`, so it passes to the cofactor variable unchanged. -/

/-- The `h` term of one outer prime factor, reindexed by the cofactor, with the recentring factor
carried along. -/
private lemma upperH_fibre_reindex_weighted {ε Y : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q)
    {L K p1 : ℕ} (hp1 : p1.Prime) :
    ∑ m ∈ Finset.Ioc L K,
        (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε)) then
          ((Real.log (m : ℝ) / Real.log Y * upperRough (m / p1) ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) *
            χ (m : ZMod q) else 0)
      = χ (p1 : ZMod q) *
          ∑ n ∈ Finset.Ioc (L / p1) (K / p1),
            (if (((p1 : ℝ) * n) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < ((p1 : ℝ) * n) ^ upperC4 ε)
              then ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
                upperRough n (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) * χ (n : ZMod q)
              else 0) := by
  have hp1pos : 0 < p1 := hp1.pos
  have hp1one : 1 ≤ p1 := by omega
  have hsplit : ∀ m : ℕ,
      (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε)) then
        ((Real.log (m : ℝ) / Real.log Y * upperRough (m / p1) ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) *
          χ (m : ZMod q) else 0)
      = (if p1 ∣ m then
          (if ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε) then
            ((Real.log (m : ℝ) / Real.log Y * upperRough (m / p1) ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) *
              χ (m : ZMod q) else 0)
          else 0) := by
    intro m
    by_cases h : p1 ∣ m <;>
      by_cases h2 : ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε) <;>
      simp [h, h2]
  rw [Finset.sum_congr rfl (fun m _ => hsplit m)]
  rw [Rough514.sum_dvd_reindex hp1one L K
    (fun m => if ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε) then
        ((Real.log (m : ℝ) / Real.log Y * upperRough (m / p1) ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) *
          χ (m : ZMod q) else 0)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hdiv : (p1 * n) / p1 = n := Nat.mul_div_cancel_left n hp1pos
  have hcast : (((p1 * n : ℕ)) : ℝ) = (p1 : ℝ) * (n : ℝ) := by push_cast; ring
  have hchi : χ (((p1 * n : ℕ)) : ZMod q) = χ (p1 : ZMod q) * χ (n : ZMod q) := by
    push_cast
    rw [map_mul]
  rw [hdiv, hcast, hchi]
  by_cases hw : ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
      (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε
  · rw [if_pos hw, if_pos hw]
    push_cast
    ring
  · rw [if_neg hw, if_neg hw]
    ring

/-- The `h` term reindexed by its outer prime factor, with the recentring factor inside the double
sum. -/
private lemma upperH_weighted_reindex {ε Y : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q) {L K : ℕ} :
    ∑ m ∈ Finset.Ioc L K,
        ((Real.log (m : ℝ) / Real.log Y * upperH ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)
      = ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          χ (p1 : ZMod q) *
            ∑ n ∈ Finset.Ioc (L / p1) (K / p1),
              (if (((p1 : ℝ) * n) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                  (p1 : ℝ) < ((p1 : ℝ) * n) ^ upperC4 ε)
                then ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
                  upperRough n (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) * χ (n : ZMod q)
                else 0) := by
  have hper : ∀ m ∈ Finset.Ioc L K,
      ((Real.log (m : ℝ) / Real.log Y * upperH ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q) =
        ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
            then ((Real.log (m : ℝ) / Real.log Y *
              upperRough (m / p1) ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) * χ (m : ZMod q)
            else 0) := by
    intro m hm
    obtain ⟨hmL, hmK⟩ := Finset.mem_Ioc.mp hm
    have hm0 : 0 < m := by omega
    have hset : m.primeFactors.filter
          (fun p : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (m : ℝ) ^ upperC4 ε)
        = ((Finset.Icc 2 K).filter Nat.Prime).filter
            (fun p1 => p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < (m : ℝ) ^ upperC4 ε)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨hpp, hpd, -⟩, hW⟩
        exact ⟨⟨⟨hpp.two_le, (Nat.le_of_dvd hm0 hpd).trans hmK⟩, hpp⟩, hpd, hW⟩
      · rintro ⟨⟨⟨h2p, hpK⟩, hpp⟩, hpd, hW⟩
        exact ⟨⟨hpp, hpd, by omega⟩, hW⟩
    have hinner : upperH ε (m : ℝ) m =
        ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
            then upperRough (m / p1) ((m : ℝ) ^ upperC1 ε) else 0) := by
      unfold upperH
      rw [hset, Finset.sum_filter]
    rw [hinner, Finset.mul_sum]
    rw [Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p1 _ => ?_
    by_cases h : (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
        (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      simp
  calc ∑ m ∈ Finset.Ioc L K,
        ((Real.log (m : ℝ) / Real.log Y * upperH ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)
      = ∑ m ∈ Finset.Ioc L K, ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
            then ((Real.log (m : ℝ) / Real.log Y *
              upperRough (m / p1) ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) * χ (m : ZMod q)
            else 0) := Finset.sum_congr rfl hper
    _ = ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          ∑ m ∈ Finset.Ioc L K,
            (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
              then ((Real.log (m : ℝ) / Real.log Y *
                upperRough (m / p1) ((m : ℝ) ^ upperC1 ε) : ℝ) : ℂ) * χ (m : ZMod q)
              else 0) := Finset.sum_comm
    _ = ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          χ (p1 : ZMod q) *
            ∑ n ∈ Finset.Ioc (L / p1) (K / p1),
              (if (((p1 : ℝ) * n) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                  (p1 : ℝ) < ((p1 : ℝ) * n) ^ upperC4 ε)
                then ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
                  upperRough n (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) * χ (n : ZMod q)
                else 0) := by
        refine Finset.sum_congr rfl fun p1 hp1 => ?_
        exact upperH_fibre_reindex_weighted (Y := Y) χ (L := L) (K := K) (p1 := p1)
          (Finset.mem_filter.mp hp1).2


/-- The page 53 rough indicator is at most one. -/
private lemma roughIndicator_le_one (n z : ℕ) : Task308.roughIndicator n z ≤ 1 := by
  unfold Task308.roughIndicator
  split_ifs <;> norm_num

/-- The page 53 rough indicator is antitone in the level: a larger level divides out more integers.
-/
private lemma roughIndicator_le_of_le {n z z' : ℕ} (h : z ≤ z') :
    Task308.roughIndicator n z' ≤ Task308.roughIndicator n z := by
  have h01 : Task308.roughIndicator n z = 0 ∨ Task308.roughIndicator n z = 1 := by
    unfold Task308.roughIndicator
    split_ifs <;> simp
  have key : Task308.roughIndicator n z = 0 → Task308.roughIndicator n z' = 0 := by
    intro h0
    unfold Task308.roughIndicator at h0 ⊢
    by_cases hh : n = 1 ∨ z' ≤ n.minFac
    · have h2 : n = 1 ∨ z ≤ n.minFac := hh.elim Or.inl (fun h3 => Or.inr (le_trans h h3))
      rw [if_pos h2] at h0
      exact absurd h0 (by norm_num)
    · rw [if_neg hh]
  rcases h01 with h0 | h1
  · rw [h0, key h0]
  · rw [h1]; exact roughIndicator_le_one n z'

/-- The level ladder in its reduced form: the rough indicator at level `M` is the indicator at a
lower level `z` minus the single fibre of the least prime factor in the window `[z, M)`. Composing
`roughIndicator_level_decomp` with the fact that only the least prime factor can carry a fibre. -/
private lemma roughIndicator_eq_sub_minFac {n z M : ℕ} (hn : 2 ≤ n) (hzM : z ≤ M) :
    Task308.roughIndicator n M =
      Task308.roughIndicator n z -
        (if z ≤ n.minFac ∧ n.minFac < M then (1 : ℝ) else 0) := by
  unfold Task308.roughIndicator
  by_cases hz : z ≤ n.minFac
  · by_cases hM : n.minFac < M
    · rw [if_neg (by omega : ¬ (n = 1 ∨ M ≤ n.minFac)),
          if_pos (by omega : n = 1 ∨ z ≤ n.minFac),
          if_pos (by omega : z ≤ n.minFac ∧ n.minFac < M)]
      norm_num
    · rw [if_pos (by omega : n = 1 ∨ M ≤ n.minFac),
          if_pos (by omega : n = 1 ∨ z ≤ n.minFac),
          if_neg (by omega : ¬ (z ≤ n.minFac ∧ n.minFac < M))]
      norm_num
  · rw [if_neg (by omega : ¬ (n = 1 ∨ M ≤ n.minFac)),
        if_neg (by omega : ¬ (n = 1 ∨ z ≤ n.minFac)),
        if_neg (by omega : ¬ (z ≤ n.minFac ∧ n.minFac < M))]
    norm_num

/-- The two window tests of page 53 read as the two ends of an interval in the cofactor. -/
private lemma window_nat_iff {c : ℝ} (hc : 0 < c) {p1 n : ℕ} (hp1 : 1 ≤ p1) (hn : 1 ≤ n) :
    (((p1 : ℝ) * (n : ℝ)) ^ c ≤ (p1 : ℝ) ↔ n ≤ ⌊(p1 : ℝ) ^ (1 / c - 1)⌋₊) ∧
      ((p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ c ↔ ⌊(p1 : ℝ) ^ (1 / c - 1)⌋₊ < n) := by
  obtain ⟨h1, h2⟩ := window_interval (c := c) hc hp1 hn
  have hb : (0 : ℝ) ≤ (p1 : ℝ) ^ (1 / c - 1) := by positivity
  constructor
  · rw [h1, Nat.le_floor_iff hb]
  · rw [h2]
    exact (Nat.floor_lt hb).symm

/-- A sub-interval of an integer interval cut out by two further bounds is again an integer
interval. -/
private lemma filter_window_Ioc {a b p q : ℕ} :
    (Finset.Ioc a b).filter (fun n : ℕ => n ≤ q ∧ p < n) = Finset.Ioc (max a p) (min b q) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor <;> intro h <;> omega

/-- The `h` term's fourth frozen constant is positive and below one under the standing smallness of
`ε`. -/
private lemma upperC4_pos {ε : ℝ} (hε8 : ε ≤ 1 / 10 ^ 8) : 0 < upperC4 ε := by
  unfold upperC4
  have h2 : (2 * (1 / 16 - 1 / 10 ^ 5) / 8 : ℝ) = 1 / 64 - 1 / 400000 := by norm_num
  rw [h2]
  linarith

/-- `upperC4 ε < 1` under the standing smallness of `ε`. -/
private lemma upperC4_lt_one {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    upperC4 ε < 1 := by
  unfold upperC4
  have h2 : (2 * (1 / 16 - 1 / 10 ^ 5) / 8 : ℝ) = 1 / 64 - 1 / 400000 := by norm_num
  rw [h2]
  linarith

/-- A natural below the ceiling of a real is below that real. -/
private lemma nat_lt_ceil_iff {L : ℝ} {p : ℕ} : p < ⌈L⌉₊ ↔ (p : ℝ) < L := by
  rw [← not_le, Nat.ceil_le, not_le]

/-- One term of the level ladder: a prime dividing `n` carries a rough indicator at its own level
exactly when it is the least prime factor of `n`. -/
private lemma ladder_term_eq {n p : ℕ} (hn : 2 ≤ n) :
    (if p.Prime ∧ p ∣ n then Task308.roughIndicator n p else 0) =
      (if p = n.minFac then (1 : ℝ) else 0) := by
  by_cases hc : p.Prime ∧ p ∣ n
  · obtain ⟨hpp, hpd⟩ := hc
    have hle : n.minFac ≤ p := Nat.minFac_le_of_dvd hpp.two_le hpd
    rw [if_pos ⟨hpp, hpd⟩, roughIndicator_eq_minFac hn p]
    by_cases hpe : p = n.minFac
    · rw [if_pos (le_of_eq hpe), if_pos hpe]
    · rw [if_neg (by omega : ¬ p ≤ n.minFac), if_neg hpe]
  · rw [if_neg hc]
    symm
    by_cases hpe : p = n.minFac
    · rw [if_pos hpe]
      exfalso
      apply hc
      rw [hpe]
      exact ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩
    · rw [if_neg hpe]

/-- The ladder fibres summed over the primes: the number of primes of `[z, P)` that divide `n` and
lie below the level `L` is one exactly when the least prime factor of `n` lies in `[z, L)`. -/
private lemma ladder_sum_eq {n z P : ℕ} {L : ℝ} (hn : 2 ≤ n) (hP : ⌈L⌉₊ ≤ P) :
    (∑ p ∈ Finset.Ico z P,
        (if p.Prime ∧ (p : ℝ) < L ∧ p ∣ n then Task308.roughIndicator n p else 0)) =
      (if z ≤ n.minFac ∧ (n.minFac : ℝ) < L then (1 : ℝ) else 0) := by
  have hterm : ∀ p ∈ Finset.Ico z P,
      (if p.Prime ∧ (p : ℝ) < L ∧ p ∣ n then Task308.roughIndicator n p else 0) =
        (if p = n.minFac ∧ (p : ℝ) < L then (1 : ℝ) else 0) := by
    intro p _
    by_cases hc : p.Prime ∧ (p : ℝ) < L ∧ p ∣ n
    · obtain ⟨hpp, hpL, hpd⟩ := hc
      have hle : n.minFac ≤ p := Nat.minFac_le_of_dvd hpp.two_le hpd
      rw [if_pos ⟨hpp, hpL, hpd⟩, roughIndicator_eq_minFac hn p]
      by_cases hpe : p = n.minFac
      · rw [if_pos (by omega : p ≤ n.minFac), if_pos ⟨hpe, hpL⟩]
      · rw [if_neg (by omega : ¬ p ≤ n.minFac), if_neg (by rintro ⟨h, -⟩; exact hpe h)]
    · by_cases h2 : p = n.minFac ∧ (p : ℝ) < L
      · exfalso
        apply hc
        refine ⟨?_, h2.2, ?_⟩
        · rw [h2.1]; exact Nat.minFac_prime (by omega)
        · rw [h2.1]; exact Nat.minFac_dvd n
      · rw [if_neg hc, if_neg h2]
  rw [Finset.sum_congr rfl hterm]
  by_cases hq : z ≤ n.minFac ∧ (n.minFac : ℝ) < L
  · have hML : n.minFac < ⌈L⌉₊ := nat_lt_ceil_iff.mpr hq.2
    have hmem : n.minFac ∈ Finset.Ico z P := Finset.mem_Ico.mpr ⟨hq.1, lt_of_lt_of_le hML hP⟩
    rw [if_pos hq, Finset.sum_eq_single n.minFac]
    · rw [if_pos ⟨rfl, hq.2⟩]
    · intro b _ hb
      rw [if_neg (by rintro ⟨hbe, -⟩; exact hb hbe)]
    · intro hnot
      exact absurd hmem hnot
  · rw [if_neg hq]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [if_neg]
    rintro ⟨hpe, hpL⟩
    apply hq
    refine ⟨?_, ?_⟩
    · have := (Finset.mem_Ico.mp hp).1
      omega
    · rwa [← hpe]

/-- The level ladder in the form the `h`, `j` and `kept` leaves use: the self scaled rough indicator
of the cofactor is the indicator at a fixed lower level minus the fibres of the primes of
`[z, P)` below the level. -/
private lemma rough_level_decomp_fibre {n z P : ℕ} {L : ℝ} (hn : 2 ≤ n)
    (hz : z ≤ ⌈L⌉₊) (hP : ⌈L⌉₊ ≤ P) :
    upperRough n L =
      Task308.roughIndicator n z -
        ∑ p ∈ Finset.Ico z P,
          (if p.Prime ∧ (p : ℝ) < L ∧ p ∣ n then Task308.roughIndicator n p else 0) := by
  rw [upperRough_eq_roughIndicator_ceil hn, roughIndicator_eq_sub_minFac hn hz, ladder_sum_eq hn hP]
  congr 1
  by_cases h1 : z ≤ n.minFac
  · by_cases h3 : n.minFac < ⌈L⌉₊
    · rw [if_pos ⟨h1, h3⟩, if_pos ⟨h1, nat_lt_ceil_iff.mp h3⟩]
    · rw [if_neg (by rintro ⟨-, hc⟩; exact h3 hc),
        if_neg (by rintro ⟨-, hc⟩; exact h3 (nat_lt_ceil_iff.mpr hc))]
  · rw [if_neg (by rintro ⟨h, -⟩; exact h1 h), if_neg (by rintro ⟨h, -⟩; exact h1 h)]


/-- The lower window test forces the cofactor above one: a prime in the window `[m ^ c1, m ^ c4)` with
`c4 < 1` can only be a strict divisor, so `n ≥ 2`. -/
private lemma window_ge_two {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {p1 n : ℕ}
    (hp1 : 1 ≤ p1)
    (hw : ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
      (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) : 2 ≤ n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0] at hw
    simp only [Nat.cast_zero, mul_zero] at hw
    have hc4 : 0 < upperC4 ε := upperC4_pos hε8
    rw [Real.zero_rpow hc4.ne'] at hw
    have hpos1 : (0 : ℝ) ≤ (p1 : ℝ) := by positivity
    linarith [hw.2]
  · obtain ⟨-, h2⟩ := window_nat_iff (c := upperC4 ε) (upperC4_pos hε8) hp1 hpos
    have h3 : ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊ < n := h2.mp hw.2
    have hc4 : upperC4 ε < 1 := upperC4_lt_one hε hε8
    have hc4pos : 0 < upperC4 ε := upperC4_pos hε8
    have hexp : (0 : ℝ) < 1 / upperC4 ε - 1 := by
      rw [sub_pos, lt_div_iff₀ hc4pos]
      linarith
    have hgt : (1 : ℝ) ≤ (p1 : ℝ) ^ (1 / upperC4 ε - 1) := by
      calc (1 : ℝ) = (1 : ℝ) ^ (1 / upperC4 ε - 1) := (Real.one_rpow _).symm
        _ ≤ (p1 : ℝ) ^ (1 / upperC4 ε - 1) :=
            Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp1) hexp.le
    have h4 : ((1 : ℕ) : ℝ) ≤ (p1 : ℝ) ^ (1 / upperC4 ε - 1) := by exact_mod_cast hgt
    have h5 : 1 ≤ ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊ := Nat.le_floor h4
    omega

/-- The level ladder summed over one fibre: the self scaled rough sum of the cofactor is the fixed
level rough sum minus the sums of its least prime factor fibres, summed over the primes of `[z, P)`.

This is the identity the `h`, `j` and `kept` leaves need: every piece on the right has a *fixed*
rough level, so it is a rough character sum over an interval and can be bounded by
`Rough514.rough_character_interval`. -/
private lemma fibre_ladder_identity {ε : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q) {Y : ℝ}
    {L K Pmax : ℕ} {p1 z : ℕ}
    (hS2 : ∀ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
      (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
        (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε), 2 ≤ n)
    (hzS : ∀ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
      (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
        (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε),
      z ≤ ⌈((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε⌉₊)
    (hPS : ∀ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
      (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
        (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε),
      ⌈((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε⌉₊ ≤ Pmax) :
    ∑ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
        (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε),
        ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
          upperRough n (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) * χ (n : ZMod q)
      = ∑ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
          (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
            (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε),
          ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
            Task308.roughIndicator n z : ℝ) : ℂ) * χ (n : ZMod q) -
        ∑ p ∈ Finset.Ico z Pmax,
          ∑ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
            (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε),
            (if p.Prime ∧ (p : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ∧ p ∣ n then
              ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
                Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)
              else 0) := by
  set S : Finset ℕ := (Finset.Ioc (L / p1) (K / p1)).filter
    (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
      (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) with hS
  set F : ℕ → ℂ := fun n =>
    ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
      upperRough n (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) * χ (n : ZMod q) with hF
  set G : ℕ → ℂ := fun n =>
    ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
      Task308.roughIndicator n z : ℝ) : ℂ) * χ (n : ZMod q) with hG
  set H : ℕ → ℕ → ℂ := fun p n =>
    (if p.Prime ∧ (p : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ∧ p ∣ n then
      ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
        Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)
      else 0) with hH
  have key : ∀ n ∈ S, F n = G n - ∑ p ∈ Finset.Ico z Pmax, H p n := by
    intro n hn
    rw [hS] at hn
    simp only [hF, hG, hH]
    rw [rough_level_decomp_fibre (hn := hS2 n hn) (hz := hzS n hn) (hP := hPS n hn)]
    rw [mul_sub, Complex.ofReal_sub, sub_mul]
    congr 1
    rw [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hc : (p.Prime ∧ (p : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ∧ p ∣ n)
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
      simp
  calc ∑ n ∈ S, F n
      = ∑ n ∈ S, (G n - ∑ p ∈ Finset.Ico z Pmax, H p n) := Finset.sum_congr rfl key
    _ = ∑ n ∈ S, G n - ∑ n ∈ S, ∑ p ∈ Finset.Ico z Pmax, H p n := by
        rw [Finset.sum_sub_distrib]
    _ = ∑ n ∈ S, G n - ∑ p ∈ Finset.Ico z Pmax, ∑ n ∈ S, H p n := by rw [Finset.sum_comm]


/-- The page 53 window on one fibre as an integer interval in the cofactor. -/
private lemma filter_window_eq_Ioc {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {p1 a b : ℕ}
    (hp1 : 1 ≤ p1) :
    (Finset.Ioc a b).filter
        (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) =
      Finset.Ioc (max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊)
        (min b ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊) := by
  have hpred : ∀ n : ℕ,
      (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
        (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) ↔
      (n ≤ ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ ∧ ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊ < n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have hc4 : 0 < upperC4 ε := upperC4_pos hε8
      have hzero : ((p1 : ℝ) * ((0 : ℕ) : ℝ)) ^ upperC4 ε = 0 := by
        rw [Nat.cast_zero, mul_zero, Real.zero_rpow hc4.ne']
      constructor
      · rintro ⟨-, h2⟩
        rw [hzero] at h2
        have hp1R : (0 : ℝ) ≤ (p1 : ℝ) := by positivity
        linarith
      · rintro ⟨-, h2⟩
        exact absurd h2 (by omega)
    · obtain ⟨h1, -⟩ := window_nat_iff (c := upperC1 ε) (upperC1_pos hε8) hp1 hpos
      obtain ⟨-, h2⟩ := window_nat_iff (c := upperC4 ε) (upperC4_pos hε8) hp1 hpos
      exact ⟨fun h => ⟨h1.mp h.1, h2.mp h.2⟩, fun h => ⟨h1.mpr h.1, h2.mpr h.2⟩⟩
  calc (Finset.Ioc a b).filter
        (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε)
      = (Finset.Ioc a b).filter
          (fun n : ℕ => n ≤ ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ ∧
            ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊ < n) := by
        refine Finset.filter_congr fun n _ => ?_
        exact hpred n
    _ = Finset.Ioc (max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊)
          (min b ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊) := filter_window_Ioc

/-- The fixed level part of one fibre of `h`: Abel summation against the monotone recentring factor,
with the prefix bound of the rough character sum over an interval. -/
private lemma fibre_A_le {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {Y : ℝ} {L K p1 z : ℕ} {C0 A : ℝ}
    (hp1 : p1.Prime) (hY2 : 2 ≤ Y) (hKY : (K : ℝ) ≤ 2 * Y) (hz1 : 1 ≤ z)
    (hC0 : 0 ≤ C0)
    (hpre : ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ 2 * Y →
      ‖∑ n ∈ Finset.Ioc a b, ((Task308.roughIndicator n z : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
        C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) :
    ‖∑ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
        (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε),
        ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
          Task308.roughIndicator n z : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
      4 * (C0 * ((K / p1 : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) := by
  have hp1one : 1 ≤ p1 := le_trans (by norm_num) hp1.two_le
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log (2 * Y) := Real.log_pos (by linarith)
  have hc4p : 0 < upperC4 ε := upperC4_pos hε8
  have hc4l : upperC4 ε < 1 := upperC4_lt_one hε hε8
  have hexp : (0 : ℝ) < 1 / upperC4 ε - 1 := by
    rw [sub_pos, lt_div_iff₀ hc4p]; linarith
  have hpp1 : 1 ≤ ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊ := by
    have hgt : (1 : ℝ) ≤ (p1 : ℝ) ^ (1 / upperC4 ε - 1) := by
      calc (1 : ℝ) = (1 : ℝ) ^ (1 / upperC4 ε - 1) := (Real.one_rpow _).symm
        _ ≤ (p1 : ℝ) ^ (1 / upperC4 ε - 1) :=
            Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp1one) hexp.le
    exact Nat.le_floor (by exact_mod_cast hgt)
  rw [filter_window_eq_Ioc hε hε8 hp1one]
  by_cases hle : max (L / p1) ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊ ≤
      min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊
  · have hbK : (min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊) ≤ K / p1 := min_le_left _ _
    have hbK' : ((min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ : ℕ) : ℝ) ≤ (K : ℝ) := by
      have h1 : ((min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ : ℕ) : ℝ)
          ≤ ((K / p1 : ℕ) : ℝ) := by exact_mod_cast hbK
      have h2 : ((K / p1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.div_le_self K p1
      linarith
    have hbX : ((min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ : ℕ) : ℝ) ≤ 2 * Y :=
      le_trans hbK' hKY
    have ha1 : 1 ≤ max (L / p1) ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊ :=
      le_trans hpp1 (le_max_right _ _)
    have hb1 : 1 ≤ min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ := le_trans ha1 hle
    have hposb : (0 : ℝ) < ((min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ : ℕ) : ℝ) := by
      have : (0 : ℕ) < min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ := by omega
      exact_mod_cast this
    -- the recentring factor at the top of the fibre is at most two
    have hgb : Real.log ((p1 : ℝ) *
        ((min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ : ℕ) : ℝ)) / Real.log Y ≤ 2 := by
      rw [div_le_iff₀ hlogY]
      have h3 : (K / p1 : ℕ) * p1 ≤ K := Nat.div_mul_le_self K p1
      have h4 : ((K / p1 : ℕ) * p1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast h3
      have h5 : ((min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ : ℕ) : ℝ)
          ≤ ((K / p1 : ℕ) : ℝ) := by exact_mod_cast hbK
      have h1 : (p1 : ℝ) * ((min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ : ℕ) : ℝ) ≤ (K : ℝ) := by
        nlinarith
      have h2 : Real.log ((p1 : ℝ) * ((min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ : ℕ) : ℝ))
          ≤ Real.log (2 * Y) := Real.log_le_log (by positivity) (le_trans h1 hKY)
      have h6 : Real.log (2 * Y) ≤ 2 * Real.log Y := by
        rw [Real.log_mul (by norm_num) hY0.ne']
        have h7 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY2
        linarith
      linarith
    have hM0 : (0 : ℝ) ≤ C0 * ((min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ : ℕ) : ℝ) *
        Real.log (2 * Y) ^ (-(A + 6)) :=
      mul_nonneg (mul_nonneg hC0 (le_of_lt hposb)) (Real.rpow_nonneg hlogX.le _)
    have hterm : ∀ n : ℕ,
        ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
          Task308.roughIndicator n z : ℝ) : ℂ) * χ (n : ZMod q) =
        ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y : ℝ) : ℂ) *
          (((Task308.roughIndicator n z : ℝ) : ℂ) * χ (n : ZMod q)) := by
      intro n; push_cast; ring
    rw [Finset.sum_congr rfl (fun n _ => hterm n)]
    refine le_trans (sum_mono_mul_le_of_prefix
      (f := fun n : ℕ => ((Task308.roughIndicator n z : ℝ) : ℂ) * χ (n : ZMod q))
      (g := fun n : ℕ => Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y)
      (A := max (L / p1) ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊)
      (B := min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊) hle hM0 ?_ ?_ ?_ ?_) ?_
    · -- nonnegativity at the left end
      refine div_nonneg (Real.log_nonneg ?_) hlogY.le
      have h1 : (1 : ℝ) ≤ ((max (L / p1) ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊ + 1 : ℕ) : ℝ) := by
        have h2 : (1 : ℕ) ≤ max (L / p1) ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊ + 1 := by omega
        exact_mod_cast h2
      have h3 : (1 : ℝ) ≤ (p1 : ℝ) := by exact_mod_cast hp1one
      nlinarith
    · -- nonnegativity at the right end
      refine div_nonneg (Real.log_nonneg ?_) hlogY.le
      have h3 : (1 : ℝ) ≤ (p1 : ℝ) := by exact_mod_cast hp1one
      have h4 : (1 : ℝ) ≤ ((min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hb1
      nlinarith
    · -- monotonicity of the recentring factor
      intro m hm
      refine div_le_div_of_nonneg_right ?_ hlogY.le
      have hm1 : 1 ≤ m := by
        have := (Finset.mem_Ioc.mp hm).1
        omega
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have h3 : (1 : ℝ) ≤ (p1 : ℝ) := by exact_mod_cast hp1one
      have hmp : (0 : ℝ) < (p1 : ℝ) * (m : ℝ) := by nlinarith
      refine Real.log_le_log hmp ?_
      push_cast
      nlinarith
    · -- the prefix bound from `rough_character_interval`
      intro k hk1 hk2
      have hkX : (k : ℝ) ≤ 2 * Y := le_trans (by exact_mod_cast hk2) hbX
      have hb := hpre (max (L / p1) ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊) k ha1 hkX
      refine le_trans hb ?_
      have hL : (0 : ℝ) ≤ Real.log (2 * Y) ^ (-(A + 6)) := Real.rpow_nonneg hlogX.le _
      have hk : (k : ℝ) ≤ ((min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hk2
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hC0) hL
    · -- the arithmetic
      have h1 : (0 : ℝ) ≤ C0 * Real.log (2 * Y) ^ (-(A + 6)) :=
        mul_nonneg hC0 (Real.rpow_nonneg hlogX.le _)
      have h2 : ((min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ : ℕ) : ℝ)
          ≤ ((K / p1 : ℕ) : ℝ) := by exact_mod_cast hbK
      have h3 : (0 : ℝ) ≤ ((min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ : ℕ) : ℝ) :=
        le_of_lt hposb
      have h4 : (2 : ℝ) * (Real.log ((p1 : ℝ) *
          ((min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ : ℕ) : ℝ)) / Real.log Y) *
          (C0 * ((min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ : ℕ) : ℝ) *
            Real.log (2 * Y) ^ (-(A + 6)))
          ≤ 2 * 2 * (C0 * ((K / p1 : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) := by
        nlinarith [hgb, h1, h2, h3]
      linarith
  · rw [Finset.Ioc_eq_empty_of_le (by omega : min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ ≤
      max (L / p1) ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊), Finset.sum_empty, norm_zero]
    have hp : (0 : ℝ) ≤ ((K / p1 : ℕ) : ℝ) := by positivity
    have h1 : (0 : ℝ) ≤ C0 * ((K / p1 : ℕ) : ℝ) := mul_nonneg hC0 hp
    have h2 : (0 : ℝ) ≤ Real.log (2 * Y) ^ (-(A + 6)) := Real.rpow_nonneg hlogX.le _
    linarith [mul_nonneg h1 h2]


/-- The two frozen page 53 exponents are at most a third under the standing smallness of `ε`. -/
private lemma upperC1_le_third {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    upperC1 ε ≤ 1 / 3 := by
  unfold upperC1
  have h2 : (7 * (2 * (1 / 16 - 1 / 10 ^ 5)) : ℝ) = 7 * (1 / 8 - 1 / 50000) := by norm_num
  rw [h2]; linarith

/-- The fourth frozen page 53 exponent is at most a third under the standing smallness of `ε`. -/
private lemma upperC4_le_third {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    upperC4 ε ≤ 1 / 3 := by
  unfold upperC4
  have h2 : (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ) = 1 / 8 - 1 / 50000 := by norm_num
  rw [h2]; linarith

/-- The exponent comparison behind the lower end of the prime fibres: with `c1, c4 ≤ 1/3` one has
`(1/c4 - 1) (1/c1 - 2) ≥ 1`. -/
private lemma exponent_product_ge_one {c1 c4 : ℝ} (h1 : 0 < c1) (h1c : c1 ≤ 1 / 3)
    (h4 : 0 < c4) (h4c : c4 ≤ 1 / 3) : 1 ≤ (1 / c4 - 1) * (1 / c1 - 2) := by
  have h1' : 3 ≤ 1 / c1 := by
    rw [le_div_iff₀ h1]; nlinarith
  have h4' : 3 ≤ 1 / c4 := by
    rw [le_div_iff₀ h4]; nlinarith
  have e1 : 1 ≤ 1 / c1 - 2 := by linarith
  have e4 : 2 ≤ 1 / c4 - 1 := by linarith
  have e0 : (0 : ℝ) ≤ 1 / c4 - 1 := by linarith
  nlinarith [e1, e4, e0]

/-- The lower end of a prime fibre of the ladder is at least the prime itself: `p` is either below
the window's low end, or so large that the level condition `p < (p1 n) ^ c1` already forces
`n > thr` with `thr ≥ p`. This is what makes `A / p ≥ 1` for the Abel step. -/
private lemma thr_ge_of_gt {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {p1 p : ℕ} (hp1 : p1.Prime)
    (hp : p.Prime) {A0 : ℕ} (hA0 : ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊ ≤ A0) (hpA : A0 < p) :
    (p : ℝ) ≤ (p : ℝ) ^ (1 / upperC1 ε) / (p1 : ℝ) := by
  have hc1 : 0 < upperC1 ε := upperC1_pos hε8
  have hc4 : 0 < upperC4 ε := upperC4_pos hε8
  have hc1c : upperC1 ε ≤ 1 / 3 := upperC1_le_third hε hε8
  have hc4c : upperC4 ε ≤ 1 / 3 := upperC4_le_third hε hε8
  have hp2 : 2 ≤ p := hp.two_le
  have hp1R : (1 : ℝ) ≤ (p1 : ℝ) := by
    have := hp1.two_le
    exact_mod_cast (le_trans (by norm_num) this)
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1pos : (0 : ℝ) < (p1 : ℝ) := by linarith
  -- `p` exceeds the window's low end `p1 ^ (1/c4 - 1)`
  have hlt : (p1 : ℝ) ^ (1 / upperC4 ε - 1) < (p : ℝ) := by
    have hnat : (⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊ : ℕ) + 1 ≤ p := by omega
    have h1 : (((⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊ : ℕ) + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast hnat
    push_cast at h1
    have h2 := Nat.lt_floor_add_one ((p1 : ℝ) ^ (1 / upperC4 ε - 1))
    linarith
  -- hence `p ^ (1/c1 - 1) > p1 ^ ((1/c4 - 1) (1/c1 - 1)) ≥ p1`
  have hexp4 : (0 : ℝ) < 1 / upperC4 ε - 1 := by
    rw [sub_pos, lt_div_iff₀ hc4]; linarith
  have hexp1 : (0 : ℝ) < 1 / upperC1 ε - 1 := by
    rw [sub_pos, lt_div_iff₀ hc1]; linarith
  have hexp2 : (0 : ℝ) < 1 / upperC1 ε - 2 := by
    have h3 : (3 : ℝ) ≤ 1 / upperC1 ε := by
      rw [le_div_iff₀ hc1]; nlinarith
    linarith
  have hprod : 1 ≤ (1 / upperC4 ε - 1) * (1 / upperC1 ε - 2) :=
    exponent_product_ge_one hc1 hc1c hc4 hc4c
  have hkey : (p : ℝ) ^ (1 / upperC1 ε - 2) ≥ (p1 : ℝ) := by
    have h1 : ((p1 : ℝ) ^ (1 / upperC4 ε - 1)) ^ (1 / upperC1 ε - 2) <
        (p : ℝ) ^ (1 / upperC1 ε - 2) :=
      Real.rpow_lt_rpow (by positivity) hlt hexp2
    have h2 : ((p1 : ℝ) ^ (1 / upperC4 ε - 1)) ^ (1 / upperC1 ε - 2) =
        (p1 : ℝ) ^ ((1 / upperC4 ε - 1) * (1 / upperC1 ε - 2)) := by
      rw [← Real.rpow_mul (by positivity)]
    have h3 : (p1 : ℝ) ^ (1 : ℝ) ≤ (p1 : ℝ) ^ ((1 / upperC4 ε - 1) * (1 / upperC1 ε - 2)) :=
      Real.rpow_le_rpow_of_exponent_le hp1R hprod
    rw [Real.rpow_one] at h3
    linarith [h1, h2, h3]
  -- `thr = p ^ (1/c1 - 1) / p1 = p ^ (1/c1 - 2) * p / p1 ≥ p`
  have hsplit : (p : ℝ) ^ (1 / upperC1 ε) =
      (p : ℝ) ^ (1 / upperC1 ε - 2) * (p : ℝ) * (p : ℝ) := by
    rw [show 1 / upperC1 ε = (1 / upperC1 ε - 2) + 2 by ring]
    rw [Real.rpow_add hpR, show (2 : ℝ) = 1 + 1 by norm_num, Real.rpow_add hpR,
      Real.rpow_one]
    ring
  rw [hsplit, le_div_iff₀ hp1pos]
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := by
    have : 1 ≤ p := by omega
    exact_mod_cast this
  have hPe : (1 : ℝ) ≤ (p : ℝ) ^ (1 / upperC1 ε - 2) := Real.one_le_rpow hP1 hexp2.le
  calc (p : ℝ) * (p1 : ℝ) ≤ (p : ℝ) * (p : ℝ) ^ (1 / upperC1 ε - 2) :=
        mul_le_mul_of_nonneg_left hkey hpR.le
    _ ≤ (p : ℝ) * ((p : ℝ) ^ (1 / upperC1 ε - 2) * (p : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hpR.le
        have hPpos : (0 : ℝ) < (p : ℝ) ^ (1 / upperC1 ε - 2) :=
          Real.rpow_pos_of_pos hpR _
        nlinarith [hPpos, hP1]
    _ = (p : ℝ) ^ (1 / upperC1 ε - 2) * (p : ℝ) * (p : ℝ) := by ring


/-- One prime fibre of the ladder reindexed: the fibre over the multiples of `p` becomes a sum over
the cofactor `k = n / p` with the fixed level `p`, the level condition `p < (p1 n) ^ c1` becoming the
lower end `⌊p ^ (1/c1) / p1⌋` of the interval in `k`. -/
private lemma fibre_B_reindex {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {Y : ℝ} {L K p1 p : ℕ} (hp1 : p1.Prime) (hp : p.Prime) :
    ∑ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
        (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε),
        (if p.Prime ∧ (p : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ∧ p ∣ n then
          ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
            Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)
          else 0)
      = χ (p : ZMod q) *
          ∑ k ∈ Finset.Ioc
              (max (max (L / p1) ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊)
                ⌊(p : ℝ) ^ (1 / upperC1 ε) / (p1 : ℝ)⌋₊ / p)
              (min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ / p),
            ((Real.log ((p1 : ℝ) * (p : ℝ) * (k : ℝ)) / Real.log Y *
              Task308.roughIndicator k p : ℝ) : ℂ) * χ (k : ZMod q) := by
  have hp1one : 1 ≤ p1 := le_trans (by norm_num) hp1.two_le
  have hp2 : 2 ≤ p := hp.two_le
  have hc1 : 0 < upperC1 ε := upperC1_pos hε8
  -- the level condition is a lower bound on the cofactor
  have hlevel : ∀ n : ℕ,
      (p : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ↔
        ⌊(p : ℝ) ^ (1 / upperC1 ε) / (p1 : ℝ)⌋₊ < n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have hz : ((p1 : ℝ) * ((0 : ℕ) : ℝ)) ^ upperC1 ε = 0 := by
        rw [Nat.cast_zero, mul_zero, Real.zero_rpow hc1.ne']
      rw [hz]
      have h0' : (0 : ℝ) ≤ (p : ℝ) ^ (1 / upperC1 ε) / (p1 : ℝ) := by positivity
      constructor
      · intro h
        have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
        linarith
      · intro h
        exact absurd h (by omega)
    · have hiff := peel_level_iff (c := upperC1 ε) hc1 (d := p1) (p := p) (n := n) hp1one hpos
      have h0' : (0 : ℝ) ≤ (p : ℝ) ^ (1 / upperC1 ε) / (p1 : ℝ) := by positivity
      rw [hiff]
      exact ⟨fun h => (Nat.floor_lt h0').mpr h, fun h => (Nat.floor_lt h0').mp h⟩
  rw [filter_window_eq_Ioc hε hε8 hp1one]
  -- the prime test is redundant, and the level condition joins the lower end
  have hif : ∀ n : ℕ,
      (if p.Prime ∧ (p : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ∧ p ∣ n then
        ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
          Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)
        else 0)
      = (if ⌊(p : ℝ) ^ (1 / upperC1 ε) / (p1 : ℝ)⌋₊ < n ∧ p ∣ n then
        ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
          Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)
        else 0) := by
    intro n
    by_cases h : ⌊(p : ℝ) ^ (1 / upperC1 ε) / (p1 : ℝ)⌋₊ < n ∧ p ∣ n
    · rw [if_pos ⟨hp, (hlevel n).mpr h.1, h.2⟩, if_pos h]
    · rw [if_neg, if_neg h]
      rintro ⟨-, hlev, hdvd⟩
      exact h ⟨(hlevel n).mp hlev, hdvd⟩
  rw [Finset.sum_congr rfl (fun n _ => hif n)]
  have hset : (Finset.Ioc (max (L / p1) ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊)
        (min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊)).filter
        (fun n => ⌊(p : ℝ) ^ (1 / upperC1 ε) / (p1 : ℝ)⌋₊ < n ∧ p ∣ n)
      = (Finset.Ioc (max (max (L / p1) ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊)
          ⌊(p : ℝ) ^ (1 / upperC1 ε) / (p1 : ℝ)⌋₊)
          (min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊)).filter (fun n => p ∣ n) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨by omega, h2⟩, h4⟩
    · rintro ⟨⟨h1, h2⟩, h4⟩
      exact ⟨⟨by omega, h2⟩, by omega, h4⟩
  rw [← Finset.sum_filter, hset, Finset.sum_filter]
  -- reindex the multiples of `p`
  rw [Rough514.sum_dvd_reindex (by omega : 1 ≤ p) _ _
    (fun m => ((Real.log ((p1 : ℝ) * (m : ℝ)) / Real.log Y *
      Task308.roughIndicator m p : ℝ) : ℂ) * χ (m : ZMod q))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hchi : χ (((p * k : ℕ)) : ZMod q) = χ (p : ZMod q) * χ (k : ZMod q) := by
    push_cast
    rw [map_mul]
  have hrough : Task308.roughIndicator (p * k) p = Task308.roughIndicator k p := by
    rw [Rough514.rough_prime_mul hp, if_pos (le_refl p)]
  have harg : ((p1 : ℝ) * (((p * k : ℕ)) : ℝ)) = (p1 : ℝ) * (p : ℝ) * (k : ℝ) := by
    push_cast
    ring
  rw [hchi, hrough, harg]
  ring


set_option maxHeartbeats 20000000 in
/-- One prime fibre of the ladder, bounded: after the reindexing of `fibre_B_reindex` the sum over the
cofactor has the fixed level `p ≥ X ^ (c1/2)`, so Abel summation against the monotone recentring
factor and `Rough514.rough_character_interval` bound it by `4 C0 (K / (p1 p)) (log X) ^ (-(A+6))`. -/
private lemma fibre_B_le {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {Y : ℝ} {L K p1 z p : ℕ} {C0 A : ℝ}
    (hp1 : p1.Prime) (hp : p.Prime) (hpz : z ≤ p)
    (hY2 : 2 ≤ Y) (hKY : (K : ℝ) ≤ 2 * Y) (hzX : (2 * Y) ^ (upperC1 ε / 2) ≤ (z : ℝ))
    (hC0 : 0 ≤ C0)
    (hpre : ∀ (ζ a b : ℕ), (2 * Y) ^ (upperC1 ε / 2) ≤ (ζ : ℝ) → 1 ≤ a → (b : ℝ) ≤ 2 * Y →
      ‖∑ n ∈ Finset.Ioc a b, ((Task308.roughIndicator n ζ : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
        C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) :
    ‖∑ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
        (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε),
        (if p.Prime ∧ (p : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ∧ p ∣ n then
          ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
            Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)
          else 0)‖ ≤
      4 * (C0 * ((K / p1 / p : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) := by
  have hp1one : 1 ≤ p1 := le_trans (by norm_num) hp1.two_le
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : 0 < p := by omega
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log (2 * Y) := Real.log_pos (by linarith)
  have hp1R : (0 : ℝ) < (p1 : ℝ) := by exact_mod_cast hp1.pos
  have hpL : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hp1ge : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hp1oneR : (1 : ℝ) ≤ (p1 : ℝ) := by exact_mod_cast hp1one
  rw [fibre_B_reindex hε hε8 χ hp1 hp]
  set A0 : ℕ := max (max (L / p1) ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊)
    ⌊(p : ℝ) ^ (1 / upperC1 ε) / (p1 : ℝ)⌋₊ with hA0def
  set B0 : ℕ := min (K / p1) ⌊(p1 : ℝ) ^ (1 / upperC1 ε - 1)⌋₊ with hB0def
  rw [norm_mul]
  have hχ1 : ‖χ (p : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  -- the lower end of the cofactor interval is at least one
  have hpA0 : p ≤ A0 := by
    by_contra hcon
    push_neg at hcon
    have hA0pp : ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊ ≤
        max (max (L / p1) ⌊(p1 : ℝ) ^ (1 / upperC4 ε - 1)⌋₊)
          ⌊(p : ℝ) ^ (1 / upperC1 ε) / (p1 : ℝ)⌋₊ :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have hthr : (p : ℝ) ≤ (p : ℝ) ^ (1 / upperC1 ε) / (p1 : ℝ) :=
      thr_ge_of_gt hε hε8 hp1 hp hA0pp (by rw [← hA0def]; exact hcon)
    have hfl : p ≤ ⌊(p : ℝ) ^ (1 / upperC1 ε) / (p1 : ℝ)⌋₊ := Nat.le_floor hthr
    have h1 : ⌊(p : ℝ) ^ (1 / upperC1 ε) / (p1 : ℝ)⌋₊ ≤ A0 := by
      rw [hA0def]; exact le_max_right _ _
    omega
  by_cases hbA : A0 / p ≤ B0 / p
  · have ha1 : 1 ≤ A0 / p := Nat.one_le_div_iff hp0 |>.mpr hpA0
    have hbB : B0 ≤ K / p1 := by rw [hB0def]; exact min_le_left _ _
    have hbp : ((B0 / p : ℕ) : ℝ) ≤ ((K / p1 / p : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_le_div_right hbB)
    have hbX : ((B0 / p : ℕ) : ℝ) ≤ 2 * Y := by
      have h1 : ((K / p1 / p : ℕ) : ℝ) ≤ (K : ℝ) := by
        have h2 : K / p1 / p ≤ K := le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)
        exact_mod_cast h2
      linarith
    have hposb : (0 : ℝ) < ((B0 / p : ℕ) : ℝ) := by
      have : (0 : ℕ) < B0 / p := lt_of_lt_of_le (by omega : 0 < A0 / p) hbA
      exact_mod_cast this
    -- the recentring factor at the top of the cofactor interval is at most two
    have hgb : Real.log ((p1 : ℝ) * (p : ℝ) * ((B0 / p : ℕ) : ℝ)) / Real.log Y ≤ 2 := by
      rw [div_le_iff₀ hlogY]
      have h1 : (p : ℝ) * ((B0 / p : ℕ) : ℝ) ≤ (B0 : ℝ) := by
        have h2 : p * (B0 / p) ≤ B0 := Nat.mul_div_le B0 p
        exact_mod_cast h2
      have h3 : (B0 : ℝ) ≤ ((K / p1 : ℕ) : ℝ) := by exact_mod_cast hbB
      have h3' : ((K / p1 : ℕ) : ℝ) * (p1 : ℝ) ≤ (K : ℝ) := by
        have h2 : (K / p1) * p1 ≤ K := Nat.div_mul_le_self K p1
        exact_mod_cast h2
      have h4 : (p1 : ℝ) * (p : ℝ) * ((B0 / p : ℕ) : ℝ) ≤ (K : ℝ) := by nlinarith [hp1R]
      have h5 : Real.log ((p1 : ℝ) * (p : ℝ) * ((B0 / p : ℕ) : ℝ)) ≤ Real.log (2 * Y) :=
        Real.log_le_log (by positivity) (le_trans h4 hKY)
      have h6 : Real.log (2 * Y) ≤ 2 * Real.log Y := by
        rw [Real.log_mul (by norm_num) hY0.ne']
        have h7 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY2
        linarith
      linarith
    set g : ℕ → ℝ := fun k => Real.log ((p1 : ℝ) * (p : ℝ) * (k : ℝ)) / Real.log Y with hgdef
    set F : ℕ → ℂ := fun k => ((Task308.roughIndicator k p : ℝ) : ℂ) * χ (k : ZMod q) with hFdef
    set M : ℝ := C0 * ((B0 / p : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6)) with hMdef
    have hM0 : (0 : ℝ) ≤ M := by
      rw [hMdef]
      exact mul_nonneg (mul_nonneg hC0 (le_of_lt hposb)) (Real.rpow_nonneg hlogX.le _)
    have hterm : ∀ k : ℕ,
        ((Real.log ((p1 : ℝ) * (p : ℝ) * (k : ℝ)) / Real.log Y *
          Task308.roughIndicator k p : ℝ) : ℂ) * χ (k : ZMod q) = (g k : ℂ) * F k := by
      intro k; rw [hgdef, hFdef]; push_cast; ring
    have hga : (0 : ℝ) ≤ g (A0 / p + 1) := by
      rw [hgdef]
      refine div_nonneg (Real.log_nonneg ?_) hlogY.le
      have h1 : (1 : ℝ) ≤ ((A0 / p + 1 : ℕ) : ℝ) := by
        have h2 : (1 : ℕ) ≤ A0 / p + 1 := by omega
        exact_mod_cast h2
      have h3 : (1 : ℝ) ≤ (p1 : ℝ) * (p : ℝ) := by nlinarith [hp1oneR, hp1ge]
      nlinarith [h3, h1]
    have hgb2 : (0 : ℝ) ≤ g (B0 / p) := by
      rw [hgdef]
      refine div_nonneg (Real.log_nonneg ?_) hlogY.le
      have h4 : (1 : ℝ) ≤ ((B0 / p : ℕ) : ℝ) := by
        have : (1 : ℕ) ≤ B0 / p := by omega
        exact_mod_cast this
      have h3 : (1 : ℝ) ≤ (p1 : ℝ) * (p : ℝ) := by nlinarith [hp1oneR, hp1ge]
      nlinarith [h3, h4]
    have hinc : ∀ m ∈ Finset.Ioc (A0 / p) (B0 / p - 1), g m ≤ g (m + 1) := by
      intro m hm
      rw [hgdef]
      refine div_le_div_of_nonneg_right ?_ hlogY.le
      have hm1 : 1 ≤ m := by
        have := (Finset.mem_Ioc.mp hm).1
        omega
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have h3 : (1 : ℝ) ≤ (p1 : ℝ) * (p : ℝ) := by nlinarith [hp1oneR, hp1ge]
      refine Real.log_le_log (by nlinarith [h3, hmR]) ?_
      push_cast
      nlinarith
    have hP : ∀ k, A0 / p ≤ k → k ≤ B0 / p → ‖∑ m ∈ Finset.Ioc (A0 / p) k, F m‖ ≤ M := by
      intro k hk1 hk2
      have hkX : (k : ℝ) ≤ 2 * Y := le_trans (by exact_mod_cast hk2) hbX
      have hlev : (2 * Y) ^ (upperC1 ε / 2) ≤ (p : ℝ) := le_trans hzX (by exact_mod_cast hpz)
      have hb := hpre p (A0 / p) k hlev ha1 hkX
      rw [hMdef]
      refine le_trans hb ?_
      have hL : (0 : ℝ) ≤ Real.log (2 * Y) ^ (-(A + 6)) := Real.rpow_nonneg hlogX.le _
      have hk : (k : ℝ) ≤ ((B0 / p : ℕ) : ℝ) := by exact_mod_cast hk2
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hC0) hL
    have hAbel : ‖∑ k ∈ Finset.Ioc (A0 / p) (B0 / p), (g k : ℂ) * F k‖ ≤ 2 * g (B0 / p) * M :=
      sum_mono_mul_le_of_prefix hbA hM0 hga hgb2 hinc hP
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    calc ‖χ (p : ZMod q)‖ * ‖∑ k ∈ Finset.Ioc (A0 / p) (B0 / p), (g k : ℂ) * F k‖
        ≤ 1 * ‖∑ k ∈ Finset.Ioc (A0 / p) (B0 / p), (g k : ℂ) * F k‖ :=
          mul_le_mul_of_nonneg_right hχ1 (norm_nonneg _)
      _ = ‖∑ k ∈ Finset.Ioc (A0 / p) (B0 / p), (g k : ℂ) * F k‖ := one_mul _
      _ ≤ 2 * g (B0 / p) * M := hAbel
      _ = 2 * (Real.log ((p1 : ℝ) * (p : ℝ) * ((B0 / p : ℕ) : ℝ)) / Real.log Y) *
            (C0 * ((B0 / p : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) := by rw [hgdef, hMdef]
      _ ≤ 4 * (C0 * ((K / p1 / p : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) := by
          have h1 : (0 : ℝ) ≤ C0 * Real.log (2 * Y) ^ (-(A + 6)) :=
            mul_nonneg hC0 (Real.rpow_nonneg hlogX.le _)
          have h3 : (0 : ℝ) ≤ ((B0 / p : ℕ) : ℝ) := le_of_lt hposb
          nlinarith [hgb, h1, hbp, h3]
  · rw [Finset.Ioc_eq_empty_of_le (by omega : B0 / p ≤ A0 / p)]
    simp only [Finset.sum_empty, norm_zero, mul_zero]
    have hp' : (0 : ℝ) ≤ ((K / p1 / p : ℕ) : ℝ) := by positivity
    have h1 : (0 : ℝ) ≤ C0 * ((K / p1 / p : ℕ) : ℝ) := mul_nonneg hC0 hp'
    have h2 : (0 : ℝ) ≤ Real.log (2 * Y) ^ (-(A + 6)) := Real.rpow_nonneg hlogX.le _
    linarith [mul_nonneg h1 h2]



set_option maxHeartbeats 20000000 in
/-- The `h` term of the self scaled upper coefficient at a fixed scale: the ladder decomposition turns
it into one fixed level rough character sum plus one sum of prime fibres, each a rough character sum
over an interval at a fixed level at least `(2 Y) ^ (c1/2)`, and the two reciprocal sums over `p1` and
`p` cost only logarithms. -/
private lemma upperH_self_bound {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, C ≤ Y → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log Y ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ L K : ℕ, 1 ≤ L → (L : ℝ) ≤ Y → ⌊Y⌋₊ ≤ L → (K : ℝ) ≤ 2 * Y →
        ‖∑ m ∈ Finset.Ioc L K,
          ((Real.log (m : ℝ) / Real.log Y * upperH ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
          C * Y * Real.log Y ^ (-A) := by
  intro A hA
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Rough514.rough_character_interval (c := upperC1 ε / 2) (A := A + 6)
      (by linarith [upperC1_pos hε8]) (by linarith)
  refine ⟨max (96 * C0) 4, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) (le_max_right _ _)
  intro Y hY q hq hqA χ hχ L K hL hLY hLf hKY
  have hCl : (max (96 * C0) 4 : ℝ) ≤ Y := hY
  have hC4 : (4 : ℝ) ≤ Y := le_trans (le_max_right _ _) hCl
  have hY2 : 2 ≤ Y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hC0Y : C0 ≤ 2 * Y := by
    have h1 : (0 : ℝ) ≤ C0 := hC0pos.le
    have h2 : C0 ≤ 96 * C0 := by nlinarith
    have h3 : 96 * C0 ≤ max (96 * C0) 4 := le_max_left _ _
    linarith
  have hlogY1 : (1 : ℝ) ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le hY0]
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hc1 : 0 < upperC1 ε := upperC1_pos hε8
  have hc1le : upperC1 ε ≤ 1 := upperC1_le_one hε
  -- the fixed level and the top level of the ladder
  have hX : (2 * Y) ^ (upperC1 ε / 2) ≤ Y ^ upperC1 ε := level_ge hc1 hY2
  set z : ℕ := ⌈(2 * Y) ^ (upperC1 ε / 2)⌉₊ with hzdef
  set Pmax : ℕ := ⌈(K : ℝ) ^ upperC1 ε⌉₊ with hPdef
  have hzX : (2 * Y) ^ (upperC1 ε / 2) ≤ (z : ℝ) := Nat.le_ceil _
  have hz1 : 1 ≤ z := by
    have h1 : (1 : ℝ) ≤ (2 * Y) ^ (upperC1 ε / 2) := by
      have h2 : (1 : ℝ) ≤ 2 * Y := by linarith
      calc (1 : ℝ) = (1 : ℝ) ^ (upperC1 ε / 2) := (Real.one_rpow _).symm
        _ ≤ (2 * Y) ^ (upperC1 ε / 2) := Real.rpow_le_rpow (by norm_num) h2 (by positivity)
    have h2 : (1 : ℝ) ≤ (z : ℝ) := by
      rw [hzdef]
      exact le_trans h1 (Nat.le_ceil _)
    exact_mod_cast h2
  -- the modulus is within the log power the interval estimate asks for
  have hlogX : 0 < Real.log (2 * Y) := Real.log_pos (by linarith)
  have hqA' : (q : ℝ) ≤ Real.log (2 * Y) ^ (A + 6) := by
    have h1 : Real.log Y ≤ Real.log (2 * Y) := Real.log_le_log hY0 (by linarith)
    have h3 : Real.log Y ^ A ≤ Real.log (2 * Y) ^ (A + 6) := by
      have h4 : Real.log Y ^ A ≤ Real.log (2 * Y) ^ A :=
        Real.rpow_le_rpow hlogY.le h1 hA.le
      have h5 : Real.log (2 * Y) ^ A ≤ Real.log (2 * Y) ^ (A + 6) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      linarith
    linarith
  have hpre : ∀ (ζ a b : ℕ), (2 * Y) ^ (upperC1 ε / 2) ≤ (ζ : ℝ) → 1 ≤ a → (b : ℝ) ≤ 2 * Y →
      ‖∑ n ∈ Finset.Ioc a b, ((Task308.roughIndicator n ζ : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
        C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6)) := by
    intro ζ a b hζ ha hb
    exact hC0 (2 * Y) hC0Y q hq hqA' χ hχ ζ hζ a b ha hb
  -- reindex the `h` term by its outer prime factor
  rw [upperH_weighted_reindex (Y := Y) χ]
  simp only [← Finset.sum_filter]
  refine le_trans (norm_sum_le _ _) ?_
  have hfibre : ∀ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
      ‖χ (p1 : ZMod q) *
          ∑ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
            (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε),
            ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
              upperRough n (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
        4 * (C0 * ((K / p1 : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) +
          4 * (C0 * ((K / p1 : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) *
            (1 + Real.log Pmax) := by
    intro p1 hp1mem
    obtain ⟨hp1K, hp1P⟩ := Finset.mem_filter.mp hp1mem
    have hp1le : p1 ≤ K := (Finset.mem_Icc.mp hp1K).2
    have hp1 : p1.Prime := hp1P
    have hp1one : 1 ≤ p1 := le_trans (by norm_num) hp1.two_le
    have hmK : ∀ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
        (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε), p1 * n ≤ K := by
      intro n hn
      obtain ⟨hnI, -⟩ := Finset.mem_filter.mp hn
      have h1 : n ≤ K / p1 := (Finset.mem_Ioc.mp hnI).2
      calc p1 * n ≤ p1 * (K / p1) := Nat.mul_le_mul_left _ h1
        _ ≤ K := Nat.mul_div_le K p1
    have hmY : ∀ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
        (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε), Y ≤ (p1 : ℝ) * (n : ℝ) := by
      intro n hn
      obtain ⟨hnI, -⟩ := Finset.mem_filter.mp hn
      have h1 : L / p1 < n := (Finset.mem_Ioc.mp hnI).1
      have h2 : L < p1 * n := by
        have h3 : L / p1 + 1 ≤ n := by omega
        have h4 : p1 * (L / p1 + 1) ≤ p1 * n := Nat.mul_le_mul_left _ h3
        have h5 : L < p1 * (L / p1 + 1) := by
          have h6 := Nat.div_add_mod L p1
          have h7 : L % p1 < p1 := Nat.mod_lt _ (by omega : 0 < p1)
          have h8 : p1 * (L / p1 + 1) = p1 * (L / p1) + p1 := by ring
          omega
        omega
      have h6 : (L : ℝ) + 1 ≤ ((p1 * n : ℕ) : ℝ) := by
        have h7 : L + 1 ≤ p1 * n := by omega
        exact_mod_cast h7
      push_cast at h6
      have h7 : (Y : ℝ) < (L : ℝ) + 1 := by
        have h8 : (⌊Y⌋₊ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLf
        have h9 : Y < (⌊Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Y
        linarith
      linarith
    have hS2 : ∀ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
        (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε), 2 ≤ n := by
      intro n hn
      exact window_ge_two hε hε8 hp1one (Finset.mem_filter.mp hn).2
    have hzS : ∀ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
        (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε),
        z ≤ ⌈((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε⌉₊ := by
      intro n hn
      rw [hzdef]
      have h1 : (Y : ℝ) ^ upperC1 ε ≤ ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε :=
        Real.rpow_le_rpow hY0.le (hmY n hn) hc1.le
      exact Nat.ceil_le.mpr (le_trans (le_trans hX h1) (Nat.le_ceil _))
    have hPS : ∀ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
        (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε),
        ⌈((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε⌉₊ ≤ Pmax := by
      intro n hn
      rw [hPdef]
      have h1 : ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (K : ℝ) ^ upperC1 ε := by
        refine Real.rpow_le_rpow (by positivity) ?_ hc1.le
        have h2 : ((p1 * n : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast (hmK n hn)
        push_cast at h2 ⊢
        exact h2
      exact Nat.ceil_le.mpr (le_trans h1 (Nat.le_ceil _))
    have hAB := fibre_ladder_identity (Y := Y) χ hS2 hzS hPS
    rw [hAB]
    refine le_trans (norm_mul_le _ _) ?_
    refine le_trans (mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _)
      (norm_nonneg _)) ?_
    rw [one_mul]
    refine le_trans (norm_sub_le _ _) ?_
    refine add_le_add ?_ ?_
    · refine fibre_A_le hε hε8 χ hp1 (by linarith) hKY hz1 hC0pos.le ?_
      exact fun a b ha hb => hpre z a b hzX ha hb
    · refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum (g := fun p =>
        (4 * (C0 * ((K / p1 / p : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6)))))
        (fun p hpI => ?_)) ?_
      · by_cases hpp : p.Prime
        · exact fibre_B_le (p := p) (z := z) hε hε8 χ hp1 hpp (Finset.mem_Ico.mp hpI).1
            (by linarith) hKY hzX hC0pos.le hpre
        · have hzero : (∑ n ∈ (Finset.Ioc (L / p1) (K / p1)).filter
              (fun n : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε),
              (if p.Prime ∧ (p : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ∧ p ∣ n then
                ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
                  Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)
                else 0)) = 0 :=
            Finset.sum_eq_zero (fun n _ => if_neg (fun h => hpp h.1))
          rw [hzero, norm_zero]
          exact mul_nonneg (by norm_num)
            (mul_nonneg (mul_nonneg hC0pos.le (by positivity)) (Real.rpow_nonneg hlogX.le _))
      · have h1 : ∑ p ∈ Finset.Ico z Pmax, ((K / p1 / p : ℕ) : ℝ) ≤
            ((K / p1 : ℕ) : ℝ) * (1 + Real.log Pmax) := by
          have h2 : ∑ p ∈ Finset.Ico z Pmax, ((K / p1 / p : ℕ) : ℝ) ≤
              ∑ p ∈ Finset.Ico z Pmax, ((K / p1 : ℕ) : ℝ) / (p : ℝ) := by
            refine Finset.sum_le_sum fun p _ => ?_
            simpa using Nat.cast_div_le (α := ℝ) (m := K / p1) (n := p)
          have h3 : ∑ p ∈ Finset.Ico z Pmax, ((K / p1 : ℕ) : ℝ) / (p : ℝ) =
              ((K / p1 : ℕ) : ℝ) * ∑ p ∈ Finset.Ico z Pmax, (1 : ℝ) / (p : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => by ring
          have h4 : ∑ p ∈ Finset.Ico z Pmax, (1 : ℝ) / (p : ℝ) ≤ 1 + Real.log Pmax := by
            have hsub : Finset.Ico z Pmax ⊆ Finset.Icc 1 Pmax := by
              intro p hp
              obtain ⟨hzp, hpP⟩ := Finset.mem_Ico.mp hp
              exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun _ _ _ => by positivity)) ?_
            have hh := harmonic_le_one_add_log Pmax
            rw [harmonic_eq_sum_Icc] at hh
            push_cast at hh
            simpa [one_div] using hh
          calc ∑ p ∈ Finset.Ico z Pmax, ((K / p1 / p : ℕ) : ℝ)
              ≤ ∑ p ∈ Finset.Ico z Pmax, ((K / p1 : ℕ) : ℝ) / (p : ℝ) := h2
            _ = ((K / p1 : ℕ) : ℝ) * ∑ p ∈ Finset.Ico z Pmax, (1 : ℝ) / (p : ℝ) := h3
            _ ≤ ((K / p1 : ℕ) : ℝ) * (1 + Real.log Pmax) :=
                mul_le_mul_of_nonneg_left h4 (by positivity)
        calc ∑ p ∈ Finset.Ico z Pmax,
              4 * (C0 * ((K / p1 / p : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6)))
            = 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) *
                ∑ p ∈ Finset.Ico z Pmax, ((K / p1 / p : ℕ) : ℝ) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun p _ => by ring
          _ ≤ 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) *
                (((K / p1 : ℕ) : ℝ) * (1 + Real.log Pmax)) := by
              refine mul_le_mul_of_nonneg_left h1 ?_
              exact mul_nonneg (mul_nonneg (by norm_num) hC0pos.le) (Real.rpow_nonneg hlogX.le _)
          _ = 4 * (C0 * ((K / p1 : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) *
                (1 + Real.log Pmax) := by ring
  -- the outer sum over the prime factors
  refine le_trans (Finset.sum_le_sum hfibre) ?_
  have hLnn : (0 : ℝ) ≤ Real.log (2 * Y) ^ (-(A + 6)) := Real.rpow_nonneg hlogX.le _
  have hsum1 : ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, ((K / p1 : ℕ) : ℝ) ≤
      (K : ℝ) * (1 + Real.log (K : ℝ)) := by
    have h2 : ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, ((K / p1 : ℕ) : ℝ) ≤
        ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, (K : ℝ) / (p1 : ℝ) := by
      refine Finset.sum_le_sum fun p _ => ?_
      simpa using Nat.cast_div_le (α := ℝ) (m := K) (n := p)
    have h3 : ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, (K : ℝ) / (p1 : ℝ) =
        (K : ℝ) * ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, (1 : ℝ) / (p1 : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by ring
    have h4 : ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, (1 : ℝ) / (p1 : ℝ) ≤
        1 + Real.log (K : ℝ) := prime_inv_sum_le K
    calc ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, ((K / p1 : ℕ) : ℝ)
        ≤ ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, (K : ℝ) / (p1 : ℝ) := h2
      _ = (K : ℝ) * ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, (1 : ℝ) / (p1 : ℝ) := h3
      _ ≤ (K : ℝ) * (1 + Real.log (K : ℝ)) := mul_le_mul_of_nonneg_left h4 (by positivity)
  have hlogK0 : (0 : ℝ) ≤ Real.log (K : ℝ) := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0]; simp
    · exact Real.log_nonneg (by exact_mod_cast hpos)
  have hlogK : Real.log (K : ℝ) ≤ 2 * Real.log Y := by
    have h1 : Real.log (K : ℝ) ≤ Real.log (2 * Y) := by
      rcases Nat.eq_zero_or_pos K with h0 | hpos
      · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith
      · exact Real.log_le_log (by exact_mod_cast hpos) hKY
    have h2 : Real.log (2 * Y) ≤ 2 * Real.log Y := by
      rw [Real.log_mul (by norm_num) hY0.ne']
      have h3 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY2
      linarith
    linarith
  have hlogP0 : (0 : ℝ) ≤ Real.log (Pmax : ℝ) := by
    rcases Nat.eq_zero_or_pos Pmax with h0 | hpos
    · rw [h0]; simp
    · exact Real.log_nonneg (by exact_mod_cast hpos)
  have hlogP : Real.log (Pmax : ℝ) ≤ 2 * Real.log Y := by
    have hKc1 : (K : ℝ) ^ upperC1 ε ≤ (K : ℝ) := by
      rcases Nat.lt_or_ge K 2 with h | h
      · interval_cases K
        · rw [Nat.cast_zero, Real.zero_rpow hc1.ne']
        · rw [Nat.cast_one, Real.one_rpow]
      · have h2 : (1 : ℝ) ≤ (K : ℝ) := by
          exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 2) h)
        calc (K : ℝ) ^ upperC1 ε ≤ (K : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h2 hc1le
          _ = (K : ℝ) := Real.rpow_one _
    have h1 : (Pmax : ℝ) ≤ (K : ℝ) := by
      rw [hPdef]
      have h2 : ⌈(K : ℝ) ^ upperC1 ε⌉₊ ≤ K := Nat.ceil_le.mpr hKc1
      exact_mod_cast h2
    rcases Nat.eq_zero_or_pos Pmax with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith
    · exact le_trans (Real.log_le_log (by exact_mod_cast hpos) h1) hlogK
  -- combine
  have hstep : ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
      (4 * (C0 * ((K / p1 : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) +
        4 * (C0 * ((K / p1 : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) * (1 + Real.log Pmax))
      = 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * (2 + Real.log Pmax) *
          ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, ((K / p1 : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => by ring
  rw [hstep]
  -- the logarithms
  have hlogXge : Real.log Y ≤ Real.log (2 * Y) := Real.log_le_log hY0 (by linarith)
  have hLXle : Real.log (2 * Y) ^ (-(A + 6)) ≤ Real.log Y ^ (-(A + 6)) :=
    Real.rpow_le_rpow_of_nonpos hlogY hlogXge (by linarith)
  have hpow : Real.log Y ^ (-(A + 6)) * (Real.log Y * Real.log Y) = Real.log Y ^ (-(A + 4)) := by
    rw [show Real.log Y * Real.log Y = Real.log Y ^ (2 : ℝ) from by rw [Real.rpow_two]; ring]
    rw [← Real.rpow_add hlogY]
    congr 1
    ring
  have hlY : (0 : ℝ) ≤ Real.log Y ^ (-A) := Real.rpow_nonneg hlogY.le _
  have hl4 : Real.log Y ^ (-(A + 4)) ≤ Real.log Y ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hlogY1 (by linarith)
  have hYnn : (0 : ℝ) ≤ Y := hY0.le
  have h1 : (2 + Real.log Pmax) ≤ 4 * Real.log Y := by linarith
  have h2 : (1 + Real.log (K : ℝ)) ≤ 3 * Real.log Y := by linarith
  have hp2 : (0 : ℝ) ≤ 2 + Real.log Pmax := by linarith
  have hp3 : (0 : ℝ) ≤ 1 + Real.log (K : ℝ) := by linarith
  have hprod : (2 + Real.log Pmax) * ((K : ℝ) * (1 + Real.log (K : ℝ))) ≤
      (4 * Real.log Y) * ((2 * Y) * (3 * Real.log Y)) := by
    refine mul_le_mul h1 (mul_le_mul hKY h2 hp3 (by linarith)) (by nlinarith [hp2, hp3])
      (by nlinarith [hlogY1])
  have hW : Real.log (2 * Y) ^ (-(A + 6)) * ((4 * Real.log Y) * ((2 * Y) * (3 * Real.log Y)))
      ≤ 24 * Y * Real.log Y ^ (-A) := by
    have hWy : (0 : ℝ) ≤ 4 * Real.log Y * ((2 * Y) * (3 * Real.log Y)) := by
      have h3 : (0 : ℝ) ≤ Real.log Y := hlogY.le
      nlinarith [h3, hYnn]
    have hsplit : Real.log (2 * Y) ^ (-(A + 6)) * ((4 * Real.log Y) * ((2 * Y) * (3 * Real.log Y)))
        = 24 * Y * (Real.log (2 * Y) ^ (-(A + 6)) * (Real.log Y * Real.log Y)) := by ring
    rw [hsplit]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (mul_le_mul_of_nonneg_right hLXle (by positivity)) ?_
    rw [hpow]
    exact hl4
  calc 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * (2 + Real.log Pmax) *
        ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, ((K / p1 : ℕ) : ℝ)
      ≤ 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) *
          ((2 + Real.log Pmax) * ((K : ℝ) * (1 + Real.log (K : ℝ)))) := by
        have hnn : (0 : ℝ) ≤ 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) := by positivity
        have hstep2 := mul_le_mul_of_nonneg_left hsum1 hp2
        calc 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * (2 + Real.log Pmax) *
              ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, ((K / p1 : ℕ) : ℝ)
            = 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) *
                ((2 + Real.log Pmax) * ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
                  ((K / p1 : ℕ) : ℝ)) := by ring
          _ ≤ 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) *
                ((2 + Real.log Pmax) * ((K : ℝ) * (1 + Real.log (K : ℝ)))) :=
              mul_le_mul_of_nonneg_left hstep2 hnn
    _ ≤ 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) *
          ((4 * Real.log Y) * ((2 * Y) * (3 * Real.log Y))) := by
        refine mul_le_mul_of_nonneg_left hprod ?_
        positivity
    _ = 4 * C0 * (Real.log (2 * Y) ^ (-(A + 6)) * ((4 * Real.log Y) * ((2 * Y) * (3 * Real.log Y)))) := by
        ring
    _ ≤ 4 * C0 * (24 * Y * Real.log Y ^ (-A)) := by
        refine mul_le_mul_of_nonneg_left hW ?_
        exact mul_nonneg (by norm_num) hC0pos.le
    _ = 96 * C0 * Y * Real.log Y ^ (-A) := by ring
    _ ≤ max (96 * C0) 4 * Y * Real.log Y ^ (-A) := by
        have h4 : 96 * C0 ≤ max (96 * C0) 4 := le_max_left _ _
        have h6 : (0 : ℝ) ≤ Y * Real.log Y ^ (-A) := mul_nonneg hYnn hlY
        calc 96 * C0 * Y * Real.log Y ^ (-A) = (96 * C0) * (Y * Real.log Y ^ (-A)) := by ring
          _ ≤ max (96 * C0) 4 * (Y * Real.log Y ^ (-A)) := mul_le_mul_of_nonneg_right h4 h6
          _ = max (96 * C0) 4 * Y * Real.log Y ^ (-A) := by ring


/-- The `j` term of one outer prime factor, reindexed by the cofactor: the inner `p2`-sum is carried
along, and after `m = p1 * n` its window is the window at the level `p1 * n` with the fixed upper end
`p2 < p1`. -/
private lemma upperJ_fibre_reindex {ε Y : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q)
    {L K p1 : ℕ} (hp1 : 1 ≤ p1) :
    ∑ m ∈ Finset.Ioc L K,
        (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε)) then
          ((Real.log (m : ℝ) / Real.log Y *
            (∑ p2 ∈ (m / p1).primeFactors.filter
              (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
              upperRough (m / p1 / p2) ((m : ℝ) ^ upperC1 ε)) : ℝ) : ℂ) * χ (m : ZMod q)
          else 0)
      = χ (p1 : ZMod q) *
          ∑ n ∈ Finset.Ioc (L / p1) (K / p1),
            (if (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε)
              then ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
                (∑ p2 ∈ n.primeFactors.filter
                  (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                    (p2 : ℝ) < (p1 : ℝ)),
                  upperRough (n / p2) (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε)) : ℝ) : ℂ) *
                χ (n : ZMod q)
              else 0) := by
  have hp1pos : 0 < p1 := by omega
  have hsplit : ∀ m : ℕ,
      (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε)) then
        ((Real.log (m : ℝ) / Real.log Y *
          (∑ p2 ∈ (m / p1).primeFactors.filter
            (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
            upperRough (m / p1 / p2) ((m : ℝ) ^ upperC1 ε)) : ℝ) : ℂ) * χ (m : ZMod q)
        else 0)
      = (if p1 ∣ m then
          (if ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε) then
            ((Real.log (m : ℝ) / Real.log Y *
              (∑ p2 ∈ (m / p1).primeFactors.filter
                (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
                upperRough (m / p1 / p2) ((m : ℝ) ^ upperC1 ε)) : ℝ) : ℂ) * χ (m : ZMod q)
            else 0)
          else 0) := by
    intro m
    by_cases h : p1 ∣ m <;>
      by_cases h2 : ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε) <;>
      simp [h, h2]
  rw [Finset.sum_congr rfl (fun m _ => hsplit m)]
  rw [Rough514.sum_dvd_reindex hp1 L K
    (fun m => if ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε) then
        ((Real.log (m : ℝ) / Real.log Y *
          (∑ p2 ∈ (m / p1).primeFactors.filter
            (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
            upperRough (m / p1 / p2) ((m : ℝ) ^ upperC1 ε)) : ℝ) : ℂ) * χ (m : ZMod q)
        else 0)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hdiv : (p1 * n) / p1 = n := Nat.mul_div_cancel_left n hp1pos
  have hcast : (((p1 * n : ℕ)) : ℝ) = (p1 : ℝ) * (n : ℝ) := by push_cast; ring
  have hchi : χ (((p1 * n : ℕ)) : ZMod q) = χ (p1 : ZMod q) * χ (n : ZMod q) := by
    push_cast
    rw [map_mul]
  have hsum : (∑ p2 ∈ ((p1 * n) / p1).primeFactors.filter
        (fun p2 : ℕ => (((p1 * n : ℕ)) : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
        upperRough ((p1 * n) / p1 / p2) ((((p1 * n : ℕ)) : ℝ) ^ upperC1 ε))
      = ∑ p2 ∈ n.primeFactors.filter
        (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
        upperRough (n / p2) (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε) := by
    rw [hdiv, hcast]
  rw [hsum, hchi, hcast]
  by_cases hw : ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
      (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε
  · rw [if_pos hw, if_pos hw]
    ring
  · rw [if_neg hw, if_neg hw]
    ring

/-- The `j` term reindexed by its outer prime factor, with the recentring factor inside the double
sum and the inner `p2`-sum carried along. -/
private lemma upperJ_weighted_reindex {ε Y : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q) {L K : ℕ} :
    ∑ m ∈ Finset.Ioc L K,
        ((Real.log (m : ℝ) / Real.log Y * upperJ ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)
      = ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          χ (p1 : ZMod q) *
            ∑ n ∈ Finset.Ioc (L / p1) (K / p1),
              (if (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                  (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε)
                then ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
                  (∑ p2 ∈ n.primeFactors.filter
                    (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                      (p2 : ℝ) < (p1 : ℝ)),
                    upperRough (n / p2) (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε)) : ℝ) : ℂ) *
                  χ (n : ZMod q)
                else 0) := by
  have hper : ∀ m ∈ Finset.Ioc L K,
      ((Real.log (m : ℝ) / Real.log Y * upperJ ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q) =
        ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
            then ((Real.log (m : ℝ) / Real.log Y *
              (∑ p2 ∈ (m / p1).primeFactors.filter
                (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
                upperRough (m / p1 / p2) ((m : ℝ) ^ upperC1 ε)) : ℝ) : ℂ) * χ (m : ZMod q)
            else 0) := by
    intro m hm
    obtain ⟨hmL, hmK⟩ := Finset.mem_Ioc.mp hm
    have hm0 : 0 < m := by omega
    have hset : m.primeFactors.filter
          (fun p : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (m : ℝ) ^ upperC4 ε)
        = ((Finset.Icc 2 K).filter Nat.Prime).filter
            (fun p1 => p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < (m : ℝ) ^ upperC4 ε)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨hpp, hpd, -⟩, hW⟩
        exact ⟨⟨⟨hpp.two_le, (Nat.le_of_dvd hm0 hpd).trans hmK⟩, hpp⟩, hpd, hW⟩
      · rintro ⟨⟨⟨h2p, hpK⟩, hpp⟩, hpd, hW⟩
        exact ⟨⟨hpp, hpd, by omega⟩, hW⟩
    have hinner : upperJ ε (m : ℝ) m =
        ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
            then (∑ p2 ∈ (m / p1).primeFactors.filter
              (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
              upperRough (m / p1 / p2) ((m : ℝ) ^ upperC1 ε)) else 0) := by
      unfold upperJ
      rw [hset, Finset.sum_filter]
    rw [hinner, Finset.mul_sum]
    rw [Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p1 _ => ?_
    by_cases h : (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
        (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      simp
  calc ∑ m ∈ Finset.Ioc L K,
        ((Real.log (m : ℝ) / Real.log Y * upperJ ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)
      = ∑ m ∈ Finset.Ioc L K, ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
            then ((Real.log (m : ℝ) / Real.log Y *
              (∑ p2 ∈ (m / p1).primeFactors.filter
                (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
                upperRough (m / p1 / p2) ((m : ℝ) ^ upperC1 ε)) : ℝ) : ℂ) * χ (m : ZMod q)
            else 0) := Finset.sum_congr rfl hper
    _ = ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          ∑ m ∈ Finset.Ioc L K,
            (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
              then ((Real.log (m : ℝ) / Real.log Y *
                (∑ p2 ∈ (m / p1).primeFactors.filter
                  (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
                  upperRough (m / p1 / p2) ((m : ℝ) ^ upperC1 ε)) : ℝ) : ℂ) * χ (m : ZMod q)
              else 0) := Finset.sum_comm
    _ = ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          χ (p1 : ZMod q) *
            ∑ n ∈ Finset.Ioc (L / p1) (K / p1),
              (if (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                  (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε)
                then ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
                  (∑ p2 ∈ n.primeFactors.filter
                    (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                      (p2 : ℝ) < (p1 : ℝ)),
                    upperRough (n / p2) (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε)) : ℝ) : ℂ) *
                  χ (n : ZMod q)
                else 0) := by
        refine Finset.sum_congr rfl fun p1 hp1 => ?_
        exact upperJ_fibre_reindex (Y := Y) χ (le_trans (by norm_num) (Finset.mem_filter.mp hp1).2.two_le)

/-- Peeling the second prime factor of the `j` term: for a fixed outer prime `p1` the inner sum over the
prime factors of the cofactor in the window `[(p1 n)^c1, p1)` becomes a sum over the fixed prime set,
the two sums are interchanged, and the multiples of `p2` are reindexed by `n = p2 * k`. What remains is
a condition on `k` plus the fixed ordering `p2 < p1`. -/
private lemma upperJ_inner_peel {ε Y : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q) {L' K' p1 : ℕ}
    (hp1 : 1 ≤ p1) :
    ∑ n ∈ Finset.Ioc L' K',
        (if (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
            (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) then
          ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
            (∑ p2 ∈ n.primeFactors.filter
              (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                (p2 : ℝ) < (p1 : ℝ)),
              upperRough (n / p2) (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε)) : ℝ) : ℂ) *
            χ (n : ZMod q)
          else 0)
      = ∑ p2 ∈ (Finset.Icc 2 K').filter Nat.Prime,
          (if (p2 : ℝ) < (p1 : ℝ) then
            χ (p2 : ZMod q) *
              ∑ k ∈ Finset.Ioc (L' / p2) (K' / p2),
                (if ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                    (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
                    (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ))
                  then ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
                    upperRough k ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) *
                    χ (k : ZMod q)
                  else 0)
            else 0) := by
  have hone : ∀ n ∈ Finset.Ioc L' K',
      (∑ p2 ∈ n.primeFactors.filter
        (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
        upperRough (n / p2) (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε))
      = ∑ p2 ∈ (Finset.Icc 2 K').filter Nat.Prime,
          (if (p2 ∣ n ∧ (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
            (p2 : ℝ) < (p1 : ℝ))) then
            upperRough (n / p2) (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε) else 0) := by
    intro n hn
    obtain ⟨hnL, hnK⟩ := Finset.mem_Ioc.mp hn
    have hn0 : 0 < n := by omega
    have hset : n.primeFactors.filter
          (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ))
        = ((Finset.Icc 2 K').filter Nat.Prime).filter
            (fun p2 => p2 ∣ n ∧ (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
              (p2 : ℝ) < (p1 : ℝ))) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨hpp, hpd, -⟩, hW⟩
        exact ⟨⟨⟨hpp.two_le, (Nat.le_of_dvd hn0 hpd).trans hnK⟩, hpp⟩, hpd, hW⟩
      · rintro ⟨⟨⟨h2p, hpK⟩, hpp⟩, hpd, hW⟩
        exact ⟨⟨hpp, hpd, by omega⟩, hW⟩
    rw [hset, Finset.sum_filter]
  have hper : ∀ n ∈ Finset.Ioc L' K',
      (if (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) then
        ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
          (∑ p2 ∈ n.primeFactors.filter
            (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
              (p2 : ℝ) < (p1 : ℝ)),
            upperRough (n / p2) (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε)) : ℝ) : ℂ) *
          χ (n : ZMod q)
        else 0)
      = ∑ p2 ∈ (Finset.Icc 2 K').filter Nat.Prime,
          (if ((((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) ∧
              p2 ∣ n ∧ (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                (p2 : ℝ) < (p1 : ℝ))) then
            ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
              upperRough (n / p2) (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) *
              χ (n : ZMod q)
            else 0) := by
    intro n hn
    rw [hone n hn]
    by_cases hA : (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
        (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε)
    · rw [if_pos hA, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p2 _ => ?_
      by_cases hB : (p2 ∣ n ∧ (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
          (p2 : ℝ) < (p1 : ℝ)))
      · rw [if_pos hB, if_pos ⟨hA, hB⟩]
      · rw [if_neg hB, if_neg (fun h => hB h.2)]
        simp
    · rw [if_neg hA]
      refine (Finset.sum_eq_zero fun p2 _ => ?_).symm
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact hA h1
  rw [Finset.sum_congr rfl hper, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p2 hp2 => ?_
  have hp2P : p2.Prime := (Finset.mem_filter.mp hp2).2
  have hp2pos : 0 < p2 := hp2P.pos
  by_cases hlt : (p2 : ℝ) < (p1 : ℝ)
  · rw [if_pos hlt]
    have hsplit : ∀ n : ℕ,
        (if ((((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
            (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) ∧
            p2 ∣ n ∧ (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
              (p2 : ℝ) < (p1 : ℝ))) then
          ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
            upperRough (n / p2) (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) *
            χ (n : ZMod q)
          else 0)
        = (if p2 ∣ n then
            (if ((((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) ∧
                (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                  (p2 : ℝ) < (p1 : ℝ))) then
              ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
                upperRough (n / p2) (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) *
                χ (n : ZMod q)
              else 0)
            else 0) := by
      intro n
      by_cases h : p2 ∣ n <;>
        by_cases h2 : ((((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
            (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) ∧
            (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ))) <;>
        simp [h, h2]
    rw [Finset.sum_congr rfl (fun n _ => hsplit n)]
    rw [Rough514.sum_dvd_reindex (le_trans (by norm_num) hp2P.two_le) L' K'
      (fun n => if ((((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) ∧
          (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ))) then
        ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
          upperRough (n / p2) (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) *
          χ (n : ZMod q)
        else 0)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hdiv : (p2 * k) / p2 = k := Nat.mul_div_cancel_left k hp2pos
    have hchi : χ (((p2 * k : ℕ)) : ZMod q) = χ (p2 : ZMod q) * χ (k : ZMod q) := by
      push_cast
      rw [map_mul]
    have harg : ((p1 : ℝ) * (((p2 * k : ℕ)) : ℝ)) = ((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ) := by
      push_cast; ring
    have hrough : upperRough ((p2 * k) / p2) (((p1 : ℝ) * (((p2 * k : ℕ)) : ℝ)) ^ upperC1 ε)
        = upperRough k ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε) := by
      rw [hdiv, harg]
    have hlogeq : Real.log ((p1 : ℝ) * (((p2 * k : ℕ)) : ℝ)) / Real.log Y =
        Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y := by rw [harg]
    have hcond : ((((p1 : ℝ) * (((p2 * k : ℕ)) : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (((p2 * k : ℕ)) : ℝ)) ^ upperC4 ε) ∧
          (((p1 : ℝ) * (((p2 * k : ℕ)) : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)))
        ↔ ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
          (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ)) := by
      rw [harg]
      exact ⟨fun h => ⟨h.1.1, h.1.2, h.2.1⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2, hlt⟩⟩
    rw [hrough, hlogeq, hchi]
    by_cases hc : ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
        (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
        (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ))
    · rw [if_pos (hcond.mpr hc), if_pos hc]
      ring
    · rw [if_neg (fun h => hc (hcond.mp h)), if_neg hc]
      ring
  · rw [if_neg hlt]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [if_neg]
    rintro ⟨-, -, -, h4⟩
    exact hlt h4

/-- The level ladder summed over an arbitrary index set: for any `S` of integers above one the self
scaled rough sum of the cofactor is the fixed level rough sum minus the sums of the least prime factor
fibres. Generalises `fibre_ladder_identity`, which is this statement for the window filtered interval
of one prime factor, to the index sets that the `j` and `kept` fibres produce. -/
private lemma ladder_identity_general {ε : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q) {Y : ℝ}
    {d Pmax z : ℕ} {S : Finset ℕ}
    (hS2 : ∀ n ∈ S, 2 ≤ n)
    (hzS : ∀ n ∈ S, z ≤ ⌈((d : ℝ) * (n : ℝ)) ^ upperC1 ε⌉₊)
    (hPS : ∀ n ∈ S, ⌈((d : ℝ) * (n : ℝ)) ^ upperC1 ε⌉₊ ≤ Pmax) :
    ∑ n ∈ S, ((Real.log ((d : ℝ) * (n : ℝ)) / Real.log Y *
        upperRough n (((d : ℝ) * (n : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) * χ (n : ZMod q)
      = ∑ n ∈ S, ((Real.log ((d : ℝ) * (n : ℝ)) / Real.log Y *
          Task308.roughIndicator n z : ℝ) : ℂ) * χ (n : ZMod q) -
        ∑ p ∈ Finset.Ico z Pmax,
          ∑ n ∈ S,
            (if p.Prime ∧ (p : ℝ) < ((d : ℝ) * (n : ℝ)) ^ upperC1 ε ∧ p ∣ n then
              ((Real.log ((d : ℝ) * (n : ℝ)) / Real.log Y *
                Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)
              else 0) := by
  set F : ℕ → ℂ := fun n =>
    ((Real.log ((d : ℝ) * (n : ℝ)) / Real.log Y *
      upperRough n (((d : ℝ) * (n : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) * χ (n : ZMod q) with hF
  set G : ℕ → ℂ := fun n =>
    ((Real.log ((d : ℝ) * (n : ℝ)) / Real.log Y *
      Task308.roughIndicator n z : ℝ) : ℂ) * χ (n : ZMod q) with hG
  set H : ℕ → ℕ → ℂ := fun p n =>
    (if p.Prime ∧ (p : ℝ) < ((d : ℝ) * (n : ℝ)) ^ upperC1 ε ∧ p ∣ n then
      ((Real.log ((d : ℝ) * (n : ℝ)) / Real.log Y *
        Task308.roughIndicator n p : ℝ) : ℂ) * χ (n : ZMod q)
      else 0) with hH
  have key : ∀ n ∈ S, F n = G n - ∑ p ∈ Finset.Ico z Pmax, H p n := by
    intro n hn
    simp only [hF, hG, hH]
    rw [rough_level_decomp_fibre (hn := hS2 n hn) (hz := hzS n hn) (hP := hPS n hn)]
    rw [mul_sub, Complex.ofReal_sub, sub_mul]
    congr 1
    rw [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hc : (p.Prime ∧ (p : ℝ) < ((d : ℝ) * (n : ℝ)) ^ upperC1 ε ∧ p ∣ n)
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
      simp
  calc ∑ n ∈ S, F n
      = ∑ n ∈ S, (G n - ∑ p ∈ Finset.Ico z Pmax, H p n) := Finset.sum_congr rfl key
    _ = ∑ n ∈ S, G n - ∑ n ∈ S, ∑ p ∈ Finset.Ico z Pmax, H p n := by
        rw [Finset.sum_sub_distrib]
    _ = ∑ n ∈ S, G n - ∑ p ∈ Finset.Ico z Pmax, ∑ n ∈ S, H p n := by rw [Finset.sum_comm]

/-- The fixed level part of one fibre over a plain interval: Abel summation against the monotone
recentring factor `log (d k)/log Y` with the prefix bound of the rough character sum. This is
`fibre_A_le` without the window conversion, for the interval index sets that the `j` and `kept`
fibres produce. -/
private lemma interval_A_le {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {Y : ℝ} {d K z a b : ℕ} {C0 A : ℝ}
    (hd : 1 ≤ d) (hY2 : 2 ≤ Y) (hKY : (K : ℝ) ≤ 2 * Y) (hz1 : 1 ≤ z)
    (hab : a ≤ b) (ha1 : 1 ≤ a) (hdbK : d * b ≤ K) (hC0 : 0 ≤ C0)
    (hpre : ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ 2 * Y →
      ‖∑ n ∈ Finset.Ioc a b, ((Task308.roughIndicator n z : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
        C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) :
    ‖∑ k ∈ Finset.Ioc a b,
        ((Real.log ((d : ℝ) * (k : ℝ)) / Real.log Y *
          Task308.roughIndicator k z : ℝ) : ℂ) * χ (k : ZMod q)‖ ≤
      4 * (C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log (2 * Y) := Real.log_pos (by linarith)
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hb1 : 1 ≤ b := le_trans ha1 hab
  have hposb : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hbX : (b : ℝ) ≤ 2 * Y := by
    have h1 : ((d * b : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hdbK
    push_cast at h1
    nlinarith
  have hdb2 : (d : ℝ) * (b : ℝ) ≤ 2 * Y := by
    have h1 : ((d * b : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hdbK
    push_cast at h1
    linarith
  -- the recentring factor at the top of the interval is at most two
  have hgb : Real.log ((d : ℝ) * (b : ℝ)) / Real.log Y ≤ 2 := by
    rw [div_le_iff₀ hlogY]
    have h2 : Real.log ((d : ℝ) * (b : ℝ)) ≤ Real.log (2 * Y) :=
      Real.log_le_log (by positivity) hdb2
    have h6 : Real.log (2 * Y) ≤ 2 * Real.log Y := by
      rw [Real.log_mul (by norm_num) hY0.ne']
      have h7 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY2
      linarith
    linarith
  have hM0 : (0 : ℝ) ≤ C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6)) :=
    mul_nonneg (mul_nonneg hC0 hposb.le) (Real.rpow_nonneg hlogX.le _)
  have hterm : ∀ k : ℕ,
      ((Real.log ((d : ℝ) * (k : ℝ)) / Real.log Y *
        Task308.roughIndicator k z : ℝ) : ℂ) * χ (k : ZMod q) =
      ((Real.log ((d : ℝ) * (k : ℝ)) / Real.log Y : ℝ) : ℂ) *
        (((Task308.roughIndicator k z : ℝ) : ℂ) * χ (k : ZMod q)) := by
    intro k; push_cast; ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  refine le_trans (sum_mono_mul_le_of_prefix
    (f := fun k : ℕ => ((Task308.roughIndicator k z : ℝ) : ℂ) * χ (k : ZMod q))
    (g := fun k : ℕ => Real.log ((d : ℝ) * (k : ℝ)) / Real.log Y)
    (A := a) (B := b) hab hM0 ?_ ?_ ?_ ?_) ?_
  · -- nonnegativity at the left end
    refine div_nonneg (Real.log_nonneg ?_) hlogY.le
    have h1 : (1 : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by
      have h2 : (1 : ℕ) ≤ a + 1 := by omega
      exact_mod_cast h2
    have h3 : (1 : ℝ) ≤ (d : ℝ) := hdR
    nlinarith
  · -- nonnegativity at the right end
    refine div_nonneg (Real.log_nonneg ?_) hlogY.le
    have hb1R : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
    nlinarith [hdR, hb1R]
  · -- monotonicity
    intro m hm
    refine div_le_div_of_nonneg_right ?_ hlogY.le
    have hm1 : 1 ≤ m := by
      have := (Finset.mem_Ioc.mp hm).1
      omega
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hmp : (0 : ℝ) < (d : ℝ) * (m : ℝ) := by nlinarith
    refine Real.log_le_log hmp ?_
    push_cast
    nlinarith
  · -- the prefix bound
    intro k hk1 hk2
    have hkX : (k : ℝ) ≤ 2 * Y := le_trans (by exact_mod_cast hk2) hbX
    have hb := hpre a k ha1 hkX
    refine le_trans hb ?_
    have hL : (0 : ℝ) ≤ Real.log (2 * Y) ^ (-(A + 6)) := Real.rpow_nonneg hlogX.le _
    have hk : (k : ℝ) ≤ (b : ℝ) := by exact_mod_cast hk2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hC0) hL
  · -- the arithmetic
    have h3 : (0 : ℝ) ≤ (b : ℝ) := hposb.le
    have h4 : (2 : ℝ) * (Real.log ((d : ℝ) * (b : ℝ)) / Real.log Y) *
        (C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) ≤
        4 * (C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) := by
      have h1 : (0 : ℝ) ≤ C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6)) := hM0
      nlinarith [hgb, h1]
    linarith

/-- Sharper rational bounds on the two frozen exponents, used by the two-prime threshold argument:
`c1` lies in `[31/250, 1/8]` and `c4` is at most `133/500`. -/
private lemma upperC1_bounds {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    upperC1 ε ≤ 1 / 8 ∧ 31 / 250 ≤ upperC1 ε := by
  have h2 : (7 * (2 * (1 / 16 - 1 / 10 ^ 5)) : ℝ) = 7 * (1 / 8 - 1 / 50000) := by norm_num
  constructor
  · unfold upperC1; rw [h2]; nlinarith [hε.le, hε8]
  · unfold upperC1; rw [h2]; linarith

/-- The fourth frozen exponent is at most `133/500`. -/
private lemma upperC4_le_133_500 {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    upperC4 ε ≤ 133 / 500 := by
  have h2 : (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ) = 1 / 8 - 1 / 50000 := by norm_num
  unfold upperC4; rw [h2]; nlinarith [hε.le, hε8]

/-- The exponent comparison of the two-prime threshold: `2 ≤ (1/c4 - 2)(1/c1 - 1)`. -/
private lemma exponent_pair_ge_two {c1 c4 : ℝ} (h1 : 0 < c1) (h1hi : c1 ≤ 1 / 8)
    (h4 : 0 < c4) (h4hi : c4 ≤ 133 / 500) :
    2 ≤ (1 / c4 - 2) * (1 / c1 - 1) := by
  have h4' : (500 : ℝ) / 133 ≤ 1 / c4 := by rw [le_div_iff₀ h4]; nlinarith
  have h1' : (8 : ℝ) ≤ 1 / c1 := by rw [le_div_iff₀ h1]; nlinarith
  have e4 : (234 : ℝ) / 133 ≤ 1 / c4 - 2 := by linarith
  have e1 : (7 : ℝ) ≤ 1 / c1 - 1 := by linarith
  have e0 : (0 : ℝ) ≤ 1 / c4 - 2 := by linarith
  calc (2 : ℝ) ≤ 7 * (234 / 133) := by norm_num
    _ = (234 / 133) * 7 := by ring
    _ ≤ (1 / c4 - 2) * (1 / c1 - 1) := mul_le_mul e4 e1 (by norm_num) e0

/-- The two-prime threshold: if the index interval's low end is at least the pair window's floor
`p1 ^ (1/c4) / (p1 p2)` and below `p`, then `p ≤ p ^ (1/c1) / (p1 p2)`, so the prime fibre's level
condition forces the cofactor above one. Since `p2 < p1`, the floor hypothesis gives
`p > p1 ^ (1/c4 - 2)`, and `p1 ^ ((1/c4 - 2)(1/c1 - 1)) ≥ p1 ^ 2 > p1 p2` closes the argument. -/
private lemma thr_ge_of_gt_pair {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {p1 p2 p : ℕ}
    (hp1 : p1.Prime) (hp2 : p2.Prime) (hlt : p2 < p1) (hp : p.Prime)
    {A0 : ℕ} (hA0 : ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ ≤ A0)
    (hpA : A0 < p) :
    (p : ℝ) ≤ (p : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ)) := by
  have hc1 : 0 < upperC1 ε := upperC1_pos hε8
  have hc4 : 0 < upperC4 ε := upperC4_pos hε8
  obtain ⟨hc1hi, hc1lo⟩ := upperC1_bounds hε hε8
  have hc4hi : upperC4 ε ≤ 133 / 500 := upperC4_le_133_500 hε hε8
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp2R : (0 : ℝ) < (p2 : ℝ) := by exact_mod_cast hp2.pos
  have hp1pos : (0 : ℝ) < (p1 : ℝ) := by exact_mod_cast hp1.pos
  have hp1R : (1 : ℝ) ≤ (p1 : ℝ) := by
    exact_mod_cast (le_trans (by norm_num) hp1.two_le)
  have hdR : (0 : ℝ) < (p1 : ℝ) * (p2 : ℝ) := by positivity
  -- the interval's low end is below `p`, so the pair window's floor is below `p`
  have hx : (p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ)) < (p : ℝ) := by
    have hnat : ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ + 1 ≤ p := by omega
    have h1 : (((⌊(p1 : ℝ) ^ (1 / upperC4 ε) /
        ((p1 : ℝ) * (p2 : ℝ))⌋₊ : ℕ)) : ℝ) + 1 ≤ (p : ℝ) := by
      exact_mod_cast hnat
    have h2 := Nat.lt_floor_add_one ((p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ)))
    linarith
  have h2 : (p1 : ℝ) ^ (1 / upperC4 ε) < (p : ℝ) * ((p1 : ℝ) * (p2 : ℝ)) := by
    have h3 := mul_lt_mul_of_pos_right hx hdR
    rwa [div_mul_cancel₀ _ hdR.ne'] at h3
  -- hence `p1 ^ (1/c4 - 2) < p`
  have hsplit : (p1 : ℝ) ^ (1 / upperC4 ε) = (p1 : ℝ) ^ (1 / upperC4 ε - 1) * (p1 : ℝ) := by
    nth_rewrite 1 [show 1 / upperC4 ε = (1 / upperC4 ε - 1) + 1 by ring]
    rw [Real.rpow_add hp1pos, Real.rpow_one]
  have h3 : (p1 : ℝ) ^ (1 / upperC4 ε - 1) < (p : ℝ) * (p2 : ℝ) := by
    rw [hsplit] at h2
    have h2' : (p1 : ℝ) ^ (1 / upperC4 ε - 1) * (p1 : ℝ) < ((p : ℝ) * (p2 : ℝ)) * (p1 : ℝ) := by
      nlinarith [h2]
    exact lt_of_mul_lt_mul_right h2' hp1pos.le
  have h4 : (p1 : ℝ) ^ (1 / upperC4 ε - 2) < (p : ℝ) := by
    have h5 : (p1 : ℝ) ^ (1 / upperC4 ε - 1) / (p2 : ℝ) < (p : ℝ) := by
      rw [div_lt_iff₀ hp2R]
      linarith
    have h6 : (p1 : ℝ) ^ (1 / upperC4 ε - 2) ≤ (p1 : ℝ) ^ (1 / upperC4 ε - 1) / (p2 : ℝ) := by
      have h9 : (p1 : ℝ) ^ (1 / upperC4 ε - 2) = (p1 : ℝ) ^ (1 / upperC4 ε - 1) / (p1 : ℝ) := by
        have hsub : 1 / upperC4 ε - 2 = (1 / upperC4 ε - 1) - 1 := by ring
        rw [hsub, Real.rpow_sub hp1pos, Real.rpow_one]
      rw [h9]
      refine div_le_div_of_nonneg_left (Real.rpow_nonneg hp1pos.le _) hp2R ?_
      exact_mod_cast le_of_lt hlt
    linarith
  -- raise to `1/c1 - 1` and compare exponents
  have hexp : (0 : ℝ) < 1 / upperC1 ε - 1 := by
    rw [sub_pos, lt_div_iff₀ hc1]; linarith
  have hprod : 2 ≤ (1 / upperC4 ε - 2) * (1 / upperC1 ε - 1) :=
    exponent_pair_ge_two hc1 hc1hi hc4 hc4hi
  have h5 : ((p1 : ℝ) ^ (1 / upperC4 ε - 2)) ^ (1 / upperC1 ε - 1) <
      (p : ℝ) ^ (1 / upperC1 ε - 1) :=
    Real.rpow_lt_rpow (by positivity) h4 hexp
  rw [← Real.rpow_mul hp1pos.le] at h5
  have h6 : (p1 : ℝ) ^ (2 : ℝ) ≤ (p1 : ℝ) ^ ((1 / upperC4 ε - 2) * (1 / upperC1 ε - 1)) :=
    Real.rpow_le_rpow_of_exponent_le hp1R hprod
  have h7 : (p1 : ℝ) * (p2 : ℝ) < (p1 : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    have h8 : (p2 : ℝ) < (p1 : ℝ) := by exact_mod_cast hlt
    nlinarith
  have h8 : (p1 : ℝ) * (p2 : ℝ) < (p : ℝ) ^ (1 / upperC1 ε - 1) := by
    calc (p1 : ℝ) * (p2 : ℝ) < (p1 : ℝ) ^ (2 : ℝ) := h7
      _ ≤ (p1 : ℝ) ^ ((1 / upperC4 ε - 2) * (1 / upperC1 ε - 1)) := h6
      _ < (p : ℝ) ^ (1 / upperC1 ε - 1) := h5
  -- conclude
  rw [le_div_iff₀ hdR]
  calc (p : ℝ) * ((p1 : ℝ) * (p2 : ℝ)) ≤ (p : ℝ) ^ (1 / upperC1 ε - 1) * (p : ℝ) := by
        nlinarith [h8, hpR]
    _ = (p : ℝ) ^ (1 / upperC1 ε) := by
        rw [show (1 : ℝ) / upperC1 ε = (1 / upperC1 ε - 1) + 1 by ring,
          Real.rpow_add hpR, Real.rpow_one]
        ring

/-- The prime fibre of the ladder over a plain interval: the level condition is a lower bound on the
index, the multiples of `p` are reindexed by `k = p m`, and the cofactor interval starts at one because
the two-prime threshold puts its low end above `p`. Abel summation then gives the same bound as
`fibre_B_le`, with `d = p1 p2` as the multiplier of the recentring factor. -/
private lemma interval_B_le {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {Y : ℝ} {K p1 p2 z p a b : ℕ} {C0 A : ℝ}
    (hp1 : p1.Prime) (hp2 : p2.Prime) (hlt : p2 < p1) (hp : p.Prime) (hpz : z ≤ p)
    (hY2 : 2 ≤ Y) (hKY : (K : ℝ) ≤ 2 * Y) (hzX : (2 * Y) ^ (upperC1 ε / 2) ≤ (z : ℝ))
    (hdbK : p1 * p2 * b ≤ K) (hab : a ≤ b)
    (hwlo : ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ ≤ a)
    (hC0 : 0 ≤ C0)
    (hpre : ∀ (ζ a' b' : ℕ), (2 * Y) ^ (upperC1 ε / 2) ≤ (ζ : ℝ) → 1 ≤ a' → (b' : ℝ) ≤ 2 * Y →
      ‖∑ n ∈ Finset.Ioc a' b', ((Task308.roughIndicator n ζ : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
        C0 * (b' : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) :
    ‖∑ k ∈ Finset.Ioc a b,
        (if p.Prime ∧ (p : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ∧ p ∣ k then
          ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
            Task308.roughIndicator k p : ℝ) : ℂ) * χ (k : ZMod q)
          else 0)‖ ≤
      4 * (C0 * ((b / p : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) := by
  have hc1 : 0 < upperC1 ε := upperC1_pos hε8
  have hc4 : 0 < upperC4 ε := upperC4_pos hε8
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log (2 * Y) := Real.log_pos (by linarith)
  have hp0 : 0 < p := hp.pos
  have hp2le : 2 ≤ p := hp.two_le
  have hdR : (0 : ℝ) < (p1 : ℝ) * (p2 : ℝ) := by
    have h1 : (0 : ℝ) < (p1 : ℝ) := by exact_mod_cast hp1.pos
    have h2 : (0 : ℝ) < (p2 : ℝ) := by exact_mod_cast hp2.pos
    positivity
  -- (i) the level condition as a lower bound on the index
  have hlevel : ∀ k : ℕ,
      (p : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ↔
        ⌊(p : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ < k := by
    intro k
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      have hz : (((p1 : ℝ) * (p2 : ℝ)) * ((0 : ℕ) : ℝ)) ^ upperC1 ε = 0 := by
        rw [Nat.cast_zero, mul_zero, Real.zero_rpow hc1.ne']
      rw [hz]
      have h0' : (0 : ℝ) ≤ (p : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ)) := by positivity
      constructor
      · intro h
        have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
        linarith
      · intro h
        exact absurd h (by omega)
    · have hd : 1 ≤ p1 * p2 := by
        have h1 : 1 ≤ p1 := le_trans (by norm_num) hp1.two_le
        have h2 : 1 ≤ p2 := le_trans (by norm_num) hp2.two_le
        calc 1 = 1 * 1 := by ring
          _ ≤ p1 * p2 := Nat.mul_le_mul h1 h2
      have hiff := peel_level_iff (c := upperC1 ε) hc1 (d := p1 * p2) (p := p) (n := k) hd hpos
      have hcast : (((p1 * p2 : ℕ)) : ℝ) = (p1 : ℝ) * (p2 : ℝ) := by push_cast; ring
      rw [hcast] at hiff
      have h0' : (0 : ℝ) ≤ (p : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ)) := by positivity
      rw [hiff]
      exact ⟨fun h => (Nat.floor_lt h0').mpr h, fun h => (Nat.floor_lt h0').mp h⟩
  set thr : ℝ := (p : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ)) with hthrdef
  -- (ii) the low end of the index interval is at least `p`
  have hpA0 : p ≤ max a ⌊thr⌋₊ := by
    by_cases hpa : p ≤ a
    · exact le_trans hpa (le_max_left _ _)
    · push_neg at hpa
      have hthr : (p : ℝ) ≤ thr :=
        thr_ge_of_gt_pair hε hε8 hp1 hp2 hlt hp hwlo hpa
      have hfl : p ≤ ⌊thr⌋₊ := Nat.le_floor hthr
      exact le_trans hfl (le_max_right _ _)
  -- (iii) the support is the multiples of `p` in the interval `(max a ⌊thr⌋, b]`
  have hif : ∀ k : ℕ,
      (if p.Prime ∧ (p : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ∧ p ∣ k then
        ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
          Task308.roughIndicator k p : ℝ) : ℂ) * χ (k : ZMod q)
        else 0)
      = (if ⌊thr⌋₊ < k ∧ p ∣ k then
        ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
          Task308.roughIndicator k p : ℝ) : ℂ) * χ (k : ZMod q)
        else 0) := by
    intro k
    rw [← hthrdef] at *
    by_cases h : ⌊thr⌋₊ < k ∧ p ∣ k
    · rw [if_pos ⟨hp, (hlevel k).mpr h.1, h.2⟩, if_pos h]
    · rw [if_neg, if_neg h]
      rintro ⟨-, hlev, hdvd⟩
      exact h ⟨(hlevel k).mp hlev, hdvd⟩
  rw [Finset.sum_congr rfl (fun k _ => hif k)]
  have hset : (Finset.Ioc a b).filter (fun k => ⌊thr⌋₊ < k ∧ p ∣ k)
      = (Finset.Ioc (max a ⌊thr⌋₊) b).filter (fun k => p ∣ k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨by omega, h2⟩, h4⟩
    · rintro ⟨⟨h1, h2⟩, h4⟩
      exact ⟨⟨by omega, h2⟩, by omega, h4⟩
  rw [← Finset.sum_filter, hset, Finset.sum_filter]
  -- (iv) reindex the multiples of `p`
  rw [Rough514.sum_dvd_reindex (le_trans (by norm_num) hp2le) _ _
    (fun m => ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (m : ℝ)) / Real.log Y *
      Task308.roughIndicator m p : ℝ) : ℂ) * χ (m : ZMod q))]
  -- (v) Abel on the cofactor interval
  have hlow1 : 1 ≤ max a ⌊thr⌋₊ / p := Nat.one_le_div_iff hp0 |>.mpr hpA0
  have hterm : ∀ m : ℕ,
      ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * ((p * m : ℕ) : ℝ)) / Real.log Y *
        Task308.roughIndicator (p * m) p : ℝ) : ℂ) * χ (((p * m : ℕ)) : ZMod q)
      = χ (p : ZMod q) * (((Real.log (((p1 : ℝ) * (p2 : ℝ) * (p : ℝ)) * (m : ℝ)) / Real.log Y : ℝ) : ℂ) *
        (((Task308.roughIndicator m p : ℝ) : ℂ) * χ (m : ZMod q))) := by
    intro m
    have hrough : Task308.roughIndicator (p * m) p = Task308.roughIndicator m p := by
      rw [Rough514.rough_prime_mul hp, if_pos (le_refl p)]
    have harg : (((p1 : ℝ) * (p2 : ℝ)) * (((p * m : ℕ)) : ℝ)) =
        ((p1 : ℝ) * (p2 : ℝ) * (p : ℝ)) * (m : ℝ) := by push_cast; ring
    have hchi : χ (((p * m : ℕ)) : ZMod q) = χ (p : ZMod q) * χ (m : ZMod q) := by
      push_cast; rw [map_mul]
    rw [hrough, harg, hchi]
    have hcast : ((Real.log (((p1 : ℝ) * (p2 : ℝ) * (p : ℝ)) * (m : ℝ)) / Real.log Y *
        Task308.roughIndicator m p : ℝ) : ℂ)
        = ((Real.log (((p1 : ℝ) * (p2 : ℝ) * (p : ℝ)) * (m : ℝ)) / Real.log Y : ℝ) : ℂ) *
          ((Task308.roughIndicator m p : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    ring
  rw [Finset.sum_congr rfl (fun m _ => hterm m)]
  rw [← Finset.mul_sum, norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)) ?_
  rw [one_mul]
  by_cases hbA : max a ⌊thr⌋₊ / p ≤ b / p
  · -- the cofactor interval is not empty
    have hbX : ((b / p : ℕ) : ℝ) ≤ 2 * Y := by
      have h1 : ((b / p : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast Nat.div_le_self b p
      have h3 : (1 : ℕ) ≤ p1 * p2 := by
        have h4 : 1 ≤ p1 := le_trans (by norm_num) hp1.two_le
        have h5 : 1 ≤ p2 := le_trans (by norm_num) hp2.two_le
        calc 1 = 1 * 1 := by ring
          _ ≤ p1 * p2 := Nat.mul_le_mul h4 h5
      have h2 : ((p1 * p2 * b : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hdbK
      have h4 : (b : ℝ) ≤ ((p1 * p2 * b : ℕ) : ℝ) := by
        have h5 : b ≤ p1 * p2 * b := by
          calc b = 1 * b := by ring
            _ ≤ p1 * p2 * b := Nat.mul_le_mul_right b h3
        exact_mod_cast h5
      push_cast at h2 h4
      linarith
    have hdb2 : ((p1 : ℝ) * (p2 : ℝ) * (p : ℝ)) * ((b / p : ℕ) : ℝ) ≤ 2 * Y := by
      have h1 : (p : ℝ) * ((b / p : ℕ) : ℝ) ≤ (b : ℝ) := by
        have h2 : p * (b / p) ≤ b := Nat.mul_div_le b p
        exact_mod_cast h2
      have h3 : (p1 : ℝ) * (p2 : ℝ) * (p : ℝ) * ((b / p : ℕ) : ℝ)
          = (p1 : ℝ) * (p2 : ℝ) * ((p : ℝ) * ((b / p : ℕ) : ℝ)) := by ring
      rw [h3]
      have h4 : (p1 : ℝ) * (p2 : ℝ) * (b : ℝ) ≤ (K : ℝ) := by
        have h5 : ((p1 * p2 * b : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hdbK
        push_cast at h5
        linarith
      have h5 : (p1 : ℝ) * (p2 : ℝ) * (b : ℝ) ≤ 2 * Y := le_trans h4 hKY
      have hp1R : (0 : ℝ) ≤ (p1 : ℝ) := by positivity
      have hp2R : (0 : ℝ) ≤ (p2 : ℝ) := by positivity
      nlinarith [h1, h5, hp1R, hp2R]
    have hbpos : (0 : ℝ) < ((b / p : ℕ) : ℝ) := by
      have h1 : 1 ≤ b / p := le_trans hlow1 hbA
      exact_mod_cast (by omega : 0 < b / p)
    have hgb : Real.log (((p1 : ℝ) * (p2 : ℝ) * (p : ℝ)) * ((b / p : ℕ) : ℝ)) / Real.log Y ≤ 2 := by
      rw [div_le_iff₀ hlogY]
      have h2 : Real.log (((p1 : ℝ) * (p2 : ℝ) * (p : ℝ)) * ((b / p : ℕ) : ℝ)) ≤ Real.log (2 * Y) :=
        Real.log_le_log (by positivity) hdb2
      have h6 : Real.log (2 * Y) ≤ 2 * Real.log Y := by
        rw [Real.log_mul (by norm_num) hY0.ne']
        have h7 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY2
        linarith
      linarith
    have hM0 : (0 : ℝ) ≤ C0 * ((b / p : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6)) :=
      mul_nonneg (mul_nonneg hC0 hbpos.le) (Real.rpow_nonneg hlogX.le _)
    refine le_trans (sum_mono_mul_le_of_prefix
      (f := fun m : ℕ => ((Task308.roughIndicator m p : ℝ) : ℂ) * χ (m : ZMod q))
      (g := fun m : ℕ => Real.log (((p1 : ℝ) * (p2 : ℝ) * (p : ℝ)) * (m : ℝ)) / Real.log Y)
      (A := max a ⌊thr⌋₊ / p) (B := b / p) hbA hM0 ?_ ?_ ?_ ?_) ?_
    · -- nonnegativity at the left end
      refine div_nonneg (Real.log_nonneg ?_) hlogY.le
      have h1 : (1 : ℝ) ≤ ((max a ⌊thr⌋₊ / p + 1 : ℕ) : ℝ) := by
        have h2 : (1 : ℕ) ≤ max a ⌊thr⌋₊ / p + 1 := by omega
        exact_mod_cast h2
      have h3 : (1 : ℝ) ≤ (p1 : ℝ) * (p2 : ℝ) * (p : ℝ) := by
        have h4 : (1 : ℝ) ≤ (p1 : ℝ) := by exact_mod_cast (le_trans (by norm_num) hp1.two_le)
        have h5 : (1 : ℝ) ≤ (p2 : ℝ) := by exact_mod_cast (le_trans (by norm_num) hp2.two_le)
        have h6 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
        nlinarith
      nlinarith
    · -- nonnegativity at the right end
      refine div_nonneg (Real.log_nonneg ?_) hlogY.le
      have h3 : (1 : ℝ) ≤ (p1 : ℝ) * (p2 : ℝ) * (p : ℝ) := by
        have h4 : (1 : ℝ) ≤ (p1 : ℝ) := by exact_mod_cast (le_trans (by norm_num) hp1.two_le)
        have h5 : (1 : ℝ) ≤ (p2 : ℝ) := by exact_mod_cast (le_trans (by norm_num) hp2.two_le)
        have h6 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
        nlinarith
      have h4 : (1 : ℝ) ≤ ((b / p : ℕ) : ℝ) := by
        have h5 : 1 ≤ b / p := le_trans hlow1 hbA
        exact_mod_cast h5
      nlinarith
    · -- monotonicity
      intro m hm
      refine div_le_div_of_nonneg_right ?_ hlogY.le
      have hm1 : 1 ≤ m := by
        have := (Finset.mem_Ioc.mp hm).1
        omega
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have h3 : (0 : ℝ) < (p1 : ℝ) * (p2 : ℝ) * (p : ℝ) := by
        have h4 : (0 : ℝ) < (p1 : ℝ) := by exact_mod_cast hp1.pos
        have h5 : (0 : ℝ) < (p2 : ℝ) := by exact_mod_cast hp2.pos
        have h6 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
        positivity
      refine Real.log_le_log (by nlinarith) ?_
      push_cast
      nlinarith
    · -- the prefix bound
      intro k hk1 hk2
      have hkX : (k : ℝ) ≤ 2 * Y := le_trans (by exact_mod_cast hk2) hbX
      have hlev : (2 * Y) ^ (upperC1 ε / 2) ≤ (p : ℝ) := le_trans hzX (by exact_mod_cast hpz)
      have hb := hpre p (max a ⌊thr⌋₊ / p) k hlev hlow1 hkX
      refine le_trans hb ?_
      have hL : (0 : ℝ) ≤ Real.log (2 * Y) ^ (-(A + 6)) := Real.rpow_nonneg hlogX.le _
      have hk : (k : ℝ) ≤ ((b / p : ℕ) : ℝ) := by exact_mod_cast hk2
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hC0) hL
    · -- the arithmetic
      have h3 : (0 : ℝ) ≤ ((b / p : ℕ) : ℝ) := hbpos.le
      have h4 : (2 : ℝ) * (Real.log (((p1 : ℝ) * (p2 : ℝ) * (p : ℝ)) * ((b / p : ℕ) : ℝ)) /
          Real.log Y) * (C0 * ((b / p : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6)))
          ≤ 4 * (C0 * ((b / p : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) := by
        nlinarith [hgb, hM0, h3]
      linarith
  · -- the cofactor interval is empty
    rw [Finset.Ioc_eq_empty_of_le (by omega : b / p ≤ max a ⌊thr⌋₊ / p)]
    simp only [Finset.sum_empty, norm_zero]
    have h1 : (0 : ℝ) ≤ C0 * ((b / p : ℕ) : ℝ) :=
      mul_nonneg hC0 (Nat.cast_nonneg _)
    have h2 : (0 : ℝ) ≤ Real.log (2 * Y) ^ (-(A + 6)) := Real.rpow_nonneg hlogX.le _
    linarith [mul_nonneg h1 h2]

/-- The two prime windows of the `j` term read as an interval in the cofactor `k` of the pair
`p1 p2`: the three tests `((p1 p2) k)^c1 ≤ p1`, `p1 < ((p1 p2) k)^c4` and `((p1 p2) k)^c1 ≤ p2` are the
two ends of one integer interval, and the middle test against `p1` plus the upper test against `p2`
give the upper end, because `p2 < p1` makes `((p1 p2) k)^c1 ≤ p2` imply `((p1 p2) k)^c1 ≤ p1`. -/
private lemma filter_window_pair_eq_Ioc {ε : ℝ} (hε8 : ε ≤ 1 / 10 ^ 8) {p1 p2 a b : ℕ}
    (hp1 : 1 ≤ p1) (hp2 : 1 ≤ p2) (hlt : p2 ≤ p1) :
    (Finset.Ioc a b).filter
        (fun k : ℕ => (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
          (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ)) =
      Finset.Ioc (max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊)
        (min b ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊) := by
  have hc1 : 0 < upperC1 ε := upperC1_pos hε8
  have hc4 : 0 < upperC4 ε := upperC4_pos hε8
  have hp1R : (0 : ℝ) < (p1 : ℝ) := by exact_mod_cast (by omega : 0 < p1)
  have hp2R : (0 : ℝ) < (p2 : ℝ) := by exact_mod_cast (by omega : 0 < p2)
  have hdR : (0 : ℝ) < (p1 : ℝ) * (p2 : ℝ) := by positivity
  have hd : 1 ≤ p1 * p2 := by
    calc 1 = 1 * 1 := by ring
      _ ≤ p1 * p2 := Nat.mul_le_mul hp1 hp2
  have hpred : ∀ k : ℕ,
      ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
          (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ)) ↔
        (k ≤ ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ ∧
          ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ < k) := by
    intro k
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      have hdcast : (((p1 * p2 : ℕ)) : ℝ) = (p1 : ℝ) * (p2 : ℝ) := by push_cast; ring
      have hz : (((p1 : ℝ) * (p2 : ℝ)) * ((0 : ℕ) : ℝ)) ^ upperC4 ε = 0 := by
        rw [Nat.cast_zero, mul_zero, Real.zero_rpow hc4.ne']
      have hz1 : (((p1 : ℝ) * (p2 : ℝ)) * ((0 : ℕ) : ℝ)) ^ upperC1 ε = 0 := by
        rw [Nat.cast_zero, mul_zero, Real.zero_rpow hc1.ne']
      rw [hz, hz1]
      have hq0 : (0 : ℝ) ≤ (p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ)) := by positivity
      have hp0 : (0 : ℝ) ≤ (p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ)) := by positivity
      constructor
      · rintro ⟨-, h2, -⟩
        have h3 : (0 : ℝ) ≤ (p1 : ℝ) := hp1R.le
        linarith
      · rintro ⟨-, h2⟩
        exact absurd h2 (by omega)
    · have hiff4 := peel_level_iff (c := upperC4 ε) hc4 (d := p1 * p2) (p := p1) (n := k) hd hpos
      have hiff1 := peel_level_iff (c := upperC1 ε) hc1 (d := p1 * p2) (p := p2) (n := k) hd hpos
      have hcast : (((p1 * p2 : ℕ)) : ℝ) = (p1 : ℝ) * (p2 : ℝ) := by push_cast; ring
      rw [hcast] at hiff4 hiff1
      have hA : (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ↔
          k ≤ (p1 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ)) := by
        have h1 := rpow_self_le_iff (cc := upperC1 ε) hc1
          (x := ((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) (p := (p1 : ℝ)) (by positivity) (by positivity)
        rw [h1, le_div_iff₀ hdR]
        constructor <;> intro h <;> nlinarith
      have hC : (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ↔
          k ≤ (p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ)) := by
        have h1 := rpow_self_le_iff (cc := upperC1 ε) hc1
          (x := ((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) (p := (p2 : ℝ)) (by positivity) (by positivity)
        rw [h1, le_div_iff₀ hdR]
        constructor <;> intro h <;> nlinarith
      have hq0 : (0 : ℝ) ≤ (p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ)) := by positivity
      have hp0 : (0 : ℝ) ≤ (p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ)) := by positivity
      constructor
      · rintro ⟨hA', hB', hC'⟩
        exact ⟨(Nat.le_floor_iff hq0).mpr (hC.mp hC'), (Nat.floor_lt hp0).mpr (hiff4.mp hB')⟩
      · rintro ⟨hq, hp⟩
        refine ⟨hA.mpr ?_, hiff4.mpr ((Nat.floor_lt hp0).mp hp), hC.mpr ((Nat.le_floor_iff hq0).mp hq)⟩
        -- `k ≤ p2^{1/c1}/d ≤ p1^{1/c1}/d`
        have h1 : (p2 : ℝ) ^ (1 / upperC1 ε) ≤ (p1 : ℝ) ^ (1 / upperC1 ε) :=
          Real.rpow_le_rpow hp2R.le (by exact_mod_cast hlt) (le_of_lt (by positivity))
        have h2 : (p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ)) ≤
            (p1 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ)) := by
          exact div_le_div_of_nonneg_right h1 hdR.le
        have h3 : (k : ℝ) ≤ (p1 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ)) :=
          le_trans ((Nat.le_floor_iff hq0).mp hq) h2
        exact h3
  calc (Finset.Ioc a b).filter
        (fun k : ℕ => (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
          (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ))
      = (Finset.Ioc a b).filter
          (fun k : ℕ => k ≤ ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ ∧
            ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ < k) := by
        refine Finset.filter_congr fun k _ => ?_
        exact hpred k
    _ = Finset.Ioc (max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊)
          (min b ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊) := filter_window_Ioc

/-! ### The `j` term: one fibre per pair of primes -/

/-- One term of the `j` fibre, with the prime pair collected into a single natural number. -/
private lemma j_cast_term {ε : ℝ} (p1 p2 k : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) {Y : ℝ} :
    ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
        upperRough k ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) *
        χ (k : ZMod q)
      = ((Real.log (((p1 * p2 : ℕ) : ℝ) * (k : ℝ)) / Real.log Y *
        upperRough k ((((p1 * p2 : ℕ) : ℝ) * (k : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) *
        χ (k : ZMod q) := by
  have h : (((p1 * p2 : ℕ) : ℝ) * (k : ℝ)) = ((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ) := by
    push_cast
    ring
  rw [h]

/-- The same collapse of the prime pair for a term carrying the page 53 indicator at `p`. -/
private lemma j_cast_term_indicator {ε : ℝ} (p1 p2 p k : ℕ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {Y : ℝ} :
    ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
        Task308.roughIndicator k p : ℝ) : ℂ) * χ (k : ZMod q)
      = ((Real.log (((p1 * p2 : ℕ) : ℝ) * (k : ℝ)) / Real.log Y *
        Task308.roughIndicator k p : ℝ) : ℂ) * χ (k : ZMod q) := by
  have h : (((p1 * p2 : ℕ) : ℝ) * (k : ℝ)) = ((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ) := by
    push_cast
    ring
  rw [h]

/-- The lower floor of the pair window is at least one, so the cofactor interval of a `j` fibre
starts above zero. -/
private lemma pair_floor_ge_one {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    {p1 p2 : ℕ} (hp1 : p1.Prime) (hp2 : p2.Prime) (hlt : p2 < p1) :
    1 ≤ ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ := by
  have hc4 : 0 < upperC4 ε := upperC4_pos hε8
  have hc4hi : upperC4 ε ≤ 133 / 500 := upperC4_le_133_500 hε hε8
  have hexp : (2 : ℝ) ≤ 1 / upperC4 ε := by
    rw [le_div_iff₀ hc4]
    nlinarith
  have hp1R : (1 : ℝ) ≤ (p1 : ℝ) := by
    exact_mod_cast (le_trans (by norm_num) hp1.two_le)
  have hp1pos : (0 : ℝ) < (p1 : ℝ) := by linarith
  have hp2R : (0 : ℝ) < (p2 : ℝ) := by
    exact_mod_cast hp2.pos
  have hp2lt : (p2 : ℝ) ≤ (p1 : ℝ) := by
    exact_mod_cast le_of_lt hlt
  have hsq : (p1 : ℝ) ^ (2 : ℝ) ≤ (p1 : ℝ) ^ (1 / upperC4 ε) :=
    Real.rpow_le_rpow_of_exponent_le hp1R hexp
  have h2 : ((p1 : ℝ) ^ (2 : ℝ)) = (p1 : ℝ) * (p1 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hdR : (0 : ℝ) < (p1 : ℝ) * (p2 : ℝ) := by positivity
  have hge : (p1 : ℝ) * (p2 : ℝ) ≤ (p1 : ℝ) ^ (1 / upperC4 ε) := by
    rw [h2] at hsq
    calc (p1 : ℝ) * (p2 : ℝ) ≤ (p1 : ℝ) * (p1 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hp2lt hp1pos.le
      _ ≤ (p1 : ℝ) ^ (1 / upperC4 ε) := hsq
  have hx : (1 : ℝ) ≤ (p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ)) := by
    rw [le_div_iff₀ hdR, one_mul]
    exact hge
  have hx' : ((1 : ℕ) : ℝ) ≤ (p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ)) := by
    push_cast
    exact hx
  exact (Nat.le_floor_iff (by positivity)).mpr hx'

/-- The `j` fibre over one pair of primes: after the ladder decomposition of the cofactor's rough
indicator, the Abel bound applies to the fixed level part and to each prime fibre at the fixed level
of its own prime. -/
private lemma j_pair_le {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {Y : ℝ} {K p1 p2 a b z Pmax : ℕ} {C0 A : ℝ}
    (hp1 : p1.Prime) (hp2 : p2.Prime) (hlt : p2 < p1)
    (hab : a ≤ b) (hdbK : p1 * p2 * b ≤ K)
    (hwlo : ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ ≤ a)
    (hY2 : 2 ≤ Y) (hKY : (K : ℝ) ≤ 2 * Y) (hz1 : 1 ≤ z)
    (hzX : (2 * Y) ^ (upperC1 ε / 2) ≤ (z : ℝ))
    (hS2 : ∀ n ∈ Finset.Ioc a b, 2 ≤ n)
    (hzS : ∀ n ∈ Finset.Ioc a b, z ≤ ⌈((p1 : ℝ) * (p2 : ℝ) * (n : ℝ)) ^ upperC1 ε⌉₊)
    (hPS : ∀ n ∈ Finset.Ioc a b, ⌈((p1 : ℝ) * (p2 : ℝ) * (n : ℝ)) ^ upperC1 ε⌉₊ ≤ Pmax)
    (hC0 : 0 ≤ C0)
    (hpre : ∀ (ζ a' b' : ℕ), (2 * Y) ^ (upperC1 ε / 2) ≤ (ζ : ℝ) → 1 ≤ a' → (b' : ℝ) ≤ 2 * Y →
      ‖∑ n ∈ Finset.Ioc a' b', ((Task308.roughIndicator n ζ : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
        C0 * (b' : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) :
    ‖∑ k ∈ Finset.Ioc a b,
        ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
          upperRough k ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) *
          χ (k : ZMod q)‖ ≤
      4 * (C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) +
        ∑ p ∈ Finset.Ico z Pmax,
          4 * (C0 * ((b / p : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) := by
  have hlogX : 0 < Real.log (2 * Y) := Real.log_pos (by linarith)
  have ha1 : 1 ≤ a := le_trans (pair_floor_ge_one hε hε8 hp1 hp2 hlt) hwlo
  have hd : 1 ≤ p1 * p2 := by
    have h : 2 * 2 ≤ p1 * p2 := Nat.mul_le_mul hp1.two_le hp2.two_le
    omega
  have hcast : ∀ n : ℕ,
      (((p1 * p2 : ℕ) : ℝ) * (n : ℝ)) = ((p1 : ℝ) * (p2 : ℝ)) * (n : ℝ) := by
    intro n
    push_cast
    ring
  -- collect the prime pair into a single multiplier
  have hnorm : ‖∑ k ∈ Finset.Ioc a b,
        ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
          upperRough k ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) *
          χ (k : ZMod q)‖
      = ‖∑ k ∈ Finset.Ioc a b,
        ((Real.log (((p1 * p2 : ℕ) : ℝ) * (k : ℝ)) / Real.log Y *
          upperRough k ((((p1 * p2 : ℕ) : ℝ) * (k : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) *
          χ (k : ZMod q)‖ := by
    rw [Finset.sum_congr rfl fun k _ => j_cast_term p1 p2 k χ (Y := Y)]
  rw [hnorm]
  have hAB := ladder_identity_general (ε := ε) (Y := Y) (d := p1 * p2) (Pmax := Pmax)
    (z := z) (S := Finset.Ioc a b) χ (fun n hn => hS2 n hn)
    (fun n hn => by rw [hcast n]; exact hzS n hn)
    (fun n hn => by rw [hcast n]; exact hPS n hn)
  rw [hAB]
  refine le_trans (norm_sub_le _ _) ?_
  refine add_le_add ?_ ?_
  · exact interval_A_le (d := p1 * p2) hε hε8 χ hd hY2 hKY hz1 hab ha1 hdbK hC0
      (fun a' b' ha' hb' => hpre z a' b' hzX ha' hb')
  · refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun p hpI => ?_
    have hzp : z ≤ p := (Finset.mem_Ico.mp hpI).1
    have hconv : (∑ k ∈ Finset.Ioc a b,
          (if p.Prime ∧ (p : ℝ) < (((p1 * p2 : ℕ) : ℝ) * (k : ℝ)) ^ upperC1 ε ∧ p ∣ k then
            ((Real.log (((p1 * p2 : ℕ) : ℝ) * (k : ℝ)) / Real.log Y *
              Task308.roughIndicator k p : ℝ) : ℂ) * χ (k : ZMod q) else 0))
        = (∑ k ∈ Finset.Ioc a b,
          (if p.Prime ∧ (p : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ∧ p ∣ k then
            ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
              Task308.roughIndicator k p : ℝ) : ℂ) * χ (k : ZMod q) else 0)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hiff : (p.Prime ∧ (p : ℝ) < (((p1 * p2 : ℕ) : ℝ) * (k : ℝ)) ^ upperC1 ε ∧ p ∣ k) ↔
          (p.Prime ∧ (p : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ∧ p ∣ k) := by
        rw [hcast k]
      have hterm : ((Real.log (((p1 * p2 : ℕ) : ℝ) * (k : ℝ)) / Real.log Y *
            Task308.roughIndicator k p : ℝ) : ℂ) * χ (k : ZMod q)
          = ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
            Task308.roughIndicator k p : ℝ) : ℂ) * χ (k : ZMod q) := by
        rw [hcast k]
      by_cases hc : (p.Prime ∧ (p : ℝ) < (((p1 * p2 : ℕ) : ℝ) * (k : ℝ)) ^ upperC1 ε ∧ p ∣ k)
      · rw [if_pos hc, if_pos (hiff.mp hc), hterm]
      · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]
    rw [hconv]
    by_cases hpp : p.Prime
    · exact interval_B_le (p := p) (z := z) hε hε8 χ hp1 hp2 hlt hpp hzp hY2 hKY hzX hdbK hab
        hwlo hC0 hpre
    · have hzero : (∑ k ∈ Finset.Ioc a b,
          (if p.Prime ∧ (p : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ∧ p ∣ k then
            ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
              Task308.roughIndicator k p : ℝ) : ℂ) * χ (k : ZMod q) else 0)) = 0 :=
        Finset.sum_eq_zero fun k _ => if_neg (fun h => hpp h.1)
      rw [hzero, norm_zero]
      exact mul_nonneg (by norm_num)
        (mul_nonneg (mul_nonneg hC0 (by positivity)) (Real.rpow_nonneg hlogX.le _))

/-- The double reciprocal sum over a decreasing pair of primes costs two logarithms. -/
private lemma pair_inv_sum_le (K : ℕ) :
    ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
      (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
        (if (p2 : ℝ) < (p1 : ℝ) then ((K / p1 / p2 : ℕ) : ℝ) else 0))
      ≤ (K : ℝ) * (1 + Real.log (K : ℝ)) ^ 2 := by
  have hlogK : (0 : ℝ) ≤ Real.log (K : ℝ) := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0]; simp
    · exact Real.log_nonneg (by exact_mod_cast hpos)
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := by positivity
  -- the inner sum over the second prime
  have hinner : ∀ p1 : ℕ,
      (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
        (if (p2 : ℝ) < (p1 : ℝ) then ((K / p1 / p2 : ℕ) : ℝ) else 0))
      ≤ ((K : ℝ) / (p1 : ℝ)) * (1 + Real.log (K : ℝ)) := by
    intro p1
    have h1 : (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
        (if (p2 : ℝ) < (p1 : ℝ) then ((K / p1 / p2 : ℕ) : ℝ) else 0))
        ≤ ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime, ((K / p1 / p2 : ℕ) : ℝ) := by
      refine Finset.sum_le_sum fun p2 _ => ?_
      by_cases hc : (p2 : ℝ) < (p1 : ℝ)
      · rw [if_pos hc]
      · rw [if_neg hc]
        exact Nat.cast_nonneg _
    have h2 : (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime, ((K / p1 / p2 : ℕ) : ℝ))
        ≤ ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
            ((K : ℝ) / (p1 : ℝ)) / (p2 : ℝ) := by
      refine Finset.sum_le_sum fun p2 _ => ?_
      exact le_trans (Nat.cast_div_le (α := ℝ) (m := K / p1) (n := p2))
        (div_le_div_of_nonneg_right (Nat.cast_div_le (α := ℝ) (m := K) (n := p1)) (by positivity))
    have h3 : (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
        ((K : ℝ) / (p1 : ℝ)) / (p2 : ℝ))
        = ((K : ℝ) / (p1 : ℝ)) *
            ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime, (1 : ℝ) / (p2 : ℝ) := by
      rw [Finset.mul_sum]
      try refine Finset.sum_congr rfl fun p2 _ => by ring
    have h4 : (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime, (1 : ℝ) / (p2 : ℝ))
        ≤ 1 + Real.log (K : ℝ) := by
      have hsub : (Finset.Icc 2 (K / p1)).filter Nat.Prime ⊆ (Finset.Icc 2 K).filter Nat.Prime := by
        intro p hp
        obtain ⟨hpI, hpP⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp2, hpk⟩ := Finset.mem_Icc.mp hpI
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨hp2, le_trans hpk (Nat.div_le_self K p1)⟩, hpP⟩
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) ?_
      exact prime_inv_sum_le K
    calc (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
          (if (p2 : ℝ) < (p1 : ℝ) then ((K / p1 / p2 : ℕ) : ℝ) else 0))
        ≤ ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime, ((K / p1 / p2 : ℕ) : ℝ) := h1
      _ ≤ ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
            ((K : ℝ) / (p1 : ℝ)) / (p2 : ℝ) := h2
      _ = ((K : ℝ) / (p1 : ℝ)) *
            ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime, (1 : ℝ) / (p2 : ℝ) := h3
      _ ≤ ((K : ℝ) / (p1 : ℝ)) * (1 + Real.log (K : ℝ)) := by
          refine mul_le_mul_of_nonneg_left h4 ?_
          positivity
  -- the outer sum
  refine le_trans (Finset.sum_le_sum fun p1 _ => hinner p1) ?_
  have h5 : (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
      ((K : ℝ) / (p1 : ℝ)) * (1 + Real.log (K : ℝ)))
      ≤ (K : ℝ) * (1 + Real.log (K : ℝ)) * (1 + Real.log (K : ℝ)) := by
    have h6 : (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, ((K : ℝ) / (p1 : ℝ)))
        = (K : ℝ) * ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, (1 : ℝ) / (p1 : ℝ) := by
      rw [Finset.mul_sum]
      try refine Finset.sum_congr rfl fun p1 _ => by ring
    have h7 : (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, (1 : ℝ) / (p1 : ℝ))
        ≤ 1 + Real.log (K : ℝ) := prime_inv_sum_le K
    calc (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
        ((K : ℝ) / (p1 : ℝ)) * (1 + Real.log (K : ℝ)))
        = (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, ((K : ℝ) / (p1 : ℝ))) *
            (1 + Real.log (K : ℝ)) := by
          rw [Finset.sum_mul]
      _ = (K : ℝ) * (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, (1 : ℝ) / (p1 : ℝ)) *
            (1 + Real.log (K : ℝ)) := by rw [h6]
      _ ≤ (K : ℝ) * (1 + Real.log (K : ℝ)) * (1 + Real.log (K : ℝ)) := by
          have h8 : (0 : ℝ) ≤ (K : ℝ) := hK0
          have h9 : (0 : ℝ) ≤ 1 + Real.log (K : ℝ) := by linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h7 h8) h9
  calc (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
        ((K : ℝ) / (p1 : ℝ)) * (1 + Real.log (K : ℝ)))
      ≤ (K : ℝ) * (1 + Real.log (K : ℝ)) * (1 + Real.log (K : ℝ)) := h5
    _ = (K : ℝ) * (1 + Real.log (K : ℝ)) ^ 2 := by ring


set_option maxHeartbeats 20000000 in
/-- The `j` term of the self scaled upper coefficient at a fixed scale: after the two prime peels the
index runs over the cofactor with two fixed prime multipliers, the ladder decomposition at the
product level splits each fibre, and the two reciprocal sums over the pair of primes cost two
logarithms. -/
private lemma upperJ_self_bound {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, C ≤ Y → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log Y ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ L K : ℕ, 1 ≤ L → (L : ℝ) ≤ Y → ⌊Y⌋₊ ≤ L → (K : ℝ) ≤ 2 * Y →
        ‖∑ m ∈ Finset.Ioc L K,
          ((Real.log (m : ℝ) / Real.log Y * upperJ ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
          C * Y * Real.log Y ^ (-A) := by
  intro A hA
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Rough514.rough_character_interval (c := upperC1 ε / 2) (A := A + 6)
      (by linarith [upperC1_pos hε8]) (by linarith)
  refine ⟨max (288 * C0) 4, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) (le_max_right _ _)
  intro Y hY q hq hqA χ hχ L K hL hLY hLf hKY
  have hCl : (max (288 * C0) 4 : ℝ) ≤ Y := hY
  have hC4 : (4 : ℝ) ≤ Y := le_trans (le_max_right _ _) hCl
  have hY2 : 2 ≤ Y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hC0Y : C0 ≤ 2 * Y := by
    have h1 : (0 : ℝ) ≤ C0 := hC0pos.le
    have h2 : C0 ≤ 288 * C0 := by nlinarith
    have h3 : 288 * C0 ≤ max (288 * C0) 4 := le_max_left _ _
    linarith
  have hlogY1 : (1 : ℝ) ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le hY0]
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hc1 : 0 < upperC1 ε := upperC1_pos hε8
  have hc1le : upperC1 ε ≤ 1 := upperC1_le_one hε
  have hX : (2 * Y) ^ (upperC1 ε / 2) ≤ Y ^ upperC1 ε := level_ge hc1 hY2
  set z : ℕ := ⌈(2 * Y) ^ (upperC1 ε / 2)⌉₊ with hzdef
  set Pmax : ℕ := ⌈(K : ℝ) ^ upperC1 ε⌉₊ with hPdef
  have hzX : (2 * Y) ^ (upperC1 ε / 2) ≤ (z : ℝ) := Nat.le_ceil _
  have hz1 : 1 ≤ z := by
    have h1 : (1 : ℝ) ≤ (2 * Y) ^ (upperC1 ε / 2) := by
      have h2 : (1 : ℝ) ≤ 2 * Y := by linarith
      calc (1 : ℝ) = (1 : ℝ) ^ (upperC1 ε / 2) := (Real.one_rpow _).symm
        _ ≤ (2 * Y) ^ (upperC1 ε / 2) := Real.rpow_le_rpow (by norm_num) h2 (by positivity)
    have h2 : (1 : ℝ) ≤ (z : ℝ) := by
      rw [hzdef]
      exact le_trans h1 (Nat.le_ceil _)
    exact_mod_cast h2
  have hlogX : 0 < Real.log (2 * Y) := Real.log_pos (by linarith)
  have hqA' : (q : ℝ) ≤ Real.log (2 * Y) ^ (A + 6) := by
    have h1 : Real.log Y ≤ Real.log (2 * Y) := Real.log_le_log hY0 (by linarith)
    have h3 : Real.log Y ^ A ≤ Real.log (2 * Y) ^ (A + 6) := by
      have h4 : Real.log Y ^ A ≤ Real.log (2 * Y) ^ A :=
        Real.rpow_le_rpow hlogY.le h1 hA.le
      have h5 : Real.log (2 * Y) ^ A ≤ Real.log (2 * Y) ^ (A + 6) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      linarith
    linarith
  have hpre : ∀ (ζ a b : ℕ), (2 * Y) ^ (upperC1 ε / 2) ≤ (ζ : ℝ) → 1 ≤ a → (b : ℝ) ≤ 2 * Y →
      ‖∑ n ∈ Finset.Ioc a b, ((Task308.roughIndicator n ζ : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
        C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6)) := by
    intro ζ a b hζ ha hb
    exact hC0 (2 * Y) hC0Y q hq hqA' χ hχ ζ hζ a b ha hb
  -- the three logarithms that the two reciprocal sums cost
  have hlogK0 : (0 : ℝ) ≤ Real.log (K : ℝ) := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0]; simp
    · exact Real.log_nonneg (by exact_mod_cast hpos)
  have hlogK : Real.log (K : ℝ) ≤ 2 * Real.log Y := by
    have h1 : Real.log (K : ℝ) ≤ Real.log (2 * Y) := by
      rcases Nat.eq_zero_or_pos K with h0 | hpos
      · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith
      · exact Real.log_le_log (by exact_mod_cast hpos) hKY
    have h2 : Real.log (2 * Y) ≤ 2 * Real.log Y := by
      rw [Real.log_mul (by norm_num) hY0.ne']
      have h3 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY2
      linarith
    linarith
  have hlogP0 : (0 : ℝ) ≤ Real.log (Pmax : ℝ) := by
    rcases Nat.eq_zero_or_pos Pmax with h0 | hpos
    · rw [h0]; simp
    · exact Real.log_nonneg (by exact_mod_cast hpos)
  have hlogP : Real.log (Pmax : ℝ) ≤ 2 * Real.log Y := by
    have hKc1 : (K : ℝ) ^ upperC1 ε ≤ (K : ℝ) := by
      rcases Nat.lt_or_ge K 2 with h | h
      · interval_cases K
        · rw [Nat.cast_zero, Real.zero_rpow hc1.ne']
        · rw [Nat.cast_one, Real.one_rpow]
      · have h2 : (1 : ℝ) ≤ (K : ℝ) := by
          exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 2) h)
        calc (K : ℝ) ^ upperC1 ε ≤ (K : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h2 hc1le
          _ = (K : ℝ) := Real.rpow_one _
    have h1 : (Pmax : ℝ) ≤ (K : ℝ) := by
      rw [hPdef]
      have h2 : ⌈(K : ℝ) ^ upperC1 ε⌉₊ ≤ K := Nat.ceil_le.mpr hKc1
      exact_mod_cast h2
    rcases Nat.eq_zero_or_pos Pmax with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith
    · exact le_trans (Real.log_le_log (by exact_mod_cast hpos) h1) hlogK
  rw [upperJ_weighted_reindex (Y := Y) χ]
  refine le_trans (norm_sum_le _ _) ?_
  have hinner : ∀ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
      ‖χ (p1 : ZMod q) *
        ∑ n ∈ Finset.Ioc (L / p1) (K / p1),
          (if (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) then
            ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
              (∑ p2 ∈ n.primeFactors.filter
                (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                  (p2 : ℝ) < (p1 : ℝ)),
                upperRough (n / p2) (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε)) : ℝ) : ℂ) *
              χ (n : ZMod q)
          else 0)‖ ≤
      4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * (2 + Real.log (Pmax : ℝ)) *
        ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
          (if (p2 : ℝ) < (p1 : ℝ) then ((K / p1 / p2 : ℕ) : ℝ) else 0) := by
    intro p1 hp1mem
    obtain ⟨hp1K, hp1P⟩ := Finset.mem_filter.mp hp1mem
    have hp1 : p1.Prime := hp1P
    have hp1one : 1 ≤ p1 := le_trans (by norm_num) hp1.two_le
    refine le_trans (norm_mul_le _ _) ?_
    refine le_trans (mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ (p1 : ZMod q))
      (norm_nonneg _)) ?_
    rw [one_mul]
    rw [upperJ_inner_peel (Y := Y) (L' := L / p1) (K' := K / p1) χ hp1one]
    refine le_trans (norm_sum_le _ _) ?_
    have hstep : (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
        4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * (2 + Real.log (Pmax : ℝ)) *
          (if (p2 : ℝ) < (p1 : ℝ) then ((K / p1 / p2 : ℕ) : ℝ) else 0))
        = 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * (2 + Real.log (Pmax : ℝ)) *
          ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
            (if (p2 : ℝ) < (p1 : ℝ) then ((K / p1 / p2 : ℕ) : ℝ) else 0) := by
      rw [Finset.mul_sum]

    have hper : ∀ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
        ‖if (p2 : ℝ) < (p1 : ℝ) then
            χ (p2 : ZMod q) *
              ∑ k ∈ Finset.Ioc ((L / p1) / p2) ((K / p1) / p2),
                (if ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                    (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
                    (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ))
                  then ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
                    upperRough k ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) *
                    χ (k : ZMod q)
                  else 0)
            else 0‖ ≤
          4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * (2 + Real.log (Pmax : ℝ)) *
            (if (p2 : ℝ) < (p1 : ℝ) then ((K / p1 / p2 : ℕ) : ℝ) else 0) := by
      intro p2 hp2
      by_cases hlt : (p2 : ℝ) < (p1 : ℝ)
      · have hp2P : p2.Prime := (Finset.mem_filter.mp hp2).2
        have hltn : p2 < p1 := by exact_mod_cast hlt
        have hp2one : 1 ≤ p2 := le_trans (by norm_num) hp2P.two_le
        rw [if_pos hlt, if_pos hlt]
        refine le_trans (norm_mul_le _ _) ?_
        refine le_trans (mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ (p2 : ZMod q))
          (norm_nonneg _)) ?_
        rw [one_mul]
        -- the cofactor interval of the pair window
        have hS : (∑ k ∈ Finset.Ioc ((L / p1) / p2) ((K / p1) / p2),
              (if ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                  (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
                  (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ)) then
                ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
                  upperRough k ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) *
                  χ (k : ZMod q)
                else 0))
            = ∑ k ∈ Finset.Ioc
                (max ((L / p1) / p2) ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊)
                (min ((K / p1) / p2) ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊),
                ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
                  upperRough k ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) *
                  χ (k : ZMod q) := by
          rw [← Finset.sum_filter]
          rw [filter_window_pair_eq_Ioc hε8 hp1one hp2one (le_of_lt hltn)]
        rw [hS]
        by_cases hab : max ((L / p1) / p2)
            ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ ≤
          min ((K / p1) / p2) ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊
        · -- the pair fibre
          have hbK : p1 * p2 *
              (min ((K / p1) / p2) ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊) ≤ K := by
            have h1 : min ((K / p1) / p2)
                ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ ≤ (K / p1) / p2 :=
              min_le_left _ _
            have h2 : p2 * ((K / p1) / p2) ≤ K / p1 := Nat.mul_div_le _ _
            have h3 : p1 * (p2 * ((K / p1) / p2)) ≤ p1 * (K / p1) := Nat.mul_le_mul_left _ h2
            have h4 : p1 * (K / p1) ≤ K := Nat.mul_div_le _ _
            calc p1 * p2 * (min ((K / p1) / p2)
                  ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊)
                ≤ p1 * p2 * ((K / p1) / p2) := Nat.mul_le_mul_left _ h1
              _ = p1 * (p2 * ((K / p1) / p2)) := by ring
              _ ≤ K := le_trans h3 h4
          have hS2 : ∀ n ∈ Finset.Ioc
              (max ((L / p1) / p2) ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊)
              (min ((K / p1) / p2) ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊), 2 ≤ n := by
            intro n hn
            have h1 : max ((L / p1) / p2)
                ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ < n :=
              (Finset.mem_Ioc.mp hn).1
            have h2 : 1 ≤ ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ :=
              pair_floor_ge_one hε hε8 hp1 hp2P hltn
            have h3 : 1 ≤ max ((L / p1) / p2)
                ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ := le_trans h2 (le_max_right _ _)
            omega
          have hmY : ∀ n ∈ Finset.Ioc
              (max ((L / p1) / p2) ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊)
              (min ((K / p1) / p2) ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊),
              (Y : ℝ) ≤ ((p1 : ℝ) * (p2 : ℝ)) * (n : ℝ) := by
            intro n hn
            have h1 : (L / p1) / p2 < n := lt_of_le_of_lt (le_max_left _ _) (Finset.mem_Ioc.mp hn).1
            have h2 : L / p1 < p2 * n := by
              have h3 : (L / p1) / p2 + 1 ≤ n := by omega
              have h4 : p2 * ((L / p1) / p2 + 1) ≤ p2 * n := Nat.mul_le_mul_left _ h3
              have h5 : L / p1 < p2 * ((L / p1) / p2 + 1) := by
                have h6 : p2 * ((L / p1) / p2) + (L / p1) % p2 = L / p1 :=
                  Nat.div_add_mod _ _
                have h7 : (L / p1) % p2 < p2 := Nat.mod_lt _ hp2P.pos
                have h8 : p2 * ((L / p1) / p2 + 1) = p2 * ((L / p1) / p2) + p2 := by ring
                omega
              omega
            have h6 : L < p1 * (p2 * n) := by
              have h7 : L / p1 + 1 ≤ p2 * n := by omega
              have h8 : p1 * (L / p1 + 1) ≤ p1 * (p2 * n) := Nat.mul_le_mul_left _ h7
              have h9 : p1 * (L / p1) + L % p1 = L := Nat.div_add_mod _ _
              have h10 : L % p1 < p1 := Nat.mod_lt _ hp1.pos
              have h9' : p1 * (L / p1 + 1) = p1 * (L / p1) + p1 := by ring
              omega
            have h11 : (L : ℝ) + 1 ≤ ((p1 * (p2 * n) : ℕ) : ℝ) := by
              have h12 : L + 1 ≤ p1 * (p2 * n) := by omega
              exact_mod_cast h12
            push_cast at h11
            have h13 : (Y : ℝ) < (L : ℝ) + 1 := by
              have h14 : (⌊Y⌋₊ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLf
              have h15 : Y < (⌊Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Y
              linarith
            linarith
          have hzSn : ∀ n ∈ Finset.Ioc
              (max ((L / p1) / p2) ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊)
              (min ((K / p1) / p2) ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊),
              z ≤ ⌈((p1 : ℝ) * (p2 : ℝ) * (n : ℝ)) ^ upperC1 ε⌉₊ := by
            intro n hn
            rw [hzdef]
            have h1 : (Y : ℝ) ^ upperC1 ε ≤ ((p1 : ℝ) * (p2 : ℝ) * (n : ℝ)) ^ upperC1 ε :=
              Real.rpow_le_rpow hY0.le (hmY n hn) hc1.le
            exact Nat.ceil_le.mpr (le_trans (le_trans hX h1) (Nat.le_ceil _))
          have hPSn : ∀ n ∈ Finset.Ioc
              (max ((L / p1) / p2) ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊)
              (min ((K / p1) / p2) ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊),
              ⌈((p1 : ℝ) * (p2 : ℝ) * (n : ℝ)) ^ upperC1 ε⌉₊ ≤ Pmax := by
            intro n hn
            rw [hPdef]
            have h1 : ((p1 : ℝ) * (p2 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (K : ℝ) ^ upperC1 ε := by
              refine Real.rpow_le_rpow (by positivity) ?_ hc1.le
              have h2 : p1 * (p2 * n) ≤ K := by
                have h3 : n ≤ min ((K / p1) / p2)
                    ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ :=
                  (Finset.mem_Ioc.mp hn).2
                have h4 : n ≤ (K / p1) / p2 := le_trans h3 (min_le_left _ _)
                have h5 : p2 * n ≤ K / p1 := by
                  have h6 : p2 * n ≤ p2 * ((K / p1) / p2) := Nat.mul_le_mul_left _ h4
                  exact le_trans h6 (Nat.mul_div_le _ _)
                exact le_trans (Nat.mul_le_mul_left _ h5) (Nat.mul_div_le _ _)
              have h7 : ((p1 * (p2 * n) : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast h2
              have h7' : (p1 : ℝ) * (p2 : ℝ) * (n : ℝ) ≤ (K : ℝ) := by
                have h8 : ((p1 * (p2 * n) : ℕ) : ℝ) = (p1 : ℝ) * (p2 : ℝ) * (n : ℝ) := by
                  push_cast
                  ring
                rw [h8] at h7
                exact h7
              exact h7'
            exact Nat.ceil_le.mpr (le_trans h1 (Nat.le_ceil _))
          have hbnd := j_pair_le (p1 := p1) (p2 := p2) (K := K) (a := max ((L / p1) / p2)
              ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊)
            (b := min ((K / p1) / p2) ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊)
            (z := z) (Pmax := Pmax) (C0 := C0) (A := A) hε hε8 χ hp1 hp2P hltn hab hbK
            (le_max_right _ _) hY2 hKY hz1 hzX hS2 hzSn hPSn hC0pos.le hpre
          -- the constant bookkeeping of the pair
          have hb1 : ((min ((K / p1) / p2)
              ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ : ℕ) : ℝ) ≤
              ((K / p1 / p2 : ℕ) : ℝ) := by
            exact_mod_cast min_le_left _ _
          have hfib : (∑ p ∈ Finset.Ico z Pmax,
              ((min ((K / p1) / p2)
                ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ / p : ℕ) : ℝ))
              ≤ ((K / p1 / p2 : ℕ) : ℝ) * (1 + Real.log (Pmax : ℝ)) := by
            have h2 : ∑ p ∈ Finset.Ico z Pmax,
                ((min ((K / p1) / p2)
                  ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ / p : ℕ) : ℝ) ≤
                ∑ p ∈ Finset.Ico z Pmax, ((K / p1 / p2 : ℕ) : ℝ) / (p : ℝ) := by
              refine Finset.sum_le_sum fun p _ => ?_
              refine le_trans (Nat.cast_div_le (α := ℝ)
                (m := min ((K / p1) / p2)
                  ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊) (n := p)) ?_
              exact div_le_div_of_nonneg_right hb1 (by positivity)
            have h3 : ∑ p ∈ Finset.Ico z Pmax, ((K / p1 / p2 : ℕ) : ℝ) / (p : ℝ) =
                ((K / p1 / p2 : ℕ) : ℝ) * ∑ p ∈ Finset.Ico z Pmax, (1 : ℝ) / (p : ℝ) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun p _ => by ring
            have h4 : ∑ p ∈ Finset.Ico z Pmax, (1 : ℝ) / (p : ℝ) ≤ 1 + Real.log (Pmax : ℝ) := by
              have hsub : Finset.Ico z Pmax ⊆ Finset.Icc 1 Pmax := by
                intro p hp
                obtain ⟨hzp, hpP⟩ := Finset.mem_Ico.mp hp
                exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
              refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
                (fun _ _ _ => by positivity)) ?_
              have hh := harmonic_le_one_add_log Pmax
              rw [harmonic_eq_sum_Icc] at hh
              push_cast at hh
              simpa [one_div] using hh
            calc ∑ p ∈ Finset.Ico z Pmax,
                ((min ((K / p1) / p2)
                  ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ / p : ℕ) : ℝ)
                ≤ ∑ p ∈ Finset.Ico z Pmax, ((K / p1 / p2 : ℕ) : ℝ) / (p : ℝ) := h2
              _ = ((K / p1 / p2 : ℕ) : ℝ) * ∑ p ∈ Finset.Ico z Pmax, (1 : ℝ) / (p : ℝ) := h3
              _ ≤ ((K / p1 / p2 : ℕ) : ℝ) * (1 + Real.log (Pmax : ℝ)) :=
                  mul_le_mul_of_nonneg_left h4 (by positivity)
          have hL6 : (0 : ℝ) ≤ Real.log (2 * Y) ^ (-(A + 6)) := Real.rpow_nonneg hlogX.le _
          have hk0 : (0 : ℝ) ≤ ((K / p1 / p2 : ℕ) : ℝ) := by positivity
          have hlogP0 : (0 : ℝ) ≤ Real.log (Pmax : ℝ) := by
            rcases Nat.eq_zero_or_pos Pmax with h0 | hpos
            · rw [h0]; simp
            · exact Real.log_nonneg (by exact_mod_cast hpos)
          calc ‖∑ k ∈ Finset.Ioc
                (max ((L / p1) / p2) ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊)
                (min ((K / p1) / p2) ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊),
                ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
                  upperRough k ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε) : ℝ) : ℂ) *
                  χ (k : ZMod q)‖
              ≤ 4 * (C0 * ((min ((K / p1) / p2)
                    ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ : ℕ) : ℝ) *
                    Real.log (2 * Y) ^ (-(A + 6))) +
                  ∑ p ∈ Finset.Ico z Pmax,
                    4 * (C0 * ((min ((K / p1) / p2)
                      ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ / p : ℕ) : ℝ) *
                      Real.log (2 * Y) ^ (-(A + 6))) := hbnd
            _ ≤ 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * (2 + Real.log (Pmax : ℝ)) *
                  ((K / p1 / p2 : ℕ) : ℝ) := by
                have h1 : 4 * (C0 * ((min ((K / p1) / p2)
                      ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ : ℕ) : ℝ) *
                      Real.log (2 * Y) ^ (-(A + 6))) ≤
                    4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * ((K / p1 / p2 : ℕ) : ℝ) := by
                  have h2 : C0 * ((min ((K / p1) / p2)
                        ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ : ℕ) : ℝ) ≤
                      C0 * ((K / p1 / p2 : ℕ) : ℝ) :=
                    mul_le_mul_of_nonneg_left hb1 hC0pos.le
                  have h3 : C0 * ((min ((K / p1) / p2)
                        ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ : ℕ) : ℝ) *
                        Real.log (2 * Y) ^ (-(A + 6)) ≤
                      C0 * ((K / p1 / p2 : ℕ) : ℝ) * Real.log (2 * Y) ^ (-(A + 6)) :=
                    mul_le_mul_of_nonneg_right h2 hL6
                  linarith [h3]
                have h2 : (∑ p ∈ Finset.Ico z Pmax,
                    4 * (C0 * ((min ((K / p1) / p2)
                      ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ / p : ℕ) : ℝ) *
                      Real.log (2 * Y) ^ (-(A + 6)))) =
                    4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) *
                      ∑ p ∈ Finset.Ico z Pmax,
                        ((min ((K / p1) / p2)
                          ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ / p : ℕ) : ℝ) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun p _ => by ring
                have h3 : 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) *
                      ∑ p ∈ Finset.Ico z Pmax,
                        ((min ((K / p1) / p2)
                          ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ / p : ℕ) : ℝ)
                    ≤ 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * ((K / p1 / p2 : ℕ) : ℝ) *
                      (1 + Real.log (Pmax : ℝ)) := by
                  have h4 : (0 : ℝ) ≤ 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) := by positivity
                  calc 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) *
                        ∑ p ∈ Finset.Ico z Pmax,
                          ((min ((K / p1) / p2)
                            ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊ / p : ℕ) : ℝ)
                      ≤ 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) *
                          (((K / p1 / p2 : ℕ) : ℝ) * (1 + Real.log (Pmax : ℝ))) :=
                        mul_le_mul_of_nonneg_left hfib h4
                    _ = 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * ((K / p1 / p2 : ℕ) : ℝ) *
                          (1 + Real.log (Pmax : ℝ)) := by ring
                linarith [h1, h2, h3]
        · -- the pair window is empty
          have hemp : Finset.Ioc (max ((L / p1) / p2)
              ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊)
              (min ((K / p1) / p2) ⌊(p2 : ℝ) ^ (1 / upperC1 ε) / ((p1 : ℝ) * (p2 : ℝ))⌋₊) = ∅ :=
            Finset.Ioc_eq_empty_of_le (le_of_lt (not_le.mp hab))
          rw [hemp]
          simp only [Finset.sum_empty, norm_zero]
          have h1 : (0 : ℝ) ≤ 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) := by positivity
          have h2 : (0 : ℝ) ≤ 2 + Real.log (Pmax : ℝ) := by linarith
          exact mul_nonneg (mul_nonneg h1 h2) (by positivity)
      · rw [if_neg hlt, if_neg hlt, norm_zero]
        simp

    exact le_trans (Finset.sum_le_sum hper) (le_of_eq hstep)
  refine le_trans (Finset.sum_le_sum fun p1 hp1 => hinner p1 hp1) ?_
  have hpair := pair_inv_sum_le K
  have hstep2 : (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
      4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * (2 + Real.log (Pmax : ℝ)) *
        ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
          (if (p2 : ℝ) < (p1 : ℝ) then ((K / p1 / p2 : ℕ) : ℝ) else 0))
      = 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * (2 + Real.log (Pmax : ℝ)) *
        ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
            (if (p2 : ℝ) < (p1 : ℝ) then ((K / p1 / p2 : ℕ) : ℝ) else 0) := by
    rw [← Finset.mul_sum]
  rw [hstep2]
  -- the logarithm arithmetic
  have h1 : (2 + Real.log (Pmax : ℝ)) ≤ 4 * Real.log Y := by linarith
  have h2 : (1 + Real.log (K : ℝ)) ≤ 3 * Real.log Y := by linarith
  have hp2 : (0 : ℝ) ≤ 2 + Real.log (Pmax : ℝ) := by linarith
  have hp3 : (0 : ℝ) ≤ 1 + Real.log (K : ℝ) := by linarith
  have hsq : (1 + Real.log (K : ℝ)) ^ 2 ≤ (3 * Real.log Y) ^ 2 := by
    nlinarith [hp3, h2]
  have hprod : (2 + Real.log (Pmax : ℝ)) * ((K : ℝ) * (1 + Real.log (K : ℝ)) ^ 2) ≤
      (4 * Real.log Y) * ((2 * Y) * (3 * Real.log Y) ^ 2) := by
    refine mul_le_mul h1 (mul_le_mul hKY hsq (by positivity) (by linarith)) ?_ (by linarith)
    nlinarith [hp2, hp3]
  have hlogXge : Real.log Y ≤ Real.log (2 * Y) := Real.log_le_log hY0 (by linarith)
  have hLXle : Real.log (2 * Y) ^ (-(A + 6)) ≤ Real.log Y ^ (-(A + 6)) :=
    Real.rpow_le_rpow_of_nonpos hlogY hlogXge (by linarith)
  have hcube : Real.log Y * Real.log Y * Real.log Y = Real.log Y ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hcomb : Real.log Y ^ (-(A + 6)) * Real.log Y ^ (3 : ℝ) = Real.log Y ^ (-(A + 3)) := by
    rw [← Real.rpow_add hlogY]
    congr 1
    ring
  have hlA3 : Real.log Y ^ (-(A + 3)) ≤ Real.log Y ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hlogY1 (by linarith)
  have hL6 : (0 : ℝ) ≤ Real.log (2 * Y) ^ (-(A + 6)) := Real.rpow_nonneg hlogX.le _
  have hcube0 : (0 : ℝ) ≤ Real.log Y * Real.log Y * Real.log Y := by positivity
  have hpw : Real.log (2 * Y) ^ (-(A + 6)) * (Real.log Y * Real.log Y * Real.log Y) ≤
      Real.log Y ^ (-A) := by
    rw [hcube]
    calc Real.log (2 * Y) ^ (-(A + 6)) * Real.log Y ^ (3 : ℝ)
        ≤ Real.log Y ^ (-(A + 6)) * Real.log Y ^ (3 : ℝ) :=
          mul_le_mul_of_nonneg_right hLXle (by positivity)
      _ = Real.log Y ^ (-(A + 3)) := hcomb
      _ ≤ Real.log Y ^ (-A) := hlA3
  have hYnn : (0 : ℝ) ≤ Y := hY0.le
  have hlY : (0 : ℝ) ≤ Real.log Y ^ (-A) := Real.rpow_nonneg hlogY.le _
  have hl6nonneg : (0 : ℝ) ≤ 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) *
      (2 + Real.log (Pmax : ℝ)) := by
    have h3 : (0 : ℝ) ≤ 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) := by positivity
    exact mul_nonneg h3 hp2
  calc 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * (2 + Real.log (Pmax : ℝ)) *
        (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
            (if (p2 : ℝ) < (p1 : ℝ) then ((K / p1 / p2 : ℕ) : ℝ) else 0))
      ≤ 4 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * (2 + Real.log (Pmax : ℝ)) *
          ((K : ℝ) * (1 + Real.log (K : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hpair hl6nonneg
    _ = 4 * C0 * (Real.log (2 * Y) ^ (-(A + 6)) *
          ((2 + Real.log (Pmax : ℝ)) * ((K : ℝ) * (1 + Real.log (K : ℝ)) ^ 2))) := by ring
    _ ≤ 4 * C0 * (Real.log (2 * Y) ^ (-(A + 6)) *
          ((4 * Real.log Y) * ((2 * Y) * (3 * Real.log Y) ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hprod hL6
    _ = 4 * C0 * (72 * Y * (Real.log (2 * Y) ^ (-(A + 6)) *
          (Real.log Y * Real.log Y * Real.log Y))) := by ring
    _ ≤ 4 * C0 * (72 * Y * Real.log Y ^ (-A)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hpw (by positivity)
    _ = 288 * C0 * Y * Real.log Y ^ (-A) := by ring
    _ ≤ max (288 * C0) 4 * Y * Real.log Y ^ (-A) := by
        have h4 : 288 * C0 ≤ max (288 * C0) 4 := le_max_left _ _
        have h6 : (0 : ℝ) ≤ Y * Real.log Y ^ (-A) := mul_nonneg hYnn hlY
        calc 288 * C0 * Y * Real.log Y ^ (-A) = (288 * C0) * (Y * Real.log Y ^ (-A)) := by ring
          _ ≤ max (288 * C0) 4 * (Y * Real.log Y ^ (-A)) := mul_le_mul_of_nonneg_right h4 h6
          _ = max (288 * C0) 4 * Y * Real.log Y ^ (-A) := by ring


/-! ### The `kept` term: one fibre per triple of primes -/

/-- A term of the `kept` fibre with the prime triple collected into a single natural number. -/
private lemma kept_cast_term {ε : ℝ} (p1 p2 p3 j : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {Y : ℝ} {c : Prop} [Decidable c] :
    (if c then ((Real.log (((p1 : ℝ) * (p2 : ℝ) * (p3 : ℝ)) * (j : ℝ)) / Real.log Y *
        upperRough j (p3 : ℝ) : ℝ) : ℂ) * χ (j : ZMod q) else 0)
      = (if c then ((Real.log (((p1 * p2 * p3 : ℕ) : ℝ) * (j : ℝ)) / Real.log Y *
        upperRough j (p3 : ℝ) : ℝ) : ℂ) * χ (j : ZMod q) else 0) := by
  have h : (((p1 * p2 * p3 : ℕ) : ℝ) * (j : ℝ)) =
      ((p1 : ℝ) * (p2 : ℝ) * (p3 : ℝ)) * (j : ℝ) := by
    push_cast
    ring
  rw [h]

/-- The `kept` fibre over one triple of primes: the sifted level of the cofactor is the third prime
itself, so the Abel bound of the fixed level rough character sum applies directly, and the covering
indicator is bounded by one. -/
private lemma kept_triple_le {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {Y : ℝ} {K p1 p2 p3 a b : ℕ} {C0 A : ℝ}
    (hp1 : p1.Prime) (hp2 : p2.Prime) (hp3 : p3.Prime) (hlt : p3 < p2)
    (hab : a ≤ b) (ha1 : 1 ≤ a) (hdbK : p1 * p2 * p3 * b ≤ K)
    (hY2 : 2 ≤ Y) (hKY : (K : ℝ) ≤ 2 * Y)
    (hzX : (2 * Y) ^ (upperC1 ε / 2) ≤ (p3 : ℝ))
    (hC0 : 0 ≤ C0)
    (hpre : ∀ (ζ a' b' : ℕ), (2 * Y) ^ (upperC1 ε / 2) ≤ (ζ : ℝ) → 1 ≤ a' → (b' : ℝ) ≤ 2 * Y →
      ‖∑ n ∈ Finset.Ioc a' b', ((Task308.roughIndicator n ζ : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
        C0 * (b' : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) :
    ‖∑ j ∈ Finset.Ioc a b,
        (if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log Y)
            (Real.log (p2 : ℝ) / Real.log Y) (Real.log (p3 : ℝ) / Real.log Y) then
          ((Real.log (((p1 : ℝ) * (p2 : ℝ) * (p3 : ℝ)) * (j : ℝ)) / Real.log Y *
            upperRough j (p3 : ℝ) : ℝ) : ℂ) * χ (j : ZMod q)
          else 0)‖ ≤
      4 * (C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) := by
  have hp3pos : 1 ≤ p3 := le_trans (by norm_num) hp3.two_le
  have hd : 1 ≤ p1 * p2 * p3 := by
    have h : 2 * 2 * 2 ≤ p1 * p2 * p3 :=
      Nat.mul_le_mul (Nat.mul_le_mul hp1.two_le hp2.two_le) hp3.two_le
    omega
  -- the sifted indicator at the third prime is the lab's fixed level indicator
  have hR : ∀ j ∈ Finset.Ioc a b, upperRough j (p3 : ℝ) = Task308.roughIndicator j p3 := by
    intro j hj
    have hj2 : 2 ≤ j := by
      have h1 : a < j := (Finset.mem_Ioc.mp hj).1
      omega
    rw [upperRough_eq_roughIndicator_ceil hj2 (p3 : ℝ)]
    norm_num
  by_cases hc : upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log Y)
      (Real.log (p2 : ℝ) / Real.log Y) (Real.log (p3 : ℝ) / Real.log Y)
  · simp only [if_pos hc]
    have hstep : (∑ j ∈ Finset.Ioc a b,
        ((Real.log (((p1 : ℝ) * (p2 : ℝ) * (p3 : ℝ)) * (j : ℝ)) / Real.log Y *
          upperRough j (p3 : ℝ) : ℝ) : ℂ) * χ (j : ZMod q))
        = (∑ j ∈ Finset.Ioc a b,
        ((Real.log (((p1 * p2 * p3 : ℕ) : ℝ) * (j : ℝ)) / Real.log Y *
          upperRough j (p3 : ℝ) : ℝ) : ℂ) * χ (j : ZMod q)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have h1 : (((p1 * p2 * p3 : ℕ) : ℝ) * (j : ℝ)) =
          ((p1 : ℝ) * (p2 : ℝ) * (p3 : ℝ)) * (j : ℝ) := by
        push_cast
        ring
      rw [h1]
    rw [hstep]
    have hstep2 : (∑ j ∈ Finset.Ioc a b,
        ((Real.log (((p1 * p2 * p3 : ℕ) : ℝ) * (j : ℝ)) / Real.log Y *
          upperRough j (p3 : ℝ) : ℝ) : ℂ) * χ (j : ZMod q))
        = (∑ j ∈ Finset.Ioc a b,
        ((Real.log (((p1 * p2 * p3 : ℕ) : ℝ) * (j : ℝ)) / Real.log Y *
          Task308.roughIndicator j p3 : ℝ) : ℂ) * χ (j : ZMod q)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hR j hj]
    rw [hstep2]
    exact interval_A_le (d := p1 * p2 * p3) (z := p3) hε hε8 χ hd hY2 hKY hp3pos hab ha1
      hdbK hC0
      (fun a' b' ha' hb' => hpre p3 a' b' hzX ha' hb')
  · have hzero : (∑ j ∈ Finset.Ioc a b,
        (if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log Y)
            (Real.log (p2 : ℝ) / Real.log Y) (Real.log (p3 : ℝ) / Real.log Y) then
          ((Real.log (((p1 : ℝ) * (p2 : ℝ) * (p3 : ℝ)) * (j : ℝ)) / Real.log Y *
            upperRough j (p3 : ℝ) : ℝ) : ℂ) * χ (j : ZMod q)
          else 0)) = 0 :=
      Finset.sum_eq_zero fun j _ => if_neg hc
    rw [hzero, norm_zero]
    have hL6 : (0 : ℝ) ≤ Real.log (2 * Y) ^ (-(A + 6)) :=
      Real.rpow_nonneg (le_of_lt (Real.log_pos (by linarith))) (-(A + 6))
    exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hC0 (by positivity)) hL6)


/-- The page 53 window of one `kept` triple, read as an integer interval in the cofactor: the level
`(d k) ^ c1` against the third prime gives the upper end, and the middle test against the first prime
gives the lower end, the level test against the first prime being implied because `p3 ≤ p1`. -/
private lemma filter_window_general {ε : ℝ} (hε8 : ε ≤ 1 / 10 ^ 8) {d plo phi a b : ℕ}
    (hd : 1 ≤ d) (hphi : 1 ≤ phi) (hle : phi ≤ plo) :
    (Finset.Ioc a b).filter
        (fun k : ℕ => ((d : ℝ) * (k : ℝ)) ^ upperC1 ε ≤ (plo : ℝ) ∧
          (plo : ℝ) < ((d : ℝ) * (k : ℝ)) ^ upperC4 ε ∧
          ((d : ℝ) * (k : ℝ)) ^ upperC1 ε ≤ (phi : ℝ)) =
      Finset.Ioc (max a ⌊(plo : ℝ) ^ (1 / upperC4 ε) / (d : ℝ)⌋₊)
        (min b ⌊(phi : ℝ) ^ (1 / upperC1 ε) / (d : ℝ)⌋₊) := by
  have hc1 : 0 < upperC1 ε := upperC1_pos hε8
  have hc4 : 0 < upperC4 ε := upperC4_pos hε8
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hphiR : (0 : ℝ) < (phi : ℝ) := by exact_mod_cast (by omega : 0 < phi)
  have hpred : ∀ k : ℕ,
      (((d : ℝ) * (k : ℝ)) ^ upperC1 ε ≤ (plo : ℝ) ∧
          (plo : ℝ) < ((d : ℝ) * (k : ℝ)) ^ upperC4 ε ∧
          ((d : ℝ) * (k : ℝ)) ^ upperC1 ε ≤ (phi : ℝ)) ↔
        (k ≤ ⌊(phi : ℝ) ^ (1 / upperC1 ε) / (d : ℝ)⌋₊ ∧
          ⌊(plo : ℝ) ^ (1 / upperC4 ε) / (d : ℝ)⌋₊ < k) := by
    intro k
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      have hz : ((d : ℝ) * ((0 : ℕ) : ℝ)) = 0 := by
        rw [Nat.cast_zero, mul_zero]
      have hzc4 : ((d : ℝ) * ((0 : ℕ) : ℝ)) ^ upperC4 ε = 0 := by
        rw [hz, Real.zero_rpow hc4.ne']
      have hzc1 : ((d : ℝ) * ((0 : ℕ) : ℝ)) ^ upperC1 ε = 0 := by
        rw [hz, Real.zero_rpow hc1.ne']
      constructor
      · rintro ⟨-, h2, -⟩
        rw [hzc4] at h2
        exact absurd h2 (by linarith)
      · rintro ⟨-, h2⟩
        rw [hzc1] at *
        exact absurd h2 (by omega)
    · have hiff4 := peel_level_iff (c := upperC4 ε) hc4 (d := d) (p := plo) (n := k) hd hpos
      have hC : ((d : ℝ) * (k : ℝ)) ^ upperC1 ε ≤ (phi : ℝ) ↔
          k ≤ (phi : ℝ) ^ (1 / upperC1 ε) / (d : ℝ) := by
        have h1 := rpow_self_le_iff (cc := upperC1 ε) hc1
          (x := (d : ℝ) * (k : ℝ)) (p := (phi : ℝ)) (by positivity) (by positivity)
        rw [h1, le_div_iff₀ hdR]
        constructor <;> intro h <;> nlinarith
      have hq0 : (0 : ℝ) ≤ (phi : ℝ) ^ (1 / upperC1 ε) / (d : ℝ) := by positivity
      have hp0 : (0 : ℝ) ≤ (plo : ℝ) ^ (1 / upperC4 ε) / (d : ℝ) := by positivity
      constructor
      · rintro ⟨-, hB', hC'⟩
        exact ⟨(Nat.le_floor_iff hq0).mpr (hC.mp hC'), (Nat.floor_lt hp0).mpr (hiff4.mp hB')⟩
      · rintro ⟨hq, hp⟩
        have hC' : ((d : ℝ) * (k : ℝ)) ^ upperC1 ε ≤ (phi : ℝ) :=
          hC.mpr ((Nat.le_floor_iff hq0).mp hq)
        exact ⟨le_trans hC' (by exact_mod_cast hle),
          hiff4.mpr ((Nat.floor_lt hp0).mp hp), hC'⟩
  calc (Finset.Ioc a b).filter
        (fun k : ℕ => ((d : ℝ) * (k : ℝ)) ^ upperC1 ε ≤ (plo : ℝ) ∧
          (plo : ℝ) < ((d : ℝ) * (k : ℝ)) ^ upperC4 ε ∧
          ((d : ℝ) * (k : ℝ)) ^ upperC1 ε ≤ (phi : ℝ))
      = (Finset.Ioc a b).filter
          (fun k : ℕ => k ≤ ⌊(phi : ℝ) ^ (1 / upperC1 ε) / (d : ℝ)⌋₊ ∧
            ⌊(plo : ℝ) ^ (1 / upperC4 ε) / (d : ℝ)⌋₊ < k) := by
        refine Finset.filter_congr fun k _ => ?_
        exact hpred k
    _ = Finset.Ioc (max a ⌊(plo : ℝ) ^ (1 / upperC4 ε) / (d : ℝ)⌋₊)
          (min b ⌊(phi : ℝ) ^ (1 / upperC1 ε) / (d : ℝ)⌋₊) := filter_window_Ioc

/-- Page 48 Lemma 33's region, with the two exponents written as `A/u` and `B/u` for a positive
level `u`, is a conjunction of threshold conditions on `u` alone: the order `B ≤ A`, the two frozen
exponent bounds, and one of the three paper alternatives.  This is the form in which the covering
weight of the `kept` term becomes a function of the ambient level that changes only at finitely many
thresholds. -/
private lemma pair_region_iff {ε A B u : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    (hA : 0 < A) (hB : 0 < B) (hu : 0 < u) :
    upperPairRegion ε (A / u) (B / u) ↔
      (B ≤ A ∧ 2 * A ≤ u ∧ u ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) ∧
        B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u ∧
        (((2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u ∧
            A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u) ∨
          ((4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u ∧
            u ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε))) ∨
          ((4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u ∧
            u ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε))))) := by
  have hth : (0:ℝ) < 2 * (1 / 16 - 1 / 10 ^ 5) := by norm_num
  have hc1 : (0:ℝ) < (1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε := by nlinarith
  have hc2 : (0:ℝ) < (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε := by nlinarith
  have hd : (0:ℝ) < 2 * (1 / 16 - 1 / 10 ^ 5) - ε := by nlinarith
  have hd2 : (0:ℝ) < 2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε) := by nlinarith
  have hd2' : (0:ℝ) < 2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε) := by nlinarith
  have hSA : (0:ℝ) < 4 * A + 3 * B := by linarith
  have hSB : (0:ℝ) < 4 * A + B := by linarith
  -- the eight clause reductions
  have e1 : (B / u ≤ A / u) ↔ (B ≤ A) := by
    rw [div_le_div_iff_of_pos_right hu]
  have e2 : (A / u ≤ 1 / 2) ↔ (2 * A ≤ u) := by
    rw [div_le_iff₀ hu]; constructor <;> intro h <;> linarith
  have e3 : ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ B / u) ↔
      (u ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) := by
    rw [le_div_iff₀ hu, le_div_iff₀ hc1]; constructor <;> intro h <;> nlinarith
  have e4 : (B / u ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ↔
      (B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u) := by
    rw [div_le_iff₀ hu, div_le_iff₀ hc2]; constructor <;> intro h <;> nlinarith
  have e6 : (A / u ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ↔
      (A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u) := by
    rw [div_le_iff₀ hu, div_le_iff₀ hc2]; constructor <;> intro h <;> nlinarith
  have e5 : (2 * (B / u) - (2 * (1 / 16 - 1 / 10 ^ 5)) + ε ≤ A / u) ↔
      ((2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u) := by
    have hkey : 2 * (B / u) - (2 * (1 / 16 - 1 / 10 ^ 5)) + ε =
        (2 * B - (2 * (1 / 16 - 1 / 10 ^ 5) - ε) * u) / u := by
      field_simp; try ring
    rw [hkey, div_le_div_iff_of_pos_right hu, div_le_iff₀ hd]
    constructor <;> intro h <;> linarith
  have e7 : (|4 * (A / u) + 3 * (B / u) - 2| ≤ 2 * (1 / 16 - 1 / 10 ^ 5) - ε) ↔
      ((4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u ∧
        u ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε))) := by
    have hkey : 4 * (A / u) + 3 * (B / u) - 2 =
        (4 * A + 3 * B - 2 * u) / u := by
      field_simp; try ring
    rw [hkey, abs_le]
    constructor
    · rintro ⟨h1, h2⟩
      rw [le_div_iff₀ hu] at h1
      rw [div_le_iff₀ hu] at h2
      constructor
      · rw [div_le_iff₀ hd2']; nlinarith
      · rw [le_div_iff₀ hd2]; nlinarith
    · rintro ⟨h1, h2⟩
      rw [div_le_iff₀ hd2'] at h1
      rw [le_div_iff₀ hd2] at h2
      constructor
      · rw [le_div_iff₀ hu]; nlinarith
      · rw [div_le_iff₀ hu]; nlinarith
  have e8 : (|4 * (A / u) + (B / u) - 2| ≤ 2 * (1 / 16 - 1 / 10 ^ 5) - ε) ↔
      ((4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u ∧
        u ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε))) := by
    have hkey : 4 * (A / u) + (B / u) - 2 = (4 * A + B - 2 * u) / u := by
      field_simp; try ring
    rw [hkey, abs_le]
    constructor
    · rintro ⟨h1, h2⟩
      rw [le_div_iff₀ hu] at h1
      rw [div_le_iff₀ hu] at h2
      constructor
      · rw [div_le_iff₀ hd2']; nlinarith
      · rw [le_div_iff₀ hd2]; nlinarith
    · rintro ⟨h1, h2⟩
      rw [div_le_iff₀ hd2'] at h1
      rw [le_div_iff₀ hd2] at h2
      constructor
      · rw [le_div_iff₀ hu]; nlinarith
      · rw [div_le_iff₀ hu]; nlinarith
  unfold upperPairRegion
  rw [e1, e2, e3, e4, e5, e6, e7, e8]



/-- Summation by parts on `range`: the weighted sum is the top weight times the full sum minus the
increments of the weight against the prefix sums. -/
private lemma abel_range (w : ℕ → ℂ) (g : ℕ → ℂ) :
    ∀ n : ℕ, (∑ i ∈ Finset.range (n + 1), w i * g i)
      = w n * (∑ i ∈ Finset.range (n + 1), g i)
        - ∑ i ∈ Finset.range n, (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hL : (∑ i ∈ Finset.range (n + 1 + 1), w i * g i)
        = (∑ i ∈ Finset.range (n + 1), w i * g i) + w (n + 1) * g (n + 1) := by
      rw [Finset.sum_range_succ]
    have hG : (∑ i ∈ Finset.range (n + 1 + 1), g i)
        = (∑ i ∈ Finset.range (n + 1), g i) + g (n + 1) := by
      rw [Finset.sum_range_succ]
    have hD : (∑ i ∈ Finset.range (n + 1),
          (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j))
        = (∑ i ∈ Finset.range n, (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j))
          + (w (n + 1) - w n) * (∑ j ∈ Finset.range (n + 1), g j) := by
      rw [Finset.sum_range_succ]
    rw [hL, hG, hD, ih]
    ring

/-- A `{0,1}` valued weight that only changes at the members of `C` has total variation at most the
cardinality of `C`. -/
private lemma variation_le {w : ℕ → ℂ} {C : Finset ℕ} (a b : ℕ)
    (hw : ∀ j, w j = 0 ∨ w j = 1)
    (hchange : ∀ j, a ≤ j → j + 1 ≤ b → w (j + 1) ≠ w j → (j + 1) ∈ C) :
    ∑ j ∈ Finset.Ioc a (b - 1), ‖w (j + 1) - w j‖ ≤ (C.card : ℝ) := by
  have hstep : ∀ j ∈ Finset.Ioc a (b - 1), ‖w (j + 1) - w j‖ ≤ (if (j + 1) ∈ C then (1:ℝ) else 0) := by
    intro j hj
    obtain ⟨haj, hjb⟩ := Finset.mem_Ioc.mp hj
    by_cases hmem : (j + 1) ∈ C
    · rw [if_pos hmem]
      have h1 : w (j + 1) = 0 ∨ w (j + 1) = 1 := hw (j + 1)
      have h2 : w j = 0 ∨ w j = 1 := hw j
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]
    · rw [if_neg hmem]
      have heq : w (j + 1) = w j := by
        by_contra hne
        exact hmem (hchange j (le_of_lt haj) (by omega) hne)
      simp [heq]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_boole]
  have hinj : ∀ j ∈ (Finset.Ioc a (b - 1)).filter (fun j => (j + 1) ∈ C),
      ∀ k ∈ (Finset.Ioc a (b - 1)).filter (fun j => (j + 1) ∈ C), j + 1 = k + 1 → j = k := by
    intro j _ k _ h; omega
  have hcard := Finset.card_le_card_of_injOn
    (s := (Finset.Ioc a (b - 1)).filter (fun j => (j + 1) ∈ C))
    (t := C) (f := fun j : ℕ => j + 1) (fun j hj => (Finset.mem_filter.mp hj).2) hinj
  exact_mod_cast hcard


/-- An integer interval sum is a `range` sum of the shifted sequence. -/
private lemma sum_Ioc_shift {β : Type*} [AddCommMonoid β] (f : ℕ → β) {a b : ℕ} (hab : a ≤ b) :
    ∑ j ∈ Finset.Ioc a b, f j = ∑ i ∈ Finset.range (b - a), f (a + 1 + i) := by
  have hset : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
    ext j; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have h1 : b + 1 - (a + 1) = b - a := by omega
  rw [h1]

/-- Summation by parts on an integer interval for a `{0,1}` weight: if every prefix sum of `g` over
the interval is bounded by `M` and the total variation of `w` is at most `V`, then the weighted sum is
bounded by `(V + 1) M`. -/
private lemma abel_Ioc_bound {w g : ℕ → ℂ} {a b : ℕ} (hab : a ≤ b) {M V : ℝ}
    (hM0 : 0 ≤ M) (hw : ∀ j, w j = 0 ∨ w j = 1)
    (hM : ∀ k, a ≤ k → k ≤ b → ‖∑ j ∈ Finset.Ioc a k, g j‖ ≤ M)
    (hvar : ∑ j ∈ Finset.Ioc a (b - 1), ‖w (j + 1) - w j‖ ≤ V) :
    ‖∑ j ∈ Finset.Ioc a b, w j * g j‖ ≤ (V + 1) * M := by
  set n : ℕ := b - a with hn
  have hbn : b = a + n := by omega
  have ha1 : a ≤ a + 1 := by omega
  set W : ℕ → ℂ := fun i => w (a + 1 + i) with hW
  set G : ℕ → ℂ := fun i => g (a + 1 + i) with hG
  have hw1 : ∀ j, ‖w j‖ ≤ 1 := by
    intro j
    rcases hw j with h | h <;> simp [h]
  have hpre_eq : ∀ i, (∑ j ∈ Finset.range (i + 1), G j) = ∑ j ∈ Finset.Ioc a (a + 1 + i), g j := by
    intro i
    have h := sum_Ioc_shift (fun j => g j) (a := a) (b := a + 1 + i) (by omega)
    rw [h]
    have hidx : a + 1 + i - a = i + 1 := by omega
    rw [hidx]
    try rfl
  have hpre_bound : ∀ i, i < n → ‖∑ j ∈ Finset.range (i + 1), G j‖ ≤ M := by
    intro i hi
    rw [hpre_eq i]
    exact hM (a + 1 + i) (by omega) (by omega)
  have hfull_bound : ‖∑ i ∈ Finset.range n, G i‖ ≤ M := by
    have h2 : (∑ i ∈ Finset.range n, G i) = ∑ j ∈ Finset.Ioc a (a + n), g j := by
      have h := sum_Ioc_shift (fun j => g j) (a := a) (b := a + n) (by omega)
      rw [h]
      have hidx : a + n - a = n := by omega
      rw [hidx]
      try rfl
    rw [h2, ← hbn]
    exact hM b (by omega) (le_refl b)
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have hb : b = a := by omega
    have hsum0 : (∑ j ∈ Finset.Ioc a a, w j * g j) = 0 := by simp
    rw [hb, hsum0, norm_zero]
    have hemp : Finset.Ioc a (a - 1) = ∅ := Finset.Ioc_eq_empty_of_le (by omega)
    have hV : (0:ℝ) ≤ V := by
      have h := hvar
      rw [hb, hemp] at h
      simpa using h
    nlinarith
  · have hn1 : n - 1 + 1 = n := by omega
    have habel := abel_range W G (n - 1)
    rw [hn1] at habel
    have hWdiff2 : (∑ i ∈ Finset.range (n - 1), ‖W (i + 1) - W i‖)
        = ∑ i ∈ Finset.range (n - 1), ‖w (a + 1 + i + 1) - w (a + 1 + i)‖ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have e1 : W (i + 1) = w (a + 1 + i + 1) := by
        simp only [hW]
        try congr 1
        try omega
      rw [e1]
      try rfl
    have hvar_eq : (∑ i ∈ Finset.range (n - 1), ‖w ((a + 1 + i) + 1) - w (a + 1 + i)‖)
        = ∑ j ∈ Finset.Ioc a (b - 1), ‖w (j + 1) - w j‖ := by
      have h := sum_Ioc_shift (fun j : ℕ => ‖w (j + 1) - w j‖) (a := a) (b := b - 1) (by omega)
      have hidx : b - 1 - a = n - 1 := by omega
      rw [h, hidx]
    have hL : (∑ j ∈ Finset.Ioc a b, w j * g j) = ∑ i ∈ Finset.range n, W i * G i := by
      rw [show (∑ j ∈ Finset.Ioc a b, w j * g j) =
        ∑ i ∈ Finset.range (b - a), (fun j => w j * g j) (a + 1 + i) from sum_Ioc_shift _ hab]
      try simp only [hW, hG, hn]
    rw [hL, habel]
    have hterm : ‖W (n - 1) * (∑ i ∈ Finset.range n, G i)‖ ≤ M := by
      rw [norm_mul]
      calc ‖W (n - 1)‖ * ‖∑ i ∈ Finset.range n, G i‖ ≤ 1 * M := by
            refine mul_le_mul ?_ hfull_bound (norm_nonneg _) (by norm_num)
            rcases hw (a + 1 + (n - 1)) with h | h <;> simp [hW, h]
        _ = M := by ring
    have hrest : ‖∑ i ∈ Finset.range (n - 1),
        (W (i + 1) - W i) * (∑ j ∈ Finset.range (i + 1), G j)‖ ≤ V * M := by
      refine le_trans (norm_sum_le _ _) ?_
      have hb1 : ∀ i ∈ Finset.range (n - 1),
          ‖(W (i + 1) - W i) * (∑ j ∈ Finset.range (i + 1), G j)‖ ≤ ‖W (i + 1) - W i‖ * M := by
        intro i hi
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hpre_bound i (by have := Finset.mem_range.mp hi; omega))
          (norm_nonneg _)
      refine le_trans (Finset.sum_le_sum hb1) ?_
      rw [← Finset.sum_mul]
      rw [hWdiff2, show (∑ i ∈ Finset.range (n - 1), ‖w (a + 1 + i + 1) - w (a + 1 + i)‖)
        = ∑ i ∈ Finset.range (n - 1), ‖w ((a + 1 + i) + 1) - w (a + 1 + i)‖ from rfl,
        hvar_eq]
      exact mul_le_mul_of_nonneg_right hvar hM0
    calc ‖W (n - 1) * (∑ i ∈ Finset.range n, G i) -
          ∑ i ∈ Finset.range (n - 1), (W (i + 1) - W i) * (∑ j ∈ Finset.range (i + 1), G j)‖
        ≤ ‖W (n - 1) * (∑ i ∈ Finset.range n, G i)‖ +
            ‖∑ i ∈ Finset.range (n - 1),
              (W (i + 1) - W i) * (∑ j ∈ Finset.range (i + 1), G j)‖ := norm_sub_le _ _
      _ ≤ M + V * M := add_le_add hterm hrest
      _ = (V + 1) * M := by ring

/-- The total variation of a monotone `[0,1]`-valued sequence over an integer interval is at most one. -/
private lemma var_le_one_of_mono {f : ℕ → ℝ} {a b : ℕ}
    (h0 : ∀ j, 0 ≤ f j) (h1 : ∀ j, f j ≤ 1) (hmono : ∀ j, f j ≤ f (j + 1)) :
    ∑ j ∈ Finset.Ioc a (b - 1), |f (j + 1) - f j| ≤ 1 := by
  rcases Nat.lt_or_ge a b with hab | hba
  · have hab' : a ≤ b - 1 := by omega
    have hterm : ∀ j ∈ Finset.Ioc a (b - 1), |f (j + 1) - f j| = f (j + 1) - f j := by
      intro j _
      rw [abs_of_nonneg]
      linarith [hmono j]
    rw [Finset.sum_congr rfl hterm]
    have hshift := sum_Ioc_shift (fun j => f (j + 1) - f j) (a := a) (b := b - 1) hab'
    rw [hshift]
    have htele : (∑ i ∈ Finset.range (b - 1 - a), (f (a + 1 + i + 1) - f (a + 1 + i)))
        = f (a + 1 + (b - 1 - a)) - f (a + 1 + 0) := by
      have := Finset.sum_range_sub (fun i => f (a + 1 + i)) (b - 1 - a)
      simpa only [add_assoc] using this
    rw [htele]
    have e1 : a + 1 + (b - 1 - a) = b := by omega
    rw [e1]
    have h2 : 0 ≤ f (a + 1 + 0) := h0 _
    have h3 : f b ≤ 1 := h1 _
    linarith
  · have hemp : Finset.Ioc a (b - 1) = ∅ := Finset.Ioc_eq_empty_of_le (by omega)
    rw [hemp, Finset.sum_empty]
    norm_num


/-- The total variation of an antitone `[0,1]`-valued sequence over an integer interval is at most
one: its complement is monotone and has the same differences. -/
private lemma var_le_one_of_anti {f : ℕ → ℝ} {a b : ℕ}
    (h0 : ∀ j, 0 ≤ f j) (h1 : ∀ j, f j ≤ 1) (hanti : ∀ j, f (j + 1) ≤ f j) :
    ∑ j ∈ Finset.Ioc a (b - 1), |f (j + 1) - f j| ≤ 1 := by
  have key := var_le_one_of_mono (f := fun j => 1 - f j) (a := a) (b := b)
    (fun j => by linarith [h1 j]) (fun j => by linarith [h0 j])
    (fun j => by linarith [hanti j])
  refine le_trans (le_of_eq ?_) key
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (1 - f (j + 1)) - (1 - f j) = -(f (j + 1) - f j) by ring, abs_neg]

/-- A real threshold on the ambient level is a threshold on the cofactor: `e` is at most the
logarithm of `d j` exactly when the cofactor reaches the ceiling of `exp e / d`. -/
private lemma le_log_iff {d j : ℕ} (hd : 0 < d) (hj : 1 ≤ j) (e : ℝ) :
    (e ≤ Real.log ((d : ℝ) * (j : ℝ))) ↔ (⌈Real.exp e / (d : ℝ)⌉₊ ≤ j) := by
  have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
  have step1 : (e ≤ Real.log ((d:ℝ) * (j:ℝ))) ↔ (Real.exp e ≤ (d:ℝ) * (j:ℝ)) :=
    Real.le_log_iff_exp_le (by positivity)
  have step2 : (Real.exp e ≤ (d:ℝ) * (j:ℝ)) ↔ (Real.exp e / (d:ℝ) ≤ (j:ℝ)) := by
    rw [div_le_iff₀ hdpos]; constructor <;> intro h <;> linarith
  rw [step1, step2, Nat.ceil_le]

/-- The mirror image: the logarithm of `d j` is at most `e` exactly when the cofactor is at most the
floor of `exp e / d`. -/
private lemma log_le_iff {d j : ℕ} (hd : 0 < d) (hj : 1 ≤ j) (e : ℝ) :
    (Real.log ((d : ℝ) * (j : ℝ)) ≤ e) ↔ (j ≤ ⌊Real.exp e / (d : ℝ)⌋₊) := by
  have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
  have step1 : (Real.log ((d:ℝ) * (j:ℝ)) ≤ e) ↔ ((d:ℝ) * (j:ℝ) ≤ Real.exp e) :=
    Real.log_le_iff_le_exp (by positivity)
  have step2 : ((d:ℝ) * (j:ℝ) ≤ Real.exp e) ↔ ((j:ℝ) ≤ Real.exp e / (d:ℝ)) := by
    rw [le_div_iff₀ hdpos]; constructor <;> intro h <;> linarith
  rw [step1, step2]
  constructor
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    have h1 : Real.exp e / (d:ℝ) < ((⌊Real.exp e / (d:ℝ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : ((⌊Real.exp e / (d:ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ (j : ℝ) := by
      have h3 : ⌊Real.exp e / (d:ℝ)⌋₊ + 1 ≤ j := by omega
      exact_mod_cast h3
    linarith
  · intro h
    have h1 : ((⌊Real.exp e / (d:ℝ)⌋₊ : ℕ) : ℝ) ≤ Real.exp e / (d:ℝ) := Nat.floor_le (by positivity)
    have h2 : (j : ℝ) ≤ ((⌊Real.exp e / (d:ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
    linarith

/-- The covering predicate of the `kept` term, read at the ambient level, is constant between two
consecutive members of the cut set: every one of its thresholds separates the two cofactors, and each
threshold of the level is a member of the cut set through its ceiling or its floor. -/
private lemma atom_cell {d : ℕ} (hd : 0 < d) {E : Finset ℝ} {C : Finset ℕ} {j j' : ℕ}
    (hj : 1 ≤ j) (hj' : 1 ≤ j')
    (hC1 : ∀ e ∈ E, ⌈Real.exp e / (d : ℝ)⌉₊ ∈ C)
    (hC2 : ∀ e ∈ E, ⌊Real.exp e / (d : ℝ)⌋₊ + 1 ∈ C)
    (hcut : ∀ c ∈ C, c ≤ j ↔ c ≤ j') :
    ∀ e ∈ E, (e ≤ Real.log ((d : ℝ) * (j : ℝ)) ↔ e ≤ Real.log ((d : ℝ) * (j' : ℝ))) ∧
      (Real.log ((d : ℝ) * (j : ℝ)) ≤ e ↔ Real.log ((d : ℝ) * (j' : ℝ)) ≤ e) := by
  intro e he
  refine ⟨?_, ?_⟩
  · rw [le_log_iff hd hj e, le_log_iff hd hj' e]
    exact hcut _ (hC1 e he)
  · rw [log_le_iff hd hj e, log_le_iff hd hj' e]
    have hF := hcut (⌊Real.exp e / (d : ℝ)⌋₊ + 1) (hC2 e he)
    constructor
    · intro h
      by_contra hcon
      have h2 : ⌊Real.exp e / (d : ℝ)⌋₊ + 1 ≤ j' := by omega
      rw [← hF] at h2
      omega
    · intro h
      by_contra hcon
      have h2 : ⌊Real.exp e / (d : ℝ)⌋₊ + 1 ≤ j := by omega
      rw [hF] at h2
      omega



/-- Two `{0,1}` indicators whose propositions differ differ by one in absolute value. -/
private lemma ind_diff_eq_one {P Q : Prop} [Decidable P] [Decidable Q] (h : ¬ (P ↔ Q)) :
    |(if P then (1 : ℝ) else 0) - (if Q then (1 : ℝ) else 0)| = 1 := by
  by_cases hP : P
  · have hQ : ¬ Q := fun hq => h ⟨fun _ => hq, fun _ => hP⟩
    rw [if_pos hP, if_neg hQ]; norm_num
  · have hQ : Q := by
      by_contra hq
      exact h ⟨fun hp => absurd hp hP, fun hq' => absurd hq' hq⟩
    rw [if_neg hP, if_pos hQ]; norm_num

/-- Two `{0,1}` indicators whose propositions agree are equal. -/
private lemma ind_diff_eq_zero {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then (1 : ℝ) else 0) - (if Q then (1 : ℝ) else 0) = 0 := by
  by_cases hP : P
  · rw [if_pos hP, if_pos (h.mp hP)]; norm_num
  · rw [if_neg hP, if_neg (fun hq => hP (h.mpr hq))]; norm_num

/-- The complex norm of the difference of two `{0,1}` indicators is the real absolute value of the
corresponding difference. -/
private lemma norm_ind_sub (P Q : Prop) [Decidable P] [Decidable Q] :
    ‖(if P then (1 : ℂ) else 0) - (if Q then (1 : ℂ) else 0)‖ =
      |(if P then (1 : ℝ) else 0) - (if Q then (1 : ℝ) else 0)| := by
  by_cases h1 : P <;> by_cases h2 : Q <;> simp [h1, h2]

/-- A `{0,1}`-valued complex indicator takes one of two values. -/
private lemma ind_val (P : Prop) [Decidable P] :
    (if P then (1 : ℂ) else 0) = 0 ∨ (if P then (1 : ℂ) else 0) = 1 := by
  by_cases h : P <;> simp [h]

/-- An indicator times a factor is the factor restricted to the proposition. -/
private lemma ind_mul (P : Prop) [Decidable P] (X : ℂ) :
    (if P then X else 0) = (if P then (1 : ℂ) else 0) * X := by
  by_cases h : P <;> simp [h]

set_option maxHeartbeats 30000000 in
/-- The total variation of one region of Lemma 33, read as a function of the ambient level along the
monotone ray `u j`, is at most nine: the region is a boolean function of nine threshold comparisons,
each monotone or antitone and therefore of variation at most one. -/
private lemma var_region_le {ε A B : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    (hA : 0 < A) (hB : 0 < B) {u : ℕ → ℝ} (hupos : ∀ j, 1 ≤ j → 0 < u j)
    (hmono : ∀ j j', j ≤ j' → u j ≤ u j') {a b : ℕ} :
    ∑ j ∈ Finset.Ioc a (b - 1),
      |(if upperPairRegion ε (A / u (j + 1)) (B / u (j + 1)) then (1 : ℝ) else 0) -
        (if upperPairRegion ε (A / u j) (B / u j) then (1 : ℝ) else 0)| ≤ 9 := by
  have e1 : (∑ j ∈ Finset.Ioc a (b - 1), |(if 2 * A ≤ u (j+1) then (1:ℝ) else 0) - (if 2 * A ≤ u j then (1:ℝ) else 0)|) ≤ 1 :=
    var_le_one_of_mono (f := fun j => (if 2 * A ≤ u j then (1:ℝ) else 0))
      (fun j => by positivity)
      (fun j => by split_ifs <;> norm_num)
      (fun j => by
        by_cases h : 2 * A ≤ u j
        · rw [if_pos h, if_pos (le_trans h (hmono j (j + 1) (by omega)))]
        · rw [if_neg h]; split_ifs with h2 <;> norm_num)
  have e2 : (∑ j ∈ Finset.Ioc a (b - 1), |(if u (j+1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0) - (if u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0)|) ≤ 1 :=
    var_le_one_of_anti (f := fun j => (if u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0))
      (fun j => by positivity)
      (fun j => by split_ifs <;> norm_num)
      (fun j => by
        by_cases h : u (j + 1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)
        · rw [if_pos h, if_pos (le_trans (hmono j (j + 1) (by omega)) h)]
        · rw [if_neg h]; split_ifs with h2 <;> norm_num)
  have e3 : (∑ j ∈ Finset.Ioc a (b - 1), |(if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)|) ≤ 1 :=
    var_le_one_of_mono (f := fun j => (if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0))
      (fun j => by positivity)
      (fun j => by split_ifs <;> norm_num)
      (fun j => by
        by_cases h : B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j
        · rw [if_pos h, if_pos (le_trans h (hmono j (j + 1) (by omega)))]
        · rw [if_neg h]; split_ifs with h2 <;> norm_num)
  have e4 : (∑ j ∈ Finset.Ioc a (b - 1), |(if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j then (1:ℝ) else 0)|) ≤ 1 :=
    var_le_one_of_mono (f := fun j => (if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j then (1:ℝ) else 0))
      (fun j => by positivity)
      (fun j => by split_ifs <;> norm_num)
      (fun j => by
        by_cases h : (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j
        · rw [if_pos h, if_pos (le_trans h (hmono j (j + 1) (by omega)))]
        · rw [if_neg h]; split_ifs with h2 <;> norm_num)
  have e5 : (∑ j ∈ Finset.Ioc a (b - 1), |(if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)|) ≤ 1 :=
    var_le_one_of_mono (f := fun j => (if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0))
      (fun j => by positivity)
      (fun j => by split_ifs <;> norm_num)
      (fun j => by
        by_cases h : A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j
        · rw [if_pos h, if_pos (le_trans h (hmono j (j + 1) (by omega)))]
        · rw [if_neg h]; split_ifs with h2 <;> norm_num)
  have e6 : (∑ j ∈ Finset.Ioc a (b - 1), |(if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)|) ≤ 1 :=
    var_le_one_of_mono (f := fun j => (if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0))
      (fun j => by positivity)
      (fun j => by split_ifs <;> norm_num)
      (fun j => by
        by_cases h : (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j
        · rw [if_pos h, if_pos (le_trans h (hmono j (j + 1) (by omega)))]
        · rw [if_neg h]; split_ifs with h2 <;> norm_num)
  have e7 : (∑ j ∈ Finset.Ioc a (b - 1), |(if u (j+1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0)|) ≤ 1 :=
    var_le_one_of_anti (f := fun j => (if u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0))
      (fun j => by positivity)
      (fun j => by split_ifs <;> norm_num)
      (fun j => by
        by_cases h : u (j + 1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε))
        · rw [if_pos h, if_pos (le_trans (hmono j (j + 1) (by omega)) h)]
        · rw [if_neg h]; split_ifs with h2 <;> norm_num)
  have e8 : (∑ j ∈ Finset.Ioc a (b - 1), |(if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)|) ≤ 1 :=
    var_le_one_of_mono (f := fun j => (if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0))
      (fun j => by positivity)
      (fun j => by split_ifs <;> norm_num)
      (fun j => by
        by_cases h : (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j
        · rw [if_pos h, if_pos (le_trans h (hmono j (j + 1) (by omega)))]
        · rw [if_neg h]; split_ifs with h2 <;> norm_num)
  have e9 : (∑ j ∈ Finset.Ioc a (b - 1), |(if u (j+1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0)|) ≤ 1 :=
    var_le_one_of_anti (f := fun j => (if u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0))
      (fun j => by positivity)
      (fun j => by split_ifs <;> norm_num)
      (fun j => by
        by_cases h : u (j + 1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε))
        · rw [if_pos h, if_pos (le_trans (hmono j (j + 1) (by omega)) h)]
        · rw [if_neg h]; split_ifs with h2 <;> norm_num)
  have key : ∀ j, 1 ≤ j → ((2 * A ≤ u (j + 1)) ↔ (2 * A ≤ u j)) →
      ((u (j + 1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) ↔ (u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε))) →
      ((B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j + 1)) ↔ (B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j)) →
      (((2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u (j + 1)) ↔ ((2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j)) →
      ((A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j + 1)) ↔ (A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j)) →
      (((4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j + 1)) ↔ ((4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j)) →
      ((u (j + 1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε))) ↔ (u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)))) →
      (((4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j + 1)) ↔ ((4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j)) →
      ((u (j + 1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε))) ↔ (u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)))) →
      (upperPairRegion ε (A / u (j + 1)) (B / u (j + 1)) ↔
        upperPairRegion ε (A / u j) (B / u j)) := by
    intro j hj i1 i2 i3 i4 i5 i6 i7 i8 i9
    rw [pair_region_iff hε hε8 hA hB (hupos (j + 1) (by omega)), pair_region_iff hε hε8 hA hB (hupos j hj)]
    simp only [i1, i2, i3, i4, i5, i6, i7, i8, i9]
  have hpt : ∀ j, 1 ≤ j →
      |(if upperPairRegion ε (A / u (j + 1)) (B / u (j + 1)) then (1:ℝ) else 0) -
        (if upperPairRegion ε (A / u j) (B / u j) then (1:ℝ) else 0)| ≤ |(if 2 * A ≤ u (j+1) then (1:ℝ) else 0) - (if 2 * A ≤ u j then (1:ℝ) else 0)| + |(if u (j+1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0) - (if u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0)| + |(if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)| + |(if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j then (1:ℝ) else 0)| + |(if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)| + |(if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)| + |(if u (j+1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0)| + |(if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)| + |(if u (j+1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0)| := by
    intro j hj
    by_cases hR : upperPairRegion ε (A / u (j + 1)) (B / u (j + 1)) ↔
        upperPairRegion ε (A / u j) (B / u j)
    · rw [ind_diff_eq_zero hR, abs_zero]
      linarith [abs_nonneg ((if 2 * A ≤ u (j+1) then (1:ℝ) else 0) - (if 2 * A ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0) - (if u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0)), abs_nonneg ((if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0))]
    · rw [ind_diff_eq_one hR]
      have hnot : ¬ (((2 * A ≤ u (j + 1)) ↔ (2 * A ≤ u j)) ∧
        ((u (j + 1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) ↔ (u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε))) ∧
        ((B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j + 1)) ↔ (B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j)) ∧
        (((2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u (j + 1)) ↔ ((2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j)) ∧
        ((A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j + 1)) ↔ (A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j)) ∧
        (((4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j + 1)) ↔ ((4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j)) ∧
        ((u (j + 1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε))) ↔ (u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)))) ∧
        (((4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j + 1)) ↔ ((4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j)) ∧
        ((u (j + 1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε))) ↔ (u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε))))) := by
        intro h
        exact hR (key j hj h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2)
      have hor : ¬((2 * A ≤ u (j + 1)) ↔ (2 * A ≤ u j)) ∨
        ¬((u (j + 1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) ↔ (u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε))) ∨
        ¬((B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j + 1)) ↔ (B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j)) ∨
        ¬(((2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u (j + 1)) ↔ ((2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j)) ∨
        ¬((A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j + 1)) ↔ (A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j)) ∨
        ¬(((4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j + 1)) ↔ ((4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j)) ∨
        ¬((u (j + 1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε))) ↔ (u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)))) ∨
        ¬(((4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j + 1)) ↔ ((4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j)) ∨
        ¬((u (j + 1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε))) ↔ (u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)))) := by tauto
      rcases hor with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
      · have hk := ind_diff_eq_one (P := (2 * A ≤ u (j + 1))) (Q := (2 * A ≤ u j)) h1
        linarith [hk, abs_nonneg ((if u (j+1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0) - (if u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0)), abs_nonneg ((if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (u (j + 1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε))) (Q := (u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε))) h2
        linarith [hk, abs_nonneg ((if 2 * A ≤ u (j+1) then (1:ℝ) else 0) - (if 2 * A ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j + 1))) (Q := (B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j)) h3
        linarith [hk, abs_nonneg ((if 2 * A ≤ u (j+1) then (1:ℝ) else 0) - (if 2 * A ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0) - (if u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0)), abs_nonneg ((if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := ((2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u (j + 1))) (Q := ((2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j)) h4
        linarith [hk, abs_nonneg ((if 2 * A ≤ u (j+1) then (1:ℝ) else 0) - (if 2 * A ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0) - (if u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0)), abs_nonneg ((if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j + 1))) (Q := (A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j)) h5
        linarith [hk, abs_nonneg ((if 2 * A ≤ u (j+1) then (1:ℝ) else 0) - (if 2 * A ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0) - (if u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0)), abs_nonneg ((if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := ((4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j + 1))) (Q := ((4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j)) h6
        linarith [hk, abs_nonneg ((if 2 * A ≤ u (j+1) then (1:ℝ) else 0) - (if 2 * A ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0) - (if u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0)), abs_nonneg ((if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (u (j + 1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)))) (Q := (u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)))) h7
        linarith [hk, abs_nonneg ((if 2 * A ≤ u (j+1) then (1:ℝ) else 0) - (if 2 * A ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0) - (if u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0)), abs_nonneg ((if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := ((4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j + 1))) (Q := ((4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j)) h8
        linarith [hk, abs_nonneg ((if 2 * A ≤ u (j+1) then (1:ℝ) else 0) - (if 2 * A ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0) - (if u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0)), abs_nonneg ((if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (u (j + 1) ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)))) (Q := (u j ≤ (4 * A + B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)))) h9
        linarith [hk, abs_nonneg ((if 2 * A ≤ u (j+1) then (1:ℝ) else 0) - (if 2 * A ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0) - (if u j ≤ B / ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε) then (1:ℝ) else 0)), abs_nonneg ((if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if B / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if (2 * B - A) / (2 * (1 / 16 - 1 / 10 ^ 5) - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u (j+1) then (1:ℝ) else 0) - (if A / ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + 3 * B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0)), abs_nonneg ((if u (j+1) ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0) - (if u j ≤ (4 * A + 3 * B) / (2 - (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) then (1:ℝ) else 0)), abs_nonneg ((if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u (j+1) then (1:ℝ) else 0) - (if (4 * A + B) / (2 + (2 * (1 / 16 - 1 / 10 ^ 5) - ε)) ≤ u j then (1:ℝ) else 0))]
  refine le_trans (Finset.sum_le_sum fun j hj => hpt j (by have h := (Finset.mem_Ioc.mp hj).1; omega)) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith [e1, e2, e3, e4, e5, e6, e7, e8, e9]

set_option maxHeartbeats 20000000 in
/-- The total variation of the covering predicate of the `kept` term, read at the ambient level along
the monotone ray `u j`, is at most `108`: it is the disjunction of the twelve regions of Lemma 33 and
each region contributes at most nine. -/
private lemma var_cov_le {ε la lb lc : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    (hla : 0 < la) (hlb : 0 < lb) (hlc : 0 < lc) {u : ℕ → ℝ} (hupos : ∀ j, 1 ≤ j → 0 < u j)
    (hmono : ∀ j j', j ≤ j' → u j ≤ u j') {a b : ℕ} :
    ∑ j ∈ Finset.Ioc a (b - 1),
      |(if upperPrimeCovered ε (la / u (j + 1)) (lb / u (j + 1)) (lc / u (j + 1)) then (1 : ℝ)
          else 0) -
        (if upperPrimeCovered ε (la / u j) (lb / u j) (lc / u j) then (1 : ℝ) else 0)| ≤ 108 := by
  have v1 : (∑ j ∈ Finset.Ioc a (b - 1), |(if upperPairRegion ε (la / u (j + 1)) (lb / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j) then (1:ℝ) else 0)|) ≤ 9 := by
    simpa only [add_div] using
      var_region_le (A := la) (B := lb) hε hε8 (hla) (hlb) hupos hmono
  have v2 : (∑ j ∈ Finset.Ioc a (b - 1), |(if upperPairRegion ε (lb / u (j + 1)) (la / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j) then (1:ℝ) else 0)|) ≤ 9 := by
    simpa only [add_div] using
      var_region_le (A := lb) (B := la) hε hε8 (hlb) (hla) hupos hmono
  have v3 : (∑ j ∈ Finset.Ioc a (b - 1), |(if upperPairRegion ε (la / u (j + 1)) (lc / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lc / u j) then (1:ℝ) else 0)|) ≤ 9 := by
    simpa only [add_div] using
      var_region_le (A := la) (B := lc) hε hε8 (hla) (hlc) hupos hmono
  have v4 : (∑ j ∈ Finset.Ioc a (b - 1), |(if upperPairRegion ε (lc / u (j + 1)) (la / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j) then (1:ℝ) else 0)|) ≤ 9 := by
    simpa only [add_div] using
      var_region_le (A := lc) (B := la) hε hε8 (hlc) (hla) hupos hmono
  have v5 : (∑ j ∈ Finset.Ioc a (b - 1), |(if upperPairRegion ε (lb / u (j + 1)) (lc / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (lc / u j) then (1:ℝ) else 0)|) ≤ 9 := by
    simpa only [add_div] using
      var_region_le (A := lb) (B := lc) hε hε8 (hlb) (hlc) hupos hmono
  have v6 : (∑ j ∈ Finset.Ioc a (b - 1), |(if upperPairRegion ε (lc / u (j + 1)) (lb / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (lb / u j) then (1:ℝ) else 0)|) ≤ 9 := by
    simpa only [add_div] using
      var_region_le (A := lc) (B := lb) hε hε8 (hlc) (hlb) hupos hmono
  have v7 : (∑ j ∈ Finset.Ioc a (b - 1), |(if upperPairRegion ε (la / u (j + 1) + lb / u (j + 1)) (lc / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lb / u j) (lc / u j) then (1:ℝ) else 0)|) ≤ 9 := by
    simpa only [add_div] using
      var_region_le (A := la + lb) (B := lc) hε hε8 (by linarith [hla, hlb, hlc]) (hlc) hupos hmono
  have v8 : (∑ j ∈ Finset.Ioc a (b - 1), |(if upperPairRegion ε (lc / u (j + 1)) (la / u (j + 1) + lb / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j + lb / u j) then (1:ℝ) else 0)|) ≤ 9 := by
    simpa only [add_div] using
      var_region_le (A := lc) (B := la + lb) hε hε8 (hlc) (by linarith [hla, hlb, hlc]) hupos hmono
  have v9 : (∑ j ∈ Finset.Ioc a (b - 1), |(if upperPairRegion ε (la / u (j + 1) + lc / u (j + 1)) (lb / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lc / u j) (lb / u j) then (1:ℝ) else 0)|) ≤ 9 := by
    simpa only [add_div] using
      var_region_le (A := la + lc) (B := lb) hε hε8 (by linarith [hla, hlb, hlc]) (hlb) hupos hmono
  have v10 : (∑ j ∈ Finset.Ioc a (b - 1), |(if upperPairRegion ε (lb / u (j + 1)) (la / u (j + 1) + lc / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j + lc / u j) then (1:ℝ) else 0)|) ≤ 9 := by
    simpa only [add_div] using
      var_region_le (A := lb) (B := la + lc) hε hε8 (hlb) (by linarith [hla, hlb, hlc]) hupos hmono
  have v11 : (∑ j ∈ Finset.Ioc a (b - 1), |(if upperPairRegion ε (lb / u (j + 1) + lc / u (j + 1)) (la / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j + lc / u j) (la / u j) then (1:ℝ) else 0)|) ≤ 9 := by
    simpa only [add_div] using
      var_region_le (A := lb + lc) (B := la) hε hε8 (by linarith [hla, hlb, hlc]) (hla) hupos hmono
  have v12 : (∑ j ∈ Finset.Ioc a (b - 1), |(if upperPairRegion ε (la / u (j + 1)) (lb / u (j + 1) + lc / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j + lc / u j) then (1:ℝ) else 0)|) ≤ 9 := by
    simpa only [add_div] using
      var_region_le (A := la) (B := lb + lc) hε hε8 (hla) (by linarith [hla, hlb, hlc]) hupos hmono
  have hpt : ∀ j, 1 ≤ j →
      |(if upperPrimeCovered ε (la / u (j + 1)) (lb / u (j + 1)) (lc / u (j + 1)) then (1 : ℝ)
          else 0) -
        (if upperPrimeCovered ε (la / u j) (lb / u j) (lc / u j) then (1 : ℝ) else 0)| ≤ |(if upperPairRegion ε (la / u (j + 1)) (lb / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j) then (1:ℝ) else 0)| + |(if upperPairRegion ε (lb / u (j + 1)) (la / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j) then (1:ℝ) else 0)| + |(if upperPairRegion ε (la / u (j + 1)) (lc / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lc / u j) then (1:ℝ) else 0)| + |(if upperPairRegion ε (lc / u (j + 1)) (la / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j) then (1:ℝ) else 0)| + |(if upperPairRegion ε (lb / u (j + 1)) (lc / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (lc / u j) then (1:ℝ) else 0)| + |(if upperPairRegion ε (lc / u (j + 1)) (lb / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (lb / u j) then (1:ℝ) else 0)| + |(if upperPairRegion ε (la / u (j + 1) + lb / u (j + 1)) (lc / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lb / u j) (lc / u j) then (1:ℝ) else 0)| + |(if upperPairRegion ε (lc / u (j + 1)) (la / u (j + 1) + lb / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j + lb / u j) then (1:ℝ) else 0)| + |(if upperPairRegion ε (la / u (j + 1) + lc / u (j + 1)) (lb / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lc / u j) (lb / u j) then (1:ℝ) else 0)| + |(if upperPairRegion ε (lb / u (j + 1)) (la / u (j + 1) + lc / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j + lc / u j) then (1:ℝ) else 0)| + |(if upperPairRegion ε (lb / u (j + 1) + lc / u (j + 1)) (la / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j + lc / u j) (la / u j) then (1:ℝ) else 0)| + |(if upperPairRegion ε (la / u (j + 1)) (lb / u (j + 1) + lc / u (j + 1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j + lc / u j) then (1:ℝ) else 0)| := by
    intro j hj
    by_cases hR : upperPrimeCovered ε (la / u (j + 1)) (lb / u (j + 1)) (lc / u (j + 1)) ↔
        upperPrimeCovered ε (la / u j) (lb / u j) (lc / u j)
    · rw [ind_diff_eq_zero hR, abs_zero]
      linarith [abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1) + lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j + lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j + lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1) + lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j + lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j + lc / u j) then (1:ℝ) else 0))]
    · rw [ind_diff_eq_one hR]
      have hnot : ¬ (((upperPairRegion ε (la / u (j + 1)) (lb / u (j + 1))) ↔ (upperPairRegion ε (la / u j) (lb / u j))) ∧
        ((upperPairRegion ε (lb / u (j + 1)) (la / u (j + 1))) ↔ (upperPairRegion ε (lb / u j) (la / u j))) ∧
        ((upperPairRegion ε (la / u (j + 1)) (lc / u (j + 1))) ↔ (upperPairRegion ε (la / u j) (lc / u j))) ∧
        ((upperPairRegion ε (lc / u (j + 1)) (la / u (j + 1))) ↔ (upperPairRegion ε (lc / u j) (la / u j))) ∧
        ((upperPairRegion ε (lb / u (j + 1)) (lc / u (j + 1))) ↔ (upperPairRegion ε (lb / u j) (lc / u j))) ∧
        ((upperPairRegion ε (lc / u (j + 1)) (lb / u (j + 1))) ↔ (upperPairRegion ε (lc / u j) (lb / u j))) ∧
        ((upperPairRegion ε (la / u (j + 1) + lb / u (j + 1)) (lc / u (j + 1))) ↔ (upperPairRegion ε (la / u j + lb / u j) (lc / u j))) ∧
        ((upperPairRegion ε (lc / u (j + 1)) (la / u (j + 1) + lb / u (j + 1))) ↔ (upperPairRegion ε (lc / u j) (la / u j + lb / u j))) ∧
        ((upperPairRegion ε (la / u (j + 1) + lc / u (j + 1)) (lb / u (j + 1))) ↔ (upperPairRegion ε (la / u j + lc / u j) (lb / u j))) ∧
        ((upperPairRegion ε (lb / u (j + 1)) (la / u (j + 1) + lc / u (j + 1))) ↔ (upperPairRegion ε (lb / u j) (la / u j + lc / u j))) ∧
        ((upperPairRegion ε (lb / u (j + 1) + lc / u (j + 1)) (la / u (j + 1))) ↔ (upperPairRegion ε (lb / u j + lc / u j) (la / u j))) ∧
        ((upperPairRegion ε (la / u (j + 1)) (lb / u (j + 1) + lc / u (j + 1))) ↔ (upperPairRegion ε (la / u j) (lb / u j + lc / u j)))) := by
        intro h
        apply hR
        unfold upperPrimeCovered
        simp only [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2]
      have hor : ¬((upperPairRegion ε (la / u (j + 1)) (lb / u (j + 1))) ↔ (upperPairRegion ε (la / u j) (lb / u j))) ∨
        ¬((upperPairRegion ε (lb / u (j + 1)) (la / u (j + 1))) ↔ (upperPairRegion ε (lb / u j) (la / u j))) ∨
        ¬((upperPairRegion ε (la / u (j + 1)) (lc / u (j + 1))) ↔ (upperPairRegion ε (la / u j) (lc / u j))) ∨
        ¬((upperPairRegion ε (lc / u (j + 1)) (la / u (j + 1))) ↔ (upperPairRegion ε (lc / u j) (la / u j))) ∨
        ¬((upperPairRegion ε (lb / u (j + 1)) (lc / u (j + 1))) ↔ (upperPairRegion ε (lb / u j) (lc / u j))) ∨
        ¬((upperPairRegion ε (lc / u (j + 1)) (lb / u (j + 1))) ↔ (upperPairRegion ε (lc / u j) (lb / u j))) ∨
        ¬((upperPairRegion ε (la / u (j + 1) + lb / u (j + 1)) (lc / u (j + 1))) ↔ (upperPairRegion ε (la / u j + lb / u j) (lc / u j))) ∨
        ¬((upperPairRegion ε (lc / u (j + 1)) (la / u (j + 1) + lb / u (j + 1))) ↔ (upperPairRegion ε (lc / u j) (la / u j + lb / u j))) ∨
        ¬((upperPairRegion ε (la / u (j + 1) + lc / u (j + 1)) (lb / u (j + 1))) ↔ (upperPairRegion ε (la / u j + lc / u j) (lb / u j))) ∨
        ¬((upperPairRegion ε (lb / u (j + 1)) (la / u (j + 1) + lc / u (j + 1))) ↔ (upperPairRegion ε (lb / u j) (la / u j + lc / u j))) ∨
        ¬((upperPairRegion ε (lb / u (j + 1) + lc / u (j + 1)) (la / u (j + 1))) ↔ (upperPairRegion ε (lb / u j + lc / u j) (la / u j))) ∨
        ¬((upperPairRegion ε (la / u (j + 1)) (lb / u (j + 1) + lc / u (j + 1))) ↔ (upperPairRegion ε (la / u j) (lb / u j + lc / u j))) := by
        by_contra hc
        push_neg at hc
        exact hnot hc
      rcases hor with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
      · have hk := ind_diff_eq_one (P := (upperPairRegion ε (la / u (j + 1)) (lb / u (j + 1)))) (Q := (upperPairRegion ε (la / u j) (lb / u j))) h1
        linarith [hk, abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1) + lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j + lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j + lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1) + lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j + lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j + lc / u j) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (upperPairRegion ε (lb / u (j + 1)) (la / u (j + 1)))) (Q := (upperPairRegion ε (lb / u j) (la / u j))) h2
        linarith [hk, abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1) + lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j + lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j + lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1) + lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j + lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j + lc / u j) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (upperPairRegion ε (la / u (j + 1)) (lc / u (j + 1)))) (Q := (upperPairRegion ε (la / u j) (lc / u j))) h3
        linarith [hk, abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1) + lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j + lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j + lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1) + lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j + lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j + lc / u j) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (upperPairRegion ε (lc / u (j + 1)) (la / u (j + 1)))) (Q := (upperPairRegion ε (lc / u j) (la / u j))) h4
        linarith [hk, abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1) + lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j + lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j + lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1) + lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j + lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j + lc / u j) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (upperPairRegion ε (lb / u (j + 1)) (lc / u (j + 1)))) (Q := (upperPairRegion ε (lb / u j) (lc / u j))) h5
        linarith [hk, abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1) + lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j + lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j + lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1) + lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j + lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j + lc / u j) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (upperPairRegion ε (lc / u (j + 1)) (lb / u (j + 1)))) (Q := (upperPairRegion ε (lc / u j) (lb / u j))) h6
        linarith [hk, abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1) + lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j + lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j + lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1) + lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j + lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j + lc / u j) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (upperPairRegion ε (la / u (j + 1) + lb / u (j + 1)) (lc / u (j + 1)))) (Q := (upperPairRegion ε (la / u j + lb / u j) (lc / u j))) h7
        linarith [hk, abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1) + lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j + lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j + lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1) + lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j + lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j + lc / u j) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (upperPairRegion ε (lc / u (j + 1)) (la / u (j + 1) + lb / u (j + 1)))) (Q := (upperPairRegion ε (lc / u j) (la / u j + lb / u j))) h8
        linarith [hk, abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j + lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1) + lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j + lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j + lc / u j) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (upperPairRegion ε (la / u (j + 1) + lc / u (j + 1)) (lb / u (j + 1)))) (Q := (upperPairRegion ε (la / u j + lc / u j) (lb / u j))) h9
        linarith [hk, abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1) + lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j + lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j + lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1) + lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j + lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j + lc / u j) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (upperPairRegion ε (lb / u (j + 1)) (la / u (j + 1) + lc / u (j + 1)))) (Q := (upperPairRegion ε (lb / u j) (la / u j + lc / u j))) h10
        linarith [hk, abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1) + lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j + lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1) + lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j + lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j + lc / u j) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (upperPairRegion ε (lb / u (j + 1) + lc / u (j + 1)) (la / u (j + 1)))) (Q := (upperPairRegion ε (lb / u j + lc / u j) (la / u j))) h11
        linarith [hk, abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1) + lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j + lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j + lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j + lc / u j) then (1:ℝ) else 0))]
      · have hk := ind_diff_eq_one (P := (upperPairRegion ε (la / u (j + 1)) (lb / u (j + 1) + lc / u (j + 1)))) (Q := (upperPairRegion ε (la / u j) (lb / u j + lc / u j))) h12
        linarith [hk, abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lb / u (j+1)) (lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lb / u j) (lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lc / u (j+1)) (la / u (j+1) + lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lc / u j) (la / u j + lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (la / u (j+1) + lc / u (j+1)) (lb / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (la / u j + lc / u j) (lb / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1)) (la / u (j+1) + lc / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j) (la / u j + lc / u j) then (1:ℝ) else 0)), abs_nonneg ((if upperPairRegion ε (lb / u (j+1) + lc / u (j+1)) (la / u (j+1)) then (1:ℝ) else 0) - (if upperPairRegion ε (lb / u j + lc / u j) (la / u j) then (1:ℝ) else 0))]
  refine le_trans (Finset.sum_le_sum fun j hj => hpt j (by have h := (Finset.mem_Ioc.mp hj).1; omega)) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]

set_option maxHeartbeats 16000000 in
/-- The `kept` fibre over one triple of primes, with the covering predicate read at the **ambient**
level `p1 p2 p3 j`.  The window tests cut an integer interval out of the cofactor range, the sifted
level is the third prime, and the covering weight has total variation at most `108`
(`var_cov_le`), so summation by parts against the Abel bound of the fixed level character sum costs
only that constant. -/
private lemma kept_fibre_le {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {Y : ℝ} {K p1 p2 p3 a b : ℕ} {C0 A : ℝ}
    (hp1 : p1.Prime) (hp2 : p2.Prime) (hp3 : p3.Prime) (hlt32 : p3 < p2) (hlt21 : p2 < p1)
    (hab : a ≤ b) (ha1 : 1 ≤ a)
    (hdbK : p1 * p2 * p3 * b ≤ K)
    (hY2 : 2 ≤ Y) (hKY : (K : ℝ) ≤ 2 * Y)
    (hzX : (2 * Y) ^ (upperC1 ε / 2) ≤ (p3 : ℝ))
    (hC0 : 0 ≤ C0)
    (hpre : ∀ (ζ a' b' : ℕ), (2 * Y) ^ (upperC1 ε / 2) ≤ (ζ : ℝ) → 1 ≤ a' → (b' : ℝ) ≤ 2 * Y →
      ‖∑ n ∈ Finset.Ioc a' b', ((Task308.roughIndicator n ζ : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
        C0 * (b' : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) :
    ‖∑ j ∈ Finset.Ioc a b,
        (if ((((p1 * p2 * p3 : ℕ) : ℝ) * (j : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
            (p1 : ℝ) < (((p1 * p2 * p3 : ℕ) : ℝ) * (j : ℝ)) ^ upperC4 ε ∧
            (((p1 * p2 * p3 : ℕ) : ℝ) * (j : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ)) then
          (if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p2 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p3 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) then
            ((Real.log (((p1 * p2 * p3 : ℕ) : ℝ) * (j : ℝ)) / Real.log Y *
              upperRough j (p3 : ℝ) : ℝ) : ℂ) * χ (j : ZMod q)
            else 0)
          else 0)‖ ≤
      436 * (C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) := by
  classical
  have hd1 : 1 ≤ p1 * p2 * p3 := by
    have h : 2 * 2 * 2 ≤ p1 * p2 * p3 :=
      Nat.mul_le_mul (Nat.mul_le_mul hp1.two_le hp2.two_le) hp3.two_le
    omega
  have hp31 : 1 ≤ p3 := le_trans (by norm_num) hp3.two_le
  have hle1 : p3 ≤ p1 := le_of_lt (lt_trans hlt32 hlt21)
  have hd0 : 0 < p1 * p2 * p3 := by omega
  have hd8 : (8 : ℝ) ≤ ((p1 * p2 * p3 : ℕ) : ℝ) := by
    have h : 8 ≤ p1 * p2 * p3 := by
      have h2 : 2 * 2 * 2 ≤ p1 * p2 * p3 := by
        exact Nat.mul_le_mul (Nat.mul_le_mul hp1.two_le hp2.two_le) hp3.two_le
      omega
    exact_mod_cast h
  rw [← Finset.sum_filter,
    filter_window_general (d := p1 * p2 * p3) (plo := p1) (phi := p3) hε8 hd1 hp31 hle1]
  have hlap : 0 < Real.log (p1 : ℝ) := Real.log_pos (by exact_mod_cast (by have h := hp1.two_le; omega : 1 < p1))
  have hlbn : 0 < Real.log (p2 : ℝ) := Real.log_pos (by exact_mod_cast (by have h := hp2.two_le; omega : 1 < p2))
  have hlcn : 0 < Real.log (p3 : ℝ) := Real.log_pos (by exact_mod_cast (by have h := hp3.two_le; omega : 1 < p3))
  have ha'1 : 1 ≤ (max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊) := le_trans ha1 (le_max_left _ _)
  have hL60 : (0 : ℝ) ≤ Real.log (2 * Y) ^ (-(A + 6)) :=
    Real.rpow_nonneg (Real.log_pos (by linarith)).le _
  rcases le_or_gt ((max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊)) ((min b ⌊(p3 : ℝ) ^ (1 / upperC1 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊)) with hAB | hAB
  · -- the sifted level is the third prime; the roughness is the fixed level indicator
    have hconv : (∑ j ∈ Finset.Ioc (max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊) (min b ⌊(p3 : ℝ) ^ (1 / upperC1 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊),
          (if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p2 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p3 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) then
            ((Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ)) / Real.log Y * upperRough j (p3 : ℝ) : ℝ) : ℂ) * χ (j : ZMod q)
          else 0))
        = (∑ j ∈ Finset.Ioc (max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊) (min b ⌊(p3 : ℝ) ^ (1 / upperC1 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊),
          (if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p2 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p3 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) then
            ((Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ)) / Real.log Y * Task308.roughIndicator j p3 : ℝ) : ℂ) *
              χ (j : ZMod q)
          else 0)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj2 : 2 ≤ j := by
        have h1 : (max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊) < j := (Finset.mem_Ioc.mp hj).1
        omega
      by_cases hc : upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p2 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p3 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ)))
      · rw [if_pos hc, if_pos hc, upperRough_eq_roughIndicator_ceil hj2 (p3 : ℝ),
          Nat.ceil_natCast]
      · rw [if_neg hc, if_neg hc]
    rw [hconv]
    -- the ambient level is monotone along the cofactor, and positive from one onwards
    have humono : ∀ j j' : ℕ, j ≤ j' → Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ)) ≤ Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j' : ℝ)) := by
      intro j j' hjj
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        rw [Nat.cast_zero, mul_zero, Real.log_zero]
        rcases Nat.eq_zero_or_pos j' with h0' | hpos'
        · rw [h0', Nat.cast_zero, mul_zero, Real.log_zero]
        · refine Real.log_nonneg ?_
          have h1 : (1 : ℝ) ≤ (j' : ℝ) := by exact_mod_cast hpos'
          nlinarith
      · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hpos
        have hjj' : (j : ℝ) ≤ (j' : ℝ) := by exact_mod_cast hjj
        have hj'1 : (1 : ℝ) ≤ (j' : ℝ) := le_trans hj1 hjj'
        refine Real.log_le_log (by positivity) ?_
        nlinarith
    have huposj : ∀ j : ℕ, 1 ≤ j → 0 < Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ)) := by
      intro j hj1
      have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      exact Real.log_pos (by nlinarith)
    have hvarR : (∑ j ∈ Finset.Ioc (max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊) ((min b ⌊(p3 : ℝ) ^ (1 / upperC1 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊) - 1),
        |(if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * ((j + 1 : ℕ) : ℝ))) (Real.log (p2 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * ((j + 1 : ℕ) : ℝ))) (Real.log (p3 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * ((j + 1 : ℕ) : ℝ))) then (1:ℝ) else 0) - (if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p2 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p3 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) then (1:ℝ) else 0)|) ≤ 108 :=
      var_cov_le (u := fun j : ℕ => Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) hε hε8 hlap hlbn hlcn huposj humono
    have hvar : (∑ j ∈ Finset.Ioc (max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊) ((min b ⌊(p3 : ℝ) ^ (1 / upperC1 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊) - 1),
        ‖(if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * ((j + 1 : ℕ) : ℝ))) (Real.log (p2 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * ((j + 1 : ℕ) : ℝ))) (Real.log (p3 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * ((j + 1 : ℕ) : ℝ))) then (1:ℂ) else 0) - (if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p2 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p3 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) then (1:ℂ) else 0)‖) ≤ 108 := by
      refine le_trans (le_of_eq ?_) hvarR
      refine Finset.sum_congr rfl fun j _ => ?_
      exact norm_ind_sub _ _
    -- the Abel bound of the fixed level character sum    -- the Abel bound of the fixed level character sum, uniformly over prefixes
    have hM : ∀ k, (max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊) ≤ k → k ≤ (min b ⌊(p3 : ℝ) ^ (1 / upperC1 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊) →
        ‖∑ j ∈ Finset.Ioc (max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊) k, ((Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ)) / Real.log Y *
        Task308.roughIndicator j p3 : ℝ) : ℂ) * χ (j : ZMod q)‖ ≤
          4 * (C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6))) := by
      intro k hak hkb
      have hkb' : k ≤ b := le_trans hkb (min_le_left _ _)
      have hdbK' : p1 * p2 * p3 * k ≤ K := by
        calc p1 * p2 * p3 * k ≤ p1 * p2 * p3 * b := Nat.mul_le_mul_left _ hkb'
          _ = p1 * p2 * p3 * b := rfl
          _ ≤ K := hdbK
      have hcore := interval_A_le (d := p1 * p2 * p3) (K := K) (z := p3) (a := (max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊)) (b := k)
        hε hε8 χ hd1 hY2 hKY hp31 hak ha'1 hdbK' hC0
        (fun a'' b'' ha'' hb'' => hpre p3 a'' b'' hzX ha'' hb'')
      refine le_trans hcore ?_
      have hkR : (k : ℝ) ≤ (b : ℝ) := by exact_mod_cast hkb'
      have hL6 : (0 : ℝ) ≤ Real.log (2 * Y) ^ (-(A + 6)) := hL60
      have h2 : C0 * (k : ℝ) ≤ C0 * (b : ℝ) := mul_le_mul_of_nonneg_left hkR hC0
      have h3 : C0 * (k : ℝ) * Real.log (2 * Y) ^ (-(A + 6)) ≤
          C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6)) :=
        mul_le_mul_of_nonneg_right h2 hL6
      linarith [h3]
    have hmain := abel_Ioc_bound
      (w := fun j : ℕ => (if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p2 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p3 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) then (1:ℂ) else 0))
      (g := fun j : ℕ => ((Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ)) / Real.log Y *
        Task308.roughIndicator j p3 : ℝ) : ℂ) * χ (j : ZMod q))
      (a := (max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊)) (b := (min b ⌊(p3 : ℝ) ^ (1 / upperC1 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊)) (M := 4 * (C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6))))
      (V := 108) hAB (by positivity)
      (fun j => ind_val _)
      hM hvar
    refine le_trans (le_of_eq ?_) (le_trans hmain ?_)
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      exact ind_mul (upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p2 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ))) (Real.log (p3 : ℝ) / Real.log ((((p1 * p2 * p3 : ℕ) : ℝ)) * (j : ℝ)))) _
    · refine le_of_eq ?_
      rw [show ((108 : ℝ) + 1) = 109 by norm_num]
      ring
  · have hemp : Finset.Ioc (max a ⌊(p1 : ℝ) ^ (1 / upperC4 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊) (min b ⌊(p3 : ℝ) ^ (1 / upperC1 ε) / (((p1 * p2 * p3 : ℕ) : ℝ))⌋₊) = ∅ :=
      Finset.Ioc_eq_empty_of_le (le_of_lt hAB)
    rw [hemp]
    simp only [Finset.sum_empty, norm_zero]
    have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : 1 ≤ b)
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := by linarith
    have hprod : (0 : ℝ) ≤ C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6)) :=
      mul_nonneg (mul_nonneg hC0 hb0) hL60
    nlinarith [hprod]



private lemma upperKept_fibre_reindex {ε Y : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q)
    {L K p1 : ℕ} (hp1 : 1 ≤ p1) :
    ∑ m ∈ Finset.Ioc L K,
        (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε)) then
          ((Real.log (m : ℝ) / Real.log Y *
          (∑ p2 ∈ (m / p1).primeFactors.filter
            (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2).primeFactors.filter
              (fun p3 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (m : ℝ))
                  (Real.log (p2 : ℝ) / Real.log (m : ℝ)) (Real.log (p3 : ℝ) / Real.log (m : ℝ))
                then upperRough (m / p1 / p2 / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) * χ (m : ZMod q)
          else 0)
      = χ (p1 : ZMod q) *
          ∑ n ∈ Finset.Ioc (L / p1) (K / p1),
            (if (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε)
              then ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
                (∑ p2 ∈ n.primeFactors.filter
                (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                  (p2 : ℝ) < (p1 : ℝ)),
                ∑ p3 ∈ (n / p2).primeFactors.filter
                  (fun p3 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧
                    (p3 : ℝ) < (p2 : ℝ)),
                  if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((p1 : ℝ) * (n : ℝ)))
                    (Real.log (p2 : ℝ) / Real.log ((p1 : ℝ) * (n : ℝ))) (Real.log (p3 : ℝ) / Real.log ((p1 : ℝ) * (n : ℝ)))
                  then upperRough (n / p2 / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                χ (n : ZMod q)
              else 0) := by
  have hp1pos : 0 < p1 := by omega
  have hsplit : ∀ m : ℕ,
      (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε)) then
        ((Real.log (m : ℝ) / Real.log Y *
          (∑ p2 ∈ (m / p1).primeFactors.filter
            (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2).primeFactors.filter
              (fun p3 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (m : ℝ))
                  (Real.log (p2 : ℝ) / Real.log (m : ℝ)) (Real.log (p3 : ℝ) / Real.log (m : ℝ))
                then upperRough (m / p1 / p2 / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) * χ (m : ZMod q)
        else 0)
      = (if p1 ∣ m then
          (if ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε) then
            ((Real.log (m : ℝ) / Real.log Y *
          (∑ p2 ∈ (m / p1).primeFactors.filter
            (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2).primeFactors.filter
              (fun p3 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (m : ℝ))
                  (Real.log (p2 : ℝ) / Real.log (m : ℝ)) (Real.log (p3 : ℝ) / Real.log (m : ℝ))
                then upperRough (m / p1 / p2 / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) * χ (m : ZMod q)
            else 0)
          else 0) := by
    intro m
    by_cases h : p1 ∣ m <;>
      by_cases h2 : ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε) <;>
      simp [h, h2]
  rw [Finset.sum_congr rfl (fun m _ => hsplit m)]
  rw [Rough514.sum_dvd_reindex hp1 L K
    (fun m => if ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε) then
        ((Real.log (m : ℝ) / Real.log Y *
          (∑ p2 ∈ (m / p1).primeFactors.filter
            (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2).primeFactors.filter
              (fun p3 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (m : ℝ))
                  (Real.log (p2 : ℝ) / Real.log (m : ℝ)) (Real.log (p3 : ℝ) / Real.log (m : ℝ))
                then upperRough (m / p1 / p2 / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) * χ (m : ZMod q)
        else 0)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hdiv : (p1 * n) / p1 = n := Nat.mul_div_cancel_left n hp1pos
  have hcast : (((p1 * n : ℕ)) : ℝ) = (p1 : ℝ) * (n : ℝ) := by push_cast; ring
  have hchi : χ (((p1 * n : ℕ)) : ZMod q) = χ (p1 : ZMod q) * χ (n : ZMod q) := by
    push_cast
    rw [map_mul]
  have hsum : (∑ p2 ∈ ((p1 * n) / p1).primeFactors.filter
        (fun p2 : ℕ => (((p1 * n : ℕ)) : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
        ∑ p3 ∈ (((p1 * n) / p1) / p2).primeFactors.filter
          (fun p3 : ℕ => (((p1 * n : ℕ)) : ℝ) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
          if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 * n : ℕ)) : ℝ))
              (Real.log (p2 : ℝ) / Real.log (((p1 * n : ℕ)) : ℝ))
              (Real.log (p3 : ℝ) / Real.log (((p1 * n : ℕ)) : ℝ))
            then upperRough (((p1 * n) / p1) / p2 / p3) (p3 : ℝ) else 0)
      = ∑ p2 ∈ n.primeFactors.filter
        (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
        ∑ p3 ∈ (n / p2).primeFactors.filter
          (fun p3 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
          if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((p1 : ℝ) * (n : ℝ)))
              (Real.log (p2 : ℝ) / Real.log ((p1 : ℝ) * (n : ℝ)))
              (Real.log (p3 : ℝ) / Real.log ((p1 : ℝ) * (n : ℝ)))
            then upperRough (n / p2 / p3) (p3 : ℝ) else 0 := by
    rw [hdiv, hcast]
  rw [hsum, hchi, hcast]
  by_cases hw : (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε)
  · rw [if_pos hw, if_pos hw]
    ring
  · rw [if_neg hw, if_neg hw]
    ring

/-- The `kept` term reindexed by its outer prime factor, with the recentring factor inside the
triple sum. -/
private lemma upperKept_weighted_reindex {ε Y : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q) {L K : ℕ} :
    ∑ m ∈ Finset.Ioc L K,
        ((Real.log (m : ℝ) / Real.log Y * upperKept ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)
      = ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          χ (p1 : ZMod q) *
            ∑ n ∈ Finset.Ioc (L / p1) (K / p1),
              (if (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε)
                then ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
                (∑ p2 ∈ n.primeFactors.filter
                (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                  (p2 : ℝ) < (p1 : ℝ)),
                ∑ p3 ∈ (n / p2).primeFactors.filter
                  (fun p3 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧
                    (p3 : ℝ) < (p2 : ℝ)),
                  if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((p1 : ℝ) * (n : ℝ)))
                    (Real.log (p2 : ℝ) / Real.log ((p1 : ℝ) * (n : ℝ))) (Real.log (p3 : ℝ) / Real.log ((p1 : ℝ) * (n : ℝ)))
                  then upperRough (n / p2 / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                χ (n : ZMod q)
                else 0) := by
  have hper : ∀ m ∈ Finset.Ioc L K,
      ((Real.log (m : ℝ) / Real.log Y * upperKept ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q) =
        ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
            then ((Real.log (m : ℝ) / Real.log Y *
          (∑ p2 ∈ (m / p1).primeFactors.filter
            (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2).primeFactors.filter
              (fun p3 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (m : ℝ))
                  (Real.log (p2 : ℝ) / Real.log (m : ℝ)) (Real.log (p3 : ℝ) / Real.log (m : ℝ))
                then upperRough (m / p1 / p2 / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) * χ (m : ZMod q)
            else 0) := by
    intro m hm
    obtain ⟨hmL, hmK⟩ := Finset.mem_Ioc.mp hm
    have hm0 : 0 < m := by omega
    have hset : m.primeFactors.filter
          (fun p : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (m : ℝ) ^ upperC4 ε)
        = ((Finset.Icc 2 K).filter Nat.Prime).filter
            (fun p1 => p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨hpp, hpd, -⟩, hW⟩
        exact ⟨⟨⟨hpp.two_le, (Nat.le_of_dvd hm0 hpd).trans hmK⟩, hpp⟩, hpd, hW⟩
      · rintro ⟨⟨⟨h2p, hpK⟩, hpp⟩, hpd, hW⟩
        exact ⟨⟨hpp, hpd, by omega⟩, hW⟩
    have hinner : upperKept ε (m : ℝ) m =
        ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
            then (∑ p2 ∈ (m / p1).primeFactors.filter
            (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2).primeFactors.filter
              (fun p3 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (m : ℝ))
                  (Real.log (p2 : ℝ) / Real.log (m : ℝ)) (Real.log (p3 : ℝ) / Real.log (m : ℝ))
                then upperRough (m / p1 / p2 / p3) (p3 : ℝ) else 0) else 0) := by
      unfold upperKept
      rw [hset, Finset.sum_filter]
    rw [hinner, Finset.mul_sum]
    rw [Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p1 _ => ?_
    by_cases h : (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      simp
  calc ∑ m ∈ Finset.Ioc L K,
        ((Real.log (m : ℝ) / Real.log Y * upperKept ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)
      = ∑ m ∈ Finset.Ioc L K, ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
            then ((Real.log (m : ℝ) / Real.log Y *
          (∑ p2 ∈ (m / p1).primeFactors.filter
            (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2).primeFactors.filter
              (fun p3 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (m : ℝ))
                  (Real.log (p2 : ℝ) / Real.log (m : ℝ)) (Real.log (p3 : ℝ) / Real.log (m : ℝ))
                then upperRough (m / p1 / p2 / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) * χ (m : ZMod q)
            else 0) := Finset.sum_congr rfl hper
    _ = ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          ∑ m ∈ Finset.Ioc L K,
            (if (p1 ∣ m ∧ ((m : ℝ) ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < (m : ℝ) ^ upperC4 ε))
              then ((Real.log (m : ℝ) / Real.log Y *
          (∑ p2 ∈ (m / p1).primeFactors.filter
            (fun p2 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2).primeFactors.filter
              (fun p3 : ℕ => (m : ℝ) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (m : ℝ))
                  (Real.log (p2 : ℝ) / Real.log (m : ℝ)) (Real.log (p3 : ℝ) / Real.log (m : ℝ))
                then upperRough (m / p1 / p2 / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) * χ (m : ZMod q)
              else 0) := Finset.sum_comm
    _ = ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          χ (p1 : ZMod q) *
            ∑ n ∈ Finset.Ioc (L / p1) (K / p1),
              (if (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε)
                then ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
                (∑ p2 ∈ n.primeFactors.filter
                (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                  (p2 : ℝ) < (p1 : ℝ)),
                ∑ p3 ∈ (n / p2).primeFactors.filter
                  (fun p3 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧
                    (p3 : ℝ) < (p2 : ℝ)),
                  if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((p1 : ℝ) * (n : ℝ)))
                    (Real.log (p2 : ℝ) / Real.log ((p1 : ℝ) * (n : ℝ))) (Real.log (p3 : ℝ) / Real.log ((p1 : ℝ) * (n : ℝ)))
                  then upperRough (n / p2 / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                χ (n : ZMod q)
                else 0) := by
        refine Finset.sum_congr rfl fun p1 hp1 => ?_
        exact upperKept_fibre_reindex (Y := Y) χ
          (le_trans (by norm_num) (Finset.mem_filter.mp hp1).2.two_le)


private lemma kept_inner_peel {ε Y : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q) {L' K' p1 : ℕ}
    (hp1 : 1 ≤ p1) :
    ∑ n ∈ Finset.Ioc L' K',
        (if (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
            (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) then
          ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
            (∑ p2 ∈ n.primeFactors.filter
              (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                (p2 : ℝ) < (p1 : ℝ)),
              (∑ p3 ∈ ((n / p2)).primeFactors.filter
              (fun p3 : ℕ => (((p1 : ℝ) * (n : ℝ))) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ)))) (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                then upperRough (((n / p2)) / p3) (p3 : ℝ) else 0)) : ℝ) : ℂ) *
            χ (n : ZMod q)
          else 0)
      = ∑ p2 ∈ (Finset.Icc 2 K').filter Nat.Prime,
          (if (p2 : ℝ) < (p1 : ℝ) then
            χ (p2 : ZMod q) *
              ∑ k ∈ Finset.Ioc (L' / p2) (K' / p2),
                (if ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                    (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
                    (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ))
                  then ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
                    (∑ p3 ∈ (k).primeFactors.filter
              (fun p3 : ℕ => ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ))) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ))))
                  (Real.log (p2 : ℝ) / Real.log ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))) (Real.log (p3 : ℝ) / Real.log ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ))))
                then upperRough ((k) / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                    χ (k : ZMod q)
                  else 0)
            else 0) := by
  have hone : ∀ n ∈ Finset.Ioc L' K',
      (∑ p2 ∈ n.primeFactors.filter
        (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)),
        (∑ p3 ∈ ((n / p2)).primeFactors.filter
              (fun p3 : ℕ => (((p1 : ℝ) * (n : ℝ))) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ)))) (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                then upperRough (((n / p2)) / p3) (p3 : ℝ) else 0))
      = ∑ p2 ∈ (Finset.Icc 2 K').filter Nat.Prime,
          (if (p2 ∣ n ∧ (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
            (p2 : ℝ) < (p1 : ℝ))) then
            (∑ p3 ∈ ((n / p2)).primeFactors.filter
              (fun p3 : ℕ => (((p1 : ℝ) * (n : ℝ))) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ)))) (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                then upperRough (((n / p2)) / p3) (p3 : ℝ) else 0) else 0) := by
    intro n hn
    obtain ⟨hnL, hnK⟩ := Finset.mem_Ioc.mp hn
    have hn0 : 0 < n := by omega
    have hset : n.primeFactors.filter
          (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ))
        = ((Finset.Icc 2 K').filter Nat.Prime).filter
            (fun p2 => p2 ∣ n ∧ (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
              (p2 : ℝ) < (p1 : ℝ))) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨hpp, hpd, -⟩, hW⟩
        exact ⟨⟨⟨hpp.two_le, (Nat.le_of_dvd hn0 hpd).trans hnK⟩, hpp⟩, hpd, hW⟩
      · rintro ⟨⟨⟨h2p, hpK⟩, hpp⟩, hpd, hW⟩
        exact ⟨⟨hpp, hpd, by omega⟩, hW⟩
    rw [hset, Finset.sum_filter]
  have hper : ∀ n ∈ Finset.Ioc L' K',
      (if (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) then
        ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
          (∑ p2 ∈ n.primeFactors.filter
            (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
              (p2 : ℝ) < (p1 : ℝ)),
            (∑ p3 ∈ ((n / p2)).primeFactors.filter
              (fun p3 : ℕ => (((p1 : ℝ) * (n : ℝ))) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ)))) (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                then upperRough (((n / p2)) / p3) (p3 : ℝ) else 0)) : ℝ) : ℂ) *
          χ (n : ZMod q)
        else 0)
      = ∑ p2 ∈ (Finset.Icc 2 K').filter Nat.Prime,
          (if ((((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) ∧
              p2 ∣ n ∧ (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                (p2 : ℝ) < (p1 : ℝ))) then
            ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
              (∑ p3 ∈ ((n / p2)).primeFactors.filter
              (fun p3 : ℕ => (((p1 : ℝ) * (n : ℝ))) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ)))) (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                then upperRough (((n / p2)) / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) *
              χ (n : ZMod q)
            else 0) := by
    intro n hn
    rw [hone n hn]
    by_cases hA : (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
        (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε)
    · rw [if_pos hA, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p2 _ => ?_
      by_cases hB : (p2 ∣ n ∧ (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
          (p2 : ℝ) < (p1 : ℝ)))
      · rw [if_pos hB, if_pos ⟨hA, hB⟩]
      · rw [if_neg hB, if_neg (fun h => hB h.2)]
        simp
    · rw [if_neg hA]
      refine (Finset.sum_eq_zero fun p2 _ => ?_).symm
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact hA h1
  rw [Finset.sum_congr rfl hper, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p2 hp2 => ?_
  have hp2P : p2.Prime := (Finset.mem_filter.mp hp2).2
  have hp2pos : 0 < p2 := hp2P.pos
  by_cases hlt : (p2 : ℝ) < (p1 : ℝ)
  · rw [if_pos hlt]
    have hsplit : ∀ n : ℕ,
        (if ((((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
            (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) ∧
            p2 ∣ n ∧ (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
              (p2 : ℝ) < (p1 : ℝ))) then
          ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
            (∑ p3 ∈ ((n / p2)).primeFactors.filter
              (fun p3 : ℕ => (((p1 : ℝ) * (n : ℝ))) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ)))) (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                then upperRough (((n / p2)) / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) *
            χ (n : ZMod q)
          else 0)
        = (if p2 ∣ n then
            (if ((((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) ∧
                (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                  (p2 : ℝ) < (p1 : ℝ))) then
              ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
                (∑ p3 ∈ ((n / p2)).primeFactors.filter
              (fun p3 : ℕ => (((p1 : ℝ) * (n : ℝ))) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ)))) (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                then upperRough (((n / p2)) / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                χ (n : ZMod q)
              else 0)
            else 0) := by
      intro n
      by_cases h : p2 ∣ n <;>
        by_cases h2 : ((((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
            (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) ∧
            (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ))) <;>
        simp [h, h2]
    rw [Finset.sum_congr rfl (fun n _ => hsplit n)]
    rw [Rough514.sum_dvd_reindex (le_trans (by norm_num) hp2P.two_le) L' K'
      (fun n => if ((((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) ∧
          (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ))) then
        ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
          (∑ p3 ∈ ((n / p2)).primeFactors.filter
              (fun p3 : ℕ => (((p1 : ℝ) * (n : ℝ))) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ)))) (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (n : ℝ))))
                then upperRough (((n / p2)) / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) *
          χ (n : ZMod q)
        else 0)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hdiv : (p2 * k) / p2 = k := Nat.mul_div_cancel_left k hp2pos
    have hchi : χ (((p2 * k : ℕ)) : ZMod q) = χ (p2 : ZMod q) * χ (k : ZMod q) := by
      push_cast
      rw [map_mul]
    have harg : ((p1 : ℝ) * (((p2 * k : ℕ)) : ℝ)) = ((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ) := by
      push_cast; ring
    have hrough : (∑ p3 ∈ (((p2 * k) / p2)).primeFactors.filter
              (fun p3 : ℕ => (((p1 : ℝ) * (((p2 * k : ℕ)) : ℝ))) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (((p2 * k : ℕ)) : ℝ))))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (((p2 * k : ℕ)) : ℝ)))) (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (((p2 * k : ℕ)) : ℝ))))
                then upperRough ((((p2 * k) / p2)) / p3) (p3 : ℝ) else 0)
        = (∑ p3 ∈ (k).primeFactors.filter
              (fun p3 : ℕ => ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ))) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ))))
                  (Real.log (p2 : ℝ) / Real.log ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))) (Real.log (p3 : ℝ) / Real.log ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ))))
                then upperRough ((k) / p3) (p3 : ℝ) else 0) := by
      rw [hdiv, harg]
    have hlogeq : Real.log ((p1 : ℝ) * (((p2 * k : ℕ)) : ℝ)) / Real.log Y =
        Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y := by rw [harg]
    have hcond : ((((p1 : ℝ) * (((p2 * k : ℕ)) : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < ((p1 : ℝ) * (((p2 * k : ℕ)) : ℝ)) ^ upperC4 ε) ∧
          (((p1 : ℝ) * (((p2 * k : ℕ)) : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p1 : ℝ)))
        ↔ ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
          (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
          (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ)) := by
      rw [harg]
      exact ⟨fun h => ⟨h.1.1, h.1.2, h.2.1⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2, hlt⟩⟩
    rw [hrough, hlogeq, hchi]
    by_cases hc : ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
        (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
        (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ))
    · rw [if_pos (hcond.mpr hc), if_pos hc]
      ring
    · rw [if_neg (fun h => hc (hcond.mp h)), if_neg hc]
      ring
  · rw [if_neg hlt]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [if_neg]
    rintro ⟨-, -, -, h4⟩
    exact hlt h4


/-- The first cofactor is never in the page 53 window: the product of three decreasing primes is at
most the cube of the first and `3 c4 ≤ 1`. This is what lets a `kept` fibre whose interval of
cofactors starts at zero be read as the same fibre starting at one. -/
private lemma kept_base_not_in_window {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    {p1 p2 p3 : ℕ} (hp1 : 1 ≤ p1) (hp21 : p2 ≤ p1) (hp31 : p3 ≤ p1) :
    ¬ ((p1 : ℝ) < ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * ((1 : ℕ) : ℝ)) ^ upperC4 ε) := by
  have hc4 : 0 < upperC4 ε := upperC4_pos hε8
  have hc4hi : upperC4 ε ≤ 133 / 500 := upperC4_le_133_500 hε hε8
  have hp1R : (1 : ℝ) ≤ (p1 : ℝ) := by exact_mod_cast hp1
  have hpos : (0 : ℝ) < (p1 : ℝ) := by linarith
  have hprod : ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * ((1 : ℕ) : ℝ)) ≤ (p1 : ℝ) ^ 3 := by
    have h2 : (p2 : ℝ) ≤ (p1 : ℝ) := by exact_mod_cast hp21
    have h3 : (p3 : ℝ) ≤ (p1 : ℝ) := by exact_mod_cast hp31
    have h3' : (0 : ℝ) ≤ (p3 : ℝ) := by positivity
    have h4 : (p1 : ℝ) * (p2 : ℝ) ≤ (p1 : ℝ) * (p1 : ℝ) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h5 : (p1 : ℝ) * (p2 : ℝ) * (p3 : ℝ) ≤ (p1 : ℝ) * (p1 : ℝ) * (p1 : ℝ) :=
      mul_le_mul h4 h3 h3' (by positivity)
    calc (((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * ((1 : ℕ) : ℝ)
        = (p1 : ℝ) * (p2 : ℝ) * (p3 : ℝ) := by ring
      _ ≤ (p1 : ℝ) * (p1 : ℝ) * (p1 : ℝ) := h5
      _ = (p1 : ℝ) ^ 3 := by ring
  have h3c4 : 3 * upperC4 ε ≤ 1 := by nlinarith
  have h1 : ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * ((1 : ℕ) : ℝ)) ^ upperC4 ε ≤
      ((p1 : ℝ) ^ 3) ^ upperC4 ε := Real.rpow_le_rpow (by positivity) hprod hc4.le
  have h2 : ((p1 : ℝ) ^ 3) ^ upperC4 ε = (p1 : ℝ) ^ (3 * upperC4 ε) := by
    rw [show ((p1 : ℝ) ^ 3) = (p1 : ℝ) ^ (3 : ℝ) from (Real.rpow_natCast _ 3).symm,
      Real.rpow_mul hpos.le]
  have h3 : (p1 : ℝ) ^ (3 * upperC4 ε) ≤ (p1 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hp1R h3c4
  have h4 : ((p1 : ℝ) ^ (1 : ℝ)) = (p1 : ℝ) := Real.rpow_one _
  intro hcon
  rw [h2] at h1
  rw [h4] at h3
  linarith

/-- The triple reciprocal sum over a decreasing triple of primes costs three logarithms. -/
private lemma triple_inv_sum_le (K : ℕ) :
    ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
      (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
            (if (p2 : ℝ) < (p1 : ℝ) then
              ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
                (if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0)
              else 0))
      ≤ (K : ℝ) * (1 + Real.log (K : ℝ)) ^ 3 := by
  have hlogK : (0 : ℝ) ≤ Real.log (K : ℝ) := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0]; simp
    · exact Real.log_nonneg (by exact_mod_cast hpos)
  have hL1 : (0 : ℝ) ≤ 1 + Real.log (K : ℝ) := by linarith
  have hinn : ∀ p1 p2 : ℕ,
      (∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
        (if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0))
      ≤ (((K / p1) / p2 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)) := by
    intro p1 p2
    have h1 : (∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
        (if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0))
        ≤ ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
            ((((K / p1) / p2) / p3 : ℕ) : ℝ) := by
      refine Finset.sum_le_sum fun p3 _ => ?_
      by_cases hc : (p3 : ℝ) < (p2 : ℝ)
      · rw [if_pos hc]
      · rw [if_neg hc]
        exact Nat.cast_nonneg _
    have h2 : (∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
        ((((K / p1) / p2) / p3 : ℕ) : ℝ))
        ≤ ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
            (((K / p1) / p2 : ℕ) : ℝ) / (p3 : ℝ) := by
      refine Finset.sum_le_sum fun p3 _ => ?_
      exact Nat.cast_div_le (α := ℝ)
    have h3 : (∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
        (((K / p1) / p2 : ℕ) : ℝ) / (p3 : ℝ))
        = (((K / p1) / p2 : ℕ) : ℝ) *
            ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime, (1 : ℝ) / (p3 : ℝ) := by
      rw [Finset.mul_sum]
      try refine Finset.sum_congr rfl fun p3 _ => by ring
    have h4 : (∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime, (1 : ℝ) / (p3 : ℝ))
        ≤ 1 + Real.log (K : ℝ) := by
      have hsub : (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime ⊆
          (Finset.Icc 2 K).filter Nat.Prime := by
        intro p hp
        obtain ⟨hpI, hpP⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp2, hpk⟩ := Finset.mem_Icc.mp hpI
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp2,
          le_trans hpk (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))⟩, hpP⟩
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) ?_
      exact prime_inv_sum_le K
    calc (∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
          (if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0))
        ≤ ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
            ((((K / p1) / p2) / p3 : ℕ) : ℝ) := h1
      _ ≤ ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
            (((K / p1) / p2 : ℕ) : ℝ) / (p3 : ℝ) := h2
      _ = (((K / p1) / p2 : ℕ) : ℝ) *
            ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime, (1 : ℝ) / (p3 : ℝ) := h3
      _ ≤ (((K / p1) / p2 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
  have hmid : ∀ p1 : ℕ,
      (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
        (if (p2 : ℝ) < (p1 : ℝ) then
              ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
                (if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0)
              else 0))
      ≤ ((K / p1 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)) ^ 2 := by
    intro p1
    have h1 : (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
        (if (p2 : ℝ) < (p1 : ℝ) then
              ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
                (if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0)
              else 0))
        ≤ ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
            (((K / p1) / p2 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)) := by
      refine Finset.sum_le_sum fun p2 _ => ?_
      by_cases hc : (p2 : ℝ) < (p1 : ℝ)
      · rw [if_pos hc]
        exact hinn p1 p2
      · rw [if_neg hc]
        positivity
    have h2 : (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
        (((K / p1) / p2 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)))
        ≤ ((K / p1 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)) * (1 + Real.log (K : ℝ)) := by
      have hdrop : (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
          (((K / p1) / p2 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)))
          ≤ ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
              ((K / p1 : ℕ) : ℝ) / (p2 : ℝ) * (1 + Real.log (K : ℝ)) := by
        refine Finset.sum_le_sum fun p2 _ => ?_
        have h5 : (((K / p1) / p2 : ℕ) : ℝ) ≤ ((K / p1 : ℕ) : ℝ) / (p2 : ℝ) :=
          Nat.cast_div_le (α := ℝ)
        exact mul_le_mul_of_nonneg_right h5 hL1
      have h6 : (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
          ((K / p1 : ℕ) : ℝ) / (p2 : ℝ) * (1 + Real.log (K : ℝ)))
          = ((K / p1 : ℕ) : ℝ) *
              (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime, (1 : ℝ) / (p2 : ℝ)) *
                (1 + Real.log (K : ℝ)) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p2 _ => by ring
      have h7 : (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime, (1 : ℝ) / (p2 : ℝ))
          ≤ 1 + Real.log (K : ℝ) := by
        have hsub : (Finset.Icc 2 (K / p1)).filter Nat.Prime ⊆
            (Finset.Icc 2 K).filter Nat.Prime := by
          intro p hp
          obtain ⟨hpI, hpP⟩ := Finset.mem_filter.mp hp
          obtain ⟨hp2, hpk⟩ := Finset.mem_Icc.mp hpI
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp2,
            le_trans hpk (Nat.div_le_self _ _)⟩, hpP⟩
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) ?_
        exact prime_inv_sum_le K
      calc (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
            (((K / p1) / p2 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)))
          ≤ ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
              ((K / p1 : ℕ) : ℝ) / (p2 : ℝ) * (1 + Real.log (K : ℝ)) := hdrop
        _ = ((K / p1 : ℕ) : ℝ) *
              (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime, (1 : ℝ) / (p2 : ℝ)) *
                (1 + Real.log (K : ℝ)) := h6
        _ ≤ ((K / p1 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)) * (1 + Real.log (K : ℝ)) := by
            have h8 : (0 : ℝ) ≤ ((K / p1 : ℕ) : ℝ) := by positivity
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h7 h8) hL1
    calc (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
          (if (p2 : ℝ) < (p1 : ℝ) then
              ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
                (if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0)
              else 0))
        ≤ ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
            (((K / p1) / p2 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)) := h1
      _ ≤ ((K / p1 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)) * (1 + Real.log (K : ℝ)) := h2
      _ = ((K / p1 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)) ^ 2 := by ring
  refine le_trans (Finset.sum_le_sum fun p1 _ => hmid p1) ?_
  have h9 : (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
      ((K / p1 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)) ^ 2)
      ≤ (K : ℝ) * (1 + Real.log (K : ℝ)) ^ 2 * (1 + Real.log (K : ℝ)) := by
    have hdrop : (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
        ((K / p1 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)) ^ 2)
        ≤ ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
            (K : ℝ) / (p1 : ℝ) * (1 + Real.log (K : ℝ)) ^ 2 := by
      refine Finset.sum_le_sum fun p1 _ => ?_
      have h5 : ((K / p1 : ℕ) : ℝ) ≤ (K : ℝ) / (p1 : ℝ) := Nat.cast_div_le (α := ℝ)
      exact mul_le_mul_of_nonneg_right h5 (by positivity)
    have h6 : (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
        (K : ℝ) / (p1 : ℝ) * (1 + Real.log (K : ℝ)) ^ 2)
        = (K : ℝ) * (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, (1 : ℝ) / (p1 : ℝ)) *
            (1 + Real.log (K : ℝ)) ^ 2 := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p1 _ => by ring
    have h7 : (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, (1 : ℝ) / (p1 : ℝ)) ≤ 1 + Real.log (K : ℝ) :=
      prime_inv_sum_le K
    calc (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
          ((K / p1 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)) ^ 2)
        ≤ ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
            (K : ℝ) / (p1 : ℝ) * (1 + Real.log (K : ℝ)) ^ 2 := hdrop
      _ = (K : ℝ) * (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, (1 : ℝ) / (p1 : ℝ)) *
            (1 + Real.log (K : ℝ)) ^ 2 := h6
      _ ≤ (K : ℝ) * (1 + Real.log (K : ℝ)) * (1 + Real.log (K : ℝ)) ^ 2 := by
          have h8 : (0 : ℝ) ≤ (K : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h7 h8) (by positivity)
      _ = (K : ℝ) * (1 + Real.log (K : ℝ)) ^ 2 * (1 + Real.log (K : ℝ)) := by ring
  calc (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
      ((K / p1 : ℕ) : ℝ) * (1 + Real.log (K : ℝ)) ^ 2)
      ≤ (K : ℝ) * (1 + Real.log (K : ℝ)) ^ 2 * (1 + Real.log (K : ℝ)) := h9
    _ = (K : ℝ) * (1 + Real.log (K : ℝ)) ^ 3 := by ring

set_option maxHeartbeats 4000000 in
private lemma kept_third_peel {ε Y : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q) {L' K' p1 p2 : ℕ}
    (hp1 : 1 ≤ p1) (hp2 : 1 ≤ p2) :
    ∑ k ∈ Finset.Ioc L' K',
        (if ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
            (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
            (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ)) then
          ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
            (∑ p3 ∈ k.primeFactors.filter
              (fun p3 : ℕ => (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧
                (p3 : ℝ) < (p2 : ℝ)),
              if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                  (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                then upperRough (k / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) *
            χ (k : ZMod q)
          else 0)
      = ∑ p3 ∈ (Finset.Icc 2 K').filter Nat.Prime,
          (if (p3 : ℝ) < (p2 : ℝ) then
            χ (p3 : ZMod q) *
              ∑ j ∈ Finset.Ioc (L' / p3) (K' / p3),
                (if ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                    (p1 : ℝ) < ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ)) ^ upperC4 ε ∧
                    ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) then
                  (if upperPrimeCovered ε (Real.log (p1 : ℝ) /
                        Real.log ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ)))
                      (Real.log (p2 : ℝ) / Real.log ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ)))
                      (Real.log (p3 : ℝ) / Real.log ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ)))
                    then ((Real.log ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ)) / Real.log Y *
                      upperRough j (p3 : ℝ) : ℝ) : ℂ) * χ (j : ZMod q)
                    else 0)
                  else 0)
            else 0) := by
  have hone : ∀ k ∈ Finset.Ioc L' K',
      (∑ p3 ∈ k.primeFactors.filter
        (fun p3 : ℕ => (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧
          (p3 : ℝ) < (p2 : ℝ)),
        if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                  (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
          then upperRough (k / p3) (p3 : ℝ) else 0)
      = ∑ p3 ∈ (Finset.Icc 2 K').filter Nat.Prime,
          (if (p3 ∣ k ∧ ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ))) then
            (if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                  (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
              then upperRough (k / p3) (p3 : ℝ) else 0) else 0) := by
    intro k hk
    obtain ⟨hkL, hkK⟩ := Finset.mem_Ioc.mp hk
    have hk0 : 0 < k := by omega
    have hset : k.primeFactors.filter
          (fun p3 : ℕ => (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧
            (p3 : ℝ) < (p2 : ℝ))
        = ((Finset.Icc 2 K').filter Nat.Prime).filter
            (fun p3 => p3 ∣ k ∧ ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ))) := by
      ext p3
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨hpp, hpd, -⟩, hW⟩
        exact ⟨⟨⟨hpp.two_le, (Nat.le_of_dvd hk0 hpd).trans hkK⟩, hpp⟩, hpd, hW⟩
      · rintro ⟨⟨⟨h2p, hpK⟩, hpp⟩, hpd, hW⟩
        exact ⟨⟨hpp, hpd, by omega⟩, hW⟩
    rw [hset, Finset.sum_filter]
  have hper : ∀ k ∈ Finset.Ioc L' K',
      (if ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
            (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
            (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ)) then
        ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
          (∑ p3 ∈ k.primeFactors.filter
            (fun p3 : ℕ => (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧
              (p3 : ℝ) < (p2 : ℝ)),
            if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                  (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
              then upperRough (k / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) *
          χ (k : ZMod q)
        else 0)
      = ∑ p3 ∈ (Finset.Icc 2 K').filter Nat.Prime,
          (if p3 ∣ k then
            (if ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
                (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ))) then
              (if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                  (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                then ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
                  upperRough (k / p3) (p3 : ℝ) : ℝ) : ℂ) * χ (k : ZMod q)
                else 0)
            else 0)
          else 0) := by
    intro k hk
    rw [hone k hk]
    by_cases hW : ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
            (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
            (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ))
    · rw [if_pos hW, Complex.ofReal_mul, Complex.ofReal_sum, mul_assoc, Finset.sum_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun p3 _ => ?_
      by_cases hd : p3 ∣ k
      · rw [if_pos hd]
        by_cases hB : ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ))
        · have hc1 : (p3 ∣ k ∧ ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ))) := ⟨hd, hB⟩
          have hc2 : ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
                (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ))) := ⟨hW.1, hW.2.1, hW.2.2, hB.1, hB.2⟩
          rw [if_pos hc1, if_pos hc2]
          by_cases hcov : upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                  (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
          · rw [if_pos hcov, if_pos hcov]
            push_cast
            ring
          · rw [if_neg hcov, if_neg hcov]
            push_cast
            ring
        · have hc1 : ¬ (p3 ∣ k ∧ ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ))) := fun h => hB h.2
          have hc2 : ¬ ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
                (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ))) := fun h => hB h.2.2.2
          rw [if_neg hc1, if_neg hc2]
          push_cast
          ring
      · have hc1 : ¬ (p3 ∣ k ∧ ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ))) := fun h => hd h.1
        rw [if_neg hd, if_neg hc1]
        push_cast
        ring
    · rw [if_neg hW]
      refine (Finset.sum_eq_zero fun p3 _ => ?_).symm
      by_cases hd : p3 ∣ k
      · rw [if_pos hd]
        have hc2 : ¬ ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
                (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ))) :=
          fun h => hW ⟨h.1, h.2.1, h.2.2.1⟩
        rw [if_neg hc2]
      · rw [if_neg hd]
  rw [Finset.sum_congr rfl hper, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p3 hp3 => ?_
  have hp3P : p3.Prime := (Finset.mem_filter.mp hp3).2
  have hp3one : 1 ≤ p3 := le_trans (by norm_num) hp3P.two_le
  have hp3pos : 0 < p3 := hp3P.pos
  by_cases hlt : (p3 : ℝ) < (p2 : ℝ)
  · rw [if_pos hlt]
    rw [Rough514.sum_dvd_reindex hp3one L' K'
      (fun k => if ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
                (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ))) then
        (if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                  (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                  (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
          then ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
            upperRough (k / p3) (p3 : ℝ) : ℝ) : ℂ) * χ (k : ZMod q)
          else 0)
        else 0)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hdiv : (p3 * j) / p3 = j := Nat.mul_div_cancel_left j hp3pos
    have harg : ((p1 : ℝ) * (p2 : ℝ)) * (((p3 * j : ℕ)) : ℝ) =
        (((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ) := by
      push_cast
      ring
    have hchi : χ (((p3 * j : ℕ)) : ZMod q) = χ (p3 : ZMod q) * χ (j : ZMod q) := by
      push_cast
      rw [map_mul]
    rw [hdiv, harg, hchi]
    set D : ℝ := (((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ) with hD
    have hcovD : upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log D)
        (Real.log (p2 : ℝ) / Real.log D) (Real.log (p3 : ℝ) / Real.log D)
        ↔ upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log D)
          (Real.log (p2 : ℝ) / Real.log D) (Real.log (p3 : ℝ) / Real.log D) := Iff.rfl
    by_cases hc3 : (D ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < D ^ upperC4 ε ∧
      D ^ upperC1 ε ≤ (p3 : ℝ))
    · have hL : (D ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < D ^ upperC4 ε ∧
          D ^ upperC1 ε ≤ (p2 : ℝ) ∧ (D ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ))) :=
        ⟨hc3.1, hc3.2.1, le_trans hc3.2.2 (le_of_lt hlt), hc3.2.2, hlt⟩
      rw [if_pos hL, if_pos hc3]
      by_cases hcov : upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log D)
          (Real.log (p2 : ℝ) / Real.log D) (Real.log (p3 : ℝ) / Real.log D)
      · rw [if_pos hcov, if_pos hcov]
        push_cast
        ring
      · rw [if_neg hcov, if_neg hcov]
        push_cast
        ring
    · have hL : ¬ (D ^ upperC1 ε ≤ (p1 : ℝ) ∧ (p1 : ℝ) < D ^ upperC4 ε ∧
          D ^ upperC1 ε ≤ (p2 : ℝ) ∧ (D ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ))) :=
        fun h => hc3 ⟨h.1, h.2.1, h.2.2.2.1⟩
      rw [if_neg hL, if_neg hc3]
      push_cast
      ring
  · rw [if_neg hlt]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hd : p3 ∣ k
    · rw [if_pos hd]
      have hc2 : ¬ ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
                (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧ (p3 : ℝ) < (p2 : ℝ))) := fun h => hlt h.2.2.2.2
      rw [if_neg hc2]
    · rw [if_neg hd]


/-- A sum over the cofactors starting at zero is the sum starting at one, once the cofactor one does
not contribute. -/
private lemma sum_Ioc_zero_eq_one {b : ℕ} {f : ℕ → ℂ} (h1 : f 1 = 0) :
    ∑ j ∈ Finset.Ioc 0 b, f j = ∑ j ∈ Finset.Ioc 1 b, f j := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · rw [hb]
    simp
  · refine (Finset.sum_subset (s₁ := Finset.Ioc 1 b) (s₂ := Finset.Ioc 0 b) ?_ ?_).symm
    · intro x hx
      exact Finset.mem_Ioc.mpr
        ⟨lt_trans Nat.zero_lt_one (Finset.mem_Ioc.mp hx).1, (Finset.mem_Ioc.mp hx).2⟩
    · intro x hx hxs
      have hx1 : x = 1 := by
        have h1' : 0 < x := (Finset.mem_Ioc.mp hx).1
        have h2' : ¬ (1 < x) := fun h =>
          hxs (Finset.mem_Ioc.mpr ⟨h, (Finset.mem_Ioc.mp hx).2⟩)
        omega
      subst hx1
      exact h1

/-- A sum whose summand vanishes throughout has norm zero. -/
private lemma norm_sum_eq_zero_of_forall {s : Finset ℕ} {f : ℕ → ℂ}
    (h : ∀ x ∈ s, f x = 0) : ‖∑ x ∈ s, f x‖ = 0 := by
  rw [Finset.sum_eq_zero h, norm_zero]

/-- A cofactor of a `kept` triple window is large: the recentred product `p1 p2 p3 j` exceeds `Y`. -/
private lemma kept_cofactor_gt {Y : ℝ} {L p1 p2 p3 j b : ℕ} (hp1 : p1.Prime)
    (hp2 : p2.Prime) (hp3 : p3.Prime) (hLf : ⌊Y⌋₊ ≤ L)
    (hj : j ∈ Finset.Ioc (((L / p1) / p2) / p3) b) :
    (Y : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ) := by
  have h3 : L < p1 * (p2 * (p3 * j)) := by
    have h4 : (L / p1 / p2) / p3 + 1 ≤ j := (Finset.mem_Ioc.mp hj).1
    have h6 : L / p1 / p2 < p3 * (L / p1 / p2 / p3 + 1) := by
      have h7 : p3 * (L / p1 / p2 / p3) + (L / p1 / p2) % p3 = L / p1 / p2 :=
        Nat.div_add_mod _ _
      have h8 : (L / p1 / p2) % p3 < p3 := Nat.mod_lt _ hp3.pos
      have h9 : p3 * (L / p1 / p2 / p3 + 1) = p3 * (L / p1 / p2 / p3) + p3 := by ring
      omega
    have h10 : L / p1 / p2 < p3 * j := by
      have h5 : p3 * (L / p1 / p2 / p3 + 1) ≤ p3 * j := Nat.mul_le_mul_left _ h4
      omega
    have h12 : L / p1 < p2 * (L / p1 / p2 + 1) := by
      have h13 : p2 * (L / p1 / p2) + (L / p1) % p2 = L / p1 := Nat.div_add_mod _ _
      have h14 : (L / p1) % p2 < p2 := Nat.mod_lt _ hp2.pos
      have h15 : p2 * (L / p1 / p2 + 1) = p2 * (L / p1 / p2) + p2 := by ring
      omega
    have h16 : L / p1 < p2 * (p3 * j) := by
      have h11 : p2 * (L / p1 / p2 + 1) ≤ p2 * (p3 * j) := Nat.mul_le_mul_left _ (by omega)
      omega
    have h18 : L < p1 * (L / p1 + 1) := by
      have h19 : p1 * (L / p1) + L % p1 = L := Nat.div_add_mod _ _
      have h20 : L % p1 < p1 := Nat.mod_lt _ hp1.pos
      have h21 : p1 * (L / p1 + 1) = p1 * (L / p1) + p1 := by ring
      omega
    have h17 : p1 * (L / p1 + 1) ≤ p1 * (p2 * (p3 * j)) := Nat.mul_le_mul_left _ (by omega)
    exact lt_of_lt_of_le h18 h17
  have h22 : ((p1 * (p2 * (p3 * j)) : ℕ) : ℝ) = (((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ) := by
    push_cast
    ring
  have h24 : (L : ℝ) < ((p1 * (p2 * (p3 * j)) : ℕ) : ℝ) := by exact_mod_cast h3
  rw [h22] at h24
  have h2 : (⌊Y⌋₊ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLf
  have h25 : Y < (⌊Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Y
  have h26 : (L : ℝ) + 1 ≤ (((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ) := by
    have h27 : ((L + 1 : ℕ) : ℝ) ≤ ((p1 * (p2 * (p3 * j)) : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt h3
    rw [h22] at h27
    push_cast at h27
    linarith
  linarith [h24, h26, h2, h25]

set_option maxHeartbeats 200000000 in
/-- The `kept` term of the self scaled upper coefficient at a fixed scale. The `p1` peel is
`upperKept_weighted_reindex`, the `p2` peel `kept_inner_peel`, the `p3` peel `kept_third_peel`. After
the three peels one fibre is one triple of primes, on which the covering indicator is constant and
the sifted level is the third prime itself, so the Abel bound `kept_fibre_le` of the fixed level rough
character sum applies with no ladder decomposition. The three reciprocal sums over the decreasing
primes cost three logarithms, which the `A + 6` shift absorbs. -/
private lemma upperKept_self_bound {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, C ≤ Y → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log Y ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ L K : ℕ, 1 ≤ L → (L : ℝ) ≤ Y → ⌊Y⌋₊ ≤ L → (K : ℝ) ≤ 2 * Y →
        ‖∑ m ∈ Finset.Ioc L K,
          ((Real.log (m : ℝ) / Real.log Y * upperKept ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
          C * Y * Real.log Y ^ (-A) := by
  intro A hA
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Rough514.rough_character_interval (c := upperC1 ε / 2) (A := A + 6)
      (by linarith [upperC1_pos hε8]) (by linarith)
  refine ⟨max (23544 * C0) 4, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) (le_max_right _ _)
  intro Y hY q hq hqA χ hχ L K hL hLY hLf hKY
  have hCl : (max (23544 * C0) 4 : ℝ) ≤ Y := hY
  have hC4 : (4 : ℝ) ≤ Y := le_trans (le_max_right _ _) hCl
  have hY2 : 2 ≤ Y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hC0Y : C0 ≤ 2 * Y := by
    have h1 : (0 : ℝ) ≤ C0 := hC0pos.le
    have h2 : C0 ≤ 23544 * C0 := by nlinarith
    have h3 : 23544 * C0 ≤ max (23544 * C0) 4 := le_max_left _ _
    linarith
  have hlogY1 : (1 : ℝ) ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le hY0]
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hc1 : 0 < upperC1 ε := upperC1_pos hε8
  have hc1le : upperC1 ε ≤ 1 := upperC1_le_one hε
  have hX : (2 * Y) ^ (upperC1 ε / 2) ≤ Y ^ upperC1 ε := level_ge hc1 hY2
  set z : ℕ := ⌈(2 * Y) ^ (upperC1 ε / 2)⌉₊ with hzdef
  set Pmax : ℕ := ⌈(K : ℝ) ^ upperC1 ε⌉₊ with hPdef
  have hzX : (2 * Y) ^ (upperC1 ε / 2) ≤ (z : ℝ) := Nat.le_ceil _
  have hz1 : 1 ≤ z := by
    have h1 : (1 : ℝ) ≤ (2 * Y) ^ (upperC1 ε / 2) := by
      have h2 : (1 : ℝ) ≤ 2 * Y := by linarith
      calc (1 : ℝ) = (1 : ℝ) ^ (upperC1 ε / 2) := (Real.one_rpow _).symm
        _ ≤ (2 * Y) ^ (upperC1 ε / 2) := Real.rpow_le_rpow (by norm_num) h2 (by positivity)
    have h2 : (1 : ℝ) ≤ (z : ℝ) := by
      rw [hzdef]
      exact le_trans h1 (Nat.le_ceil _)
    exact_mod_cast h2
  have hlogX : 0 < Real.log (2 * Y) := Real.log_pos (by linarith)
  have hqA' : (q : ℝ) ≤ Real.log (2 * Y) ^ (A + 6) := by
    have h1 : Real.log Y ≤ Real.log (2 * Y) := Real.log_le_log hY0 (by linarith)
    have h3 : Real.log Y ^ A ≤ Real.log (2 * Y) ^ (A + 6) := by
      have h4 : Real.log Y ^ A ≤ Real.log (2 * Y) ^ A :=
        Real.rpow_le_rpow hlogY.le h1 hA.le
      have h5 : Real.log (2 * Y) ^ A ≤ Real.log (2 * Y) ^ (A + 6) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      linarith
    linarith
  have hpre : ∀ (ζ a b : ℕ), (2 * Y) ^ (upperC1 ε / 2) ≤ (ζ : ℝ) → 1 ≤ a → (b : ℝ) ≤ 2 * Y →
      ‖∑ n ∈ Finset.Ioc a b, ((Task308.roughIndicator n ζ : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
        C0 * (b : ℝ) * Real.log (2 * Y) ^ (-(A + 6)) := by
    intro ζ a b hζ ha hb
    exact hC0 (2 * Y) hC0Y q hq hqA' χ hχ ζ hζ a b ha hb
  -- the three logarithms that the two reciprocal sums cost
  have hlogK0 : (0 : ℝ) ≤ Real.log (K : ℝ) := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0]; simp
    · exact Real.log_nonneg (by exact_mod_cast hpos)
  have hlogK : Real.log (K : ℝ) ≤ 2 * Real.log Y := by
    have h1 : Real.log (K : ℝ) ≤ Real.log (2 * Y) := by
      rcases Nat.eq_zero_or_pos K with h0 | hpos
      · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith
      · exact Real.log_le_log (by exact_mod_cast hpos) hKY
    have h2 : Real.log (2 * Y) ≤ 2 * Real.log Y := by
      rw [Real.log_mul (by norm_num) hY0.ne']
      have h3 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY2
      linarith
    linarith
  have hlogP0 : (0 : ℝ) ≤ Real.log (Pmax : ℝ) := by
    rcases Nat.eq_zero_or_pos Pmax with h0 | hpos
    · rw [h0]; simp
    · exact Real.log_nonneg (by exact_mod_cast hpos)
  have hlogP : Real.log (Pmax : ℝ) ≤ 2 * Real.log Y := by
    have hKc1 : (K : ℝ) ^ upperC1 ε ≤ (K : ℝ) := by
      rcases Nat.lt_or_ge K 2 with h | h
      · interval_cases K
        · rw [Nat.cast_zero, Real.zero_rpow hc1.ne']
        · rw [Nat.cast_one, Real.one_rpow]
      · have h2 : (1 : ℝ) ≤ (K : ℝ) := by
          exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 2) h)
        calc (K : ℝ) ^ upperC1 ε ≤ (K : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h2 hc1le
          _ = (K : ℝ) := Real.rpow_one _
    have h1 : (Pmax : ℝ) ≤ (K : ℝ) := by
      rw [hPdef]
      have h2 : ⌈(K : ℝ) ^ upperC1 ε⌉₊ ≤ K := Nat.ceil_le.mpr hKc1
      exact_mod_cast h2
    rcases Nat.eq_zero_or_pos Pmax with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith
    · exact le_trans (Real.log_le_log (by exact_mod_cast hpos) h1) hlogK
  rw [upperKept_weighted_reindex (Y := Y) χ]
  refine le_trans (norm_sum_le _ _) ?_
  have hinner : ∀ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime,
      ‖χ (p1 : ZMod q) *
        ∑ n ∈ Finset.Ioc (L / p1) (K / p1),
          (if (((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
              (p1 : ℝ) < ((p1 : ℝ) * (n : ℝ)) ^ upperC4 ε) then
            ((Real.log ((p1 : ℝ) * (n : ℝ)) / Real.log Y *
              (∑ p2 ∈ n.primeFactors.filter
                (fun p2 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ) ∧
                  (p2 : ℝ) < (p1 : ℝ)),
                ∑ p3 ∈ (n / p2).primeFactors.filter
                  (fun p3 : ℕ => ((p1 : ℝ) * (n : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧
                    (p3 : ℝ) < (p2 : ℝ)),
                  if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((p1 : ℝ) * (n : ℝ)))
                    (Real.log (p2 : ℝ) / Real.log ((p1 : ℝ) * (n : ℝ))) (Real.log (p3 : ℝ) / Real.log ((p1 : ℝ) * (n : ℝ)))
                  then upperRough (n / p2 / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) *
              χ (n : ZMod q)
          else 0)‖ ≤ 436 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
            (if (p2 : ℝ) < (p1 : ℝ) then
              ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
                (if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0)
              else 0)) := by
    intro p1 hp1mem
    obtain ⟨hp1K, hp1P⟩ := Finset.mem_filter.mp hp1mem
    have hp1 : p1.Prime := hp1P
    have hp1one : 1 ≤ p1 := le_trans (by norm_num) hp1.two_le
    refine le_trans (norm_mul_le _ _) ?_
    refine le_trans (mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ (p1 : ZMod q))
      (norm_nonneg _)) ?_
    rw [one_mul]
    rw [kept_inner_peel (Y := Y) (L' := L / p1) (K' := K / p1) χ hp1one]
    refine le_trans (norm_sum_le _ _) ?_
    have hper : ∀ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
        ‖(if (p2 : ℝ) < (p1 : ℝ) then
            χ (p2 : ZMod q) *
              ∑ k ∈ Finset.Ioc ((L / p1) / p2) ((K / p1) / p2),
                (if ((((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                    (p1 : ℝ) < (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC4 ε ∧
                    (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p2 : ℝ)) then
                  ((Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) / Real.log Y *
                    (∑ p3 ∈ k.primeFactors.filter
                      (fun p3 : ℕ => (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ) ∧
                        (p3 : ℝ) < (p2 : ℝ)),
                      if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                          (Real.log (p2 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                          (Real.log (p3 : ℝ) / Real.log (((p1 : ℝ) * (p2 : ℝ)) * (k : ℝ)))
                        then upperRough (k / p3) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                    χ (k : ZMod q)
                  else 0)
            else 0)‖ ≤ 436 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * ((if (p2 : ℝ) < (p1 : ℝ) then
              ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
                (if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0)
              else 0)) := by
      intro p2 hp2mem
      obtain ⟨hp2K, hp2P⟩ := Finset.mem_filter.mp hp2mem
      have hp2one : 1 ≤ p2 := le_trans (by norm_num) hp2P.two_le
      by_cases hlt21 : (p2 : ℝ) < (p1 : ℝ)
      · rw [if_pos hlt21, if_pos hlt21]
        refine le_trans (norm_mul_le _ _) ?_
        refine le_trans (mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ (p2 : ZMod q))
          (norm_nonneg _)) ?_
        rw [one_mul]
        rw [kept_third_peel (Y := Y) (L' := (L / p1) / p2) (K' := (K / p1) / p2) χ hp1one hp2one]
        refine le_trans (norm_sum_le _ _) ?_
        have hper3 : ∀ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
            ‖(if (p3 : ℝ) < (p2 : ℝ) then
                χ (p3 : ZMod q) *
                  ∑ j ∈ Finset.Ioc (((L / p1) / p2) / p3) (((K / p1) / p2) / p3),
                    (if (((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ)) ^ upperC1 ε ≤ (p1 : ℝ) ∧
                          (p1 : ℝ) < ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ)) ^ upperC4 ε ∧
                          ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ)) ^ upperC1 ε ≤ (p3 : ℝ)) then
                      (if upperPrimeCovered ε (Real.log (p1 : ℝ) / Real.log ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ)))
                          (Real.log (p2 : ℝ) / Real.log ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ)))
                          (Real.log (p3 : ℝ) / Real.log ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ)))
                        then ((Real.log ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ)) / Real.log Y *
                          upperRough j (p3 : ℝ) : ℝ) : ℂ) * χ (j : ZMod q)
                        else 0)
                      else 0)
              else 0)‖ ≤ 436 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * ((if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0)) := by
          intro p3 hp3mem
          obtain ⟨hp3K, hp3P⟩ := Finset.mem_filter.mp hp3mem
          have hp3one : 1 ≤ p3 := le_trans (by norm_num) hp3P.two_le
          have hle21 : p2 ≤ p1 := by exact_mod_cast le_of_lt hlt21
          by_cases hlt32 : (p3 : ℝ) < (p2 : ℝ)
          · rw [if_pos hlt32, if_pos hlt32]
            have hle31 : p3 ≤ p1 := by exact_mod_cast le_of_lt (lt_trans hlt32 hlt21)
            have hcastprod : (((p1 * p2 * p3 : ℕ)) : ℝ) =
                (p1 : ℝ) * (p2 : ℝ) * (p3 : ℝ) := by
              push_cast
              ring
            refine le_trans (norm_mul_le _ _) ?_
            refine le_trans (mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one
              χ (p3 : ZMod q)) (norm_nonneg _)) ?_
            rw [one_mul]
            have hdbK : p1 * p2 * p3 * (((K / p1) / p2) / p3) ≤ K := by
              have h2 : p3 * (((K / p1) / p2) / p3) ≤ (K / p1) / p2 := Nat.mul_div_le _ _
              have h3 : p2 * (p3 * (((K / p1) / p2) / p3)) ≤ K / p1 :=
                le_trans (Nat.mul_le_mul_left _ h2) (Nat.mul_div_le _ _)
              have h4 : p1 * (p2 * (p3 * (((K / p1) / p2) / p3))) ≤ K :=
                le_trans (Nat.mul_le_mul_left _ h3) (Nat.mul_div_le _ _)
              calc p1 * p2 * p3 * (((K / p1) / p2) / p3)
                  = p1 * (p2 * (p3 * (((K / p1) / p2) / p3))) := by ring
                _ ≤ K := h4
            by_cases hab : (((L / p1) / p2) / p3) ≤ (((K / p1) / p2) / p3)
            · by_cases hzX : (2 * Y) ^ (upperC1 ε / 2) ≤ (p3 : ℝ)
              · by_cases ha1 : 1 ≤ ((L / p1) / p2) / p3
                · rw [← hcastprod]
                  refine le_trans (kept_fibre_le (K := K) (a := ((L / p1) / p2) / p3)
                    (b := ((K / p1) / p2) / p3) hε hε8 χ hp1 hp2P hp3P
                    (by exact_mod_cast hlt32) (by exact_mod_cast hlt21) hab ha1 hdbK hY2 hKY hzX hC0pos.le
                    hpre) ?_
                  exact le_of_eq (by ring)
                · have ha0 : ((L / p1) / p2) / p3 = 0 := by
                    by_contra hne
                    exact ha1 (Nat.pos_of_ne_zero hne)
                  rw [ha0]
                  rw [sum_Ioc_zero_eq_one (b := ((K / p1) / p2) / p3)]
                  · by_cases hb0 : ((K / p1) / p2) / p3 = 0
                    · rw [hb0, Finset.Ioc_eq_empty_of_le (Nat.zero_le 1), Finset.sum_empty,
                        norm_zero]
                      positivity
                    · have hb1 : 1 ≤ ((K / p1) / p2) / p3 := Nat.one_le_iff_ne_zero.mpr hb0
                      rw [← hcastprod]
                      refine le_trans (kept_fibre_le (K := K) (a := 1)
                        (b := ((K / p1) / p2) / p3) hε hε8 χ hp1 hp2P hp3P
                        (by exact_mod_cast hlt32) (by exact_mod_cast hlt21) hb1 (le_refl 1) hdbK hY2 hKY hzX hC0pos.le
                        hpre) ?_
                      exact le_of_eq (by ring)
                  · rw [if_neg]
                    exact fun hcon => kept_base_not_in_window hε hε8 hp1one hle21 hle31 hcon.2.1
              · refine le_trans (le_of_eq ?_) (mul_nonneg (by positivity) (Nat.cast_nonneg _))
                rw [norm_sum_eq_zero_of_forall]
                intro j hj
                rw [if_neg]
                intro hcon
                have hjY := kept_cofactor_gt hp1 hp2P hp3P hLf hj
                have hlev : (Y : ℝ) ^ upperC1 ε < ((((p1 : ℝ) * (p2 : ℝ)) * (p3 : ℝ)) * (j : ℝ)) ^ upperC1 ε :=
                  Real.rpow_lt_rpow (by linarith) hjY (upperC1_pos hε8)
                have hYc : (2 * Y) ^ (upperC1 ε / 2) ≤ (Y : ℝ) ^ upperC1 ε :=
                  level_ge (upperC1_pos hε8) hY2
                linarith [hcon.2.2, hYc, hlev, not_le.mp hzX]
            · rw [Finset.Ioc_eq_empty_of_le (le_of_lt (not_le.mp hab)), Finset.sum_empty, norm_zero]
              exact mul_nonneg (by positivity) (Nat.cast_nonneg _)
          · rw [if_neg hlt32, if_neg hlt32, norm_zero]
            exact mul_nonneg (by positivity) (by positivity)
        have hstep3 : (∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime, 436 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * ((if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0)))
            = 436 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime, ((if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0)) := by
          rw [Finset.mul_sum]
          try refine Finset.sum_congr rfl fun p3 _ => by ring
        exact le_trans (Finset.sum_le_sum hper3) (le_of_eq hstep3)
      · rw [if_neg hlt21, if_neg hlt21, norm_zero]
        exact mul_nonneg (by positivity) (by positivity)
    have hstep2 : (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime, 436 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * ((if (p2 : ℝ) < (p1 : ℝ) then
              ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
                (if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0)
              else 0)))
        = 436 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * ∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime, ((if (p2 : ℝ) < (p1 : ℝ) then
              ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
                (if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0)
              else 0)) := by
      rw [Finset.mul_sum]
      try refine Finset.sum_congr rfl fun p2 _ => by ring
    exact le_trans (Finset.sum_le_sum hper) (le_of_eq hstep2)
  have hstep1 : (∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, 436 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
            (if (p2 : ℝ) < (p1 : ℝ) then
              ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
                (if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0)
              else 0)))
      = 436 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
            (if (p2 : ℝ) < (p1 : ℝ) then
              ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
                (if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0)
              else 0)) := by
    rw [Finset.mul_sum]
    try refine Finset.sum_congr rfl fun p1 _ => by ring
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [hstep1]
  have h2 : (1 + Real.log (K : ℝ)) ≤ 3 * Real.log Y := by linarith
  have hp3 : (0 : ℝ) ≤ 1 + Real.log (K : ℝ) := by linarith
  have hcube : (1 + Real.log (K : ℝ)) ^ 3 ≤ 27 * (Real.log Y * Real.log Y * Real.log Y) := by
    have h5 : (1 + Real.log (K : ℝ)) ^ 3 ≤ (3 * Real.log Y) ^ 3 :=
      pow_le_pow_left₀ hp3 h2 3
    calc (1 + Real.log (K : ℝ)) ^ 3 ≤ (3 * Real.log Y) ^ 3 := h5
      _ = 27 * (Real.log Y * Real.log Y * Real.log Y) := by ring
  have hlogXge : Real.log Y ≤ Real.log (2 * Y) := Real.log_le_log hY0 (by linarith)
  have hLXle : Real.log (2 * Y) ^ (-(A + 6)) ≤ Real.log Y ^ (-(A + 6)) :=
    Real.rpow_le_rpow_of_nonpos hlogY hlogXge (by linarith)
  have hcube' : Real.log Y * Real.log Y * Real.log Y = Real.log Y ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hcomb : Real.log Y ^ (-(A + 6)) * Real.log Y ^ (3 : ℝ) = Real.log Y ^ (-(A + 3)) := by
    rw [← Real.rpow_add hlogY]
    congr 1
    ring
  have hlA3 : Real.log Y ^ (-(A + 3)) ≤ Real.log Y ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hlogY1 (by linarith)
  have hpw : Real.log (2 * Y) ^ (-(A + 6)) * (Real.log Y * Real.log Y * Real.log Y) ≤ Real.log Y ^ (-A) := by
    rw [hcube']
    calc Real.log (2 * Y) ^ (-(A + 6)) * Real.log Y ^ (3 : ℝ)
        ≤ Real.log Y ^ (-(A + 6)) * Real.log Y ^ (3 : ℝ) :=
          mul_le_mul_of_nonneg_right hLXle (by positivity)
      _ = Real.log Y ^ (-(A + 3)) := hcomb
      _ ≤ Real.log Y ^ (-A) := hlA3
  have hYnn : (0 : ℝ) ≤ Y := hY0.le
  calc 436 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * ∑ p1 ∈ (Finset.Icc 2 K).filter Nat.Prime, (∑ p2 ∈ (Finset.Icc 2 (K / p1)).filter Nat.Prime,
            (if (p2 : ℝ) < (p1 : ℝ) then
              ∑ p3 ∈ (Finset.Icc 2 ((K / p1) / p2)).filter Nat.Prime,
                (if (p3 : ℝ) < (p2 : ℝ) then ((((K / p1) / p2) / p3 : ℕ) : ℝ) else 0)
              else 0))
      ≤ 436 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * ((K : ℝ) * (1 + Real.log (K : ℝ)) ^ 3) :=
        mul_le_mul_of_nonneg_left (triple_inv_sum_le K) (by positivity)
    _ ≤ 436 * C0 * Real.log (2 * Y) ^ (-(A + 6)) * ((2 * Y) * (27 * (Real.log Y * Real.log Y * Real.log Y))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul hKY hcube (by positivity) (by linarith)
    _ = 23544 * C0 * (Y * (Real.log (2 * Y) ^ (-(A + 6)) * (Real.log Y * Real.log Y * Real.log Y))) := by ring
    _ ≤ 23544 * C0 * (Y * Real.log Y ^ (-A)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hpw (by positivity)
    _ = 23544 * C0 * Y * Real.log Y ^ (-A) := by ring
    _ ≤ 23544 * C0 * Y * Real.log Y ^ (-A) := by
        have h1 : (23544 : ℝ) * C0 ≤ 23544 * C0 := by nlinarith [hC0pos.le]
        have h2 : (0 : ℝ) ≤ Y * Real.log Y ^ (-A) :=
          mul_nonneg hY0.le (Real.rpow_nonneg hlogY.le _)
        calc 23544 * C0 * Y * Real.log Y ^ (-A) = (23544 * C0) * (Y * Real.log Y ^ (-A)) := by ring
          _ ≤ (23544 * C0) * (Y * Real.log Y ^ (-A)) := mul_le_mul_of_nonneg_right h1 h2
          _ = 23544 * C0 * Y * Real.log Y ^ (-A) := by ring
    _ ≤ max (23544 * C0) 4 * Y * Real.log Y ^ (-A) := by
        have h4 : 23544 * C0 ≤ max (23544 * C0) 4 := le_max_left _ _
        have h6 : (0 : ℝ) ≤ Y * Real.log Y ^ (-A) :=
          mul_nonneg hY0.le (Real.rpow_nonneg hlogY.le _)
        calc 23544 * C0 * Y * Real.log Y ^ (-A) = (23544 * C0) * (Y * Real.log Y ^ (-A)) := by ring
          _ ≤ max (23544 * C0) 4 * (Y * Real.log Y ^ (-A)) := mul_le_mul_of_nonneg_right h4 h6
          _ = max (23544 * C0) 4 * Y * Real.log Y ^ (-A) := by ring

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
  intro A hA
  obtain ⟨CH, hCHpos, hCH⟩ := upperH_self_bound hε hε8 (A + 1) (by linarith)
  set b : ℝ := 11 / 20 + ε with hbdef
  have hb0 : 0 < b := by rw [hbdef]; linarith
  have hb1 : b ≤ 1 := by rw [hbdef]; linarith
  refine ⟨max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
    (CH * (20 / 11 : ℝ) ^ (A + 1))) 4, fun x hx q hq hqA χ hχ t ht => ?_⟩
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  -- the threshold reaches every part of the constant
  have hexpb : Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1) ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hbase_le : max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).mpr hexpb
  have hlogx1 : (1 : ℝ) ≤ Real.log x := le_trans (le_max_right _ _) hbase_le
  have hlogx0 : 0 < Real.log x := by linarith
  have hlogx_big : (20 / 11 : ℝ) ^ (A + 1) ≤ Real.log x := by
    have h1 : (20 / 11 : ℝ) ^ (A + 1) ≤
        max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1 :=
      le_trans (le_max_right (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1)))
        (le_max_left _ 1)
    linarith
  have hlogCHbase : Real.log CH / b + 1 ≤ Real.log x := by
    have h1 : Real.log CH / b + 1 ≤
        max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1 :=
      le_trans (le_max_left (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1)))
        (le_max_left _ 1)
    linarith
  set Y : ℝ := x ^ b with hYdef
  have hY0 : (0 : ℝ) < Y := by rw [hYdef]; exact Real.rpow_pos_of_pos hx0 _
  have hY1 : (1 : ℝ) ≤ Y := by rw [hYdef]; exact Real.one_le_rpow hx1 hb0.le
  have hlogY : Real.log Y = b * Real.log x := by rw [hYdef]; exact Real.log_rpow hx0 _
  have hlogY0 : 0 < Real.log Y := by rw [hlogY]; nlinarith
  have hCHY : CH ≤ Y := by
    have hdiv : Real.log CH / b ≤ Real.log x - 1 := by linarith
    have h2 : Real.log CH ≤ Real.log x * b := by
      rw [div_le_iff₀ hb0] at hdiv
      nlinarith [hdiv, hb0]
    have h3 : CH = Real.exp (Real.log CH) := (Real.exp_log hCHpos).symm
    have h4 : x ^ b = Real.exp (Real.log x * b) := Real.rpow_def_of_pos hx0 b
    rw [hYdef, h3, h4]
    exact Real.exp_le_exp.mpr h2
  -- the modulus bound at the core's exponent
  have hqY : (q : ℝ) ≤ Real.log Y ^ (A + 1) := by
    have hbm : (1 : ℝ) ≤ b * (20 / 11 : ℝ) := by rw [hbdef]; nlinarith
    have hone : (1 : ℝ) ≤ (b * (20 / 11 : ℝ)) ^ (A + 1) := Real.one_le_rpow hbm (by linarith)
    have hbx : (b * (20 / 11 : ℝ)) ^ (A + 1) =
        b ^ (A + 1) * (20 / 11 : ℝ) ^ (A + 1) := Real.mul_rpow hb0.le (by norm_num)
    have hone' : (1 : ℝ) ≤ b ^ (A + 1) * (20 / 11 : ℝ) ^ (A + 1) := by
      rw [← hbx]; exact hone
    have hA0 : (0 : ℝ) ≤ Real.log x ^ A := Real.rpow_nonneg hlogx0.le _
    have hsplit : Real.log x ^ (A + 1) = Real.log x ^ A * Real.log x := by
      rw [show (A + 1 : ℝ) = A + 1 by ring, Real.rpow_add hlogx0, Real.rpow_one]
    have hstep : Real.log x ^ A * (20 / 11 : ℝ) ^ (A + 1) ≤ Real.log x ^ A * Real.log x :=
      mul_le_mul_of_nonneg_left hlogx_big hA0
    have hkey : Real.log x ^ A ≤ b ^ (A + 1) * Real.log x ^ (A + 1) := by
      rw [hsplit]
      have hbA : (0 : ℝ) < b ^ (A + 1) := Real.rpow_pos_of_pos hb0 _
      calc Real.log x ^ A = 1 * Real.log x ^ A := by ring
        _ ≤ (b ^ (A + 1) * (20 / 11 : ℝ) ^ (A + 1)) * Real.log x ^ A :=
            mul_le_mul_of_nonneg_right hone' hA0
        _ = b ^ (A + 1) * (Real.log x ^ A * (20 / 11 : ℝ) ^ (A + 1)) := by ring
        _ ≤ b ^ (A + 1) * (Real.log x ^ A * Real.log x) :=
            mul_le_mul_of_nonneg_left hstep hbA.le
    rw [hlogY, Real.mul_rpow hb0.le hlogx0.le]
    linarith
  have hLpos : 1 ≤ ⌊Y⌋₊ := Nat.floor_pos.mpr hY1
  set L : ℕ := ⌊Y⌋₊ with hLdef
  set B : ℕ := ⌊2 * Y⌋₊ with hBdef
  set K : ℕ := min B ⌊t⌋₊ with hKdef
  have hYB : Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊ = Finset.Ioc L B := by
    rw [← hbdef, ← hYdef, hLdef, hBdef]
  have hS : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) = Finset.Ioc L K := by
    have h := filter_rightInterval (t := t) (A := L) (B := B) hLpos
    rw [rightInterval, hYB]
    simpa [hKdef] using h
  rw [hS]
  rcases Nat.lt_or_ge L K with hLK | hLK
  · have hLY : (L : ℝ) ≤ Y := by rw [hLdef]; exact Nat.floor_le (by linarith)
    have hLf : ⌊Y⌋₊ ≤ L := by rw [hLdef]
    have hKY : (K : ℝ) ≤ 2 * Y := by
      rw [hKdef]
      exact le_trans (by exact_mod_cast min_le_left B ⌊t⌋₊) (Nat.floor_le (by linarith))
    have hcore := hCH Y hCHY q hq hqY χ hχ L K hLpos hLY hLf hKY
    refine le_trans hcore ?_
    -- `log Y` is `b log x` and the exponent shift costs `(20/11)^(A+1)`
    have hpow : Real.log Y ^ (-(A + 1)) = b ^ (-(A + 1)) * Real.log x ^ (-(A + 1)) := by
      rw [hlogY, Real.mul_rpow hb0.le hlogx0.le]
    have hbm1 : (1 : ℝ) ≤ b * (20 / 11 : ℝ) := by rw [hbdef]; nlinarith
    have hone : (1 : ℝ) ≤ b ^ (A + 1) * (20 / 11 : ℝ) ^ (A + 1) := by
      have h2 : (1 : ℝ) ≤ (b * (20 / 11 : ℝ)) ^ (A + 1) := Real.one_le_rpow hbm1 (by linarith)
      rwa [Real.mul_rpow hb0.le (by norm_num)] at h2
    have hbp : (0 : ℝ) < b ^ (A + 1) := Real.rpow_pos_of_pos hb0 _
    have hstep : b ^ (-(A + 1)) ≤ (20 / 11 : ℝ) ^ (A + 1) := by
      rw [Real.rpow_neg hb0.le, inv_eq_one_div, div_le_iff₀ hbp]
      simpa [mul_comm] using hone
    have hlxn : (0 : ℝ) ≤ Real.log x ^ (-(A + 1)) := Real.rpow_nonneg hlogx0.le _
    have hYnn : (0 : ℝ) ≤ Y := hY0.le
    have hmid : CH * Y * (b ^ (-(A + 1)) * Real.log x ^ (-(A + 1))) ≤
        CH * Y * ((20 / 11 : ℝ) ^ (A + 1) * Real.log x ^ (-(A + 1))) := by
      have h0 : (0 : ℝ) ≤ CH * Y := mul_nonneg hCHpos.le hYnn
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hstep hlxn) h0
    have hexp2 : Real.log x ^ (-(A + 1)) ≤ Real.log x ^ (-A) :=
      Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith)
    have htail : Y * Real.log x ^ (-(A + 1)) ≤ Y * Real.log x ^ (-A) :=
      mul_le_mul_of_nonneg_left hexp2 hYnn
    have hfin : CH * Y * ((20 / 11 : ℝ) ^ (A + 1) * Real.log x ^ (-(A + 1))) ≤
        max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
          (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * Y * Real.log x ^ (-A) := by
      have hC : max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
          (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 ≤ x := hx
      have h1 : CH * (20 / 11 : ℝ) ^ (A + 1) ≤
          max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
            (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 := by
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      have h2 : (0 : ℝ) ≤ Y * Real.log x ^ (-A) :=
        mul_nonneg hYnn (Real.rpow_nonneg hlogx0.le _)
      have heq : CH * Y * ((20 / 11 : ℝ) ^ (A + 1) * Real.log x ^ (-(A + 1)))
          = (CH * (20 / 11 : ℝ) ^ (A + 1)) * (Y * Real.log x ^ (-(A + 1))) := by ring
      have heq2 : max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
            (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * Y * Real.log x ^ (-A)
          = max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
            (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * (Y * Real.log x ^ (-A)) := by ring
      rw [heq, heq2]
      calc (CH * (20 / 11 : ℝ) ^ (A + 1)) * (Y * Real.log x ^ (-(A + 1)))
          ≤ (CH * (20 / 11 : ℝ) ^ (A + 1)) * (Y * Real.log x ^ (-A)) :=
            mul_le_mul_of_nonneg_left htail (by positivity)
        _ ≤ max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
              (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * (Y * Real.log x ^ (-A)) :=
            mul_le_mul_of_nonneg_right h1 h2
    calc CH * Y * Real.log Y ^ (-(A + 1))
        = CH * Y * (b ^ (-(A + 1)) * Real.log x ^ (-(A + 1))) := by rw [hpow]
      _ ≤ CH * Y * ((20 / 11 : ℝ) ^ (A + 1) * Real.log x ^ (-(A + 1))) := hmid
      _ ≤ max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
            (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * Y * Real.log x ^ (-A) := hfin
      _ = max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
            (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
          rw [← hbdef, hYdef]
  · rw [Finset.Ioc_eq_empty_of_le hLK, Finset.sum_empty, norm_zero]
    have h1 : (0 : ℝ) ≤ max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
        (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 := by
      have h2 : (0 : ℝ) < Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1) :=
        Real.exp_pos _
      exact le_trans (le_trans h2.le (le_max_left _ _)) (le_max_left _ _)
    have h3 : (0 : ℝ) ≤ x ^ (11 / 20 + ε) := by positivity
    exact mul_nonneg (mul_nonneg h1 h3) (Real.rpow_nonneg hlogx0.le _)

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
  intro A hA
  obtain ⟨CH, hCHpos, hCH⟩ := upperJ_self_bound hε hε8 (A + 1) (by linarith)
  set b : ℝ := 11 / 20 + ε with hbdef
  have hb0 : 0 < b := by rw [hbdef]; linarith
  have hb1 : b ≤ 1 := by rw [hbdef]; linarith
  refine ⟨max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
    (CH * (20 / 11 : ℝ) ^ (A + 1))) 4, fun x hx q hq hqA χ hχ t ht => ?_⟩
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  -- the threshold reaches every part of the constant
  have hexpb : Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1) ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hbase_le : max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).mpr hexpb
  have hlogx1 : (1 : ℝ) ≤ Real.log x := le_trans (le_max_right _ _) hbase_le
  have hlogx0 : 0 < Real.log x := by linarith
  have hlogx_big : (20 / 11 : ℝ) ^ (A + 1) ≤ Real.log x := by
    have h1 : (20 / 11 : ℝ) ^ (A + 1) ≤
        max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1 :=
      le_trans (le_max_right (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1)))
        (le_max_left _ 1)
    linarith
  have hlogCHbase : Real.log CH / b + 1 ≤ Real.log x := by
    have h1 : Real.log CH / b + 1 ≤
        max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1 :=
      le_trans (le_max_left (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1)))
        (le_max_left _ 1)
    linarith
  set Y : ℝ := x ^ b with hYdef
  have hY0 : (0 : ℝ) < Y := by rw [hYdef]; exact Real.rpow_pos_of_pos hx0 _
  have hY1 : (1 : ℝ) ≤ Y := by rw [hYdef]; exact Real.one_le_rpow hx1 hb0.le
  have hlogY : Real.log Y = b * Real.log x := by rw [hYdef]; exact Real.log_rpow hx0 _
  have hlogY0 : 0 < Real.log Y := by rw [hlogY]; nlinarith
  have hCHY : CH ≤ Y := by
    have hdiv : Real.log CH / b ≤ Real.log x - 1 := by linarith
    have h2 : Real.log CH ≤ Real.log x * b := by
      rw [div_le_iff₀ hb0] at hdiv
      nlinarith [hdiv, hb0]
    have h3 : CH = Real.exp (Real.log CH) := (Real.exp_log hCHpos).symm
    have h4 : x ^ b = Real.exp (Real.log x * b) := Real.rpow_def_of_pos hx0 b
    rw [hYdef, h3, h4]
    exact Real.exp_le_exp.mpr h2
  -- the modulus bound at the core's exponent
  have hqY : (q : ℝ) ≤ Real.log Y ^ (A + 1) := by
    have hbm : (1 : ℝ) ≤ b * (20 / 11 : ℝ) := by rw [hbdef]; nlinarith
    have hone : (1 : ℝ) ≤ (b * (20 / 11 : ℝ)) ^ (A + 1) := Real.one_le_rpow hbm (by linarith)
    have hbx : (b * (20 / 11 : ℝ)) ^ (A + 1) =
        b ^ (A + 1) * (20 / 11 : ℝ) ^ (A + 1) := Real.mul_rpow hb0.le (by norm_num)
    have hone' : (1 : ℝ) ≤ b ^ (A + 1) * (20 / 11 : ℝ) ^ (A + 1) := by
      rw [← hbx]; exact hone
    have hA0 : (0 : ℝ) ≤ Real.log x ^ A := Real.rpow_nonneg hlogx0.le _
    have hsplit : Real.log x ^ (A + 1) = Real.log x ^ A * Real.log x := by
      rw [show (A + 1 : ℝ) = A + 1 by ring, Real.rpow_add hlogx0, Real.rpow_one]
    have hstep : Real.log x ^ A * (20 / 11 : ℝ) ^ (A + 1) ≤ Real.log x ^ A * Real.log x :=
      mul_le_mul_of_nonneg_left hlogx_big hA0
    have hkey : Real.log x ^ A ≤ b ^ (A + 1) * Real.log x ^ (A + 1) := by
      rw [hsplit]
      have hbA : (0 : ℝ) < b ^ (A + 1) := Real.rpow_pos_of_pos hb0 _
      calc Real.log x ^ A = 1 * Real.log x ^ A := by ring
        _ ≤ (b ^ (A + 1) * (20 / 11 : ℝ) ^ (A + 1)) * Real.log x ^ A :=
            mul_le_mul_of_nonneg_right hone' hA0
        _ = b ^ (A + 1) * (Real.log x ^ A * (20 / 11 : ℝ) ^ (A + 1)) := by ring
        _ ≤ b ^ (A + 1) * (Real.log x ^ A * Real.log x) :=
            mul_le_mul_of_nonneg_left hstep hbA.le
    rw [hlogY, Real.mul_rpow hb0.le hlogx0.le]
    linarith
  have hLpos : 1 ≤ ⌊Y⌋₊ := Nat.floor_pos.mpr hY1
  set L : ℕ := ⌊Y⌋₊ with hLdef
  set B : ℕ := ⌊2 * Y⌋₊ with hBdef
  set K : ℕ := min B ⌊t⌋₊ with hKdef
  have hYB : Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊ = Finset.Ioc L B := by
    rw [← hbdef, ← hYdef, hLdef, hBdef]
  have hS : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) = Finset.Ioc L K := by
    have h := filter_rightInterval (t := t) (A := L) (B := B) hLpos
    rw [rightInterval, hYB]
    simpa [hKdef] using h
  rw [hS]
  rcases Nat.lt_or_ge L K with hLK | hLK
  · have hLY : (L : ℝ) ≤ Y := by rw [hLdef]; exact Nat.floor_le (by linarith)
    have hLf : ⌊Y⌋₊ ≤ L := by rw [hLdef]
    have hKY : (K : ℝ) ≤ 2 * Y := by
      rw [hKdef]
      exact le_trans (by exact_mod_cast min_le_left B ⌊t⌋₊) (Nat.floor_le (by linarith))
    have hcore := hCH Y hCHY q hq hqY χ hχ L K hLpos hLY hLf hKY
    refine le_trans hcore ?_
    -- `log Y` is `b log x` and the exponent shift costs `(20/11)^(A+1)`
    have hpow : Real.log Y ^ (-(A + 1)) = b ^ (-(A + 1)) * Real.log x ^ (-(A + 1)) := by
      rw [hlogY, Real.mul_rpow hb0.le hlogx0.le]
    have hbm1 : (1 : ℝ) ≤ b * (20 / 11 : ℝ) := by rw [hbdef]; nlinarith
    have hone : (1 : ℝ) ≤ b ^ (A + 1) * (20 / 11 : ℝ) ^ (A + 1) := by
      have h2 : (1 : ℝ) ≤ (b * (20 / 11 : ℝ)) ^ (A + 1) := Real.one_le_rpow hbm1 (by linarith)
      rwa [Real.mul_rpow hb0.le (by norm_num)] at h2
    have hbp : (0 : ℝ) < b ^ (A + 1) := Real.rpow_pos_of_pos hb0 _
    have hstep : b ^ (-(A + 1)) ≤ (20 / 11 : ℝ) ^ (A + 1) := by
      rw [Real.rpow_neg hb0.le, inv_eq_one_div, div_le_iff₀ hbp]
      simpa [mul_comm] using hone
    have hlxn : (0 : ℝ) ≤ Real.log x ^ (-(A + 1)) := Real.rpow_nonneg hlogx0.le _
    have hYnn : (0 : ℝ) ≤ Y := hY0.le
    have hmid : CH * Y * (b ^ (-(A + 1)) * Real.log x ^ (-(A + 1))) ≤
        CH * Y * ((20 / 11 : ℝ) ^ (A + 1) * Real.log x ^ (-(A + 1))) := by
      have h0 : (0 : ℝ) ≤ CH * Y := mul_nonneg hCHpos.le hYnn
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hstep hlxn) h0
    have hexp2 : Real.log x ^ (-(A + 1)) ≤ Real.log x ^ (-A) :=
      Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith)
    have htail : Y * Real.log x ^ (-(A + 1)) ≤ Y * Real.log x ^ (-A) :=
      mul_le_mul_of_nonneg_left hexp2 hYnn
    have hfin : CH * Y * ((20 / 11 : ℝ) ^ (A + 1) * Real.log x ^ (-(A + 1))) ≤
        max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
          (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * Y * Real.log x ^ (-A) := by
      have hC : max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
          (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 ≤ x := hx
      have h1 : CH * (20 / 11 : ℝ) ^ (A + 1) ≤
          max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
            (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 := by
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      have h2 : (0 : ℝ) ≤ Y * Real.log x ^ (-A) :=
        mul_nonneg hYnn (Real.rpow_nonneg hlogx0.le _)
      have heq : CH * Y * ((20 / 11 : ℝ) ^ (A + 1) * Real.log x ^ (-(A + 1)))
          = (CH * (20 / 11 : ℝ) ^ (A + 1)) * (Y * Real.log x ^ (-(A + 1))) := by ring
      have heq2 : max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
            (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * Y * Real.log x ^ (-A)
          = max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
            (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * (Y * Real.log x ^ (-A)) := by ring
      rw [heq, heq2]
      calc (CH * (20 / 11 : ℝ) ^ (A + 1)) * (Y * Real.log x ^ (-(A + 1)))
          ≤ (CH * (20 / 11 : ℝ) ^ (A + 1)) * (Y * Real.log x ^ (-A)) :=
            mul_le_mul_of_nonneg_left htail (by positivity)
        _ ≤ max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
              (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * (Y * Real.log x ^ (-A)) :=
            mul_le_mul_of_nonneg_right h1 h2
    calc CH * Y * Real.log Y ^ (-(A + 1))
        = CH * Y * (b ^ (-(A + 1)) * Real.log x ^ (-(A + 1))) := by rw [hpow]
      _ ≤ CH * Y * ((20 / 11 : ℝ) ^ (A + 1) * Real.log x ^ (-(A + 1))) := hmid
      _ ≤ max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
            (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * Y * Real.log x ^ (-A) := hfin
      _ = max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
            (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
          rw [← hbdef, hYdef]
  · rw [Finset.Ioc_eq_empty_of_le hLK, Finset.sum_empty, norm_zero]
    have h1 : (0 : ℝ) ≤ max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
        (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 := by
      have h2 : (0 : ℝ) < Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1) :=
        Real.exp_pos _
      exact le_trans (le_trans h2.le (le_max_left _ _)) (le_max_left _ _)
    have h3 : (0 : ℝ) ≤ x ^ (11 / 20 + ε) := by positivity
    exact mul_nonneg (mul_nonneg h1 h3) (Real.rpow_nonneg hlogx0.le _)

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
  intro A hA
  obtain ⟨CH, hCHpos, hCH⟩ := upperKept_self_bound hε hε8 (A + 1) (by linarith)
  set b : ℝ := 11 / 20 + ε with hbdef
  have hb0 : 0 < b := by rw [hbdef]; linarith
  have hb1 : b ≤ 1 := by rw [hbdef]; linarith
  refine ⟨max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
    (CH * (20 / 11 : ℝ) ^ (A + 1))) 4, fun x hx q hq hqA χ hχ t ht => ?_⟩
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  -- the threshold reaches every part of the constant
  have hexpb : Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1) ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hbase_le : max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).mpr hexpb
  have hlogx1 : (1 : ℝ) ≤ Real.log x := le_trans (le_max_right _ _) hbase_le
  have hlogx0 : 0 < Real.log x := by linarith
  have hlogx_big : (20 / 11 : ℝ) ^ (A + 1) ≤ Real.log x := by
    have h1 : (20 / 11 : ℝ) ^ (A + 1) ≤
        max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1 :=
      le_trans (le_max_right (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1)))
        (le_max_left _ 1)
    linarith
  have hlogCHbase : Real.log CH / b + 1 ≤ Real.log x := by
    have h1 : Real.log CH / b + 1 ≤
        max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1 :=
      le_trans (le_max_left (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1)))
        (le_max_left _ 1)
    linarith
  set Y : ℝ := x ^ b with hYdef
  have hY0 : (0 : ℝ) < Y := by rw [hYdef]; exact Real.rpow_pos_of_pos hx0 _
  have hY1 : (1 : ℝ) ≤ Y := by rw [hYdef]; exact Real.one_le_rpow hx1 hb0.le
  have hlogY : Real.log Y = b * Real.log x := by rw [hYdef]; exact Real.log_rpow hx0 _
  have hlogY0 : 0 < Real.log Y := by rw [hlogY]; nlinarith
  have hCHY : CH ≤ Y := by
    have hdiv : Real.log CH / b ≤ Real.log x - 1 := by linarith
    have h2 : Real.log CH ≤ Real.log x * b := by
      rw [div_le_iff₀ hb0] at hdiv
      nlinarith [hdiv, hb0]
    have h3 : CH = Real.exp (Real.log CH) := (Real.exp_log hCHpos).symm
    have h4 : x ^ b = Real.exp (Real.log x * b) := Real.rpow_def_of_pos hx0 b
    rw [hYdef, h3, h4]
    exact Real.exp_le_exp.mpr h2
  -- the modulus bound at the core's exponent
  have hqY : (q : ℝ) ≤ Real.log Y ^ (A + 1) := by
    have hbm : (1 : ℝ) ≤ b * (20 / 11 : ℝ) := by rw [hbdef]; nlinarith
    have hone : (1 : ℝ) ≤ (b * (20 / 11 : ℝ)) ^ (A + 1) := Real.one_le_rpow hbm (by linarith)
    have hbx : (b * (20 / 11 : ℝ)) ^ (A + 1) =
        b ^ (A + 1) * (20 / 11 : ℝ) ^ (A + 1) := Real.mul_rpow hb0.le (by norm_num)
    have hone' : (1 : ℝ) ≤ b ^ (A + 1) * (20 / 11 : ℝ) ^ (A + 1) := by
      rw [← hbx]; exact hone
    have hA0 : (0 : ℝ) ≤ Real.log x ^ A := Real.rpow_nonneg hlogx0.le _
    have hsplit : Real.log x ^ (A + 1) = Real.log x ^ A * Real.log x := by
      rw [show (A + 1 : ℝ) = A + 1 by ring, Real.rpow_add hlogx0, Real.rpow_one]
    have hstep : Real.log x ^ A * (20 / 11 : ℝ) ^ (A + 1) ≤ Real.log x ^ A * Real.log x :=
      mul_le_mul_of_nonneg_left hlogx_big hA0
    have hkey : Real.log x ^ A ≤ b ^ (A + 1) * Real.log x ^ (A + 1) := by
      rw [hsplit]
      have hbA : (0 : ℝ) < b ^ (A + 1) := Real.rpow_pos_of_pos hb0 _
      calc Real.log x ^ A = 1 * Real.log x ^ A := by ring
        _ ≤ (b ^ (A + 1) * (20 / 11 : ℝ) ^ (A + 1)) * Real.log x ^ A :=
            mul_le_mul_of_nonneg_right hone' hA0
        _ = b ^ (A + 1) * (Real.log x ^ A * (20 / 11 : ℝ) ^ (A + 1)) := by ring
        _ ≤ b ^ (A + 1) * (Real.log x ^ A * Real.log x) :=
            mul_le_mul_of_nonneg_left hstep hbA.le
    rw [hlogY, Real.mul_rpow hb0.le hlogx0.le]
    linarith
  have hLpos : 1 ≤ ⌊Y⌋₊ := Nat.floor_pos.mpr hY1
  set L : ℕ := ⌊Y⌋₊ with hLdef
  set B : ℕ := ⌊2 * Y⌋₊ with hBdef
  set K : ℕ := min B ⌊t⌋₊ with hKdef
  have hYB : Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊ = Finset.Ioc L B := by
    rw [← hbdef, ← hYdef, hLdef, hBdef]
  have hS : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) = Finset.Ioc L K := by
    have h := filter_rightInterval (t := t) (A := L) (B := B) hLpos
    rw [rightInterval, hYB]
    simpa [hKdef] using h
  rw [hS]
  rcases Nat.lt_or_ge L K with hLK | hLK
  · have hLY : (L : ℝ) ≤ Y := by rw [hLdef]; exact Nat.floor_le (by linarith)
    have hLf : ⌊Y⌋₊ ≤ L := by rw [hLdef]
    have hKY : (K : ℝ) ≤ 2 * Y := by
      rw [hKdef]
      exact le_trans (by exact_mod_cast min_le_left B ⌊t⌋₊) (Nat.floor_le (by linarith))
    have hcore := hCH Y hCHY q hq hqY χ hχ L K hLpos hLY hLf hKY
    refine le_trans hcore ?_
    -- `log Y` is `b log x` and the exponent shift costs `(20/11)^(A+1)`
    have hpow : Real.log Y ^ (-(A + 1)) = b ^ (-(A + 1)) * Real.log x ^ (-(A + 1)) := by
      rw [hlogY, Real.mul_rpow hb0.le hlogx0.le]
    have hbm1 : (1 : ℝ) ≤ b * (20 / 11 : ℝ) := by rw [hbdef]; nlinarith
    have hone : (1 : ℝ) ≤ b ^ (A + 1) * (20 / 11 : ℝ) ^ (A + 1) := by
      have h2 : (1 : ℝ) ≤ (b * (20 / 11 : ℝ)) ^ (A + 1) := Real.one_le_rpow hbm1 (by linarith)
      rwa [Real.mul_rpow hb0.le (by norm_num)] at h2
    have hbp : (0 : ℝ) < b ^ (A + 1) := Real.rpow_pos_of_pos hb0 _
    have hstep : b ^ (-(A + 1)) ≤ (20 / 11 : ℝ) ^ (A + 1) := by
      rw [Real.rpow_neg hb0.le, inv_eq_one_div, div_le_iff₀ hbp]
      simpa [mul_comm] using hone
    have hlxn : (0 : ℝ) ≤ Real.log x ^ (-(A + 1)) := Real.rpow_nonneg hlogx0.le _
    have hYnn : (0 : ℝ) ≤ Y := hY0.le
    have hmid : CH * Y * (b ^ (-(A + 1)) * Real.log x ^ (-(A + 1))) ≤
        CH * Y * ((20 / 11 : ℝ) ^ (A + 1) * Real.log x ^ (-(A + 1))) := by
      have h0 : (0 : ℝ) ≤ CH * Y := mul_nonneg hCHpos.le hYnn
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hstep hlxn) h0
    have hexp2 : Real.log x ^ (-(A + 1)) ≤ Real.log x ^ (-A) :=
      Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith)
    have htail : Y * Real.log x ^ (-(A + 1)) ≤ Y * Real.log x ^ (-A) :=
      mul_le_mul_of_nonneg_left hexp2 hYnn
    have hfin : CH * Y * ((20 / 11 : ℝ) ^ (A + 1) * Real.log x ^ (-(A + 1))) ≤
        max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
          (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * Y * Real.log x ^ (-A) := by
      have hC : max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
          (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 ≤ x := hx
      have h1 : CH * (20 / 11 : ℝ) ^ (A + 1) ≤
          max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
            (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 := by
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      have h2 : (0 : ℝ) ≤ Y * Real.log x ^ (-A) :=
        mul_nonneg hYnn (Real.rpow_nonneg hlogx0.le _)
      have heq : CH * Y * ((20 / 11 : ℝ) ^ (A + 1) * Real.log x ^ (-(A + 1)))
          = (CH * (20 / 11 : ℝ) ^ (A + 1)) * (Y * Real.log x ^ (-(A + 1))) := by ring
      have heq2 : max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
            (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * Y * Real.log x ^ (-A)
          = max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
            (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * (Y * Real.log x ^ (-A)) := by ring
      rw [heq, heq2]
      calc (CH * (20 / 11 : ℝ) ^ (A + 1)) * (Y * Real.log x ^ (-(A + 1)))
          ≤ (CH * (20 / 11 : ℝ) ^ (A + 1)) * (Y * Real.log x ^ (-A)) :=
            mul_le_mul_of_nonneg_left htail (by positivity)
        _ ≤ max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
              (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * (Y * Real.log x ^ (-A)) :=
            mul_le_mul_of_nonneg_right h1 h2
    calc CH * Y * Real.log Y ^ (-(A + 1))
        = CH * Y * (b ^ (-(A + 1)) * Real.log x ^ (-(A + 1))) := by rw [hpow]
      _ ≤ CH * Y * ((20 / 11 : ℝ) ^ (A + 1) * Real.log x ^ (-(A + 1))) := hmid
      _ ≤ max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
            (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * Y * Real.log x ^ (-A) := hfin
      _ = max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
            (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
          rw [← hbdef, hYdef]
  · rw [Finset.Ioc_eq_empty_of_le hLK, Finset.sum_empty, norm_zero]
    have h1 : (0 : ℝ) ≤ max (max (Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1))
        (CH * (20 / 11 : ℝ) ^ (A + 1))) 4 := by
      have h2 : (0 : ℝ) < Real.exp (max (max (Real.log CH / b + 1) ((20 / 11 : ℝ) ^ (A + 1))) 1) :=
        Real.exp_pos _
      exact le_trans (le_trans h2.le (le_max_left _ _)) (le_max_left _ _)
    have h3 : (0 : ℝ) ≤ x ^ (11 / 20 + ε) := by positivity
    exact mul_nonneg (mul_nonneg h1 h3) (Real.rpow_nonneg hlogx0.le _)

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


/-- LEAF: condition iii, principal character. The short interval sums of the self scaled upper
coefficient against the trivial character obey the paper density statement, at the frozen level
constant plus the deleted integral, with every power of the logarithm saved. There is no mean
square clause and no non-principal character, so this is strictly easier than the target. The
factor `(1 : DirichletCharacter ℂ q) (m : ZMod q)` is kept in the summand so that the assembly is
a substitution. Non-vacuity: the index set is empty at `t = 0`, and `b1` is pinned by `hb`. -/
theorem upper_self_scaled_principal_distribution
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {b1 : ℝ → ℕ → ℝ}
    (hb : ∀ x m, b1 x m = if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then
      Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m else 0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((b1 x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q) -
            ((ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
              upperDeletedIntegral ω ε : ℝ) : ℂ) /
              Real.log (x ^ (11 / 20 + ε)))‖ ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: condition iii, non-principal characters. The delta factor vanishes off the principal
character, so the claim is only that the short character sums of the self scaled coefficient at
level `x ^ (11/20 + eps)` save any power of the logarithm, uniformly in `q` up to `log x ^ A` and in
`chi` other than the trivial character. No mean square clause and no principal character, so this
is strictly easier than the target. Non-vacuity: at `t = 0` the index set is empty and the sum is
zero, and `q` and `chi` are arbitrary. -/
theorem upper_self_scaled_nonprincipal_distribution
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
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
  upper_self_scaled_nonprincipal_distribution_split h4 h9 hω hz hε hε8 hb

/-- LEAF: condition iii yields condition iv. Given the divisor bound for `b1` at exponent two and
the short interval distribution clause at the paper density, the averaged square of the centred
short character sums over the complement of an exceptional set obeys the short interval mean square
clause at the same density, the exceptional characters being the ones whose windowed sum is
atypically large. The distribution clause is a hypothesis here and the mean square clause is not,
so this is strictly easier than the target. Non-vacuity: the divisor bound holds for the `b1`
fixed by `hb`, so both hypotheses are satisfiable. -/
theorem upper_self_scaled_mean_square_of_distribution
    {ω : ℝ → ℝ} {ε : ℝ} {b1 : ℝ → ℕ → ℝ}
    (hdiv : ∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (2 : ℝ))
    (hdist : Task308.ShortDistribution ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε) b1) :
    Task308.ShortMeanSquare ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε) b1 := by
  sorry

/-- The target `upper_self_scaled_conditions` of Upper312RouteSelfScaled, verbatim, assembled from
the three leaves. For each power of the logarithm the two character leaves give the two constants;
the maximum of them and one is the constant of the distribution clause, whose principal case is the
first leaf after evaluating the delta factor and whose non-principal case is the second leaf after
evaluating the delta factor to zero. The divisor bound of the target's coefficient, proved in the
imported file, and the distribution clause just obtained feed the third leaf, which returns the
mean square clause at the same density. No step uses the sealed target. -/
theorem upper_self_scaled_conditions_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {b1 : ℝ → ℕ → ℝ}
    (hb : ∀ x m, b1 x m = if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then
      Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m else 0) :
    Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 ∧
      Task308.ShortMeanSquare ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 := by
  have hdiv : ∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (2 : ℝ) :=
    upper_self_scaled_divisor_bound (B := 2) (by norm_num) hε8 hb
  have hdist : Task308.ShortDistribution ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε) b1 := by
    intro A hA
    obtain ⟨C1, hC1⟩ :=
      upper_self_scaled_principal_distribution h4 h9 hω hz hε hε8 hb A hA
    obtain ⟨C2, hC2⟩ :=
      upper_self_scaled_nonprincipal_distribution h4 h9 hω hz hε hε8 hb A hA
    refine ⟨max (max C1 C2) 1, fun x hx q hq hqA χ t ht => ?_⟩
    have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hxone : 1 ≤ x := le_trans (le_max_right _ _) hx
    have hscale : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (Real.log_nonneg hxone) _)
    by_cases hχ : χ = 1
    · subst hχ
      have hd : Thm2.delta (1 : DirichletCharacter ℂ q) = 1 := by simp [Thm2.delta]
      rw [hd, one_mul]
      calc _ ≤ C1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := hC1 x hx1 q hq hqA t ht
        _ ≤ max (max C1 C2) 1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
            rw [mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_right
              (le_trans (le_max_left _ _) (le_max_left _ _)) hscale
    · have hd : Thm2.delta χ = 0 := by simp [Thm2.delta, hχ]
      rw [hd, zero_mul, zero_div]
      simp only [sub_zero]
      calc _ ≤ C2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := hC2 x hx2 q hq hqA χ hχ t ht
        _ ≤ max (max C1 C2) 1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
            rw [mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_right
              (le_trans (le_max_right _ _) (le_max_left _ _)) hscale
  exact ⟨hdist, upper_self_scaled_mean_square_of_distribution hdiv hdist⟩

end LeanLab.BHP1997.Upper312Route
