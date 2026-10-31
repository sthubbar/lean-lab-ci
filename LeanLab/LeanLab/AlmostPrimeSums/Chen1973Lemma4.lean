/-
AI-written Lean code, Claude, 2026-10-21, session 20261020T2317Z-cloud53, unit U-6794, track T1.
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176, lab copy papers/P0002.pdf.
Chen's Lemma 4, p. 161: for `m ≠ 1` and squarefree odd `k`,
`|∑*_{χ_k} χ_k(m)| ≤ |(m - 1, k)|`, the sum over primitive characters mod `k`.
`Chen1973Lemmas.lean` proved the prime modulus case. Here the GENERAL modulus `k ≥ 1` is
proved, without Chen's hypotheses `m ≠ 1`, `k` odd, `k` squarefree, by a route different from
Chen's CRT product: every character mod `k` comes from a unique primitive character mod its
conductor `d ∣ k`, so `∑_{d ∣ k} ∑*_{χ mod d} χ(m) = [m ≡ 1 (k)] φ(k)` for `(m, k) = 1`, and
Möbius inversion gives `∑*_{χ mod k} χ(m) = ∑_{d e = k, d ∣ m - 1} μ(e) φ(d)`, whose absolute
value is at most `∑_{d ∣ (m - 1, k)} φ(d) = (m - 1, k)`.
Binary Goldbach is OPEN.
-/
import Mathlib

open Finset

noncomputable section
namespace LeanLab.AlmostPrimeSums.Chen1973Lemma4

open DirichletCharacter

open Classical in
/-- Chen's `∑*_{χ_d} χ_d(a)`: the sum of `χ(a)` over the primitive characters mod `d`. -/
def primSum (d : ℕ) (a : ℤ) : ℂ :=
  ∑ ψ ∈ univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive), ψ (a : ZMod d)

/-- The value of the full character sum at a modulus `d`, as a function for Möbius inversion. -/
def gFull (a : ℤ) (d : ℕ) : ℂ := if (d : ℤ) ∣ a - 1 then (d.totient : ℂ) else 0

/-- **Decomposition by conductor**: for `k ≠ 0` and `a` coprime to `k`, the sum over all
characters mod `k` equals the sum over `d ∣ k` of the sums over primitive characters mod `d`. -/
theorem sum_all_eq_sum_primSum {k : ℕ} (hk : k ≠ 0) {a : ℤ} (ha : IsCoprime a k) :
    ∑ χ : DirichletCharacter ℂ k, χ (a : ZMod k) = ∑ d ∈ k.divisors, primSum d a := by
  classical
  have : NeZero k := ⟨hk⟩
  unfold primSum
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij
    (fun x hx => changeLevel (Nat.dvd_of_mem_divisors (Finset.mem_sigma.1 hx).1) x.2)
    (fun _ _ => mem_univ _) ?_ ?_ ?_
  · rintro ⟨d1, ψ1⟩ h1 ⟨d2, ψ2⟩ h2 heq
    simp only [Finset.mem_sigma, Finset.mem_filter, mem_univ, true_and] at h1 h2
    have c1 := congrArg DirichletCharacter.conductor heq
    rw [conductor_changeLevel, conductor_changeLevel, h1.2, h2.2] at c1
    subst c1
    have := changeLevel_injective (Nat.dvd_of_mem_divisors h1.1) heq
    subst this
    rfl
  · intro χ _
    refine ⟨⟨χ.conductor, χ.primitiveCharacter⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_filter, mem_univ, true_and, Nat.mem_divisors]
      exact ⟨⟨χ.conductor_dvd_level, hk⟩, χ.primitiveCharacter_isPrimitive⟩
    · exact χ.changeLevel_primitiveCharacter
  · rintro ⟨d, ψ⟩ _
    exact (changeLevel_eq_cast_of_dvd' ψ _ ha).symm

/-- The full character sum mod `d ≠ 0` at an integer, in the form `gFull`. -/
theorem sum_all_eq_gFull {d : ℕ} (hd : d ≠ 0) (a : ℤ) :
    ∑ χ : DirichletCharacter ℂ d, χ (a : ZMod d) = gFull a d := by
  have : NeZero d := ⟨hd⟩
  rw [DirichletCharacter.sum_characters_eq, gFull]
  have : ((a : ZMod d) = 1) ↔ (d : ℤ) ∣ a - 1 := by
    rw [show (1 : ZMod d) = ((1 : ℤ) : ZMod d) by simp, ZMod.intCast_eq_intCast_iff_dvd_sub,
      ← dvd_neg, neg_sub]
  simp only [this]

/-- **Exact formula**: for `k ≠ 0` and `a` coprime to `k`,
`∑*_{χ mod k} χ(a) = ∑_{(e, d), e d = k} μ(e) [d ∣ a - 1] φ(d)`. -/
theorem primSum_eq_moebius {k : ℕ} (hk : k ≠ 0) {a : ℤ} (ha : IsCoprime a k) :
    primSum k a =
      ∑ x ∈ k.divisorsAntidiagonal, ((ArithmeticFunction.moebius x.1 : ℤ) : ℂ) * gFull a x.2 := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on (R := ℂ)
    (f := fun d => primSum d a) (g := gFull a) {n | n ∣ k}
    (fun m n hmn hn => dvd_trans hmn hn)).mp ?_ k (Nat.pos_of_ne_zero hk) (dvd_refl k)
  · simpa using h.symm
  · intro n hn hnk
    have hcop : IsCoprime a n := ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hnk)
    rw [← sum_all_eq_sum_primSum hn.ne' hcop, sum_all_eq_gFull hn.ne']

/-- The divisors of `k` that divide `a - 1` are the divisors of `(a - 1, k)`. -/
lemma filter_divisors_eq {k : ℕ} (hk : k ≠ 0) (a : ℤ) :
    k.divisors.filter (fun d : ℕ => (d : ℤ) ∣ a - 1) = (Int.gcd (a - 1) k).divisors := by
  have hg : Int.gcd (a - 1) k ≠ 0 :=
    (Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hk)).ne'
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Int.gcd, Int.natAbs_natCast]
  rw [Nat.dvd_gcd_iff, Int.natCast_dvd]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, h1⟩, by simpa [Int.gcd] using hg⟩
  · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h2, hk⟩, h1⟩

/-- **Chen 1973, Lemma 4, general modulus**: for every `k ≥ 1` and every integer `m`,
`|∑*_{χ mod k} χ(m)| ≤ (m - 1, k)`. Chen's hypotheses `m ≠ 1`, `k` odd and squarefree are not
needed. -/
theorem chen_lemma4 {k : ℕ} (hk : k ≠ 0) (m : ℤ) :
    ‖primSum k m‖ ≤ (Int.gcd (m - 1) k : ℝ) := by
  have : NeZero k := ⟨hk⟩
  by_cases hu : IsUnit (m : ZMod k)
  · have ha : IsCoprime m k :=
      isCoprime_comm.mp ((ZMod.coe_int_isUnit_iff_isCoprime m k).mp hu)
    rw [primSum_eq_moebius hk ha]
    calc ‖∑ x ∈ k.divisorsAntidiagonal,
            ((ArithmeticFunction.moebius x.1 : ℤ) : ℂ) * gFull m x.2‖
        ≤ ∑ x ∈ k.divisorsAntidiagonal,
            ‖((ArithmeticFunction.moebius x.1 : ℤ) : ℂ) * gFull m x.2‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ k.divisorsAntidiagonal,
            (if (x.2 : ℤ) ∣ m - 1 then (x.2.totient : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro x _
          rw [norm_mul, gFull]
          have hmu : ‖((ArithmeticFunction.moebius x.1 : ℤ) : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_intCast]
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          split_ifs
          · rw [Complex.norm_natCast]
            calc _ ≤ 1 * (x.2.totient : ℝ) := by gcongr
              _ = _ := one_mul _
          · simp
      _ = ∑ d ∈ k.divisors, (if (d : ℤ) ∣ m - 1 then (d.totient : ℝ) else 0) :=
          Nat.sum_divisorsAntidiagonal' (fun _ d => if (d : ℤ) ∣ m - 1 then (d.totient : ℝ) else 0)
      _ = ∑ d ∈ (Int.gcd (m - 1) k).divisors, (d.totient : ℝ) := by
          rw [← Finset.sum_filter, filter_divisors_eq hk]
      _ = (Int.gcd (m - 1) k : ℝ) := by
          rw [← Nat.cast_sum, Nat.sum_totient]
  · have h0 : primSum k m = 0 := by
      unfold primSum
      exact Finset.sum_eq_zero fun ψ _ => MulChar.map_nonunit ψ hu
    rw [h0, norm_zero]; positivity

/-- **Chen's Lemma 4 in his own wording**: `m ≠ 1`, `k` squarefree and odd. A specialization. -/
theorem chen_lemma4_as_stated {k : ℕ} (hk : k ≠ 0) (_hsq : Squarefree k) (_hodd : Odd k)
    {m : ℤ} (_hm : m ≠ 1) : ‖primSum k m‖ ≤ (Int.gcd (m - 1) k : ℝ) :=
  chen_lemma4 hk m

/-- Non-vacuity, `k = 15`, `m = 7`: the bound is `(6, 15) = 3`, and Chen's hypotheses hold. -/
example : ‖primSum 15 7‖ ≤ 3 := by
  have := chen_lemma4_as_stated (k := 15) (m := 7) (by norm_num)
    ((Nat.squarefree_mul_iff.mpr ⟨by norm_num, Nat.prime_three.squarefree,
      Nat.prime_five.squarefree⟩ : Squarefree (3 * 5)))
    (by decide) (by norm_num)
  have h3 : Int.gcd (7 - 1) ((15 : ℕ) : ℤ) = 3 := by rfl
  rw [h3] at this
  exact_mod_cast this

end LeanLab.AlmostPrimeSums.Chen1973Lemma4
