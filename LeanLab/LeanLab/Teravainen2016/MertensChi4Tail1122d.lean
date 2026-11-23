/-
P0076, Teravainen 2016, Section 4, page 15: the closing LEAF of the chi_4 Mertens split in
MertensChi41122b.lean, Davenport, Multiplicative Number Theory, Chapter 4: the prime powers
p ^ k with k at least 2 contribute a bounded amount to the sum of Lambda d / d.
Proof: nonzero terms are prime powers d = p ^ k, mapped injectively to the pair minFac d and
its exponent; the geometric tail over k at least 2 is at most 2 / p ^ 2, and log p is at most
2 p ^ 1/2, so the whole sum is at most the convergent sum of 4 / n ^ 3/2.
Then leaf_chi4_prime_powers1122b and leaf_mertens_chi4 are rebuilt without the LEAF.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.MertensChi41122b

open Finset Real
open scoped Classical ArithmeticFunction.vonMangoldt

namespace LeanLab.Teravainen2016

/-- The prime power tail for one p: the sum over k from 2 to N of log p / p ^ k is at most
4 / p ^ 3/2, by the geometric series and log p at most 2 p ^ 1/2. -/
lemma pp_tail_term_le1122d (p : ℕ) (N : ℕ) :
    ∑ k ∈ Ico 2 (N + 1), Real.log p / (p : ℝ) ^ k ≤ 4 * (((p : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  have hf0 : 0 ≤ 4 * (((p : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by positivity
  rcases lt_or_ge p 2 with hp | hp
  · interval_cases p <;> simp
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hx0 : 0 ≤ (1 / (p : ℝ)) := by positivity
  have hx1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; linarith
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 2) (n := N + 1) hx0 hx1
  have h1 : ∑ k ∈ Ico 2 (N + 1), Real.log p / (p : ℝ) ^ k
      = Real.log p * ∑ k ∈ Ico 2 (N + 1), (1 / (p : ℝ)) ^ k := by
    rw [mul_sum]; apply sum_congr rfl; intro k _; rw [one_div_pow]; ring
  have h2 : (1 / (p : ℝ)) ^ 2 / (1 - 1 / p) ≤ 2 / (p : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by rw [sub_pos]; exact hx1) (by positivity)]
    field_simp
    nlinarith
  have hl : Real.log p ≤ (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div hp0.le (by norm_num)
  have hsplit : (p : ℝ) ^ 2 = (p : ℝ) ^ (1 / 2 : ℝ) * (p : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hp0]; norm_num
  have hA : 0 < (p : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hp0 _
  have hB : 0 < (p : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hp0 _
  rw [h1]
  calc Real.log p * ∑ k ∈ Ico 2 (N + 1), (1 / (p : ℝ)) ^ k
      ≤ Real.log p * (2 / (p : ℝ) ^ 2) := by gcongr; exact hgeom.trans h2
    _ ≤ (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) * (2 / (p : ℝ) ^ 2) := by gcongr
    _ = 4 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
      rw [hsplit]; field_simp; ring

/-- Proved form of the LEAF leaf_vonMangoldt_nonprime_bounded1122b of MertensChi41122b.lean,
Davenport Chapter 4: the nonprime d contribute a bounded amount to the sum of Lambda d / d. -/
theorem leaf_vonMangoldt_nonprime_bounded1122b_proved :
    type_of% @leaf_vonMangoldt_nonprime_bounded1122b := by
  set f : ℕ → ℝ := fun n => 4 * (((n : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ with hfdef
  have hs : Summable f := (Real.summable_nat_rpow_inv.2 (by norm_num)).mul_left 4
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [hfdef]; positivity
  refine ⟨∑' n, f n, tsum_nonneg hf0, fun N => ?_⟩
  set S := (Ioc 0 N).filter (fun d => ¬ d.Prime)
  set g : ℕ × ℕ → ℝ := fun q => Real.log q.1 / (q.1 : ℝ) ^ q.2 with hg
  set φ : ℕ → ℕ × ℕ := fun d => (d.minFac, d.factorization d.minFac) with hφ
  have hstep1 : ∑ d ∈ S, Λ d / d = ∑ d ∈ S.filter IsPrimePow, Λ d / d := by
    refine (sum_filter_of_ne fun d _ hd => ?_).symm
    by_contra hpp
    apply hd
    rw [ArithmeticFunction.vonMangoldt_apply, if_neg hpp, zero_div]
  have hstep2 : ∑ d ∈ S.filter IsPrimePow, Λ d / d = ∑ d ∈ S.filter IsPrimePow, g (φ d) := by
    apply sum_congr rfl; intro d hd
    have hpp : IsPrimePow d := (mem_filter.1 hd).2
    have he := hpp.minFac_pow_factorization_eq
    simp only [hg, hφ]
    rw [ArithmeticFunction.vonMangoldt_apply, if_pos hpp]
    congr 1
    conv_lhs => rw [← he]
    push_cast; rfl
  have hinj : Set.InjOn φ (S.filter IsPrimePow) := by
    intro a ha b hb hab
    have ea := (mem_filter.1 ha).2.minFac_pow_factorization_eq
    have eb := (mem_filter.1 hb).2.minFac_pow_factorization_eq
    simp only [hφ, Prod.mk.injEq] at hab
    rw [← ea, ← eb, hab.2, hab.1]
  set T := range (N + 1) ×ˢ Ico 2 (N + 1)
  have hsub : (S.filter IsPrimePow).image φ ⊆ T := by
    intro q hq
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hq
    obtain ⟨hdS, hpp⟩ := mem_filter.1 hd
    obtain ⟨hdI, hnp⟩ := mem_filter.1 hdS
    obtain ⟨hd0, hdN⟩ := mem_Ioc.1 hdI
    have he := hpp.minFac_pow_factorization_eq
    have hd1 : d ≠ 1 := fun h => by subst h; exact not_isPrimePow_one hpp
    have hpr : d.minFac.Prime := Nat.minFac_prime hd1
    set k := d.factorization d.minFac
    have hk0 : k ≠ 0 := fun h => by rw [h, pow_zero] at he; exact hd1 he.symm
    have hk1 : k ≠ 1 := fun h => by rw [h, pow_one] at he; exact hnp (he ▸ hpr)
    have hklt : k < d := by
      calc k < 2 ^ k := Nat.lt_two_pow_self
        _ ≤ d.minFac ^ k := Nat.pow_le_pow_left hpr.two_le k
        _ = d := he
    simp only [T, φ, mem_product, mem_range, mem_Ico]
    refine ⟨by have := Nat.minFac_le hd0; omega, by omega, by omega⟩
  have hgnn : ∀ q ∈ T, 0 ≤ g q := fun q _ => by
    simp only [hg]; exact div_nonneg (Real.log_natCast_nonneg _) (by positivity)
  calc ∑ d ∈ S, Λ d / d = ∑ q ∈ (S.filter IsPrimePow).image φ, g q := by
        rw [hstep1, hstep2, sum_image hinj]
    _ ≤ ∑ q ∈ T, g q := sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => hgnn q hq)
    _ = ∑ p ∈ range (N + 1), ∑ k ∈ Ico 2 (N + 1), Real.log p / (p : ℝ) ^ k := by
        rw [sum_product]
    _ ≤ ∑ p ∈ range (N + 1), f p := sum_le_sum fun p _ => pp_tail_term_le1122d p N
    _ ≤ ∑' n, f n := hs.sum_le_tsum _ (fun i _ => hf0 i)

/-- Twin of leaf_chi4_prime_powers1122b rebuilt from the proved bound above, with the same
proof as in MertensChi41122b.lean. -/
theorem chi4_prime_powers_proved1122d : type_of% @leaf_chi4_prime_powers1122b := by
  intro χ hχ
  obtain ⟨B, hB, HB⟩ := leaf_vonMangoldt_nonprime_bounded1122b_proved
  refine ⟨B, hB, fun N => ?_⟩
  have hset : (Ioc 0 N).filter Nat.Prime = Nat.primesLE N := by
    ext p
    simp only [mem_filter, mem_Ioc, Nat.primesLE, Nat.primesBelow, mem_range]
    constructor
    · rintro ⟨⟨_, h2⟩, hp⟩; exact ⟨by omega, hp⟩
    · rintro ⟨h1, hp⟩; exact ⟨⟨hp.pos, by omega⟩, hp⟩
  have hsplit := (sum_filter_add_sum_filter_not (Ioc 0 N) Nat.Prime (fun d => χ d * Λ d / d)).symm
  have hprime : ∑ d ∈ (Ioc 0 N).filter Nat.Prime, χ d * Λ d / d =
      ∑ p ∈ Nat.primesLE N, χ p * log p / p := by
    rw [hset]; apply sum_congr rfl; intro p hp
    have hp' : p.Prime := (Nat.mem_primesLE.1 hp).2
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp']
  rw [hsplit, hprime, add_sub_cancel_left]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun d _ => ?_).trans (HB N))
  have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
  rw [abs_div, abs_mul, abs_of_nonneg hΛ, Nat.abs_cast]
  have hχ1 : |χ d| ≤ 1 := by rw [hχ]; split_ifs <;> simp
  gcongr
  calc |χ d| * Λ d ≤ 1 * Λ d := by gcongr
    _ = Λ d := one_mul _

/-- The closed Mertens theorem for chi_4, the statement of the LEAF leaf_mertens_chi4 of
MertensMod4Bias.lean, Davenport Chapter 4, with the same proof as leaf_mertens_chi4_of_leaves
but using the proved prime power bound. -/
theorem leaf_mertens_chi4_proved1122d : type_of% @leaf_mertens_chi4 := by
  set χ : ℕ → ℝ := fun n => if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0 with hχd
  have hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0 :=
    fun n => rfl
  obtain ⟨B1, hB1, H1⟩ := chi4_vonMangoldt_bounded1122b χ hχ
  obtain ⟨B2, hB2, H2⟩ := chi4_prime_powers_proved1122d χ hχ
  refine ⟨B1 + B2, by positivity, fun x _ => ?_⟩
  set N := ⌊x⌋₊
  have h := H2 N
  have h1 := H1 N
  change |∑ p ∈ Nat.primesLE N, χ p * log p / p| ≤ B1 + B2
  have := abs_sub_abs_le_abs_sub (∑ p ∈ Nat.primesLE N, χ p * log p / p)
    (∑ d ∈ Ioc 0 N, χ d * Λ d / d)
  rw [abs_sub_comm] at this
  linarith

end LeanLab.Teravainen2016

#print axioms LeanLab.Teravainen2016.leaf_vonMangoldt_nonprime_bounded1122b_proved
#print axioms LeanLab.Teravainen2016.chi4_prime_powers_proved1122d
#print axioms LeanLab.Teravainen2016.leaf_mertens_chi4_proved1122d
