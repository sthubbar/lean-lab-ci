/-
Gallagher 1975 p.134 after display 6. General base arithmetic support.
Source https://doi.org/10.1007/BF01390190
The exponent convention is positive powers as in display 3.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.Linnik.Decomp554b

/-- Gallagher 1975 p.134 after display 6. Every difference of two equal length
sums of positive powers of g is divisible by g times g minus one. -/
theorem tuple_difference_divisible (g k : ℕ) (hg : 2 ≤ g)
    (ν μ : Fin k → ℕ) (hν : ∀ i, 1 ≤ ν i) (hμ : ∀ i, 1 ≤ μ i) :
    ((g * (g - 1) : ℕ) : ℤ) ∣
      (∑ i, (g : ℤ) ^ ν i) - ∑ i, (g : ℤ) ^ μ i := by
  have hcast : ((g * (g - 1) : ℕ) : ℤ) = (g : ℤ) * ((g : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ g), Nat.cast_one]
  rw [hcast]
  have hd (a : ℕ) (ha : 1 ≤ a) :
      (g : ℤ) * ((g : ℤ) - 1) ∣ (g : ℤ) ^ a - (g : ℤ) := by
    have h := mul_dvd_mul_left (g : ℤ) (sub_one_dvd_pow_sub_one (g : ℤ) (a - 1))
    simpa only [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel ha] using h
  have hleft := Finset.dvd_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hd (ν i) (hν i))
  have hright := Finset.dvd_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hd (μ i) (hμ i))
  have h := dvd_sub hleft hright
  simpa only [Finset.sum_sub_distrib, sub_sub_sub_cancel_right] using h

/-- Gallagher 1975 p.134 proof of Lemma 5. A sorted sum of two powers
of any integer base at least two determines both exponents. -/
theorem sorted_power_pair_injective (g : ℕ) (hg : 2 ≤ g)
    (a b c d : ℕ) (hab : a ≤ b) (hcd : c ≤ d)
    (h : g ^ a + g ^ b = g ^ c + g ^ d) : a = c ∧ b = d := by
  have bound (u v : ℕ) (huv : u ≤ v) : g ^ u + g ^ v ≤ g ^ (v + 1) := by
    have hpow := Nat.pow_le_pow_right (by omega : 0 < g) huv
    rw [pow_succ]
    have hm := Nat.mul_le_mul_left (g ^ v) hg
    omega
  have max_le (u v w z : ℕ) (huv : u ≤ v)
      (heq : g ^ u + g ^ v = g ^ w + g ^ z) : z ≤ v := by
    by_contra hz
    have hvz : v + 1 ≤ z := by omega
    have hp := (bound u v huv).trans (Nat.pow_le_pow_right (by omega : 0 < g) hvz)
    have hw : 0 < g ^ w := pow_pos (by omega) _
    omega
  have hbd : b = d := le_antisymm (max_le c d a b hcd h.symm) (max_le a b c d hab h)
  subst d
  have hac : g ^ a = g ^ c := Nat.add_right_cancel h
  exact ⟨(Nat.pow_right_inj (by omega : 1 < g)).mp hac, rfl⟩

/-- Gallagher 1975 p.134 proof of Lemma 5. Two sums of two powers
of g are equal only for the same two exponents, allowing interchange. -/
theorem power_pair_eq_or_swap (g : ℕ) (hg : 2 ≤ g) (a b c d : ℕ)
    (h : g ^ a + g ^ b = g ^ c + g ^ d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases le_total a b with hab | hba
  · rcases le_total c d with hcd | hdc
    · exact Or.inl (sorted_power_pair_injective g hg a b c d hab hcd h)
    · exact Or.inr (sorted_power_pair_injective g hg a b d c hab hdc (by omega))
  · rcases le_total c d with hcd | hdc
    · have he := sorted_power_pair_injective g hg b a c d hba hcd (by omega)
      exact Or.inr ⟨he.2, he.1⟩
    · have he := sorted_power_pair_injective g hg b a d c hba hdc (by omega)
      exact Or.inl ⟨he.2, he.1⟩

/-- Gallagher 1975 p.134 proof of Lemma 5. Any natural n has at most
two ordered representations as the sum of two positive powers of g with exponents at most L. -/
theorem card_power_pairs_le_two (g : ℕ) (hg : 2 ≤ g) (L n : ℕ) :
    ((Finset.Icc 1 L ×ˢ Finset.Icc 1 L).filter
      (fun x => g ^ x.1 + g ^ x.2 = n)).card ≤ 2 := by
  classical
  let S := (Finset.Icc 1 L ×ˢ Finset.Icc 1 L).filter
    (fun x => g ^ x.1 + g ^ x.2 = n)
  change S.card ≤ 2
  by_cases hs : S.Nonempty
  · obtain ⟨x, hx⟩ := hs
    have hsub : S ⊆ {x, (x.2, x.1)} := by
      intro y hy
      have he := (Finset.mem_filter.mp hy).2.trans (Finset.mem_filter.mp hx).2.symm
      rcases power_pair_eq_or_swap g hg _ _ _ _ he with h | h
      · simp [Prod.ext h.1 h.2]
      · simp [show y = (x.2, x.1) from Prod.ext h.1 h.2]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

/-- Gallagher 1975 p.134 Lemma 5 display 4. For every base at least two,
the zero shift count of two k-tuples is at most `2 * L ^ (2*k-2)`. -/
theorem zero_shift_count_general_base (g : ℕ) (hg : 2 ≤ g)
    (k L : ℕ) (hk : 2 ≤ k) :
    ((Finset.univ : Finset ((Fin k → Fin L) × (Fin k → Fin L))).filter
      (fun x => (∑ i, g ^ ((x.1 i : ℕ) + 1)) = ∑ i, g ^ ((x.2 i : ℕ) + 1))).card ≤
      2 * L ^ (2 * k - 2) := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  let X := (Fin (j + 2) → Fin L) × (Fin (j + 2) → Fin L)
  let Y := (Fin (j + 2) → Fin L) × (Fin j → Fin L)
  let S : Finset X := Finset.univ.filter (fun x =>
    (∑ i, g ^ ((x.1 i : ℕ) + 1)) = ∑ i, g ^ ((x.2 i : ℕ) + 1))
  let f : X → Y := fun x => (x.1, fun i => x.2 i.succ.succ)
  have hfiber (b : Y) : (S.filter (fun x => f x = b)).card ≤ 2 := by
    let F := S.filter (fun x => f x = b)
    change F.card ≤ 2
    by_cases hF : F.Nonempty
    · obtain ⟨x, hx⟩ := hF
      let swap : X := (x.1, Fin.cons (x.2 1)
        (Fin.cons (x.2 0) (fun i => x.2 i.succ.succ)))
      have hsub : F ⊆ {x, swap} := by
        intro y hy
        have hyS := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
        have hxS := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
        have hyf := (Finset.mem_filter.mp hy).2
        have hxf := (Finset.mem_filter.mp hx).2
        have heq : f y = f x := hyf.trans hxf.symm
        have hν : y.1 = x.1 := congrArg (fun z : Y => z.1) heq
        have htail : (fun i : Fin j => y.2 i.succ.succ) =
            (fun i : Fin j => x.2 i.succ.succ) := congrArg Prod.snd heq
        have hsum : (∑ i, g ^ ((y.2 i : ℕ) + 1)) =
            ∑ i, g ^ ((x.2 i : ℕ) + 1) := by rw [← hyS, ← hxS, hν]
        have ht : (∑ i : Fin j, g ^ ((y.2 i.succ.succ : ℕ) + 1)) =
            ∑ i : Fin j, g ^ ((x.2 i.succ.succ : ℕ) + 1) :=
          congrArg (fun z : Fin j → Fin L => ∑ i, g ^ ((z i : ℕ) + 1)) htail
        simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one] at hsum
        have hp : g ^ ((y.2 0 : ℕ) + 1) + g ^ ((y.2 1 : ℕ) + 1) =
            g ^ ((x.2 0 : ℕ) + 1) + g ^ ((x.2 1 : ℕ) + 1) := by omega
        rcases power_pair_eq_or_swap g hg _ _ _ _ hp with hp | hp
        · have h0 : y.2 0 = x.2 0 := Fin.ext (by omega)
          have h1 : y.2 1 = x.2 1 := Fin.ext (by omega)
          have hμ : y.2 = x.2 := by
            funext i
            refine Fin.cases h0 (fun a => Fin.cases h1 (fun b => congrFun htail b) a) i
          have hxy : y = x := Prod.ext hν hμ
          simp [hxy]
        · have h0 : y.2 0 = x.2 1 := Fin.ext (by omega)
          have h1 : y.2 1 = x.2 0 := Fin.ext (by omega)
          have hμ : y.2 = swap.2 := by
            funext i
            refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => ?_) a) i
            · exact h0
            · exact h1
            · exact congrFun htail b
          have hxy : y = swap := Prod.ext hν hμ
          simp [hxy]
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    · simp [Finset.not_nonempty_iff_eq_empty.mp hF]
  have hcard := Finset.card_le_mul_card_image_of_maps_to
    (f := f) (s := S) (t := Finset.univ) (fun _ _ => Finset.mem_univ _) 2
    (fun b _ => hfiber b)
  change S.card ≤ _
  simpa [Y, Fintype.card_prod, Fintype.card_fun, ← pow_add,
    show j + 2 + j = 2 * (j + 2) - 2 by omega] using hcard

end LeanLab.Linnik.Decomp554b
#print axioms LeanLab.Linnik.Decomp554b.tuple_difference_divisible

#print axioms LeanLab.Linnik.Decomp554b.sorted_power_pair_injective

#print axioms LeanLab.Linnik.Decomp554b.power_pair_eq_or_swap

#print axioms LeanLab.Linnik.Decomp554b.card_power_pairs_le_two

#print axioms LeanLab.Linnik.Decomp554b.zero_shift_count_general_base
