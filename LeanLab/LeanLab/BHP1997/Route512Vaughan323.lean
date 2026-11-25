/-
P0069 Baker Harman Pintz 1997, page 8, display 2.7, which cites Vaughan reference 31,
The Hardy-Littlewood Method, Cambridge 1981, chapter 3, book page 34, display 3.23.
Split of `Section2MS.leaf_vaughan_323_512` into two cited LEAF pieces of Vaughan's
proof of 3.23 and a CONDITIONAL assembly theorem with the verbatim statement.
Burst burst-20261122 session S64. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp512a
import LeanLab.BHP1997.RamanujanS72
import LeanLab.BHP1997.TotientTailS72

namespace LeanLab.BHP1997.Section2MS
open Classical

/-- LEAF: Vaughan 1981 chapter 3, display 3.14 and the evaluation of the Ramanujan sum used
in the proof of display 3.23 on book page 34: for squarefree q the Ramanujan sum
c_q(-m) = Σ_{(a,q)=1} e(-am/q) equals μ(q/(q,m)) φ((q,m)), so its absolute value is
φ((q,m)). Class EASY: the lab's private `c512_real_form` in Decomp512a writes c_q as
Σ_{d|q} [q/d ∣ m] (q/d) μ(d), and for squarefree q = g r with g = (q,m) this is
μ(r) Σ_{e|g} e μ(g/e) = μ(r) φ(g). -/
theorem leaf_ramanujan_sqfree_norm512 (q N : ℕ) (hq : Squarefree q) :
    ‖ramanujan512 q N‖ ≤ (Nat.totient (Nat.gcd q N) : ℝ) :=
  ramanujan_sqfree_normS72 q N hq

/-- LEAF: Vaughan 1981 chapter 3, book page 34, the elementary fact printed under display
3.23: Σ_{q>Z} φ(q)^{-2} ≪ Z^{-1}, together with the convergence of Σ_q φ(q)^{-2}, which
gives the bound min(Z^{-1}, 1) for every Z > 0, uniformly in the upper cutoff R.
Class MEDIUM: from Σ_{q≤R} (q/φ(q))² ≪ R, which follows from
q/φ(q) = Σ_{d|q} μ(d)²/φ(d), and partial summation. PROVED in `TotientTailS72`,
session S72, by an elementary Euler product argument. -/
theorem leaf_totient_sq_tail512 :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Z : ℝ, 0 < Z → ∀ R : ℕ,
      ∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)),
          1 / (Nat.totient r : ℝ) ^ 2 ≤ K * min (1 / Z) 1 :=
  TotientTailS72.leaf_totient_sq_tail512

/-- Vaughan 1981 display 3.23 at m = N, verbatim statement of
`Section2MS.leaf_vaughan_323_512`, CONDITIONAL ON the two LEAFs above. The proof is Vaughan's:
drop the non squarefree q, bound the Ramanujan sum by φ((q,N)), sort q by g = (q,N),
write q = g r with (g,r) = 1 so φ(q) = φ(g) φ(r), and sum the tail over r > X/g. -/
theorem leaf_vaughan_323_512_of_leaves :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → ∀ X : ℝ, 0 < X → ∀ M : ℕ,
      ‖∑ q ∈ Finset.Ioc ⌊X⌋₊ M,
          (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
            ramanujan512 q N‖ ≤
        K * ∑ d ∈ N.divisors,
          (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ) *
            min ((d : ℝ) / X) 1 := by
  obtain ⟨K, hK0, hK⟩ := leaf_totient_sq_tail512
  refine ⟨K, hK0, fun N hN X hX M => ?_⟩
  set S := Finset.Ioc ⌊X⌋₊ M with hS
  let f : ℕ → ℝ := fun q =>
    if Squarefree q then (Nat.totient (Nat.gcd q N) : ℝ) / (Nat.totient q : ℝ) ^ 2 else 0
  have hf0 : ∀ q, 0 ≤ f q := by
    intro q; simp only [f]; split_ifs <;> positivity
  -- step 1: triangle inequality and the Ramanujan bound
  have step1 : ‖∑ q ∈ S, (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
      ramanujan512 q N‖ ≤ ∑ q ∈ S, f q := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    by_cases hq : Squarefree q
    · have hmu : (ArithmeticFunction.moebius q : ℂ) ^ 2 = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq
        exact_mod_cast this
      simp only [f, if_pos hq, hmu, norm_mul, norm_div, norm_one, norm_pow,
        Complex.norm_natCast]
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right (leaf_ramanujan_sqfree_norm512 q N hq) (by positivity)
    · have hmu : (ArithmeticFunction.moebius q : ℂ) = 0 := by
        have := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq
        exact_mod_cast this
      simp [f, hq]
  -- step 2: sort by g = gcd q N
  have hN0 : N ≠ 0 := by omega
  have hmaps : ∀ q ∈ S, Nat.gcd q N ∈ N.divisors := by
    intro q _
    exact Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right q N, hN0⟩
  have step2 : ∑ q ∈ S, f q =
      ∑ g ∈ N.divisors, ∑ q ∈ S.filter (fun q => Nat.gcd q N = g), f q :=
    (Finset.sum_fiberwise_of_maps_to hmaps f).symm
  -- step 3: each fiber
  have step3 : ∀ g ∈ N.divisors, ∑ q ∈ S.filter (fun q => Nat.gcd q N = g), f q ≤
      K * ((ArithmeticFunction.moebius g : ℝ) ^ 2 / (Nat.totient g : ℝ) *
        min ((g : ℝ) / X) 1) := by
    intro g hg
    have hgpos : 0 < g := Nat.pos_of_mem_divisors hg
    by_cases hsg : Squarefree g
    · have hmu : (ArithmeticFunction.moebius g : ℝ) ^ 2 = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsg
        exact_mod_cast this
      rw [hmu]
      have hphig : (0 : ℝ) < Nat.totient g := by exact_mod_cast Nat.totient_pos.2 hgpos
      let h : ℕ → ℝ := fun r => 1 / (Nat.totient r : ℝ) ^ 2
      have hle : ∀ q ∈ S.filter (fun q => Nat.gcd q N = g),
          f q ≤ 1 / (Nat.totient g : ℝ) * h (q / g) := by
        intro q hq
        rw [Finset.mem_filter] at hq
        by_cases hsq : Squarefree q
        · have hgq : g ∣ q := hq.2 ▸ Nat.gcd_dvd_left q N
          have hqe : q = g * (q / g) := (Nat.mul_div_cancel' hgq).symm
          have hcop : Nat.Coprime g (q / g) :=
            Nat.coprime_of_squarefree_mul (hqe ▸ hsq)
          have htot : (Nat.totient q : ℝ) =
              (Nat.totient g : ℝ) * (Nat.totient (q / g) : ℝ) := by
            conv_lhs => rw [hqe]
            rw [Nat.totient_mul hcop]; push_cast; ring
          simp only [f, h, if_pos hsq, hq.2, htot]
          have hr : (0 : ℝ) < Nat.totient (q / g) := by
            have hq0 : 0 < q := by
              rcases Nat.eq_zero_or_pos q with h0 | h0
              · exact absurd (h0 ▸ hsq) not_squarefree_zero
              · exact h0
            have : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq0 hgq) hgpos
            exact_mod_cast Nat.totient_pos.2 this
          field_simp
          ring_nf
          exact le_refl _
        · simp only [f, if_neg hsq]
          simp only [h]; positivity
      refine (Finset.sum_le_sum hle).trans ?_
      rw [← Finset.mul_sum]
      have hinj : Set.InjOn (fun q => q / g) ↑(S.filter (fun q => Nat.gcd q N = g)) := by
        intro a ha b hb hab
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
        have ha' : g ∣ a := ha.2 ▸ Nat.gcd_dvd_left a N
        have hb' : g ∣ b := hb.2 ▸ Nat.gcd_dvd_left b N
        simp only at hab
        rw [← Nat.mul_div_cancel' ha', ← Nat.mul_div_cancel' hb', hab]
      rw [← Finset.sum_image (f := h) hinj]
      have hsub : (S.filter (fun q => Nat.gcd q N = g)).image (fun q => q / g) ⊆
          (Finset.Icc 1 M).filter (fun r : ℕ => X / g < (r : ℝ)) := by
        intro r hr
        rw [Finset.mem_image] at hr
        obtain ⟨q, hq, rfl⟩ := hr
        rw [Finset.mem_filter, hS, Finset.mem_Ioc] at hq
        have hgq : g ∣ q := hq.2 ▸ Nat.gcd_dvd_left q N
        have hXq : X < (q : ℝ) := Nat.lt_of_floor_lt hq.1.1
        have hq0 : 0 < q := by
          have : (0 : ℝ) < q := lt_trans hX hXq
          exact_mod_cast this
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.div_pos (Nat.le_of_dvd hq0 hgq) hgpos,
          le_trans (Nat.div_le_self q g) hq.1.2⟩, ?_⟩
        have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
        rw [div_lt_iff₀ hgR]
        have : ((q / g : ℕ) : ℝ) * g = q := by
          rw [← Nat.cast_mul, Nat.div_mul_cancel hgq]
        rw [this]; exact hXq
      have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
      have htail := hK (X / g) (div_pos hX hgR) M
      have hmono := Finset.sum_le_sum_of_subset_of_nonneg (f := h) hsub
        (fun r _ _ => by simp only [h]; positivity)
      rw [one_div_div] at htail
      calc 1 / (Nat.totient g : ℝ) * ∑ r ∈ (S.filter (fun q => Nat.gcd q N = g)).image
              (fun q => q / g), h r
          ≤ 1 / (Nat.totient g : ℝ) * (K * min ((g : ℝ) / X) 1) := by
            apply mul_le_mul_of_nonneg_left (hmono.trans htail)
            positivity
        _ = K * (1 / (Nat.totient g : ℝ) * min ((g : ℝ) / X) 1) := by ring
    · have hzero : ∀ q ∈ S.filter (fun q => Nat.gcd q N = g), f q = 0 := by
        intro q hq
        rw [Finset.mem_filter] at hq
        have hgq : g ∣ q := hq.2 ▸ Nat.gcd_dvd_left q N
        have hsq : ¬ Squarefree q := fun hs => hsg (Squarefree.squarefree_of_dvd hgq hs)
        simp only [f, if_neg hsq]
      rw [Finset.sum_eq_zero hzero]
      apply mul_nonneg hK0
      positivity
  calc _ ≤ ∑ q ∈ S, f q := step1
    _ = _ := step2
    _ ≤ ∑ g ∈ N.divisors, K * ((ArithmeticFunction.moebius g : ℝ) ^ 2 /
          (Nat.totient g : ℝ) * min ((g : ℝ) / X) 1) := Finset.sum_le_sum step3
    _ = _ := by rw [Finset.mul_sum]

/-- Verbatim check: the assembly has exactly the type of `leaf_vaughan_323_512`. -/
example : type_of% leaf_vaughan_323_512 := leaf_vaughan_323_512_of_leaves

end LeanLab.BHP1997.Section2MS
