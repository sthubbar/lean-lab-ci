/-
P0083 Perelli 1996, page 482, equation 6 of the proof of the named Lemma.
ROUTE BURST S79 burst-20261122 split of Diff1122.leaf_weyl_differencing.
The k-1 fold Weyl differencing and the count of difference tuples by τ_k are LEAFs;
grouping the tuples by the frequency m and choosing one interval per m is proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.VaughanInput

namespace LeanLab.Perelli1996.Weyl1122
open Finset Real Polynomial
open LeanLab.Perelli1996.Section2
noncomputable section

/-- The difference tuples (h_1, ..., h_(k-1)) with 1 ≤ |h_i| ≤ R. -/
abbrev tuples (k R : ℕ) : Finset (Fin (k - 1) → ℤ) :=
  Fintype.piFinset fun _ => (Icc (-(R : ℤ)) R).filter (· ≠ 0)

/-- The frequency k! a_k |h_1 ⋯ h_(k-1)| of the linear (k-1)-th difference, page 482. -/
abbrev freq (k a : ℕ) (h : Fin (k - 1) → ℤ) : ℕ := k.factorial * a * (∏ i, h i).natAbs

/-- LEAF: Page 482 equation 6, first half, as in Vaughan 1981 Lemma 2.4 with j = k-1:
|K(F,α)|^K ≪ H^(K-k) (H^(k-1) + ∑_h |∑_{n ∈ I_h} e(α k! a_k h_1⋯h_(k-1) n)|), the sum over
tuples with 1 ≤ |h_i| ≤ H, the tuples with some h_i = 0 contributing H^(k-1), and I_h an
interval of at most H+1 consecutive integers. The constant term of the linear difference
and the sign of the product do not change the modulus. Class MEDIUM. -/
theorem leaf_iterated_differencing (F : ℤ[X]) (hF : Admissible F) (hk : 2 ≤ F.natDegree) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧
      ∀ N H α : ℝ, N₀ ≤ N → 1 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∃ start len : (Fin (F.natDegree - 1) → ℤ) → ℕ, (∀ h, (len h : ℝ) ≤ H + 1) ∧
        ‖polynomialKernel F N H α‖ ^ weylExponent F ≤
          C * H ^ (weylExponent F - F.natDegree) *
            (H ^ (F.natDegree - 1) +
              ∑ h ∈ tuples F.natDegree ⌊H⌋₊,
                ‖Kernel.T (start h) (len h) (α * (freq F.natDegree F.leadingCoeff.natAbs h : ℕ))‖) := by
  sorry

/-- Page 482 equation 6, second half: the number of tuples with
k! a |h_1⋯h_(k-1)| = m is at most 2^(k-1) τ_(k-1)(m/(k! a)) ≤ 2^(k-1) τ_k(m).
Burst S8 burst-20261124 unit S8-14: no longer a LEAF, proved outright. The sign map
h ↦ |h| has fibres of size at most 2^(k-1) and lands in the ordered k-1 factorizations
of m/(k! a); their number is at most τ_(k-1)(m/(k! a)) by induction on k, and that is
at most τ_k(m) since m/(k! a) divides m. -/
theorem leaf_tuple_count (k a R m : ℕ) (hk : 2 ≤ k) (ha : 1 ≤ a) :
    (((tuples k R).filter (fun h => freq k a h = m)).card : ℝ) ≤
      2 ^ (k - 1) * (divisorCount k m : ℝ) := by
  classical
  -- the zeta power card bound: #{d-tuples with product n} ≤ (ζ^d)(n)
  have hcard : ∀ d n : ℕ, (Nat.finMulAntidiag d n).card ≤ (ArithmeticFunction.zeta ^ d) n := by
    intro d
    induction d with
    | zero =>
      intro n
      by_cases hn : n = 1
      · subst hn
        rw [Nat.finMulAntidiag_one, pow_zero]
        simp
      · rw [Nat.finMulAntidiag_zero_left hn]
        simp
    | succ d ih =>
      intro n
      have hsub : Nat.finMulAntidiag (d + 1) n ⊆ n.divisors.biUnion
          (fun b => (Nat.finMulAntidiag d (n / b)).image (fun g => (Fin.cons b g : Fin (d + 1) → ℕ))) := by
        intro f hf
        have hf' := Nat.mem_finMulAntidiag.mp hf
        rw [Finset.mem_biUnion]
        refine ⟨f 0, Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_finMulAntidiag hf 0, hf'.2⟩, ?_⟩
        rw [Finset.mem_image]
        refine ⟨Fin.tail f, ?_, Fin.cons_self_tail f⟩
        rw [Nat.mem_finMulAntidiag]
        have h0 : f 0 ≠ 0 := Nat.ne_zero_of_mem_finMulAntidiag hf 0
        have hp : f 0 * ∏ i, Fin.tail f i = n := by
          rw [← hf'.1, Fin.prod_univ_succ]; rfl
        refine ⟨?_, ?_⟩
        · rw [← hp, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h0)]
        · intro hz
          rw [← hp, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h0)] at hz
          rw [hz, mul_zero] at hp
          exact hf'.2 hp.symm
      calc (Nat.finMulAntidiag (d + 1) n).card
          ≤ (n.divisors.biUnion (fun b => (Nat.finMulAntidiag d (n / b)).image
              (fun g => (Fin.cons b g : Fin (d + 1) → ℕ)))).card := Finset.card_le_card hsub
        _ ≤ ∑ b ∈ n.divisors, ((Nat.finMulAntidiag d (n / b)).image
              (fun g => (Fin.cons b g : Fin (d + 1) → ℕ))).card := Finset.card_biUnion_le
        _ ≤ ∑ b ∈ n.divisors, (ArithmeticFunction.zeta ^ d) (n / b) :=
            Finset.sum_le_sum (fun b _ => Finset.card_image_le.trans (ih _))
        _ = ∑ b ∈ n.divisors, (ArithmeticFunction.zeta ^ d) b := Nat.sum_div_divisors n _
        _ = (ArithmeticFunction.zeta ^ (d + 1)) n := by
            rw [pow_succ', ← ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.natCoe_nat]
  set c := k.factorial * a with hc
  have hc1 : 1 ≤ c := Nat.mul_pos (Nat.factorial_pos k) ha
  set S := (tuples k R).filter (fun h => freq k a h = m) with hS
  by_cases hne : S.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  obtain ⟨h₀, hh₀⟩ := hne
  have hmem : ∀ h ∈ S, (∀ i, h i ≠ 0) ∧ c * (∏ i, h i).natAbs = m := by
    intro h hh
    rw [hS, Finset.mem_filter, Fintype.mem_piFinset] at hh
    exact ⟨fun i => (Finset.mem_filter.mp (hh.1 i)).2, hh.2⟩
  have hprodabs : ∀ h : Fin (k - 1) → ℤ, (∏ i, h i).natAbs = ∏ i, (h i).natAbs :=
    fun h => map_prod Int.natAbsHom h Finset.univ
  obtain ⟨hnz₀, hm₀⟩ := hmem h₀ hh₀
  have hp₀ : (∏ i, h₀ i).natAbs ≠ 0 := by
    rw [hprodabs]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by simpa using hnz₀ i)
  have hm0 : m ≠ 0 := by
    rw [← hm₀]; exact Nat.mul_ne_zero (by omega) hp₀
  have hcm : c ∣ m := ⟨_, hm₀.symm⟩
  set n := m / c with hn
  have hnm : n ∣ m := Nat.div_dvd_of_dvd hcm
  -- the sign map h ↦ |h| sends S into the ordered k-1 factorizations of n
  let g : (Fin (k - 1) → ℤ) → (Fin (k - 1) → ℕ) := fun h i => (h i).natAbs
  have himg : S.image g ⊆ Nat.finMulAntidiag (k - 1) n := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨_, hmh⟩ := hmem h hh
    rw [Nat.mem_finMulAntidiag]
    refine ⟨?_, ?_⟩
    · show ∏ i, (h i).natAbs = n
      rw [← hprodabs, hn, ← hmh, Nat.mul_div_cancel_left _ (by omega)]
    · intro h0
      rw [hn] at h0
      have := Nat.div_mul_cancel hcm
      rw [h0, zero_mul] at this
      exact hm0 this.symm
  -- each fibre of the sign map has at most 2^(k-1) elements
  have hfib : ∀ x ∈ S.image g, (S.filter (fun h => g h = x)).card ≤ 2 ^ (k - 1) := by
    intro x _
    have hsub : S.filter (fun h => g h = x) ⊆
        Fintype.piFinset (fun i => ({(x i : ℤ), -(x i : ℤ)} : Finset ℤ)) := by
      intro h hh
      have hgx := (Finset.mem_filter.mp hh).2
      rw [Fintype.mem_piFinset]
      intro i
      have hi : (h i).natAbs = x i := congrFun hgx i
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases Int.natAbs_eq (h i) with h1 | h1
      · left; rw [h1, hi]
      · right; rw [h1, hi]
    calc (S.filter (fun h => g h = x)).card
        ≤ (Fintype.piFinset (fun i => ({(x i : ℤ), -(x i : ℤ)} : Finset ℤ))).card :=
          Finset.card_le_card hsub
      _ = ∏ i, ({(x i : ℤ), -(x i : ℤ)} : Finset ℤ).card := Fintype.card_piFinset _
      _ ≤ ∏ _i : Fin (k - 1), 2 := Finset.prod_le_prod (fun i _ => Finset.card_le_two)
      _ = 2 ^ (k - 1) := by simp
  -- τ_(k-1)(n) ≤ τ_k(m) since n divides m
  have htau : (ArithmeticFunction.zeta ^ (k - 1)) n ≤ divisorCount k m := by
    unfold divisorCount
    have hk1 : (ArithmeticFunction.zeta ^ k) m = (ArithmeticFunction.zeta ^ ((k - 1) + 1)) m := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have hsum : (ArithmeticFunction.zeta ^ ((k - 1) + 1)) m =
        ∑ i ∈ m.divisors, (ArithmeticFunction.zeta ^ (k - 1)) i := by
      rw [pow_succ', ← ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.natCoe_nat]
    rw [hk1, hsum]
    exact Finset.single_le_sum (f := fun i => (ArithmeticFunction.zeta ^ (k - 1)) i)
      (fun i _ => Nat.zero_le _) (Nat.mem_divisors.mpr ⟨hnm, hm0⟩)
  have hnat : S.card ≤ 2 ^ (k - 1) * divisorCount k m := by
    calc S.card ≤ 2 ^ (k - 1) * (S.image g).card := Finset.card_le_mul_card_image S _ hfib
      _ ≤ 2 ^ (k - 1) * (Nat.finMulAntidiag (k - 1) n).card :=
          Nat.mul_le_mul_left _ (Finset.card_le_card himg)
      _ ≤ 2 ^ (k - 1) * (ArithmeticFunction.zeta ^ (k - 1)) n :=
          Nat.mul_le_mul_left _ (hcard _ _)
      _ ≤ 2 ^ (k - 1) * divisorCount k m := Nat.mul_le_mul_left _ htau
  exact_mod_cast hnat


end
end LeanLab.Perelli1996.Weyl1122
