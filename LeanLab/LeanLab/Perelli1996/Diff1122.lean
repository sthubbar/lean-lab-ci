/-
P0083 Perelli 1996, page 482, equation 6 of the proof of the named Lemma.
ROUTE BURST S79 burst-20261122 split of Decomp103b.leaf_differencing.
The K-th root and the heavy and light partition are proved in Decomp103b;
only the Weyl differencing display 6 itself stays a LEAF here.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Weyl1122

namespace LeanLab.Perelli1996.Diff1122
open Finset Real Polynomial
open LeanLab.Perelli1996.Section2
noncomputable section

/-- Page 482 equation 6, Weyl differencing as in Vaughan 1981 Lemma 2.4.
Burst S79: no longer a LEAF; proved from Weyl1122.leaf_iterated_differencing and
Weyl1122.leaf_tuple_count by grouping the tuples by their frequency m. With K equal to two to the k minus one,
|K(F,α)|^K is at most a constant times H^(K-k) times
H^(k-1) plus the sum over 1 ≤ h ≤ c₃ H^(k-1) of τ_k(h) |∑_{n ∈ I} e(nαh)|.
The paper's suitable interval I inside [N^(1/k), N^(1/k)+H] is rendered as one
block of at most H+1 consecutive integers for each h, start h through
start h plus len h minus one. Here τ_k is divisorCount k. -/
theorem leaf_weyl_differencing (F : ℤ[X]) (hF : Admissible F) (hk : 2 ≤ F.natDegree) :
    ∃ c C N₀ : ℝ, 0 < c ∧ 0 < C ∧ 3 ≤ N₀ ∧
      ∀ N H α : ℝ, N₀ ≤ N → 1 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∃ start len : ℕ → ℕ, (∀ h, (len h : ℝ) ≤ H + 1) ∧
        ‖polynomialKernel F N H α‖ ^ weylExponent F ≤
          C * H ^ (weylExponent F - F.natDegree) *
            (H ^ (F.natDegree - 1) +
              ∑ h ∈ Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊,
                (divisorCount F.natDegree h : ℝ) * ‖Kernel.T (start h) (len h) (α * h)‖) := by
  classical
  obtain ⟨C, N₀, hC, hN₀, hA⟩ := Weyl1122.leaf_iterated_differencing F hF hk
  set k := F.natDegree with hkdef
  set a := F.leadingCoeff.natAbs with hadef
  have ha : 1 ≤ a := by
    have := hF.2; rw [hadef]; omega
  have hfac : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  refine ⟨(k.factorial : ℝ) * a, C * 2 ^ (k - 1), N₀, by positivity, by positivity, hN₀, ?_⟩
  intro N H α hN hH hHu
  obtain ⟨st, ln, hln, hb⟩ := hA N H α hN hH hHu
  set R := ⌊H⌋₊ with hR
  set Tup := Weyl1122.tuples k R with hTup
  have hH0 : 0 < H := by linarith
  let Tp : (Fin (k - 1) → ℤ) → ℝ := fun h =>
    ‖Kernel.T (st h) (ln h) (α * (Weyl1122.freq k a h : ℕ))‖
  let fib : ℕ → Finset (Fin (k - 1) → ℤ) := fun m =>
    Tup.filter (fun h => Weyl1122.freq k a h = m)
  let best : ℕ → (Fin (k - 1) → ℤ) := fun m =>
    if hne : (fib m).Nonempty then Classical.choose (Finset.exists_max_image (fib m) Tp hne)
    else 0
  have hbest : ∀ m, ∀ h ∈ fib m, Tp h ≤ ‖Kernel.T (st (best m)) (ln (best m)) (α * m)‖ := by
    intro m h hh
    have hne : (fib m).Nonempty := ⟨h, hh⟩
    have hspec := Classical.choose_spec (Finset.exists_max_image (fib m) Tp hne)
    have hb1 : best m = Classical.choose (Finset.exists_max_image (fib m) Tp hne) := by
      simp only [best, dif_pos hne]
    have hm : Weyl1122.freq k a (best m) = m := by
      rw [hb1]; exact (Finset.mem_filter.mp hspec.1).2
    have := hspec.2 h hh
    rw [← hb1] at this
    dsimp only [Tp] at this
    rw [hm] at this
    exact this
  refine ⟨fun m => st (best m), fun m => ln (best m), fun m => hln _, ?_⟩
  set G : ℕ → ℝ := fun m => ‖Kernel.T (st (best m)) (ln (best m)) (α * m)‖ with hG
  -- every tuple frequency lies in 1 .. ⌊k! a H^(k-1)⌋
  have hmaps : ∀ h ∈ Tup,
      Weyl1122.freq k a h ∈ Icc 1 ⌊(k.factorial : ℝ) * a * H ^ (k - 1)⌋₊ := by
    intro h hh
    rw [Fintype.mem_piFinset] at hh
    have hne : ∀ i, h i ≠ 0 := fun i => (Finset.mem_filter.mp (hh i)).2
    have habs : ∀ i, (h i).natAbs ≤ R := by
      intro i
      have := Finset.mem_Icc.mp (Finset.mem_filter.mp (hh i)).1
      omega
    have hprod : (∏ i, h i).natAbs = ∏ i, (h i).natAbs := by
      exact map_prod Int.natAbsHom h Finset.univ
    have hpos : 1 ≤ (∏ i, h i).natAbs := by
      rw [hprod]
      exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => by
        simpa using hne i))
    have hle : (∏ i, h i).natAbs ≤ R ^ (k - 1) := by
      rw [hprod]
      calc ∏ i, (h i).natAbs ≤ R ^ (Finset.univ : Finset (Fin (k - 1))).card :=
            Finset.prod_le_pow_card _ _ _ (fun i _ => habs i)
        _ = R ^ (k - 1) := by simp
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · have h1 : 1 ≤ k.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
      unfold Weyl1122.freq
      calc 1 = 1 * 1 * 1 := by norm_num
        _ ≤ k.factorial * a * (∏ i, h i).natAbs := by gcongr
    · apply Nat.le_floor
      unfold Weyl1122.freq
      push_cast
      have hRH : (R : ℝ) ≤ H := Nat.floor_le hH0.le
      have hle' : ((∏ i, h i).natAbs : ℝ) ≤ H ^ (k - 1) := by
        calc ((∏ i, h i).natAbs : ℝ) ≤ ((R ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast hle
          _ = (R : ℝ) ^ (k - 1) := by push_cast; ring
          _ ≤ H ^ (k - 1) := by gcongr
      have h0 : (0 : ℝ) ≤ (k.factorial : ℝ) * a := by positivity
      calc (k.factorial : ℝ) * a * ((∏ i, h i).natAbs : ℝ) ≤ (k.factorial : ℝ) * a * H ^ (k - 1) :=
            mul_le_mul_of_nonneg_left hle' h0
        _ = _ := by push_cast; ring
  set M := ⌊(k.factorial : ℝ) * a * H ^ (k - 1)⌋₊ with hM
  have hsum : (∑ h ∈ Tup, Tp h) ≤
      2 ^ (k - 1) * ∑ m ∈ Icc 1 M, (divisorCount k m : ℝ) * G m := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    calc (∑ h ∈ fib m, Tp h)
        ≤ ∑ h ∈ fib m, G m := Finset.sum_le_sum (fun h hh => hbest m h hh)
      _ = ((fib m).card : ℝ) * G m := by simp
      _ ≤ (2 ^ (k - 1) * (divisorCount k m : ℝ)) * G m :=
          mul_le_mul_of_nonneg_right (Weyl1122.leaf_tuple_count k a R m hk ha) (norm_nonneg _)
      _ = 2 ^ (k - 1) * ((divisorCount k m : ℝ) * G m) := by ring
  have hS0 : 0 ≤ ∑ m ∈ Icc 1 M, (divisorCount k m : ℝ) * G m :=
    Finset.sum_nonneg (fun m _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  have h2 : (1 : ℝ) ≤ 2 ^ (k - 1) := one_le_pow₀ (by norm_num)
  have hHk : 0 ≤ H ^ (k - 1) := by positivity
  have hHK : 0 ≤ H ^ (weylExponent F - (k : ℝ)) := by positivity
  calc ‖polynomialKernel F N H α‖ ^ weylExponent F
      ≤ C * H ^ (weylExponent F - (k : ℝ)) * (H ^ (k - 1) + ∑ h ∈ Tup, Tp h) := hb
    _ ≤ C * H ^ (weylExponent F - (k : ℝ)) *
        (H ^ (k - 1) + 2 ^ (k - 1) * ∑ m ∈ Icc 1 M, (divisorCount k m : ℝ) * G m) := by gcongr
    _ ≤ C * H ^ (weylExponent F - (k : ℝ)) *
        (2 ^ (k - 1) * (H ^ (k - 1) + ∑ m ∈ Icc 1 M, (divisorCount k m : ℝ) * G m)) := by
        gcongr; nlinarith
    _ = C * 2 ^ (k - 1) * H ^ (weylExponent F - (k : ℝ)) *
        (H ^ (k - 1) + ∑ m ∈ Icc 1 M, (divisorCount k m : ℝ) * G m) := by ring

end
end LeanLab.Perelli1996.Diff1122
