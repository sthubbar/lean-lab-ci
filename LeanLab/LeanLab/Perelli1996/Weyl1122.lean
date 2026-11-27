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

/-- The absolute value of a product over `Fin n` is the product of the absolute values. -/
private theorem natAbs_prod_fin (n : ℕ) (h : Fin n → ℤ) :
    (∏ i, h i).natAbs = ∏ i, (h i).natAbs := by
  induction n with
  | zero => simp
  | succ n ih => rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Int.natAbs_mul, ih]

/-- The product of the absolute values of a tuple of nonzero integers is at least one. -/
private theorem one_le_natAbs_prod {j : ℕ} (h : Fin j → ℤ) (hne : ∀ i, h i ≠ 0) :
    1 ≤ ∏ k, (h k).natAbs := by
  classical
  apply Finset.one_le_prod
  intro k _
  exact Int.natAbs_pos.2 (hne k)

/-- A coordinate of a tuple of nonzero integers is at most the product of the absolute values. -/
private theorem natAbs_le_natAbs_prod {j : ℕ} (h : Fin j → ℤ) (hne : ∀ i, h i ≠ 0)
    (i : Fin j) : (h i).natAbs ≤ ∏ k, (h k).natAbs := by
  classical
  have hsplit : ∏ k : Fin j, (h k).natAbs
      = (h i).natAbs * ∏ k ∈ Finset.univ.erase i, (h k).natAbs :=
    (Finset.mul_prod_erase Finset.univ (fun k => (h k).natAbs) (Finset.mem_univ i)).symm
  rw [hsplit]
  have h1 : 1 ≤ ∏ k ∈ Finset.univ.erase i, (h k).natAbs := by
    apply Finset.one_le_prod
    intro k _
    exact Int.natAbs_pos.2 (hne k)
  calc (h i).natAbs = (h i).natAbs * 1 := (Nat.mul_one _).symm
    _ ≤ (h i).natAbs * ∏ k ∈ Finset.univ.erase i, (h k).natAbs :=
        Nat.mul_le_mul_left _ h1

/-- The number of ordered factorizations of `m` into `j` positive factors is at most `τ j m`. -/
private theorem card_factor_le_divisorCount (j M m : ℕ) (hm : 0 < m) (hM : m ≤ M) :
    ((Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 M)).filter
        (fun f => ∏ i, f i = m)).card ≤ divisorCount j m := by
  classical
  induction j generalizing m with
  | zero =>
      by_cases hm1 : m = 1
      · subst hm1
        have hd : divisorCount 0 1 = 1 := by simp [divisorCount]
        rw [hd]
        refine Finset.card_le_one.2 (fun a _ b _ => ?_)
        funext i
        exact i.elim0
      · have hd : divisorCount 0 m = 0 := by simp [divisorCount, hm1]
        rw [hd, Nat.le_zero]
        by_contra hne
        obtain ⟨f, hf⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
        rw [Finset.mem_filter] at hf
        have hp : ∏ i : Fin 0, f i = 1 := Fin.prod_univ_zero f
        rw [hp] at hf
        exact hm1 hf.2.symm
  | succ j ih =>
      set T : Finset (Fin (j + 1) → ℕ) :=
        (Fintype.piFinset (fun _ : Fin (j + 1) => Finset.Icc 1 M)).filter
          (fun f => ∏ i, f i = m) with hT
      have hprod : ∀ f : Fin (j + 1) → ℕ, ∏ i, f i = f 0 * ∏ i : Fin j, Fin.tail f i := by
        intro f
        rw [Fin.prod_univ_succ]
        rfl
      have hmaps : ∀ f ∈ T, (∏ i, Fin.tail f i) ∈ m.divisors := by
        intro f hf
        rw [hT, Finset.mem_filter, Fintype.mem_piFinset] at hf
        obtain ⟨hfpi, hfprod⟩ := hf
        rw [Nat.mem_divisors]
        refine ⟨⟨f 0, ?_⟩, hm.ne'⟩
        rw [← hfprod, hprod f]
        exact Nat.mul_comm _ _
      have hcard : T.card = ∑ b ∈ m.divisors, (T.filter (fun f => ∏ i, Fin.tail f i = b)).card :=
        Finset.card_eq_sum_card_fiberwise hmaps
      have hfib : ∀ b ∈ m.divisors,
          (T.filter (fun f => ∏ i, Fin.tail f i = b)).card ≤ divisorCount j b := by
        intro b hb
        obtain ⟨hb1, hb2⟩ := Nat.mem_divisors.1 hb
        have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hb1 hm
        have hble : b ≤ m := Nat.le_of_dvd hm hb1
        have hdivmul : m / b * b = m := Nat.div_mul_cancel hb1
        have hbij : (T.filter (fun f => ∏ i, Fin.tail f i = b)).card
            = ((Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 M)).filter
                (fun g => ∏ i, g i = b)).card := by
          refine Finset.card_bij' (fun f _ => Fin.tail f) (fun g _ => Fin.cons (m / b) g)
            ?_ ?_ ?_ ?_
          · intro f hf
            rw [Finset.mem_filter] at hf
            obtain ⟨hfT, hfb⟩ := hf
            rw [hT, Finset.mem_filter, Fintype.mem_piFinset] at hfT
            exact Finset.mem_filter.2
              ⟨Fintype.mem_piFinset.2 (fun i => hfT.1 i.succ), hfb⟩
          · intro g hg
            rw [Finset.mem_filter, Fintype.mem_piFinset] at hg
            obtain ⟨hgpi, hgprod⟩ := hg
            rw [Finset.mem_filter, hT, Finset.mem_filter, Fintype.mem_piFinset]
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · rw [Fin.forall_fin_succ]
              refine ⟨?_, fun i => by simpa using hgpi i⟩
              rw [Fin.cons_zero, Finset.mem_Icc]
              have hne0 : m / b ≠ 0 := by
                intro h0
                rw [h0, Nat.zero_mul] at hdivmul
                omega
              exact ⟨Nat.one_le_iff_ne_zero.2 hne0, (Nat.div_le_self m b).trans hM⟩
            · rw [Fin.prod_univ_succ]
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [hgprod, hdivmul]
            · simp only [Fin.tail, Fin.cons_succ]
              exact hgprod
          · intro f hf
            rw [Finset.mem_filter] at hf
            obtain ⟨hfT, hfb⟩ := hf
            rw [hT, Finset.mem_filter, Fintype.mem_piFinset] at hfT
            have hf0 : f 0 = m / b := by
              rw [← Nat.mul_div_cancel (f 0) hbpos]
              congr 1
              rw [← hfb, ← hprod f, hfT.2]
            rw [← hf0]
            exact Fin.cons_self_tail f
          · intro g _
            funext i
            rfl
        rw [hbij]
        exact ih b hbpos (le_trans hble hM)
      calc T.card = ∑ b ∈ m.divisors, (T.filter (fun f => ∏ i, Fin.tail f i = b)).card := hcard
        _ ≤ ∑ b ∈ m.divisors, divisorCount j b := Finset.sum_le_sum hfib
        _ = divisorCount (j + 1) m := by
            rw [divisorCount, pow_succ, ArithmeticFunction.mul_zeta_apply]
            rfl

/-- LEAF: Page 482 equation 6, second half: the number of tuples with
k! a |h_1⋯h_(k-1)| = m is at most 2^(k-1) τ_(k-1)(m/(k! a)) ≤ 2^(k-1) τ_k(m).
Class EASY. -/
theorem leaf_tuple_count (k a R m : ℕ) (hk : 2 ≤ k) (ha : 1 ≤ a) :
    (((tuples k R).filter (fun h => freq k a h = m)).card : ℝ) ≤
      2 ^ (k - 1) * (divisorCount k m : ℝ) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hpow : (2 : ℕ) ^ (n + 1 - 1) = 2 ^ n := by rw [Nat.add_sub_cancel]
  have hfac : 1 ≤ (n + 1).factorial * a :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (by omega))
  have key : ((tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m)).card ≤
      2 ^ n * divisorCount (n + 1) m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      have hzero : ((tuples (n + 1) R).filter (fun h => freq (n + 1) a h = 0)).card = 0 := by
        by_contra hne
        obtain ⟨h, hh⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
        rw [Finset.mem_filter] at hh
        obtain ⟨htup, hfreq⟩ := hh
        rw [tuples, Fintype.mem_piFinset] at htup
        have hhne : ∀ i, h i ≠ 0 := by
          intro i
          have hi := htup i
          rw [Finset.mem_filter] at hi
          exact hi.2
        have hP : 1 ≤ (∏ i, h i).natAbs := by
          rw [natAbs_prod_fin]
          exact one_le_natAbs_prod h hhne
        have hmin : 1 ≤ freq (n + 1) a h := by
          have hm := Nat.mul_le_mul hfac hP
          simpa [freq, Nat.one_mul] using hm
        omega
      have hd0 : divisorCount (n + 1) 0 = 0 := by
        rw [divisorCount, pow_succ, ArithmeticFunction.mul_zeta_apply]
        simp
      rw [hzero, hd0]
      simp
    · set T : Finset (Fin (n + 1) → ℕ) :=
        (Fintype.piFinset (fun _ : Fin (n + 1) => Finset.Icc 1 m)).filter
          (fun f => ∏ i, f i = m) with hT
      set Φ : (Fin n → ℤ) → (Fin (n + 1) → ℕ) :=
        fun h => Fin.cons ((n + 1).factorial * a) (fun i : Fin n => (h i).natAbs) with hΦ
      set sgn : (Fin n → ℤ) → (Fin n → Bool) := fun h i => decide (h i < 0) with hsgn
      have hmem : ∀ h ∈ (tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m),
          (∀ i, h i ≠ 0) ∧ freq (n + 1) a h = m := by
        intro h hh
        rw [Finset.mem_filter] at hh
        obtain ⟨htup, hfreq⟩ := hh
        rw [tuples, Fintype.mem_piFinset] at htup
        refine ⟨fun i => ?_, hfreq⟩
        have hi := htup i
        rw [Finset.mem_filter] at hi
        exact hi.2
      have hΦprod : ∀ h : Fin n → ℤ,
          ∏ i : Fin (n + 1), Φ h i = (n + 1).factorial * a * ∏ i, (h i).natAbs := by
        intro h
        rw [hΦ, Fin.prod_univ_succ]
        simp
      have hΦmem : ∀ h ∈ (tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m),
          Φ h ∈ T := by
        intro h hh
        obtain ⟨hhne, hfreq⟩ := hmem h hh
        have hP : 1 ≤ ∏ i, (h i).natAbs := one_le_natAbs_prod h hhne
        have hmul : (n + 1).factorial * a * ∏ i, (h i).natAbs = m := by
          rw [← natAbs_prod_fin]
          exact hfreq
        have h0 : Φ h 0 = (n + 1).factorial * a := Fin.cons_zero _ _
        have hj : ∀ i : Fin n, Φ h i.succ = (h i).natAbs := fun i => Fin.cons_succ _ _ _
        rw [hT, Finset.mem_filter, Fintype.mem_piFinset]
        refine ⟨?_, ?_⟩
        · rw [Fin.forall_fin_succ]
          refine ⟨?_, ?_⟩
          · rw [h0, Finset.mem_Icc]
            exact ⟨hfac, by
              calc (n + 1).factorial * a = (n + 1).factorial * a * 1 := (Nat.mul_one _).symm
                _ ≤ (n + 1).factorial * a * ∏ k, (h k).natAbs :=
                    Nat.mul_le_mul (le_refl _) hP
                _ = m := hmul⟩
          · intro i
            rw [hj i, Finset.mem_Icc]
            refine ⟨Int.natAbs_pos.2 (hhne i), ?_⟩
            calc (h i).natAbs ≤ ∏ k, (h k).natAbs := natAbs_le_natAbs_prod h hhne i
              _ = 1 * ∏ k, (h k).natAbs := (Nat.one_mul _).symm
              _ ≤ ((n + 1).factorial * a) * ∏ k, (h k).natAbs :=
                  Nat.mul_le_mul hfac (le_refl _)
              _ = m := hmul
        · rw [hΦprod]
          exact hmul
      have hinj : ∀ h1 ∈ (tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m),
          ∀ h2 ∈ (tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m),
          (sgn h1, Φ h1) = (sgn h2, Φ h2) → h1 = h2 := by
        intro h1 h1s h2 h2s heq
        obtain ⟨hsgneq, hΦeq⟩ := Prod.ext_iff.1 heq
        funext i
        have habs : (h1 i).natAbs = (h2 i).natAbs := by
          have h := congrFun hΦeq i.succ
          exact h
        have hsgniff : (h1 i < 0) ↔ (h2 i < 0) := by
          have h := congrFun hsgneq i
          rw [hsgn] at h
          simpa using h
        rcases Int.natAbs_eq_natAbs_iff.1 habs with h' | h'
        · exact h'
        · have h2zero : h2 i = 0 := by
            by_contra hb
            rcases Int.lt_or_gt_of_ne hb with hbn | hbp
            · have h1pos : 0 < h1 i := by omega
              have h1neg : h1 i < 0 := hsgniff.mpr hbn
              omega
            · have h1neg : h1 i < 0 := by omega
              have h2neg : h2 i < 0 := hsgniff.mp h1neg
              omega
          omega
      have huniv : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
        rw [Finset.card_univ]
        simp
      have hstep1 : ((tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m)).card
          ≤ ((Finset.univ : Finset (Fin n → Bool)) ×ˢ T).card := by
        apply Finset.card_le_card_of_injOn (fun h => (sgn h, Φ h))
        · intro h hh
          exact Finset.mem_product.2 ⟨Finset.mem_univ _, hΦmem h hh⟩
        · exact hinj
      have hstep3 : T.card ≤ divisorCount (n + 1) m :=
        card_factor_le_divisorCount (n + 1) m m hmpos (le_refl m)
      calc ((tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m)).card
          ≤ ((Finset.univ : Finset (Fin n → Bool)) ×ˢ T).card := hstep1
        _ = 2 ^ n * T.card := by rw [Finset.card_product, huniv]
        _ ≤ 2 ^ n * divisorCount (n + 1) m := Nat.mul_le_mul (le_refl _) hstep3
  have keyR : (((tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m)).card : ℝ) ≤
      ((2 ^ n * divisorCount (n + 1) m : ℕ) : ℝ) := by exact_mod_cast key
  calc (((tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m)).card : ℝ)
      ≤ ((2 ^ n * divisorCount (n + 1) m : ℕ) : ℝ) := keyR
    _ = 2 ^ (n + 1 - 1) * (divisorCount (n + 1) m : ℝ) := by
        rw [Nat.add_sub_cancel]
        push_cast
        ring

end
end LeanLab.Perelli1996.Weyl1122
