import LeanLab.RieselVaughan1983.Lemma2Derivatives
import LeanLab.RieselVaughan1983.Lemma2LocalMoments
import LeanLab.RieselVaughan1983.Lemma2Assembly

/-! Finite smooth-number Euler products for the page 51 moments.
AI wrote the Lean code. Binary Goldbach is OPEN. -/
namespace LeanLab.RieselVaughan1983.Lemma2
open Real Finset Set Filter Topology
noncomputable section

def localTerm (p : ℕ) (w : ℝ) : ℝ :=
  1 + gTerm p w + gTerm (p ^ 2) w + gTerm (p ^ 3) w

def smoothG (N : ℕ) (w : ℝ) : ℝ := ∑' n : N.smoothNumbers, gTerm n w

lemma gTerm_one (w : ℝ) : gTerm 1 w = 1 := by simp [gTerm, g_multiplicative.map_one]

lemma gTerm_mul (w : ℝ) {a b : ℕ} (hab : a.Coprime b) :
    gTerm (a * b) w = gTerm a w * gTerm b w := by
  simp only [gTerm, Nat.cast_mul, g_multiplicative.map_mul_of_coprime hab,
    Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  ring

lemma localTerm_hasSum (p : ℕ) (hp : p.Prime) (w : ℝ) :
    HasSum (fun e : ℕ => gTerm (p ^ e) w) (localTerm p w) := by
  have hz : ∀ e ∉ ({0, 1, 2, 3} : Finset ℕ), gTerm (p ^ e) w = 0 := by
    intro e he
    have he4 : 4 ≤ e := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
      omega
    simp [gTerm, g_prime_pow_ge_four p e hp he4]
  convert hasSum_sum_of_ne_finset_zero hz using 1
  · simp [localTerm, gTerm_one, add_assoc]
  · infer_instance

lemma localTerm_zero (p : ℕ) : localTerm p 0 = localG p := by
  simp [localTerm, localG, gTerm]

lemma smoothG_eq_product (N : ℕ) (w : ℝ) :
    smoothG N w = ∏ p ∈ N.primesBelow, localTerm p w := by
  have h := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := fun n => gTerm n w) (gTerm_one w) (fun h => gTerm_mul w h)
    (fun hp => (localTerm_hasSum _ hp w).summable.norm) N).2
  unfold smoothG
  rw [h.tsum_eq]
  apply prod_congr rfl
  intro p hp
  exact (localTerm_hasSum p (Nat.prime_of_mem_primesBelow hp) w).tsum_eq

lemma localTerm_hasDerivAt_zero (p : ℕ) (hp : p.Prime) :
    HasDerivAt (localTerm p) (localFirst p * localG p) 0 := by
  have h := (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (gTerm_hasDerivAt p 0)).add
    (gTerm_hasDerivAt (p ^ 2) 0)).add (gTerm_hasDerivAt (p ^ 3) 0)
  change HasDerivAt (fun w => 1 + gTerm p w + gTerm (p ^ 2) w + gTerm (p ^ 3) w) _ 0
  convert h using 1
  simp only [gTermFirst, neg_zero, Real.rpow_zero, mul_one, Nat.cast_pow, Real.log_pow, zero_add]
  unfold localFirst
  field_simp [(localG_pos p hp).ne']
  <;> ring

lemma smoothG_hasDerivAt_zero (N : ℕ) :
    HasDerivAt (smoothG N) (∑' n : N.smoothNumbers, gTermFirst n 0) 0 := by
  have hm := mass_summable.subtype (fun n => n ∈ N.smoothNumbers)
  have h0 : Summable (fun n : N.smoothNumbers => gTerm n 0) := by
    exact (g_summable_norm.of_norm.subtype (fun n => n ∈ N.smoothNumbers)).congr
      (fun n => by simp [gTerm])
  exact hasDerivAt_tsum_of_isPreconnected (hm.mul_left 6)
    isOpen_Ioi (convex_Ioi _).isPreconnected
    (fun n y _ => gTerm_hasDerivAt n y)
    (fun n y hy => gTermFirst_bound n y hy)
    (by norm_num : (0 : ℝ) ∈ Ioi (-(1 / 6 : ℝ))) h0 (by norm_num)

lemma product_hasDerivAt_zero (N : ℕ) :
    HasDerivAt (fun w : ℝ => ∏ p ∈ N.primesBelow, localTerm p w)
      ((∏ p ∈ N.primesBelow, localG p) * (∑ p ∈ N.primesBelow, localFirst p)) 0 := by
  have h := HasDerivAt.fun_finsetProd (u := N.primesBelow)
    (fun p hp => localTerm_hasDerivAt_zero p (Nat.prime_of_mem_primesBelow hp))
  convert h using 1
  simp only [localTerm_zero, smul_eq_mul]
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  have he := Finset.mul_prod_erase N.primesBelow localG hp
  nlinarith [congrArg (fun x : ℝ => x * localFirst p) he]

lemma smooth_first_identity (N : ℕ) :
    (∑' n : N.smoothNumbers, gTermFirst n 0) =
      (∏ p ∈ N.primesBelow, localG p) * (∑ p ∈ N.primesBelow, localFirst p) := by
  have he : smoothG N = (fun w => ∏ p ∈ N.primesBelow, localTerm p w) :=
    funext (smoothG_eq_product N)
  have h := smoothG_hasDerivAt_zero N
  rw [he] at h
  exact h.unique (product_hasDerivAt_zero N)

lemma tendsto_smooth_tsum (f : ℕ → ℝ) (hf0 : f 0 = 0) (hs : Summable (fun n => ‖f n‖)) :
    Tendsto (fun N : ℕ => ∑' n : N.smoothNumbers, f n) atTop (nhds (∑' n : ℕ, f n)) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (g := f) (f := fun (N n : ℕ) =>
      (N.smoothNumbers : Set ℕ).indicator f n) hs
  have hpoint : ∀ n : ℕ, Tendsto (fun N : ℕ => (N.smoothNumbers : Set ℕ).indicator f n)
      atTop (nhds (f n)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa [hf0, Set.indicator_apply] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop n] with N hN
      exact (Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hn hN) f).symm
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      ‖(N.smoothNumbers : Set ℕ).indicator f n‖ ≤ ‖f n‖ := by
    exact Eventually.of_forall (fun N n => norm_indicator_le_norm_self _ _)
  simpa only [← _root_.tsum_subtype] using h hpoint hbound

lemma firstMoment_proved : FirstMomentP := by
  have hm := tendsto_smooth_tsum (fun n => gTermFirst n 0) (by simp [gTermFirst])
    (by simpa [gTermFirst, neg_mul] using log_moment_summable_norm)
  have hg := tendsto_smooth_tsum (fun n => g n) (by simp) g_summable_norm
  have hp : Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, localG p) atTop
      (nhds (1 / Ctw)) := by
    have he : (fun N : ℕ => ∑' n : N.smoothNumbers, g n) =
        (fun N => ∏ p ∈ N.primesBelow, localG p) := by
      funext N
      simpa [smoothG, gTerm, localTerm_zero] using smoothG_eq_product N 0
    rw [he] at hg
    have heval : (∑' n : ℕ, g n) = 1 / Ctw := by simpa [G] using G_zero
    simpa only [heval] using hg
  have hprime : Tendsto (fun N : ℕ => ∑ p ∈ N.primesBelow, localFirst p) atTop (nhds A1) := by
    simpa [Nat.primesBelow, Finset.sum_filter] using localFirst_hasSum.tendsto_sum_nat
  have hprod := hp.mul hprime
  have he : (∑' n : ℕ, gTermFirst n 0) = (1 / Ctw) * A1 :=
    tendsto_nhds_unique hm (hprod.congr' (Eventually.of_forall (fun N => (smooth_first_identity N).symm)))
  unfold FirstMomentP
  have hm1 : (∑' n : ℕ, gTermFirst n 0) = -moment 1 := by
    simp [gTermFirst, moment, tsum_neg, neg_mul]
  rw [hm1] at he
  calc moment 1 = -((1 / Ctw) * A1) := by linarith
    _ = -(A1 / Ctw) := by ring

end
end LeanLab.RieselVaughan1983.Lemma2

#print axioms LeanLab.RieselVaughan1983.Lemma2.gTerm_one
#print axioms LeanLab.RieselVaughan1983.Lemma2.gTerm_mul
#print axioms LeanLab.RieselVaughan1983.Lemma2.localTerm_hasSum
#print axioms LeanLab.RieselVaughan1983.Lemma2.localTerm_zero
#print axioms LeanLab.RieselVaughan1983.Lemma2.smoothG_eq_product
#print axioms LeanLab.RieselVaughan1983.Lemma2.localTerm_hasDerivAt_zero
#print axioms LeanLab.RieselVaughan1983.Lemma2.smoothG_hasDerivAt_zero
#print axioms LeanLab.RieselVaughan1983.Lemma2.product_hasDerivAt_zero
#print axioms LeanLab.RieselVaughan1983.Lemma2.smooth_first_identity
#print axioms LeanLab.RieselVaughan1983.Lemma2.tendsto_smooth_tsum
#print axioms LeanLab.RieselVaughan1983.Lemma2.firstMoment_proved
