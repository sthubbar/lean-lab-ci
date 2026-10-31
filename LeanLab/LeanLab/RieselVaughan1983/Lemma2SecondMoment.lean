import LeanLab.RieselVaughan1983.Lemma2SmoothMoments

/-! Second moments through finite smooth-number products, pages 50 and 51.
AI wrote the Lean code. Binary Goldbach is OPEN. -/
namespace LeanLab.RieselVaughan1983.Lemma2
open Real Finset Set Filter Topology
noncomputable section

def localTermFirst (p : ℕ) (w : ℝ) : ℝ :=
  gTermFirst p w + gTermFirst (p ^ 2) w + gTermFirst (p ^ 3) w

def productFirst (s : Finset ℕ) (w : ℝ) : ℝ :=
  ∑ p ∈ s, (∏ q ∈ s.erase p, localTerm q w) * localTermFirst p w

def smoothGFirst (N : ℕ) (w : ℝ) : ℝ := ∑' n : N.smoothNumbers, gTermFirst n w

lemma localTerm_hasDerivAt (p : ℕ) (w : ℝ) :
    HasDerivAt (localTerm p) (localTermFirst p w) w := by
  have h := (((hasDerivAt_const w (1 : ℝ)).add (gTerm_hasDerivAt p w)).add
    (gTerm_hasDerivAt (p ^ 2) w)).add (gTerm_hasDerivAt (p ^ 3) w)
  change HasDerivAt (fun x => 1 + gTerm p x + gTerm (p ^ 2) x + gTerm (p ^ 3) x) _ w
  convert h using 1 <;> dsimp [localTermFirst] <;> ring

lemma localTermFirst_zero (p : ℕ) (hp : p.Prime) :
    localTermFirst p 0 = localFirst p * localG p :=
  (localTerm_hasDerivAt p 0).unique (localTerm_hasDerivAt_zero p hp)

lemma localTermFirst_hasDerivAt_zero (p : ℕ) (hp : p.Prime) :
    HasDerivAt (localTermFirst p)
      (localG p * (localSecond p + localFirst p ^ 2)) 0 := by
  have h := ((gTermFirst_hasDerivAt p 0).add
    (gTermFirst_hasDerivAt (p ^ 2) 0)).add (gTermFirst_hasDerivAt (p ^ 3) 0)
  change HasDerivAt (fun w => gTermFirst p w + gTermFirst (p ^ 2) w + gTermFirst (p ^ 3) w) _ 0
  convert h using 1
  simp only [gTermSecond, neg_zero, Real.rpow_zero, mul_one, Nat.cast_pow, Real.log_pow]
  unfold localSecond localFirst
  field_simp [(localG_pos p hp).ne']
  <;> ring

lemma finite_product_hasDerivAt (s : Finset ℕ) (w : ℝ) :
    HasDerivAt (fun x : ℝ => ∏ p ∈ s, localTerm p x) (productFirst s w) w := by
  simpa only [productFirst, smul_eq_mul] using
    HasDerivAt.fun_finsetProd (fun p (_ : p ∈ s) => localTerm_hasDerivAt p w)

lemma finite_product_hasDerivAt_zero (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    HasDerivAt (fun w : ℝ => ∏ p ∈ s, localTerm p w)
      ((∏ p ∈ s, localG p) * (∑ p ∈ s, localFirst p)) 0 := by
  have h := HasDerivAt.fun_finsetProd (fun p hp => localTerm_hasDerivAt_zero p (hs p hp))
  convert h using 1
  simp only [localTerm_zero, smul_eq_mul]
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  have he := Finset.mul_prod_erase s localG hp
  nlinarith [congrArg (fun x : ℝ => x * localFirst p) he]

lemma productFirst_hasDerivAt_zero (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    HasDerivAt (productFirst s)
      ((∏ p ∈ s, localG p) * ((∑ p ∈ s, localFirst p) ^ 2 + ∑ p ∈ s, localSecond p)) 0 := by
  have h := HasDerivAt.fun_sum (u := s) (fun p hp =>
    (finite_product_hasDerivAt_zero (s.erase p) (fun q hq => hs q (mem_of_mem_erase hq))).mul
      (localTermFirst_hasDerivAt_zero p (hs p hp)))
  change HasDerivAt (fun w => ∑ p ∈ s, (∏ q ∈ s.erase p, localTerm q w) * localTermFirst p w) _ 0
  convert h using 1
  symm
  simp only [localTerm_zero]
  calc
    _ = ∑ p ∈ s, (∏ q ∈ s, localG q) *
        (localFirst p * (∑ q ∈ s, localFirst q) + localSecond p) := by
      apply sum_congr rfl
      intro p hp
      rw [localTermFirst_zero p (hs p hp)]
      have hprod := Finset.prod_erase_mul s localG hp
      have hsum := Finset.sum_erase_add s localFirst hp
      nlinarith [congrArg (fun x : ℝ => x * localFirst p *
        (∑ q ∈ s.erase p, localFirst q)) hprod,
        congrArg (fun x : ℝ => x * (localSecond p + localFirst p ^ 2)) hprod,
        congrArg (fun x : ℝ => (∏ q ∈ s, localG q) * localFirst p * x) hsum]
    _ = _ := by rw [← mul_sum]; congr 1; rw [sum_add_distrib, ← sum_mul]; ring

lemma smoothG_hasDerivAt (N : ℕ) (w : ℝ) (hw : -(1 / 6 : ℝ) < w) :
    HasDerivAt (smoothG N) (smoothGFirst N w) w := by
  have hm := mass_summable.subtype (fun n => n ∈ N.smoothNumbers)
  have h0 : Summable (fun n : N.smoothNumbers => gTerm n 0) := by
    exact (g_summable_norm.of_norm.subtype (fun n => n ∈ N.smoothNumbers)).congr
      (fun n => by simp [gTerm])
  exact hasDerivAt_tsum_of_isPreconnected (hm.mul_left 6)
    isOpen_Ioi (convex_Ioi _).isPreconnected
    (fun n y _ => gTerm_hasDerivAt n y) (fun n y hy => gTermFirst_bound n y hy)
    (by norm_num : (0 : ℝ) ∈ Ioi (-(1 / 6 : ℝ))) h0 hw

lemma smoothGFirst_hasDerivAt_zero (N : ℕ) :
    HasDerivAt (smoothGFirst N) (∑' n : N.smoothNumbers, gTermSecond n 0) 0 := by
  have hm := mass_summable.subtype (fun n => n ∈ N.smoothNumbers)
  have h0 : Summable (fun n : N.smoothNumbers => gTermFirst n 0) := by
    exact ((log_moment_summable_norm.of_norm.neg).subtype
      (fun n => n ∈ N.smoothNumbers)).congr (fun n => by simp [gTermFirst, neg_mul])
  exact hasDerivAt_tsum_of_isPreconnected (hm.mul_left 72)
    isOpen_Ioi (convex_Ioi _).isPreconnected
    (fun n y _ => gTermFirst_hasDerivAt n y) (fun n y hy => gTermSecond_bound n y hy)
    (by norm_num : (0 : ℝ) ∈ Ioi (-(1 / 6 : ℝ))) h0 (by norm_num)

lemma smooth_second_identity (N : ℕ) :
    (∑' n : N.smoothNumbers, gTermSecond n 0) =
      (∏ p ∈ N.primesBelow, localG p) *
        ((∑ p ∈ N.primesBelow, localFirst p) ^ 2 + ∑ p ∈ N.primesBelow, localSecond p) := by
  have he : smoothGFirst N =ᶠ[nhds (0 : ℝ)] productFirst N.primesBelow := by
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioi (-(1 / 6 : ℝ)))] with w hw
    have h1 := smoothG_hasDerivAt N w hw
    have hfun : smoothG N = (fun x => ∏ p ∈ N.primesBelow, localTerm p x) :=
      funext (smoothG_eq_product N)
    rw [hfun] at h1
    exact h1.unique (finite_product_hasDerivAt N.primesBelow w)
  have h1 := (smoothGFirst_hasDerivAt_zero N).deriv
  have h2 := (productFirst_hasDerivAt_zero N.primesBelow
    (fun p hp => Nat.prime_of_mem_primesBelow hp)).deriv
  rw [he.deriv_eq] at h1
  exact h1.symm.trans h2

lemma secondMoment_proved : SecondMomentP := by
  have hm := tendsto_smooth_tsum (fun n => gTermSecond n 0) (by simp [gTermSecond])
    (by simpa [gTermSecond] using log_sq_moment_summable_norm)
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
  have hfirst : Tendsto (fun N : ℕ => ∑ p ∈ N.primesBelow, localFirst p) atTop (nhds A1) := by
    simpa [Nat.primesBelow, Finset.sum_filter] using localFirst_hasSum.tendsto_sum_nat
  have hsecond : Tendsto (fun N : ℕ => ∑ p ∈ N.primesBelow, localSecond p) atTop
      (nhds (Real.log 2 ^ 2 / 4 - A2)) := by
    simpa [Nat.primesBelow, Finset.sum_filter] using localSecond_hasSum.tendsto_sum_nat
  have hprod := hp.mul ((hfirst.pow 2).add hsecond)
  have he := tendsto_nhds_unique hm
    (hprod.congr' (Eventually.of_forall (fun N => (smooth_second_identity N).symm)))
  change moment 2 = _
  have hm2 : (∑' n : ℕ, gTermSecond n 0) = moment 2 := by simp [gTermSecond, moment]
  rw [hm2] at he
  rw [he]
  ring

/-- Lemma 2 on page 50 with both evaluated moments discharged. -/
theorem lemma2_unconditional : Lemma2P :=
  lemma2_of_moments firstMoment_proved secondMoment_proved

end
end LeanLab.RieselVaughan1983.Lemma2

#print axioms LeanLab.RieselVaughan1983.Lemma2.localTerm_hasDerivAt
#print axioms LeanLab.RieselVaughan1983.Lemma2.localTermFirst_zero
#print axioms LeanLab.RieselVaughan1983.Lemma2.localTermFirst_hasDerivAt_zero
#print axioms LeanLab.RieselVaughan1983.Lemma2.finite_product_hasDerivAt
#print axioms LeanLab.RieselVaughan1983.Lemma2.finite_product_hasDerivAt_zero
#print axioms LeanLab.RieselVaughan1983.Lemma2.productFirst_hasDerivAt_zero
#print axioms LeanLab.RieselVaughan1983.Lemma2.smoothG_hasDerivAt
#print axioms LeanLab.RieselVaughan1983.Lemma2.smoothGFirst_hasDerivAt_zero
#print axioms LeanLab.RieselVaughan1983.Lemma2.smooth_second_identity
#print axioms LeanLab.RieselVaughan1983.Lemma2.secondMoment_proved
#print axioms LeanLab.RieselVaughan1983.Lemma2.lemma2_unconditional
