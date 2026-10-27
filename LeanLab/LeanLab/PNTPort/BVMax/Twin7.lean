import LeanLab.PNTPort.BVMax.Renyi7
import LeanLab.PNTPort.BVMax.TwinRenyi

/-!
# Rényi's twin theorem with `K = 7`

Unit U-6804, CLOUD 20261021T0117Z-cloud55, idea I-5051. AI wrote the Lean code. Known mathematics,
Kuhn's weighted sieve, Kuhn 1954; Chen 1973 has `Ω(p + 2) ≤ 2`, far stronger.

The twin form of `Renyi7.lean` on `A = {p + 2 : p ≤ N prime}` of `TwinRenyi.lean`, with the
remainders of `twin_rem_family`: the lower sieve and every upper sieve of `A_q` use the same block
pack at `z = N^{2/79}`, `y = N^{0.22669}`, level `N^{0.4866}`, Kuhn weight `1 - (1/5) #{q ∣ a}`.
The bound `p + 2 ≤ N + 2 ≤ e N` costs `+1` in the logarithm, absorbed by
`4 · 2/79 + 4 · 0.22669 - 1 = 0.00803` of `log N`; and `X = li(N) ≥ (10/11)(N - 2)/log N`, so
`X V ≥ (395/11) e^{-36} (N - 2)/log² N` and the margin `0.0466` leaves `1.39` of it after the
squares and the errors. No small exceptional set: `p = 2` gives `Ω(4) = 2`.
Numerics in `numerics/twin7_check.py`.

The twin prime conjecture is `Ω(p + 2) = 1` and stays OPEN.
-/

namespace LeanLab.PNTPort.BVMax

open Finset LeanLab.PNTSieve.Bonferroni

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **Twin Rényi with `K = 7`, deterministic core with the count**, Kuhn weights
`1 - (1/5) #{q ∣ a}` on `A = {p + 2}` at `z = N^{2/79}`, `y = N^{0.22669}`. -/
theorem twin7_count {B K : ℝ} (N : ℕ)
    (hR : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ 3 ≤ p) → ∀ F : Finset (Finset ℕ),
      F ⊆ P.powerset → (∀ T ∈ F, ∏ p ∈ T, p ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊) →
      ∑ T ∈ F, |rem (twinSeq N) xDen (liD (N : ℝ)) T| ≤
        K * N / Real.log N ^ (5 : ℝ))
    (hℓ6 : (2 : ℝ) ^ 2100 ≤ Real.log N)
    (hE2 : Real.exp (49 / 100 * Real.log N) ≤ Real.sqrt N / Real.log N ^ B)
    (hE3 : 100 * |K| * N / Real.log N ^ (3 : ℝ) + Real.exp (Real.log N / 3) + 2 ≤
      (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / Real.log N ^ 2) :
    Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((Icc 1 N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 7)).card : ℝ) := by
  classical
  set ℓ := Real.log N with hℓ
  obtain ⟨hLbig0, h10⟩ := big_aux7 ℓ hℓ6
  clear hℓ6
  obtain ⟨Bs, hG, hmem, hcov, hlev, hρ, h3k⟩ := block_pack 1 (2 / 79 * ℓ) hLbig0
  clear hLbig0
  have hℓpos : 0 < ℓ := by linarith
  have hN1 : (1 : ℝ) < N := by
    by_contra h; push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hexpℓ : Real.exp ℓ = N := Real.exp_log hNpos
  have hN38 : (38 : ℝ) ≤ N := by
    rw [← hexpℓ]
    have := Real.add_one_le_exp ℓ
    linarith
  have h4 : 4 ≤ N := by exact_mod_cast (show (4 : ℝ) ≤ N by linarith)
  -- the two limits
  set L := 2 / 79 * ℓ with hL
  obtain ⟨hz3, hzr, hz1, hlogz1, hlogz2, hlogz3⟩ := floor_exp_facts L (by linarith)
  obtain ⟨hy3, hyr, hy1, hlogy1, hlogy2, hlogy3⟩ := floor_exp_facts
    (895430243255237372246531 / 3950000000000000000000000 * ℓ) (by linarith)
  set z := ⌊Real.exp L⌋₊ with hz
  set y := ⌊Real.exp (895430243255237372246531 / 3950000000000000000000000 * ℓ)⌋₊ with hy
  have hLy : L ≤ 895430243255237372246531 / 3950000000000000000000000 * ℓ := by linarith
  have hzy : z ≤ y := Nat.floor_le_floor (Real.exp_le_exp.mpr hLy)
  set Ω := univB Bs with hΩ
  set Q := (Ioc z y).filter (fun q => q.Prime ∧ ¬ q ∣ 1) with hQ
  have hΩz : ∀ p ∈ Ω, p ≤ z := fun p hp => Nat.le_floor (hmem p hp).1
  have hQmem : ∀ q ∈ Q, z < q ∧ q ≤ y ∧ q.Prime ∧ ¬ q ∣ 1 := by
    intro q hq
    rw [hQ, mem_filter, mem_Ioc] at hq
    exact ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩
  -- the sequence
  set A := twinSeq N with hAdef
  set X := liD (N : ℝ) with hXdef
  have hX : 0 ≤ X := by
    rw [hXdef]; unfold liD liN
    exact sum_nonneg (fun n _ => div_nonneg zero_le_one (Real.log_natCast_nonneg n))
  have hlevel : ∀ e : ℝ, e ≤ 49 / 100 * ℓ → ∀ n : ℕ, (n : ℝ) ≤ Real.exp e →
      n ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ := fun e he n hn =>
    Nat.le_floor (hn.trans ((Real.exp_le_exp.mpr he).trans hE2))
  -- the lower sieve
  have hρ5 : rhoSum xDen Bs ≤ 1 / 5 := hρ.trans (by norm_num)
  have hlow := blocks_main_rel5 A Bs hG xDen xDen_nonneg xDen_lt_one X hX hρ5
  have hlowR := hR Ω (fun p hp => ⟨(hmem p hp).2.1, (hmem p hp).2.2.2⟩)
    (Ω.powerset.filter (fun S => cL Bs S ≠ 0)) (filter_subset _ _) (fun T hT => by
      rw [mem_filter, mem_powerset] at hT
      refine (support_prod Bs hG T hT.1 (Or.inl hT.2)).trans
        (hlevel (154 / 15 * L) (by linarith) _ hlev))
  -- the upper sieves, same blocks
  set F' := Ω.powerset.filter (fun S => cU Bs S ≠ 0) with hF'
  have hup : ∀ q ∈ Q, (sifted (A.filter (fun a => q ∣ a)) Ω : ℝ) ≤
      X * xDen q * (∏ p ∈ Ω, (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Bs) +
        ∑ S ∈ F', |rem A xDen X (insert q S)| := by
    intro q hq
    obtain ⟨hzq, -, hqp, -⟩ := hQmem q hq
    have h := blocks_upper_rel5 (A.filter (fun a => q ∣ a)) Bs hG xDen xDen_nonneg xDen_lt_one
      (X * xDen q) (mul_nonneg hX (xDen_nonneg q)) hρ5
    refine h.trans (le_of_eq ?_)
    congr 1
    refine sum_congr rfl (fun S hS => ?_)
    rw [hF', mem_filter, mem_powerset] at hS
    rw [rem_filter_dvd A xDen X hqp S (fun p hp => (hmem p (hS.1 hp)).2.1)
      (fun hqS => by have := hΩz q (hS.1 hqS); omega)]
  set G := (Q ×ˢ F').image (fun qs => insert qs.1 qs.2) with hGdef
  have hinj : Set.InjOn (fun qs : ℕ × Finset ℕ => insert qs.1 qs.2) ↑(Q ×ˢ F') := by
    rintro ⟨q1, S1⟩ h1 ⟨q2, S2⟩ h2 he
    simp only [coe_product, Set.mem_prod, mem_coe] at h1 h2
    simp only at he
    have hS1 : S1 ⊆ Ω := mem_powerset.mp (mem_filter.mp h1.2).1
    have hS2 : S2 ⊆ Ω := mem_powerset.mp (mem_filter.mp h2.2).1
    have hq1 := (hQmem q1 h1.1).1
    have hq2 := (hQmem q2 h2.1).1
    have hn1 : q1 ∉ S1 := fun h => by have := hΩz q1 (hS1 h); omega
    have hn2 : q2 ∉ S2 := fun h => by have := hΩz q2 (hS2 h); omega
    have hq : q1 = q2 := by
      have : q1 ∈ insert q2 S2 := by rw [← he]; exact mem_insert_self q1 S1
      rcases mem_insert.mp this with h | h
      · exact h
      · exact absurd (hΩz q1 (hS2 h)) (by omega)
    subst hq
    have e1 := erase_insert hn1
    have e2 := erase_insert hn2
    rw [he] at e1
    rw [e1] at e2
    rw [Prod.mk.injEq]
    exact ⟨rfl, e2⟩
  have hGR : ∑ T ∈ G, |rem A xDen X T| ≤ K * N / ℓ ^ (5 : ℝ) := by
    refine hR (Ω ∪ Q) (fun p hp => ?_) G ?_ ?_
    · rcases mem_union.mp hp with h | h
      · exact ⟨(hmem p h).2.1, (hmem p h).2.2.2⟩
      · obtain ⟨h1, -, h3, -⟩ := hQmem p h
        exact ⟨h3, by omega⟩
    · intro T hT
      obtain ⟨⟨q, S⟩, hqS, rfl⟩ := mem_image.mp hT
      rw [mem_product] at hqS
      have hS : S ⊆ Ω := mem_powerset.mp (mem_filter.mp hqS.2).1
      rw [mem_powerset]
      intro p hp
      rcases mem_insert.mp hp with h | h
      · exact mem_union_right _ (h ▸ hqS.1)
      · exact mem_union_left _ (hS h)
    · intro T hT
      obtain ⟨⟨q, S⟩, hqS, rfl⟩ := mem_image.mp hT
      rw [mem_product] at hqS
      have hS : S ⊆ Ω := mem_powerset.mp (mem_filter.mp hqS.2).1
      have hcU : cU Bs S ≠ 0 := (mem_filter.mp hqS.2).2
      obtain ⟨hzq, hqy, -, -⟩ := hQmem q hqS.1
      have hn : q ∉ S := fun h => by have := hΩz q (hS h); omega
      simp only
      rw [prod_insert hn]
      have hSl := support_prod Bs hG S hS (Or.inr hcU)
      apply hlevel ((895430243255237372246531 / 3950000000000000000000000 * ℓ) + 154 / 15 * L)
        (by linarith)
      rw [Real.exp_add]
      push_cast
      have hqr : (q : ℝ) ≤
          Real.exp ((895430243255237372246531 / 3950000000000000000000000 * ℓ)) :=
        le_trans (by exact_mod_cast hqy) hyr
      have hSr : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ Real.exp (154 / 15 * L) :=
        le_trans (by exact_mod_cast hSl) hlev
      push_cast at hSr
      exact mul_le_mul hqr hSr (by positivity) (Real.exp_pos _).le
  -- the densities
  set V := ∏ p ∈ Ω, (1 - xDen p) with hVdef
  have hupsum : ∑ q ∈ Q, (sifted (A.filter (fun a => q ∣ a)) Ω : ℝ) ≤
      X * V * (1 + 5 / 4 * rhoSum xDen Bs) * ∑ q ∈ Q, xDen q +
        K * N / ℓ ^ (5 : ℝ) := by
    refine (sum_le_sum hup).trans ?_
    rw [sum_add_distrib]
    have e1 : ∑ q ∈ Q, X * xDen q * V * (1 + 5 / 4 * rhoSum xDen Bs) =
        X * V * (1 + 5 / 4 * rhoSum xDen Bs) * ∑ q ∈ Q, xDen q := by
      rw [mul_sum]; refine sum_congr rfl (fun q _ => by ring)
    have e2 : ∑ q ∈ Q, ∑ S ∈ F', |rem A xDen X (insert q S)| = ∑ T ∈ G, |rem A xDen X T| := by
      rw [hGdef, sum_image hinj, sum_product]
    rw [e1, e2]
    linarith
  have hV0 : 0 ≤ V := prod_nonneg (fun p _ => by linarith [xDen_le_one p])
  have hsQ : ∑ q ∈ Q, xDen q ≤ 2300023 / 1000000 := by
    have hY : (2 / 79 : ℝ) * (11 / 10) ^ 23 =
        895430243255237372246531 / 3950000000000000000000000 := by norm_num
    have h := xDen_geom ℓ (2 / 79) (11 / 10) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) 23 Q (fun q hq => by
        rw [hY]
        obtain ⟨h1, h2, h3, -⟩ := hQmem q hq
        exact ⟨h3, h1, h2⟩)
    refine h.trans ?_
    norm_num
  have hsQ0 : 0 ≤ ∑ q ∈ Q, xDen q := sum_nonneg (fun p _ => xDen_nonneg p)
  have hρ0 := rhoSum_nonneg xDen xDen_nonneg xDen_le_one Bs
  -- the main term
  have hXV0 : 0 ≤ X * V := mul_nonneg hX hV0
  have hsubtr : X * V * (1 + 5 / 4 * rhoSum xDen Bs) * ∑ q ∈ Q, xDen q ≤
      X * V * (2851 / 1000) := by
    have h1 : (1 + 5 / 4 * rhoSum xDen Bs) * ∑ q ∈ Q, xDen q ≤
        (12395 / 10000) * (2300023 / 1000000) :=
      mul_le_mul (by linarith) hsQ hsQ0 (by norm_num)
    have h2 : (1 + 5 / 4 * rhoSum xDen Bs) * ∑ q ∈ Q, xDen q ≤ 2851 / 1000 :=
      h1.trans (by norm_num)
    have h4 := mul_le_mul_of_nonneg_left h2 hXV0
    calc X * V * (1 + 5 / 4 * rhoSum xDen Bs) * ∑ q ∈ Q, xDen q
        = X * V * ((1 + 5 / 4 * rhoSum xDen Bs) * ∑ q ∈ Q, xDen q) := by ring
      _ ≤ X * V * (2851 / 1000) := h4
  have hlowmain : X * V * (6168 / 10000) ≤ X * V * (1 - 2 * rhoSum xDen Bs) :=
    mul_le_mul_of_nonneg_left (by linarith) hXV0
  -- absolute size of X V
  have hV2 : Real.exp (-36) * 79 / (2 * ℓ) ≤ V := by
    have hV := LeanLab.PNTSieve.Mertens.prod_one_sub_inv_pred_ge z hz3 Ω
      (fun p hp => ⟨(hmem p hp).2.1, (hmem p hp).2.2.2, Nat.le_floor (hmem p hp).1⟩)
    have hV' : Real.exp (-36) / Real.log z ≤ V := by
      refine hV.trans (le_of_eq (prod_congr rfl (fun p hp => ?_)))
      simp only [xDen, if_pos (hmem p hp).2.2.2]
    refine le_trans ?_ hV'
    have hlz : 0 < Real.log z := by linarith
    rw [div_le_div_iff₀ (by positivity) hlz]
    have := Real.exp_pos (-36 : ℝ)
    have : Real.log z * 79 ≤ 2 * ℓ := by linarith
    nlinarith
  have hliD : ((N : ℝ) - 2) / (11 / 10 * ℓ) ≤ X := by
    have h := liD_ge (N + 1) (by omega)
    rw [show N + 1 - 1 = N by omega] at h
    push_cast at h
    refine le_trans ?_ h
    have hl1 : Real.log ((N : ℝ) + 1) ≤ 11 / 10 * ℓ := by
      have h2 : Real.log ((N : ℝ) + 1) ≤ Real.log (2 * N) :=
        Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) hNpos.ne', ← hℓ] at h2
      have := Real.log_two_lt_d9
      norm_num at this
      linarith
    have hl0 : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
    calc ((N : ℝ) - 2) / (11 / 10 * ℓ) ≤ ((N : ℝ) - 2) / Real.log ((N : ℝ) + 1) :=
          div_le_div_of_nonneg_left (by linarith) hl0 hl1
      _ ≤ ((N : ℝ) + 1 - 2) / Real.log ((N : ℝ) + 1) :=
          div_le_div_of_nonneg_right (by linarith) hl0.le
  have hliD0 : 0 ≤ ((N : ℝ) - 2) / (11 / 10 * ℓ) := div_nonneg (by linarith) (by positivity)
  have hXV : ((N : ℝ) - 2) / (11 / 10 * ℓ) * (Real.exp (-36) * 79 / (2 * ℓ)) ≤ X * V :=
    mul_le_mul hliD hV2 (by positivity) hX
  have hXV2 : ((N : ℝ) - 2) / (11 / 10 * ℓ) * (Real.exp (-36) * 79 / (2 * ℓ)) =
      395 / 11 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) := by
    field_simp
    ring
  have hXV' : 395 / 11 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) ≤ X * V := hXV2 ▸ hXV
  -- errors
  have h5r : ℓ ^ (5 : ℝ) = ℓ ^ 5 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h3r : ℓ ^ (3 : ℝ) = ℓ ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hKN : K * N / ℓ ^ (5 : ℝ) ≤ |K| * N / ℓ ^ 5 := by
    rw [h5r]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) hNpos.le)
      (by positivity)
  have hK0 : 0 ≤ |K| * N / ℓ ^ 5 := by positivity
  have herr : ((3 : ℝ) ^ Bs.length + 1) * (|K| * N / ℓ ^ 5) ≤ |K| * N / ℓ ^ (3 : ℝ) := by
    rw [h3r]
    have h1 : (3 : ℝ) ^ Bs.length + 1 ≤ ℓ ^ 2 := by
      have : 4 * L ^ 2 + 1 ≤ ℓ ^ 2 := by rw [hL]; nlinarith
      linarith
    calc ((3 : ℝ) ^ Bs.length + 1) * (|K| * N / ℓ ^ 5) ≤ ℓ ^ 2 * (|K| * N / ℓ ^ 5) :=
          mul_le_mul_of_nonneg_right h1 hK0
      _ = |K| * N / ℓ ^ 3 := by field_simp
  have hlow3 : (3 : ℝ) ^ Bs.length *
      ∑ S ∈ Ω.powerset.filter (fun S => cL Bs S ≠ 0), |rem A xDen X S| ≤
      (3 : ℝ) ^ Bs.length * (|K| * N / ℓ ^ 5) :=
    mul_le_mul_of_nonneg_left (hlowR.trans hKN) (by positivity)
  -- the sifted set and the weight
  set Sz := A.filter (fun a => ∀ p ∈ Ω, ¬ p ∣ a) with hSz
  have hcardSz : (sifted A Ω : ℝ) = (Sz.card : ℝ) := by simp [sifted, hSz]
  have hswap : ∑ a ∈ Sz, ((Q.filter (fun q => q ∣ a)).card : ℝ) =
      ∑ q ∈ Q, ((Sz.filter (fun a => q ∣ a)).card : ℝ) := by
    rw [show (∑ a ∈ Sz, ((Q.filter (fun q => q ∣ a)).card : ℝ)) =
        ∑ a ∈ Sz, ∑ q ∈ Q, (if q ∣ a then (1 : ℝ) else 0) from
      sum_congr rfl (fun a _ => (sum_boole _ _).symm)]
    rw [sum_comm]
    exact sum_congr rfl (fun q _ => sum_boole _ _)
  have hqle : ∀ q ∈ Q, ((Sz.filter (fun a => q ∣ a)).card : ℝ) ≤
      (sifted (A.filter (fun a => q ∣ a)) Ω : ℝ) := by
    intro q _
    simp only [sifted]
    push_cast
    exact_mod_cast card_le_card (fun a ha => by
      simp only [hSz, mem_filter] at ha ⊢
      exact ⟨⟨ha.1.1, ha.2⟩, fun p hp => ha.1.2 p hp⟩)
  set SQ := A.filter (fun a => ∃ q ∈ Q, q ^ 2 ∣ a) with hSQ
  set Gd := ((Icc 1 N).filter Nat.Prime).filter
    (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 7) with hGd
  set U := SQ ∪ Gd.image (fun p => p + 2) with hU
  have hNe : Real.log ((N : ℝ) * Real.exp 1) = ℓ + 1 := by
    rw [Real.log_mul hNpos.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have hw : ∀ a ∈ Sz, 1 - ((Q.filter (fun q => q ∣ a)).card : ℝ) / 5 ≤
      if a ∈ U then 1 else 0 := by
    intro a ha
    split_ifs with haU
    · have : (0 : ℝ) ≤ ((Q.filter (fun q => q ∣ a)).card : ℝ) := Nat.cast_nonneg _
      linarith
    · rw [hSz, mem_filter] at ha
      obtain ⟨haA, haP⟩ := ha
      have haA' := haA
      rw [hAdef] at haA'
      unfold twinSeq at haA'
      obtain ⟨p, hp, rfl⟩ := mem_image.mp haA'
      rw [mem_filter, mem_Icc] at hp
      obtain ⟨⟨hp1, hpN⟩, hpp⟩ := hp
      simp only [hU, mem_union, not_or] at haU
      obtain ⟨hnsq, hng⟩ := haU
      have hm0 : p + 2 ≠ 0 := by omega
      have hsq : ∀ q ∈ Q.filter (fun q => q ∣ p + 2), ¬ q ^ 2 ∣ p + 2 := fun q hq h2 =>
        hnsq (mem_filter.mpr ⟨haA, q, (mem_filter.mp hq).1, h2⟩)
      have hΩ11 : 8 ≤ ArithmeticFunction.cardFactors (p + 2) := by
        by_contra hc
        push Not at hc
        exact hng (mem_image.mpr ⟨p, by
          rw [hGd, mem_filter, mem_filter, mem_Icc]; exact ⟨⟨⟨hp1, hpN⟩, hpp⟩, by omega⟩, rfl⟩)
      have hp2 : p ≠ 2 := by
        rintro rfl
        have e4 : ArithmeticFunction.cardFactors (2 + 2) = 2 := by
          rw [show 2 + 2 = 2 ^ 2 by norm_num,
            ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two]
        omega
      have hpodd : Odd p := hpp.odd_of_ne_two hp2
      have hmodd : Odd (p + 2) := by
        rcases hpodd with ⟨b, hb⟩
        exact ⟨b + 1, by omega⟩
      have hsmallD : ∀ r, r.Prime → r ∣ p + 2 → r ≤ y →
          r ∈ Q.filter (fun q => q ∣ p + 2) := by
        intro r hrp hrd hry
        have hr2 : r ≠ 2 := by
          rintro rfl
          exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr hrd)
        have hr3 : 3 ≤ r := by have := hrp.two_le; omega
        have hrN : ¬ r ∣ 1 := fun h => hrp.one_lt.ne' (Nat.dvd_one.mp h)
        have hrz : z < r := by
          by_contra hle
          push Not at hle
          exact haP r (hcov r hrp hrN hr3
            ((show (r : ℝ) ≤ z by exact_mod_cast hle).trans hzr)) hrd
        rw [mem_filter, hQ, mem_filter, mem_Ioc]
        exact ⟨⟨⟨hrz, hry⟩, hrp, hrN⟩, hrd⟩
      obtain ⟨hcardle, hpow⟩ := omega_split (p + 2) hm0 (Q.filter (fun q => q ∣ p + 2))
        (fun q hq => ⟨(hQmem q (mem_filter.mp hq).1).2.2.1, (mem_filter.mp hq).2⟩) hsq y hsmallD
        (z + 1) (fun q hq => (hQmem q (mem_filter.mp hq).1).1)
      set d := (Q.filter (fun q => q ∣ p + 2)).card with hd
      set Ωa := ArithmeticFunction.cardFactors (p + 2) with hΩa
      by_contra hlt
      push Not at hlt
      have hd4 : d ≤ 4 := by
        have h1 : (d : ℝ) < 5 := by linarith
        have h2 : d < 5 := by exact_mod_cast h1
        omega
      have hpowr : ((z : ℝ) + 1) ^ d * ((y : ℝ) + 1) ^ (Ωa - d) ≤ N * Real.exp 1 := by
        have h1 : (z + 1) ^ d * (y + 1) ^ (Ωa - d) ≤ N + 2 := hpow.trans (by omega)
        have h2 : (((z + 1) ^ d * (y + 1) ^ (Ωa - d) : ℕ) : ℝ) ≤ (N : ℝ) + 2 := by
          exact_mod_cast h1
        have he := Real.add_one_le_exp (1 : ℝ)
        push_cast at h2
        nlinarith
      have hlog := Real.log_le_log (by positivity) hpowr
      rw [hNe, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        Nat.cast_sub hcardle] at hlog
      have hdr : (d : ℝ) ≤ 4 := by exact_mod_cast hd4
      have hΩr : (8 : ℝ) ≤ Ωa := by exact_mod_cast hΩ11
      have hdΩ : (d : ℝ) ≤ Ωa := by exact_mod_cast hcardle
      have h1 : (d : ℝ) * (2 / 79 * ℓ) ≤ d * Real.log ((z : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      have h2 : ((Ωa : ℝ) - d) * ((895430243255237372246531 / 3950000000000000000000000 * ℓ)) ≤ ((Ωa : ℝ) - d) * Real.log ((y : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hlogy3.le (by linarith)
      have h3 := mul_nonneg (show (0 : ℝ) ≤ 4 - d by linarith) hℓpos.le
      have h4 := mul_nonneg (show (0 : ℝ) ≤ (Ωa : ℝ) - 8 by linarith) hℓpos.le
      linarith
  have hsumw := sum_le_sum hw
  rw [sum_boole, sum_sub_distrib, ← sum_div, hswap] at hsumw
  simp only [sum_const, nsmul_eq_mul, mul_one] at hsumw
  have hU1 : (Sz.filter (fun a => a ∈ U)).card ≤ U.card := card_le_card (fun a ha => (mem_filter.mp ha).2)
  have hU2 : U.card ≤ SQ.card + Gd.card :=
    (card_union_le _ _).trans (Nat.add_le_add_left card_image_le _)
  have hU3 : ((Sz.filter (fun a => a ∈ U)).card : ℝ) ≤ SQ.card + Gd.card := by
    have : (Sz.filter (fun a => a ∈ U)).card ≤ SQ.card + Gd.card := by omega
    exact_mod_cast this
  have hqsum : ∑ q ∈ Q, ((Sz.filter (fun a => q ∣ a)).card : ℝ) ≤
      ∑ q ∈ Q, (sifted (A.filter (fun a => q ∣ a)) Ω : ℝ) := sum_le_sum hqle
  -- the squares
  have hSQ1 : (SQ.card : ℝ) ≤ 2 * ((N : ℝ) + 2) / ((z : ℝ) + 1) := by
    have h1 : SQ ⊆ Q.biUnion (fun q => (Ioc 0 (N + 2)).filter (fun x => q ^ 2 ∣ x)) := by
      intro a ha
      rw [hSQ, mem_filter] at ha
      obtain ⟨haA, q, hq, hqa⟩ := ha
      rw [mem_biUnion]
      refine ⟨q, hq, mem_filter.mpr ⟨?_, hqa⟩⟩
      rw [hAdef] at haA
      unfold twinSeq at haA
      obtain ⟨p, hp, rfl⟩ := mem_image.mp haA
      rw [mem_filter, mem_Icc] at hp
      rw [mem_Ioc]
      omega
    have h2 := (card_le_card h1).trans card_biUnion_le
    have h3 : ∀ q ∈ Q, (((Ioc 0 (N + 2)).filter (fun x => q ^ 2 ∣ x)).card : ℝ) ≤
        ((N : ℝ) + 2) * ((q : ℝ) ^ 2)⁻¹ := by
      intro q _
      rw [Nat.Ioc_filter_dvd_card_eq_div]
      have := Nat.cast_div_le (α := ℝ) (m := N + 2) (n := q ^ 2)
      push_cast at this
      rw [div_eq_mul_inv] at this
      exact this
    have h4 : ∑ q ∈ Q, ((q : ℝ) ^ 2)⁻¹ ≤ 2 / ((z : ℝ) + 1) := by
      refine le_trans (sum_le_sum_of_subset_of_nonneg (?_ : Q ⊆ Ioo z (y + 1))
        (fun _ _ _ => by positivity)) (sum_Ioo_inv_sq_le z (y + 1))
      intro q hq
      obtain ⟨h1, h2, -, -⟩ := hQmem q hq
      rw [mem_Ioo]
      omega
    calc (SQ.card : ℝ) ≤ ∑ q ∈ Q, (((Ioc 0 (N + 2)).filter (fun x => q ^ 2 ∣ x)).card : ℝ) := by
          exact_mod_cast h2
      _ ≤ ∑ q ∈ Q, ((N : ℝ) + 2) * ((q : ℝ) ^ 2)⁻¹ := sum_le_sum h3
      _ = ((N : ℝ) + 2) * ∑ q ∈ Q, ((q : ℝ) ^ 2)⁻¹ := by rw [mul_sum]
      _ ≤ ((N : ℝ) + 2) * (2 / ((z : ℝ) + 1)) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 2 * ((N : ℝ) + 2) / ((z : ℝ) + 1) := by ring
  have hSQ2 : 2 * ((N : ℝ) + 2) / ((z : ℝ) + 1) ≤ Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) / 4 := by
    have hcube := Real.pow_div_factorial_le_exp (x := L) (by linarith) 3
    have hT : ℓ ^ 3 / (1479117 / 4) ≤ (z : ℝ) + 1 := by
      have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
      rw [h6] at hcube
      have e : ℓ ^ 3 / (1479117 / 4) = L ^ 3 / 6 := by rw [hL]; ring
      linarith
    have hTpos : 0 < ℓ ^ 3 / (1479117 / 4) := by positivity
    have hstep : 2 * ((N : ℝ) + 2) / ((z : ℝ) + 1) ≤ 2 * ((N : ℝ) + 2) / (ℓ ^ 3 / (1479117 / 4)) :=
      div_le_div_of_nonneg_left (by positivity) hTpos hT
    refine hstep.trans ?_
    rw [div_div_eq_mul_div, div_le_iff₀ (pow_pos hℓpos 3)]
    have e3 : ℓ ^ 3 = ℓ ^ 2 * ℓ := by ring
    have e : Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) / 4 * ℓ ^ 3 =
        Real.exp (-36) * (((N : ℝ) - 2) * ℓ) / 4 := by
      rw [e3, show Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) / 4 * (ℓ ^ 2 * ℓ) =
        Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2 * ℓ ^ 2) * ℓ / 4 by ring,
        div_mul_cancel₀ _ (pow_pos hℓpos 2).ne']
      ring
    rw [e]
    have hem : (1 : ℝ) / 10 ^ 18 ≤ Real.exp (-36) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos 36) exp_36_le
    have h1 : ((N : ℝ) - 2) * 10 ^ 30 ≤ ((N : ℝ) - 2) * ℓ :=
      mul_le_mul_of_nonneg_left h10 (by linarith)
    have h2 : (1 / 10 ^ 18) * (((N : ℝ) - 2) * ℓ) ≤ Real.exp (-36) * (((N : ℝ) - 2) * ℓ) :=
      mul_le_mul_of_nonneg_right hem (mul_nonneg (by linarith) hℓpos.le)
    linarith
  -- y is small
  have hy50 : 50 * ((y : ℝ) + 1) ≤ Real.exp (ℓ / 3) + 2 := by
    have h1 : Real.exp (ℓ / 3) =
        Real.exp ((895430243255237372246531 / 3950000000000000000000000 * ℓ)) *
          Real.exp ((1263709270234287883260407 / 11850000000000000000000000 * ℓ)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : (100 : ℝ) ≤ Real.exp ((1263709270234287883260407 / 11850000000000000000000000 * ℓ)) := by
      have := Real.add_one_le_exp ((1263709270234287883260407 / 11850000000000000000000000 * ℓ))
      linarith
    have h3 : (1 : ℝ) ≤ Real.exp ((895430243255237372246531 / 3950000000000000000000000 * ℓ)) :=
      Real.one_le_exp (by linarith)
    have h4 := mul_le_mul_of_nonneg_left h2 (le_trans zero_le_one h3)
    linarith
  have hc0 : Real.exp (-36) - Real.exp (-37) ≤ Real.exp (-36) := by
    have := Real.exp_pos (-37 : ℝ); linarith
  have hD : 0 ≤ ((N : ℝ) - 2) / ℓ ^ 2 := div_nonneg (by linarith) (by positivity)
  have hcD : (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 ≤
      Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right hc0 hD
  have hK3 : 0 ≤ |K| * N / ℓ ^ (3 : ℝ) := by rw [h3r]; positivity
  have he36 := Real.exp_pos (-36 : ℝ)
  have hgoal : Real.exp (-36) * N / ℓ ^ 2 ≤
      11 / 10 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) := by
    rw [div_le_iff₀ (by positivity)]
    have e : 11 / 10 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) * ℓ ^ 2 =
        11 / 10 * Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2 * ℓ ^ 2) := by ring
    rw [e, div_mul_cancel₀ _ (pow_pos hℓpos 2).ne']
    nlinarith [mul_nonneg he36.le (show (0 : ℝ) ≤ (N : ℝ) - 38 by linarith)]
  have hE3' : 100 * (|K| * N / ℓ ^ (3 : ℝ)) + Real.exp (ℓ / 3) + 2 ≤
      Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) := by
    have : 100 * |K| * N / ℓ ^ (3 : ℝ) = 100 * (|K| * N / ℓ ^ (3 : ℝ)) := by ring
    linarith
  rw [hcardSz] at hlow
  linarith

end LeanLab.PNTPort.BVMax
