import LeanLab.ExceptionalSet.MVEstermann
import LeanLab.PNTPort.Vinogradov.TernaryAssembly

/-!
# Estermann's major arcs on `ZMod M` as a disjoint union, and the binary complete sums

Lab proof, unit U-6250, CLOUD 20261020T0917Z-cloud39. AI wrote the Lean code. Known
mathematics, no cited input. Binary Goldbach is OPEN.

* `arcMV x Q q a`: the `k` with `‖k/M - a/q‖ ≤ Q/M`, `M = 2x + 1`.
* `majorArcs_eq`: `majorArcs x Q`, the major arcs of `MVEstermann.lean`, is the union of the
  `arcMV x Q q a` over the reduced `a/q` with `q ≤ ⌊Q⌋`; `arcsMV_disjoint`: the union is
  disjoint once `2Q³ < M`.
* `J2 N n = #{(y, z) ∈ [1, N]² : y + z = n}`, `J2_eq`: `n - 1` for `1 ≤ n ≤ N + 1`;
  `full_sum_V2`: `∑_{k mod M} V(-(k/M - γ))² e(n(k/M - γ)) = M · J2(n)` for `2N < M`, `n < M`.
* `tail_V2_le`: off an arc of half-width `δ`, `∑ |V|² ≤ 2M/δ + 1/(2δ²)`, by dyadic shells.
-/

namespace LeanLab.ExceptionalSet.MVMajor

open Complex Finset Real ZMod
open LeanLab.PNTPort.Vinogradov LeanLab.PNTPort.LargeSieve LeanLab.ExceptionalSet.MV

attribute [local instance] Classical.propDecidable

/-- One major arc of Estermann's dissection. -/
noncomputable def arcMV (x : ℕ) (Q : ℝ) (q a : ℕ) : Finset (ZMod (Mx x)) :=
  univ.filter (fun k => dist0 ((k.val : ℝ) / (Mx x) - (a : ℝ) / q) ≤ Q / (Mx x))

/-- The major arcs are the union of the arcs around reduced fractions. -/
theorem majorArcs_eq (x : ℕ) (Q : ℝ) :
    majorArcs x Q = (majIdx ⌊Q⌋₊).biUnion (fun p => arcMV x Q p.1 p.2) := by
  ext k
  simp only [majorArcs, arcMV, mem_filter, mem_univ, true_and, mem_biUnion]
  constructor
  · rintro ⟨q, hq1, hqQ, a, ha⟩
    have hq0 : (0 : ℤ) < q := by exact_mod_cast hq1
    set r : ℕ := (a % (q : ℤ)).toNat with hr
    have hr0 : (0 : ℤ) ≤ a % (q : ℤ) := Int.emod_nonneg a hq0.ne'
    have hrq : ((r : ℕ) : ℤ) = a % (q : ℤ) := by rw [hr, Int.toNat_of_nonneg hr0]
    have hrlt : r < q := by
      have := Int.emod_lt_of_pos a hq0
      omega
    have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    -- `r/q` differs from `a/q` by an integer
    have hdist : dist0 ((k.val : ℝ) / (Mx x) - (r : ℝ) / q) ≤ Q / (Mx x) := by
      refine le_trans ?_ ha
      have e1 : ((r : ℝ)) = (a : ℝ) - q * ((a / (q : ℤ) : ℤ) : ℝ) := by
        have := Int.emod_add_mul_ediv a (q : ℤ)
        have h2 : ((r : ℤ) : ℝ) = ((a % (q : ℤ) : ℤ) : ℝ) := by rw [hrq]
        push_cast at h2
        rw [h2]
        have h3 : ((a % (q : ℤ) : ℤ) : ℝ) + (q : ℝ) * ((a / (q : ℤ) : ℤ) : ℝ) = (a : ℝ) := by
          exact_mod_cast this
        linarith
      have e2 : (k.val : ℝ) / (Mx x) - (a : ℝ) / q =
          ((k.val : ℝ) / (Mx x) - (r : ℝ) / q) - (((a / (q : ℤ) : ℤ) : ℝ) : ℝ) := by
        rw [e1]; push_cast; field_simp; ring
      rw [e2]
      exact dist0_le_abs_sub_int _ _
    -- reduce `r/q`
    set g := Nat.gcd r q with hg
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_right r (by omega)
    refine ⟨(q / g, r / g), ?_, ?_⟩
    · simp only [majIdx, mem_filter, mem_product, mem_Icc, mem_range]
      have hgq : g ∣ q := Nat.gcd_dvd_right r q
      have hgr : g ∣ r := Nat.gcd_dvd_left r q
      have hq'1 : 1 ≤ q / g := Nat.div_pos (Nat.le_of_dvd (by omega) hgq) hg0
      have hq'le : q / g ≤ ⌊Q⌋₊ := by
        apply Nat.le_floor
        exact le_trans (by exact_mod_cast Nat.div_le_self q g) hqQ
      have hlt : r / g < q / g := by
        obtain ⟨r', hr'⟩ := hgr
        obtain ⟨q', hq'⟩ := hgq
        rw [hr', hq', Nat.mul_div_cancel_left _ hg0, Nat.mul_div_cancel_left _ hg0]
        rw [hr', hq'] at hrlt
        exact Nat.lt_of_mul_lt_mul_left hrlt
      refine ⟨⟨⟨hq'1, hq'le⟩, by omega⟩, hlt, ?_⟩
      exact Nat.coprime_div_gcd_div_gcd hg0
    · have heq : ((r / g : ℕ) : ℝ) / ((q / g : ℕ) : ℝ) = (r : ℝ) / q := by
        rw [Nat.cast_div (Nat.gcd_dvd_left r q) (by exact_mod_cast hg0.ne'),
          Nat.cast_div (Nat.gcd_dvd_right r q) (by exact_mod_cast hg0.ne')]
        have : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
        field_simp
      simp only
      rw [heq]
      exact hdist
  · rintro ⟨⟨q, a⟩, hp, hk⟩
    simp only [majIdx, mem_filter, mem_product, mem_Icc, mem_range] at hp
    obtain ⟨⟨⟨hq1, hqP⟩, _⟩, _, _⟩ := hp
    have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hQ0 : (0 : ℝ) ≤ Q := by
      have := le_trans (dist0_nonneg _) hk
      have hM : (0 : ℝ) < Mx x := by unfold Mx; positivity
      by_contra h
      push_neg at h
      have : Q / (Mx x) < 0 := div_neg_of_neg_of_pos h hM
      linarith
    refine ⟨q, hq1, le_trans (by exact_mod_cast hqP) (Nat.floor_le hQ0),
      (a : ℤ) + q * round ((k.val : ℝ) / (Mx x) - (a : ℝ) / q), ?_⟩
    refine le_trans (le_of_eq ?_) hk
    unfold dist0
    congr 1
    push_cast
    field_simp
    ring

/-- The arcs are pairwise disjoint once `2Q³ < M`. -/
theorem arcsMV_disjoint {x : ℕ} {Q : ℝ} (hQ : 1 ≤ Q) (hQM : 2 * Q ^ 3 < Mx x) :
    Set.PairwiseDisjoint (↑(majIdx ⌊Q⌋₊)) (fun p : ℕ × ℕ => arcMV x Q p.1 p.2) := by
  intro p hp p' hp' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro k hk hk'
  simp only [arcMV, mem_filter, mem_univ, true_and] at hk hk'
  have hsep := frac_sep hp hp' hne
  simp only [majIdx, mem_filter, mem_product, mem_Icc, mem_range, coe_filter,
    Set.mem_setOf_eq] at hp hp'
  have hM : (0 : ℝ) < Mx x := by unfold Mx; positivity
  have hP : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hq : (p.1 : ℝ) ≤ Q := le_trans (by exact_mod_cast hp.1.1.2) hP
  have hq' : (p'.1 : ℝ) ≤ Q := le_trans (by exact_mod_cast hp'.1.1.2) hP
  have hq1 : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp.1.1.1
  have hq1' : (1 : ℝ) ≤ p'.1 := by exact_mod_cast hp'.1.1.1
  have h2 : dist0 ((p.2 : ℝ) / p.1 - (p'.2 : ℝ) / p'.1) ≤ 2 * Q / Mx x := by
    have := dist0_add_le ((k.val : ℝ) / (Mx x) - (p'.2 : ℝ) / p'.1)
      (-((k.val : ℝ) / (Mx x) - (p.2 : ℝ) / p.1))
    rw [dist0_neg] at this
    have e : (k.val : ℝ) / (Mx x) - (p'.2 : ℝ) / p'.1 + -((k.val : ℝ) / (Mx x) - (p.2 : ℝ) / p.1) =
        (p.2 : ℝ) / p.1 - (p'.2 : ℝ) / p'.1 := by ring
    rw [e] at this
    have : 2 * Q / Mx x = Q / Mx x + Q / Mx x := by ring
    linarith
  have h3 : 1 / Q ^ 2 ≤ 1 / ((p.1 : ℝ) * p'.1) := by
    apply one_div_le_one_div_of_le (by positivity)
    calc (p.1 : ℝ) * p'.1 ≤ Q * Q := mul_le_mul hq hq' (by linarith) (by linarith)
      _ = Q ^ 2 := by ring
  have h4 : 2 * Q / Mx x < 1 / Q ^ 2 := by
    rw [div_lt_div_iff₀ hM (by positivity)]
    nlinarith
  linarith

/-! ## Complete sums of `V²` -/

/-- The number of `(y, z) ∈ [1, N]²` with `y + z = n`. -/
noncomputable def J2 (N n : ℕ) : ℝ :=
  ∑ y ∈ Icc 1 N, ∑ z ∈ Icc 1 N, if y + z = n then (1 : ℝ) else 0

theorem J2_eq {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N + 1) : J2 N n = (n : ℝ) - 1 := by
  unfold J2
  have h1 : ∀ y ∈ Icc 1 N, (∑ z ∈ Icc 1 N, if y + z = n then (1 : ℝ) else 0) =
      if y + 1 ≤ n then 1 else 0 := by
    intro y hy
    rw [mem_Icc] at hy
    by_cases h : y + 1 ≤ n
    · rw [if_pos h, sum_eq_single (n - y)]
      · rw [if_pos (by omega)]
      · intro z _ hz; rw [if_neg (by omega)]
      · intro hz; exfalso; apply hz; rw [mem_Icc]; omega
    · rw [if_neg h]
      apply sum_eq_zero
      intro z hz
      rw [mem_Icc] at hz
      rw [if_neg (by omega)]
  rw [sum_congr rfl h1, ← sum_filter]
  have hset : (Icc 1 N).filter (fun y => y + 1 ≤ n) = Icc 1 (n - 1) := by
    ext y; simp only [mem_filter, mem_Icc]; omega
  rw [hset, sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring_nf
  rw [Nat.cast_sub hn]
  push_cast; ring

lemma V_neg_sq (N : ℕ) (θ : ℝ) (n : ℕ) :
    V N (-θ) ^ 2 * e (n * θ) = ∑ y ∈ Icc 1 N, ∑ z ∈ Icc 1 N, e (((n : ℤ) - y - z : ℤ) * θ) := by
  unfold V
  rw [pow_two]
  simp only [sum_mul, mul_sum]
  refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
  rw [← e_add, ← e_add]
  congr 1; push_cast; ring

/-- The complete sum of `V²`. -/
theorem full_sum_V2 {N M : ℕ} [NeZero M] (h2 : 2 * N < M) {n : ℕ} (hn : n < M) (γ : ℝ) :
    ∑ k : ZMod M, V N (-((k.val : ℝ) / M - γ)) ^ 2 * e (n * ((k.val : ℝ) / M - γ)) =
      (M : ℂ) * (J2 N n : ℂ) := by
  simp_rw [V_neg_sq]
  rw [sum_comm]
  unfold J2
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun y hy => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun z hz => ?_
  rw [mem_Icc] at hy hz
  have hs := sum_e_int_zmod (M := M) ((n : ℤ) - y - z)
    (by rw [abs_lt]; constructor <;> omega) γ
  push_cast at hs
  rw [hs]
  by_cases h : y + z = n
  · rw [if_pos (by omega), if_pos h]; simp
  · rw [if_neg (by omega), if_neg h]; simp

/-! ## The tail of `V²` off an arc -/

lemma norm_V_le_inv (N : ℕ) {θ : ℝ} (h : 0 < dist0 θ) : ‖V N (-θ)‖ ≤ 1 / (2 * dist0 θ) := by
  have := norm_sum_Ioc_e_le 0 N (-θ)
  have hI : Ioc 0 (0 + N) = Icc 1 N := by ext m; simp only [mem_Ioc, mem_Icc]; omega
  rw [hI] at this
  unfold V
  refine this.trans ((G_le_inv (by rw [dist0_neg]; exact h)).trans ?_)
  rw [dist0_neg]

/-- **The tail of `V²`**: off an arc of half-width `δ > 0` around `γ`,
`∑ |V(-(k/M - γ))|² ≤ 2M/δ + 1/(2δ²)`. -/
theorem tail_V2_le {N M : ℕ} [NeZero M] (γ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (T : Finset (ZMod M)) (hT : ∀ k ∈ T, δ < dist0 ((k.val : ℝ) / M - γ)) :
    ∑ k ∈ T, ‖V N (-((k.val : ℝ) / M - γ))‖ ^ 2 ≤ 2 * M / δ + 1 / (2 * δ ^ 2) := by
  set d : ZMod M → ℝ := fun k => dist0 ((k.val : ℝ) / M - γ) with hd
  have hex : ∀ k : ZMod M, ∃ j : ℕ, d k ≤ 2 ^ (j + 1) * δ := by
    intro k
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / δ) (by norm_num : (1 : ℝ) < 2)
    refine ⟨j, ?_⟩
    have h1 : d k ≤ 1 / 2 := dist0_le_half _
    have h2 : 1 < 2 ^ j * δ := by rwa [div_lt_iff₀ hδ] at hj
    have h3 : (2 : ℝ) ^ (j + 1) * δ = 2 * (2 ^ j * δ) := by ring
    linarith
  set g : ZMod M → ℕ := fun k => Nat.find (hex k) with hg
  have hg_up : ∀ k, d k ≤ 2 ^ (g k + 1) * δ := fun k => Nat.find_spec (hex k)
  have hg_lo : ∀ k ∈ T, 2 ^ g k * δ < d k := by
    intro k hk
    rcases Nat.eq_zero_or_pos (g k) with h0 | hpos
    · rw [h0, pow_zero, one_mul]; exact hT k hk
    · have := Nat.find_min (hex k) (show g k - 1 < g k by omega)
      push_neg at this
      rwa [show g k - 1 + 1 = g k by omega] at this
  have hpt : ∀ k ∈ T, ‖V N (-((k.val : ℝ) / M - γ))‖ ^ 2 ≤ 1 / (4 * (2 ^ g k * δ) ^ 2) := by
    intro k hk
    have hlo := hg_lo k hk
    have hpos : 0 < d k := lt_trans (by positivity) hlo
    have h1 := norm_V_le_inv N hpos
    have h2 : 1 / (2 * d k) ≤ 1 / (2 * (2 ^ g k * δ)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have h3 := h1.trans h2
    calc ‖V N (-((k.val : ℝ) / M - γ))‖ ^ 2 ≤ (1 / (2 * (2 ^ g k * δ))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h3 2
      _ = 1 / (4 * (2 ^ g k * δ) ^ 2) := by ring
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  -- fiberwise
  rw [← sum_fiberwise_of_maps_to (g := g) (t := T.image g) (fun k hk => mem_image_of_mem g hk)]
  have hfib : ∀ j ∈ T.image g, ∑ k ∈ T.filter (fun k => g k = j),
      ‖V N (-((k.val : ℝ) / M - γ))‖ ^ 2 ≤ (1 / 2) ^ j * (M / δ) + (1 / 2) ^ j * (1 / (4 * δ ^ 2)) := by
    intro j _
    have hc : ((T.filter (fun k => g k = j)).card : ℝ) ≤ 2 * (2 ^ (j + 1) * δ) * M + 1 := by
      refine le_trans ?_ (card_arc_le (M := M) γ (by positivity : (0 : ℝ) ≤ 2 ^ (j + 1) * δ))
      exact_mod_cast card_le_card (fun k hk => by
        rw [mem_filter] at hk ⊢
        refine ⟨mem_univ _, ?_⟩
        have := hg_up k
        rw [hk.2] at this
        exact_mod_cast this)
    calc ∑ k ∈ T.filter (fun k => g k = j), ‖V N (-((k.val : ℝ) / M - γ))‖ ^ 2
        ≤ ∑ k ∈ T.filter (fun k => g k = j), 1 / (4 * (2 ^ j * δ) ^ 2) := by
          refine sum_le_sum fun k hk => ?_
          rw [mem_filter] at hk
          have := hpt k hk.1
          rwa [hk.2] at this
      _ = ((T.filter (fun k => g k = j)).card : ℝ) * (1 / (4 * (2 ^ j * δ) ^ 2)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (2 * (2 ^ (j + 1) * δ) * M + 1) * (1 / (4 * (2 ^ j * δ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (1 / 2) ^ j * (M / δ) + (1 / 4) ^ j * (1 / (4 * δ ^ 2)) := by
          have h2 : (0 : ℝ) < 2 ^ j := by positivity
          rw [one_div_pow, one_div_pow, show (4 : ℝ) ^ j = (2 ^ j) ^ 2 by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num]
          field_simp
          ring
      _ ≤ (1 / 2) ^ j * (M / δ) + (1 / 2) ^ j * (1 / (4 * δ ^ 2)) := by
          gcongr
          norm_num
  refine (sum_le_sum hfib).trans ?_
  rw [sum_add_distrib, ← sum_mul, ← sum_mul]
  set m := (T.image g).sup id + 1
  have hsub : T.image g ⊆ range m := by
    intro j hj
    rw [mem_range]
    have := le_sup (f := id) hj
    simp only [id] at this
    omega
  have hgeo : ∑ j ∈ T.image g, (1 / 2 : ℝ) ^ j ≤ 2 :=
    le_trans (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity)
      (sum_geometric_two_le m)
  have h1 : (0 : ℝ) ≤ M / δ := by positivity
  have h2 : (0 : ℝ) ≤ 1 / (4 * δ ^ 2) := by positivity
  calc (∑ j ∈ T.image g, (1 / 2 : ℝ) ^ j) * (M / δ) +
        (∑ j ∈ T.image g, (1 / 2 : ℝ) ^ j) * (1 / (4 * δ ^ 2))
      ≤ 2 * (M / δ) + 2 * (1 / (4 * δ ^ 2)) := by gcongr
    _ = 2 * M / δ + 1 / (2 * δ ^ 2) := by field_simp; ring

end LeanLab.ExceptionalSet.MVMajor
