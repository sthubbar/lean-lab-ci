/-
P0038 Shao 2012, Proposition 1.4 for a prime modulus p ≥ 7, the base case of Proposition 3.1:
sort f, apply Lemma 2.1 contrapositively, take superlevel sets, use Cauchy-Davenport, then the
monotonicity of h(x, y, z) = xy + yz + zx - 5/8 (x + y + z).
AI-written Lean code, Claude, 2026-10-17, run 20261016T2303Z-22954, unit U-0097.
-/
import LeanLab.DensityGoldbach.Statements
import LeanLab.DensityGoldbach.Lemma21

open Finset
open scoped Pointwise

namespace LeanLab.DensityGoldbach

/-- `h(x, y, z) = xy + yz + zx - 5/8 (x + y + z)`. -/
noncomputable def hfun (x y z : ℝ) : ℝ := x * y + y * z + z * x - 5 / 8 * (x + y + z)

/-- If `h(a, b, c) > 0` with `a, b, c ∈ [0, 1]`, every pair sums to at least `5/8`. -/
lemma pair_ge (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (h : 0 < hfun a b c) : 5 / 8 ≤ a + b := by
  unfold hfun at h
  by_contra hlt
  push Not at hlt
  have h1 : a * b ≤ 5 / 8 * (a + b) := by nlinarith
  have h2 : c * (a + b) ≤ 5 / 8 * c := by nlinarith
  nlinarith

/-- **The final step**: from `h(a, b, c) > 0` and `x ≥ a, y ≥ b, z ≥ c`, all in `[0, 1]`, get
`xyz > 0` and `x + y + z > 3/2`. -/
lemma final_step (a b c x y z : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx1 : x ≤ 1) (hy1 : y ≤ 1) (hz1 : z ≤ 1) (hax : a ≤ x) (hby : b ≤ y) (hcz : c ≤ z)
    (h : 0 < hfun a b c) : 0 < x * y * z ∧ 3 / 2 < x + y + z := by
  have ha1 : a ≤ 1 := by linarith
  have hb1 : b ≤ 1 := by linarith
  have hc1 : c ≤ 1 := by linarith
  have hab := pair_ge a b c ha hb hc ha1 hb1 h
  have hbc := pair_ge b c a hb hc ha hb1 hc1 (by unfold hfun at h ⊢; linarith)
  have hca := pair_ge c a b hc ha hb hc1 ha1 (by unfold hfun at h ⊢; linarith)
  -- move one variable at a time; `h` is affine in each variable with slope ≥ 0.
  have s1 : hfun a b c ≤ hfun x b c := by
    unfold hfun; nlinarith
  have s2 : hfun x b c ≤ hfun x y c := by
    unfold hfun; nlinarith
  have s3 : hfun x y c ≤ hfun x y z := by
    unfold hfun; nlinarith
  have hpos : 0 < hfun x y z := by linarith
  have hx : 0 ≤ x := by linarith
  have hy : 0 ≤ y := by linarith
  have hz : 0 ≤ z := by linarith
  unfold hfun at hpos
  constructor
  · -- a zero coordinate forces `h ≤ 0`.
    rcases hx.lt_or_eq with hx' | hx'
    · rcases hy.lt_or_eq with hy' | hy'
      · rcases hz.lt_or_eq with hz' | hz'
        · positivity
        · rw [← hz'] at hpos; nlinarith
      · rw [← hy'] at hpos; nlinarith
    · rw [← hx'] at hpos; nlinarith
  · -- `xy + yz + zx ≤ (x + y + z)² / 3`, so `s > 15/8`.
    have hq : x * y + y * z + z * x ≤ (x + y + z) ^ 2 / 3 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    have hs : 5 / 8 * (x + y + z) < (x + y + z) ^ 2 / 3 := by linarith
    have hs0 : 0 ≤ x + y + z := by linarith
    generalize x + y + z = s at hs hs0 ⊢
    by_contra hc; push Not at hc
    nlinarith

/-- **Proposition 1.4 for a prime modulus `p ≥ 7`.** -/
theorem prop14_prime (p : ℕ) [hp : Fact p.Prime] (hp7 : 7 ≤ p) : Prop14 p := by
  intro f hf hsum x
  set U := unitsMod p with hU
  have hUeq : U = univ.erase (0 : ZMod p) := by
    ext u; simp [hU, unitsMod, isUnit_iff_ne_zero]
  have hn : #U = p - 1 := by
    rw [hUeq, card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  rw [Nat.totient_prime hp.out] at hsum
  set n := #U with hndef
  have hcardU : Fintype.card U = n := Fintype.card_coe U
  let e : Fin n ≃ U := (Fintype.equivFinOfCardEq hcardU).symm
  let g : Fin n → ℝ := fun i => f (e i).1
  let σ := Tuple.sort g
  have hmono : Monotone (g ∘ σ) := Tuple.monotone_sort g
  let w : Fin n → ZMod p := fun i => (e (σ (Fin.rev i))).1
  have hw_inj : Function.Injective w := by
    intro i j h
    exact Fin.rev_injective (σ.injective (e.injective (Subtype.ext h)))
  have hwU : ∀ i, w i ∈ U := fun i => (e (σ (Fin.rev i))).2
  let dec : Fin n → ℝ := fun i => f (w i)
  have hanti : ∀ i j : Fin n, i ≤ j → dec j ≤ dec i := by
    intro i j hij
    exact hmono (Fin.rev_le_rev.2 hij)
  let a : ℕ → ℝ := fun i => if h : i < n then dec ⟨i, h⟩ else 0
  have ha_eq : ∀ i (h : i < n), a i = dec ⟨i, h⟩ := fun i h => dif_pos h
  have hasum : ∑ i ∈ range n, a i = ∑ u ∈ U, f u := by
    rw [← Fin.sum_univ_eq_sum_range a n]
    have h1 : ∑ i : Fin n, a i.val = ∑ i : Fin n, dec i :=
      sum_congr rfl fun i _ => ha_eq i.val i.isLt
    rw [h1]
    have h2 : ∑ i : Fin n, dec i = ∑ u : U, f u.1 :=
      Equiv.sum_comp ((Fin.revPerm).trans (σ.trans e)) (fun u : U => f u.1)
    rw [h2, sum_coe_sort U f]
  -- `n = 2m` with `m ≥ 3`.
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  obtain ⟨m, hm⟩ : ∃ m, n = 2 * m := ⟨(p - 1) / 2, by obtain ⟨k, hk⟩ := hodd; omega⟩
  have hm3 : 3 ≤ m := by omega
  -- Lemma 2.1, contrapositively.
  obtain ⟨i, j, k, hi, hj, hk, hs, hlt⟩ : ∃ i j k, i < n ∧ j < n ∧ k < n ∧ n ≤ i + j + k ∧
      5 / 8 * (a i + a j + a k) < a i * a j + a j * a k + a k * a i := by
    by_contra hne
    push Not at hne
    have hbd : ∀ i, i < 2 * m → 0 ≤ a i ∧ a i ≤ 1 := by
      intro i hi; rw [ha_eq i (by omega)]; exact hf _
    have hmo : ∀ i j, i ≤ j → j < 2 * m → a j ≤ a i := by
      intro i j hij hj
      rw [ha_eq i (by omega), ha_eq j (by omega)]
      exact hanti _ _ (Fin.mk_le_mk.2 hij)
    have := shao_lemma21 m hm3 a hbd hmo (fun i j k hi hj hk hs =>
      hne i j k (by omega) (by omega) (by omega) (by omega))
    rw [← hm, hasum] at this
    have hn' : ((p - 1 : ℕ) : ℝ) = (2 * m : ℕ) := by rw [← hn, hm]
    push_cast at hn'
    rw [hn'] at hsum
    linarith
  set ii : Fin n := ⟨i, hi⟩
  set jj : Fin n := ⟨j, hj⟩
  set kk : Fin n := ⟨k, hk⟩
  rw [ha_eq i hi, ha_eq j hj, ha_eq k hk] at hlt
  -- superlevel sets
  have level : ∀ t : Fin n, t.val + 1 ≤ #(U.filter (fun u => dec t ≤ f u)) := by
    intro t
    have hsub : (Iic t).image w ⊆ U.filter (fun u => dec t ≤ f u) := by
      intro u hu
      obtain ⟨l, hl, rfl⟩ := mem_image.1 hu
      exact mem_filter.2 ⟨hwU l, hanti l t (mem_Iic.1 hl)⟩
    have := card_le_card hsub
    rwa [card_image_of_injective _ hw_inj, Fin.card_Iic] at this
  set I := U.filter (fun u => dec ii ≤ f u)
  set J := U.filter (fun u => dec jj ≤ f u)
  set K := U.filter (fun u => dec kk ≤ f u)
  have hI : i + 1 ≤ #I := level ii
  have hJ : j + 1 ≤ #J := level jj
  have hK : k + 1 ≤ #K := level kk
  have hIne : I.Nonempty := card_pos.1 (by omega)
  have hJne : J.Nonempty := card_pos.1 (by omega)
  have hKne : K.Nonempty := card_pos.1 (by omega)
  have c1 := ZMod.cauchy_davenport hp.out hIne hJne
  have c2 := ZMod.cauchy_davenport hp.out (hIne.add hJne) hKne
  have hbig : p ≤ #(I + J + K) := by
    omega
  have huniv : I + J + K = univ := by
    apply eq_univ_of_card
    rw [ZMod.card]
    exact le_antisymm (by simpa [ZMod.card] using card_le_univ (I + J + K)) hbig
  have hx : x ∈ I + J + K := by rw [huniv]; exact mem_univ x
  obtain ⟨y, hy, z3, hz3, rfl⟩ := mem_add.1 hx
  obtain ⟨z1, hz1, z2, hz2, rfl⟩ := mem_add.1 hy
  obtain ⟨hz1U, hz1f⟩ := mem_filter.1 hz1
  obtain ⟨hz2U, hz2f⟩ := mem_filter.1 hz2
  obtain ⟨hz3U, hz3f⟩ := mem_filter.1 hz3
  have hh : 0 < hfun (dec ii) (dec jj) (dec kk) := by unfold hfun; linarith
  obtain ⟨hprod, hsum3⟩ := final_step (dec ii) (dec jj) (dec kk) (f z1) (f z2) (f z3)
    (hf _).1 (hf _).1 (hf _).1 (hf _).2 (hf _).2 (hf _).2 hz1f hz2f hz3f hh
  exact ⟨z1, hz1U, z2, hz2U, z3, hz3U, rfl, hprod, hsum3⟩

end LeanLab.DensityGoldbach
