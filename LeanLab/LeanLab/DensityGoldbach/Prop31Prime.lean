/-
P0038 Shao 2012, Proposition 3.1 for a prime modulus, in the form the induction needs:
the conclusion is h(f a, f b, f c) > 0 with h = hfun, and a three-function fiber version
for primes p ≥ 11 from Lemma 2.2.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0102Z-30056, unit U-0111.
-/
import LeanLab.DensityGoldbach.PrimeProp14
import LeanLab.DensityGoldbach.Lemma22

open Finset
open scoped Pointwise

namespace LeanLab.DensityGoldbach

/-- `h` only grows when each coordinate grows, inside `[0, 1]`, once it is positive. -/
lemma hfun_mono (a b c x y z : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx1 : x ≤ 1) (hy1 : y ≤ 1) (hz1 : z ≤ 1) (hax : a ≤ x) (hby : b ≤ y) (hcz : c ≤ z)
    (h : 0 < hfun a b c) : 0 < hfun x y z := by
  have ha1 : a ≤ 1 := by linarith
  have hb1 : b ≤ 1 := by linarith
  have hc1 : c ≤ 1 := by linarith
  have hab := pair_ge a b c ha hb hc ha1 hb1 h
  have hbc := pair_ge b c a hb hc ha hb1 hc1 (by unfold hfun at h ⊢; linarith)
  have hca := pair_ge c a b hc ha hb hc1 ha1 (by unfold hfun at h ⊢; linarith)
  have s1 : hfun a b c ≤ hfun x b c := by unfold hfun; nlinarith
  have s2 : hfun x b c ≤ hfun x y c := by unfold hfun; nlinarith
  have s3 : hfun x y c ≤ hfun x y z := by unfold hfun; nlinarith
  linarith

/-- Sorting a function on a finset into a non-increasing sequence, with its superlevel
sets: the `i`-th largest value is reached on at least `i + 1` points. -/
lemma sort_seq {α : Type*} (U : Finset α) (g : α → ℝ) (hg : ∀ a, 0 ≤ g a ∧ g a ≤ 1) :
    ∃ a : ℕ → ℝ, (∀ i, i < #U → 0 ≤ a i ∧ a i ≤ 1) ∧
      (∀ i j, i ≤ j → j < #U → a j ≤ a i) ∧
      ∑ i ∈ range #U, a i = ∑ u ∈ U, g u ∧
      ∀ i, i < #U → i + 1 ≤ #(U.filter (fun u => a i ≤ g u)) := by
  classical
  set n := #U with hndef
  have hcardU : Fintype.card U = n := Fintype.card_coe U
  let e : Fin n ≃ U := (Fintype.equivFinOfCardEq hcardU).symm
  let gg : Fin n → ℝ := fun i => g (e i).1
  let σ := Tuple.sort gg
  have hmono : Monotone (gg ∘ σ) := Tuple.monotone_sort gg
  let w : Fin n → α := fun i => (e (σ (Fin.rev i))).1
  have hw_inj : Function.Injective w := by
    intro i j h
    exact Fin.rev_injective (σ.injective (e.injective (Subtype.ext h)))
  have hwU : ∀ i, w i ∈ U := fun i => (e (σ (Fin.rev i))).2
  let dec : Fin n → ℝ := fun i => g (w i)
  have hanti : ∀ i j : Fin n, i ≤ j → dec j ≤ dec i := by
    intro i j hij
    exact hmono (Fin.rev_le_rev.2 hij)
  let a : ℕ → ℝ := fun i => if h : i < n then dec ⟨i, h⟩ else 0
  have ha_eq : ∀ i (h : i < n), a i = dec ⟨i, h⟩ := fun i h => dif_pos h
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [ha_eq i hi]; exact hg _
  · intro i j hij hj
    rw [ha_eq i (by omega), ha_eq j hj]
    exact hanti _ _ (Fin.mk_le_mk.2 hij)
  · rw [← Fin.sum_univ_eq_sum_range a n]
    have h1 : ∑ i : Fin n, a i.val = ∑ i : Fin n, dec i :=
      sum_congr rfl fun i _ => ha_eq i.val i.isLt
    rw [h1]
    have h2 : ∑ i : Fin n, dec i = ∑ u : U, g u.1 :=
      Equiv.sum_comp ((Fin.revPerm).trans (σ.trans e)) (fun u : U => g u.1)
    rw [h2, sum_coe_sort U g]
  · intro i hi
    rw [ha_eq i hi]
    set t : Fin n := ⟨i, hi⟩
    have hsub : (Iic t).image w ⊆ U.filter (fun u => dec t ≤ g u) := by
      intro u hu
      obtain ⟨l, hl, rfl⟩ := mem_image.1 hu
      exact mem_filter.2 ⟨hwU l, hanti l t (mem_Iic.1 hl)⟩
    have := card_le_card hsub
    rwa [card_image_of_injective _ hw_inj, Fin.card_Iic] at this

lemma card_unitsMod_prime (p : ℕ) [hp : Fact p.Prime] : #(unitsMod p) = p - 1 := by
  have hUeq : unitsMod p = univ.erase (0 : ZMod p) := by
    ext u; simp [unitsMod, isUnit_iff_ne_zero]
  rw [hUeq, card_erase_of_mem (mem_univ _), card_univ, ZMod.card]

/-- Three superlevel sets in `Z/p` of sizes `i + 1, j + 1, k + 1` with `i + j + k ≥ p - 1`
cover every residue as a sum. -/
lemma three_levels (p : ℕ) [hp : Fact p.Prime] (I J K : Finset (ZMod p)) (i j k : ℕ)
    (hI : i + 1 ≤ #I) (hJ : j + 1 ≤ #J) (hK : k + 1 ≤ #K) (hs : p - 1 ≤ i + j + k) :
    I + J + K = univ := by
  have hIne : I.Nonempty := card_pos.1 (by omega)
  have hJne : J.Nonempty := card_pos.1 (by omega)
  have hKne : K.Nonempty := card_pos.1 (by omega)
  have c1 := ZMod.cauchy_davenport hp.out hIne hJne
  have c2 := ZMod.cauchy_davenport hp.out (hIne.add hJne) hKne
  have hbig : p ≤ #(I + J + K) := by omega
  apply eq_univ_of_card
  rw [ZMod.card]
  exact le_antisymm (by simpa [ZMod.card] using card_le_univ (I + J + K)) hbig

/-- Shao Prop 3.1's statement for one modulus: average above `5/8` on the reduced residues
gives every `x` as `a + b + c` with reduced summands and `h(f a, f b, f c) > 0`. -/
def Prop31 (m : ℕ) [NeZero m] : Prop := ∀ f : ZMod m → ℝ,
  (∀ a, 0 ≤ f a ∧ f a ≤ 1) → 5 / 8 * (m.totient : ℝ) < ∑ a ∈ unitsMod m, f a →
  ∀ x : ZMod m, ∃ a₁ ∈ unitsMod m, ∃ a₂ ∈ unitsMod m, ∃ a₃ ∈ unitsMod m,
    x = a₁ + a₂ + a₃ ∧ 0 < hfun (f a₁) (f a₂) (f a₃)

/-- Prop 3.1 implies Prop 1.4 at the same modulus, by `final_step`. -/
theorem prop14_of_prop31 (m : ℕ) [NeZero m] (h : Prop31 m) : Prop14 m := by
  intro f hf hsum x
  obtain ⟨a₁, h1, a₂, h2, a₃, h3, rfl, hh⟩ := h f hf hsum x
  obtain ⟨hp, hs⟩ := final_step _ _ _ _ _ _ (hf a₁).1 (hf a₂).1 (hf a₃).1 (hf a₁).2 (hf a₂).2
    (hf a₃).2 le_rfl le_rfl le_rfl hh
  exact ⟨a₁, h1, a₂, h2, a₃, h3, rfl, hp, hs⟩

/-- **Shao Prop 3.1, base case**: a prime modulus `p ≥ 7`. -/
theorem prop31_prime (p : ℕ) [hp : Fact p.Prime] (hp7 : 7 ≤ p) : Prop31 p := by
  intro f hf hsum x
  set U := unitsMod p with hU
  have hn : #U = p - 1 := card_unitsMod_prime p
  rw [Nat.totient_prime hp.out] at hsum
  obtain ⟨a, hbd, hmo, hasum, hlev⟩ := sort_seq U f hf
  rw [hn] at hbd hmo hasum hlev
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  obtain ⟨m, hm⟩ : ∃ m, p - 1 = 2 * m := ⟨(p - 1) / 2, by obtain ⟨k, hk⟩ := hodd; omega⟩
  have hm3 : 3 ≤ m := by omega
  obtain ⟨i, j, k, hi, hj, hk, hs, hlt⟩ : ∃ i j k, i < p - 1 ∧ j < p - 1 ∧ k < p - 1 ∧
      p - 1 ≤ i + j + k ∧ 5 / 8 * (a i + a j + a k) < a i * a j + a j * a k + a k * a i := by
    by_contra hne
    push Not at hne
    rw [hm] at hbd hmo hasum
    have := shao_lemma21 m hm3 a hbd hmo (fun i j k hi hj hk hs =>
      hne i j k (by omega) (by omega) (by omega) (by omega))
    rw [hasum] at this
    have hn' : ((p - 1 : ℕ) : ℝ) = (2 * m : ℕ) := by rw [hm]
    push_cast at hn'
    rw [hn'] at hsum
    linarith
  have huniv := three_levels p _ _ _ i j k (hlev i hi) (hlev j hj) (hlev k hk) hs
  have hx : x ∈ U.filter (fun u => a i ≤ f u) + U.filter (fun u => a j ≤ f u) +
      U.filter (fun u => a k ≤ f u) := by rw [huniv]; exact mem_univ x
  obtain ⟨y, hy, z3, hz3, rfl⟩ := mem_add.1 hx
  obtain ⟨z1, hz1, z2, hz2, rfl⟩ := mem_add.1 hy
  obtain ⟨hz1U, hz1f⟩ := mem_filter.1 hz1
  obtain ⟨hz2U, hz2f⟩ := mem_filter.1 hz2
  obtain ⟨hz3U, hz3f⟩ := mem_filter.1 hz3
  have hh : 0 < hfun (a i) (a j) (a k) := by unfold hfun; linarith
  exact ⟨z1, hz1U, z2, hz2U, z3, hz3U, rfl, hfun_mono _ _ _ _ _ _ (hbd i hi).1 (hbd j hj).1
    (hbd k hk).1 (hf _).2 (hf _).2 (hf _).2 hz1f hz2f hz3f hh⟩

/-- **The fiber step of Shao Prop 3.1**, `p ≥ 11` prime: three functions on `Z/p` with values
in `[0, 1]` whose sums over the nonzero residues `S₁, S₂, S₃` satisfy
`S₁S₂ + S₂S₃ + S₃S₁ > 5/8 (p - 1)(S₁ + S₂ + S₃)`, that is `h` of the averages is positive;
then every `y` is `s + t + r`, nonzero, with `h(g₁ s, g₂ t, g₃ r) > 0`. By Lemma 2.2. -/
theorem prime_three (p : ℕ) [hp : Fact p.Prime] (hp11 : 11 ≤ p) (g₁ g₂ g₃ : ZMod p → ℝ)
    (hg₁ : ∀ a, 0 ≤ g₁ a ∧ g₁ a ≤ 1) (hg₂ : ∀ a, 0 ≤ g₂ a ∧ g₂ a ≤ 1)
    (hg₃ : ∀ a, 0 ≤ g₃ a ∧ g₃ a ≤ 1)
    (hsum : 5 / 8 * ((p : ℝ) - 1) * ((∑ u ∈ unitsMod p, g₁ u) + (∑ u ∈ unitsMod p, g₂ u)
        + (∑ u ∈ unitsMod p, g₃ u)) <
      (∑ u ∈ unitsMod p, g₁ u) * (∑ u ∈ unitsMod p, g₂ u)
        + (∑ u ∈ unitsMod p, g₂ u) * (∑ u ∈ unitsMod p, g₃ u)
        + (∑ u ∈ unitsMod p, g₃ u) * (∑ u ∈ unitsMod p, g₁ u))
    (y : ZMod p) : ∃ s ∈ unitsMod p, ∃ t ∈ unitsMod p, ∃ r ∈ unitsMod p,
      y = s + t + r ∧ 0 < hfun (g₁ s) (g₂ t) (g₃ r) := by
  set U := unitsMod p with hU
  have hn : #U = p - 1 := card_unitsMod_prime p
  obtain ⟨a, hbda, hmoa, hsa, hleva⟩ := sort_seq U g₁ hg₁
  obtain ⟨b, hbdb, hmob, hsb, hlevb⟩ := sort_seq U g₂ hg₂
  obtain ⟨c, hbdc, hmoc, hsc, hlevc⟩ := sort_seq U g₃ hg₃
  rw [hn] at hbda hmoa hsa hleva hbdb hmob hsb hlevb hbdc hmoc hsc hlevc
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  obtain ⟨m, hm⟩ : ∃ m, p - 1 = 2 * m := ⟨(p - 1) / 2, by obtain ⟨k, hk⟩ := hodd; omega⟩
  have hm5 : 5 ≤ m := by omega
  obtain ⟨i, j, k, hi, hj, hk, hs, hlt⟩ : ∃ i j k, i < p - 1 ∧ j < p - 1 ∧ k < p - 1 ∧
      p - 1 ≤ i + j + k ∧ 5 / 8 * (a i + b j + c k) < a i * b j + b j * c k + c k * a i := by
    by_contra hne
    push Not at hne
    rw [hm] at hbda hmoa hsa hbdb hmob hsb hbdc hmoc hsc
    have := shao_lemma22 m hm5 a b c hbda hbdb hbdc hmoa hmob hmoc (fun i j k hi hj hk hs =>
      hne i j k (by omega) (by omega) (by omega) (by omega))
    rw [hsa, hsb, hsc] at this
    have hn' : (p : ℝ) - 1 = 2 * m := by
      have : ((p - 1 : ℕ) : ℝ) = (2 * m : ℕ) := by rw [hm]
      push_cast at this
      rwa [Nat.cast_sub (by omega), Nat.cast_one] at this
    rw [hn'] at hsum
    linarith
  have huniv := three_levels p _ _ _ i j k (hleva i hi) (hlevb j hj) (hlevc k hk) hs
  have hx : y ∈ U.filter (fun u => a i ≤ g₁ u) + U.filter (fun u => b j ≤ g₂ u) +
      U.filter (fun u => c k ≤ g₃ u) := by rw [huniv]; exact mem_univ y
  obtain ⟨y', hy, z3, hz3, rfl⟩ := mem_add.1 hx
  obtain ⟨z1, hz1, z2, hz2, rfl⟩ := mem_add.1 hy
  obtain ⟨hz1U, hz1f⟩ := mem_filter.1 hz1
  obtain ⟨hz2U, hz2f⟩ := mem_filter.1 hz2
  obtain ⟨hz3U, hz3f⟩ := mem_filter.1 hz3
  have hh : 0 < hfun (a i) (b j) (c k) := by unfold hfun; linarith
  exact ⟨z1, hz1U, z2, hz2U, z3, hz3U, rfl, hfun_mono _ _ _ _ _ _ (hbda i hi).1 (hbdb j hj).1
    (hbdc k hk).1 (hg₁ _).2 (hg₂ _).2 (hg₃ _).2 hz1f hz2f hz3f hh⟩

end LeanLab.DensityGoldbach
