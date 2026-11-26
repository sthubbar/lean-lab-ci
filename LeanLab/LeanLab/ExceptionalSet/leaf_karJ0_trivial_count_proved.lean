/-
PROVED twin of `leaf_karJ0_trivial_count` of `LeanLab.ExceptionalSet.KarLemma2CoreSplit`,
the starting count of Vinogradov's mean value theorem used in Karacuba 1971 Lemma 1, p. 243:
`karJ0 d k M ≤ d! (M+1)^{2k-d}` for `1 ≤ d ≤ k`.

Proof: fix `u` and the last `k - d` coordinates of `v`; the first `d` coordinates of `v` then have
prescribed power sums `p_1, ..., p_d`; Newton's identities, `MvPolynomial.mul_esymm_eq_sum`, give
the elementary symmetric functions, Vieta gives the polynomial `Π (X - v_i)`, its roots give the
multiset, and a tuple with a given multiset of values is one of at most `d!` rearrangements.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.KarLemma2CoreSplit

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open Finset

/-- PROVED. Newton's identities: equal power sums `p_1, ..., p_d` of two real `d`-tuples give
equal elementary symmetric functions of every order. -/
theorem karNewton_esymm_eq_of_psum_eq {d : ℕ} (x y : Fin d → ℝ)
    (h : ∀ j, 1 ≤ j → j ≤ d → ∑ i, x i ^ j = ∑ i, y i ^ j) :
    ∀ k, (univ.val.map x).esymm k = (univ.val.map y).esymm k := by
  have hp : ∀ j ≤ d, MvPolynomial.aeval x (MvPolynomial.psum (Fin d) ℝ j)
      = MvPolynomial.aeval y (MvPolynomial.psum (Fin d) ℝ j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [MvPolynomial.psum]
    · simp [MvPolynomial.psum, h j hj0 hj]
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k ≤ d
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp
      have hx := congrArg (MvPolynomial.aeval x) (MvPolynomial.mul_esymm_eq_sum (Fin d) ℝ k)
      have hy := congrArg (MvPolynomial.aeval y) (MvPolynomial.mul_esymm_eq_sum (Fin d) ℝ k)
      simp only [map_mul, map_pow, map_neg, map_one, map_sum, map_natCast] at hx hy
      rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin d) ℝ,
        ← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin d) ℝ]
      have : (k : ℝ) * MvPolynomial.aeval x (MvPolynomial.esymm (Fin d) ℝ k)
          = k * MvPolynomial.aeval y (MvPolynomial.esymm (Fin d) ℝ k) := by
        rw [hx, hy]; congr 1; apply Finset.sum_congr rfl; intro a ha
        rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
        rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.aeval_esymm_eq_multiset_esymm,
          ih a.1 ha.2, hp a.2 (by omega)]
      exact mul_left_cancel₀ (by positivity) this
    · have hz : ∀ z : Fin d → ℝ, (univ.val.map z).esymm k = 0 := by
        intro z
        simp only [Multiset.esymm]
        rw [Multiset.powersetCard_eq_empty]
        · simp
        · simp; omega
      rw [hz, hz]

/-- PROVED. Vieta: equal elementary symmetric functions give equal monic polynomials
`Π (X - r)`, hence equal multisets of roots. -/
theorem karVieta_multiset_eq_of_esymm_eq (s t : Multiset ℝ) (hc : Multiset.card s = Multiset.card t)
    (h : ∀ k, s.esymm k = t.esymm k) : s = t := by
  have hp : (s.map fun r => Polynomial.X - Polynomial.C r).prod
      = (t.map fun r => Polynomial.X - Polynomial.C r).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hc]
    simp_rw [h]
  have := congrArg Polynomial.roots hp
  rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this

/-- PROVED. Two tuples with the same multiset of values differ by a permutation. -/
theorem karTuple_exists_perm_of_map_eq {d M : ℕ} (w w0 : Fin d → Fin (M + 1))
    (h : univ.val.map w = univ.val.map w0) : ∃ σ : Equiv.Perm (Fin d), w = w0 ∘ σ := by
  have hperm : List.ofFn (w ∘ Tuple.sort w) = List.ofFn (w0 ∘ Tuple.sort w0) := by
    apply List.Perm.eq_of_sortedLE
    · exact List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort w)
    · exact List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort w0)
    · refine ((Equiv.Perm.ofFn_comp_perm _ _).trans ?_).trans (Equiv.Perm.ofFn_comp_perm _ _).symm
      rw [Fin.univ_val_map, Fin.univ_val_map] at h
      exact Multiset.coe_eq_coe.mp h
  have he := List.ofFn_injective hperm
  refine ⟨Tuple.sort w0 * (Tuple.sort w)⁻¹, ?_⟩
  funext i
  have := congrFun he ((Tuple.sort w)⁻¹ i)
  simpa [Equiv.Perm.mul_apply] using this

/-- PROVED. At most `d!` tuples `w` from `0, ..., M` have prescribed power sums
`Σ w_i^j`, `j = 1, ..., d`. -/
theorem karCard_powsum_fiber_le (d M : ℕ) (c : Fin d → ℝ) :
    (univ.filter (fun w : Fin d → Fin (M + 1) =>
      ∀ j : Fin d, ∑ i, ((w i : ℕ) : ℝ) ^ ((j : ℕ) + 1) = c j)).card ≤ d.factorial := by
  classical
  set S := univ.filter (fun w : Fin d → Fin (M + 1) =>
      ∀ j : Fin d, ∑ i, ((w i : ℕ) : ℝ) ^ ((j : ℕ) + 1) = c j) with hS
  rcases S.eq_empty_or_nonempty with he | ⟨w0, hw0⟩
  · rw [he]; simp
  have hsub : S ⊆ (univ : Finset (Equiv.Perm (Fin d))).image (fun σ : Equiv.Perm (Fin d) => w0 ∘ ⇑σ) := by
    intro w hw
    rw [hS, mem_filter] at hw hw0
    have hps : ∀ j, 1 ≤ j → j ≤ d → ∑ i, ((w i : ℕ) : ℝ) ^ j = ∑ i, ((w0 i : ℕ) : ℝ) ^ j := by
      intro j hj1 hjd
      have h1 := hw.2 ⟨j - 1, by omega⟩
      have h2 := hw0.2 ⟨j - 1, by omega⟩
      simp only [Nat.sub_add_cancel hj1] at h1 h2
      rw [h1, h2]
    have hm := karVieta_multiset_eq_of_esymm_eq _ _ (by simp)
      (karNewton_esymm_eq_of_psum_eq (fun i => ((w i : ℕ) : ℝ)) (fun i => ((w0 i : ℕ) : ℝ)) hps)
    have hinj : Function.Injective (fun a : Fin (M + 1) => ((a : ℕ) : ℝ)) := by
      intro a b hab; exact Fin.ext (by simpa using hab)
    have hm' : univ.val.map w = univ.val.map w0 := by
      apply Multiset.map_injective hinj
      simpa [Multiset.map_map, Function.comp_def] using hm
    obtain ⟨σ, hσ⟩ := karTuple_exists_perm_of_map_eq w w0 hm'
    exact mem_image.mpr ⟨σ, mem_univ _, hσ.symm⟩
  calc S.card ≤ _ := card_le_card hsub
    _ ≤ (univ : Finset (Equiv.Perm (Fin d))).card := card_image_le
    _ = d.factorial := by simp [Fintype.card_perm]


/-- PROVED twin of `leaf_karJ0_trivial_count`, statement copied verbatim: Vinogradov's mean value
theorem, Karacuba's reference [1], the trivial count `J_k(0) ≤ d! (M+1)^{2k-d}`. Fix `u` and
`v_{d+1}, ..., v_k`; Newton's identities make the multiset of `v_1, ..., v_d` unique. -/
theorem leaf_karJ0_trivial_count_proved :
    ∀ d k M : ℕ, 1 ≤ d → d ≤ k →
      karJ0 d k M ≤ (d.factorial : ℝ) * ((M : ℝ) + 1) ^ (2 * k - d) := by
  classical
  intro d k M _ hdk
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hdk
  have hexp : 2 * (d + e) - d = (d + e) + e := by omega
  rw [hexp]
  unfold karJ0
  simp_rw [Finset.sum_boole]
  have key : ∀ u : Fin (d + e) → Fin (M + 1),
      (univ.filter (fun v : Fin (d + e) → Fin (M + 1) => ∀ j : Fin d,
        ∑ i : Fin (d + e), ((u i : ℕ) : ℝ) ^ ((j : ℕ) + 1) =
        ∑ i : Fin (d + e), ((v i : ℕ) : ℝ) ^ ((j : ℕ) + 1))).card ≤ d.factorial * (M + 1) ^ e := by
    intro u
    set A := univ.filter (fun v : Fin (d + e) → Fin (M + 1) => ∀ j : Fin d,
        ∑ i : Fin (d + e), ((u i : ℕ) : ℝ) ^ ((j : ℕ) + 1) =
        ∑ i : Fin (d + e), ((v i : ℕ) : ℝ) ^ ((j : ℕ) + 1)) with hA
    let tl : (Fin (d + e) → Fin (M + 1)) → (Fin e → Fin (M + 1)) := fun v i => v (Fin.natAdd d i)
    let hd : (Fin (d + e) → Fin (M + 1)) → (Fin d → Fin (M + 1)) := fun v i => v (Fin.castAdd e i)
    have h1 := Finset.card_le_mul_card_image A d.factorial (f := tl) (by
      intro t _
      let c : Fin d → ℝ := fun j => ∑ i : Fin (d + e), ((u i : ℕ) : ℝ) ^ ((j : ℕ) + 1)
        - ∑ i : Fin e, ((t i : ℕ) : ℝ) ^ ((j : ℕ) + 1)
      refine le_trans ?_ (karCard_powsum_fiber_le d M c)
      refine Finset.card_le_card_of_injOn hd ?_ ?_
      · intro v hv
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, hA, Finset.mem_filter, Finset.mem_univ,
          true_and] at hv ⊢
        intro j
        have h1 := hv.1 j
        have h2 := Fin.sum_univ_add (fun i => ((v i : ℕ) : ℝ) ^ ((j : ℕ) + 1))
        simp only [c, hd]; rw [← hv.2]; simp only [tl]; linarith [h1, h2]
      · intro v1 hv1 v2 hv2 h12
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, hA, Finset.mem_filter, Finset.mem_univ,
          true_and] at hv1 hv2
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · exact congrFun h12 i
        · have := congrFun (hv1.2.trans hv2.2.symm) i
          exact this)
    calc A.card ≤ d.factorial * (A.image tl).card := h1
      _ ≤ d.factorial * (M + 1) ^ e := by
        gcongr
        calc (A.image tl).card ≤ (univ : Finset (Fin e → Fin (M + 1))).card :=
              card_le_card (subset_univ _)
          _ = (M + 1) ^ e := by simp
  calc (∑ u : Fin (d + e) → Fin (M + 1), ((univ.filter (fun v : Fin (d + e) → Fin (M + 1) =>
        ∀ j : Fin d, ∑ i : Fin (d + e), ((u i : ℕ) : ℝ) ^ ((j : ℕ) + 1) =
        ∑ i : Fin (d + e), ((v i : ℕ) : ℝ) ^ ((j : ℕ) + 1))).card : ℝ))
      ≤ ∑ _u : Fin (d + e) → Fin (M + 1), ((d.factorial * (M + 1) ^ e : ℕ) : ℝ) := by
        gcongr with u; exact_mod_cast key u
    _ = (d.factorial : ℝ) * ((M : ℝ) + 1) ^ (d + e + e) := by
        simp [pow_add]; ring

end LeanLab.ExceptionalSet.U1539.KaracubaSplit

#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.leaf_karJ0_trivial_count_proved
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.karCard_powsum_fiber_le
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.karNewton_esymm_eq_of_psum_eq
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.karVieta_multiset_eq_of_esymm_eq
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.karTuple_exists_perm_of_map_eq
