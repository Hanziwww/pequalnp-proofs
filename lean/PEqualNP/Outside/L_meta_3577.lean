import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Outside.L_meta_3577

def Pset (M t : ℕ) [NeZero M] : Finset (Finset (ZMod M)) :=
  (Finset.univ : Finset (ZMod M)).powersetCard t

def Fset (M t : ℕ) [NeZero M] (r : ZMod M) : Finset (Finset (ZMod M)) :=
  (Pset M t).filter (fun A => A.sum id = r)

def eCount (M t : ℕ) [NeZero M] (a b : ZMod M) : ℕ :=
  ((Fset M t a) ×ˢ (Fset M t b)).filter (fun p => Disjoint p.1 p.2) |>.card

def Ik (M : ℕ) [NeZero M] (k : ℕ) : Finset (ZMod M) :=
  (Finset.Ico k (k + 24)).image (Nat.cast : ℕ → ZMod M)

lemma mem_Ik {M : ℕ} [NeZero M] {k : ℕ} (hk2 : k + 24 ≤ M) (y : ZMod M) :
    y ∈ Ik M k ↔ k ≤ y.val ∧ y.val < k + 24 := by
  simp only [Ik, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    exact ⟨ha1, ha2⟩
  · rintro ⟨hy1, hy2⟩
    exact ⟨y.val, ⟨hy1, hy2⟩, ZMod.natCast_zmod_val y⟩

lemma Ik_injOn {M : ℕ} [NeZero M] {k : ℕ} (hk2 : k + 24 ≤ M) :
    Set.InjOn (Nat.cast : ℕ → ZMod M) (Finset.Ico k (k + 24) : Set ℕ) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb
  have hv := congrArg ZMod.val hab
  rw [ZMod.val_natCast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
  exact hv

lemma Ik_card {M : ℕ} [NeZero M] {k : ℕ} (hk2 : k + 24 ≤ M) : (Ik M k).card = 24 := by
  rw [Ik, Finset.card_image_of_injOn (Ik_injOn hk2), Nat.card_Ico]
  omega

lemma Ik_sum {M : ℕ} [NeZero M] {k : ℕ} (hk2 : k + 24 ≤ M) :
    (Ik M k).sum id = ((24 * k + 276 : ℕ) : ZMod M) := by
  rw [Ik, Finset.sum_image (Ik_injOn hk2)]
  change ∑ x ∈ Finset.Ico k (k + 24), (x : ZMod M) = ((24 * k + 276 : ℕ) : ZMod M)
  rw [← Nat.cast_sum]
  congr 1
  rw [Finset.sum_Ico_eq_sum_range]
  have hsub : k + 24 - k = 24 := by omega
  rw [hsub, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hid : (∑ x ∈ Finset.range 24, x) * 2 = 24 * 23 := by
    simpa using Finset.sum_range_id_mul_two 24
  omega

lemma Ik_zero_not_mem {M : ℕ} [NeZero M] {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 24 ≤ M) :
    (0 : ZMod M) ∉ Ik M k := by
  rw [mem_Ik hk2]
  have h0 : (0 : ZMod M).val = 0 := ZMod.val_zero
  omega

lemma cast_modM (M : ℕ) [NeZero M] (m q r : ℕ) (h : m = q * M + r) :
    (m : ZMod M) = (r : ZMod M) := by
  rw [h, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]

lemma I1_sum (M : ℕ) [NeZero M] (hM : M = 53) : (Ik M 1).sum id = (35 : ZMod M) := by
  rw [Ik_sum (by omega)]
  exact cast_modM M (24 * 1 + 276) 5 35 (by omega)

lemma I23_sum (M : ℕ) [NeZero M] (hM : M = 53) : (Ik M 23).sum id = (33 : ZMod M) := by
  rw [Ik_sum (by omega)]
  exact cast_modM M (24 * 23 + 276) 15 33 (by omega)

lemma I22_sum (M : ℕ) [NeZero M] (hM : M = 53) : (Ik M 22).sum id = (9 : ZMod M) := by
  rw [Ik_sum (by omega)]
  exact cast_modM M (24 * 22 + 276) 15 9 (by omega)

lemma exists_zero_not_mem (M t : ℕ) [NeZero M] (hM : M = 53) (ht : t = 25) (r' : ZMod M) :
    ∃ A ∈ Fset M t r', (0 : ZMod M) ∉ A := by
  set z : ZMod M := r' - 35
  have hzlt : z.val < M := ZMod.val_lt z
  have hzr : z + 35 = r' := sub_add_cancel r' 35
  by_cases h1 : 25 ≤ z.val
  · refine ⟨insert z (Ik M 1), ?_, ?_⟩
    · have hznot : z ∉ Ik M 1 := by
        rw [mem_Ik (by omega)]
        omega
      simp only [Fset, Pset, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      refine ⟨?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hznot, Ik_card (by omega), ht]
      · rw [Finset.sum_insert hznot, id, I1_sum M hM, hzr]
    · intro h0
      rcases Finset.mem_insert.mp h0 with h0z | h0I
      · have : z.val = 0 := by rw [← h0z]; exact ZMod.val_zero
        omega
      · exact Ik_zero_not_mem (by omega) (by omega) h0I
  · by_cases h2 : z.val ≤ 20
    · set z1 : ZMod M := z + 2
      have hz1val : z1.val = z.val + 2 := by
        dsimp [z1]
        rw [ZMod.val_add]
        have h2val : (2 : ZMod M).val = 2 := by
          change ((2 : ℕ) : ZMod M).val = 2
          rw [ZMod.val_natCast]
          exact Nat.mod_eq_of_lt (by omega)
        rw [h2val]
        exact Nat.mod_eq_of_lt (by omega)
      have hz1not : z1 ∉ Ik M 23 := by
        rw [mem_Ik (by omega)]
        omega
      have h2_33 : (2 : ZMod M) + 33 = 35 := by
        change ((2 : ℕ) : ZMod M) + ((33 : ℕ) : ZMod M) = ((2 + 33 : ℕ) : ZMod M)
        rw [Nat.cast_add]
      have hz1sum : z1 + 33 = r' := by
        calc z1 + 33 = z + (2 + 33) := by dsimp [z1]; rw [add_assoc]
          _ = z + 35 := by rw [h2_33]
          _ = r' := hzr
      refine ⟨insert z1 (Ik M 23), ?_, ?_⟩
      · simp only [Fset, Pset, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
        refine ⟨?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hz1not, Ik_card (by omega), ht]
        · rw [Finset.sum_insert hz1not, id, I23_sum M hM, hz1sum]
      · intro h0
        rcases Finset.mem_insert.mp h0 with h0z | h0I
        · have : z1.val = 0 := by rw [← h0z]; exact ZMod.val_zero
          omega
        · exact Ik_zero_not_mem (by omega) (by omega) h0I
    · set z2 : ZMod M := z + 26
      have hz2val : z2.val = z.val + 26 := by
        dsimp [z2]
        rw [ZMod.val_add]
        have h26val : (26 : ZMod M).val = 26 := by
          change ((26 : ℕ) : ZMod M).val = 26
          rw [ZMod.val_natCast]
          exact Nat.mod_eq_of_lt (by omega)
        rw [h26val]
        exact Nat.mod_eq_of_lt (by omega)
      have hz2not : z2 ∉ Ik M 22 := by
        rw [mem_Ik (by omega)]
        omega
      have h26_9 : (26 : ZMod M) + 9 = 35 := by
        change ((26 : ℕ) : ZMod M) + ((9 : ℕ) : ZMod M) = ((26 + 9 : ℕ) : ZMod M)
        rw [Nat.cast_add]
      have hz2sum : z2 + 9 = r' := by
        calc z2 + 9 = z + (26 + 9) := by dsimp [z2]; rw [add_assoc]
          _ = z + 35 := by rw [h26_9]
          _ = r' := hzr
      refine ⟨insert z2 (Ik M 22), ?_, ?_⟩
      · simp only [Fset, Pset, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
        refine ⟨?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hz2not, Ik_card (by omega), ht]
        · rw [Finset.sum_insert hz2not, id, I22_sum M hM, hz2sum]
      · intro h0
        rcases Finset.mem_insert.mp h0 with h0z | h0I
        · have : z2.val = 0 := by rw [← h0z]; exact ZMod.val_zero
          omega
        · exact Ik_zero_not_mem (by omega) (by omega) h0I

lemma exists_not_mem (M t : ℕ) [NeZero M] (hM : M = 53) (ht : t = 25) (r x : ZMod M) :
    ∃ A ∈ Fset M t r, x ∉ A := by
  obtain ⟨A0, hA0F, h0⟩ := exists_zero_not_mem M t hM ht (r - (t : ZMod M) * x)
  have hA0c : A0.card = t := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA0F).1).2
  have hA0s : A0.sum id = r - (t : ZMod M) * x := (Finset.mem_filter.mp hA0F).2
  refine ⟨A0.image (· + x), ?_, ?_⟩
  · simp only [Fset, Pset, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    refine ⟨?_, ?_⟩
    · rw [Finset.card_image_of_injective A0 (add_left_injective x), hA0c]
    · rw [Finset.sum_image (fun y _ z _ h => add_left_injective x h)]
      change ∑ y ∈ A0, (y + x) = r
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hA0c]
      change A0.sum id + (t : ZMod M) * x = r
      rw [hA0s, sub_add_cancel]
  · intro hx
    obtain ⟨y, hyA0, hyx⟩ := Finset.mem_image.mp hx
    have hy0 : y = 0 := add_right_cancel (b := x) (by rw [hyx, zero_add])
    exact h0 (hy0 ▸ hyA0)

lemma exists_two_mem_F (M t : ℕ) [NeZero M] (hM : M = 53) (ht : t = 25) (r : ZMod M) :
    ∃ A ∈ Fset M t r, ∃ B ∈ Fset M t r, A ≠ B := by
  obtain ⟨A, hA, _⟩ := exists_not_mem M t hM ht r 0
  have hAc : A.card = t := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).2
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨y, hyA⟩ := hAne
  obtain ⟨B, hB, hyB⟩ := exists_not_mem M t hM ht r y
  refine ⟨A, hA, B, hB, ?_⟩
  intro hEq
  exact hyB (hEq ▸ hyA)

lemma union_card_ge_27 {M t : ℕ} [NeZero M] (ht : t = 25) {r : ZMod M}
    {A B : Finset (ZMod M)} (hA : A ∈ Fset M t r) (hB : B ∈ Fset M t r) (hne : A ≠ B) :
    27 ≤ (A ∪ B).card := by
  have hAc : A.card = t := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).2
  have hBc : B.card = t := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hB).1).2
  have hAs : A.sum id = r := (Finset.mem_filter.mp hA).2
  have hBs : B.sum id = r := (Finset.mem_filter.mp hB).2
  have hle : (A ∩ B).card ≤ t := (Finset.card_le_card Finset.inter_subset_left).trans_eq hAc
  have hne25 : (A ∩ B).card ≠ t := by
    intro h25
    have h1 : A ∩ B = A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have h2 : A ∩ B = B := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hne (h1.symm.trans h2)
  have hne24 : (A ∩ B).card ≠ 24 := by
    intro h24
    have hABc : (A \ B).card = 1 := by
      have h := Finset.card_sdiff_add_card_inter A B
      omega
    have hBAc : (B \ A).card = 1 := by
      have h := Finset.card_sdiff_add_card_inter B A
      rw [Finset.inter_comm] at h
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hABc
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hBAc
    have hsumA : x + (A ∩ B).sum id = r := by
      have h1 := Finset.sum_sdiff (s₁ := A ∩ B) (s₂ := A) (f := id) Finset.inter_subset_left
      rw [Finset.sdiff_inter_self_left, hx, Finset.sum_singleton, hAs] at h1
      exact h1
    have hsumB : y + (A ∩ B).sum id = r := by
      have h1 := Finset.sum_sdiff (s₁ := B ∩ A) (s₂ := B) (f := id) Finset.inter_subset_left
      rw [Finset.sdiff_inter_self_left, hy, Finset.sum_singleton, Finset.inter_comm, hBs] at h1
      exact h1
    have hxy : x = y := add_right_cancel (hsumA.trans hsumB.symm)
    have hxA : x ∈ A \ B := by rw [hx]; exact Finset.mem_singleton_self x
    have hyB : y ∈ B \ A := by rw [hy]; exact Finset.mem_singleton_self y
    rw [Finset.mem_sdiff] at hxA hyB
    exact hxA.2 (hxy ▸ hyB.1)
  have hu := Finset.card_union_add_card_inter A B
  omega

lemma choose_28_25 : Nat.choose 28 25 = 3276 := by
  rw [← Nat.choose_symm (by omega : 25 ≤ 28)]
  change Nat.choose 28 3 = 3276
  have h1 : Nat.choose 28 1 = 28 := Nat.choose_one_right 28
  have h2 : Nat.choose 28 2 * 2 = Nat.choose 28 1 * 27 := Nat.choose_succ_right_eq 28 1
  have h3 : Nat.choose 28 3 * 3 = Nat.choose 28 2 * 26 := Nat.choose_succ_right_eq 28 2
  omega

lemma sum_F_card (M t : ℕ) [NeZero M] :
    ∑ a : ZMod M, (Fset M t a).card = (Pset M t).card := by
  exact (Finset.card_eq_sum_card_fiberwise
    (f := fun A : Finset (ZMod M) => A.sum id)
    (s := Pset M t) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)).symm

lemma sum_lhs (M t : ℕ) [NeZero M] (hM : M = 53) :
    ∑ p : ZMod M × ZMod M, 29 * ((Fset M t p.1).card + (Fset M t p.2).card) =
      3074 * (Pset M t).card := by
  have h1 : ∑ p : ZMod M × ZMod M, (Fset M t p.1).card = M * (Pset M t).card := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
    rw [← Finset.mul_sum, sum_F_card]
  have h2 : ∑ p : ZMod M × ZMod M, (Fset M t p.2).card = M * (Pset M t).card := by
    rw [Fintype.sum_prod_type_right]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
    rw [← Finset.mul_sum, sum_F_card]
  have h3 : 29 * (M * (Pset M t).card + M * (Pset M t).card) = 3074 * (Pset M t).card := by
    set c : ℕ := (Pset M t).card
    rw [hM]
    omega
  calc ∑ p : ZMod M × ZMod M, 29 * ((Fset M t p.1).card + (Fset M t p.2).card)
      = 29 * ∑ p : ZMod M × ZMod M, ((Fset M t p.1).card + (Fset M t p.2).card) := by
          rw [Finset.mul_sum]
    _ = 29 * ((∑ p : ZMod M × ZMod M, (Fset M t p.1).card) +
              (∑ p : ZMod M × ZMod M, (Fset M t p.2).card)) := by
          rw [Finset.sum_add_distrib]
    _ = 29 * (M * (Pset M t).card + M * (Pset M t).card) := by rw [h1, h2]
    _ = 3074 * (Pset M t).card := h3

lemma sum_eCount (M t : ℕ) [NeZero M] (hM : M = 53) (ht : t = 25) :
    ∑ p : ZMod M × ZMod M, eCount M t p.1 p.2 = 3276 * (Pset M t).card := by
  set D : Finset (Finset (ZMod M) × Finset (ZMod M)) :=
    (Pset M t ×ˢ Pset M t).filter (fun q => Disjoint q.1 q.2)
  have hfib : ∑ p : ZMod M × ZMod M, eCount M t p.1 p.2 = D.card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := fun q : Finset (ZMod M) × Finset (ZMod M) => (q.1.sum id, q.2.sum id))
      (s := D) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    rw [h]
    refine Finset.sum_congr rfl ?_
    rintro ⟨a, b⟩ _
    unfold eCount
    congr 1
    ext ⟨A, B⟩
    simp only [D, Fset, Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
    tauto
  rw [hfib]
  have hD : D.card = ∑ q ∈ Pset M t ×ˢ Pset M t, if Disjoint q.1 q.2 then 1 else 0 :=
    Finset.card_filter _ _
  rw [hD, Finset.sum_product]
  have hinner : ∀ A ∈ Pset M t, (∑ B ∈ Pset M t, if Disjoint A B then 1 else 0) = 3276 := by
    intro A hA
    rw [← Finset.card_filter]
    have hfilt : (Pset M t).filter (fun B => Disjoint A B) = (Finset.univ \ A).powersetCard t := by
      ext B
      simp only [Pset, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      constructor
      · rintro ⟨hBc, hdisj⟩
        refine ⟨?_, hBc⟩
        intro x hxB
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, Finset.disjoint_right.mp hdisj hxB⟩
      · rintro ⟨hsub, hBc⟩
        refine ⟨hBc, Finset.disjoint_right.mpr ?_⟩
        intro x hxB
        exact (Finset.mem_sdiff.mp (hsub hxB)).2
    rw [hfilt, Finset.card_powersetCard]
    have hAc : A.card = t := (Finset.mem_powersetCard.mp hA).2
    have hsc : (Finset.univ \ A).card = 28 := by
      have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
      have huc : (Finset.univ : Finset (ZMod M)).card = M := ZMod.card M
      omega
    rw [hsc, ht, choose_28_25]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_comm]

lemma exists_good_pair (M t : ℕ) [NeZero M] (hM : M = 53) (ht : t = 25) :
    ∃ a b : ZMod M, 29 * ((Fset M t a).card + (Fset M t b).card) < eCount M t a b := by
  have hPpos : 0 < (Pset M t).card := by
    obtain ⟨A, hA, _⟩ := exists_not_mem M t hM ht 0 0
    exact Finset.card_pos.mpr ⟨A, (Finset.mem_filter.mp hA).1⟩
  have hlt : ∑ p : ZMod M × ZMod M, 29 * ((Fset M t p.1).card + (Fset M t p.2).card) <
      ∑ p : ZMod M × ZMod M, eCount M t p.1 p.2 := by
    rw [sum_lhs M t hM, sum_eCount M t hM ht]
    omega
  by_contra hall
  have hle : ∑ p : ZMod M × ZMod M, eCount M t p.1 p.2 ≤
      ∑ p : ZMod M × ZMod M, 29 * ((Fset M t p.1).card + (Fset M t p.2).card) := by
    refine Finset.sum_le_sum fun p _ => ?_
    exact Nat.le_of_not_lt fun h => hall ⟨p.1, p.2, h⟩
  omega

abbrev V (M t : ℕ) [NeZero M] (a b : ZMod M) :=
  {A : Finset (ZMod M) // A ∈ Fset M t a} ⊕ {B : Finset (ZMod M) // B ∈ Fset M t b}

def setOfV {M t : ℕ} [NeZero M] {a b : ZMod M} : V M t a b → Finset (ZMod M) :=
  Sum.elim Subtype.val Subtype.val

lemma card_setOfV {M t : ℕ} [NeZero M] {a b : ZMod M} (u : V M t a b) :
    (setOfV u).card = t := by
  cases u with
  | inl A => exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp A.2).1).2
  | inr B => exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp B.2).1).2

lemma union_card_ge_27_V {M t : ℕ} [NeZero M] (ht : t = 25) {a b : ZMod M} {u v : V M t a b}
    (hsame : u.isRight = v.isRight) (hne : u ≠ v) : 27 ≤ (setOfV u ∪ setOfV v).card := by
  cases u with
  | inl A1 =>
    cases v with
    | inl A2 =>
      have hne' : A1.1 ≠ A2.1 := fun h => hne (congrArg Sum.inl (Subtype.ext h))
      exact union_card_ge_27 ht A1.2 A2.2 hne'
    | inr B2 =>
      simp at hsame
  | inr B1 =>
    cases v with
    | inl A2 =>
      simp at hsame
    | inr B2 =>
      have hne' : B1.1 ≠ B2.1 := fun h => hne (congrArg Sum.inr (Subtype.ext h))
      exact union_card_ge_27 ht B1.2 B2.2 hne'

lemma card_add_two_le_of_two_not_mem {n : ℕ} {S : Finset (Fin n)} {v1 v2 : Fin n}
    (hne : v1 ≠ v2) (h1 : v1 ∉ S) (h2 : v2 ∉ S) : S.card + 2 ≤ n := by
  have hdisj : Disjoint S ({v1, v2} : Finset (Fin n)) := by
    rw [Finset.disjoint_right]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h1
    · exact h2
  have hpair : ({v1, v2} : Finset (Fin n)).card = 2 := Finset.card_pair hne
  have hu : (S ∪ {v1, v2}).card = S.card + 2 := by
    rw [Finset.card_union_of_disjoint hdisj, hpair]
  have hle : (S ∪ {v1, v2}).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
  rw [Fintype.card_fin] at hle
  omega

lemma bool_eq_of_ne_ne {x y z : Bool} (h1 : x ≠ y) (h2 : y ≠ z) : x = z := by
  cases x <;> cases y <;> cases z <;> simp_all

lemma refute_from_params (M t : ℕ) [NeZero M] (hM : M = 53) (ht : t = 25) :
    ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card)) := by
  classical
  intro hall
  obtain ⟨a, b, hab⟩ := exists_good_pair M t hM ht
  let n : ℕ := Fintype.card (V M t a b)
  have hn : n = (Fset M t a).card + (Fset M t b).card := by
    dsimp [n, V]
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  let e : V M t a b ≃ Fin n := Fintype.equivFin (V M t a b)
  let side : Fin n → Bool := fun v => (e.symm v).isRight
  let G : SimpleGraph (Fin n) := {
    Adj := fun u v => side u ≠ side v ∧ Disjoint (setOfV (e.symm u)) (setOfV (e.symm v))
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩
  }
  let I : Fin 55 → Finset (Fin n) := fun j =>
    if j.val = 0 then Finset.univ.filter (fun v => side v = false)
    else if j.val = 1 then Finset.univ.filter (fun v => side v = true)
    else Finset.univ.filter (fun v => ((j.val - 2 : ℕ) : ZMod M) ∈ setOfV (e.symm v))
  have hI0 : ∀ (j : Fin 55), j.val = 0 → ∀ v : Fin n, v ∈ I j ↔ side v = false := by
    intro j hj v
    dsimp only [I]
    split_ifs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hI1 : ∀ (j : Fin 55), j.val = 1 → ∀ v : Fin n, v ∈ I j ↔ side v = true := by
    intro j hj v
    dsimp only [I]
    split_ifs
    · omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hI2 : ∀ (j : Fin 55), 2 ≤ j.val → ∀ v : Fin n,
      v ∈ I j ↔ ((j.val - 2 : ℕ) : ZMod M) ∈ setOfV (e.symm v) := by
    intro j hj v
    dsimp only [I]
    split_ifs
    · omega
    · omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : ∀ u v : Fin n, G.Adj u v → side u ≠ side v := fun _ _ h => h.1
  have h2 : ∀ v1 v2 v3 v4 : Fin n, v1 ≠ v3 → v2 ≠ v4 →
      ¬ (G.Adj v1 v2 ∧ G.Adj v2 v3 ∧ G.Adj v3 v4 ∧ G.Adj v4 v1) := by
    intro v1 v2 v3 v4 h13 h24 ⟨h12, h23, h34, h41⟩
    have hu13 : e.symm v1 ≠ e.symm v3 := fun h => h13 (e.symm.injective h)
    have hu24 : e.symm v2 ≠ e.symm v4 := fun h => h24 (e.symm.injective h)
    have hs13 : (e.symm v1).isRight = (e.symm v3).isRight :=
      bool_eq_of_ne_ne h12.1 h23.1
    have hs24 : (e.symm v2).isRight = (e.symm v4).isRight :=
      bool_eq_of_ne_ne h23.1 h34.1
    have hc13 : 27 ≤ (setOfV (e.symm v1) ∪ setOfV (e.symm v3)).card :=
      union_card_ge_27_V ht hs13 hu13
    have hc24 : 27 ≤ (setOfV (e.symm v2) ∪ setOfV (e.symm v4)).card :=
      union_card_ge_27_V ht hs24 hu24
    have hdisj : Disjoint (setOfV (e.symm v1) ∪ setOfV (e.symm v3))
        (setOfV (e.symm v2) ∪ setOfV (e.symm v4)) := by
      rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
      exact ⟨⟨h12.2, h41.2.symm⟩, ⟨h23.2.symm, h34.2⟩⟩
    have hunion : ((setOfV (e.symm v1) ∪ setOfV (e.symm v3)) ∪
        (setOfV (e.symm v2) ∪ setOfV (e.symm v4))).card ≤ M := by
      calc ((setOfV (e.symm v1) ∪ setOfV (e.symm v3)) ∪
            (setOfV (e.symm v2) ∪ setOfV (e.symm v4))).card
          ≤ Fintype.card (ZMod M) := Finset.card_le_univ _
        _ = M := ZMod.card M
    rw [Finset.card_union_of_disjoint hdisj] at hunion
    omega
  have h3 : 2 ≤ (55 : ℕ) := by omega
  have h4 : ∀ j : Fin 55, ∀ u ∈ I j, ∀ v ∈ I j, ¬ G.Adj u v := by
    intro j u hu v hv hadj
    by_cases hj0 : j.val = 0
    · rw [hI0 j hj0] at hu hv
      exact hadj.1 (hu.trans hv.symm)
    · by_cases hj1 : j.val = 1
      · rw [hI1 j hj1] at hu hv
        exact hadj.1 (hu.trans hv.symm)
      · rw [hI2 j (by omega)] at hu hv
        exact Finset.disjoint_left.mp hadj.2 hu hv
  have h5 : ∀ v : Fin n, ∃ j : Fin 55, v ∈ I j := by
    intro v
    cases hv : side v
    · exact ⟨⟨0, by omega⟩, (hI0 ⟨0, by omega⟩ rfl v).mpr hv⟩
    · exact ⟨⟨1, by omega⟩, (hI1 ⟨1, by omega⟩ rfl v).mpr hv⟩
  have h6 : ∀ v : Fin n, ∃ j : Fin 55, v ∉ I j := by
    intro v
    cases hv : side v
    · refine ⟨⟨1, by omega⟩, ?_⟩
      rw [hI1 ⟨1, by omega⟩ rfl, hv]
      decide
    · refine ⟨⟨0, by omega⟩, ?_⟩
      rw [hI0 ⟨0, by omega⟩ rfl, hv]
      decide
  have h7 : ∀ j : Fin 55, (I j).card + 2 ≤ n := by
    intro j
    by_cases hj0 : j.val = 0
    · obtain ⟨B1, hB1, B2, hB2, hneB⟩ := exists_two_mem_F M t hM ht b
      let v1 := e (.inr ⟨B1, hB1⟩)
      let v2 := e (.inr ⟨B2, hB2⟩)
      have hne : v1 ≠ v2 := by
        intro h
        have h' := Sum.inr.inj (e.injective h)
        exact hneB (congrArg Subtype.val h')
      refine card_add_two_le_of_two_not_mem hne ?_ ?_
      · rw [hI0 j hj0]
        simp [v1, side]
      · rw [hI0 j hj0]
        simp [v2, side]
    · by_cases hj1 : j.val = 1
      · obtain ⟨A1, hA1, A2, hA2, hneA⟩ := exists_two_mem_F M t hM ht a
        let v1 := e (.inl ⟨A1, hA1⟩)
        let v2 := e (.inl ⟨A2, hA2⟩)
        have hne : v1 ≠ v2 := by
          intro h
          have h' := Sum.inl.inj (e.injective h)
          exact hneA (congrArg Subtype.val h')
        refine card_add_two_le_of_two_not_mem hne ?_ ?_
        · rw [hI1 j hj1]
          simp [v1, side]
        · rw [hI1 j hj1]
          simp [v2, side]
      · have hj2 : 2 ≤ j.val := by omega
        set x : ZMod M := ((j.val - 2 : ℕ) : ZMod M)
        obtain ⟨A, hA, hxA⟩ := exists_not_mem M t hM ht a x
        obtain ⟨B, hB, hxB⟩ := exists_not_mem M t hM ht b x
        let v1 := e (.inl ⟨A, hA⟩)
        let v2 := e (.inr ⟨B, hB⟩)
        have hne : v1 ≠ v2 := fun h => nomatch e.injective h
        refine card_add_two_le_of_two_not_mem hne ?_ ?_
        · rw [hI2 j hj2]
          simpa [v1, setOfV, x] using hxA
        · rw [hI2 j hj2]
          simpa [v2, setOfV, x] using hxB
  have h8 : ∀ u v : Fin n, u ≠ v → ¬ G.Adj u v → ∃ j : Fin 55, u ∈ I j ∧ v ∈ I j := by
    intro u v _ hna
    by_cases hs : side u = side v
    · cases hu : side u
      · exact ⟨⟨0, by omega⟩, (hI0 ⟨0, by omega⟩ rfl u).mpr hu,
          (hI0 ⟨0, by omega⟩ rfl v).mpr (hs.symm.trans hu)⟩
      · exact ⟨⟨1, by omega⟩, (hI1 ⟨1, by omega⟩ rfl u).mpr hu,
          (hI1 ⟨1, by omega⟩ rfl v).mpr (hs.symm.trans hu)⟩
    · have hnd : ¬ Disjoint (setOfV (e.symm u)) (setOfV (e.symm v)) := fun hd => hna ⟨hs, hd⟩
      obtain ⟨x, hxu, hxv⟩ := Finset.not_disjoint_iff.mp hnd
      have hxlt : x.val < M := ZMod.val_lt x
      let j : Fin 55 := ⟨x.val + 2, by omega⟩
      have hj2 : 2 ≤ j.val := by dsimp [j]; omega
      have hjx : ((j.val - 2 : ℕ) : ZMod M) = x := by
        have hsub : j.val - 2 = x.val := by dsimp [j]; omega
        rw [hsub, ZMod.natCast_zmod_val]
      refine ⟨j, ?_, ?_⟩
      · rw [hI2 j hj2, hjx]; exact hxu
      · rw [hI2 j hj2, hjx]; exact hxv
  obtain ⟨T, _, hT⟩ := hall n 55 G side I h1 h2 h3 h4 h5 h6 h7 h8
  have hrhs : ∑ j : Fin 55, (n - (I j).card) = 29 * n := by
    have hstep1 : ∀ j : Fin 55, n - (I j).card = ∑ v : Fin n, if v ∉ I j then 1 else 0 := by
      intro j
      rw [← Finset.card_filter]
      have hcompl : Finset.univ.filter (fun v : Fin n => v ∉ I j) = Finset.univ \ I j := by
        ext v
        simp
      rw [hcompl]
      have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (I j))
      have huniv : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
      omega
    calc ∑ j : Fin 55, (n - (I j).card)
        = ∑ j : Fin 55, ∑ v : Fin n, if v ∉ I j then 1 else 0 := by
            refine Finset.sum_congr rfl fun j _ => hstep1 j
      _ = ∑ v : Fin n, ∑ j : Fin 55, if v ∉ I j then 1 else 0 := Finset.sum_comm
      _ = ∑ v : Fin n, 29 := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [← Finset.card_filter]
            let S01 : Finset (Fin 55) := Finset.univ.filter (fun j : Fin 55 => j.val < 2 ∧ v ∉ I j)
            let S2 : Finset (Fin 55) := Finset.univ.filter (fun j : Fin 55 => 2 ≤ j.val ∧ v ∉ I j)
            have hunion : Finset.univ.filter (fun j : Fin 55 => v ∉ I j) = S01 ∪ S2 := by
              ext j
              simp only [S01, S2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro h
                by_cases hj : j.val < 2
                · exact Or.inl ⟨hj, h⟩
                · exact Or.inr ⟨by omega, h⟩
              · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
            have hdisj : Disjoint S01 S2 := by
              rw [Finset.disjoint_left]
              intro j h1j h2j
              simp only [S01, S2, Finset.mem_filter, Finset.mem_univ, true_and] at h1j h2j
              omega
            rw [hunion, Finset.card_union_of_disjoint hdisj]
            have hS01 : S01.card = 1 := by
              cases hv : side v
              · have heq : S01 = {⟨1, by omega⟩} := by
                  ext j
                  simp only [S01, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
                  constructor
                  · rintro ⟨hjlt, hvnot⟩
                    by_cases hj0 : j.val = 0
                    · exact absurd ((hI0 j hj0 v).mpr hv) hvnot
                    · exact Fin.ext (show j.val = 1 by omega)
                  · rintro rfl
                    refine ⟨show 1 < 2 by omega, ?_⟩
                    rw [hI1 ⟨1, by omega⟩ rfl, hv]
                    decide
                rw [heq, Finset.card_singleton]
              · have heq : S01 = {⟨0, by omega⟩} := by
                  ext j
                  simp only [S01, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
                  constructor
                  · rintro ⟨hjlt, hvnot⟩
                    by_cases hj0 : j.val = 0
                    · exact Fin.ext hj0
                    · exact absurd ((hI1 j (by omega) v).mpr hv) hvnot
                  · rintro rfl
                    refine ⟨show 0 < 2 by omega, ?_⟩
                    rw [hI0 ⟨0, by omega⟩ rfl, hv]
                    decide
                rw [heq, Finset.card_singleton]
            have hS2 : S2.card = 28 := by
              have hbij : S2.card = (Finset.univ \ setOfV (e.symm v)).card := by
                refine Finset.card_bij
                  (fun j _ => ((j.val - 2 : ℕ) : ZMod M))
                  ?_ ?_ ?_
                · intro j hj
                  simp only [S2, Finset.mem_filter, Finset.mem_univ, true_and] at hj
                  rw [Finset.mem_sdiff]
                  refine ⟨Finset.mem_univ _, ?_⟩
                  intro hx
                  exact hj.2 ((hI2 j hj.1 v).mpr hx)
                · intro j1 hj1 j2 hj2 heq
                  simp only [S2, Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
                  have hval1 : (((j1.val - 2 : ℕ) : ZMod M)).val = j1.val - 2 := by
                    rw [ZMod.val_natCast]
                    exact Nat.mod_eq_of_lt (by omega)
                  have hval2 : (((j2.val - 2 : ℕ) : ZMod M)).val = j2.val - 2 := by
                    rw [ZMod.val_natCast]
                    exact Nat.mod_eq_of_lt (by omega)
                  have hsub : j1.val - 2 = j2.val - 2 := by
                    rw [← hval1, ← hval2, heq]
                  exact Fin.ext (by omega)
                · intro x hx
                  rw [Finset.mem_sdiff] at hx
                  have hxlt : x.val < M := ZMod.val_lt x
                  let j : Fin 55 := ⟨x.val + 2, by omega⟩
                  have hj2 : 2 ≤ j.val := by dsimp [j]; omega
                  have hjx : ((j.val - 2 : ℕ) : ZMod M) = x := by
                    have hsub : j.val - 2 = x.val := by dsimp [j]; omega
                    rw [hsub, ZMod.natCast_zmod_val]
                  refine ⟨j, ?_, hjx⟩
                  simp only [S2, Finset.mem_filter, Finset.mem_univ, true_and]
                  refine ⟨hj2, ?_⟩
                  rw [hI2 j hj2, hjx]
                  exact hx.2
              rw [hbij]
              have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (setOfV (e.symm v)))
              have huc : (Finset.univ : Finset (ZMod M)).card = M := ZMod.card M
              have hvc : (setOfV (e.symm v)).card = t := card_setOfV (e.symm v)
              omega
            rw [hS01, hS2]
      _ = 29 * n := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
  have hedge : eCount M t a b ≤ G.edgeFinset.card := by
    let S' : Finset ({A : Finset (ZMod M) // A ∈ Fset M t a} × {B : Finset (ZMod M) // B ∈ Fset M t b}) :=
      Finset.univ.filter (fun p => Disjoint p.1.1 p.2.1)
    have hS' : eCount M t a b = S'.card := by
      symm
      refine Finset.card_bij (fun p _ => (p.1.1, p.2.1)) ?_ ?_ ?_
      · intro p hp
        simp only [S', Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨p.1.2, p.2.2⟩, hp⟩
      · intro p1 _ p2 _ heq
        simp only [Prod.mk.injEq] at heq
        exact Prod.ext (Subtype.ext heq.1) (Subtype.ext heq.2)
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_product] at hq
        refine ⟨(⟨q.1, hq.1.1⟩, ⟨q.2, hq.1.2⟩), ?_, rfl⟩
        simp only [S', Finset.mem_filter, Finset.mem_univ, true_and]
        exact hq.2
    rw [hS']
    refine Finset.card_le_card_of_injOn
      (fun p => s(e (.inl p.1), e (.inr p.2))) ?_ ?_
    · intro p hp
      simp only [S', Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [Finset.mem_coe, SimpleGraph.mem_edgeFinset]
      change G.Adj (e (.inl p.1)) (e (.inr p.2))
      refine ⟨?_, ?_⟩
      · simp [side]
      · simpa [setOfV] using hp
    · intro p1 _ p2 _ heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hL, hR⟩ | ⟨hLR, _⟩
      · exact Prod.ext (Sum.inl.inj (e.injective hL)) (Sum.inr.inj (e.injective hR))
      · exact nomatch e.injective hLR
  omega

end PEqualNP.Outside.L_meta_3577

theorem PEqualNP.Outside.L_meta_3577 : ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card)) :=
  PEqualNP.Outside.L_meta_3577.refute_from_params 53 25 rfl rfl
