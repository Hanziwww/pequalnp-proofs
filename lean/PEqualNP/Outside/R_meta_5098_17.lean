import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_5098_17
    (hDup0 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C →
        C.size = 14 →
        C.output = 23 →
        (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length ≤ 1) →
        (∃ (i1 i2 : Fin C.gates.length), i1 < i2 ∧ 3 ≤ i1.val ∧ i1.val ≤ 6 ∧ i2.val < 13 ∧
          (C.gates.get i1).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          (C.gates.get i2).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = i1 ∨ i = i2) →
        have flat : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates
        have comp : ℕ → Prop := fun m =>
          C.eval ((List.ofFn fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 2]) =
            [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320].any fun e => m &&& e == e
        (∀ w < 23, w ∈ flat) →
        {w ∈ Finset.range 23 | 2 ≤ List.count w flat}.card ≤ 3 →
        (∀ m < 512, comp m) →
        2 ≤ List.count 0 flat ∧ List.count 0 flat ≤ 4 ∧
          (Finset.range 23).sum (fun w => List.count w flat - 1) ≤ 3 →
        False)
    (hDup1 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C →
        C.size = 14 →
        C.output = 23 →
        (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length ≤ 1) →
        (∃ (i1 i2 : Fin C.gates.length), i1 < i2 ∧ 3 ≤ i1.val ∧ i1.val ≤ 6 ∧ i2.val < 13 ∧
          (C.gates.get i1).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          (C.gates.get i2).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = i1 ∨ i = i2) →
        have flat : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates
        have comp : ℕ → Prop := fun m =>
          C.eval ((List.ofFn fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 2]) =
            [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320].any fun e => m &&& e == e
        (∀ w < 23, w ∈ flat) →
        {w ∈ Finset.range 23 | 2 ≤ List.count w flat}.card ≤ 3 →
        (∀ m < 512, comp m) →
        2 ≤ List.count 1 flat ∧ List.count 1 flat ≤ 4 ∧
          (Finset.range 23).sum (fun w => List.count w flat - 1) ≤ 3 →
        False)
    (hDup4 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C →
        C.size = 14 →
        C.output = 23 →
        (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length ≤ 1) →
        (∃ (i1 i2 : Fin C.gates.length), i1 < i2 ∧ 3 ≤ i1.val ∧ i1.val ≤ 6 ∧ i2.val < 13 ∧
          (C.gates.get i1).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          (C.gates.get i2).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = i1 ∨ i = i2) →
        have flat : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates
        have comp : ℕ → Prop := fun m =>
          C.eval ((List.ofFn fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 2]) =
            [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320].any fun e => m &&& e == e
        (∀ w < 23, w ∈ flat) →
        {w ∈ Finset.range 23 | 2 ≤ List.count w flat}.card ≤ 3 →
        (∀ m < 512, comp m) →
        2 ≤ List.count 4 flat ∧ List.count 4 flat ≤ 4 ∧
          (Finset.range 23).sum (fun w => List.count w flat - 1) ≤ 3 →
        False)
    (hDup8 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C →
        C.size = 14 →
        C.output = 23 →
        (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length ≤ 1) →
        (∃ (i1 i2 : Fin C.gates.length), i1 < i2 ∧ 3 ≤ i1.val ∧ i1.val ≤ 6 ∧ i2.val < 13 ∧
          (C.gates.get i1).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          (C.gates.get i2).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = i1 ∨ i = i2) →
        have flat : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates
        have comp : ℕ → Prop := fun m =>
          C.eval ((List.ofFn fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 2]) =
            [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320].any fun e => m &&& e == e
        (∀ w < 23, w ∈ flat) →
        {w ∈ Finset.range 23 | 2 ≤ List.count w flat}.card ≤ 3 →
        (∀ m < 512, comp m) →
        2 ≤ List.count 8 flat ∧ List.count 8 flat ≤ 4 ∧
          (Finset.range 23).sum (fun w => List.count w flat - 1) ≤ 3 →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size = (14 : ℕ) →       x1.output = (23 : ℕ) →         (∀ x5 ∈ x1.gates, x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length ≤ (1 : ℕ)) →           (∃ (x6 : Fin x1.gates.length) (x7 : Fin x1.gates.length), x6 < x7 ∧ (3 : ℕ) ≤ ↑x6 ∧ ↑x6 ≤ (6 : ℕ) ∧ ↑x7 < (13 : ℕ) ∧ (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x8 : Fin x1.gates.length), (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not → x8 = x6 ∨ x8 = x7) →             have x7 : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates;             have x8 : ℕ → Prop := fun (x8 : ℕ) => x1.eval ((List.ofFn fun (x9 : Fin (9 : ℕ)) => x8.testBit ↑x9) ++ [x8.testBit (0 : ℕ) || x8.testBit (2 : ℕ)]) = [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)].any fun (x9 : ℕ) => x8 &&& x9 == x9;             (∀ x9 < (23 : ℕ), x9 ∈ x7) → {x10 ∈ Finset.range (23 : ℕ) | (2 : ℕ) ≤ List.count x10 x7}.card ≤ (3 : ℕ) → (∀ x11 < (512 : ℕ), x8 x11) → ∀ x12 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (8 : ℕ)], List.count x12 x7 ≤ (1 : ℕ) := by
  intro C hfan hsz hout hnot1 hnot2 flat comp hall hdup3 hcomp w0 hw0
  by_contra hgt1
  have hge2 : 2 ≤ List.count w0 flat := by omega
  have excess_bound : ∀ (D : Circuit),
      FanInTwo D → D.size = 14 →
      (∀ g ∈ D.gates, g.op = GateOp.not → g.inputs.length ≤ 1) →
      (∃ (i1 i2 : Fin D.gates.length), i1 < i2 ∧
        (D.gates.get i1).op = GateOp.not ∧ (D.gates.get i2).op = GateOp.not) →
      (∀ w < 23, w ∈ D.gates.flatMap Gate.inputs) →
      (Finset.range 23).sum (fun w => List.count w (D.gates.flatMap Gate.inputs) - 1) ≤ 3 := by
    intro D hDfan hDsz hDnot1 hDnot2 hDall
    obtain ⟨i1, i2, hlt12, h1not, h2not⟩ := hDnot2
    have hflat_len : ∀ l : List Gate, (l.flatMap Gate.inputs).length = ∑ i : Fin l.length, (l.get i).inputs.length := by
      intro l
      induction l with
      | nil => simp
      | cons g rest ih =>
        rw [List.flatMap_cons, List.length_append, ih]
        change g.inputs.length + ∑ i : Fin rest.length, (rest.get i).inputs.length =
          ∑ i : Fin (rest.length + 1), ((g :: rest).get i).inputs.length
        rw [Fin.sum_univ_succ]
        rfl
    have hsum_gates : ∑ i : Fin D.gates.length, (D.gates.get i).inputs.length ≤ 26 := by
      let T : Finset (Fin D.gates.length) := {i1, i2}
      have hne12 : i1 ≠ i2 := ne_of_lt hlt12
      have hTcard : T.card = 2 := Finset.card_pair hne12
      have hsplit : ∑ i : Fin D.gates.length, (D.gates.get i).inputs.length =
          (∑ i ∈ T, (D.gates.get i).inputs.length) + (∑ i ∈ Finset.univ \ T, (D.gates.get i).inputs.length) := by
        rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ T)]
      have hT_le : ∑ i ∈ T, (D.gates.get i).inputs.length ≤ 2 := by
        calc ∑ i ∈ T, (D.gates.get i).inputs.length
            ≤ ∑ _i ∈ T, 1 := by
              apply Finset.sum_le_sum
              intro i hi
              rcases Finset.mem_insert.mp hi with rfl | hi2
              · exact hDnot1 (D.gates.get i) (List.get_mem _ _) h1not
              · rw [Finset.mem_singleton.mp hi2]
                exact hDnot1 (D.gates.get i2) (List.get_mem _ _) h2not
          _ = T.card := by simp
          _ = 2 := hTcard
      have hrest_le : ∑ i ∈ Finset.univ \ T, (D.gates.get i).inputs.length ≤ 24 := by
        have hrcard : (Finset.univ \ T).card = 12 := by
          rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hTcard]
          change D.gates.length = 14 at hDsz
          omega
        calc ∑ i ∈ Finset.univ \ T, (D.gates.get i).inputs.length
            ≤ ∑ _i ∈ Finset.univ \ T, 2 := by
              apply Finset.sum_le_sum
              intro i _
              exact (hDfan (D.gates.get i) (List.get_mem _ _)).2
          _ = (Finset.univ \ T).card * 2 := by simp
          _ = 24 := by rw [hrcard]
      omega
    have hlen26 : (D.gates.flatMap Gate.inputs).length ≤ 26 := by
      rw [hflat_len]; exact hsum_gates
    have hcount_sum_le : ∀ l : List ℕ, (Finset.range 23).sum (fun w => List.count w l) ≤ l.length := by
      intro l
      induction l with
      | nil => simp
      | cons a rest ih =>
        have hstep : (Finset.range 23).sum (fun w => List.count w (a :: rest)) =
            (Finset.range 23).sum (fun w => List.count w rest) +
            (Finset.range 23).sum (fun w => if a = w then 1 else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro w _
          rw [List.count_cons]
          by_cases haw : a = w
          · subst haw; simp
          · have hne : (a == w) = false := beq_false_of_ne haw
            simp [haw, hne]
        have h1 : (Finset.range 23).sum (fun w => if a = w then 1 else 0) ≤ 1 := by
          rw [Finset.sum_ite_eq]
          split_ifs <;> omega
        rw [hstep, List.length_cons]
        omega
    have hsum_all : (Finset.range 23).sum (fun w => List.count w (D.gates.flatMap Gate.inputs)) ≤ 26 :=
      le_trans (hcount_sum_le _) hlen26
    have hsum_shift : (Finset.range 23).sum (fun w => List.count w (D.gates.flatMap Gate.inputs) - 1) + 23 =
        (Finset.range 23).sum (fun w => List.count w (D.gates.flatMap Gate.inputs)) := by
      calc (Finset.range 23).sum (fun w => List.count w (D.gates.flatMap Gate.inputs) - 1) + 23
          = (Finset.range 23).sum (fun w => List.count w (D.gates.flatMap Gate.inputs) - 1) +
              (Finset.range 23).sum (fun _ => 1) := by simp
        _ = (Finset.range 23).sum (fun w => (List.count w (D.gates.flatMap Gate.inputs) - 1) + 1) :=
              (Finset.sum_add_distrib).symm
        _ = (Finset.range 23).sum (fun w => List.count w (D.gates.flatMap Gate.inputs)) := by
              apply Finset.sum_congr rfl
              intro w hw
              have hwlt : w < 23 := Finset.mem_range.mp hw
              have hpos : 0 < List.count w (D.gates.flatMap Gate.inputs) :=
                List.count_pos_iff.mpr (hDall w hwlt)
              omega
    omega
  have hC_excess : (Finset.range 23).sum (fun w => List.count w flat - 1) ≤ 3 := by
    obtain ⟨i1, i2, hlt12, _, _, _, h1not, h2not, _⟩ := hnot2
    exact excess_bound C hfan hsz hnot1 ⟨i1, i2, hlt12, h1not, h2not⟩ hall
  have hcount_le4 : ∀ w < 23, List.count w flat ≤ 4 := by
    intro w hw
    have hle := Finset.single_le_sum (f := fun u => List.count u flat - 1) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hw)
    omega
  let ρ : ℕ → ℕ := fun w => ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ).getD w w
  have hρ_lt9 : ∀ i : Fin 9, ρ i.val < 9 := by dsimp only [ρ]; decide
  have hρ_inv9 : ∀ i : Fin 9, ρ (ρ i.val) = i.val := by dsimp only [ρ]; decide
  have hρ_ge9 (w : ℕ) (hw : 9 ≤ w) : ρ w = w := by
    dsimp only [ρ]
    exact List.getD_eq_default [2, 1, 0, 5, 7, 3, 6, 4, 8] w (n := w) hw
  have hρ_inv (w : ℕ) : ρ (ρ w) = w := by
    by_cases hw : w < 9
    · exact hρ_inv9 ⟨w, hw⟩
    · rw [hρ_ge9 w (by omega), hρ_ge9 w (by omega)]
  have hρ_inj : Function.Injective ρ := fun a b h => by
    have := congrArg ρ h
    rwa [hρ_inv a, hρ_inv b] at this
  have hρ_lt23 (w : ℕ) (hw : w < 23) : ρ w < 23 := by
    by_cases h9 : w < 9
    · have : ρ w < 9 := hρ_lt9 ⟨w, h9⟩; omega
    · rw [hρ_ge9 w (by omega)]; exact hw
  let b0 : Bool → ℕ → ℕ := fun b r => (if b then 1 else 0) + 2 * r
  have hb0_bit (b : Bool) (r : ℕ) :
      (b0 b r).testBit 0 = b ∧ ∀ k, (b0 b r).testBit (k + 1) = r.testBit k := by
    dsimp only [b0]
    cases b <;> constructor
    · simp [Nat.testBit_zero]
    · intro k; simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.testBit_succ]; congr 1; omega
    · simp [Nat.testBit_zero]
    · intro k; simp only [↓reduceIte, Nat.testBit_succ]; congr 1; omega
  have hb0_lt (b : Bool) (r N : ℕ) (hr : r < N) : b0 b r < 2 * N := by
    dsimp only [b0]; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  let permMask : ℕ → ℕ := fun m =>
    b0 (m.testBit 2) (b0 (m.testBit 1) (b0 (m.testBit 0)
      (b0 (m.testBit 5) (b0 (m.testBit 7) (b0 (m.testBit 3)
        (b0 (m.testBit 6) (b0 (m.testBit 4) (b0 (m.testBit 8) 0))))))))
  have hpm_lt (m : ℕ) : permMask m < 512 := by
    dsimp only [permMask]
    have h8 : b0 (m.testBit 8) 0 < 2 := hb0_lt _ 0 1 (by omega)
    have h7 := hb0_lt (m.testBit 4) _ 2 h8
    have h6 := hb0_lt (m.testBit 6) _ 4 h7
    have h5 := hb0_lt (m.testBit 3) _ 8 h6
    have h4 := hb0_lt (m.testBit 7) _ 16 h5
    have h3 := hb0_lt (m.testBit 5) _ 32 h4
    have h2 := hb0_lt (m.testBit 0) _ 64 h3
    have h1 := hb0_lt (m.testBit 1) _ 128 h2
    exact hb0_lt (m.testBit 2) _ 256 h1
  have hpm_bit (m : ℕ) (i : Fin 9) : (permMask m).testBit i.val = m.testBit (ρ i.val) := by
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by
      have := i.isLt; omega
    dsimp only [permMask]
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hb0_bit _ _).1
    · exact ((hb0_bit _ _).2 0).trans (hb0_bit _ _).1
    · exact ((hb0_bit _ _).2 1).trans (((hb0_bit _ _).2 0).trans (hb0_bit _ _).1)
    · exact ((hb0_bit _ _).2 2).trans (((hb0_bit _ _).2 1).trans (((hb0_bit _ _).2 0).trans (hb0_bit _ _).1))
    · exact ((hb0_bit _ _).2 3).trans (((hb0_bit _ _).2 2).trans (((hb0_bit _ _).2 1).trans (((hb0_bit _ _).2 0).trans (hb0_bit _ _).1)))
    · exact ((hb0_bit _ _).2 4).trans (((hb0_bit _ _).2 3).trans (((hb0_bit _ _).2 2).trans (((hb0_bit _ _).2 1).trans (((hb0_bit _ _).2 0).trans (hb0_bit _ _).1))))
    · exact ((hb0_bit _ _).2 5).trans (((hb0_bit _ _).2 4).trans (((hb0_bit _ _).2 3).trans (((hb0_bit _ _).2 2).trans (((hb0_bit _ _).2 1).trans (((hb0_bit _ _).2 0).trans (hb0_bit _ _).1)))))
    · exact ((hb0_bit _ _).2 6).trans (((hb0_bit _ _).2 5).trans (((hb0_bit _ _).2 4).trans (((hb0_bit _ _).2 3).trans (((hb0_bit _ _).2 2).trans (((hb0_bit _ _).2 1).trans (((hb0_bit _ _).2 0).trans (hb0_bit _ _).1))))))
    · exact ((hb0_bit _ _).2 7).trans (((hb0_bit _ _).2 6).trans (((hb0_bit _ _).2 5).trans (((hb0_bit _ _).2 4).trans (((hb0_bit _ _).2 3).trans (((hb0_bit _ _).2 2).trans (((hb0_bit _ _).2 1).trans (((hb0_bit _ _).2 0).trans (hb0_bit _ _).1)))))))
  have hpm_or (m : ℕ) :
      ((permMask m).testBit 0 || (permMask m).testBit 2) = (m.testBit 0 || m.testBit 2) := by
    have h0 : (permMask m).testBit 0 = m.testBit 2 := hpm_bit m 0
    have h2 : (permMask m).testBit 2 = m.testBit 0 := hpm_bit m 2
    rw [h0, h2, Bool.or_comm]
  have hpm_p9 (m : ℕ) :
      ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ).any (fun e => (permMask m) &&& e == e) =
      ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ).any (fun e => m &&& e == e) := by
    have hmask (x a b e : ℕ) (hlt : e < 512) (ha9 : a < 9) (hb9 : b < 9)
        (he : ∀ k : Fin 9, e.testBit k.val = decide (k.val = a ∨ k.val = b)) :
        (x &&& e == e) = (x.testBit a && x.testBit b) := by
      have he_all (k : ℕ) : e.testBit k = decide (k = a ∨ k = b) := by
        by_cases hk : k < 9
        · exact he ⟨k, hk⟩
        · have h512 : (512 : ℕ) ≤ 2 ^ k := Nat.pow_le_pow_right (show 0 < 2 by omega) (by omega : 9 ≤ k)
          have h1 : e.testBit k = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt h512)
          have h2 : decide (k = a ∨ k = b) = false := decide_eq_false (by rintro (rfl | rfl) <;> omega)
          rw [h1, h2]
      apply Bool.eq_iff_iff.mpr
      rw [beq_iff_eq, Bool.and_eq_true]
      constructor
      · intro h
        have ha := congrArg (fun n => n.testBit a) h
        have hb := congrArg (fun n => n.testBit b) h
        rw [Nat.testBit_and, he_all a, decide_eq_true (Or.inl rfl), Bool.and_true] at ha
        rw [Nat.testBit_and, he_all b, decide_eq_true (Or.inr rfl), Bool.and_true] at hb
        exact ⟨ha, hb⟩
      · rintro ⟨ha, hb⟩
        apply Nat.eq_of_testBit_eq
        intro k
        rw [Nat.testBit_and, he_all k]
        by_cases hk : k = a ∨ k = b
        · rw [decide_eq_true hk, Bool.and_true]
          rcases hk with rfl | rfl <;> assumption
        · rw [decide_eq_false hk, Bool.and_false]
    let edges : List (Fin 9 × Fin 9 × ℕ) :=
      [(0, 1, 3), (1, 2, 6), (2, 3, 12), (0, 4, 17), (3, 4, 24), (0, 5, 33),
       (1, 6, 66), (2, 7, 132), (5, 7, 160), (3, 8, 264), (5, 8, 288), (6, 8, 320)]
    have hbits_ok : ∀ p ∈ edges,
        p.2.2 < 512 ∧ ∀ k : Fin 9, p.2.2.testBit k.val = decide (k.val = p.1.val ∨ k.val = p.2.1.val) := by
      dsimp only [edges]; decide
    have hedges_perm : ∀ p ∈ edges,
        ∃ q ∈ edges, (ρ p.1.val = q.1.val ∧ ρ p.2.1.val = q.2.1.val) ∨
          (ρ p.1.val = q.2.1.val ∧ ρ p.2.1.val = q.1.val) := by
      dsimp only [edges, ρ]; decide
    have hrew (x : ℕ) :
        ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ).any (fun e => x &&& e == e) =
        edges.any (fun p => x.testBit p.1.val && x.testBit p.2.1.val) := by
      have hmap : ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ) = edges.map (fun p => p.2.2) := rfl
      rw [hmap, List.any_map]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, Function.comp_apply]
      constructor
      · rintro ⟨p, hp, hpx⟩
        obtain ⟨hlt, hbk⟩ := hbits_ok p hp
        rw [hmask x p.1.val p.2.1.val p.2.2 hlt p.1.isLt p.2.1.isLt hbk] at hpx
        exact ⟨p, hp, hpx⟩
      · rintro ⟨p, hp, hpx⟩
        obtain ⟨hlt, hbk⟩ := hbits_ok p hp
        refine ⟨p, hp, ?_⟩
        rw [hmask x p.1.val p.2.1.val p.2.2 hlt p.1.isLt p.2.1.isLt hbk]
        exact hpx
    rw [hrew (permMask m), hrew m]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨p, hp, h1, h2⟩
      rw [hpm_bit m p.1] at h1
      rw [hpm_bit m p.2.1] at h2
      obtain ⟨q, hq, ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩⟩ := hedges_perm p hp
      · exact ⟨q, hq, by rw [← hq1]; exact h1, by rw [← hq2]; exact h2⟩
      · exact ⟨q, hq, by rw [← hq2]; exact h2, by rw [← hq1]; exact h1⟩
    · rintro ⟨p, hp, h1, h2⟩
      obtain ⟨q, hq, ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩⟩ := hedges_perm p hp
      · refine ⟨q, hq, ?_, ?_⟩
        · rw [hpm_bit m q.1, ← hq1, hρ_inv]; exact h1
        · rw [hpm_bit m q.2.1, ← hq2, hρ_inv]; exact h2
      · refine ⟨q, hq, ?_, ?_⟩
        · rw [hpm_bit m q.1, ← hq2, hρ_inv]; exact h2
        · rw [hpm_bit m q.2.1, ← hq1, hρ_inv]; exact h1
  have sym_circuit :
      let C' : Circuit := ⟨C.gates.map fun g => Gate.mk g.op (g.inputs.map ρ), C.output⟩
      FanInTwo C' ∧ C'.size = 14 ∧ C'.output = 23 ∧
      (∀ g ∈ C'.gates, g.op = GateOp.not → g.inputs.length ≤ 1) ∧
      (∃ (i1 i2 : Fin C'.gates.length), i1 < i2 ∧ 3 ≤ i1.val ∧ i1.val ≤ 6 ∧ i2.val < 13 ∧
        (C'.gates.get i1).op = GateOp.not ∧ (C'.gates.get i2).op = GateOp.not ∧
        ∀ i : Fin C'.gates.length, (C'.gates.get i).op = GateOp.not → i = i1 ∨ i = i2) ∧
      (∀ w, List.count (ρ w) (C'.gates.flatMap Gate.inputs) = List.count w flat) ∧
      (∀ w < 23, w ∈ C'.gates.flatMap Gate.inputs) ∧
      {w ∈ Finset.range 23 | 2 ≤ List.count w (C'.gates.flatMap Gate.inputs)}.card ≤ 3 ∧
      (∀ m < 512, C'.eval ((List.ofFn fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 2]) =
        [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320].any fun e => m &&& e == e) := by
    let C' : Circuit := ⟨C.gates.map fun g => Gate.mk g.op (g.inputs.map ρ), C.output⟩
    have hC'len : C'.gates.length = C.gates.length := List.length_map _
    have hC'fan : FanInTwo C' := by
      intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have h := hfan g0 hg0
      exact ⟨h.1, by simp only [List.length_map]; exact h.2⟩
    have hC'sz : C'.size = 14 := by change C'.gates.length = 14; rw [hC'len]; exact hsz
    have hC'not1 : ∀ g ∈ C'.gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
      intro g hg hop
      simp only [C', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      simp only [List.length_map]
      exact hnot1 g0 hg0 hop
    have hC'get_op (i : Fin C'.gates.length) :
        (C'.gates.get i).op = (C.gates.get ⟨i.val, by rw [← hC'len]; exact i.isLt⟩).op := by
      simp only [C', List.get_eq_getElem, List.getElem_map]
    have hC'not2 : ∃ (i1 i2 : Fin C'.gates.length), i1 < i2 ∧ 3 ≤ i1.val ∧ i1.val ≤ 6 ∧ i2.val < 13 ∧
        (C'.gates.get i1).op = GateOp.not ∧ (C'.gates.get i2).op = GateOp.not ∧
        ∀ i : Fin C'.gates.length, (C'.gates.get i).op = GateOp.not → i = i1 ∨ i = i2 := by
      obtain ⟨i1, i2, hlt12, h1ge, h1le, h2lt, h1op, h2op, honly⟩ := hnot2
      let j1 : Fin C'.gates.length := ⟨i1.val, by rw [hC'len]; exact i1.isLt⟩
      let j2 : Fin C'.gates.length := ⟨i2.val, by rw [hC'len]; exact i2.isLt⟩
      refine ⟨j1, j2, hlt12, h1ge, h1le, h2lt, by rw [hC'get_op]; exact h1op, by rw [hC'get_op]; exact h2op, ?_⟩
      intro i hi
      rw [hC'get_op] at hi
      rcases honly ⟨i.val, by rw [← hC'len]; exact i.isLt⟩ hi with h | h
      · exact Or.inl (Fin.ext (congrArg (Fin.val : Fin C.gates.length → ℕ) h))
      · exact Or.inr (Fin.ext (congrArg (Fin.val : Fin C.gates.length → ℕ) h))
    have hflat_map : C'.gates.flatMap Gate.inputs = flat.map ρ := by
      have hgen : ∀ gs : List Gate, (gs.map fun g => Gate.mk g.op (g.inputs.map ρ)).flatMap Gate.inputs =
          (gs.flatMap Gate.inputs).map ρ := by
        intro gs
        induction gs with
        | nil => rfl
        | cons g rest ih => simp only [List.map_cons, List.flatMap_cons, List.map_append, ih]
      exact hgen C.gates
    have hcount_map : ∀ (l : List ℕ) (w : ℕ), List.count (ρ w) (l.map ρ) = List.count w l := by
      intro l w
      induction l with
      | nil => rfl
      | cons a rest ih =>
        simp only [List.map_cons, List.count_cons, ih]
        by_cases haw : a = w
        · subst haw; simp
        · have hne1 : (a == w) = false := beq_false_of_ne haw
          have hne2 : (ρ a == ρ w) = false := beq_false_of_ne (fun h => haw (hρ_inj h))
          simp [hne1, hne2]
    have hC'count (w : ℕ) : List.count (ρ w) (C'.gates.flatMap Gate.inputs) = List.count w flat := by
      rw [hflat_map]; exact hcount_map flat w
    have hC'all : ∀ w < 23, w ∈ C'.gates.flatMap Gate.inputs := by
      intro w hw
      rw [hflat_map, List.mem_map]
      exact ⟨ρ w, hall (ρ w) (hρ_lt23 w hw), hρ_inv w⟩
    have hC'dup3 : {w ∈ Finset.range 23 | 2 ≤ List.count w (C'.gates.flatMap Gate.inputs)}.card ≤ 3 := by
      have hsub : {w ∈ Finset.range 23 | 2 ≤ List.count w (C'.gates.flatMap Gate.inputs)} ⊆
          ({w ∈ Finset.range 23 | 2 ≤ List.count w flat}).image ρ := by
        intro w hw
        obtain ⟨hw23, hwc⟩ := Finset.mem_filter.mp hw
        have hwlt : w < 23 := Finset.mem_range.mp hw23
        refine Finset.mem_image.mpr ⟨ρ w, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hρ_lt23 w hwlt), ?_⟩, hρ_inv w⟩
        have heq := hC'count (ρ w)
        rw [hρ_inv w] at heq
        omega
      exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le hdup3)
    have hC'comp : ∀ m < 512, C'.eval ((List.ofFn fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 2]) =
        [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320].any fun e => m &&& e == e := by
      let step : List Bool → Gate → List Bool := fun w g =>
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      let run : List Gate → List Bool → List Bool := fun gs w => gs.foldl step w
      have getD_snoc_eq {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
        rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
      have getD_snoc_ne {α : Type} (l : List α) (a d : α) (j : ℕ) (hj : j ≠ l.length) :
          (l ++ [a]).getD j d = l.getD j d := by
        by_cases hlt : j < l.length
        · exact List.getD_append _ _ _ _ hlt
        · rw [List.getD_eq_default (l ++ [a]) d (n := j) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
              List.getD_eq_default l d (n := j) (by omega)]
      have hremap_run (gs : List Gate) (wA wB : List Bool)
          (hlen_w : wA.length = wB.length) (h9 : 9 ≤ wA.length)
          (hrel : ∀ i, wB.getD (ρ i) false = wA.getD i false) :
          ∀ i, (run (gs.map fun g => Gate.mk g.op (g.inputs.map ρ)) wB).getD (ρ i) false =
            (run gs wA).getD i false := by
        induction gs generalizing wA wB with
        | nil => exact hrel
        | cons g rest ih =>
          simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
          have hinp : (g.inputs.map ρ).map (fun i => wB.getD i false) =
              g.inputs.map (fun i => wA.getD i false) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro i _
            exact hrel i
          let b := g.op.eval (g.inputs.map fun i => wA.getD i false)
          have hstepB : step wB (Gate.mk g.op (g.inputs.map ρ)) = wB ++ [b] := by
            dsimp only [step, b]; rw [hinp]
          rw [hstepB]
          apply ih (step wA g) (wB ++ [b])
          · simp only [step, List.length_append, hlen_w, List.length_cons, List.length_nil]
          · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
          · intro i
            dsimp only [step]
            by_cases hi : i = wA.length
            · subst hi
              have hfi : ρ wA.length = wB.length := by rw [hρ_ge9 wA.length h9, hlen_w]
              rw [hfi, getD_snoc_eq wB b false, getD_snoc_eq wA b false]
            · have hfi : ρ i ≠ wB.length := by
                intro hfeq
                by_cases hlt : i < 9
                · have : ρ i < 9 := hρ_lt9 ⟨i, hlt⟩; omega
                · have := hρ_ge9 i (by omega); omega
              rw [getD_snoc_ne wB b false (ρ i) hfi, getD_snoc_ne wA b false i hi]
              exact hrel i
      intro m hm
      let m' := permMask m
      have hm'lt : m' < 512 := hpm_lt m
      let wB : List Bool := (List.ofFn fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 2]
      let wA : List Bool := (List.ofFn fun i : Fin 9 => m'.testBit i.val) ++ [m'.testBit 0 || m'.testBit 2]
      have hwB_len : wB.length = 10 := by simp only [wB, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      have hwA_len : wA.length = 10 := by simp only [wA, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      have hrel : ∀ i, wB.getD (ρ i) false = wA.getD i false := by
        intro i
        by_cases h9 : i < 9
        · have hpi : ρ i < 9 := hρ_lt9 ⟨i, h9⟩
          dsimp only [wB, wA]
          rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hpi),
              List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact h9),
              List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hpi), List.getElem_ofFn,
              List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact h9), List.getElem_ofFn]
          exact (hpm_bit m ⟨i, h9⟩).symm
        · by_cases hi9 : i = 9
          · subst hi9
            rw [hρ_ge9 9 (by omega)]
            dsimp only [wB, wA]
            have hl9 : (List.ofFn fun j : Fin 9 => m.testBit j.val).length = 9 := List.length_ofFn
            have hl9' : (List.ofFn fun j : Fin 9 => m'.testBit j.val).length = 9 := List.length_ofFn
            rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
            simp only [hl9, hl9', Nat.sub_self, List.getD_cons_zero]
            exact (hpm_or m).symm
          · rw [hρ_ge9 i (by omega),
                List.getD_eq_default wB false (n := i) (by rw [hwB_len]; omega),
                List.getD_eq_default wA false (n := i) (by rw [hwA_len]; omega)]
      have hev : C'.eval wB = C.eval wA := by
        have h := hremap_run C.gates wA wB (by rw [hwA_len, hwB_len]) (by rw [hwA_len]; omega) hrel C.output
        rw [hout, hρ_ge9 23 (by omega)] at h
        change (run (C.gates.map fun g => Gate.mk g.op (g.inputs.map ρ)) wB).getD C.output false =
          (run C.gates wA).getD C.output false
        rw [hout]
        exact h
      rw [hev]
      exact (hcomp m' hm'lt).trans (hpm_p9 m)
    exact ⟨hC'fan, hC'sz, hout, hC'not1, hC'not2, hC'count, hC'all, hC'dup3, hC'comp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw0
  rcases hw0 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hDup0 C hfan hsz hout hnot1 hnot2 hall hdup3 hcomp ⟨hge2, hcount_le4 0 (by omega), hC_excess⟩
  · exact hDup1 C hfan hsz hout hnot1 hnot2 hall hdup3 hcomp ⟨hge2, hcount_le4 1 (by omega), hC_excess⟩
  · let C' : Circuit := ⟨C.gates.map fun g => Gate.mk g.op (g.inputs.map ρ), C.output⟩
    obtain ⟨hC'fan, hC'sz, hC'out, hC'not1, hC'not2, hC'count, hC'all, hC'dup3, hC'comp⟩ := sym_circuit
    have hC'ex : (Finset.range 23).sum (fun w => List.count w (C'.gates.flatMap Gate.inputs) - 1) ≤ 3 := by
      obtain ⟨i1, i2, hlt12, _, _, _, h1not, h2not, _⟩ := hC'not2
      exact excess_bound C' hC'fan hC'sz hC'not1 ⟨i1, i2, hlt12, h1not, h2not⟩ hC'all
    have h0eq : List.count 0 (C'.gates.flatMap Gate.inputs) = List.count 2 flat := hC'count 2
    exact hDup0 C' hC'fan hC'sz hC'out hC'not1 hC'not2 hC'all hC'dup3 hC'comp
      ⟨by rw [h0eq]; exact hge2, by rw [h0eq]; exact hcount_le4 2 (by omega), hC'ex⟩
  · exact hDup4 C hfan hsz hout hnot1 hnot2 hall hdup3 hcomp ⟨hge2, hcount_le4 4 (by omega), hC_excess⟩
  · let C' : Circuit := ⟨C.gates.map fun g => Gate.mk g.op (g.inputs.map ρ), C.output⟩
    obtain ⟨hC'fan, hC'sz, hC'out, hC'not1, hC'not2, hC'count, hC'all, hC'dup3, hC'comp⟩ := sym_circuit
    have hC'ex : (Finset.range 23).sum (fun w => List.count w (C'.gates.flatMap Gate.inputs) - 1) ≤ 3 := by
      obtain ⟨i1, i2, hlt12, _, _, _, h1not, h2not, _⟩ := hC'not2
      exact excess_bound C' hC'fan hC'sz hC'not1 ⟨i1, i2, hlt12, h1not, h2not⟩ hC'all
    have h4eq : List.count 4 (C'.gates.flatMap Gate.inputs) = List.count 7 flat := hC'count 7
    exact hDup4 C' hC'fan hC'sz hC'out hC'not1 hC'not2 hC'all hC'dup3 hC'comp
      ⟨by rw [h4eq]; exact hge2, by rw [h4eq]; exact hcount_le4 7 (by omega), hC'ex⟩
  · exact hDup8 C hfan hsz hout hnot1 hnot2 hall hdup3 hcomp ⟨hge2, hcount_le4 8 (by omega), hC_excess⟩
