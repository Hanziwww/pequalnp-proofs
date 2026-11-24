import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.NotPremium PEqualNP.CarriedProduct

theorem PEqualNP.Outside.R_meta_4281_17
    (hUnitDirty :
      ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
        (5 : ℕ∞) ≤ G.egirth →
        have cov : Circuit → Finset (Sym2 (Fin n)) := fun D => {e ∈ G.edgeFinset | circuitFun n D (fun v => decide (v ∈ e)) = true};
        have ok : Circuit → Prop := fun D => Monotone2 D ∧ circuitFun n D ≤ graphFun G ∅;
        ∀ C : Circuit,
          ok C →
          (∀ D : Circuit, ok D → D.size < C.size → (cov D).card < (cov C).card) →
          have d2 : ℕ → Fin n → Fin n → Prop := fun j u v => (gateAt C j).op = GateOp.and ∧ gateVal n C j (pairInput u v) = true;
          have dirty : ℕ → Prop := fun j => ∃ u v : Fin n, ¬ G.Adj u v ∧ d2 j u v;
          have kill : ℕ → Circuit := fun j => ⟨replaceByConst C.gates j false, C.output⟩;
          (∀ j, (j < C.size → cov (kill j) ⊂ cov C) ∧ (dirty j → 3 ≤ (cov C \ cov (kill j)).card)) →
          (∃ j u, d2 j u u) →
          ∃ j, dirty j ∧ (cov C \ cov (kill j)).card ≤
            c * (C.size - {k ∈ (Finset.range C.size).erase j | ∃ e ∈ G.edgeFinset, IsLive n (kill j) (fun v => decide (v ∈ e)) (n + k)}.card))
    (hNoUnitDirty :
      ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
        (5 : ℕ∞) ≤ G.egirth →
        have cov : Circuit → Finset (Sym2 (Fin n)) := fun D => {e ∈ G.edgeFinset | circuitFun n D (fun v => decide (v ∈ e)) = true};
        have ok : Circuit → Prop := fun D => Monotone2 D ∧ circuitFun n D ≤ graphFun G ∅;
        ∀ C : Circuit,
          ok C →
          (∀ D : Circuit, ok D → D.size < C.size → (cov D).card < (cov C).card) →
          have d2 : ℕ → Fin n → Fin n → Prop := fun j u v => (gateAt C j).op = GateOp.and ∧ gateVal n C j (pairInput u v) = true;
          have dirty : ℕ → Prop := fun j => ∃ u v : Fin n, ¬ G.Adj u v ∧ d2 j u v;
          have kill : ℕ → Circuit := fun j => ⟨replaceByConst C.gates j false, C.output⟩;
          (∀ j, (j < C.size → cov (kill j) ⊂ cov C) ∧ (dirty j → 3 ≤ (cov C \ cov (kill j)).card) ∧ ∀ u, ¬ d2 j u u) →
          (∃ j, dirty j) →
          ∃ j, dirty j ∧ (cov C \ cov (kill j)).card ≤
            c * (C.size - {k ∈ (Finset.range C.size).erase j | ∃ e ∈ G.edgeFinset, IsLive n (kill j) (fun v => decide (v ∈ e)) (n + k)}.card)) :
    ∃ (x1 : ℕ),   ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [DecidableRel x3.Adj],     (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) →       (5 : ℕ∞) ≤ x3.egirth →         have x7 : Sym2 (Fin x2) → Fin x2 → Bool := fun (x7 : Sym2 (Fin x2)) (x8 : Fin x2) => Decidable.decide (x8 ∈ x7);         have x8 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Sym2 (Fin x2)) := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => {x9 ∈ x3.edgeFinset | PEqualNP.MetaComplexity.circuitFun x2 x8 (x7 x9) = Bool.true};         have x9 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x9 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x9 ∧ PEqualNP.MetaComplexity.circuitFun x2 x9 ≤ PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅;         have x10 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x10 : PEqualNP.CircuitLowerBounds.Circuit) (x11 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x10 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x12 : Fin x2) (x13 : Fin x2), ¬x3.Adj x12 x13 ∧ PEqualNP.EdgeOwnership.gateVal x2 x10 x11 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true;         ∀ (x11 : PEqualNP.CircuitLowerBounds.Circuit),           x9 x11 →             (∀ (x13 : PEqualNP.CircuitLowerBounds.Circuit), x9 x13 → x13.size < x11.size → (x8 x13).card < (x8 x11).card) →               have x14 : ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x14 : ℕ) => { gates := PEqualNP.NotPremium.replaceByConst x11.gates x14 Bool.false, output := x11.output : PEqualNP.CircuitLowerBounds.Circuit };               (∀ x15 < x11.size, x8 (x14 x15) ⊂ x8 x11) → (∃ (x16 : ℕ), x10 x11 x16) → ∃ (x17 : ℕ), x10 x11 x17 ∧ (x8 x11 \ x8 (x14 x17)).card ≤ x1 * (x11.size - {x18 ∈ (Finset.range x11.size).erase x17 | ∃ x19 ∈ x3.edgeFinset, PEqualNP.CarriedProduct.IsLive x2 (x14 x17) (x7 x19) (x2 + x18)}.card) := by
  obtain ⟨c1, hc1⟩ := hUnitDirty
  obtain ⟨c2, hc2⟩ := hNoUnitDirty
  refine ⟨max 2 (max c1 c2), ?_⟩
  intro n G hdec hdeg hgirth eIn cov ok dirty C hok hmin kill hdrop hdir
  have hdir_iff (j : ℕ) :
      dirty C j ↔ ∃ u v : Fin n, ¬ G.Adj u v ∧ (gateAt C j).op = GateOp.and ∧ gateVal n C j (pairInput u v) = true := by
    constructor
    · rintro ⟨hop, u, v, hadj, hgv⟩; exact ⟨u, v, hadj, hop, hgv⟩
    · rintro ⟨u, v, hadj, hop, hgv⟩; exact ⟨hop, u, v, hadj, hgv⟩
  by_cases hlow : ∃ j, dirty C j ∧ (cov C \ cov (kill j)).card ≤ 2
  · obtain ⟨j, hdj, hle2⟩ := hlow
    have hjlt : j < C.size := by
      by_contra hge
      have hge' : C.gates.length ≤ j := by change ¬ j < C.gates.length at hge; omega
      have hdef : gateAt C j = ⟨GateOp.or, []⟩ := List.getD_eq_default C.gates ⟨GateOp.or, []⟩ hge'
      have hand := hdj.1
      rw [hdef] at hand; cases hand
    have hmem : j ∈ Finset.range C.size := Finset.mem_range.mpr hjlt
    have herase : ((Finset.range C.size).erase j).card + 1 = C.size := by
      have h := Finset.card_erase_add_one hmem
      rw [Finset.card_range] at h; exact h
    have hfilt_le : ({k ∈ (Finset.range C.size).erase j |
        ∃ e ∈ G.edgeFinset, IsLive n (kill j) (eIn e) (n + k)}).card ≤ ((Finset.range C.size).erase j).card :=
      Finset.card_filter_le _ _
    have hpos : 1 ≤ C.size - ({k ∈ (Finset.range C.size).erase j |
        ∃ e ∈ G.edgeFinset, IsLive n (kill j) (eIn e) (n + k)}).card := by omega
    refine ⟨j, hdj, ?_⟩
    have hc2_le : 2 ≤ max 2 (max c1 c2) := le_max_left _ _
    have hmul : max 2 (max c1 c2) * 1 ≤
        max 2 (max c1 c2) * (C.size - ({k ∈ (Finset.range C.size).erase j |
          ∃ e ∈ G.edgeFinset, IsLive n (kill j) (eIn e) (n + k)}).card) :=
      Nat.mul_le_mul_left _ hpos
    omega
  · have hge3 : ∀ j, (∃ u v : Fin n, ¬ G.Adj u v ∧ (gateAt C j).op = GateOp.and ∧ gateVal n C j (pairInput u v) = true) →
        3 ≤ (cov C \ cov (kill j)).card := by
      intro j hdj
      by_contra hlt
      exact hlow ⟨j, (hdir_iff j).mpr hdj, by omega⟩
    have hdir' : ∃ j, ∃ u v : Fin n, ¬ G.Adj u v ∧ (gateAt C j).op = GateOp.and ∧ gateVal n C j (pairInput u v) = true := by
      obtain ⟨j, hdj⟩ := hdir
      exact ⟨j, (hdir_iff j).mp hdj⟩
    by_cases hunit : ∃ j u, (gateAt C j).op = GateOp.and ∧ gateVal n C j (pairInput u u) = true
    · obtain ⟨j, hdj, hbd⟩ := hc1 n G hdeg hgirth C hok hmin (fun j => ⟨hdrop j, hge3 j⟩) hunit
      exact ⟨j, (hdir_iff j).mpr hdj, Nat.le_trans hbd (Nat.mul_le_mul_right _ (by omega))⟩
    · have hcomb : ∀ j, (j < C.size → cov (kill j) ⊂ cov C) ∧
          ((∃ u v : Fin n, ¬ G.Adj u v ∧ (gateAt C j).op = GateOp.and ∧ gateVal n C j (pairInput u v) = true) →
            3 ≤ (cov C \ cov (kill j)).card) ∧
          ∀ u, ¬ ((gateAt C j).op = GateOp.and ∧ gateVal n C j (pairInput u u) = true) :=
        fun j => ⟨hdrop j, hge3 j, fun u h => hunit ⟨j, u, h⟩⟩
      obtain ⟨j, hdj, hbd⟩ := hc2 n G hdeg hgirth C hok hmin hcomb hdir'
      exact ⟨j, (hdir_iff j).mpr hdj, Nat.le_trans hbd (Nat.mul_le_mul_right _ (by omega))⟩
