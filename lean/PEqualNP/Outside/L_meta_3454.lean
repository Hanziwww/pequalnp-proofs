import Mathlib.Data.Finset.Card
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3454 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ g ∈ F, g < C.gates.length) → ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => w < n)).card + ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => n ≤ w ∧ w - n ∉ F)).card + (F.filter (fun g => n + g ∈ F.biUnion (fun g' => (PEqualNP.MetaComplexity.NestedCover.gateAt C g').inputs.toFinset))).card ≤ 2 * F.card := by
  intro n C F hC valid
  let inputs (g : ℕ) := (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset
  let R := F.biUnion inputs
  let internal := F.filter (fun g => n+g ∈ R)
  let gates := R.filter (fun w => n ≤ w)
  have inputs_bound (g : ℕ) (hg : g ∈ F) : (inputs g).card ≤ 2 := by
    have hj := valid g hg
    have member : PEqualNP.MetaComplexity.NestedCover.gateAt C g ∈ C.gates := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    exact (List.toFinset_card_le _).trans (hC.2.2 _ member).le
  have total : R.card ≤ 2 * F.card := calc
    R.card ≤ ∑ g ∈ F, (inputs g).card := Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ F, 2 := Finset.sum_le_sum inputs_bound
    _ = 2 * F.card := by simp [Nat.mul_comm]
  have partition : (R.filter (fun w => w < n)).card + gates.card = R.card := by
    simpa [gates] using R.card_filter_add_card_filter_not (fun w => w < n)
  have split : (R.filter (fun w => n ≤ w ∧ w-n ∉ F)).card +
      (gates.filter (fun w => w-n ∈ F)).card = gates.card := by
    simpa [gates, Finset.filter_filter, and_comm] using
      gates.card_filter_add_card_filter_not (fun w => w-n ∉ F)
  have incl : internal.image (fun g => n+g) ⊆ gates.filter (fun w => w-n ∈ F) := by
    intro w hw
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨inF,inR⟩ := Finset.mem_filter.mp hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨inR,by omega⟩,by simpa using inF⟩
  have bound := Finset.card_le_card incl
  rw [Finset.card_image_of_injective internal (fun _ _ h => Nat.add_left_cancel h)] at bound
  change (R.filter (fun w => w < n)).card + (R.filter (fun w => n ≤ w ∧ w-n ∉ F)).card +
    internal.card ≤ 2 * F.card
  omega
