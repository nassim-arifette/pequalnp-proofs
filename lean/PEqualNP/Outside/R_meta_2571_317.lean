import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.BlindGate

-- Adjoin one virtual point whose neighbors are precisely the three flag lines.
-- Test the two wires on the minimal edges and maximal independent inputs of this graph.
theorem PEqualNP.Outside.R_meta_2571_317
    (hw : ∀ (C : Circuit), Monotone2 C → ∀ w : ℕ,
      Monotone (fun x : Fin 25 → Bool => wireValue C 25 x w))
    (hcert :
      let E (i j : Fin 25) := i.val < 12 ∧ 12 ≤ j.val ∧
        (i.val + j.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ) ∧ i.val ∉ ([0,2,8] : List ℕ)
      let S : List (Fin 25) := [13,15,21]
      let free (z : Bool × (Fin 25 → Bool)) :=
        (¬ ∃ i j, E i j ∧ z.2 i = true ∧ z.2 j = true) ∧
        (z.1 = true → ∀ j ∈ S, z.2 j = false)
      ∃ (C : Circuit) (q : ℕ), Monotone2 C ∧ C.size ≤ 45 ∧
        C.output < 25 + C.size ∧ q < 25 + C.size ∧
        (∀ i j, E i j → circuitFun 25 C (fun k => decide (k = i ∨ k = j)) = true) ∧
        (∀ j ∈ S, wireValue C 25 (fun k => decide (k = j)) q = true) ∧
        ∀ z, Maximal free z → circuitFun 25 C z.2 = false ∧
          (z.1 = true → wireValue C 25 z.2 q = false)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (45 : ℕ) ∧ x1.output < (25 : ℕ) + x1.size ∧ x2 < (25 : ℕ) + x1.size ∧ ∀ (x3 : Fin (25 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (25 : ℕ)) (x5 : Fin (25 : ℕ)), ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x4 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  classical
  let E (i j : Fin 25) := i.val < 12 ∧ 12 ≤ j.val ∧
    (i.val + j.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ) ∧ i.val ∉ ([0,2,8] : List ℕ)
  let S : List (Fin 25) := [13,15,21]
  let hit (x : Fin 25 → Bool) := ∃ i j, E i j ∧ x i = true ∧ x j = true
  let free (z : Bool × (Fin 25 → Bool)) := ¬ hit z.2 ∧
    (z.1 = true → ∀ j ∈ S, z.2 j = false)
  obtain ⟨C,q,mono,budget,hout,hq,pairs,singles,maxima⟩ := hcert
  refine ⟨C,q,mono,budget,hout,hq,?_⟩
  intro x
  have liftOn (w : ℕ) {u v : Fin 25 → Bool} (h : u ≤ v) (hu : wireValue C 25 u w = true) :
      wireValue C 25 v w = true :=
    Bool.eq_true_of_true_le (hu ▸ hw C mono w h)
  have liftOff (w : ℕ) {u v : Fin 25 → Bool} (h : u ≤ v) (hv : wireValue C 25 v w = false) :
      wireValue C 25 u w = false :=
    le_antisymm (hv ▸ hw C mono w h) (Bool.false_le _)
  have detects : circuitFun 25 C x = true ↔ hit x := by
    constructor
    · intro yes
      by_contra hn
      have hfree : free (false,x) := ⟨hn,by simp⟩
      obtain ⟨z,hz,hmax⟩ := Finite.exists_le_maximal (p := free) hfree
      have off := liftOff C.output hz.2 (maxima z hmax).1
      exact Bool.noConfusion (yes.symm.trans off)
    · rintro ⟨i,j,e,hi,hj⟩
      apply liftOn C.output _ (pairs i j e)
      intro k
      by_cases h : k = i ∨ k = j
      · rcases h with rfl | rfl <;> simp [*]
      · simp [h]
  constructor
  · constructor
    · intro yes
      obtain ⟨i,j,⟨hi,hj,he,hn⟩,xi,xj⟩ := detects.mp yes
      exact ⟨i,j,hi,hj,he,hn,xi,xj⟩
    · rintro ⟨i,j,hi,hj,he,hn,xi,xj⟩
      exact detects.mpr ⟨i,j,⟨hi,hj,he,hn⟩,xi,xj⟩
  · intro no
    change wireValue C 25 x q = (x 13 || x 15 || x 21)
    by_cases on : ∃ j ∈ S, x j = true
    · obtain ⟨j,hj,hx⟩ := on
      have aux : wireValue C 25 x q = true := by
        apply liftOn q _ (singles j hj)
        intro k
        by_cases h : k = j
        · subst k; simp [hx]
        · simp [h]
      rw [aux]
      simp only [S,List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl <;> simp [hx]
    · have dark : ∀ j ∈ S, x j = false := by
        intro j hj
        exact Bool.eq_false_iff.mpr (fun h => on ⟨j,hj,h⟩)
      have hfree : free (true,x) := ⟨fun hitx => by
        have h := detects.mpr hitx
        rw [show circuitFun 25 C x = false from no] at h
        contradiction, fun _ => dark⟩
      obtain ⟨z,hz,hmax⟩ := Finite.exists_le_maximal (p := free) hfree
      have aux := liftOff q hz.2 ((maxima z hmax).2 (Bool.eq_true_of_true_le hz.1))
      simp [aux, dark 13 (by decide), dark 15 (by decide), dark 21 (by decide)]
