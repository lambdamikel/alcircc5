-- Supporting Lean snippets for the Round 26-28 referee report
-- Intended to be placed alongside Round19Transport.lean and imported there.

import Round19Transport

namespace Round19

/-- Oracle-shaped BoundedDecider that witnesses Nonempty BoundedDecider
    without providing a genuine algorithmic checker. -/
noncomputable def oracleBoundedDecider : BoundedDecider := by
  classical
  refine
    { bound := fun _ => 1
      check := fun C _ => if Satisfiable C then true else false
      sound := ?sound
      complete := ?complete }
  · intro C n hcheck
    by_cases h : Satisfiable C
    · exact h
    · have hfalse : False := by simpa [h] using hcheck
      cases hfalse
  · intro C hsat
    refine ⟨0, by decide, ?_⟩
    simp [hsat]

noncomputable example : Nonempty BoundedDecider :=
  ⟨oracleBoundedDecider⟩

/-- Degenerate finite catalogue showing that certK_finitely_codable
    does not enforce non-trivial faithfulness. -/
def FK_emptyForCertK : FinCatalog :=
  { nCore := certK.nCore
    coreNetTable := []
    templates := []
    root := certK.root
    attaches := certK.attaches
    slotBound := 0
    fTable := [] }

example : (FinCatalog.decode FK_emptyForCertK).templates.length = 0 := rfl
example : certK.templates.length = 2 := rfl

example :
    (∀ i j, (i, j) ∈ ([] : List (Nat × Nat)) →
      (FinCatalog.decode FK_emptyForCertK).coreNet i j = certK.coreNet i j) := by
  intro i j h
  cases h

end Round19
